import ModalDistribution.Examples.ThyHBB4.Safety

/-!
# The fast delivery path

A delivery may be backed by an echo for `v` from every participant that is
sequential in the delivering world's past. The safety argument for this path
does not use depth at all: under vote monotonicity, any vote for a learner in `l`'s row
traces back to an echo quorum of some learner correlated with `l`; that quorum
meets `l`'s sequential quorum (from the fast clause's end-of-time guarantee),
and the common member echoed both values in the observer's past, so the values
coincide.
-/

namespace ModalDistribution.Examples.ThyHBB4
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

/-- Descending a vote's certificate chain to any lower rank. -/
theorem cert_of_higher_vote (h : BaseProtocol M σ) {g : World P S.EventType}
    (hg : g.time ⪯ M.history.val) {d u : S.Value} {r m : Nat} (hrm : r < m)
    (hv : ⟪g⟫ ⊨[M] σ.vote d u m) :
    ∃ g', (g' ≪ g ∨ g' = g) ∧ (⟪g'⟫ ⊨[M] σ.voteCertificate d u r) := by
  obtain ⟨i, rfl⟩ : ∃ i, m = r + 1 + i := ⟨m - (r + 1), by omega⟩
  clear hrm
  induction i generalizing g with
  | zero => exact ⟨g, Or.inr rfl, h.voteSuccBackward hg hv⟩
  | succ i ih =>
    have hcert := h.voteSuccBackward hg hv
    obtain ⟨g₁, hg₁, hv₁⟩ := quorum_witness hcert
    obtain ⟨g', hg', hc⟩ := ih (predecessor_possible hg hg₁) hv₁
    refine ⟨g', Or.inl ?_, hc⟩
    rcases hg' with hg' | rfl
    · exact accessible_trans hg hg' hg₁
    · exact hg₁

/-- Every vote in a round-zero-monotone model has a round-zero vote for the same
learner and value in its past (or is one). -/
theorem zero_vote_of_vote (h : BaseProtocol M σ) {g : World P S.EventType}
    (hg : g.time ⪯ M.history.val) {b u : S.Value} {n : Nat}
    (hv : ⟪g⟫ ⊨[M] σ.vote b u n) :
    ∃ g0, (g0 ≪ g ∨ g0 = g) ∧ (⟪g0⟫ ⊨[M] σ.vote b u 0) := by
  cases n with
  | zero => exact ⟨g, Or.inr rfl, hv⟩
  | succ n =>
    obtain ⟨g', hg', hcert⟩ := cert_of_higher_vote h hg (Nat.zero_lt_succ n) hv
    obtain ⟨g0, hg0, hv0⟩ := quorum_witness hcert
    refine ⟨g0, Or.inl ?_, hv0⟩
    rcases hg' with hg' | rfl
    · exact accessible_trans hg hg0 hg'
    · exact hg0

/-- Under vote monotonicity, if every participant sequential at `w` has echoed
`v` in the past of `w`, and `l` has a quorum sequential at `w`, then every vote
observed at any possible world `f ⪯ w` for a learner correlated with `l` at `f`
is for `v`. -/
theorem value_of_echo_unanimity (h : BaseProtocol M σ) (hmono : VoteMonotonicity M σ)
    {w : World P S.EventType} (hw : w.time ⪯ M.history.val) {l v : S.Value}
    (hQl : SequentialQuorumAt M l w)
    (hecho : SequentialEchoes M σ w v) :
    ∀ (k : Nat) {f g : World P S.EventType}, f.time ⪯ M.history.val → (f ≪ w ∨ f = w) →
      PreHistory.height g.time = k → g ≪ f →
      ∀ {b u : S.Value} {n : Nat}, Correlated M σ.correlationSymb f l b →
      (⟪g⟫ ⊨[M] σ.vote b u n) → u = v := by
  obtain ⟨Q, hQ, hQseq⟩ := hQl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro f g hf hfw hk hg b u n hlb hv
    have hgpos := predecessor_possible hf hg
    have toW : ∀ {x : World P S.EventType}, x ≪ f → x ≪ w := by
      intro x hx
      rcases hfw with hfw | rfl
      · exact accessible_trans hw hx hfw
      · exact hx
    obtain ⟨g0, hg0, hv0⟩ := zero_vote_of_vote h hgpos hv
    have hg0f : g0 ≪ f := by
      rcases hg0 with hg0 | rfl
      · exact accessible_trans hf hg0 hg
      · exact hg
    have hg0le : PreHistory.height g0.time ≤ PreHistory.height g.time := by
      rcases hg0 with hg0 | rfl
      · exact Nat.le_of_lt (PreHistory.height_lt_of_accessible hg0)
      · exact Nat.le_refl _
    have hg0pos := predecessor_possible hf hg0f
    have hbl : Correlated M σ.correlationSymb g0 b l :=
      hmono hf hg0f hv0 (Or.inl rfl) l (h.correlationSymm hf hlb)
    rcases h.voteZeroBackward hg0pos hv0 with hcert | ⟨s, m, hbs, hs⟩
    · -- Echo-based: `b`'s echo quorum meets `l`'s sequential quorum; the common
      -- member is sequential at `w`, hence echoed `v`, and also echoed `u`.
      obtain ⟨X, hX, hXecho⟩ := quorum_exists_iff.mp hcert
      obtain ⟨q, hq, _⟩ := (sat_diamond_pair_iff M f l b Formula.seq).mp
        (h.correlationSeq hf hlb) Q hQ X hX
      obtain ⟨e, he, heq, hu⟩ := hXecho q hq.2
      have hseq : isSequential (Event := S.EventType) q w.time := hQseq q hq.1
      obtain ⟨t, ht, htq, hvq⟩ := hecho q hseq
      have hew : e ≪ w := toW (accessible_trans hf he hg0f)
      exact echo_unique_of_sequential h hw hseq hew ht heq htq hu hvq
    · -- Transfer-based: recurse on the source at the transfer event.
      have hls : Correlated M σ.correlationSymb g0 l s :=
        h.correlationTrans hg0pos (h.correlationSymm hg0pos hbl) hbs
      obtain ⟨g1, hg1, hv1⟩ := observedAt_iff.mpr hs
      have hlt := PreHistory.height_lt_of_accessible hg1
      exact ih (PreHistory.height g1.time) (by omega) hg0pos (Or.inl (toW hg0f)) rfl hg1 hls hv1

/-- The observer-level form: with echoes for `v` from every `w`-sequential
participant, every observed vote for a learner in `l`'s row at `w` is for `v`. -/
theorem value_of_echo_unanimity_at (h : BaseProtocol M σ) (hmono : VoteMonotonicity M σ)
    {w : World P S.EventType} (hw : w.time ⪯ M.history.val) {l v : S.Value}
    (hQl : SequentialQuorumAt M l w)
    (hecho : SequentialEchoes M σ w v)
    {b u : S.Value} {n : Nat} (hlb : Correlated M σ.correlationSymb w l b)
    (hu : ObservedAt M w (σ.vote b u n)) : u = v := by
  obtain ⟨g, hg, hv⟩ := hu
  exact value_of_echo_unanimity h hmono hw hQl hecho _ hw (Or.inr rfl) rfl hg hlb hv

end ModalDistribution.Examples.ThyHBB4
