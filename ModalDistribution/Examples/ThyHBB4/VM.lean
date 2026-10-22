import ModalDistribution.Examples.ThyHBB4.LivenessTwo
import ModalDistribution.Examples.ThyHBB4.StrictDepth
import ModalDistribution.Examples.ThyHBB4.FastPath
import ModalDistribution.Examples.ThyHBB4.CM

/-!
# HBB4 correctness under vote monotonicity

`ProtocolVM` isolates the instances of causal monotonicity that the CM proofs
actually use, in a single axiom `VoteMonotonicity`: the target of an observed
vote keeps the observer's correlations at the vote event, for every round-zero
vote (the base case) and for the later vote of a same-signer, same-round switch
between correlated learners (the inductive step). The chains are strict, so no monotonicity is needed when
extending them. Agreement, Liveness 1 and Liveness 2 all follow, with the same
single-vote conflict bound as under CM.
-/

namespace ModalDistribution.Examples.ThyHBB4.VM
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

/-- Conflicting votes of ranks `≥ r` for learners in the observer's row force a
strict chain of index `r + 1` ending at the observer. -/
theorem conflict_yields_strict_depth_chain (h : ProtocolVM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {r n k : Nat}
    (hb : Correlated M σ.correlationSymb w a b) (hc : Correlated M σ.correlationSymb w a c) (hvu : v ≠ u)
    (hn : r ≤ n) (hk : r ≤ k)
    (hv : ObservedAt M w (σ.vote b v n))
    (hu : ObservedAt M w (σ.vote c u k)) :
    StrictEndingDepthChain M (Correlated M σ.correlationSymb) a w (r + 1) := by
  induction r generalizing w b c v u n k with
  | zero =>
    obtain ⟨V⟩ := minimal_vote h.toBaseProtocol hw hb hn hv
    obtain ⟨U⟩ := minimal_vote h.toBaseProtocol hw hc hk hu
    -- A minimal rank-zero vote is echo-based, or its transfer source lies outside
    -- the observer's row and (by vote monotonicity) inside the row at the vote.
    have classify : ∀ {x}, (X : MinimalVote (M := M) (σ := σ) w a x 0) →
        (⟪w⟫ ⊨[M] σ.echoCertificate X.target x) ∨
          StrictEndingDepthChain M (Correlated M σ.correlationSymb) a w 1 := by
      intro x X
      have hX := predecessor_possible hw X.before
      rcases h.voteZeroBackward hX X.vote with he | ⟨s, _, hls, ht⟩
      · exact Or.inl (quorum_lift hw X.before he)
      · by_cases hs : Correlated M σ.correlationSymb w a s
        · obtain ⟨e, he, hv⟩ := observedAt_iff.mpr ht
          exact False.elim (X.minimal e he s _ hs (Nat.zero_le _) hv)
        · have hmono := h.voteMonotone hw X.before X.vote (Or.inl rfl)
          have hta : Correlated M σ.correlationSymb X.event X.target a :=
            hmono a (h.correlationSymm hw X.correlated)
          have hincl : ∀ y, Correlated M σ.correlationSymb w a y →
              Correlated M σ.correlationSymb X.event a y := by
            intro y hy
            exact h.correlationTrans hX (h.correlationSymm hX hta)
              (hmono y (h.correlationTrans hw (h.correlationSymm hw X.correlated) hy))
          have has : Correlated M σ.correlationSymb X.event a s :=
            h.correlationTrans hX (h.correlationSymm hX hta) hls
          exact Or.inr (strictEndingDepthChain_append
            (strictEndingDepthChain_zero hX ⟨X.target, h.correlationSymm hX hta⟩)
            X.before hw ⟨hincl, s, has, hs⟩ ⟨X.target, X.correlated⟩)
    rcases classify V with hV | hV
    · rcases classify U with hU | hU
      · have hVU := h.correlationTrans hw (h.correlationSymm hw V.correlated) U.correlated
        obtain ⟨e, f, he, hf, hp, hve, huf, hord⟩ := quorum_pair h.toBaseProtocol hw hVU hV hU
        have eq : v = u := by
          rcases hord with hef | hfe | rfl
          · exact (h.echoNonEquivocation (predecessor_possible hw hf) huf
              ((Sat.past _ _ _).mpr ⟨e, hef, hp, hve⟩)).symm
          · exact h.echoNonEquivocation (predecessor_possible hw he) hve
              ((Sat.past _ _ _).mpr ⟨f, hfe, hp.symm, huf⟩)
          · have heq := ((Sat.ofEvent _ _ _).mp hve).1.symm.trans
              ((Sat.ofEvent _ _ _).mp huf).1
            have ha := congrArg (fun e : MaybeEvent S.EventType =>
              match e with | .none => [] | .some x => x.args) heq
            exact (List.cons.inj ha).1
        exact False.elim (hvu eq)
      · exact hU
    · exact hV
  | succ r ih =>
    obtain ⟨V⟩ := minimal_vote h.toBaseProtocol hw hb hn hv
    obtain ⟨U⟩ := minimal_vote h.toBaseProtocol hw hc hk hu
    have hVU := h.correlationTrans hw (h.correlationSymm hw V.correlated) U.correlated
    obtain ⟨e, f, he, hf, hplace, hve, huf, hord⟩ :=
      quorum_pair_before h.toBaseProtocol hw V.before U.before hVU
        (h.voteSuccBackward (predecessor_possible hw V.before) V.vote)
        (h.voteSuccBackward (predecessor_possible hw U.before) U.vote)
    have step : ∀ {v u}, v ≠ u →
        (V : MinimalVote (M := M) (σ := σ) w a v (r + 1)) →
        (U : MinimalVote (M := M) (σ := σ) w a u (r + 1)) →
        ∀ e f, e ≪ V.event → f ≪ U.event →
        (⟪e⟫ ⊨[M] σ.vote V.target v r) →
        (⟪f⟫ ⊨[M] σ.vote U.target u r) → e ≪ f → e.place = f.place →
        StrictEndingDepthChain M (Correlated M σ.correlationSymb) a w (r + 1 + 1) := by
      intro v u hvu V U e f he hf hve huf hef hplace
      have hfw := accessible_trans hw hf U.before
      have hfpos := predecessor_possible hw hfw
      have hVUw := h.correlationTrans hw (h.correlationSymm hw V.correlated) U.correlated
      -- Vote monotonicity at the later vote of the switch: `U.target`'s row at `f`
      -- contains its row at `w`.
      have hsw := h.voteMonotone hw hfw huf
        (Or.inr ⟨V.target, v, hvu, hVUw, (Sat.past _ _ _).mpr ⟨e, hef, hplace, hve⟩⟩)
      have hUa : Correlated M σ.correlationSymb f U.target a :=
        hsw a (h.correlationSymm hw U.correlated)
      have hincl : ∀ y, Correlated M σ.correlationSymb w a y →
          Correlated M σ.correlationSymb f a y := by
        intro y hy
        exact h.correlationTrans hfpos (h.correlationSymm hfpos hUa)
          (hsw y (h.correlationTrans hw (h.correlationSymm hw U.correlated) hy))
      have haV := hincl V.target V.correlated
      have haU := h.correlationSymm hfpos hUa
      have hVU := h.correlationTrans hfpos (h.correlationSymm hfpos haV) haU
      have hPast : ObservedAt M f (σ.vote V.target v r) := ⟨e, hef, hve⟩
      obtain ⟨c, k, hrk, hcU, hcv⟩ := h.voteNonEquivocation hfpos huf
        ((Sat.past _ _ _).mpr ⟨e, hef, hplace, hve⟩) (h.correlationSymm hfpos hVU) hvu
      have hcv := observedAt_iff.mpr hcv
      have hac := h.correlationTrans hfpos haU hcU
      have hnot : ¬ Correlated M σ.correlationSymb w a c := by
        intro hc
        obtain ⟨g, hgf, hgv⟩ := hcv
        exact U.minimal g (accessible_trans (predecessor_possible hw U.before) hgf hf)
          c k hc (by omega) hgv
      have chain := ih hfpos haV hac hvu (Nat.le_refl r) (by omega : r ≤ k) hPast hcv
      exact strictEndingDepthChain_append chain hfw hw ⟨hincl, c, hac, hnot⟩
        ⟨V.target, V.correlated⟩
    rcases hord with hef | hfe | heq
    · exact step hvu V U e f he hf hve huf hef hplace
    · exact step (Ne.symm hvu) U V f e hf he huf hve hfe hplace.symm
    · subst f
      exact False.elim (hvu (vote_value_eq hve huf))

/-- A vote at the depth threshold dominates all conflicting votes in its row. -/
theorem conflicting_rank_lt (h : ProtocolVM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {n k : Nat}
    (hb : Correlated M σ.correlationSymb w a b) (hc : Correlated M σ.correlationSymb w a c) (hvu : v ≠ u)
    (hn : maxDepth M (Correlated M σ.correlationSymb) a ≤ n)
    (hv : ObservedAt M w (σ.vote b v n))
    (hu : ObservedAt M w (σ.vote c u k)) :
    k < maxDepth M (Correlated M σ.correlationSymb) a := by
  by_cases hk : k < maxDepth M (Correlated M σ.correlationSymb) a
  · exact hk
  have hchain := conflict_yields_strict_depth_chain h hw hb hc hvu hn (by omega) hv hu
  have hbound := strictEndingDepthChain_le hchain
  omega

/-- Deliveries observed at a correlated world agree, even with unequal depths. The
learners must be correlated at every final world so that the fast clause's
end-of-time guarantee applies. -/
theorem agreement_at (h : ProtocolVM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b v u : S.Value}
    (habFinal : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hab : Correlated M σ.correlationSymb w a b)
    (hv : ObservedAt M w (σ.deliver a v))
    (hu : ObservedAt M w (σ.deliver b u)) : v = u := by
  have hba := h.correlationSymm hw hab
  have haa := h.correlationTrans hw hab hba
  have hbb := h.correlationTrans hw hba hab
  -- Sequential quorums for `a` and `b` at `w`, from the fast clause's guarantee.
  have hQa : ∀ {e : World P S.EventType},
      (⟪e⟫ ⊨[M] ⤒ᶠ (σ.correlation a a ⇒ᶠ □ᶠ[[a]] Formula.seq)) → SequentialQuorumAt M a w := by
    intro e hg
    have hf := habFinal e.place
    have hpos : (finalWorld M e.place).time ⪯ M.history.val := PreHistory.happensBeforeEq_refl _
    exact sequentialQuorumAt_of_guarantee hw hg
      (h.correlationTrans hpos hf (h.correlationSymm hpos hf))
  have hQb : ∀ {e : World P S.EventType},
      (⟪e⟫ ⊨[M] ⤒ᶠ (σ.correlation b b ⇒ᶠ □ᶠ[[b]] Formula.seq)) → SequentialQuorumAt M b w := by
    intro e hg
    have hf := habFinal e.place
    have hpos : (finalWorld M e.place).time ⪯ M.history.val := PreHistory.happensBeforeEq_refl _
    exact sequentialQuorumAt_of_guarantee hw hg
      (h.correlationTrans hpos (h.correlationSymm hpos hf) hf)
  rcases delivery_cases h.toBaseProtocol hw hv with hca | ⟨hechoa, ea, _, hga⟩
  · rcases delivery_cases h.toBaseProtocol hw hu with hcb | ⟨hechob, eb, _, hgb⟩
    · -- Both deliveries at the decision rank: the depth argument.
      have hv' := quorum_witness hca
      have hu' := quorum_witness hcb
      by_cases heq : v = u
      · exact heq
      apply False.elim
      by_cases hle : maxDepth M (Correlated M σ.correlationSymb) a ≤ maxDepth M (Correlated M σ.correlationSymb) b
      · have hlt := conflicting_rank_lt h hw haa hab heq (by omega) hv' hu'
        omega
      · have hlt := conflicting_rank_lt h hw hbb hba (Ne.symm heq) (by omega) hu' hv'
        omega
    · -- `b` delivered fast, and `a` has an observed `v`-vote.
      exact value_of_echo_unanimity_at h.toBaseProtocol h.voteMonotone hw (hQb hgb) hechob hba
        (quorum_witness hca)
  · rcases delivery_cases h.toBaseProtocol hw hu with hcb | ⟨hechob, _, _, _⟩
    · -- `a` delivered fast, and `b` has an observed `u`-vote.
      exact (value_of_echo_unanimity_at h.toBaseProtocol h.voteMonotone hw (hQa hga) hechoa hab
        (quorum_witness hcb)).symm
    · -- Both fast: a member of `a`'s sequential quorum echoed both values.
      obtain ⟨Q, hQ, hQseq⟩ := hQa hga
      obtain ⟨q, hq⟩ := Semifilter.quorum_nonempty hQ
      have hseq := hQseq q hq
      obtain ⟨e, he, heq, hve⟩ := hechoa q hseq
      obtain ⟨f, hf, hfq, huf⟩ := hechob q hseq
      exact echo_unique_of_sequential h.toBaseProtocol hw hseq he hf heq hfq hve huf

/-- End-of-time agreement when every final participant correlates the learners. -/
theorem agreement (h : ProtocolVM M σ) {a b v u : S.Value}
    (hab : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hv : Occurs M (σ.deliver a v)) (hu : Occurs M (σ.deliver b u)) : v = u := by
  exact agreement_at h (PreHistory.happensBeforeEq_refl _) hab
    (hab (Classical.ofNonempty)) hv hu

/-- Liveness 1. -/
theorem livenessOne (h : ProtocolVM M σ) {l v : S.Value}
    (hLiveQuorum : ∃ Q ∈ (M.learner l).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hUnique : UniqueOccurrence M σ.propose)
    (hObserved : ∃ e ∈ M.history.val,
      (⟪e⟫ ⊨[M] σ.live) ∧ ObservedAt M e (σ.propose v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver l v) := by
  exact ThyHBB4.livenessOne h.toBaseProtocol hLiveQuorum hUnique hObserved p hLive

/-- A delivered value is `UncontestedOrDelivered` throughout its correlation row. -/
theorem uncontestedOrDelivered_of_delivery (h : ProtocolVM M σ) {a b v : S.Value}
    (hab : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b) (q : P)
    (hdel : ObservedAt M (finalWorld M q) (σ.deliver a v)) :
    UncontestedOrDelivered M σ (finalWorld M q) b v := by
  have hw : (finalWorld M q).time ⪯ M.history.val := PreHistory.happensBeforeEq_refl _
  have habq := hab q
  have haa := h.correlationTrans hw habq (h.correlationSymm hw habq)
  intro d u k hdb huv hu
  have had := h.correlationTrans hw habq (h.correlationSymm hw hdb)
  rcases delivery_cases h.toBaseProtocol hw hdel with hcert | ⟨hecho, e, _, hg⟩
  · have hlt := conflicting_rank_lt h hw haa had (Ne.symm huv) (Nat.le_refl _)
      (quorum_witness hcert) hu
    exact ⟨a, by omega, habq, hdel⟩
  · have hf := hab e.place
    have hpos : (finalWorld M e.place).time ⪯ M.history.val := PreHistory.happensBeforeEq_refl _
    have hQa := sequentialQuorumAt_of_guarantee hw hg
      (h.correlationTrans hpos hf (h.correlationSymm hpos hf))
    exact absurd (value_of_echo_unanimity_at h.toBaseProtocol h.voteMonotone hw hQa hecho had hu) huv

/-- Liveness 2. -/
theorem livenessTwo (h : ProtocolVM M σ) {a b v : S.Value}
    (hCorrelation : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hLiveQuorum : ∃ Q ∈ (M.learner b).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hDelivered : Occurs M (σ.deliver a v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver b v) := by
  exact livenessTwo_of_uncontestedOrDelivered h.toBaseProtocol (uncontestedOrDelivered_of_delivery h hCorrelation) hCorrelation hLiveQuorum hDelivered p hLive

/-- Agreement in the paper's modal notation. -/
theorem agreement_modal (h : ProtocolVM M σ) {a b v u : S.Value}
    (hab : ⊨[M] □ᶠ[] (σ.correlation a b)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ
      (♢ᶠ↓[[]] (σ.deliver b u)) ⇒ᶠ (v ≃ᶠ u) := by
  exact occurrence_agreement_iff.mp (agreement h (correlated_final_iff_end.mpr hab))

/-- Liveness 1 in the paper's modal notation. -/
theorem livenessOne_modal (h : ProtocolVM M σ) {l v : S.Value}
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live)
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ⇒ᶠ
      σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) := by
  exact ThyHBB4.livenessOne_modal h.toBaseProtocol hLiveQuorum hUnique

/-- Liveness 2 in the paper's modal notation. -/
theorem livenessTwo_modal (h : ProtocolVM M σ) {a b v : S.Value}
    (hCorrelation : ⊨[M] □ᶠ[] (σ.correlation a b))
    (hLiveQuorum : ⊨[M] □ᶠ[[b]] σ.live) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ σ.live ⇒ᶠ ↕ᶠ (σ.deliver b v) := by
  exact occurrence_liveness_iff.mp (livenessTwo h
    (correlated_final_iff_end.mpr hCorrelation) (quorum_final_iff_end.mpr hLiveQuorum))

end ModalDistribution.Examples.ThyHBB4.VM

namespace ModalDistribution.Examples.ThyHBB4
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

/-- CM ⇒ VM. -/
def ProtocolCM.toVM (h : ProtocolCM M σ) : ProtocolVM M σ :=
  { h.toBaseProtocol with voteMonotone := h.voteMonotone }

end ModalDistribution.Examples.ThyHBB4
