import ModalDistribution.Examples.ThyHBB4.Axioms

namespace ModalDistribution.Examples.ThyHBB4

open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped PreHistory Formula

variable {S : Signature} {P : Type} [Nonempty P]

omit [Nonempty P] in
/-- A nonempty collection of event worlds has a causally minimal member. -/
theorem exists_causally_minimal
    (A : World P S.EventType → Prop) (hA : ∃ w, A w) :
    ∃ w, A w ∧ ∀ u, u ≪ w → ¬ A u := by
  classical
  obtain ⟨w, hw⟩ := hA
  have go : ∀ n, ∀ w, PreHistory.height w.time = n → A w →
      ∃ t, A t ∧ ∀ u, u ≪ t → ¬ A u := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro w hn hw
      by_cases h : ∃ u, u ≪ w ∧ A u
      · obtain ⟨u, huw, hu⟩ := h
        exact ih (PreHistory.height u.time)
          (hn ▸ PreHistory.height_lt_of_accessible huw) u rfl hu
      · exact ⟨w, hw, fun u huw hu => h ⟨u, huw, hu⟩⟩
  exact go _ w rfl hw

variable {M : Model S P} {σ : ProtocolSignature S}

theorem past_exists_iff {w : World P S.EventType} {φ : Formula S} :
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] φ) ↔ ∃ u, u ≪ w ∧ (⟪u⟫ ⊨[M] φ) := by
  simp only [Formula.diamondPast, Sat.diamond_nil, Sat.past]
  constructor
  · rintro ⟨p, u, hu, _, hφ⟩
    exact ⟨u, hu, hφ⟩
  · rintro ⟨u, hu, hφ⟩
    exact ⟨u.place, u, hu, rfl, hφ⟩

theorem quorum_exists_iff {w : World P S.EventType} {l : S.Value} {φ : Formula S} :
    (⟪w⟫ ⊨[M] □ᶠ↓[[l]] φ) ↔
      ∃ Q ∈ (M.learner l).quorums, ∀ p ∈ Q,
        ∃ u, u ≪ w ∧ u.place = p ∧ (⟪u⟫ ⊨[M] φ) := by
  simp only [Formula.boxPast, sat_box_singleton_exists, Sat.past]
  rfl

theorem quorum_witness {w : World P S.EventType} {l : S.Value} {φ : Formula S}
    (h : ⟪w⟫ ⊨[M] □ᶠ↓[[l]] φ) : ∃ u, u ≪ w ∧ (⟪u⟫ ⊨[M] φ) := by
  obtain ⟨Q, hQ, h⟩ := quorum_exists_iff.mp h
  obtain ⟨p, hp⟩ := Semifilter.quorum_nonempty hQ
  obtain ⟨u, hu, _, hφ⟩ := h p hp
  exact ⟨u, hu, hφ⟩

theorem predecessor_possible {w u : World P S.EventType}
    (hw : w.time ⪯ M.history.val) (hu : u ≪ w) : u.time ⪯ M.history.val :=
  (PreHistory.happensBeforeEq_iff _ _).2
    (Or.inl (accessible_happensBefore_history hw hu))

/-- Every vote has a proposal of the same value in its causal past. -/
theorem vote_provenance (h : BaseProtocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {l s v : S.Value} {n : Nat}
    (hv : ⟪w⟫ ⊨[M] σ.vote l s v n) :
    ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v) := by
  have go : ∀ k, ∀ w : World P S.EventType, PreHistory.height w.time = k →
      w.time ⪯ M.history.val → ∀ l s v n,
      (⟪w⟫ ⊨[M] σ.vote l s v n) →
      (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v)) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro w hk hw l s v n hv
      have liftProposal : ∀ u, u ≪ w →
          (⟪u⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v)) →
          (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v)) := by
        intro u hu hp
        obtain ⟨t, ht, hp⟩ := past_exists_iff.mp hp
        exact past_exists_iff.mpr ⟨t, accessible_trans hw ht hu, hp⟩
      have fromVote : ∀ u, u ≪ w → ∀ l s n,
          (⟪u⟫ ⊨[M] σ.vote l s v n) →
          (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v)) := by
        intro u hu l s n hv
        exact liftProposal u hu (ih _ (hk ▸ PreHistory.height_lt_of_accessible hu)
          u rfl (predecessor_possible hw hu) l s v n hv)
      cases n with
      | zero =>
        rcases h.voteZeroBackward hw hv with ⟨_, he⟩ | ht
        · obtain ⟨u, hu, he⟩ := quorum_witness he
          exact liftProposal u hu (h.echoBackward (predecessor_possible hw hu) he)
        · obtain ⟨u, hu, hv⟩ := quorum_witness ht
          obtain ⟨s', hv⟩ := (Sat.exists_iff _ _).mp hv
          exact fromVote u hu _ s' _ hv
      | succ n =>
        obtain ⟨u, hu, hv⟩ := quorum_witness (h.voteSuccBackward hw hv)
        exact fromVote u hu l s n hv
  exact go _ w rfl hw l s v n hv

/-- Minimal votes are chosen among every target in the observer's row. -/
structure MinimalVote (w : World P S.EventType) (a v : S.Value) (r : Nat) where
  event : World P S.EventType
  target : S.Value
  source : S.Value
  before : event ≪ w
  correlated : Corr M σ w a target
  vote : ⟪event⟫ ⊨[M] σ.vote target source v r
  minimal : ∀ u, u ≪ event → ∀ b s n, Corr M σ w a b → r ≤ n →
    ¬ (⟪u⟫ ⊨[M] σ.vote b s v n)

theorem minimal_vote (h : BaseProtocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b v : S.Value} {r n : Nat}
    (hb : Corr M σ w a b) (hn : r ≤ n)
    (hv : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.voteFromSomeSource b v n)) :
    Nonempty (MinimalVote (M := M) (σ := σ) w a v r) := by
  let A := fun e : World P S.EventType => e ≪ w ∧
    ∃ b s n, Corr M σ w a b ∧ r ≤ n ∧ (⟪e⟫ ⊨[M] σ.vote b s v n)
  obtain ⟨e, he, hv⟩ := past_exists_iff.mp hv
  obtain ⟨s, hv⟩ := (Sat.exists_iff _ _).mp hv
  obtain ⟨e, ⟨hew, b, s, n, hb, hn, hv⟩, hmin⟩ :=
    exists_causally_minimal A ⟨e, he, b, s, n, hb, hn, hv⟩
  have minimal : ∀ u, u ≪ e → ∀ b s n, Corr M σ w a b → r ≤ n →
      ¬ (⟪u⟫ ⊨[M] σ.vote b s v n) := by
    intro u hue b s n hb hn hv
    exact hmin u hue ⟨accessible_trans hw hue hew, b, s, n, hb, hn, hv⟩
  have hnr : n = r := by
    by_cases hne : n = r
    · exact hne
    apply False.elim
    have hlt : r < n := by omega
    cases n with
    | zero => omega
    | succ k =>
      obtain ⟨u, hue, hv'⟩ := quorum_witness
        (h.voteSuccBackward (predecessor_possible hw hew) hv)
      exact minimal u hue b s k hb (by omega) hv'
  subst n
  exact ⟨⟨e, b, s, hew, hb, hv, minimal⟩⟩

theorem quorum_pair (h : BaseProtocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b : S.Value} {φ ψ : Formula S}
    (hab : Corr M σ w a b)
    (hφ : ⟪w⟫ ⊨[M] □ᶠ↓[[a]] φ) (hψ : ⟪w⟫ ⊨[M] □ᶠ↓[[b]] ψ) :
    ∃ e f, e ≪ w ∧ f ≪ w ∧ e.place = f.place ∧
      (⟪e⟫ ⊨[M] φ) ∧ (⟪f⟫ ⊨[M] ψ) ∧ (e ≪ f ∨ f ≪ e ∨ e = f) := by
  obtain ⟨Q, hQ, hφ⟩ := quorum_exists_iff.mp hφ
  obtain ⟨T, hT, hψ⟩ := quorum_exists_iff.mp hψ
  have hs := h.correlationSeq hw hab
  have hs' := (sat_diamond_pair_iff (M := M) (w := w) (l := a) (l' := b)
    (φ := Formula.seq)).mp hs
  obtain ⟨p, hp, hseq⟩ := hs' Q hQ T hT
  obtain ⟨e, he, hep, hφ⟩ := hφ p hp.1
  obtain ⟨f, hf, hfp, hψ⟩ := hψ p hp.2
  exact ⟨e, f, he, hf, hep.trans hfp.symm, hφ, hψ, hseq e f he hf hep hfp⟩

theorem quorum_pair_before (h : BaseProtocol M σ) {w x y : World P S.EventType}
    (hw : w.time ⪯ M.history.val) (hx : x ≪ w) (hy : y ≪ w)
    {a b : S.Value} {φ ψ : Formula S} (hab : Corr M σ w a b)
    (hφ : ⟪x⟫ ⊨[M] □ᶠ↓[[a]] φ) (hψ : ⟪y⟫ ⊨[M] □ᶠ↓[[b]] ψ) :
    ∃ e f, e ≪ x ∧ f ≪ y ∧ e.place = f.place ∧
      (⟪e⟫ ⊨[M] φ) ∧ (⟪f⟫ ⊨[M] ψ) ∧ (e ≪ f ∨ f ≪ e ∨ e = f) := by
  obtain ⟨Q, hQ, hφ⟩ := quorum_exists_iff.mp hφ
  obtain ⟨T, hT, hψ⟩ := quorum_exists_iff.mp hψ
  obtain ⟨p, hp, hseq⟩ :=
    (sat_diamond_pair_iff (M := M) (w := w) (l := a) (l' := b)
      (φ := Formula.seq)).mp (h.correlationSeq hw hab) Q hQ T hT
  obtain ⟨e, he, hep, hφ⟩ := hφ p hp.1
  obtain ⟨f, hf, hfp, hψ⟩ := hψ p hp.2
  exact ⟨e, f, he, hf, hep.trans hfp.symm, hφ, hψ,
    hseq e f (accessible_trans hw he hx) (accessible_trans hw hf hy) hep hfp⟩

theorem quorum_lift {w e : World P S.EventType}
    (hw : w.time ⪯ M.history.val) (he : e ≪ w) {a : S.Value} {φ : Formula S}
    (hφ : ⟪e⟫ ⊨[M] □ᶠ↓[[a]] φ) : ⟪w⟫ ⊨[M] □ᶠ↓[[a]] φ := by
  obtain ⟨Q, hQ, hφ⟩ := quorum_exists_iff.mp hφ
  apply quorum_exists_iff.mpr
  refine ⟨Q, hQ, ?_⟩
  intro p hp
  obtain ⟨f, hf, hfp, hφ⟩ := hφ p hp
  exact ⟨f, accessible_trans hw hf he, hfp, hφ⟩

/-- An observed delivery has an observed vote at the delivery-certificate rank. -/
theorem observed_vote_of_observed_delivery (h : BaseProtocol M σ)
    {w : World P S.EventType} (hw : w.time ⪯ M.history.val) {a v : S.Value}
    (hd : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver a v)) :
    ⟪w⟫ ⊨[M] ♢ᶠ↓[[]]
      (σ.voteFromSomeSource a v (maxDepth M (Corr M σ) a + 1)) := by
  obtain ⟨e, he, hdel⟩ := past_exists_iff.mp hd
  exact past_exists_iff.mpr (quorum_witness
    (quorum_lift hw he (h.deliverBackward (predecessor_possible hw he) hdel)))

theorem vote_value_eq {w : World P S.EventType} {l s v b t u : S.Value} {n k : Nat}
    (hv : ⟪w⟫ ⊨[M] σ.vote l s v n) (hu : ⟪w⟫ ⊨[M] σ.vote b t u k) : v = u := by
  have he := ((Sat.ofEvent _ _ _).mp hv).1.symm.trans ((Sat.ofEvent _ _ _).mp hu).1
  have ha := congrArg (fun e : MaybeEvent S.EventType =>
    match e with | .none => [] | .some a => a.args) he
  exact (List.cons.inj (List.cons.inj (List.cons.inj ha).2).2).1

/-- A delivered value has an actual proposal in the delivery's causal past. -/
theorem deliver_provenance (h : BaseProtocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {l v : S.Value}
    (hv : ⟪w⟫ ⊨[M] σ.deliver l v) :
    ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v) := by
  obtain ⟨e, he, hv⟩ := quorum_witness (h.deliverBackward hw hv)
  obtain ⟨s, hv⟩ := (Sat.exists_iff _ _).mp hv
  obtain ⟨f, hf, hp⟩ := past_exists_iff.mp
    (vote_provenance h (predecessor_possible hw he) hv)
  exact past_exists_iff.mpr ⟨f, accessible_trans hw hf he, hp⟩


end ModalDistribution.Examples.ThyHBB4
