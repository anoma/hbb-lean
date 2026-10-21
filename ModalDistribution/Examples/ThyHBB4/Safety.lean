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

theorem quorum_witness {w : World P S.EventType} {l : S.Value} {φ : Formula S}
    (h : ⟪w⟫ ⊨[M] □ᶠ↓[[l]] φ) : ∃ u, u ≪ w ∧ (⟪u⟫ ⊨[M] φ) := by
  obtain ⟨Q, hQ, h⟩ := quorum_exists_iff.mp h
  obtain ⟨p, hp⟩ := Semifilter.quorum_nonempty hQ
  obtain ⟨u, hu, _, hφ⟩ := h p hp
  exact ⟨u, hu, hφ⟩

/-- Every vote has a proposal of the same value in its causal past. -/
theorem vote_provenance (h : BaseProtocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {l v : S.Value} {n : Nat}
    (hv : ⟪w⟫ ⊨[M] σ.vote l v n) :
    ObservedAt M w (σ.propose v) := by
  have go : ∀ k, ∀ w : World P S.EventType, PreHistory.height w.time = k →
      w.time ⪯ M.history.val → ∀ l v n,
      (⟪w⟫ ⊨[M] σ.vote l v n) →
      (ObservedAt M w (σ.propose v)) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro w hk hw l v n hv
      have liftProposal : ∀ u, u ≪ w →
          (ObservedAt M u (σ.propose v)) →
          (ObservedAt M w (σ.propose v)) := by
        intro u hu hp
        obtain ⟨t, ht, hp⟩ := hp
        exact ⟨t, accessible_trans hw ht hu, hp⟩
      have fromVote : ∀ u, u ≪ w → ∀ l n,
          (⟪u⟫ ⊨[M] σ.vote l v n) →
          (ObservedAt M w (σ.propose v)) := by
        intro u hu l n hv
        exact liftProposal u hu (ih _ (hk ▸ PreHistory.height_lt_of_accessible hu)
          u rfl (predecessor_possible hw hu) l v n hv)
      cases n with
      | zero =>
        rcases h.voteZeroBackward hw hv with he | ⟨s, _, _, ht⟩
        · obtain ⟨u, hu, he⟩ := quorum_witness he
          exact liftProposal u hu (observedAt_iff.mpr (h.echoBackward (predecessor_possible hw hu) he))
        · obtain ⟨u, hu, hv⟩ := observedAt_iff.mpr ht
          exact fromVote u hu s _ hv
      | succ n =>
        obtain ⟨u, hu, hv⟩ := quorum_witness (h.voteSuccBackward hw hv)
        exact fromVote u hu l n hv
  exact go _ w rfl hw l v n hv

/-- Minimal votes are chosen among every target in the observer's row. -/
structure MinimalVote (w : World P S.EventType) (a v : S.Value) (r : Nat) where
  event : World P S.EventType
  target : S.Value
  before : event ≪ w
  correlated : Correlated M σ.correlationSymb w a target
  vote : ⟪event⟫ ⊨[M] σ.vote target v r
  minimal : ∀ u, u ≪ event → ∀ b n, Correlated M σ.correlationSymb w a b → r ≤ n →
    ¬ (⟪u⟫ ⊨[M] σ.vote b v n)

theorem minimal_vote (h : BaseProtocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b v : S.Value} {r n : Nat}
    (hb : Correlated M σ.correlationSymb w a b) (hn : r ≤ n)
    (hv : ObservedAt M w (σ.vote b v n)) :
    Nonempty (MinimalVote (M := M) (σ := σ) w a v r) := by
  let A := fun e : World P S.EventType => e ≪ w ∧
    ∃ b n, Correlated M σ.correlationSymb w a b ∧ r ≤ n ∧ (⟪e⟫ ⊨[M] σ.vote b v n)
  obtain ⟨e, he, hv⟩ := hv
  obtain ⟨e, ⟨hew, b, n, hb, hn, hv⟩, hmin⟩ :=
    exists_causally_minimal A ⟨e, he, b, n, hb, hn, hv⟩
  have minimal : ∀ u, u ≪ e → ∀ b n, Correlated M σ.correlationSymb w a b → r ≤ n →
      ¬ (⟪u⟫ ⊨[M] σ.vote b v n) := by
    intro u hue b n hb hn hv
    exact hmin u hue ⟨accessible_trans hw hue hew, b, n, hb, hn, hv⟩
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
      exact minimal u hue b k hb (by omega) hv'
  subst n
  exact ⟨⟨e, b, hew, hb, hv, minimal⟩⟩

theorem quorum_pair (h : BaseProtocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b : S.Value} {φ ψ : Formula S}
    (hab : Correlated M σ.correlationSymb w a b)
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
    {a b : S.Value} {φ ψ : Formula S} (hab : Correlated M σ.correlationSymb w a b)
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

/-- Sequentiality in a world's past restricts to the past of any earlier world. -/
theorem isSequential_of_accessible {w d : World P S.EventType}
    (hw : w.time ⪯ M.history.val) (hd : d ≪ w) {q : P}
    (hseq : isSequential (Event := S.EventType) q w.time) :
    isSequential (Event := S.EventType) q d.time := by
  intro t₁ t₂ h₁ h₂ hp₁ hp₂
  have h₁' : t₁ ≪ d := h₁
  have h₂' : t₂ ≪ d := h₂
  exact hseq t₁ t₂ (accessible_trans hw h₁' hd) (accessible_trans hw h₂' hd) hp₁ hp₂

/-- The fast-path justification: every participant sequential in the world's past
has echoed `v` there. -/
def SequentialEchoes (M : Model S P) (σ : ProtocolSignature S)
    (w : World P S.EventType) (v : S.Value) : Prop :=
  ∀ q : P, isSequential (Event := S.EventType) q w.time →
    ∃ t, t ≪ w ∧ t.place = q ∧ (⟪t⟫ ⊨[M] σ.echo v)

theorem sequentialEchoes_iff {w : World P S.EventType} {v : S.Value} :
    (⟪w⟫ ⊨[M] □ᶠ[] (Formula.seq ⇒ᶠ ↓ᶠ (σ.echo v))) ↔ SequentialEchoes M σ w v := by
  rw [Sat.boxEmpty]
  constructor
  · intro h q hseq
    have h' := Sat.imp_elim (M := M) (w := ⟨q, †, w.time⟩) (h q) ((Sat.seq M _).mpr hseq)
    obtain ⟨t, ht, htq, he⟩ := (Sat.past M _ _).mp h'
    exact ⟨t, ht, htq, he⟩
  · intro h q
    apply Sat.imp_intro
    intro hseq
    obtain ⟨t, ht, htq, he⟩ := h q ((Sat.seq M _).mp hseq)
    exact (Sat.past M _ _).mpr ⟨t, ht, htq, he⟩

/-- The fast-path justification is inherited by later possible worlds: a
participant sequential later was sequential earlier, and its echo persists. -/
theorem sequentialEchoes_lift {w e : World P S.EventType}
    (hw : w.time ⪯ M.history.val) (he : e ≪ w) {v : S.Value}
    (h : SequentialEchoes M σ e v) : SequentialEchoes M σ w v := by
  intro q hseq
  obtain ⟨t, ht, htq, hecho⟩ := h q (isSequential_of_accessible hw he hseq)
  exact ⟨t, accessible_trans hw ht he, htq, hecho⟩

/-- An `l`-quorum all of whose members are sequential in `w`'s past. -/
def SequentialQuorumAt (M : Model S P) (l : S.Value) (w : World P S.EventType) : Prop :=
  ∃ Q ∈ (M.learner l).quorums, ∀ q ∈ Q, isSequential (Event := S.EventType) q w.time

/-- Sequentiality at the end of time restricts to every possible world. -/
theorem isSequential_of_possible {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {q : P}
    (hseq : isSequential (Event := S.EventType) q M.history.val) :
    isSequential (Event := S.EventType) q w.time := by
  intro t₁ t₂ h₁ h₂ hp₁ hp₂
  have hsub : w.time ⊆ M.history.val :=
    PreHistory.subset_of_happensBeforeEq (fun _ hh => History.subset_of_happensBefore hh) hw
  exact hseq t₁ t₂ (hsub t₁ h₁) (hsub t₂ h₂) hp₁ hp₂

/-- The fast clause's end-of-time guarantee yields, at any possible world, a
sequential `l`-quorum, provided `l` is correlated with itself at the end of time
(at the deliverer's final world). -/
theorem sequentialQuorumAt_of_guarantee {e w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {l : S.Value}
    (hg : ⟪e⟫ ⊨[M] ⤒ᶠ (σ.correlation l l ⇒ᶠ □ᶠ[[l]] Formula.seq))
    (hll : Correlated M σ.correlationSymb (finalWorld M e.place) l l) :
    SequentialQuorumAt M l w := by
  have h1 := (Sat.atEnd M e _).mp hg
  have h2 := Sat.imp_elim (M := M) (w := ⟨e.place, †, M.history.val⟩) h1 hll
  obtain ⟨Q, hQ, hQseq⟩ := (sat_box_singleton_exists M _ l Formula.seq).mp h2
  refine ⟨Q, hQ, fun q hq => ?_⟩
  exact isSequential_of_possible hw ((Sat.seq M _).mp (hQseq q hq))

/-- The two ways a delivery can be justified, lifted to the observer. The fast
justification carries the delivery event, whose final world hosts the end-of-time
guarantee. -/
theorem delivery_cases (h : BaseProtocol M σ)
    {w : World P S.EventType} (hw : w.time ⪯ M.history.val) {a v : S.Value}
    (hd : ObservedAt M w (σ.deliver a v)) :
    (⟪w⟫ ⊨[M] σ.voteCertificate a v (σ.depthBound a)) ∨
    (SequentialEchoes M σ w v ∧
      ∃ e, e ≪ w ∧ (⟪e⟫ ⊨[M] ⤒ᶠ (σ.correlation a a ⇒ᶠ □ᶠ[[a]] Formula.seq))) := by
  obtain ⟨e, he, hdel⟩ := hd
  rcases h.deliverBackward (predecessor_possible hw he) hdel with hc | ⟨hecho, hg⟩
  · exact Or.inl (quorum_lift hw he hc)
  · exact Or.inr ⟨sequentialEchoes_lift hw he (sequentialEchoes_iff.mp hecho), e, he, hg⟩

theorem vote_value_eq {w : World P S.EventType} {l v b u : S.Value} {n k : Nat}
    (hv : ⟪w⟫ ⊨[M] σ.vote l v n) (hu : ⟪w⟫ ⊨[M] σ.vote b u k) : v = u := by
  have he := ((Sat.ofEvent _ _ _).mp hv).1.symm.trans ((Sat.ofEvent _ _ _).mp hu).1
  have ha := congrArg (fun e : MaybeEvent S.EventType =>
    match e with | .none => [] | .some a => a.args) he
  exact (List.cons.inj (List.cons.inj ha).2).1

theorem echo_value_eq {w : World P S.EventType} {v u : S.Value}
    (hv : ⟪w⟫ ⊨[M] σ.echo v) (hu : ⟪w⟫ ⊨[M] σ.echo u) : v = u := by
  have he := ((Sat.ofEvent _ _ _).mp hv).1.symm.trans ((Sat.ofEvent _ _ _).mp hu).1
  have ha := congrArg (fun e : MaybeEvent S.EventType =>
    match e with | .none => [] | .some a => a.args) he
  exact (List.cons.inj ha).1

/-- A participant sequential at `w` cannot have echoed two values in `w`'s past. -/
theorem echo_unique_of_sequential (h : BaseProtocol M σ)
    {w : World P S.EventType} (hw : w.time ⪯ M.history.val) {q : P}
    (hseq : isSequential (Event := S.EventType) q w.time)
    {e f : World P S.EventType} (he : e ≪ w) (hf : f ≪ w)
    (heq : e.place = q) (hfq : f.place = q) {v u : S.Value}
    (hv : ⟪e⟫ ⊨[M] σ.echo v) (hu : ⟪f⟫ ⊨[M] σ.echo u) : v = u := by
  rcases hseq e f he hf heq hfq with hef | hfe | rfl
  · exact (h.echoNonEquivocation (predecessor_possible hw hf) hu
      ((Sat.past _ _ _).mpr ⟨e, hef, heq.trans hfq.symm, hv⟩)).symm
  · exact h.echoNonEquivocation (predecessor_possible hw he) hv
      ((Sat.past _ _ _).mpr ⟨f, hfe, hfq.trans heq.symm, hu⟩)
  · exact echo_value_eq hv hu

/-- A delivered value has an actual proposal in the delivery's causal past, for a
learner correlated (with anything) at the deliverer's final world. On the fast
path the proposal is found through a member of the learner's sequential quorum. -/
theorem deliver_provenance (h : BaseProtocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {l v : S.Value}
    (hll : Correlated M σ.correlationSymb (finalWorld M w.place) l l)
    (hv : ⟪w⟫ ⊨[M] σ.deliver l v) :
    ObservedAt M w (σ.propose v) := by
  rcases h.deliverBackward hw hv with hc | ⟨hecho, hg⟩
  · obtain ⟨e, he, hv⟩ := quorum_witness hc
    obtain ⟨f, hf, hp⟩ := vote_provenance h (predecessor_possible hw he) hv
    exact ⟨f, accessible_trans hw hf he, hp⟩
  · obtain ⟨Q, hQ, hQseq⟩ := sequentialQuorumAt_of_guarantee hw hg hll
    obtain ⟨q, hq⟩ := Semifilter.quorum_nonempty hQ
    obtain ⟨t, ht, _, he⟩ := sequentialEchoes_iff.mp hecho q (hQseq q hq)
    obtain ⟨f, hf, hp⟩ := observedAt_iff.mpr (h.echoBackward (predecessor_possible hw ht) he)
    exact ⟨f, accessible_trans hw hf ht, hp⟩

end ModalDistribution.Examples.ThyHBB4
