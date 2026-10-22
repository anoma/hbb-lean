import ModalDistribution.LowerBound.Theorem
import ModalDistribution.Examples.ThyHBB4B

/-!
# HBB4 as a `Protocol`

The budgeted HBB4 theory `ThyHBB4B` (decision rank = static budget `depthBound`)
instantiates the protocol notion of `Statement.lean`:

* `executions`: the histories all of whose events satisfy HBB4's *local* rules
  (`LocalRules`) — the backward rules with certificate-based delivery (the fast
  path's end-of-time guarantee is not local, so the fast path is left out: this
  is HBB4's slow path) and the two non-equivocation rules. They are stated
  directly in terms of a world's causal past, the topology and the correlation
  relation, so locality (`local_closure`) and freedom of proposals
  (`propose_free`) are immediate.
* `env`: `correlationSeq` (`EnvOK`), coherence of `⋈` (`Coherent`) and dominance
  of the budget over the realized depth.
* `fair`: `ThyLive` together with the forward rules (the obligations live
  participants discharge).

Correctness (`Protocol.Correct`) follows from `ThyHBB4B.CM.agreement`,
`.livenessOne`, `.livenessTwo`. For agreement, which must hold without fairness,
the model's `live` designation is first erased (`stripLive`): with nobody live,
`ThyLive` and the forward rules hold vacuously, and agreement does not depend on
`live`.

What is **not** proved here is `fair_completion` — that every `env` execution of
the local rules extends to a fair one with a prescribed live set — a genuine
nonvacuity theorem about HBB4 (an operational completion construction). It is
taken as a hypothesis `hcomp` of `hbb4Protocol`, and `hbb4_protocol_depth_bound`
derives from `depth_lower_bound`: under that hypothesis, budget-`B` HBB4 cannot
deliver, on an honest `Q`-only branch, below depth `B`.
-/

namespace ModalDistribution.LowerBound.HBB4
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples
open ModalDistribution.Examples.ThyHBB4B
open ModalDistribution.LowerBound
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]

/-- The budgeted reading of the vocabulary, forgetting the budget: the
`ThyHBB4.ProtocolSignature` the protocol notion of `Statement.lean` is stated
over. Formulas built from either reading coincide definitionally. -/
def _root_.ModalDistribution.Examples.ThyHBB4B.ProtocolSignature.toBase
    (σ : ThyHBB4B.ProtocolSignature S) : ThyHBB4.ProtocolSignature S where
  liveSymb := σ.liveSymb
  correlationSymb := σ.correlationSymb
  proposeSymb := σ.proposeSymb
  echoSymb := σ.echoSymb
  voteSymb := σ.voteSymb
  deliverSymb := σ.deliverSymb

/-- Distinctness of the event symbols used by the local rules. -/
structure DistinctSymbols (σ : ProtocolSignature S) : Prop where
  propose_ne_echo : σ.proposeSymb ≠ σ.echoSymb
  propose_ne_vote : ∀ n, σ.proposeSymb ≠ σ.voteSymb n
  propose_ne_deliver : σ.proposeSymb ≠ σ.deliverSymb

/-- A quorum of participants each with an event `E` in the past of `w`. -/
def HasCert (T : Topology S P) (l : S.Value) (w : World P S.EventType) (E : S.EventType) : Prop :=
  ∃ O ∈ (T l).quorums, ∀ p ∈ O, ∃ t ∈ w.time, t.place = p ∧ t.event = .some E

/-- HBB4's local rules (slow path), stated on a history over a topology and a
correlation relation. -/
structure LocalRules (σ : ProtocolSignature S) (H : PreHistory P S.EventType)
    (T : Topology S P) (κ : Correlation S P) : Prop where
  echo : ∀ w ∈ H, ∀ v : S.Value, w.event = .some ⟨σ.echoSymb, [v]⟩ →
    ∃ t ∈ w.time, t.event = .some ⟨σ.proposeSymb, [v]⟩
  voteZero : ∀ w ∈ H, ∀ l v : S.Value, w.event = .some ⟨σ.voteSymb 0, [l, v]⟩ →
    HasCert T l w ⟨σ.echoSymb, [v]⟩ ∨
      ∃ s m, κ w.place w.time l s ∧ ∃ t ∈ w.time, t.event = .some ⟨σ.voteSymb m, [s, v]⟩
  voteSucc : ∀ w ∈ H, ∀ (l v : S.Value) (n : Nat), w.event = .some ⟨σ.voteSymb (n + 1), [l, v]⟩ →
    HasCert T l w ⟨σ.voteSymb n, [l, v]⟩
  deliver : ∀ w ∈ H, ∀ l v : S.Value, w.event = .some ⟨σ.deliverSymb, [l, v]⟩ →
    HasCert T l w ⟨σ.voteSymb (σ.depthBound l), [l, v]⟩
  echoNE : ∀ w ∈ H, ∀ v u : S.Value, w.event = .some ⟨σ.echoSymb, [v]⟩ →
    (∃ t ∈ w.time, t.place = w.place ∧ t.event = .some ⟨σ.echoSymb, [u]⟩) → v = u
  voteNE : ∀ w ∈ H, ∀ (l b v u : S.Value) (n : Nat), w.event = .some ⟨σ.voteSymb n, [l, v]⟩ →
    (∃ t ∈ w.time, t.place = w.place ∧ t.event = .some ⟨σ.voteSymb n, [b, u]⟩) →
    κ w.place w.time l b → u ≠ v →
    ∃ c m, n < m ∧ κ w.place w.time l c ∧ ∃ t ∈ w.time, t.event = .some ⟨σ.voteSymb m, [c, v]⟩

/-- The forward rules of HBB4 (obligations of live participants). -/
structure ForwardRules (M : Model S P) (σ : ProtocolSignature S) : Prop where
  echoForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {v},
    (⟪w⟫ ⊨[M] σ.live) → (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v)) → ∃ u, (⟪w⟫ ⊨[M] ↕ᶠ (σ.echo u))
  voteZeroEchoForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l v},
    (⟪w⟫ ⊨[M] σ.live) → UncontestedOrDelivered M σ (finalWorld M w.place) l v →
    (⟪w⟫ ⊨[M] σ.echoCertificate l v) → (⟪w⟫ ⊨[M] ↕ᶠ (σ.vote l v 0))
  voteZeroTransferForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l s v},
    (⟪w⟫ ⊨[M] σ.live) → UncontestedOrDelivered M σ (finalWorld M w.place) l v →
    Correlated M σ.correlationSymb (finalWorld M w.place) l s →
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.vote s v (σ.depthBound s))) → (⟪w⟫ ⊨[M] ↕ᶠ (σ.vote l v 0))
  voteSuccForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l v n},
    n < σ.depthBound l → (⟪w⟫ ⊨[M] σ.live) → UncontestedOrDelivered M σ (finalWorld M w.place) l v →
    (⟪w⟫ ⊨[M] σ.voteCertificate l v n) → (⟪w⟫ ⊨[M] ↕ᶠ (σ.vote l v (n + 1)))
  deliverForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l v},
    (⟪w⟫ ⊨[M] σ.live) → (⟪w⟫ ⊨[M] σ.voteCertificate l v (σ.depthBound l)) →
    (⟪w⟫ ⊨[M] ↕ᶠ (σ.deliver l v))

variable (σ : ProtocolSignature S)

/-- The environment assumptions of budgeted HBB4. -/
def Env (M : Model S P) : Prop :=
  EnvOK σ.toBase M ∧ Coherent σ.toBase M ∧
    ∀ l, maxDepth M (Correlated M σ.correlationSymb) l ≤ σ.depthBound l

/-- Fairness: the liveness theory and the forward rules. -/
def Fair (M : Model S P) : Prop := (M ⊨ᵀ ThyLive σ.liveSymb) ∧ ForwardRules M σ

/-! ## Bridging satisfaction and the local rules -/

variable {σ}

theorem ofEvent_iff' {M : Model S P} {t : World P S.EventType} {E : S.EventType} :
    (⟪t⟫ ⊨[M] Formula.ofEvent E) ↔ t.event = .some E ∧ t ∈ M.history.val := ofEvent_iff

/-- At a possible world, events of the past are in the history. -/
theorem past_mem {M : Model S P} {w t : World P S.EventType} (hw : w.time ⪯ M.history.val)
    (ht : t ≪ w) : t ∈ M.history.val := by
  rcases (PreHistory.happensBeforeEq_iff _ _).1 hw with hlt | heq
  · exact History.subset_of_happensBefore (H := M.history) hlt t ht
  · rw [← heq]; exact ht

theorem observed_iff {M : Model S P} {w : World P S.EventType} (hw : w.time ⪯ M.history.val)
    (E : S.EventType) :
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (Formula.ofEvent E)) ↔ ∃ t ∈ w.time, t.event = .some E := by
  rw [← observedAt_iff]
  constructor
  · rintro ⟨t, ht, hs⟩; exact ⟨t, ht, (ofEvent_iff.mp hs).1⟩
  · rintro ⟨t, ht, he⟩; exact ⟨t, ht, ofEvent_iff.mpr ⟨he, past_mem hw ht⟩⟩

theorem cert_iff {M : Model S P} {w : World P S.EventType} (hw : w.time ⪯ M.history.val)
    (l : S.Value) (E : S.EventType) :
    (⟪w⟫ ⊨[M] □ᶠ↓[[l]] (Formula.ofEvent E)) ↔ HasCert M.learner l w E := by
  rw [quorum_exists_iff]
  constructor
  · rintro ⟨O, hO, h⟩
    refine ⟨O, hO, fun p hp => ?_⟩
    obtain ⟨u, hu, hup, hs⟩ := h p hp
    exact ⟨u, hu, hup, (ofEvent_iff.mp hs).1⟩
  · rintro ⟨O, hO, h⟩
    refine ⟨O, hO, fun p hp => ?_⟩
    obtain ⟨u, hu, hup, he⟩ := h p hp
    exact ⟨u, hu, hup, ofEvent_iff.mpr ⟨he, past_mem hw hu⟩⟩

theorem past_iff {M : Model S P} {w : World P S.EventType} (hw : w.time ⪯ M.history.val)
    (E : S.EventType) :
    (⟪w⟫ ⊨[M] ↓ᶠ (Formula.ofEvent E)) ↔ ∃ t ∈ w.time, t.place = w.place ∧ t.event = .some E := by
  rw [Sat.past]
  constructor
  · rintro ⟨t, ht, htp, hs⟩; exact ⟨t, ht, htp, (ofEvent_iff.mp hs).1⟩
  · rintro ⟨t, ht, htp, he⟩; exact ⟨t, ht, htp, ofEvent_iff.mpr ⟨he, past_mem hw ht⟩⟩

theorem correlated_corrOf {M : Model S P} (w : World P S.EventType) (a b : S.Value) :
    Correlated M σ.correlationSymb w a b ↔ corrOf σ.toBase M w.place w.time a b := Iff.rfl

/-- The local rules, environment assumptions, liveness theory and forward rules
together make a `ThyHBB4B.ProtocolCM` model. -/
theorem toCM {M : Model S P} (hloc : LocalRules σ M.history.val M.learner (corrOf σ.toBase M))
    (henv : Env σ M) (hlive : M ⊨ᵀ ThyLive σ.liveSymb) (hfwd : ForwardRules M σ) :
    ProtocolCM M σ where
  thyLive := hlive
  depthBound_dominates := henv.2.2
  echoBackward := by
    intro w hw v he
    obtain ⟨hev, hmem⟩ := ofEvent_iff.mp he
    exact (observed_iff hw _).mpr (hloc.echo w hmem v hev)
  voteZeroBackward := by
    intro w hw l v hv
    obtain ⟨hev, hmem⟩ := ofEvent_iff.mp hv
    rcases hloc.voteZero w hmem l v hev with h | ⟨s, m, hκ, h⟩
    · exact Or.inl ((cert_iff hw _ _).mpr h)
    · exact Or.inr ⟨s, m, hκ, (observed_iff hw _).mpr h⟩
  voteSuccBackward := by
    intro w hw l v n hv
    obtain ⟨hev, hmem⟩ := ofEvent_iff.mp hv
    exact (cert_iff hw _ _).mpr (hloc.voteSucc w hmem l v n hev)
  deliverBackward := by
    intro w hw l v hv
    obtain ⟨hev, hmem⟩ := ofEvent_iff.mp hv
    exact Or.inl ((cert_iff hw _ _).mpr (hloc.deliver w hmem l v hev))
  echoNonEquivocation := by
    intro w hw v u hv hu
    obtain ⟨hev, hmem⟩ := ofEvent_iff.mp hv
    exact hloc.echoNE w hmem v u hev ((past_iff hw _).mp hu)
  voteNonEquivocation := by
    intro w hw l b v u n hv hu hκ hne
    obtain ⟨hev, hmem⟩ := ofEvent_iff.mp hv
    obtain ⟨c, m, hm, hκc, h⟩ := hloc.voteNE w hmem l b v u n hev ((past_iff hw _).mp hu) hκ hne
    exact ⟨c, m, hm, hκc, (observed_iff hw _).mpr h⟩
  correlationSeq := henv.1
  correlationSymm := henv.2.1.symm
  correlationTrans := henv.2.1.trans
  correlationPast := henv.2.1.past
  echoForward := hfwd.echoForward
  voteZeroEchoForward := hfwd.voteZeroEchoForward
  voteZeroTransferForward := hfwd.voteZeroTransferForward
  voteSuccForward := hfwd.voteSuccForward
  deliverForward := hfwd.deliverForward
  causalMonotone := henv.2.1.mono

/-! ## Erasing the live designation -/

variable (σ)

/-- The model with nobody live. -/
def stripLive (M : Model S P) : Model S P :=
  { M with predInterp := fun p h => fun x => x ∈ M.predInterp p h ∧ x ≠ ⟨σ.liveSymb, []⟩ }

variable {σ}

theorem stripLive_corrOf (M : Model S P) : corrOf σ.toBase (stripLive σ M) = corrOf σ.toBase M := by
  funext p h a b
  apply propext
  show (⟨σ.correlationSymb, [a, b]⟩ : S.AtomicPredType) ∈ M.predInterp p h ∧
      (⟨σ.correlationSymb, [a, b]⟩ : S.AtomicPredType) ≠ ⟨σ.liveSymb, []⟩ ↔
    (⟨σ.correlationSymb, [a, b]⟩ : S.AtomicPredType) ∈ M.predInterp p h
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun e => absurd (congrArg Signature.AtomicPred.args e) (by simp)⟩

theorem stripLive_correlated (M : Model S P) (s : S.PredSymb) (w : World P S.EventType)
    (a b : S.Value) : Correlated (stripLive σ M) s w a b ↔ Correlated M s w a b := by
  show (⟨s, [a, b]⟩ : S.AtomicPredType) ∈ M.predInterp w.place w.time ∧
      (⟨s, [a, b]⟩ : S.AtomicPredType) ≠ ⟨σ.liveSymb, []⟩ ↔
    (⟨s, [a, b]⟩ : S.AtomicPredType) ∈ M.predInterp w.place w.time
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun e => absurd (congrArg Signature.AtomicPred.args e) (by simp)⟩

theorem stripLive_correlated_eq (M : Model S P) (s : S.PredSymb) :
    Correlated (stripLive σ M) s = Correlated M s := by
  funext w a b
  exact propext (stripLive_correlated M s w a b)

theorem stripLive_not_live (M : Model S P) (w : World P S.EventType) :
    ¬ (⟪w⟫ ⊨[stripLive σ M] σ.live) := by
  rintro ⟨_, h⟩
  exact h rfl

theorem stripLive_thyLive (M : Model S P) :
    Theory.Valid (M := stripLive σ M) (ThyLive σ.liveSymb) := by
  intro ax hax w _
  rcases hax with rfl | rfl | ⟨ls, φ, _, rfl⟩ | ⟨ls, φ, _, rfl⟩
  · show ⟪w⟫ ⊨[stripLive σ M] ((Formula.predicate0 σ.liveSymb) ⇔ᶠ ⤒ᶠ (Formula.predicate0 σ.liveSymb))
    apply Sat.and_intro
    · apply Sat.imp_intro
      intro h
      exact absurd h (stripLive_not_live M w)
    · apply Sat.imp_intro
      intro h
      exact absurd ((Sat.atEnd _ _ _).mp h) (stripLive_not_live M _)
  · apply Sat.imp_intro
    intro h
    exact absurd h (stripLive_not_live M w)
  · apply Sat.imp_intro
    intro _
    apply Sat.imp_intro
    intro h
    exact absurd h (stripLive_not_live M w)
  · apply Sat.imp_intro
    intro _
    apply Sat.imp_intro
    intro h
    exact absurd h (stripLive_not_live M w)

theorem stripLive_forward (M : Model S P) : ForwardRules (stripLive σ M) σ where
  echoForward := by intro w _ v h _; exact absurd h (stripLive_not_live M w)
  voteZeroEchoForward := by intro w _ l v h _ _; exact absurd h (stripLive_not_live M w)
  voteZeroTransferForward := by intro w _ l s v h _ _ _; exact absurd h (stripLive_not_live M w)
  voteSuccForward := by intro w _ l v n _ h _ _; exact absurd h (stripLive_not_live M w)
  deliverForward := by intro w _ l v h _; exact absurd h (stripLive_not_live M w)

theorem stripLive_envOK {M : Model S P} (h : EnvOK σ.toBase M) : EnvOK σ.toBase (stripLive σ M) := by
  intro w hw a b hab
  have := h hw ((stripLive_correlated M _ w a b).mp hab)
  exact this

theorem stripLive_coherent {M : Model S P} (h : Coherent σ.toBase M) :
    Coherent σ.toBase (stripLive σ M) where
  symm := by
    intro w hw a b hab
    rw [stripLive_correlated] at hab ⊢
    exact h.symm hw hab
  trans := by
    intro w hw a b c h1 h2
    rw [stripLive_correlated] at h1 h2 ⊢
    exact h.trans hw h1 h2
  past := by
    intro w hw a b hab u hu hp
    rw [stripLive_correlated] at hab ⊢
    exact h.past hw hab hu hp
  mono := by
    intro w hw a b hab u hu
    rw [stripLive_correlated] at hab ⊢
    exact h.mono hw hab hu

theorem stripLive_maxDepth (M : Model S P) (l : S.Value) :
    maxDepth (stripLive σ M) (Correlated (stripLive σ M) σ.correlationSymb) l =
      maxDepth M (Correlated M σ.correlationSymb) l := by
  rw [stripLive_correlated_eq]
  apply Nat.le_antisymm
  · exact le_maxDepth (M := M) (maxDepth_attained (stripLive σ M) _ l)
  · exact le_maxDepth (M := stripLive σ M) (maxDepth_attained M _ l)

theorem stripLive_env {M : Model S P} (h : Env σ M) : Env σ (stripLive σ M) :=
  ⟨stripLive_envOK h.1, stripLive_coherent h.2.1, fun l => by rw [stripLive_maxDepth]; exact h.2.2 l⟩

/-! ## The protocol -/

/-- The fair-completion property of budgeted HBB4, assumed. -/
def Completion (σ : ThyHBB4B.ProtocolSignature S) : Prop :=
  ∀ M : Model S P, LocalRules σ M.history.val M.learner (corrOf σ.toBase M) → Env σ M →
    ∀ Live : Set P, (∀ p ∈ Live, isSequential (Event := S.EventType) p M.history.val) →
    ∃ M' : Model S P, LocalRules σ M'.history.val M'.learner (corrOf σ.toBase M') ∧
      Fair σ M' ∧ Env σ M' ∧
      M'.learner = M.learner ∧ corrOf σ.toBase M' = corrOf σ.toBase M ∧
      (∀ p h, IsLive σ.toBase M' p h ↔ p ∈ Live) ∧
      M.history.val ⊆ M'.history.val ∧
      ∀ w ∈ M'.history.val, w ∉ M.history.val →
        w.place ∈ Live ∧ ∀ v : S.Value, w.event ≠ .some ⟨σ.proposeSymb, [v]⟩

variable (σ)

/-- **Budgeted HBB4 as a protocol**, given its fair-completion property. -/
def hbb4Protocol (hdist : DistinctSymbols σ) (hcomp : Completion (P := P) σ) :
    Protocol S P σ.toBase where
  executions := fun M => LocalRules σ M.history.val M.learner (corrOf σ.toBase M)
  env := Env σ
  fair := Fair σ
  fair_sequential := by
    intro M hf p hl
    have hax := thyLive_liveSeq hf.1 (t := (p, †, M.history.val)) (PreHistory.happensBeforeEq_refl _)
    have hs := Sat.imp_elim M (p, †, M.history.val) hax hl
    exact (Sat.seq M _).mp hs
  fair_observes := by
    intro M hf p hl w hw E hE hlw
    have hax := thyLive_knowledgeDiamond hf.1 [] (Formula.ofEvent E) (KnowledgeBody.event E)
      (t := (p, †, M.history.val)) (PreHistory.happensBeforeEq_refl _)
    have hprem : ⟪(p, †, M.history.val)⟫ ⊨[M] ⤒ᶠ (♢ᶠ↓[[]] ((Formula.predicate0 σ.liveSymb) ∧ᶠ Formula.ofEvent E)) := by
      apply (Sat.atEnd M _ _).mpr
      apply observedAt_iff.mp
      exact ⟨w, hw, Sat.and_intro M w hlw (ofEvent_iff.mpr ⟨hE, hw⟩)⟩
    have h1 := Sat.imp_elim M _ hax hprem
    have h2 := Sat.imp_elim M _ h1 hl
    obtain ⟨e, he, hep, hs⟩ := (Sat.sometime M _ _).mp h2
    exact ⟨e, he, hep, observedAt_iff.mpr hs⟩
  local_closure := by
    intro M h
    show LocalRules σ M.history.val M.learner (corrOf σ.toBase M)
    have get : ∀ w ∈ M.history.val, ∀ E, w.event = .some E →
        ∃ M' : Model S P, LocalRules σ M'.history.val M'.learner (corrOf σ.toBase M') ∧
          M'.learner = M.learner ∧ corrOf σ.toBase M' = corrOf σ.toBase M ∧ w ∈ M'.history.val := by
      intro w hw E hE
      obtain ⟨M', hM', hT, hκ, hw'⟩ := h w hw E hE
      exact ⟨M', hM', hT, hκ, hw'⟩
    exact {
      echo := by
        intro w hw v hev
        obtain ⟨M', hM', _, _, hw'⟩ := get w hw _ hev
        exact hM'.echo w hw' v hev
      voteZero := by
        intro w hw l v hev
        obtain ⟨M', hM', hT, hκ, hw'⟩ := get w hw _ hev
        have := hM'.voteZero w hw' l v hev
        rw [hT, hκ] at this
        exact this
      voteSucc := by
        intro w hw l v n hev
        obtain ⟨M', hM', hT, _, hw'⟩ := get w hw _ hev
        have := hM'.voteSucc w hw' l v n hev
        rw [hT] at this
        exact this
      deliver := by
        intro w hw l v hev
        obtain ⟨M', hM', hT, _, hw'⟩ := get w hw _ hev
        have := hM'.deliver w hw' l v hev
        rw [hT] at this
        exact this
      echoNE := by
        intro w hw v u hev hpast
        obtain ⟨M', hM', _, _, hw'⟩ := get w hw _ hev
        exact hM'.echoNE w hw' v u hev hpast
      voteNE := by
        intro w hw l b v u n hev hpast hκb hne
        obtain ⟨M', hM', _, hκ, hw'⟩ := get w hw _ hev
        rw [← hκ] at hκb
        have := hM'.voteNE w hw' l b v u n hev hpast hκb hne
        rw [hκ] at this
        exact this }
  propose_free := by
    intro M M' hM hT hpred w v hev hiff
    have hκ : corrOf σ.toBase M' = corrOf σ.toBase M := by
      funext p h a b
      show ((⟨σ.correlationSymb, [a, b]⟩ : S.AtomicPredType) ∈ M'.predInterp p h) =
        ((⟨σ.correlationSymb, [a, b]⟩ : S.AtomicPredType) ∈ M.predInterp p h)
      rw [hpred]
    have hM' : LocalRules σ M.history.val M.learner (corrOf σ.toBase M) := hM
    show LocalRules σ M'.history.val M'.learner (corrOf σ.toBase M')
    rw [hT, hκ]
    have hnot : ∀ (t : World P S.EventType) (E : S.EventType), t ∈ M'.history.val →
        t.event = .some E → E.sym ≠ σ.proposeSymb → t ∈ M.history.val := by
      intro t E ht hE hsym
      rcases (hiff t).mp ht with ht | rfl
      · exact ht
      · exfalso
        rw [hev] at hE
        exact hsym (congrArg Signature.Event.sym (MaybeEvent.some.inj hE)).symm
    exact {
      echo := fun t ht v hev' =>
        hM'.echo t (hnot t _ ht hev' hdist.propose_ne_echo.symm) v hev'
      voteZero := fun t ht l v hev' =>
        hM'.voteZero t (hnot t _ ht hev' (hdist.propose_ne_vote 0).symm) l v hev'
      voteSucc := fun t ht l v n hev' =>
        hM'.voteSucc t (hnot t _ ht hev' (hdist.propose_ne_vote (n + 1)).symm) l v n hev'
      deliver := fun t ht l v hev' =>
        hM'.deliver t (hnot t _ ht hev' hdist.propose_ne_deliver.symm) l v hev'
      echoNE := fun t ht v u hev' hp =>
        hM'.echoNE t (hnot t _ ht hev' hdist.propose_ne_echo.symm) v u hev' hp
      voteNE := fun t ht l b v u n hev' hp hκ hne =>
        hM'.voteNE t (hnot t _ ht hev' (hdist.propose_ne_vote n).symm) l b v u n hev' hp hκ hne }
  fair_completion := by
    intro M hM henv Live hLive
    obtain ⟨M', hM', hfair, henv', hT, hκ, hlive, hsub, hnew⟩ := hcomp M hM henv Live hLive
    exact ⟨M', hM', hfair, henv', hT, hκ, hlive, hsub, hnew⟩

/-- Budgeted HBB4 is correct in the sense of `Protocol.Correct`. -/
theorem hbb4Protocol_correct (hdist : DistinctSymbols σ) (hcomp : Completion (P := P) σ) :
    (hbb4Protocol σ hdist hcomp).Correct := by
  refine ⟨?_, ?_, ?_⟩
  · -- Agreement, via the live-free model
    intro M hloc henv a b v u hab hv hu
    have hloc' : LocalRules σ (stripLive σ M).history.val (stripLive σ M).learner
        (corrOf σ.toBase (stripLive σ M)) := by
      rw [stripLive_corrOf]; exact hloc
    have hCM := toCM hloc' (stripLive_env henv) (stripLive_thyLive M) (stripLive_forward M)
    have hab' : ∀ p, Correlated (stripLive σ M) σ.correlationSymb
        (finalWorld (stripLive σ M) p) a b :=
      fun p => (stripLive_correlated M _ _ a b).mpr (hab p)
    have hv' : Occurs (stripLive σ M) (σ.deliver a v) := by
      obtain ⟨e, he, hs⟩ := hv
      exact ⟨e, he, ofEvent_transfer hs he⟩
    have hu' : Occurs (stripLive σ M) (σ.deliver b u) := by
      obtain ⟨e, he, hs⟩ := hu
      exact ⟨e, he, ofEvent_transfer hs he⟩
    exact ThyHBB4B.CM.agreement hCM hab' hv' hu'
  · intro M hloc henv hfair l v hQ hU hO p hp
    exact ThyHBB4B.CM.livenessOne (toCM hloc henv hfair.1 hfair.2) hQ hU hO p hp
  · intro M hloc henv hfair a b v hC hQ hD p hp
    exact ThyHBB4B.CM.livenessTwo (toCM hloc henv hfair.1 hfair.2) hC hQ hD p hp

/-- **Depth lower bound for budgeted HBB4.** Under HBB4's fair-completion property,
with a uniform budget at least `B ≥ 2`, there are a topology, a causally monotone
correlation relation, a learner `L` and an `L`-quorum `Q` such that in every
execution of budgeted HBB4 meeting its environment assumptions, every honest
`Q`-only `L`-delivery has causal depth at least `B`. -/
theorem hbb4_protocol_depth_bound (hdist : DistinctSymbols σ) (hcomp : Completion (P := P) σ)
    (hP : ∃ f : Nat → P, Function.Injective f)
    (hV : ∃ g : Nat → S.Value, Function.Injective g)
    (B : Nat) (hB : 2 ≤ B) (hbudget : ∀ l, B ≤ σ.depthBound l) :
    ∃ (T : Topology S P) (κ : Correlation S P),
      CausallyMonotone σ.toBase κ ∧
      ∃ (L : S.Value) (Q : Set P), Q ∈ (T L).quorums ∧
        ∀ M ∈ (hbb4Protocol σ hdist hcomp).executionsOn T κ, ∀ d ∈ M.history.val, ∀ v : S.Value,
          (⟪d⟫ ⊨[M] σ.deliver L v) → UsesOnly Q d → HonestCone d → B ≤ worldDepth d :=
  depth_lower_bound (hbb4Protocol σ hdist hcomp) (hbb4Protocol_correct σ hdist hcomp) hP hV B hB
    (fun _ hE hC hD => ⟨hE, hC, fun l => Nat.le_trans (hD l) (hbudget l)⟩)
    (fun _ h => h.1)

end ModalDistribution.LowerBound.HBB4
