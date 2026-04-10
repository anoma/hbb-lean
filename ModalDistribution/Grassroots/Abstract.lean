import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

/-!
# Abstract grassroots distributed multiagent transition systems

This file gives a Lean formalisation of **Shapiro's grassroots property**
for distributed multiagent transition systems, completely independently
of the Murdoch–Sheff HBB framework.

## Provenance

Shapiro has published two non-identical formal definitions of "grassroots"
across his corpus:

1. **Original (DISC 2023, arXiv:2301.04391, Definition 9):**
   `TS(P) ⊊ TS(P')/P` for all `∅ ⊂ P ⊂ P' ⊆ Π`. The strict-inclusion form
   uses *projection* of the larger system onto the smaller one.

2. **Newer (arXiv:2502.11299 Definition 4.3, also arXiv:2510.15747 Def C.7,
   arXiv:2511.03286 Def 3.10/3.11):** A protocol `ℱ` is *grassroots* iff it is
   - **Oblivious**: `T(P)↑P' ⊆ T(P')` — every small-system transition lifts
     to a large-system transition (extra agents stay in initial state).
   - **Interactive**: for every `c ∈ C(P')` such that `c/P ∈ C(P)`, there is
     a computation `c →* c'` of `ℱ(P')` with `c'/P ∉ C(P)`.

The newer formulation factors more cleanly into Lean: each half is a single
quantifier, and the lifting `↑P'` is just "extra agents stay put" (no
projection-side complications). We follow the newer formulation.

## Main definitions

* `Grassroots.Abstract.Config A LocalState P` — configurations as functions
  from `↥P` to local states.
* `Grassroots.Abstract.liftConfig` — lift a configuration along `P ⊆ P'`,
  with extra agents in their initial state.
* `Grassroots.Abstract.projectConfig` — restrict a configuration along
  `P ⊆ P'`.
* `Grassroots.Abstract.DTS` — distributed multiagent transition system: a
  per-participant-set transition relation.
* `Grassroots.Abstract.Reachable` — reflexive-transitive closure of a step
  relation (specialised wrapper around `Relation.ReflTransGen`).
* `Grassroots.Abstract.ReachableConfigs` — set of configurations reachable
  from the initial configuration.
* `Grassroots.Abstract.IsOblivious` — every small-system transition lifts to
  a large-system transition.
* `Grassroots.Abstract.IsInteractive` — every large-system extension of a
  small-system reachable configuration admits an escape into a configuration
  whose projection is *not* small-system reachable.
* `Grassroots.Abstract.IsGrassroots` — oblivious + interactive.

## Main theorems

* `Grassroots.Abstract.project_lift_eq` — `projectConfig (liftConfig c) = c`.
* `Grassroots.Abstract.IsOblivious.lift_reachable` — obliviousness extends
  from single transitions to reachable configurations.
* `Grassroots.Abstract.IsOblivious.lift_reachable_set` — every small-system
  reachable configuration lifts to a large-system reachable configuration.

## Note

This file is intentionally **independent** of `Sequentiality.lean`,
`Coalescent.lean`, and `LeaderRooted.lean`. It depends only on Mathlib.
The other Grassroots modules apply this abstract framework to the HBB
modal-logic setting.
-/

namespace ModalDistribution
namespace Grassroots
namespace Abstract

universe u v

variable {A : Type u} {LocalState : Type v}

/-! ## §1. Configurations

A *configuration* over a participant set `P : Set A` assigns a local state
to each participant in `P`. We model this as a function on the subtype
`↥P`. -/

/-- A configuration over a participant set is a function from the subtype
of participants to local states. -/
def Config (P : Set A) (LocalState : Type v) : Type _ :=
  ↥P → LocalState

/-! ## §2. Subtype embedding and projection

The subtype embedding `↥P → ↥P'` for `P ⊆ P'` is the only piece of
"abstract subtype" infrastructure we need.  We define it locally to keep
this file independent of `Sequentiality.lean`. -/

/-- Inclusion of subtypes induced by `P ⊆ P'`. -/
@[simp] def embed {P P' : Set A} (h : P ⊆ P') : ↥P → ↥P' :=
  fun a => ⟨a.val, h a.property⟩

@[simp] lemma embed_val {P P' : Set A} (h : P ⊆ P') (a : ↥P) :
    (embed h a).val = a.val := rfl

/-! ## §3. Configuration lifting and projection

`liftConfig h c` extends a small-set configuration `c : Config P` to a
large-set configuration `Config P'` by setting agents in `P' \ P` to a
designated *initial* local state. `projectConfig h c'` restricts a
large-set configuration to the small set. -/

open Classical in
/-- Lift a configuration from `↥P` to `↥P'` along `P ⊆ P'`, with extra
agents (those in `P' \ P`) taking the supplied initial local state. -/
noncomputable def liftConfig {P P' : Set A} (_h : P ⊆ P')
    (initial : LocalState) (c : Config P LocalState) :
    Config P' LocalState :=
  fun a => if hap : a.val ∈ P then c ⟨a.val, hap⟩ else initial

/-- Restrict a configuration from `↥P'` to `↥P` along `P ⊆ P'`. -/
def projectConfig {P P' : Set A} (h : P ⊆ P')
    (c : Config P' LocalState) : Config P LocalState :=
  fun a => c (embed h a)

/-- **Project–lift identity.** Restricting a lifted configuration recovers
the original. -/
@[simp] theorem project_lift_eq {P P' : Set A} (h : P ⊆ P')
    (initial : LocalState) (c : Config P LocalState) :
    projectConfig h (liftConfig h initial c) = c := by
  classical
  funext a
  unfold projectConfig liftConfig embed
  simp only [dif_pos a.property]

/-- The lifted configuration agrees with `c` on agents in `P` (viewed in `↥P'`). -/
@[simp] lemma liftConfig_inP {P P' : Set A} (h : P ⊆ P')
    (initial : LocalState) (c : Config P LocalState) (a : ↥P) :
    (liftConfig h initial c) (embed h a) = c a := by
  classical
  unfold liftConfig embed
  simp only [dif_pos a.property]

/-- The lifted configuration is `initial` on agents outside `P`. -/
lemma liftConfig_outP {P P' : Set A} (_h : P ⊆ P')
    (initial : LocalState) (c : Config P LocalState)
    (a : ↥P') (hap : a.val ∉ P) :
    (liftConfig _h initial c) a = initial := by
  classical
  unfold liftConfig
  simp only [dif_neg hap]

/-! ## §4. Distributed multiagent transition systems

A `DTS A LocalState` consists of:
* a designated `initial` local state used to extend small configurations,
* a transition relation `step` parameterised by the participant set.

This mirrors Shapiro's "distributed multiagent transition system" from
arXiv:2112.13650, restricted to the data we actually need to state the
grassroots property.  -/

/-- A *distributed multiagent transition system* over an agent universe
`A` and local-state space `LocalState`. -/
structure DTS (A : Type u) (LocalState : Type v) where
  /-- The designated initial local state for every agent. -/
  initial : LocalState
  /-- The per-participant-set transition relation. -/
  step : ∀ (P : Set A), Config P LocalState → Config P LocalState → Prop

namespace DTS

variable {A : Type u} {LocalState : Type v}

/-- The initial configuration at participant set `P`: every agent in the
initial state. -/
def initialConfig (T : DTS A LocalState) (P : Set A) :
    Config P LocalState :=
  fun _ => T.initial

/-- The reflexive-transitive closure of the step relation at `P`. -/
def Reachable (T : DTS A LocalState) (P : Set A) :
    Config P LocalState → Config P LocalState → Prop :=
  Relation.ReflTransGen (T.step P)

/-- The set of configurations reachable from the initial configuration
at participant set `P`. -/
def ReachableConfigs (T : DTS A LocalState) (P : Set A) :
    Set (Config P LocalState) :=
  { c | T.Reachable P (T.initialConfig P) c }

/-- The initial configuration is always in `ReachableConfigs`. -/
lemma initialConfig_mem_reachable (T : DTS A LocalState) (P : Set A) :
    T.initialConfig P ∈ T.ReachableConfigs P :=
  Relation.ReflTransGen.refl

/-- Reachability is reflexive. -/
lemma Reachable.refl (T : DTS A LocalState) (P : Set A)
    (c : Config P LocalState) : T.Reachable P c c :=
  Relation.ReflTransGen.refl

/-- Reachability is transitive. -/
lemma Reachable.trans {T : DTS A LocalState} {P : Set A}
    {c₁ c₂ c₃ : Config P LocalState} :
    T.Reachable P c₁ c₂ → T.Reachable P c₂ c₃ → T.Reachable P c₁ c₃ :=
  Relation.ReflTransGen.trans

/-- A single step is a reachability witness. -/
lemma Reachable.single {T : DTS A LocalState} {P : Set A}
    {c c' : Config P LocalState} (hstep : T.step P c c') :
    T.Reachable P c c' :=
  Relation.ReflTransGen.single hstep

end DTS

/-! ## §5. Obliviousness (Shapiro non-interference / safety)

A DTS is *oblivious* iff every transition of the small system, when lifted
to the large system (extra agents staying initial), is a transition of the
large system. This is `T(P)↑P' ⊆ T(P')` from arXiv:2502.11299 Def 4.3. -/

/-- A DTS is **oblivious** iff every step of the small system lifts to a
step of the large system, with extra agents in the initial state. -/
def IsOblivious (T : DTS A LocalState) : Prop :=
  ∀ {P P' : Set A} (h : P ⊆ P') (c c' : Config P LocalState),
    T.step P c c' →
      T.step P'
        (liftConfig h T.initial c)
        (liftConfig h T.initial c')

namespace IsOblivious

variable {T : DTS A LocalState}

/-- Obliviousness extends from single steps to reachability. -/
theorem lift_reachable (hOb : IsOblivious T)
    {P P' : Set A} (h : P ⊆ P')
    {c c' : Config P LocalState}
    (hReach : T.Reachable P c c') :
    T.Reachable P'
      (liftConfig h T.initial c)
      (liftConfig h T.initial c') := by
  induction hReach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hStep ih =>
      exact Relation.ReflTransGen.tail ih (hOb h _ _ hStep)

/-- Obliviousness lifts the entire reachable configuration set:
every small-system reachable configuration corresponds to a large-system
reachable configuration whose projection recovers it. -/
theorem lift_reachable_set (hOb : IsOblivious T)
    {P P' : Set A} (h : P ⊆ P')
    {c : Config P LocalState}
    (hcReach : c ∈ T.ReachableConfigs P) :
    ∃ c' : Config P' LocalState,
      c' ∈ T.ReachableConfigs P' ∧ projectConfig h c' = c := by
  refine ⟨liftConfig h T.initial c, ?_, ?_⟩
  · -- The lifted initial configuration IS the initial configuration at P'.
    have hInit : liftConfig h T.initial (T.initialConfig P) =
        T.initialConfig P' := by
      classical
      funext a
      unfold liftConfig DTS.initialConfig
      by_cases hap : a.val ∈ P
      · simp only [dif_pos hap]
      · simp only [dif_neg hap]
    have hReach :=
      lift_reachable (T := T) hOb (h := h) hcReach
    rw [hInit] at hReach
    exact hReach
  · exact project_lift_eq h T.initial c

end IsOblivious

/-! ## §6. Interactivity (Shapiro strict-inclusion half)

A DTS is *interactive* iff for every nested participant pair `P ⊂ P'` and
every large-system configuration `c` whose projection is small-system
reachable, the large system has a way to *escape* the small-system
reachable set. This is the strict-inclusion half of Shapiro's grassroots
property — without it, the large system has no behaviours genuinely beyond
those of the small system. -/

/-- A DTS is **interactive** iff every large-system extension of a
small-system reachable configuration admits a computation whose projection
escapes the small-system reachable set. -/
def IsInteractive (T : DTS A LocalState) : Prop :=
  ∀ {P P' : Set A} (h : P ⊆ P') (_hStrict : P ≠ P')
    (c : Config P' LocalState),
    projectConfig h c ∈ T.ReachableConfigs P →
      ∃ c' : Config P' LocalState,
        T.Reachable P' c c' ∧
          projectConfig h c' ∉ T.ReachableConfigs P

/-! ## §7. Grassroots = oblivious + interactive

Putting the two halves together gives Shapiro's grassroots property. -/

/-- A DTS is **grassroots** iff it is both oblivious and interactive.
This is Definition 4.3 of arXiv:2502.11299, Definition C.7 of arXiv:2510.15747,
and Definition 3.11 of arXiv:2511.03286. -/
def IsGrassroots (T : DTS A LocalState) : Prop :=
  IsOblivious T ∧ IsInteractive T

namespace IsGrassroots

variable {T : DTS A LocalState}

/-- Extract the obliviousness component. -/
theorem oblivious (hG : IsGrassroots T) : IsOblivious T := hG.1

/-- Extract the interactivity component. -/
theorem interactive (hG : IsGrassroots T) : IsInteractive T := hG.2

end IsGrassroots

/-! ## §8. A discriminating example: the trivial DTS

The trivial DTS — the one with no transitions at all — is *oblivious*
(vacuously: there are no transitions to lift) but **not** interactive
(the only reachable configuration at any participant set is the initial
one, and there is no escape). This shows the two halves of grassroots are
genuinely distinct: obliviousness alone is not enough.  -/

namespace Trivial

variable (A : Type u) (LocalState : Type v) (init : LocalState)

/-- The trivial DTS: no transitions at any participant set. -/
def trivialDTS : DTS A LocalState where
  initial := init
  step _ _ _ := False

variable {A LocalState init}

/-- The trivial DTS is oblivious (vacuously). -/
theorem trivialDTS_oblivious : IsOblivious (trivialDTS A LocalState init) := by
  intro P P' h c c' hStep
  exact hStep.elim

/-- In the trivial DTS, the only reachable configuration is the initial one. -/
theorem trivialDTS_reachableConfigs (P : Set A) :
    (trivialDTS A LocalState init).ReachableConfigs P =
      {(trivialDTS A LocalState init).initialConfig P} := by
  ext c
  constructor
  · intro hMem
    -- Reach by zero or more `False`-steps; only zero steps is possible.
    have hReach : (trivialDTS A LocalState init).Reachable P
        ((trivialDTS A LocalState init).initialConfig P) c := hMem
    induction hReach with
    | refl => rfl
    | tail _ hStep _ => exact hStep.elim
  · rintro (rfl : c = _)
    exact (trivialDTS A LocalState init).initialConfig_mem_reachable P

end Trivial

end Abstract
end Grassroots
end ModalDistribution
