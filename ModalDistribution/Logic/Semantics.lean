import ModalDistribution.Core.Set
import ModalDistribution.Core.Prehistory
import ModalDistribution.Core.History
import ModalDistribution.Core.Model
import ModalDistribution.Logic.Syntax

/-!
# Modal logic semantics

We formalise the satisfaction relation of the paper's validity judgements
(Definition 3.4.10).  Satisfaction is defined for a model, a participant, a
maybe-event, and a history.  We also introduce end-of-time validity,
event-driven validity, and the notion of active participants.
-/

namespace ModalDistribution
namespace Logic

open Set
open ModalDistribution
open History
open PreHistory
open World
open scoped PreHistory Formula

set_option autoImplicit false

-- Fix at Type 0 to match Syntax.lean
variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]

/-- Quorum-intersection check for the `♢` clause of `Sat`.

`Sat.Check M Q ls acc` holds when every choice of one quorum per learner in
`ls` leaves a participant in the accumulated intersection `acc ∩ O₁ ∩ ⋯ ∩ Oₙ`
satisfying `Q`. The recursion is on the learner list only; the satisfaction
predicate `Q` is abstract, which keeps `Sat` itself structurally recursive. -/
def Sat.Check (M : Model S P) (Q : P → Prop) : List S.Value → Set P → Prop
  | [], acc => ∃ p' ∈ acc, Q p'
  | ℓ :: ls, acc =>
      ∀ O ∈ (M.learner ℓ).quorums,
        Sat.Check M Q ls (acc ∩ O)

/-- Paper: Definition 3.4.10(1) / Figure 4 (possible-world validity). Satisfaction relation
`p, x, H ⊨ φ`. -/
def Sat (M : Model S P)
    (p : P)
    (evt : MaybeEvent S.EventType)
    (H : PreHistory P (S.EventType)) : Formula S → Prop
  | .bot => False
  | .imp φ ψ => Sat M p evt H φ → Sat M p evt H ψ
  | .eq v₁ v₂ => v₁ = v₂
  | .forall body => ∀ v : Signature.Value S, Sat M p evt H (body v)
  | .event atom =>
      evt = MaybeEvent.some ⟨atom.sym, atom.args⟩ ∧
        (p, MaybeEvent.some ⟨atom.sym, atom.args⟩, H) ∈ M.history.val
  | .predicate pred =>
      ⟨pred.sym, pred.args⟩ ∈ M.predInterp p H
  | .past φ =>
      ∃ t ∈ H,
        t.place = p ∧
          Sat M (t.place) (World.event t) (World.time t) φ
  | .atEnd φ => Sat M p † M.history.val φ
  | .diamond learners φ =>
      Sat.Check M (fun p' => Sat M p' † H φ) learners Set.univ
  | .seq =>
      IsSequential (Event := S.EventType) p H

notation:65 "⟪" w "⟫" " ⊨[" M "]" φ =>
  Sat M (place w) (event w) (time w) φ

namespace Sat

variable {M : Model S P} {w : World P S.EventType}

/-! ### Propositional connectives -/

/-- `¬φ` holds exactly when `φ` fails. -/
@[simp] theorem not (M : Model S P) (w : World P S.EventType) (φ : Formula S) :
    (⟪w⟫ ⊨[M]¬ᶠ φ) ↔ ¬(⟪w⟫ ⊨[M]φ) := Iff.rfl

/-- Elimination form of `Sat.not`: `¬φ` and `φ` are contradictory. -/
theorem not_elim (M : Model S P) {w : World P S.EventType} {φ : Formula S} :
    (⟪w⟫ ⊨[M]¬ᶠ φ) → (⟪w⟫ ⊨[M]φ) → False := id

/-- Introduction form of `Sat.not`: refuting `φ` establishes `¬φ`. -/
theorem not_intro (M : Model S P) {w : World P S.EventType} {φ : Formula S}
    (h : (⟪w⟫ ⊨[M]φ) → False) :
    ⟪w⟫ ⊨[M]¬ᶠ φ := h

/-- `φ ⇒ ψ` holds exactly when `φ` implies `ψ` at the same world. -/
@[simp] theorem imp
    (M : Model S P) (w : World P S.EventType)
    (φ ψ : Formula S) :
    (⟪w⟫ ⊨[M]φ ⇒ᶠ ψ) ↔
      ((⟪w⟫ ⊨[M]φ) → (⟪w⟫ ⊨[M]ψ)) := Iff.rfl

/-- Elimination form of `Sat.imp` (modus ponens). -/
theorem imp_elim
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S} :
    (⟪w⟫ ⊨[M]φ ⇒ᶠ ψ) →
      (⟪w⟫ ⊨[M]φ) → ⟪w⟫ ⊨[M]ψ := id

/-- Introduction form of `Sat.imp`. -/
theorem imp_intro
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S}
    (h : (⟪w⟫ ⊨[M]φ) → ⟪w⟫ ⊨[M]ψ) :
    ⟪w⟫ ⊨[M]φ ⇒ᶠ ψ := h

/-- `⊤` holds at every world. -/
theorem top
    (M : Model S P)
    (w : World P S.EventType) :
    ⟪w⟫ ⊨[M]⊤ᶠ := id

/-- `φ ∧ ψ` holds exactly when both conjuncts hold. -/
@[simp] theorem and
    (M : Model S P)
    (w : World P S.EventType)
    (φ ψ : Formula S) :
    (⟪w⟫ ⊨[M]φ ∧ᶠ ψ) ↔
      (⟪w⟫ ⊨[M]φ) ∧ (⟪w⟫ ⊨[M]ψ) := by
  simp only [Formula.and, not, imp, Classical.not_imp, Classical.not_not]

/-- Introduction form of `Sat.and`. -/
theorem and_intro
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S}
    (hφ : ⟪w⟫ ⊨[M]φ)
    (hψ : ⟪w⟫ ⊨[M]ψ) :
    ⟪w⟫ ⊨[M]φ ∧ᶠ ψ :=
  (and M w φ ψ).2 ⟨hφ, hψ⟩

/-- `φ ∨ ψ` holds exactly when one of the disjuncts holds. -/
@[simp] theorem or
    (M : Model S P)
    (w : World P S.EventType)
    (φ ψ : Formula S) :
    (⟪w⟫ ⊨[M]φ ∨ᶠ ψ) ↔
      (⟪w⟫ ⊨[M]φ) ∨ (⟪w⟫ ⊨[M]ψ) := by
  simp only [Formula.or, imp, not, Classical.or_iff_not_imp_left]

/-- The forward direction of a satisfied `φ ⇔ ψ`. -/
theorem iff_mp
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S}
    (hIff : ⟪w⟫ ⊨[M]φ ⇔ᶠ ψ) :
    (⟪w⟫ ⊨[M]φ) → (⟪w⟫ ⊨[M]ψ) :=
  ((and M w _ _).1 hIff).1

/-- The backward direction of a satisfied `φ ⇔ ψ`. -/
theorem iff_mpr
    (M : Model S P)
    (w : World P S.EventType)
    {φ ψ : Formula S}
    (hIff : ⟪w⟫ ⊨[M]φ ⇔ᶠ ψ) :
    (⟪w⟫ ⊨[M]ψ) → (⟪w⟫ ⊨[M]φ) :=
  ((and M w _ _).1 hIff).2

/-! ### Equality and quantifiers -/

/-- `v₁ = v₂` holds exactly when the values coincide. -/
@[simp] theorem eq (M : Model S P) (w : World P S.EventType)
    (v₁ v₂ : S.Value) :
    (⟪w⟫ ⊨[M]v₁ ≃ᶠ v₂) ↔ v₁ = v₂ := Iff.rfl

/-- A satisfied universal formula holds at every value. -/
theorem forall_elim
    (M : Model S P) (w : World P S.EventType)
    (body : S.Value → Formula S)
    (v : Signature.Value S)
    (h : ⟪w⟫ ⊨[M].forall body) :
    ⟪w⟫ ⊨[M]body v := h v

/-- A universal formula holds when its body holds at every value. -/
theorem forall_intro
    (M : Model S P) (w : World P S.EventType)
    (body : S.Value → Formula S)
    (h : ∀ v : Signature.Value S, ⟪w⟫ ⊨[M]body v) :
    ⟪w⟫ ⊨[M].forall body := h

/-- `∃ a. φ` holds exactly when some value satisfies the body. -/
@[simp] theorem exists_iff
    (w : World P S.EventType)
    (body : Signature.Value S → Formula S) :
    (⟪w⟫ ⊨[M]∃ᶠ fun v => body v) ↔
      ∃ v, ⟪w⟫ ⊨[M]body v :=
  ⟨fun h => Classical.byContradiction fun hNone => h fun v hv => hNone ⟨v, hv⟩,
    fun ⟨v, hv⟩ h => h v hv⟩

/-! ### Atoms -/

/-- An event atom holds exactly when the world's event is that event and the
world is an event-tuple of the model. -/
@[simp] theorem ofEvent
    (M : Model S P)
    (w : World P S.EventType)
    (E : S.EventType) :
    (⟪w⟫ ⊨[M]Formula.ofEvent E) ↔
      (World.event w = MaybeEvent.some E ∧
        (World.place w, MaybeEvent.some E, World.time w) ∈ M.history.val) := Iff.rfl

/-- A world satisfying an event atom is an event-tuple of the model. -/
theorem mem_of_ofEvent
    (M : Model S P)
    {w : World P S.EventType}
    {E : S.EventType}
    (h : ⟪w⟫ ⊨[M]Formula.ofEvent E) :
    w ∈ M.history.val := by
  obtain ⟨p, evt, H⟩ := w
  obtain ⟨rfl, hMem⟩ := h
  exact hMem

/-- `seq` holds exactly when the world's place is sequential in its time. -/
@[simp] theorem seq
    (M : Model S P) (w : World P S.EventType) :
    (⟪w⟫ ⊨[M]Formula.seq (S := S)) ↔
      IsSequential (Event := S.EventType) (World.place w) (World.time w) := Iff.rfl

/-! ### Temporal modalities -/

/-- `↓φ` holds exactly when `φ` holds at some event-tuple of the current time
at the current place. -/
theorem past
    (M : Model S P)
    (w : World P S.EventType)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]↓ᶠ φ) ↔
      ∃ t ∈ w.time, t.place = w.place ∧ ⟪t⟫ ⊨[M]φ := Iff.rfl

/-- A same-place witness in the current time establishes `↓φ`. -/
theorem past_intro_of_prefix
    {t : World P S.EventType}
    {φ : Formula S}
    (ht : t ∈ w.time)
    (hp : t.place = w.place)
    (hφ : ⟪t⟫ ⊨[M]φ) :
    ⟪w⟫ ⊨[M] ↓ᶠ φ :=
  (past M w φ).2 ⟨t, ht, hp, hφ⟩

/-- `↓` is monotone: an implication at every past same-place event-tuple
carries `↓φ` to `↓ψ`. -/
theorem past_of_imp
    {φ ψ : Formula S}
    (h : ∀ (t : World P S.EventType), t ∈ w.time → t.place = w.place →
        (⟪t⟫ ⊨[M]φ) → ⟪t⟫ ⊨[M]ψ) :
    (⟪w⟫ ⊨[M] ↓ᶠ φ) → (⟪w⟫ ⊨[M] ↓ᶠ ψ) := fun hPast =>
  let ⟨t, ht, hp, hφ⟩ := (past M w φ).1 hPast
  (past M w ψ).2 ⟨t, ht, hp, h t ht hp hφ⟩

/-- `↓φ` persists into a larger time: its witness is still there. -/
theorem past_of_time_subset {p : P} {e e' : MaybeEvent S.EventType}
    {H H' : PreHistory P S.EventType} {φ : Formula S} (hTime : H ⊆ H') :
    (⟪⟨p, e, H⟩⟫ ⊨[M] ↓ᶠ φ) → ⟪⟨p, e', H'⟩⟫ ⊨[M] ↓ᶠ φ := fun hPast =>
  let ⟨t, ht, hp, hφ⟩ := (past M _ φ).1 hPast
  (past M _ φ).2 ⟨t, hTime t ht, hp, hφ⟩

/-- `⇓φ` holds exactly when `φ` holds at every event-tuple of the current time
at the current place. -/
theorem allPast
    (M : Model S P)
    (w : World P S.EventType)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]Formula.allPast φ) ↔
      ∀ t ∈ w.time, t.place = w.place → ⟪t⟫ ⊨[M]φ := by
  simp only [Formula.allPast, not, past, not_exists, not_and, Classical.not_not]

/-- `⤒φ` holds exactly when `φ` holds at the end of time, at the same place. -/
@[simp] theorem atEnd
    (M : Model S P)
    (w : World P S.EventType)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]⤒ᶠ φ) ↔
      ⟪⟨World.place w, †, M.history.val⟩⟫ ⊨[M]φ := Iff.rfl

/-- Paper: Lemma 3.6.4(1). `↕φ` holds exactly when `φ` holds at some
event-tuple of the model at the current place. -/
theorem sometime
    (M : Model S P)
    (w : World P S.EventType)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]Formula.sometime φ) ↔
      ∃ t ∈ M.history.val, t.place = w.place ∧ ⟪t⟫ ⊨[M]φ := Iff.rfl

/-- An event-tuple of the model that satisfies `φ` is its own witness for `↕φ`. -/
theorem sometime_of_mem
    (M : Model S P)
    {t : World P S.EventType}
    {φ : Formula S}
    (ht : t ∈ M.history.val)
    (hφ : ⟪t⟫ ⊨[M]φ) :
    ⟪t⟫ ⊨[M]Formula.sometime φ :=
  (sometime M t φ).2 ⟨t, ht, rfl, hφ⟩

/-- `↕φ` depends only on the place of a world. -/
theorem sometime_of_place_eq
    (M : Model S P)
    {t w : World P S.EventType}
    {φ : Formula S}
    (hPlace : t.place = w.place)
    (h : ⟪t⟫ ⊨[M]Formula.sometime φ) :
    ⟪w⟫ ⊨[M]Formula.sometime φ :=
  let ⟨s, hs, hsPlace, hφ⟩ := (sometime M t φ).1 h
  (sometime M w φ).2 ⟨s, hs, hsPlace.trans hPlace, hφ⟩

/-- Paper: Lemma 3.6.4(2). `⇕φ` holds exactly when `φ` holds at every
event-tuple of the model at the current place. -/
theorem everytime
    (M : Model S P)
    (w : World P S.EventType)
    (φ : Formula S) :
    (⟪w⟫ ⊨[M]Formula.everytime φ) ↔
      ∀ t ∈ M.history.val, t.place = w.place → ⟪t⟫ ⊨[M]φ := by
  simp only [Formula.everytime, not, sometime, not_exists, not_and, Classical.not_not]

/-! ### Quorum modalities -/

/-- `Sat.Check` over the empty learner list asks for a witness in the accumulator. -/
@[simp] theorem check_nil (M : Model S P)
    (Q : P → Prop) (acc : Set P) :
    Sat.Check M Q [] acc ↔ ∃ p' ∈ acc, Q p' := Iff.rfl

/-- `Sat.Check` over `v :: vs` intersects the accumulator with every `v`-quorum. -/
@[simp] theorem check_cons (M : Model S P)
    (Q : P → Prop)
    (v : S.Value) (vs : List S.Value) (acc : Set P) :
    Sat.Check M Q (v :: vs) acc ↔
      ∀ O ∈ (M.learner v).quorums, Sat.Check M Q vs (acc ∩ O) := Iff.rfl

/-- `Sat.Check` is monotone in the predicate it checks. -/
theorem check_mono {Q Q' : P → Prop} (h : ∀ q, Q q → Q' q) :
    ∀ {ts : List S.Value} {acc : Set P},
      Sat.Check M Q ts acc → Sat.Check M Q' ts acc
  | [], _, ⟨q, hq, hQ⟩ => ⟨q, hq, h q hQ⟩
  | _ :: _, _, hCheck => fun O hO => check_mono h (hCheck O hO)

/-- `♢φ` over no learners holds exactly when some participant satisfies `φ`
at the end of the current time. -/
@[simp] theorem diamond_nil
    (M : Model S P) (w : World P S.EventType) (φ : Formula S) :
    (⟪w⟫ ⊨[M]♢ᶠ[[]] φ) ↔
      ∃ p' : P, ⟪⟨p', †, w.time⟩⟫ ⊨[M]φ := by
  simp [Sat]

/-- `Sat.diamond_nil` for the `♢ᶠ[]` notation. -/
theorem diamondEmpty
    (M : Model S P) (w : World P S.EventType) (φ : Formula S) :
    (⟪w⟫ ⊨[M]♢ᶠ[] φ) ↔
      ∃ p' : P, ⟪⟨p', †, w.time⟩⟫ ⊨[M]φ :=
  diamond_nil M w φ

/-- `♢` is monotone in its body. -/
theorem diamond_of_imp
    (ts : List S.Value) {φ ψ : Formula S}
    (h : ∀ q, (⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) → (⟪⟨q, †, w.time⟩⟫ ⊨[M]ψ)) :
    (⟪w⟫ ⊨[M]♢ᶠ[ts] φ) → (⟪w⟫ ⊨[M]♢ᶠ[ts] ψ) :=
  check_mono h

/-- `♦φ` (`♢↓φ` over no learners) holds exactly when `φ` holds at some
event-tuple of the current time, at any place. -/
theorem diamondPast_nil {φ : Formula S} :
    (⟪w⟫ ⊨[M]♢ᶠ↓[[]] φ) ↔ ∃ t ∈ w.time, ⟪t⟫ ⊨[M]φ :=
  (diamond_nil M w _).trans
    ⟨fun ⟨_, t, ht, _, hφ⟩ => ⟨t, ht, hφ⟩, fun ⟨t, ht, hφ⟩ => ⟨t.place, t, ht, rfl, hφ⟩⟩

/-- `□φ` holds exactly when `♢¬φ` fails. -/
theorem box {ls : List S.Value} {φ : Formula S} :
    (⟪w⟫ ⊨[M]□ᶠ[ls] φ) ↔ ¬(⟪w⟫ ⊨[M]♢ᶠ[ls] (¬ᶠ φ)) := Iff.rfl

/-- `□φ` over no learners holds exactly when every participant satisfies `φ`
at the end of the current time. -/
theorem boxEmpty
    (M : Model S P)
    (w : World P S.EventType) (φ : Formula S) :
    (⟪w⟫ ⊨[M]□ᶠ[] φ) ↔ ∀ q : P, ⟪⟨q, †, w.time⟩⟫ ⊨[M]φ := by
  simp only [Formula.boxEmpty, box, diamond_nil, not, not_exists, Classical.not_not]

/-- `□` is monotone in its body. -/
theorem box_of_imp
    (ts : List S.Value) {φ ψ : Formula S}
    (h : ∀ q, (⟪⟨q, †, w.time⟩⟫ ⊨[M]φ) → ⟪⟨q, †, w.time⟩⟫ ⊨[M]ψ) :
    (⟪w⟫ ⊨[M]□ᶠ[ts] φ) →
      (⟪w⟫ ⊨[M]□ᶠ[ts] ψ) := fun hBox hDiamond =>
  hBox (diamond_of_imp ts (fun q (hNotψ : ⟪⟨q, †, w.time⟩⟫ ⊨[M]¬ᶠ ψ) hφ => hNotψ (h q hφ))
    hDiamond)

end Sat

/-- Paper: Definition 3.4.10(2) (end-of-time validity ⊨). `φ` holds at the
end of time at every participant. -/
@[simp] def EndValid
    (M : Model S P) (φ : Formula S) : Prop :=
  ∀ p : P,
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ

notation:55 "⊨[" M "]" φ =>
  EndValid M φ

/-- Modus ponens for end-of-time validity. -/
theorem EndValid.imp_elim
    (M : Model S P) {φ ψ : Formula S}
    (hImp : ⊨[M]φ ⇒ᶠ ψ) (hφ : ⊨[M]φ) : ⊨[M]ψ :=
  fun p => hImp p (hφ p)

/-- Paper: Definition 3.4.10(3) (all-world validity □W⊨). `φ` holds at every
world whose time weakly precedes the end of time. -/
@[simp] def AllWorldValid
    (M : Model S P) (φ : Formula S) : Prop :=
  ∀ {t : World P S.EventType},
    t.time ⪯ M.history.val →
      ⟪t⟫ ⊨[M]φ

/-- The time of an event-tuple of the model weakly precedes the end of time. -/
theorem _root_.ModalDistribution.Model.time_le_of_mem
    (M : Model S P) {t : World P S.EventType}
    (ht : t ∈ M.history.val) :
    t.time ⪯ M.history.val :=
  PreHistory.happensBeforeEq_of_mem ht

/-- An all-world validity holds at every event-tuple of the model. -/
theorem AllWorldValid.of_mem_history
    (M : Model S P) {φ : Formula S}
    (h : AllWorldValid M φ)
    {t : World P S.EventType}
    (ht : t ∈ M.history.val) :
    ⟪t⟫ ⊨[M]φ :=
  h (M.time_le_of_mem ht)

/-- An all-world validity holds at every end-of-time world. -/
theorem AllWorldValid.at_end
    (M : Model S P) {φ : Formula S}
    (h : AllWorldValid M φ)
    (p : P) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]φ :=
  h (PreHistory.happensBeforeEq_refl _)

notation:55 "□W⊨[" M "]" φ =>
  AllWorldValid M φ

/-- Paper: Definition 3.5.1 (active participants). `p` is active when some
event-tuple of `H` is at `p`. -/
@[simp] def IsActive
    (H : History P (S.EventType))
    (p : P) : Prop :=
  ∃ t : World P (S.EventType), t ∈ H.val ∧ t.place = p

/-- Paper: Lemma 3.5.3. `p` is active exactly when `↓⊤` holds at `p` at the
end of time. -/
theorem active_iff_past_top
    (M : Model S P)
    (p : P) :
    IsActive (H := M.history) p ↔
      (⟪⟨p, †, M.history.val⟩⟫ ⊨[M]↓ᶠ ⊤ᶠ) :=
  ⟨fun ⟨t, ht, hp⟩ => ⟨t, ht, hp, Sat.top M t⟩, fun ⟨t, ht, hp, _⟩ => ⟨t, ht, hp⟩⟩

/-! ### Named forms of `Sat.or` and `Sat.and` -/

section CaseAnalysis

variable {M : Model S P} {w : World P S.EventType}

/-- A satisfied disjunction has a satisfied disjunct. -/
theorem sat_or_cases
    {φ ψ : Formula S}
    (h : ⟪w⟫ ⊨[M](φ ∨ᶠ ψ)) :
    (⟪w⟫ ⊨[M] φ) ∨ (⟪w⟫ ⊨[M] ψ) :=
  (Sat.or M w φ ψ).1 h

/-- The right conjunct of a satisfied conjunction. -/
theorem sat_and_right
    {φ ψ : Formula S}
    (h : ⟪w⟫ ⊨[M](φ ∧ᶠ ψ)) :
    ⟪w⟫ ⊨[M] ψ :=
  ((Sat.and M w φ ψ).1 h).2

end CaseAnalysis

end Logic
end ModalDistribution
