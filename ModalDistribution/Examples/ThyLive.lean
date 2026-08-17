import ModalDistribution.Logic.AxiomSystem
import ModalDistribution.Logic.Properties
import ModalDistribution.Logic.Syntax
import ModalDistribution.Core.Prehistory
import ModalDistribution.Core.History

/-!
# Theory `ThyLive`

We formalise the liveness theory.  The theory is
parametrised by a distinguished predicate symbol `liveSymb`, and contains the
axioms `LiveAlways` and `LiveSeq`, together with two knowledge axiom
schemes.  This file records the theory and lemmas and
propositions that depend on it.
-/

namespace ModalDistribution
namespace Examples

open ModalDistribution
open ModalDistribution.Logic
open History
open PreHistory
open World
open scoped Formula

set_option autoImplicit false

variable {S : Signature}

section Axioms

/-- Paper: Figure 6, axiom (LiveAlways). Axiom `LiveAlways`: being live is independent of time. -/
@[simp] def liveAlwaysAxiom
    (liveSymb : Signature.PredSymb S) :
    Formula S :=
  (Formula.predicate0 liveSymb) ⇔ᶠ
    ⤒ᶠ (Formula.predicate0 liveSymb)

/-- Paper: Figure 6, axiom (LiveSeq). Axiom `LiveSeq`: live participants act sequentially. -/
@[simp] def liveSeqAxiom
    (liveSymb : Signature.PredSymb S) :
    Formula S :=
  (Formula.predicate0 liveSymb) ⇒ᶠ Formula.seq

/-- Paper: Figure 6, axiom-scheme (Knowledge♢↓). Axiom-scheme `Knowledge₍⋄₎`. -/
@[simp] def knowledgeDiamondAxiom
    (liveSymb : Signature.PredSymb S)
    (ls : List (Signature.Value S))
    (φ : Formula S) :
    Formula S :=
  (⤒ᶠ (♢ᶠ↓[ls]
    ((Formula.predicate0 liveSymb) ∧ᶠ φ))) ⇒ᶠ
    ((Formula.predicate0 liveSymb) ⇒ᶠ
      ↕ᶠ (♢ᶠ↓[ls] φ))

/-- Paper: Figure 6, axiom-scheme (Knowledge□↓). Axiom-scheme `Knowledge₍⋄⇓₎`. -/
@[simp] def knowledgeBoxAxiom
    (liveSymb : Signature.PredSymb S)
    (ls : List (Signature.Value S))
    (φ : Formula S) :
    Formula S :=
  (⤒ᶠ □ᶠ↓[ls]
    ((Formula.predicate0 liveSymb) ∧ᶠ φ)) ⇒ᶠ
    ((Formula.predicate0 liveSymb) ⇒ᶠ
      ↕ᶠ (□ᶠ↓[ls] φ))

/-- Paper: Definition 5.2.4 (the theory of liveness). The collection of liveness axioms (`ThyLive`). -/
@[simp] def ThyLive
    (liveSymb : Signature.PredSymb S) :
    Set (Formula S) :=
  { φ |
      φ = liveAlwaysAxiom (S := S) liveSymb ∨
      φ = liveSeqAxiom (S := S) liveSymb ∨
      (∃ ls ψ,
        φ = knowledgeDiamondAxiom (S := S) liveSymb ls ψ) ∨
      (∃ ls ψ,
        φ = knowledgeBoxAxiom (S := S) liveSymb ls ψ) }

end Axioms

section Projections

variable {P : Type} [Nonempty P] {M : Model S P} {liveSymb : Signature.PredSymb S}

/-- Project validity of `(LiveAlways)` out of a model of `ThyLive`. -/
theorem thyLive_liveAlways (hTheory : M ⊨ᵀ ThyLive liveSymb) :
    □W⊨[M] liveAlwaysAxiom (S := S) liveSymb :=
  hTheory (Or.inl rfl)

/-- Project validity of `(LiveSeq)` out of a model of `ThyLive`. -/
theorem thyLive_liveSeq (hTheory : M ⊨ᵀ ThyLive liveSymb) :
    □W⊨[M] liveSeqAxiom (S := S) liveSymb :=
  hTheory (Or.inr (Or.inl rfl))

/-- Project validity of a `(Knowledge♢↓)` instance out of a model of `ThyLive`. -/
theorem thyLive_knowledgeDiamond (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    □W⊨[M] knowledgeDiamondAxiom (S := S) liveSymb ls φ :=
  hTheory (Or.inr (Or.inr (Or.inl ⟨ls, φ, rfl⟩)))

/-- Project validity of a `(Knowledge□↓)` instance out of a model of `ThyLive`. -/
theorem thyLive_knowledgeBox (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (ls : List (Signature.Value S)) (φ : Formula S) :
    □W⊨[M] knowledgeBoxAxiom (S := S) liveSymb ls φ :=
  hTheory (Or.inr (Or.inr (Or.inr ⟨ls, φ, rfl⟩)))

end Projections


section Results

variable (P : Type) [Nonempty P]
variable (M : Model S P)
variable {liveSymb : Signature.PredSymb S}
variable {φ : Formula S}
variable {l l₁ l₂ : Signature.Value S}
variable {evt : Signature.EventType S}
variable {ls₁ ls₂ : List (Signature.Value S)}
variable {w w' t : World P (Signature.EventType S)}
variable {H : History P (Signature.EventType S)}

/-- Paper: Lemma 5.2.7. Sometime knowledge lifts to the end of time. -/
theorem sometime_past_end
    {w : World P (Signature.EventType S)}
    (hSat : ⟪w⟫ ⊨[M]↕ᶠ(♢ᶠ[]↓ᶠ (Formula.ofEvent evt))) :
    ⟪⟨w.place, †, M.history.val⟩⟫ ⊨[M] ♢ᶠ[]↓ᶠ (Formula.ofEvent evt) := by
  classical
  have hAtEnd :
      ⟪⟨w.place, †, M.history.val⟩⟫ ⊨[M]
        ↓ᶠ (♢ᶠ[]↓ᶠ (Formula.ofEvent evt)) :=
    (Sat.atEnd (M := M) (w := w)
      (φ := ↓ᶠ (♢ᶠ[]↓ᶠ (Formula.ofEvent evt)))).1
      (by simpa [Formula.sometime] using hSat)
  obtain ⟨t, ht_mem, ht_place, hDiamond⟩ :=
    (Sat.past (M := M)
      (w := ⟨w.place, †, M.history.val⟩)
      (φ := ♢ᶠ[]↓ᶠ (Formula.ofEvent evt))).1 hAtEnd
  have hBefore : t.time ≺− M.history.val :=
    happensBefore_of_mem (P := P) (Event := Signature.EventType S) ht_mem
  have hSubset_t_plain : t.time ⊆ M.history.val := by
    simpa using
      History.predecessorHistory_subset (H := M.history) hBefore
  have hSubset_t : t.time ⊆trn M.history.val :=
    transitiveSubset_of_subset (P := P) (Event := Signature.EventType S)
      hSubset_t_plain
      (by
        simpa using
          History.hereditarilyTransitive
            (History.predecessorHistory (H := M.history) hBefore))
  obtain ⟨q, hPastEvt⟩ :=
    (Sat.diamondEmpty (M := M)
      (w := t)
      (φ := ↓ᶠ (Formula.ofEvent evt))).1 hDiamond
  have hPastGlobal :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] ↓ᶠ (Formula.ofEvent evt) :=
    sat_past_event_of_subset_to_history (M := M)
      (w := ⟨q, †, t.time⟩)
      (evt := evt)
      (hSubset := hSubset_t)
      hPastEvt
  have hWitness :
      ∃ r : P,
        ⟪⟨r, †, M.history.val⟩⟫ ⊨[M] ↓ᶠ (Formula.ofEvent evt) :=
    ⟨q, hPastGlobal⟩
  have hDiamondEnd :=
    sat_diamondEmpty_of_local (M := M)
      (w := ⟨w.place, †, M.history.val⟩)
      (φ := ↓ᶠ (Formula.ofEvent evt)) hWitness
  simpa [Formula.diamondPast, Formula.diamondEmpty]
    using hDiamondEnd

/-- `LiveAlways` transports end-of-time liveness to any witnessed prefix. -/
theorem live_at_predecessor
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {w : World P (Signature.EventType S)}
    (hMem : w ∈ M.history.val)
    (hLive : ⟪⟨w.place, †, M.history.val⟩⟫ ⊨[M]Formula.predicate0 liveSymb) :
    ⟪⟨w.place, †,
      (predecessorHistory (H := M.history)
        (happensBefore_of_mem (P := P) (Event := Signature.EventType S) hMem)).val⟩⟫
      ⊨[M] Formula.predicate0 liveSymb := by
  classical
  have hAlwaysMem :
      liveAlwaysAxiom (S := S) liveSymb ∈ ThyLive liveSymb := by
    simp [ThyLive]
  have hAlways :
      AllWorldValid M (liveAlwaysAxiom (S := S) liveSymb) :=
    hTheory hAlwaysMem
  have hBefore : w.time ≺− M.history.val :=
    happensBefore_of_mem (P := P) (Event := Signature.EventType S) hMem
  set Hpre :=
      History.predecessorHistory (H := M.history) hBefore
    with hHpre
  have hIff :
      ⟪⟨w.place, w.event, Hpre.val⟩⟫ ⊨[M]
        (Formula.predicate0 liveSymb ⇔ᶠ
          ⤒ᶠ (Formula.predicate0 liveSymb)) :=
    AllWorldValid_predecessor (M := M)
      (φ := liveAlwaysAxiom (S := S) liveSymb)
      hAlways (by
        simpa [World.place, World.event, World.time]
          using hMem)
  have hAtEnd :
      ⟪⟨w.place, w.event, Hpre.val⟩⟫ ⊨[M]
        ⤒ᶠ (Formula.predicate0 liveSymb) :=
    (Sat.atEnd (M := M)
      (w := ⟨w.place, w.event, Hpre.val⟩)
      (φ := Formula.predicate0 liveSymb)).2 hLive
  have hLivePreEvent :
      ⟪⟨w.place, w.event, Hpre.val⟩⟫ ⊨[M]
        Formula.predicate0 liveSymb :=
    Sat.iff_mpr (M := M)
      (w := ⟨w.place, w.event, Hpre.val⟩)
      (φ := Formula.predicate0 liveSymb)
      (ψ := ⤒ᶠ (Formula.predicate0 liveSymb))
      hIff hAtEnd
  have hLivePre :
      ⟪⟨w.place, †, Hpre.val⟩⟫ ⊨[M]
        Formula.predicate0 liveSymb := by
    simpa [Formula.predicate0, Sat, World.place, World.time]
      using hLivePreEvent
  simpa [Hpre, hHpre]
    using hLivePre

/-- Paper: Lemma 5.2.10(1). Liveness at world equivalent to liveness at end-of-time (Liveness equivalence).
 Liveness does not depend on time: a participant is live at a specific world
if and only if it is live at the end-of-time world for that participant.
This follows from the liveness-always axiom (live ⇔ ⤒ live).

See also: `alwaysLiveEquivBackward`, liveness-always axiom. -/
theorem alwaysLiveEquivForward
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {t : World P (Signature.EventType S)}
    (ht : t ∈ M.history.val) :
    (⟪t⟫ ⊨[M] Formula.predicate0 liveSymb) ↔
      (⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M] Formula.predicate0 liveSymb) := by
  classical
  have hAlwaysMem :
      liveAlwaysAxiom (S := S) liveSymb ∈ ThyLive liveSymb := by
    simp [ThyLive]
  have hAlways :
      AllWorldValid M (liveAlwaysAxiom (S := S) liveSymb) :=
    hTheory hAlwaysMem
  have hIff :
      ⟪t⟫ ⊨[M]
        (Formula.predicate0 liveSymb ⇔ᶠ
          ⤒ᶠ (Formula.predicate0 liveSymb)) :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := liveAlwaysAxiom (S := S) liveSymb)
      hAlways ht
  constructor
  · intro hLocal
    have hAtEnd :
        ⟪t⟫ ⊨[M]
          ⤒ᶠ (Formula.predicate0 liveSymb) :=
      (Sat.iff_mp (M := M)
        (w := t)
        (φ := Formula.predicate0 liveSymb)
        (ψ := ⤒ᶠ (Formula.predicate0 liveSymb))
        hIff) hLocal
    have hGlobal :
        ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb :=
      (Sat.atEnd (M := M)
        (w := t)
        (φ := Formula.predicate0 liveSymb)).1 hAtEnd
    simpa [Sat, World.place, World.event, World.time]
      using hGlobal
  · intro hGlobal
    have hAtEnd :
        ⟪t⟫ ⊨[M]
          ⤒ᶠ (Formula.predicate0 liveSymb) :=
      (Sat.atEnd (M := M)
        (w := t)
        (φ := Formula.predicate0 liveSymb)).2
        (by
          simpa [Sat, World.place, World.event, World.time]
            using hGlobal)
    have hLocal' :
        ⟪⟨t.place, t.event, t.time⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb :=
      (Sat.iff_mpr (M := M)
        (w := ⟨t.place, t.event, t.time⟩)
        (φ := Formula.predicate0 liveSymb)
        (ψ := ⤒ᶠ (Formula.predicate0 liveSymb))
        hIff) hAtEnd
    simpa [Sat, World.place, World.event, World.time]
      using hLocal'

/-- Paper: Lemma 5.2.10(2). Liveness at any two worlds with same participant.
 Liveness does not depend on time: if two worlds have the same participant (place),
then liveness holds at one if and only if it holds at the other. This is a direct
consequence of the forward direction applied twice.

See also: `alwaysLiveEquivForward`, liveness-always axiom. -/
theorem alwaysLiveEquivBackward
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {t t' : World P (Signature.EventType S)}
    (ht : t ∈ M.history.val)
    (ht' : t' ∈ M.history.val)
    (hplace : t.place = t'.place) :
    (⟪t⟫ ⊨[M] Formula.predicate0 liveSymb) ↔
      (⟪t'⟫ ⊨[M] Formula.predicate0 liveSymb) := by
  classical
  have h_t :=
    alwaysLiveEquivForward (M := M)
      (t := t) (hTheory := hTheory) (ht := ht)
  have h_t' :=
    alwaysLiveEquivForward (M := M)
      (t := t') (hTheory := hTheory) (ht := ht')
  constructor
  · intro hLocal
    have hGlobal :
        ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb :=
      h_t.1 hLocal
    have hGlobal' :
        ⟪⟨t'.place, †, M.history.val⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb := by
      have :=
        Eq.subst
          (motive :=
            fun p : P =>
              Sat M p † M.history.val
                (Formula.predicate0 liveSymb))
          hplace hGlobal
      simpa [Sat, World.place, World.event, World.time]
        using this
    exact h_t'.2 hGlobal'
  · intro hLocal'
    have hGlobal' :
        ⟪⟨t'.place, †, M.history.val⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb :=
      h_t'.1 hLocal'
    have hGlobal :
        ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb := by
      have :=
        Eq.subst
          (motive :=
            fun p : P =>
              Sat M p † M.history.val
                (Formula.predicate0 liveSymb))
          hplace.symm hGlobal'
      simpa [Sat, World.place, World.event, World.time]
        using this
    exact h_t.2 hGlobal

/-- Paper: Lemma 5.2.10(3). Liveness at an event-tuple of the model implies liveness at every past
event at the same place. -/
theorem live_allPast
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {t : World P (Signature.EventType S)}
    (ht : t ∈ M.history.val)
    (hLive : ⟪t⟫ ⊨[M] Formula.predicate0 liveSymb) :
    ⟪t⟫ ⊨[M]⇓ᶠ (Formula.predicate0 liveSymb) := by
  classical
  refine Sat.not_intro (M := M) (w := t)
    (φ := ↓ᶠ (¬ᶠ (Formula.predicate0 liveSymb))) ?_
  intro hPast
  obtain ⟨t', ht'_mem, ht'_place, hNot⟩ :=
    (Sat.past (M := M) (w := t)
      (φ := ¬ᶠ (Formula.predicate0 liveSymb))).1 hPast
  have ht'_hist : t' ∈ M.history.val := by
    have hsub : t.time ⊆ M.history.val :=
      History.subset_of_happensBefore (H := M.history)
        (History.happensBefore_of_mem (P := P)
          (Event := Signature.EventType S) ht)
    exact hsub _ ht'_mem
  have hLive_t' : ⟪t'⟫ ⊨[M] Formula.predicate0 liveSymb :=
    (alwaysLiveEquivBackward (M := M) (hTheory := hTheory)
      (ht := ht'_hist) (ht' := ht) (hplace := ht'_place)).2 hLive
  exact
    Sat.not_elim (M := M) (w := t')
      (φ := Formula.predicate0 liveSymb) hNot hLive_t'


/-- A quorum of live participants is a quorum of sequential participants,
by the `(LiveSeq)` axiom. -/
theorem live_quorum_seq
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]Formula.predicate0 liveSymb) :
    ⊨[M]□ᶠ[[l]]Formula.seq := by
  classical
  intro p
  obtain ⟨O, hO, hAllLive⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := ⟨p, †, M.history.val⟩) (l := l)
      (φ := Formula.predicate0 liveSymb)).1 (hLiveQuorum p)
  refine
    (sat_box_singleton_exists (M := M)
      (w := ⟨p, †, M.history.val⟩) (l := l)
      (φ := Formula.seq)).2 ⟨O, hO, ?_⟩
  intro q hqO
  exact
    (Sat.imp (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := Formula.predicate0 liveSymb)
      (ψ := Formula.seq)).1
      (by
        simpa [liveSeqAxiom]
          using thyLive_liveSeq (M := M) hTheory (t := ⟨q, †, M.history.val⟩)
            (by simp [World.time]))
      (hAllLive q hqO)

/-- Instantiate the knowledge axiom at an end-of-time world. -/
theorem knowledgeDiamond_imp_at_end
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {φ : Formula S}
    (p : P) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
      (⤒ᶠ (♢ᶠ↓[[]]
        ((Formula.predicate0 liveSymb) ∧ᶠ φ))) ⇒ᶠ
        ((Formula.predicate0 liveSymb) ⇒ᶠ
          ↕ᶠ (♢ᶠ↓[[]] φ)) := by
  classical
  have hKnowMem :
      knowledgeDiamondAxiom (S := S) liveSymb [] φ ∈ ThyLive liveSymb := by
    simp [ThyLive, Formula.sometime, Formula.diamondPast]
  have hKnow :
      AllWorldValid M (knowledgeDiamondAxiom (S := S) liveSymb [] φ) :=
    hTheory hKnowMem
  exact
    AllWorldValid.at_end (M := M)
      (φ := knowledgeDiamondAxiom (S := S) liveSymb [] φ)
      hKnow p

/-- Knowledge axiom `Knowledge₍⋄₎` yields an end-of-time sometime guarantee for
arbitrary past guards. -/
theorem knowledgeDiamond_sometime_at_end_formula
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {φ : Formula S}
    {p : P}
    (hLive : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]Formula.predicate0 liveSymb)
    (hEvent : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]]((Formula.predicate0 liveSymb) ∧ᶠ φ)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]↕ᶠ (♢ᶠ↓[[]] φ) := by
  classical
  have hAtEnd :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        ⤒ᶠ (♢ᶠ↓[[]]
          ((Formula.predicate0 liveSymb) ∧ᶠ φ)) :=
    (Sat.atEnd (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ :=
        ♢ᶠ↓[[]]
          ((Formula.predicate0 liveSymb) ∧ᶠ φ))).2 hEvent
  have hImp :=
    knowledgeDiamond_imp_at_end (M := M)
      (hTheory := hTheory) (φ := φ) (p := p)
  have hLiveImp :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        (Formula.predicate0 liveSymb) ⇒ᶠ
          ↕ᶠ (♢ᶠ↓[[]] φ) :=
    Sat.imp_elim (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ :=
        ⤒ᶠ (♢ᶠ↓[[]]
          ((Formula.predicate0 liveSymb) ∧ᶠ φ)))
      (ψ :=
        (Formula.predicate0 liveSymb) ⇒ᶠ
          ↕ᶠ (♢ᶠ↓[[]] φ))
      hImp hAtEnd
  exact
    Sat.imp_elim (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := Formula.predicate0 liveSymb)
      (ψ := ↕ᶠ (♢ᶠ↓[[]] φ))
      hLiveImp hLive

/-- Specialisation of `knowledgeDiamond_sometime_at_end_formula` to event formulas. -/
theorem knowledgeDiamond_sometime_at_end
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {p : P}
    (hLive : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]Formula.predicate0 liveSymb)
    (hEvent : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]]((Formula.predicate0 liveSymb)
      ∧ᶠ Formula.ofEvent evt)) :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        ↕ᶠ (♢ᶠ↓[[]] (Formula.ofEvent evt)) := by
  classical
  exact
    knowledgeDiamond_sometime_at_end_formula (M := M)
      (hTheory := hTheory)
      (hLive := hLive) (hEvent := hEvent)

/-!
  A live participant that globally knows a quorum fact eventually comes to know that
  quorum from its local perspective.  This packages the knowledge axiom
  `Knowledge₍⋄⇓₎`, and will be shared across the liveness developments.
-/
theorem live_eventually_knows_box
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hQuorum : ⊨[M]□ᶠ↓[[l]]((Formula.predicate0 liveSymb) ∧ᶠ φ)) :
    ⊨[M](Formula.predicate0 liveSymb) ⇒ᶠ ↕ᶠ (□ᶠ↓[[l]] φ) := by
  classical
  intro p
  refine Sat.imp_intro (M := M) (w := ⟨p, †, M.history.val⟩) ?_
  intro hLiveTop

  -- The knowledge axiom instance we need.
  have hKnowMem :
      knowledgeBoxAxiom (S := S)
        liveSymb [l] φ ∈ ThyLive liveSymb := by
    dsimp [ThyLive]
    refine Or.inr ?_
    refine Or.inr ?_
    refine Or.inr ?_
    exact ⟨[l], φ, rfl⟩

  have hKnowledge :
      AllWorldValid M
        (knowledgeBoxAxiom (S := S)
          liveSymb [l] φ) :=
    hTheory hKnowMem

  have hAx :=
    AllWorldValid.at_end (M := M)
      (φ := knowledgeBoxAxiom (S := S)
        liveSymb [l] φ)
      hKnowledge p

  have hAtEnd :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        ⤒ᶠ (□ᶠ↓[[l]]
          ((Formula.predicate0 liveSymb) ∧ᶠ φ)) :=
    (Sat.atEnd (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := □ᶠ↓[[l]]
        ((Formula.predicate0 liveSymb) ∧ᶠ φ))).2 (hQuorum p)

  have hImp :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        (Formula.predicate0 liveSymb) ⇒ᶠ
          ↕ᶠ (□ᶠ↓[[l]] φ) :=
    Sat.imp_elim (M := M) (w := ⟨p, †, M.history.val⟩)
      (φ := ⤒ᶠ (□ᶠ↓[[l]]
          ((Formula.predicate0 liveSymb) ∧ᶠ φ)))
      (ψ := (Formula.predicate0 liveSymb) ⇒ᶠ
          ↕ᶠ (□ᶠ↓[[l]] φ))
      hAx hAtEnd

  exact
    Sat.imp_elim (M := M) (w := ⟨p, †, M.history.val⟩)
      (φ := Formula.predicate0 liveSymb)
      (ψ := ↕ᶠ (□ᶠ↓[[l]] φ))
      hImp hLiveTop

private theorem live_boxPast_nests_past
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hQuorum : ⊨[M]□ᶠ↓[[l]]((Formula.predicate0 liveSymb) ∧ᶠ φ))
    {q : P}
    (hPastLiveφ :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]Formula.past ((Formula.predicate0 liveSymb) ∧ᶠ φ)) :
    ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]Formula.past ((Formula.predicate0 liveSymb) ∧ᶠ □ᶠ↓[[l]] φ) := by
  classical
  have hKnowMem :
      knowledgeBoxAxiom (S := S) liveSymb [l] φ ∈
        ThyLive liveSymb := by
    dsimp [ThyLive]
    refine Or.inr ?_
    refine Or.inr ?_
    refine Or.inr ?_
    exact ⟨[l], φ, rfl⟩
  have hKnowledge :
      AllWorldValid M
        (knowledgeBoxAxiom (S := S)
          liveSymb [l] φ) :=
    hTheory hKnowMem
  obtain ⟨t, ht_mem, ht_place, hLiveφ_t⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := (Formula.predicate0 liveSymb) ∧ᶠ φ)).1 hPastLiveφ
  have ht_mem_history : t ∈ M.history.val := by
    simpa [World.time] using ht_mem
  have hLive_t :
      ⟪t⟫ ⊨[M]Formula.predicate0 liveSymb :=
    (Sat.and (M := M)
      (w := t)
      (φ := Formula.predicate0 liveSymb)
      (ψ := φ)).1 hLiveφ_t |>.1
  have hBox_q :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
        □ᶠ↓[[l]]
          ((Formula.predicate0 liveSymb) ∧ᶠ φ) := by
    simpa using hQuorum q
  have hBox_tplace :
      ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M]
        □ᶠ↓[[l]]
          ((Formula.predicate0 liveSymb) ∧ᶠ φ) :=
    Eq.subst
      (motive := fun x =>
        ⟪⟨x, †, M.history.val⟩⟫ ⊨[M]
          □ᶠ↓[[l]]
            ((Formula.predicate0 liveSymb) ∧ᶠ φ))
      ht_place.symm hBox_q
  have hAtEndBox :
      ⟪t⟫ ⊨[M]
        ⤒ᶠ (□ᶠ↓[[l]]
          ((Formula.predicate0 liveSymb) ∧ᶠ φ)) :=
    (Sat.atEnd (M := M)
      (w := t)
      (φ := □ᶠ↓[[l]]
        ((Formula.predicate0 liveSymb) ∧ᶠ φ))).2 hBox_tplace
  have hKnow_t :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := knowledgeBoxAxiom (S := S)
        liveSymb [l] φ)
      hKnowledge ht_mem_history
  have hLiveImp :
      ⟪t⟫ ⊨[M]
        (Formula.predicate0 liveSymb) ⇒ᶠ
          ↕ᶠ (□ᶠ↓[[l]] φ) :=
    Sat.imp_elim (M := M)
      (w := t)
      (φ :=
        ⤒ᶠ (□ᶠ↓[[l]]
          ((Formula.predicate0 liveSymb) ∧ᶠ φ)))
      (ψ :=
        (Formula.predicate0 liveSymb) ⇒ᶠ
          ↕ᶠ (□ᶠ↓[[l]] φ))
      hKnow_t hAtEndBox
  have hSometime :
      ⟪t⟫ ⊨[M]
        ↕ᶠ (□ᶠ↓[[l]] φ) :=
    Sat.imp_elim (M := M)
      (w := t)
      (φ := Formula.predicate0 liveSymb)
      (ψ := ↕ᶠ (□ᶠ↓[[l]] φ))
      hLiveImp hLive_t
  have hPast_box_tplace :
      ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M]
        ↓ᶠ (□ᶠ↓[[l]] φ) :=
    (Sat.atEnd (M := M)
      (w := t)
      (φ := ↓ᶠ (□ᶠ↓[[l]] φ))).1
      (by simpa [Formula.sometime] using hSometime)
  have hPast_box_q :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
        ↓ᶠ (□ᶠ↓[[l]] φ) :=
    Eq.subst
      (motive := fun x =>
        ⟪⟨x, †, M.history.val⟩⟫ ⊨[M]
          ↓ᶠ (□ᶠ↓[[l]] φ))
      ht_place hPast_box_tplace
  obtain ⟨tBox, htBox_mem, htBox_place, hBox_tBox⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := □ᶠ↓[[l]] φ)).1 hPast_box_q
  have hLive_end_t :
      ⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M]
        Formula.predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
      (hTheory := hTheory)
      (t := t)
      (ht := ht_mem)).1 hLive_t
  have hLive_end_q :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
        Formula.predicate0 liveSymb :=
    Eq.subst
      (motive := fun x =>
        ⟪⟨x, †, M.history.val⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb)
      ht_place hLive_end_t
  have hLive_end_tBox :
      ⟪⟨tBox.place, †, M.history.val⟩⟫ ⊨[M]
        Formula.predicate0 liveSymb :=
    Eq.subst
      (motive := fun x =>
        ⟪⟨x, †, M.history.val⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb)
      htBox_place.symm hLive_end_q
  have hLive_tBox :
      ⟪tBox⟫ ⊨[M]
        Formula.predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
      (hTheory := hTheory)
      (t := tBox)
      (ht := htBox_mem)).2 hLive_end_tBox
  have hConj :
      ⟪tBox⟫ ⊨[M]
        (Formula.predicate0 liveSymb) ∧ᶠ
          □ᶠ↓[[l]] φ :=
    (Sat.and (M := M)
      (w := tBox)
      (φ := Formula.predicate0 liveSymb)
      (ψ := □ᶠ↓[[l]] φ)).2
      ⟨hLive_tBox, hBox_tBox⟩
  exact
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := (Formula.predicate0 liveSymb) ∧ᶠ □ᶠ↓[[l]] φ)).2
      ⟨tBox, htBox_mem, htBox_place, hConj⟩

/-- Paper: Lemma 5.2.12. Liveness quorum boxes promote to nested
quorum boxes under `ThyLive`. -/
theorem live_boxPast_nests
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hQuorum : ⊨[M]□ᶠ↓[[l]]((Formula.predicate0 liveSymb) ∧ᶠ φ)) :
    ⊨[M]□ᶠ↓[[l]]((Formula.predicate0 liveSymb) ∧ᶠ □ᶠ↓[[l]] φ) := by
  classical
  refine fun p => ?_
  let wₚ : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hBox_p :
      ⟪wₚ⟫ ⊨[M]
        □ᶠ[[l]]
          (Formula.past ((Formula.predicate0 liveSymb) ∧ᶠ φ)) := by
    simpa [Formula.boxPast, wₚ]
      using hQuorum p
  obtain ⟨O, hO, hAll⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := wₚ) (l := l)
      (φ := Formula.past ((Formula.predicate0 liveSymb) ∧ᶠ φ))).1 hBox_p
  refine
    (sat_box_singleton_exists (M := M)
      (w := wₚ) (l := l)
      (φ := Formula.past
        ((Formula.predicate0 liveSymb) ∧ᶠ □ᶠ↓[[l]] φ))).2 ?_
  refine ⟨O, hO, ?_⟩
  intro q hqO
  have hPastLiveφ :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
        Formula.past ((Formula.predicate0 liveSymb) ∧ᶠ φ) := by
    simpa [wₚ] using hAll q hqO
  exact
    live_boxPast_nests_past (S := S) (P := P) (M := M)
      (φ := φ) (l := l) (liveSymb := liveSymb)
      (hTheory := hTheory)
      (hQuorum := hQuorum) (q := q) hPastLiveφ

theorem live_knows_eventually_past
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {p : P}
    (hLive : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]Formula.predicate0 liveSymb)
    (hEvent : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]]((Formula.predicate0 liveSymb)
                                                    ∧ᶠ φ)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
      ↓ᶠ ((Formula.predicate0 liveSymb) ∧ᶠ
        ♢ᶠ↓[[]] (φ)) := by
  classical
  have hSometime :=
    knowledgeDiamond_sometime_at_end_formula (M := M)
      (hTheory := hTheory)
      (hLive := hLive) (hEvent := hEvent)
  have hPastDiamond :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        ↓ᶠ (♢ᶠ[]↓ᶠ (φ)) :=
    (Sat.atEnd (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := ↓ᶠ (♢ᶠ[]↓ᶠ (φ)))).1
      (by
        simpa [Formula.sometime]
          using hSometime)
  obtain ⟨tPast, ht_mem, ht_place, hDiamondPast⟩ :=
    (Sat.past (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := ♢ᶠ[]↓ᶠ (φ))).1 hPastDiamond
  have ht_mem_history : tPast ∈ M.history.val := by
    simpa [World.time] using ht_mem
  have ht_place_p : tPast.place = p := by
    simpa [World.place] using ht_place
  have hLive_end :
      ⟪⟨tPast.place, †, M.history.val⟩⟫ ⊨[M]
        Formula.predicate0 liveSymb := by
    simpa [World.place, ht_place_p.symm]
      using hLive
  have hPre :=
    live_at_predecessor (M := M)
      (hTheory := hTheory)
      (w := tPast)
      (hMem := ht_mem_history)
      (hLive := hLive_end)
  have hPre_val :
      (History.predecessorHistory (H := M.history)
        (happensBefore_of_mem (P := P)
          (Event := Signature.EventType S) ht_mem_history)).val =
        tPast.time := by
    simp [History.predecessorHistory]
  have hLivePast :
      ⟪⟨tPast.place, †, tPast.time⟩⟫ ⊨[M]
        Formula.predicate0 liveSymb := by
    simpa [hPre_val]
      using hPre
  have hLivePast_event :
      ⟪tPast⟫ ⊨[M]
        Formula.predicate0 liveSymb := by
    simpa [Formula.predicate0, Sat, World.place, World.event, World.time]
      using hLivePast
  have hConjPast :
      ⟪tPast⟫ ⊨[M]
        (Formula.predicate0 liveSymb) ∧ᶠ
          ♢ᶠ↓[[]] (φ) :=
    (Sat.and (M := M)
      (w := tPast)
      (φ := Formula.predicate0 liveSymb)
      (ψ := ♢ᶠ↓[[]] (φ))).2
      ⟨hLivePast_event, hDiamondPast⟩
  exact
    Sat.past_intro_of_prefix (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (t := tPast)
      (ht := ht_mem)
      (hp := ht_place)
      (hφ := hConjPast)

theorem live_knows_eventually_event_past
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {p : P}
    (hLive : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]Formula.predicate0 liveSymb)
    (hEvent : ⊨[M]♢ᶠ↓[[]]((Formula.predicate0 liveSymb) ∧ᶠ
        ♢ᶠ↓[[]](Formula.ofEvent evt))) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
      ↓ᶠ ((Formula.predicate0 liveSymb) ∧ᶠ
        ♢ᶠ↓[[]]
          (♢ᶠ↓[[]] (Formula.ofEvent evt))) := by
  classical
  set φ := ♢ᶠ↓[[]] (Formula.ofEvent evt) with hφ
  have hEvent_p :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        ♢ᶠ↓[[]]
          ((Formula.predicate0 liveSymb) ∧ᶠ φ) := by
    simpa [hφ] using hEvent p
  have hSometime :=
    knowledgeDiamond_sometime_at_end_formula (M := M)
      (hTheory := hTheory)
      (hLive := hLive)
      (hEvent := hEvent_p)
  have hPastDiamond :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        ↓ᶠ (♢ᶠ↓[[]] φ) :=
    (Sat.atEnd (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := ↓ᶠ (♢ᶠ↓[[]] φ))).1
      (by
        simpa [Formula.sometime]
          using hSometime)
  obtain ⟨tPast, ht_mem, ht_place, hDiamondPast⟩ :=
    (Sat.past (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := ♢ᶠ↓[[]] φ)).1 hPastDiamond
  have ht_mem_history : tPast ∈ M.history.val := by
    simpa [World.time] using ht_mem
  have ht_place_p : tPast.place = p := by
    simpa [World.place] using ht_place
  have hLive_end :
      ⟪⟨tPast.place, †, M.history.val⟩⟫ ⊨[M]
        Formula.predicate0 liveSymb := by
    simpa [World.place, ht_place_p.symm] using hLive
  have hPre :=
    live_at_predecessor (M := M)
      (hTheory := hTheory)
      (w := tPast)
      (hMem := ht_mem_history)
      (hLive := hLive_end)
  have hPre_val :
      (History.predecessorHistory (H := M.history)
        (happensBefore_of_mem (P := P)
          (Event := Signature.EventType S) ht_mem_history)).val =
        tPast.time := by
    simp [History.predecessorHistory]
  have hLivePast :
      ⟪tPast⟫ ⊨[M]
        Formula.predicate0 liveSymb := by
    have hGlobal :
        ⟪⟨tPast.place, †, tPast.time⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb := by
      simpa [hPre_val]
        using hPre
    simpa [Formula.predicate0, Sat, World.place, World.event, World.time]
      using hGlobal
  have hDiamondPast' :
      ⟪tPast⟫ ⊨[M]
        ♢ᶠ↓[[]] φ := by
    simpa [Formula.diamondPast, Formula.diamondEmpty, id]
      using hDiamondPast
  have hConjPast :
      ⟪tPast⟫ ⊨[M]
        (Formula.predicate0 liveSymb) ∧ᶠ
          ♢ᶠ↓[[]] φ :=
    (Sat.and (M := M)
      (w := tPast)
      (φ := Formula.predicate0 liveSymb)
      (ψ := ♢ᶠ↓[[]] φ)).2
      ⟨hLivePast, hDiamondPast'⟩
  have hPastIntro :=
    Sat.past_intro_of_prefix (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (t := tPast)
      (ht := ht_mem)
      (hp := ht_place)
      (hφ := hConjPast)
  simpa [hφ] using hPastIntro

/-- Empty-learner past diamonds compose idempotently for event formulas. -/
theorem diamondEmpty_past_event_flat
    {w : World P (Signature.EventType S)}
    (hMem : w ∈ M.history.val)
    (hDiamond : ⟪w⟫ ⊨[M]♢ᶠ[]↓ᶠ (♢ᶠ[]↓ᶠ (Formula.ofEvent evt))) :
    ⟪w⟫ ⊨[M] ♢ᶠ[]↓ᶠ (Formula.ofEvent evt) := by
  classical
  -- Package the time component of `w` as a standalone history.
  have hBefore : w.time ≺− M.history.val :=
    History.happensBefore_of_mem (P := P)
      (Event := Signature.EventType S) (H := M.history.val)
      (e := w) hMem
  let Hw := History.predecessorHistory (H := M.history) hBefore
  -- Unfold the outer diamond to obtain a witness in the local view of `w`.
  obtain ⟨q₁, hPast₁⟩ :=
    (Sat.diamondEmpty (M := M) (w := w)
      (φ := ↓ᶠ (♢ᶠ[]↓ᶠ (Formula.ofEvent evt)))).1
      (by simpa [Formula.diamondPast, Formula.diamondEmpty, id]
        using hDiamond)
  -- That witness gives a predecessor world satisfying the inner diamond.
  obtain ⟨t₁, ht₁_mem, ht₁_place, hDiamond₁⟩ :=
    (Sat.past (M := M)
      (w := ⟨q₁, †, w.time⟩)
      (φ := ♢ᶠ[]↓ᶠ (Formula.ofEvent evt))).1 hPast₁
  -- Unfold the inner diamond to obtain a concrete past event.
  obtain ⟨q₂, hPast₂⟩ :=
    (Sat.diamondEmpty (M := M) (w := t₁)
      (φ := ↓ᶠ (Formula.ofEvent evt))).1
      (by simpa [Formula.diamondPast, Formula.diamondEmpty, id]
        using hDiamond₁)
  obtain ⟨t₂, ht₂_mem, ht₂_place, hEvent⟩ :=
    (Sat.past (M := M)
      (w := ⟨q₂, †, t₁.time⟩)
      (φ := Formula.ofEvent evt)).1 hPast₂
  -- Show that the event we uncovered lies in the original timeline of `w`.
  have hSubset_t₁ : t₁.time ⊆ w.time := by
    have hBefore_t₁ : t₁.time ≺− Hw.val := by
      have hAcc : t₁ ≪ w := by
        simpa [World.accessible, World.time]
          using ht₁_mem
      simpa [Hw, World.time] using
        PreHistory.happensBefore_of_accessible
          (P := P) (Event := Signature.EventType S) hAcc
    simpa [Hw] using
      History.subset_of_happensBefore (H := Hw) hBefore_t₁
  have hEvent_in_time :
      ⟪⟨q₂, †, w.time⟩⟫ ⊨[M] ↓ᶠ (Formula.ofEvent evt) :=
    sat_past_of_subset (M := M)
      (hSubset := hSubset_t₁) hPast₂
  -- Repackage the witness for the outer diamond.
  exact
    sat_diamondEmpty_of_local (M := M) (w := w)
      (φ := ↓ᶠ (Formula.ofEvent evt)) ⟨q₂, hEvent_in_time⟩

/-- A live participant eventually reaches a past state guaranteeing quorum knowledge. -/
theorem live_knows_eventually_quorum_past
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {p : P}
    (hLive : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]Formula.predicate0 liveSymb)
    (hQuorum : ⊨[M]♢ᶠ↓[[]]((Formula.predicate0 liveSymb) ∧ᶠ
        □ᶠ↓[id [l₁]](Formula.ofEvent evt))) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
      ↓ᶠ ((Formula.predicate0 liveSymb) ∧ᶠ
        □ᶠ↓[id [l₁]] (Formula.ofEvent evt)) := by
  classical
  set φBox :=
    □ᶠ↓[id [l₁]] (Formula.ofEvent evt) with hφBox
  have hQuorum_p :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        ♢ᶠ↓[[]]
          ((Formula.predicate0 liveSymb) ∧ᶠ φBox) := by
    simpa [hφBox] using hQuorum p
  have hSometime :=
    knowledgeDiamond_sometime_at_end_formula (M := M)
      (hTheory := hTheory)
      (hLive := hLive)
      (hEvent := hQuorum_p)
  have hPastDiamond :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        ↓ᶠ (♢ᶠ[]↓ᶠ φBox) :=
    (Sat.atEnd (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := ↓ᶠ (♢ᶠ[]↓ᶠ φBox))).1
      (by
        simpa [Formula.sometime]
          using hSometime)
  obtain ⟨tPast, ht_mem, ht_place, hDiamondPast⟩ :=
    (Sat.past (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := ♢ᶠ[]↓ᶠ φBox)).1 hPastDiamond
  have ht_mem_history : tPast ∈ M.history.val := by
    simpa [World.time] using ht_mem
  have ht_place_p : tPast.place = p := by
    simpa [World.place] using ht_place
  have hLive_end :
      ⟪⟨tPast.place, †, M.history.val⟩⟫ ⊨[M]
        Formula.predicate0 liveSymb := by
    simpa [World.place, ht_place_p.symm]
      using hLive
  have hPre :=
    live_at_predecessor (M := M)
      (hTheory := hTheory)
      (w := tPast)
      (hMem := ht_mem_history)
      (hLive := hLive_end)
  have hPre_val :
      (History.predecessorHistory (H := M.history)
        (happensBefore_of_mem (P := P)
          (Event := Signature.EventType S) ht_mem_history)).val =
        tPast.time := by
    simp [History.predecessorHistory]
  have hLivePast :
      ⟪tPast⟫ ⊨[M]
        Formula.predicate0 liveSymb := by
    have hGlobal :
        ⟪⟨tPast.place, †, tPast.time⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb := by
      simpa [hPre_val] using hPre
    simpa [Formula.predicate0, Sat, World.place, World.event, World.time]
      using hGlobal
  have hDiamondPast' :
      ⟪tPast⟫ ⊨[M]
        ♢ᶠ↓[[]] φBox := by
    simpa [Formula.diamondPast, Formula.diamondEmpty, id]
      using hDiamondPast
  have hBoxPast :
      ⟪tPast⟫ ⊨[M] φBox := by
    have hBox :=
      pastDiamondBoxCollapsesToPresentBox (M := M)
        (w := tPast) (l := l₁)
        (φ := Formula.ofEvent evt)
        (hMem := ht_mem_history)
        (by
          simpa [Formula.diamondPast, Formula.diamondEmpty,
            id, hφBox]
            using hDiamondPast')
    simpa [hφBox] using hBox
  have hConjPast :
      ⟪tPast⟫ ⊨[M]
        (Formula.predicate0 liveSymb) ∧ᶠ φBox :=
    (Sat.and (M := M)
      (w := tPast)
      (φ := Formula.predicate0 liveSymb)
      (ψ := φBox)).2
      ⟨hLivePast, hBoxPast⟩
  have hPastIntro :=
    Sat.past_intro_of_prefix (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (t := tPast)
      (ht := ht_mem)
      (hp := ht_place)
      (hφ := hConjPast)
  simpa [hφBox] using hPastIntro

/-- Paper: Proposition 5.2.8. Live quorums eventually know past facts. -/
theorem live_eventually_knows
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hLive : ⊨[M]□ᶠ[id [l]](Formula.predicate0 liveSymb))
    (hEvent : ⊨[M]♢ᶠ↓[[]]((Formula.predicate0 liveSymb) ∧ᶠ φ)) :
    ⊨[M]□ᶠ↓[id [l]]
      ((Formula.predicate0 liveSymb) ∧ᶠ
        ♢ᶠ↓[[]] (φ)) := by
  classical
  intro q
  have hBoxLive :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
        □ᶠ[id [l]] (Formula.predicate0 liveSymb) :=
    hLive q
  have hImp :
      ∀ q',
        (⟪⟨q', †, M.history.val⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb) →
          (⟪⟨q', †, M.history.val⟩⟫ ⊨[M]
            ↓ᶠ ((Formula.predicate0 liveSymb) ∧ᶠ
              ♢ᶠ[]↓ᶠ (φ))) := by
    intro q' hLiveLocal
    exact
      live_knows_eventually_past (M := M)
        (hTheory := hTheory) (p := q')
        (hLive := hLiveLocal) (hEvent := hEvent q')
  have hBoxPast :=
    ModalDistribution.Logic.Sat.box_of_imp (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (ts := id [l])
      (φ := Formula.predicate0 liveSymb)
      (ψ :=
        ↓ᶠ ((Formula.predicate0 liveSymb) ∧ᶠ
          ♢ᶠ[]↓ᶠ (φ)))
      (h := hImp) hBoxLive
  simpa [Formula.boxPast]
    using hBoxPast

/-- Paper: Corollary 5.2.9(1). Live quorums eventually know of past events. -/
theorem live_eventually_knows_event
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hLive : ⊨[M]□ᶠ[id [l]](Formula.predicate0 liveSymb))
    (hEvent : ⊨[M]♢ᶠ↓[[]]((Formula.predicate0 liveSymb)
        ∧ᶠ ♢ᶠ↓[[]](Formula.ofEvent evt))) :
    ⊨[M] □ᶠ↓[id [l]]
      ((Formula.predicate0 liveSymb) ∧ᶠ
        ♢ᶠ↓[[]] (Formula.ofEvent evt)) := by
  classical
  intro q
  have hBoxLive :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
        □ᶠ[id [l]] (Formula.predicate0 liveSymb) :=
    hLive q
  have hImp :
      ∀ q',
        (⟪⟨q', †, M.history.val⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb) →
          (⟪⟨q', †, M.history.val⟩⟫ ⊨[M]
            ↓ᶠ ((Formula.predicate0 liveSymb) ∧ᶠ
              ♢ᶠ[]↓ᶠ (Formula.ofEvent evt))) := by
    intro q' hLiveLocal
    have hPastNested :=
      live_knows_eventually_event_past (M := M)
        (hTheory := hTheory) (p := q')
        (hLive := hLiveLocal) (hEvent := hEvent)
    refine ModalDistribution.Logic.Sat.past_of_imp (M := M)
      (w := ⟨q', †, M.history.val⟩)
      (φ := (Formula.predicate0 liveSymb) ∧ᶠ
        ♢ᶠ[]↓ᶠ (♢ᶠ[]↓ᶠ (Formula.ofEvent evt)))
      (ψ := (Formula.predicate0 liveSymb) ∧ᶠ
        ♢ᶠ[]↓ᶠ (Formula.ofEvent evt))
      ?_ hPastNested
    intro t ht hp hConj
    have hAnd :=
      (Sat.and (M := M)
        (w := t)
        (φ := Formula.predicate0 liveSymb)
        (ψ := ♢ᶠ[]↓ᶠ (♢ᶠ[]↓ᶠ (Formula.ofEvent evt)))).1 hConj
    obtain ⟨hLive_t, hDiamondNested⟩ := hAnd
    have hMem_t : t ∈ M.history.val := by
      simpa [World.time] using ht
    have hDiamondFlat :=
      diamondEmpty_past_event_flat (M := M)
        (w := t) (hMem := hMem_t)
        (evt := evt) (hDiamond := hDiamondNested)
    exact
      (Sat.and (M := M)
        (w := t)
        (φ := Formula.predicate0 liveSymb)
        (ψ := ♢ᶠ[]↓ᶠ (Formula.ofEvent evt))).2
        ⟨hLive_t, hDiamondFlat⟩
  have hBoxPast :=
    ModalDistribution.Logic.Sat.box_of_imp (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (ts := id [l])
      (φ := Formula.predicate0 liveSymb)
      (ψ :=
        ↓ᶠ ((Formula.predicate0 liveSymb) ∧ᶠ
          ♢ᶠ[]↓ᶠ (Formula.ofEvent evt)))
      (h := hImp) hBoxLive
  simpa [Formula.boxPast]
    using hBoxPast

/-- Paper: Corollary 5.2.9(2). Live quorums eventually learn of performed events. -/
theorem live_eventually_knows_performed
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hLive : ⊨[M]□ᶠ[id [l]](Formula.predicate0 liveSymb))
    (hEvent : ⊨[M]♢ᶠ↓[[]]((Formula.predicate0 liveSymb) ∧ᶠ Formula.ofEvent evt)) :
    ⊨[M] □ᶠ↓[id [l]]
      ((Formula.predicate0 liveSymb) ∧ᶠ
        ♢ᶠ↓[[]] (Formula.ofEvent evt)) := by
  exact
    live_eventually_knows (M := M)
      (hTheory := hTheory) (hLive := hLive) (hEvent := hEvent)

/-- Paper: Corollary 5.2.9(3). Live quorums eventually know quorum facts. -/
theorem live_eventually_knows_quorum
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hLive : ⊨[M]□ᶠ[id [l]](Formula.predicate0 liveSymb))
    (hQuorum : ⊨[M]♢ᶠ↓[[]]((Formula.predicate0 liveSymb) ∧ᶠ
        □ᶠ↓[id [l₁]](Formula.ofEvent evt))) :
    ⊨[M] □ᶠ↓[id [l]]
      ((Formula.predicate0 liveSymb) ∧ᶠ
        □ᶠ↓[id [l₁]] (Formula.ofEvent evt)) := by
  classical
  intro q
  have hBoxLive :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
        □ᶠ[id [l]] (Formula.predicate0 liveSymb) :=
    hLive q
  have hImp :
      ∀ q',
        (⟪⟨q', †, M.history.val⟩⟫ ⊨[M]
          Formula.predicate0 liveSymb) →
          (⟪⟨q', †, M.history.val⟩⟫ ⊨[M]
            ↓ᶠ ((Formula.predicate0 liveSymb) ∧ᶠ
              □ᶠ↓[id [l₁]] (Formula.ofEvent evt))) := by
    intro q' hLiveLocal
    exact
      live_knows_eventually_quorum_past (M := M)
        (hTheory := hTheory) (p := q')
        (hLive := hLiveLocal) (hQuorum := hQuorum)
  have hBoxPast :=
    ModalDistribution.Logic.Sat.box_of_imp (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (ts := id [l])
      (φ := Formula.predicate0 liveSymb)
      (ψ :=
        ↓ᶠ ((Formula.predicate0 liveSymb) ∧ᶠ
          □ᶠ↓[id [l₁]] (Formula.ofEvent evt)))
      (h := hImp) hBoxLive
  simpa [Formula.boxPast]
    using hBoxPast

/-- Paper: Proposition 5.2.11. Live quorum intersections expose live witnesses. -/
theorem intertwined_two_quorums
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hIntersect : ⊨[M]♢ᶠ[id [l, l₁]]⊤ᶠ)
    (hLiveQuorum : ⊨[M]□ᶠ[id [l₁]](Formula.predicate0 liveSymb))
    (hWitness : ⊨[M]□ᶠ↓[id [l]]φ) :
    ⊨[M] ♢ᶠ↓[[]]
      ((Formula.predicate0 liveSymb) ∧ᶠ φ) := by
  classical
  -- Nonempty intersection of the quorum families for `[l, l₁]`.
  have hIntersect_nonempty :=
    (nWayQuorumIntersectionNonempty (M := M)
      (ls := [l, l₁])).1 hIntersect
  -- Choose a default participant for extracting quorums.
  let p₀ : P := Classical.choice inferInstance
  -- Quorum witnessing the `[l]` guard.
  obtain ⟨Oφ, hOφ, hAllφ⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := ⟨p₀, †, M.history.val⟩)
      (l := l) (φ := ↓ᶠ φ)).1
      (hWitness p₀)
  -- Quorum witnessing the `[l₁]` guard.
  obtain ⟨Oliv, hOliv, hAllLive⟩ :=
    (sat_box_singleton_exists (M := M)
      (w := ⟨p₀, †, M.history.val⟩)
      (l := l₁) (φ := Formula.predicate0 liveSymb)).1
      (hLiveQuorum p₀)
  -- Build a quorum family for `[l, l₁]`.
  let F_tail : QuorumFamily M [l₁] :=
    QuorumFamily.cons (M := M) (l := l₁) Oliv hOliv
      (QuorumFamily.nil M)
  let F : QuorumFamily M [l, l₁] :=
    QuorumFamily.cons (M := M) (l := l) Oφ hOφ F_tail
  -- Extract a witness from the intersecting quorums.
  obtain ⟨p, hpAll⟩ := hIntersect_nonempty F
  have hpSplit :=
    (QuorumFamily.forall_choose_cons (M := M)
      (l := l) (ls' := [l₁]) (F := F) (p := p)).1 hpAll
  obtain ⟨hpHead, hpTail⟩ := hpSplit
  have hpOφ : p ∈ Oφ := by
    simpa [F, F_tail, QuorumFamily.head,
      QuorumFamily.cons_choose_zero]
      using hpHead
  have hpTailSplit :=
    (QuorumFamily.forall_choose_cons (M := M)
      (l := l₁) (ls' := []) (F := F_tail) (p := p)).1 hpTail
  obtain ⟨hpTailHead, _⟩ := hpTailSplit
  have hpOliv : p ∈ Oliv := by
    simpa [F_tail, QuorumFamily.head,
      QuorumFamily.cons_choose_zero]
      using hpTailHead
  -- `p` is live thanks to the `[l₁]` guard.
  have hLivePresent :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        Formula.predicate0 liveSymb :=
    hAllLive p hpOliv
  -- `p` witnesses the past guard for `φ` thanks to the `[l]` guard.
  have hPastφ :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] ↓ᶠ φ :=
    hAllφ p hpOφ
  -- Extract the predecessor world realising `φ` in the past.
  obtain ⟨tPast, ht_mem, ht_place, hSatφ⟩ :=
    (Sat.past (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := φ)).1 hPastφ
  have ht_mem_history : tPast ∈ M.history.val := by
    simpa [World.time] using ht_mem
  -- Transport liveness from end-of-time to the predecessor world.
  have hGlobal :
      ⟪⟨tPast.place, †, M.history.val⟩⟫ ⊨[M]
        Formula.predicate0 liveSymb := by
    cases ht_place with
    | refl => exact hLivePresent
  have hPre :=
    live_at_predecessor (M := M)
      (hTheory := hTheory)
      (w := tPast)
      (hMem := ht_mem_history)
      (hLive := hGlobal)
  have hPre_val :
      (predecessorHistory (H := M.history)
        (happensBefore_of_mem (P := P)
          (Event := Signature.EventType S) ht_mem_history)).val =
        tPast.time := by
    simp [predecessorHistory]
  have hLivePast :
      ⟪tPast⟫ ⊨[M]
        Formula.predicate0 liveSymb := by
    simpa [Formula.predicate0, Sat, World.place, World.event, World.time, hPre_val]
      using hPre
  -- Combine the predecessor facts.
  have hConjPast :
      ⟪tPast⟫ ⊨[M]
        (Formula.predicate0 liveSymb) ∧ᶠ φ :=
    (Sat.and (M := M)
      (w := tPast)
      (φ := Formula.predicate0 liveSymb)
      (ψ := φ)).2
      ⟨hLivePast, hSatφ⟩
  have hPastIntro :=
    Sat.past_intro_of_prefix (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (t := tPast)
      (ht := ht_mem)
      (hp := ht_place)
      (hφ := hConjPast)
  have hPastWitness :
      ∃ q : P,
        ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
          ↓ᶠ ((Formula.predicate0 liveSymb) ∧ᶠ φ) :=
    ⟨p,
      by
        simpa using hPastIntro⟩
  -- Package the witness to conclude the diamond statement for every participant.
  intro q₀
  have hDiamond :=
    sat_diamondEmpty_of_local (M := M)
      (w := ⟨q₀, †, M.history.val⟩)
      (φ := ↓ᶠ ((Formula.predicate0 liveSymb) ∧ᶠ φ))
      hPastWitness
  simpa [Formula.diamondPast, Formula.diamondEmpty, id]
    using hDiamond

end Results

end Examples
end ModalDistribution
