import ModalDistribution.Logic.AxiomSystem
import ModalDistribution.Logic.Properties
import ModalDistribution.Logic.Sequentiality

/-!
# Theory `ThyLive`

We formalise the liveness theory from Section 5.2 of the paper.  The theory is
parametrised by a distinguished predicate symbol `liveSymb`, and contains the
axioms `LiveAlways`, `LiveSeq`, `LiveActive`, together with two knowledge axiom
schemes.  This file records the theory and the Section 5.2 lemmas and
propositions that depend on it; all results are currently stated with `sorry`
placeholders pending full formal proofs.
-/

namespace ModalDistribution
namespace Examples

open ModalDistribution
open ModalDistribution.Logic
open scoped Formula

set_option autoImplicit false

universe u₁ u₂ u₃ u₄ u₅ u₆

variable {S : Signature}

section Axioms

variable [DecidableEq S.VarSymb]

/-- Shorthand for the `live` predicate. -/
@[simp] def liveFormula
    (liveSymb : Signature.PredSymb S) : Formula S :=
  Logic.liveFormula liveSymb

lemma liveFormula_isClosed
    (liveSymb : Signature.PredSymb S) :
    (liveFormula liveSymb).IsClosed := by
  simp

/-- Axiom `LiveAlways`: being live is independent of time. -/
@[simp] def liveAlwaysAxiom
    (liveSymb : Signature.PredSymb S) :
    Axiom S :=
  { formula :=
      (liveFormula liveSymb) ⇔ᶠ
        ⤒ᶠ (liveFormula liveSymb)
    , isClosed := by simp }

/-- Axiom `LiveSeq`: live participants act sequentially. -/
@[simp] def liveSeqAxiom
    (liveSymb : Signature.PredSymb S) :
    Axiom S :=
  { formula :=
      (liveFormula liveSymb) ⇒ᶠ Formula.seq
    , isClosed := by simp }

/-- Axiom `LiveActive`: live participants are eventually active. -/
@[simp] def liveActiveAxiom
    (liveSymb : Signature.PredSymb S) :
    Axiom S :=
  { formula :=
      ⤒ᶠ (□ᶠ[] ((liveFormula liveSymb) ⇒ᶠ ↓ᶠ ⊤ᶠ))
    , isClosed := by simp }

/-- Axiom-scheme `Knowledge₍⋄₎`. -/
@[simp] def knowledgeDiamondAxiom
    (liveSymb : Signature.PredSymb S)
    (ls : List (Signature.Value S))
    (φ : Formula S)
    (hφ : φ.IsClosed) :
    Axiom S :=
  { formula :=
      (⤒ᶠ (♢ᶠ↓[Term.ofValues ls]
        ((liveFormula liveSymb) ∧ᶠ φ))) ⇒ᶠ
        ((liveFormula liveSymb) ⇒ᶠ
          ↕ᶠ (♢ᶠ↓[Term.ofValues ls] φ))
    , isClosed := by
        classical
        have hLive := liveFormula_isClosed (S := S) liveSymb
        have hAnd := Formula.IsClosed.and (S := S) hLive hφ
        have hPastAnd := Formula.IsClosed.past (S := S) hAnd
        have hLearnerClosed :
            Formula.listFreeVars (S := S) (Term.ofValues ls) = ∅ := by
          simpa [Term.ofValues] using
            (Formula.listFreeVars_ofValues (S := S) ls)
        have hDiamondPast :=
          Formula.IsClosed.diamond (S := S)
            (ls := Term.ofValues ls)
            (φ := ↓ᶠ ((liveFormula liveSymb) ∧ᶠ φ))
            hLearnerClosed hPastAnd
        have hPastφ := Formula.IsClosed.past (S := S) hφ
        have hDiamondφ :=
          Formula.IsClosed.diamond (S := S)
            (ls := Term.ofValues ls)
            (φ := ↓ᶠ φ)
            hLearnerClosed hPastφ
        have hSometime :=
          Formula.IsClosed.sometime (S := S) hDiamondφ
        have hImp :=
          Formula.IsClosed.imp (S := S) hLive hSometime
        exact Formula.IsClosed.imp (S := S)
          (Formula.IsClosed.atEnd (S := S) hDiamondPast) hImp }

/-- Axiom-scheme `Knowledge₍⋄⇓₎`. -/
@[simp] def knowledgeDiamondEventuallyAxiom
    (liveSymb : Signature.PredSymb S)
    (ls : List (Signature.Value S))
    (φ : Formula S)
    (hφ : φ.IsClosed) :
    Axiom S :=
  { formula :=
      (⤒ᶠ □ᶠ↓[Term.ofValues ls]
        ((liveFormula liveSymb) ∧ᶠ φ)) ⇒ᶠ
        ((liveFormula liveSymb) ⇒ᶠ
          ↕ᶠ (□ᶠ↓[Term.ofValues ls] φ))
    , isClosed := by
        classical
        have hLive := liveFormula_isClosed (S := S) liveSymb
        have hAnd := Formula.IsClosed.and (S := S) hLive hφ
        have hPastAnd := Formula.IsClosed.past (S := S) hAnd
        have hLearnerClosed :
            Formula.listFreeVars (S := S) (Term.ofValues ls) = ∅ := by
          simpa [Term.ofValues] using
            (Formula.listFreeVars_ofValues (S := S) ls)
        have hBoxPast :=
          Formula.IsClosed.box (S := S)
            (ls := Term.ofValues ls)
            (φ := ↓ᶠ ((liveFormula liveSymb) ∧ᶠ φ))
            hLearnerClosed hPastAnd
        have hPastφ := Formula.IsClosed.past (S := S) hφ
        have hBoxφ :=
          Formula.IsClosed.box (S := S)
            (ls := Term.ofValues ls)
            (φ := ↓ᶠ φ)
            hLearnerClosed hPastφ
        have hSometime :=
          Formula.IsClosed.sometime (S := S) hBoxφ
        have hImp :=
          Formula.IsClosed.imp (S := S) hLive hSometime
        exact Formula.IsClosed.imp (S := S)
          (Formula.IsClosed.atEnd (S := S) hBoxPast) hImp }

@[simp] lemma knowledgeDiamondAxiom_formula
    (liveSymb : Signature.PredSymb S)
    (ls : List (Signature.Value S))
    (φ : Formula S) (hφ : φ.IsClosed) :
    (knowledgeDiamondAxiom (S := S) liveSymb ls φ hφ).formula =
      (⤒ᶠ ♢ᶠ↓[Term.ofValues ls]
        ((liveFormula liveSymb) ∧ᶠ φ)) ⇒ᶠ
        ((liveFormula liveSymb) ⇒ᶠ
          ↕ᶠ (♢ᶠ↓[Term.ofValues ls] φ)) := rfl

/-- The collection of liveness axioms (`ThyLive`). -/
@[simp] def ThyLive
    (liveSymb : Signature.PredSymb S) :
    Theory S :=
  { ax |
      ax = liveAlwaysAxiom (S := S) liveSymb ∨
      ax = liveSeqAxiom (S := S) liveSymb ∨
      ax = liveActiveAxiom (S := S) liveSymb ∨
      (∃ ls φ hφ,
        ax = knowledgeDiamondAxiom (S := S) liveSymb ls φ hφ) ∨
      (∃ ls φ hφ,
        ax = knowledgeDiamondEventuallyAxiom (S := S) liveSymb ls φ hφ) }

end Axioms

section Results

variable [DecidableEq S.VarSymb]
variable {P : Type u₆} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {σ : Assignment S}
variable {φ : Formula S}
variable {l l₁ l₂ : Signature.Value S}
variable {evt : Signature.EventType S}
variable {ls₁ ls₂ : List (Signature.Value S)}

/-- Lemma 5.2.6: sometime knowledge lifts to the end of time. -/
lemma sometime_past_end
    {p : P} {H : History P (Signature.EventType S)}
    (_hSubset : H.val ⊆trn M.history.val)
    (hSat : ⟨H,p⟩ ⊨[M,σ]↕ᶠ(♢ᶠ[]↓ᶠ (Formula.ofEvent evt))) :
    ⟨M.history,p⟩ ⊨[M,σ] ♢ᶠ[]↓ᶠ (Formula.ofEvent evt) := by
  classical
  have hAtEnd :
      ⟨M.history,p⟩ ⊨[M,σ] ↓ᶠ (♢ᶠ[]↓ᶠ (Formula.ofEvent evt)) := by
    have h := hSat
    simp [Formula.sometime] at h
    exact
      (Sat.atEnd (M := M) (σ := σ) (H := H) (p := p)
        (φ := Formula.past
          (♢ᶠ[]↓ᶠ (Formula.ofEvent evt)))).1 h
  unfold Sat at hAtEnd
  rcases hAtEnd with ⟨H', hBefore, hDiamond⟩
  have hBefore' :
      H'.val ≺− M.history.val :=
    PreHistory.happensBefore_of_happensBeforeAt hBefore
  have hSubset' :
      H'.val ⊆trn M.history.val := by
    have hSub : H'.val ⊆ M.history.val :=
      History.predecessorHistory_subset
        (H := M.history) (h_before := hBefore')
    exact transitiveSubset_of_subset (P := P)
      (Event := Signature.EventType S) hSub
        (History.hereditarilyTransitive H')
  obtain ⟨q, hPastEvt⟩ :=
    (Sat.diamondEmpty (M := M) (σ := σ) (H := H') (p := p)
      (φ := ↓ᶠ (Formula.ofEvent evt))).1 hDiamond
  have hPastGlobal :
      ⟨M.history,q⟩ ⊨[M,σ] ↓ᶠ (Formula.ofEvent evt) :=
    ModalDistribution.Logic.sat_past_event_of_subset_to_history
      (M := M) (σ := σ) (H := H') (p := q)
      (evt := evt) hSubset' hPastEvt
  have hWitness :
      ∃ r, ⟨M.history,r⟩ ⊨[M ∣ᵥ M.history,σ]
          ↓ᶠ (Formula.ofEvent evt) := by
    refine ⟨q, ?_⟩
    simpa [ModalDistribution.Model.localView_full]
      using hPastGlobal
  exact
    sat_diamondEmpty_of_local (M := M) (σ := σ)
      (H := M.history) (p := p)
      (φ := ↓ᶠ (Formula.ofEvent evt)) hWitness

/-- Every model satisfying `ThyLive` admits a global past-activity guard. -/
lemma live_guard_past
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (σ : Assignment S)
    (hNonempty : ∃ t : EventTuple P (Signature.EventType S),
      t ∈ M.history.val) :
    ⊨[M,σ] □ᶠ[] ((liveFormula liveSymb) ⇒ᶠ ↓ᶠ ⊤ᶠ) := by
  classical
  have hActiveMem :
      liveActiveAxiom (S := S) liveSymb ∈ ThyLive liveSymb := by
    simp [ThyLive]
  have hActive :
      EventValid M σ ((liveActiveAxiom (S := S) liveSymb).formula) :=
    (hTheory hActiveMem) σ
  have hActiveEvent :
      EventValid M σ
        (⤒ᶠ (□ᶠ[] ((liveFormula liveSymb) ⇒ᶠ ↓ᶠ ⊤ᶠ))) := by
    intro t ht
    simpa [liveActiveAxiom] using hActive ht
  obtain ⟨p₀, hBox⟩ :=
    eventValid_atEnd_exists (M := M) (σ := σ)
      (φ := □ᶠ[] ((liveFormula liveSymb) ⇒ᶠ ↓ᶠ ⊤ᶠ))
      hActiveEvent hNonempty
  have hGuard : ∀ q : P,
      ⟨M.history,q⟩ ⊨[M,σ] ((liveFormula liveSymb) ⇒ᶠ ↓ᶠ ⊤ᶠ) :=
    (sat_boxEmpty_full_iff_local (M := M) (σ := σ)
      (p := p₀)
      (φ := (liveFormula liveSymb) ⇒ᶠ ↓ᶠ ⊤ᶠ)).1 hBox
  intro p
  exact
    (sat_boxEmpty_full_iff_local (M := M) (σ := σ)
      (p := p)
      (φ := (liveFormula liveSymb) ⇒ᶠ ↓ᶠ ⊤ᶠ)).2 hGuard

/-- `LiveAlways` transports end-of-time liveness to any witnessed prefix. -/
lemma live_at_predecessor
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (σ : Assignment S)
    {q : P} {e : MaybeEvent (Signature.EventType S)}
    {H : PreHistory P (Signature.EventType S)}
    (hMem : (q, e, H) ∈ M.history.val)
    (hLive : ⟨M.history,q⟩ ⊨[M,σ]liveFormula liveSymb) :
    ⟨History.predecessorHistory (H := M.history)
        (happensBefore_of_mem hMem), q⟩
      ⊨[M,σ] liveFormula liveSymb := by
  classical
  have hAlwaysMem :
      liveAlwaysAxiom (S := S) liveSymb ∈ ThyLive liveSymb := by
    simp [ThyLive]
  have hAlways :
      EventValid M σ
        ((liveAlwaysAxiom (S := S) liveSymb).formula) :=
    (hTheory hAlwaysMem) σ
  have hBefore :
      H ≺− M.history.val :=
    happensBefore_of_mem (P := P) (Event := Signature.EventType S) hMem
  set Hpre :=
      History.predecessorHistory (H := M.history) hBefore
    with hHpre
  dsimp [EventValid] at hAlways
  have hIff :
      ⟨Hpre,q⟩ ⊨[M,σ]
        (liveFormula liveSymb ⇔ᶠ
          ⤒ᶠ (liveFormula liveSymb)) := by
    have :=
      hAlways (t := (q, e, H)) (by simpa using hMem)
    simpa [Hpre, hHpre, History.predecessorHistory, hBefore]
      using this
  have hAtEnd :
      ⟨Hpre,q⟩ ⊨[M,σ]
        ⤒ᶠ (liveFormula liveSymb) :=
    (Sat.atEnd (M := M) (σ := σ) (H := Hpre) (p := q)
      (φ := liveFormula liveSymb)).2 hLive
  have hLivePre :
      ⟨Hpre,q⟩ ⊨[M,σ] liveFormula liveSymb :=
    Sat.iff_mpr (M := M) (σ := σ) (H := Hpre) (p := q)
      (φ := liveFormula liveSymb)
      (ψ := ⤒ᶠ (liveFormula liveSymb)) hIff hAtEnd
  simpa [Hpre, hHpre] using hLivePre

/-- Extract a predecessor event for a live participant using the guard axiom. -/
lemma live_guard_predecessor_data
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (σ : Assignment S)
    (hNonempty : ∃ t : EventTuple P (Signature.EventType S),
      t ∈ M.history.val)
    {q : P}
    (hLive : ⟨M.history,q⟩ ⊨[M,σ]liveFormula liveSymb) :
    ∃ (e : MaybeEvent (Signature.EventType S))
      (H : History P (Signature.EventType S)),
      (q, e, H.val) ∈ M.history.val ∧
      H.val ≺− M.history.val ∧
      ⟨H,q⟩ ⊨[M,σ] liveFormula liveSymb := by
  classical
  have hBox :=
    live_guard_past (M := M) (σ := σ)
      (hTheory := hTheory) hNonempty
  have hGuard_q :=
    (sat_boxEmpty_full_iff_local (M := M) (σ := σ)
      (p := q)
      (φ := (liveFormula liveSymb) ⇒ᶠ ↓ᶠ ⊤ᶠ)).1 (hBox q)
  have hPastTop :
      ⟨M.history,q⟩ ⊨[M,σ] ↓ᶠ ⊤ᶠ :=
    Sat.imp_elim (M := M) (σ := σ) (H := M.history) (p := q)
      (φ := liveFormula liveSymb)
      (ψ := ↓ᶠ ⊤ᶠ) (hGuard_q q) hLive
  unfold Sat at hPastTop
  obtain ⟨Hpast, hBefore, _⟩ := hPastTop
  rcases hBefore with ⟨evtq, hMem⟩
  have hStrict :
      Hpast.val ≺− M.history.val :=
    happensBefore_of_mem (P := P)
      (Event := Signature.EventType S) hMem
  let Hpre :=
    History.predecessorHistory (H := M.history) hStrict
  have hLivePre :=
    live_at_predecessor (M := M) (σ := σ)
      (hTheory := hTheory) (hMem := hMem)
      (hLive := hLive)
  refine ⟨evtq, Hpre, ?_, ?_, ?_⟩
  · simpa [Hpre] using hMem
  · simpa [Hpre] using hStrict
  · simpa [Hpre] using hLivePre

/-- Instantiate the knowledge axiom at a predecessor history. -/
lemma knowledgeDiamond_imp_at_predecessor
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (σ : Assignment S)
    {q : P} {evtq : MaybeEvent (Signature.EventType S)}
    {H : History P (Signature.EventType S)}
    {φ : Formula S}
    (hφ : φ.IsClosed)
    (hMem : (q, evtq, H.val) ∈ M.history.val) :
    ⟨H,q⟩ ⊨[M,σ]
      (⤒ᶠ (♢ᶠ↓[Term.ofValues []]
        ((liveFormula liveSymb) ∧ᶠ φ))) ⇒ᶠ
        ((liveFormula liveSymb) ⇒ᶠ
          ↕ᶠ (♢ᶠ↓[Term.ofValues []] φ)) := by
  classical
  have hArgs :
      Formula.listFreeVars (S := S)
        (Term.ofValues (S := S) (vals := ([] : List (Signature.Value S)))) = ∅ := by
    simp
  have hClosedEq : φ.freeVars = ∅ := by
    simpa [Formula.IsClosed] using hφ
  have hKnowMem :
      knowledgeDiamondAxiom (S := S) liveSymb [] φ hφ ∈ ThyLive liveSymb := by
    simp [ThyLive, Term.ofValues, hClosedEq]
  have hKnow :
      EventValid M σ
        ((knowledgeDiamondAxiom (S := S) liveSymb [] φ hφ).formula) :=
    (hTheory hKnowMem) σ
  have hKnowPre :=
    ModalDistribution.Logic.eventValid_predecessor (M := M) (σ := σ)
      (φ :=
        (knowledgeDiamondAxiom (S := S) liveSymb [] φ hφ).formula)
      hKnow (p := q) (e := evtq) (H := H.val) hMem
  have hHistory_eq :
      History.predecessorHistory (H := M.history)
          (happensBefore_of_mem (P := P)
            (Event := Signature.EventType S) hMem) = H := by
    apply History.ext
    simp [History.predecessorHistory]
  simpa [hHistory_eq, knowledgeDiamondAxiom_formula, Term.ofValues]
    using hKnowPre

/-- Knowledge axiom `Knowledge₍⋄₎` yields a local sometime guarantee for arbitrary past guards. -/
lemma knowledgeDiamond_sometime_at_predecessor_formula
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (σ : Assignment S)
    {q : P} {evtq : MaybeEvent (Signature.EventType S)}
    {H : History P (Signature.EventType S)}
    {φ : Formula S}
    (hφ : φ.IsClosed)
    (hMem : (q, evtq, H.val) ∈ M.history.val)
    (hLiveH : ⟨H,q⟩ ⊨[M,σ]liveFormula liveSymb)
    (hEvent : ⟨M.history,q⟩ ⊨[M,σ]♢ᶠ↓[Term.ofValues []]((liveFormula liveSymb)
      ∧ᶠ φ)) :
    ⟨H,q⟩ ⊨[M,σ]
      ↕ᶠ (♢ᶠ↓[Term.ofValues []] φ) := by
  classical
  have hAtEnd :
      ⟨H,q⟩ ⊨[M,σ]
        ⤒ᶠ (♢ᶠ↓[Term.ofValues []]
          ((liveFormula liveSymb) ∧ᶠ φ)) :=
    (Sat.atEnd (M := M) (σ := σ) (H := H) (p := q)
      (φ :=
        ♢ᶠ↓[Term.ofValues []]
          ((liveFormula liveSymb) ∧ᶠ φ))).2 hEvent
  have hImp :=
    knowledgeDiamond_imp_at_predecessor (M := M) (σ := σ)
      (φ := φ) (hTheory := hTheory) (hφ := hφ) (hMem := hMem)
  have hLiveImp :
      ⟨H,q⟩ ⊨[M,σ]
        (liveFormula liveSymb) ⇒ᶠ
          ↕ᶠ (♢ᶠ↓[Term.ofValues []] φ) :=
    Sat.imp_elim (M := M) (σ := σ) (H := H) (p := q)
      (φ :=
        ⤒ᶠ (♢ᶠ↓[Term.ofValues []]
          ((liveFormula liveSymb) ∧ᶠ φ)))
      (ψ :=
        (liveFormula liveSymb) ⇒ᶠ
          ↕ᶠ (♢ᶠ↓[Term.ofValues []] φ))
      hImp hAtEnd
  exact
    Sat.imp_elim (M := M) (σ := σ) (H := H) (p := q)
      (φ := liveFormula liveSymb)
      (ψ :=
        ↕ᶠ (♢ᶠ↓[Term.ofValues []] φ))
      hLiveImp hLiveH

/-- Specialisation of `knowledgeDiamond_sometime_at_predecessor_formula` to event formulas. -/
lemma knowledgeDiamond_sometime_at_predecessor
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (σ : Assignment S)
    {q : P} {evtq : MaybeEvent (Signature.EventType S)}
    {H : History P (Signature.EventType S)}
    (hMem : (q, evtq, H.val) ∈ M.history.val)
    (hLiveH : ⟨H,q⟩ ⊨[M,σ]liveFormula liveSymb)
    (hEvent : ⟨M.history,q⟩ ⊨[M,σ]♢ᶠ↓[Term.ofValues []]((liveFormula liveSymb)
      ∧ᶠ Formula.ofEvent evt)) :
    ⟨H,q⟩ ⊨[M,σ]
      ↕ᶠ (♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)) := by
  classical
  have hClosed : (Formula.ofEvent evt).IsClosed :=
    Formula.IsClosed.ofEvent (S := S) evt
  exact
    knowledgeDiamond_sometime_at_predecessor_formula (M := M) (σ := σ)
      (hTheory := hTheory) (hφ := hClosed) (hMem := hMem)
      (hLiveH := hLiveH) (hEvent := hEvent)

/-- Any satisfied past-guarded empty diamond witnesses a global history event. -/
lemma exists_history_of_diamondEmpty_past
    {q : P} {φ : Formula S}
    (hDiamond : ⟨M.history,q⟩ ⊨[M,σ]♢ᶠ[]↓ᶠ φ) :
    ∃ t : EventTuple P (Signature.EventType S),
      t ∈ M.history.val := by
  classical
  obtain ⟨r, hPast⟩ :=
    (Sat.diamondEmpty (M := M) (σ := σ)
        (H := M.history) (p := q) (φ := ↓ᶠ φ)).1 hDiamond
  unfold Sat at hPast
  rcases hPast with ⟨H', hBefore, _⟩
  rcases hBefore with ⟨evt, hMem⟩
  refine ⟨(r, evt, H'.val), ?_⟩
  simpa using hMem

/-- Specialisation of the knowledge axiom: live participants eventually know past events. -/
lemma live_knows_eventually
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (σ : Assignment S)
    {q : P}
    (hLive : ⟨M.history,q⟩ ⊨[M,σ]liveFormula liveSymb)
    (hEvent : ⊨[M,σ]♢ᶠ↓[Term.ofValues []]((liveFormula liveSymb) ∧ᶠ Formula.ofEvent evt)) :
    ⟨M.history,q⟩ ⊨[M,σ] ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt) := by
  classical
  have hEvent_q :
      ⟨M.history,q⟩ ⊨[M,σ]
        ♢ᶠ↓[Term.ofValues []]
          ((liveFormula liveSymb) ∧ᶠ Formula.ofEvent evt) :=
    hEvent q
  have hDiamondWitness :
      ⟨M.history,q⟩ ⊨[M,σ]
        ♢ᶠ[] ↓ᶠ ((liveFormula liveSymb) ∧ᶠ Formula.ofEvent evt) := by
    simpa [Formula.diamondPast, Formula.diamondEmpty, Term.ofValues]
      using hEvent_q
  have hNonempty :
      ∃ t : EventTuple P (Signature.EventType S),
        t ∈ M.history.val :=
    exists_history_of_diamondEmpty_past (M := M) (σ := σ)
      (q := q) (φ := (liveFormula liveSymb) ∧ᶠ Formula.ofEvent evt)
      hDiamondWitness
  obtain ⟨evtq, Hpre, hMem, hBeforeStrict, hLivePre⟩ :=
    live_guard_predecessor_data (M := M) (σ := σ)
      (hTheory := hTheory) hNonempty (q := q) hLive
  have hSometime :=
    knowledgeDiamond_sometime_at_predecessor (M := M) (σ := σ)
      (hTheory := hTheory) (hMem := hMem)
      (hLiveH := hLivePre) (hEvent := hEvent_q)
  have hSometime' :
      ⟨Hpre,q⟩ ⊨[M,σ]
        ↕ᶠ (♢ᶠ[]↓ᶠ (Formula.ofEvent evt)) := by
    simpa [Formula.diamondPast, Formula.diamondEmpty, Term.ofValues]
      using hSometime
  have hSubset : Hpre.val ⊆trn M.history.val := by
    have hSub : Hpre.val ⊆ M.history.val :=
      History.predecessorHistory_subset (H := M.history)
        (h_before := hBeforeStrict)
    exact transitiveSubset_of_subset (P := P)
      (Event := Signature.EventType S) hSub
      (History.hereditarilyTransitive Hpre)
  have hDiamondPast :
      ⟨M.history,q⟩ ⊨[M,σ]
        ♢ᶠ[]↓ᶠ (Formula.ofEvent evt) :=
    sometime_past_end (M := M) (σ := σ)
      (H := Hpre) (p := q) hSubset hSometime'
  simpa [Formula.diamondPast, Formula.diamondEmpty, Term.ofValues]
    using hDiamondPast

/-- A live participant eventually reaches a past state where the event is known. -/
lemma live_knows_eventually_past
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (σ : Assignment S)
    {q : P}
    (hLive : ⟨M.history,q⟩ ⊨[M,σ]liveFormula liveSymb)
    (hEvent : ⟨M.history,q⟩ ⊨[M,σ]♢ᶠ↓[Term.ofValues []]((liveFormula liveSymb)
      ∧ᶠ Formula.ofEvent evt)) :
    ⟨M.history,q⟩ ⊨[M,σ]
      ↓ᶠ ((liveFormula liveSymb) ∧ᶠ
        ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)) := by
  classical
  have hEvent_q := hEvent
  have hDiamondWitness :
      ⟨M.history,q⟩ ⊨[M,σ]
        ♢ᶠ[] ↓ᶠ ((liveFormula liveSymb) ∧ᶠ Formula.ofEvent evt) := by
    simpa [Formula.diamondPast, Formula.diamondEmpty, Term.ofValues]
      using hEvent_q
  have hNonempty :
      ∃ t : EventTuple P (Signature.EventType S),
        t ∈ M.history.val :=
    exists_history_of_diamondEmpty_past (M := M) (σ := σ)
      (q := q) (φ := (liveFormula liveSymb) ∧ᶠ Formula.ofEvent evt)
      hDiamondWitness
  obtain ⟨evtq, Hpre, hMem, hBeforeStrict, hLivePre⟩ :=
    live_guard_predecessor_data (M := M) (σ := σ)
      (hTheory := hTheory) hNonempty (q := q) hLive
  have hSometime :=
    knowledgeDiamond_sometime_at_predecessor (M := M) (σ := σ)
      (hTheory := hTheory) (hMem := hMem)
      (hLiveH := hLivePre) (hEvent := hEvent_q)
  have hPastDiamond :
      ⟨M.history,q⟩ ⊨[M,σ]
        ↓ᶠ (♢ᶠ[]↓ᶠ (Formula.ofEvent evt)) := by
    have hAtEnd :
        ⟨Hpre,q⟩ ⊨[M,σ]
          ⤒ᶠ (↓ᶠ (♢ᶠ[]↓ᶠ (Formula.ofEvent evt))) := by
      simpa [Formula.sometime] using hSometime
    exact
      (Sat.atEnd (M := M) (σ := σ) (H := Hpre) (p := q)
        (φ := ↓ᶠ (♢ᶠ[]↓ᶠ (Formula.ofEvent evt)))).1 hAtEnd
  unfold Sat at hPastDiamond
  rcases hPastDiamond with ⟨Hpast, hBeforePast, hDiamondPast⟩
  rcases hBeforePast with ⟨evtPast, hMemPast⟩
  have hLivePast :
      ⟨Hpast,q⟩ ⊨[M,σ] liveFormula liveSymb := by
    have hHistory_eq :
        History.predecessorHistory (H := M.history)
            (happensBefore_of_mem (P := P)
              (Event := Signature.EventType S) hMemPast) = Hpast := by
      apply History.ext
      simp [History.predecessorHistory]
    have hLivePredecessor :=
      live_at_predecessor (M := M) (σ := σ)
        (hTheory := hTheory) (hMem := hMemPast)
        (hLive := hLive)
    simpa [hHistory_eq] using hLivePredecessor
  have hDiamondPast' :
      ⟨Hpast,q⟩ ⊨[M,σ]
        ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt) := by
    simpa [Formula.diamondPast, Formula.diamondEmpty, Term.ofValues]
      using hDiamondPast
  have hConjPast :
      ⟨Hpast,q⟩ ⊨[M,σ]
        (liveFormula liveSymb) ∧ᶠ
          ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt) :=
    Sat.and_intro (M := M) (σ := σ)
      (H := Hpast) (p := q)
      (φ := liveFormula liveSymb)
      (ψ := ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt))
      hLivePast hDiamondPast'
  exact
    Sat.past_intro_of_prefix (M := M) (σ := σ)
      (H := M.history) (H' := Hpast) (p := q)
      ⟨evtPast, hMemPast⟩ hConjPast

lemma live_knows_eventually_event_past
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (σ : Assignment S)
    {q : P}
    (hLive : ⟨M.history,q⟩ ⊨[M,σ]liveFormula liveSymb)
    (hEvent : ⊨[M,σ]♢ᶠ↓[Term.ofValues []]((liveFormula liveSymb) ∧ᶠ
        ♢ᶠ↓[Term.ofValues []](Formula.ofEvent evt))) :
    ⟨M.history,q⟩ ⊨[M,σ]
      ↓ᶠ ((liveFormula liveSymb) ∧ᶠ
        ♢ᶠ↓[Term.ofValues []]
          (♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt))) := by
  classical
  set φ := ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt) with hφ
  have hEvent_q :
      ⟨M.history,q⟩ ⊨[M,σ]
        ♢ᶠ↓[Term.ofValues []]
          ((liveFormula liveSymb) ∧ᶠ φ) := by
    simpa [hφ] using hEvent q
  have hDiamondWitness :
      ⟨M.history,q⟩ ⊨[M,σ]
        ♢ᶠ[] ↓ᶠ ((liveFormula liveSymb) ∧ᶠ φ) := by
    simpa [Formula.diamondPast, Formula.diamondEmpty, Term.ofValues]
      using hEvent_q
  have hNonempty :
      ∃ t : EventTuple P (Signature.EventType S),
        t ∈ M.history.val :=
    exists_history_of_diamondEmpty_past (M := M) (σ := σ)
      (q := q) (φ := (liveFormula liveSymb) ∧ᶠ φ)
      hDiamondWitness
  obtain ⟨evtq, Hpre, hMem, hBeforeStrict, hLivePre⟩ :=
    live_guard_predecessor_data (M := M) (σ := σ)
      (hTheory := hTheory) hNonempty (q := q) hLive
  have hArgs :
      Formula.listFreeVars (S := S)
        (Term.ofValues (S := S) (vals := ([] : List (Signature.Value S)))) = ∅ := by
    simp [Term.ofValues]
  have hClosedEvent : (Formula.ofEvent evt).IsClosed :=
    Formula.IsClosed.ofEvent (S := S) evt
  have hClosedPast :
      (↓ᶠ (Formula.ofEvent evt)).IsClosed :=
    Formula.IsClosed.past (S := S) hClosedEvent
  have hClosedφ : φ.IsClosed := by
    simpa [hφ, Formula.diamondPast]
      using
        (Formula.IsClosed.diamond (S := S)
          (ls := Term.ofValues [])
          (φ := ↓ᶠ (Formula.ofEvent evt))
          hArgs hClosedPast)
  have hSometime :=
    knowledgeDiamond_sometime_at_predecessor_formula (M := M) (σ := σ)
      (hTheory := hTheory) (hφ := hClosedφ) (hMem := hMem)
      (hLiveH := hLivePre) (hEvent := by
        simpa [hφ] using hEvent_q)
  have hAtEnd :
      ⟨M.history,q⟩ ⊨[M,σ]
        ↓ᶠ (♢ᶠ↓[Term.ofValues []] φ) := by
    have h := hSometime
    simp [Formula.sometime] at h
    exact
      (Sat.atEnd (M := M) (σ := σ) (H := Hpre) (p := q)
        (φ := ↓ᶠ (♢ᶠ↓[Term.ofValues []] φ))).1 h
  unfold Sat at hAtEnd
  rcases hAtEnd with ⟨Hpast, hBeforePast, hDiamondPast⟩
  rcases hBeforePast with ⟨evtPast, hMemPast⟩
  have hHistory_eq :
      History.predecessorHistory (H := M.history)
          (happensBefore_of_mem (P := P)
            (Event := Signature.EventType S) hMemPast) = Hpast := by
    apply History.ext
    simp [History.predecessorHistory]
  have hLivePast :
      ⟨Hpast,q⟩ ⊨[M,σ] liveFormula liveSymb := by
    have hLivePredecessor :=
      live_at_predecessor (M := M) (σ := σ)
        (hTheory := hTheory) (hMem := hMemPast)
        (hLive := hLive)
    simpa [hHistory_eq]
      using hLivePredecessor
  have hDiamondPast' :
      ⟨Hpast,q⟩ ⊨[M,σ]
        ♢ᶠ↓[Term.ofValues []] φ := by
    simpa [Formula.diamondPast, Formula.diamondEmpty, Term.ofValues]
      using hDiamondPast
  have hConjPast :
      ⟨Hpast,q⟩ ⊨[M,σ]
        (liveFormula liveSymb) ∧ᶠ
          ♢ᶠ↓[Term.ofValues []] φ :=
    Sat.and_intro (M := M) (σ := σ)
      (H := Hpast) (p := q)
      (φ := liveFormula liveSymb)
      (ψ := ♢ᶠ↓[Term.ofValues []] φ)
      hLivePast hDiamondPast'
  exact
    Sat.past_intro_of_prefix (M := M) (σ := σ)
      (H := M.history) (H' := Hpast) (p := q)
      ⟨evtPast, hMemPast⟩
      (by simpa [hφ]
        using hConjPast)

/-- Empty-learner past diamonds compose idempotently for event formulas. -/
lemma diamondEmpty_past_event_flat
    {H : History P (Signature.EventType S)}
    {p : P}
    (hDiamond : ⟨H,p⟩ ⊨[M,σ]♢ᶠ[]↓ᶠ (♢ᶠ[]↓ᶠ (Formula.ofEvent evt))) :
    ⟨H,p⟩ ⊨[M,σ] ♢ᶠ[]↓ᶠ (Formula.ofEvent evt) := by
  classical
  obtain ⟨q, H₁, hBefore₁, hSubset₁, hLocal₁⟩ :=
    (sat_diamondPast_nil_iff (M := M) (σ := σ)
      (H := H) (p := p)
      (φ := ♢ᶠ[]↓ᶠ (Formula.ofEvent evt))).1 hDiamond
  obtain ⟨r, H₂, hBefore₂, hSubset₂, hLocal₂⟩ :=
    (sat_diamondPast_nil_iff (M := M ∣ᵥ H) (σ := σ)
      (H := H₁) (p := q)
      (φ := Formula.ofEvent evt)).1 hLocal₁
  have hSubset₁' : H₁.val ⊆ H.val :=
    (transitiveSubset_subset (P := P)
      (Event := Signature.EventType S) hSubset₁)
  have hSubset₂' : H₂.val ⊆ H₁.val :=
    (transitiveSubset_subset (P := P)
      (Event := Signature.EventType S) hSubset₂)
  have hBefore_total :
      PreHistory.happensBeforeAt (P := P)
        (Event := Signature.EventType S) r H₂.val H.val :=
    PreHistory.happensBeforeAt_mono (P := P)
      (Event := Signature.EventType S) hBefore₂ hSubset₁'
  have hSubset_total_sub : H₂.val ⊆ H.val := by
    intro t ht
    exact hSubset₁' _ (hSubset₂' _ ht)
  have hSubset_total : H₂.val ⊆trn H.val :=
    transitiveSubset_of_subset (P := P)
      (Event := Signature.EventType S)
      hSubset_total_sub (History.hereditarilyTransitive H₂)
  have hEvent_local :
      ⟨H₂,r⟩ ⊨[M ∣ᵥ H₁,σ] Formula.ofEvent evt := by
    simpa [ModalDistribution.Model.localView_comp]
      using hLocal₂
  have hEvent_global :
      ⟨H₂,r⟩ ⊨[M ∣ᵥ H,σ] Formula.ofEvent evt :=
    Sat.ofEvent_of_subset (M := M) (σ := σ)
      (H := H) (H₁ := H₁) (H₂ := H₂)
      (p := r) (evt := evt) hSubset₁' hEvent_local
  refine
    (sat_diamondPast_nil_iff (M := M) (σ := σ)
      (H := H) (p := p)
      (φ := Formula.ofEvent evt)).2 ?_
  exact ⟨r, H₂, hBefore_total, hSubset_total, hEvent_global⟩

/-- A live participant eventually reaches a past state guaranteeing quorum knowledge. -/
lemma live_knows_eventually_quorum_past
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (σ : Assignment S)
    {q : P}
    (hLive : ⟨M.history,q⟩ ⊨[M,σ]liveFormula liveSymb)
    (hQuorum : ⊨[M,σ]♢ᶠ↓[Term.ofValues []]((liveFormula liveSymb) ∧ᶠ
        □ᶠ↓[Term.ofValues [l₁]](Formula.ofEvent evt))) :
    ⟨M.history,q⟩ ⊨[M,σ]
      ↓ᶠ ((liveFormula liveSymb) ∧ᶠ
        □ᶠ↓[Term.ofValues [l₁]] (Formula.ofEvent evt)) := by
  classical
  set φBox :=
    □ᶠ↓[Term.ofValues [l₁]] (Formula.ofEvent evt) with hφBox
  have hQuorum_q :
      ⟨M.history,q⟩ ⊨[M,σ]
        ♢ᶠ↓[Term.ofValues []]
          ((liveFormula liveSymb) ∧ᶠ φBox) := by
    simpa [hφBox] using hQuorum q
  have hDiamondWitness :
      ⟨M.history,q⟩ ⊨[M,σ]
        ♢ᶠ[] ↓ᶠ ((liveFormula liveSymb) ∧ᶠ φBox) := by
    simpa [Formula.diamondPast, Formula.diamondEmpty, Term.ofValues]
      using hQuorum_q
  have hNonempty :
      ∃ t : EventTuple P (Signature.EventType S),
        t ∈ M.history.val :=
    exists_history_of_diamondEmpty_past (M := M) (σ := σ)
      (q := q) (φ := (liveFormula liveSymb) ∧ᶠ φBox)
      hDiamondWitness
  obtain ⟨evtq, Hpre, hMem, hBeforeStrict, hLivePre⟩ :=
    live_guard_predecessor_data (M := M) (σ := σ)
      (hTheory := hTheory) hNonempty (q := q) hLive
  have hArgs :
      Formula.listFreeVars (S := S)
        (Term.ofValues (S := S) (vals := [l₁])) = ∅ := by
    simp [Term.ofValues]
  have hClosedEvent : (Formula.ofEvent evt).IsClosed :=
    Formula.IsClosed.ofEvent (S := S) evt
  have hClosedPast :
      (↓ᶠ (Formula.ofEvent evt)).IsClosed :=
    Formula.IsClosed.past (S := S) hClosedEvent
  have hClosedBox : φBox.IsClosed := by
    simpa [hφBox]
      using
        (Formula.IsClosed.box (S := S)
          (ls := Term.ofValues [l₁])
          (φ := ↓ᶠ (Formula.ofEvent evt))
          hArgs hClosedPast)
  have hSometime :=
    knowledgeDiamond_sometime_at_predecessor_formula (M := M) (σ := σ)
      (hTheory := hTheory) (hφ := hClosedBox)
      (hMem := hMem) (hLiveH := hLivePre) (hEvent := hQuorum_q)
  have hPastDiamond :
      ⟨M.history,q⟩ ⊨[M,σ]
        ↓ᶠ (♢ᶠ[]↓ᶠ φBox) := by
    have hAtEnd :
        ⟨Hpre,q⟩ ⊨[M,σ]
          ⤒ᶠ (↓ᶠ (♢ᶠ[]↓ᶠ φBox)) := by
      simpa [Formula.sometime] using hSometime
    exact
      (Sat.atEnd (M := M) (σ := σ) (H := Hpre) (p := q)
        (φ := ↓ᶠ (♢ᶠ[]↓ᶠ φBox))).1 hAtEnd
  unfold Sat at hPastDiamond
  rcases hPastDiamond with ⟨Hpast, hBeforePast, hDiamondPast⟩
  rcases hBeforePast with ⟨evtPast, hMemPast⟩
  have hLivePast :
      ⟨Hpast,q⟩ ⊨[M,σ] liveFormula liveSymb := by
    have hHistory_eq :
        History.predecessorHistory (H := M.history)
            (happensBefore_of_mem (P := P)
              (Event := Signature.EventType S) hMemPast) = Hpast := by
      apply History.ext
      simp [History.predecessorHistory]
    have hLivePredecessor :=
      live_at_predecessor (M := M) (σ := σ)
        (hTheory := hTheory) (hMem := hMemPast)
        (hLive := hLive)
    simpa [hHistory_eq] using hLivePredecessor
  have hDiamondPast' :
      ⟨Hpast,q⟩ ⊨[M,σ]
        ♢ᶠ↓[Term.ofValues []] φBox := by
    simpa [Formula.diamondPast, Formula.diamondEmpty, Term.ofValues]
      using hDiamondPast
  have hBoxPast :
      ⟨Hpast,q⟩ ⊨[M,σ] φBox := by
    have :=
      lemma_4_2_4_part2 (M := M) (σ := σ)
        (H := Hpast) (p := q) (l := l₁) (evt := evt)
        (by
          simpa [Formula.diamondPast, Formula.diamondEmpty,
            Term.ofValues, hφBox]
            using hDiamondPast')
    simpa [hφBox] using this
  have hConjPast :
      ⟨Hpast,q⟩ ⊨[M,σ]
        (liveFormula liveSymb) ∧ᶠ φBox :=
    Sat.and_intro (M := M) (σ := σ)
      (H := Hpast) (p := q)
      (φ := liveFormula liveSymb)
      (ψ := φBox)
      hLivePast hBoxPast
  exact
    Sat.past_intro_of_prefix (M := M) (σ := σ)
      (H := M.history) (H' := Hpast) (p := q)
      ⟨evtPast, hMemPast⟩
      (by simpa [hφBox]
        using hConjPast)
/-- Proposition 5.2.7: live quorums eventually know past facts. -/
theorem live_eventually_knows
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hLive : ⊨[M,σ]□ᶠ[Term.ofValues [l]](liveFormula liveSymb))
    (hEvent : ⊨[M,σ]♢ᶠ↓[Term.ofValues []]((liveFormula liveSymb) ∧ᶠ Formula.ofEvent evt)) :
    ⊨[M,σ]□ᶠ↓[Term.ofValues [l]]
      ((liveFormula liveSymb) ∧ᶠ
        ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)) := by
  classical
  intro q
  have hBoxLive :
      ⟨M.history,q⟩ ⊨[M,σ]
        □ᶠ[Term.ofValues [l]] (liveFormula liveSymb) :=
    hLive q
  have hImp :
      ∀ q',
        (⟨M.history,q'⟩ ⊨[M ∣ᵥ M.history,σ]
          liveFormula liveSymb) →
          ⟨M.history,q'⟩ ⊨[M ∣ᵥ M.history,σ]
            ↓ᶠ ((liveFormula liveSymb) ∧ᶠ
              ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)) := by
    intro q' hLiveLocal
    have hLiveGlobal :
        ⟨M.history,q'⟩ ⊨[M,σ]
          liveFormula liveSymb := by
      simpa [ModalDistribution.Model.localView_full]
        using hLiveLocal
    have hPast :=
      live_knows_eventually_past (M := M) (σ := σ)
        (hTheory := hTheory) (q := q')
        (hLive := hLiveGlobal) (hEvent := hEvent q')
    simpa [ModalDistribution.Model.localView_full]
      using hPast
  have hBoxPast :=
    ModalDistribution.Logic.Sat.box_of_imp (M := M) (σ := σ)
      (H := M.history) (p := q)
      (ts := Term.ofValues [l])
      (φ := liveFormula liveSymb)
      (ψ :=
        ↓ᶠ ((liveFormula liveSymb) ∧ᶠ
          ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)))
      (h := hImp) hBoxLive
  simpa [Formula.boxPast]
    using hBoxPast

/-- Corollary 5.2.8(1): live quorums eventually know of past events. -/
theorem live_eventually_knows_event
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hLive : ⊨[M,σ]□ᶠ[Term.ofValues [l]](liveFormula liveSymb))
    (hEvent : ⊨[M,σ]♢ᶠ↓[Term.ofValues []]((liveFormula liveSymb)
        ∧ᶠ ♢ᶠ↓[Term.ofValues []](Formula.ofEvent evt))) :
    ⊨[M,σ] □ᶠ↓[Term.ofValues [l]]
      ((liveFormula liveSymb) ∧ᶠ
        ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)) := by
  classical
  intro q
  have hLiveBox :
      ⟨M.history,q⟩ ⊨[M,σ]
        □ᶠ[Term.ofValues [l]] (liveFormula liveSymb) :=
    hLive q
  have hImp :
      ∀ q',
        (⟨M.history,q'⟩ ⊨[M ∣ᵥ M.history,σ]
          liveFormula liveSymb) →
          ⟨M.history,q'⟩ ⊨[M ∣ᵥ M.history,σ]
            ↓ᶠ ((liveFormula liveSymb) ∧ᶠ
              ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)) := by
    intro q' hLiveLocal
    have hLiveGlobal :
        ⟨M.history,q'⟩ ⊨[M,σ]
          liveFormula liveSymb := by
      simpa [ModalDistribution.Model.localView_full]
        using hLiveLocal
    have hPast :=
      live_knows_eventually_event_past (M := M) (σ := σ)
        (hTheory := hTheory) (q := q')
        (hLive := hLiveGlobal) (hEvent := hEvent)
    have hPast' :
        ⟨M.history,q'⟩ ⊨[M,σ]
          ↓ᶠ ((liveFormula liveSymb) ∧ᶠ
            ♢ᶠ↓[Term.ofValues []]
              (♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt))) :=
      hPast
    have hPastFlatten :
        ⟨M.history,q'⟩ ⊨[M,σ]
          ↓ᶠ ((liveFormula liveSymb) ∧ᶠ
            ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)) :=
      Sat.past_of_imp (M := M) (σ := σ)
        (H := M.history) (p := q')
        (φ :=
          (liveFormula liveSymb) ∧ᶠ
            ♢ᶠ↓[Term.ofValues []]
              (♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)))
        (ψ :=
          (liveFormula liveSymb) ∧ᶠ
            ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt))
        (fun H' hConj => by
          have hLiveH' :
              ⟨H',q'⟩ ⊨[M,σ] liveFormula liveSymb :=
            Sat.and_left (M := M) (σ := σ)
              (H := H') (p := q') (φ := liveFormula liveSymb)
              (ψ :=
                ♢ᶠ↓[Term.ofValues []]
                  (♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)))
              hConj
          have hDiamondNested :
              ⟨H',q'⟩ ⊨[M,σ]
                ♢ᶠ↓[Term.ofValues []]
                  (♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)) :=
            Sat.and_right (M := M) (σ := σ)
              (H := H') (p := q') (φ := liveFormula liveSymb)
              (ψ :=
                ♢ᶠ↓[Term.ofValues []]
                  (♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)))
              hConj
          have hDiamondFlat :
              ⟨H',q'⟩ ⊨[M,σ]
                ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt) :=
            by
              have :=
                diamondEmpty_past_event_flat (M := M) (σ := σ)
                  (H := H') (p := q')
                  (evt := evt) hDiamondNested
              simpa [Formula.diamondPast, Formula.diamondEmpty,
                Term.ofValues]
                using this
          exact
            Sat.and_intro (M := M) (σ := σ)
              (H := H') (p := q')
              (φ := liveFormula liveSymb)
              (ψ := ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt))
              hLiveH' hDiamondFlat)
        hPast'
    simpa [ModalDistribution.Model.localView_full]
      using hPastFlatten
  have hBoxPast :=
    ModalDistribution.Logic.Sat.box_of_imp (M := M) (σ := σ)
      (H := M.history) (p := q)
      (ts := Term.ofValues [l])
      (φ := liveFormula liveSymb)
      (ψ :=
        ↓ᶠ ((liveFormula liveSymb) ∧ᶠ
          ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)))
      (h := hImp) hLiveBox
  simpa [Formula.boxPast]
    using hBoxPast

/-- Corollary 5.2.8(2): live quorums eventually learn of performed events. -/
theorem live_eventually_knows_performed
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hLive : ⊨[M,σ]□ᶠ[Term.ofValues [l]](liveFormula liveSymb))
    (hEvent : ⊨[M,σ]♢ᶠ↓[Term.ofValues []]((liveFormula liveSymb) ∧ᶠ Formula.ofEvent evt)) :
    ⊨[M,σ] □ᶠ↓[Term.ofValues [l]]
      ((liveFormula liveSymb) ∧ᶠ
        ♢ᶠ↓[Term.ofValues []] (Formula.ofEvent evt)) := by
  exact
    live_eventually_knows (M := M) (σ := σ)
      (hTheory := hTheory) (hLive := hLive) (hEvent := hEvent)

/-- Corollary 5.2.8(3): live quorums eventually know quorum facts. -/
theorem live_eventually_knows_quorum
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hLive : ⊨[M,σ]□ᶠ[Term.ofValues [l]](liveFormula liveSymb))
    (hQuorum : ⊨[M,σ]♢ᶠ↓[Term.ofValues []]((liveFormula liveSymb) ∧ᶠ
        □ᶠ↓[Term.ofValues [l₁]](Formula.ofEvent evt))) :
    ⊨[M,σ] □ᶠ↓[Term.ofValues [l]]
      ((liveFormula liveSymb) ∧ᶠ
        □ᶠ↓[Term.ofValues [l₁]] (Formula.ofEvent evt)) := by
  classical
  intro q
  have hBoxLive :
      ⟨M.history,q⟩ ⊨[M,σ]
        □ᶠ[Term.ofValues [l]] (liveFormula liveSymb) :=
    hLive q
  have hImp :
      ∀ q',
        (⟨M.history,q'⟩ ⊨[M ∣ᵥ M.history,σ]
          liveFormula liveSymb) →
          ⟨M.history,q'⟩ ⊨[M ∣ᵥ M.history,σ]
            ↓ᶠ ((liveFormula liveSymb) ∧ᶠ
              □ᶠ↓[Term.ofValues [l₁]] (Formula.ofEvent evt)) := by
    intro q' hLiveLocal
    have hLiveGlobal :
        ⟨M.history,q'⟩ ⊨[M,σ]
          liveFormula liveSymb := by
      simpa [ModalDistribution.Model.localView_full]
        using hLiveLocal
    have hPast :=
      live_knows_eventually_quorum_past (M := M) (σ := σ)
        (hTheory := hTheory) (q := q')
        (hLive := hLiveGlobal) (hQuorum := hQuorum)
    simpa [ModalDistribution.Model.localView_full]
      using hPast
  have hBoxPast :=
    ModalDistribution.Logic.Sat.box_of_imp (M := M) (σ := σ)
      (H := M.history) (p := q)
      (ts := Term.ofValues [l])
      (φ := liveFormula liveSymb)
      (ψ :=
        ↓ᶠ ((liveFormula liveSymb) ∧ᶠ
          □ᶠ↓[Term.ofValues [l₁]] (Formula.ofEvent evt)))
      (h := hImp) hBoxLive
  simpa [Formula.boxPast]
    using hBoxPast

/-- Lemma 5.2.9(1): liveness does not depend on time. -/
lemma live_always_equiv_part1
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {p : P} {e : MaybeEvent (Signature.EventType S)}
    {H : History P (Signature.EventType S)}
    (hMem : (p, e, H.val) ∈ M.history.val) :
    (⟨H,p⟩ ⊨[M,σ] liveFormula liveSymb) ↔
      (⟨M.history,p⟩ ⊨[M,σ] liveFormula liveSymb) := by
  classical
  have hAlwaysMem :
      liveAlwaysAxiom (S := S) liveSymb ∈ ThyLive liveSymb := by
    simp [ThyLive]
  have hAlways :
      EventValid M σ
        ((liveAlwaysAxiom (S := S) liveSymb).formula) :=
    (hTheory hAlwaysMem) σ
  have hIff :
      ⟨H,p⟩ ⊨[M,σ]
        (liveFormula liveSymb ⇔ᶠ ⤒ᶠ (liveFormula liveSymb)) :=
    hAlways (t := (p, e, H.val)) (by simpa using hMem)
  have hImp_forward :=
    Sat.iff_mp (M := M) (σ := σ) (H := H) (p := p)
      (φ := liveFormula liveSymb)
      (ψ := ⤒ᶠ (liveFormula liveSymb)) hIff
  constructor
  · intro hLiveH
    have hAtEnd := hImp_forward hLiveH
    exact
      (Sat.atEnd (M := M) (σ := σ) (H := H) (p := p)
        (φ := liveFormula liveSymb)).1 hAtEnd
  · intro hLiveEnd
    -- backward direction via `live_at_predecessor`
    exact
      live_at_predecessor (M := M) (σ := σ)
        (hTheory := hTheory) (hMem := hMem)
        (hLive := hLiveEnd)

/-- Lemma 5.2.9(2): liveness does not depend on time. -/
lemma live_always_equiv_part2
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {p : P} {e e' : MaybeEvent (Signature.EventType S)}
    {H H' : History P (Signature.EventType S)}
    (hMem : (p, e, H.val) ∈ M.history.val)
    (hMem' : (p, e', H'.val) ∈ M.history.val) :
    (⟨H,p⟩ ⊨[M,σ] liveFormula liveSymb) ↔
      (⟨H',p⟩ ⊨[M,σ] liveFormula liveSymb) := by
  classical
  have hH :=
    live_always_equiv_part1 (M := M) (σ := σ)
      (hTheory := hTheory) (hMem := hMem)
  have hH' :=
    live_always_equiv_part1 (M := M) (σ := σ)
      (hTheory := hTheory) (hMem := hMem')
  exact hH.trans hH'.symm

/-- Proposition 5.2.10: live quorum intersections expose live witnesses. -/
theorem intertwined_two_quorums
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (hIntersect : ⊨[M,σ]♢ᶠ[Term.ofValues [l, l₁]]⊤ᶠ)
    (hLiveQuorum : ⊨[M,σ]□ᶠ[Term.ofValues [l₁]](liveFormula liveSymb))
    (hWitness : ⊨[M,σ]□ᶠ↓[Term.ofValues [l]]φ) :
    ⊨[M,σ] ♢ᶠ↓[Term.ofValues []]
      ((liveFormula liveSymb) ∧ᶠ φ) := by
  classical
  -- Extract nonempty intersections for learners `[l, l₁]`.
  have hIntersect_nonempty :=
    (lemma_4_1_1_nonempty (M := M) (σ := σ)
      (ls := [l, l₁])).1 hIntersect
  -- Choose quorums realising the guard for `[l]` and `[l₁]`.
  let p₀ : P := Classical.choice (show Nonempty P from inferInstance)
  obtain ⟨Oφ, hOφ, hAllφ⟩ :=
    (sat_box_singleton_exists (M := M) (σ := σ)
      (H := M.history) (p := p₀)
      (l := l) (φ := ↓ᶠ φ)).1
      (hWitness p₀)
  obtain ⟨Oliv, hOliv, hAllLive⟩ :=
    (sat_box_singleton_exists (M := M) (σ := σ)
      (H := M.history) (p := p₀)
      (l := l₁) (φ := liveFormula liveSymb)).1
      (hLiveQuorum p₀)
  -- Build a quorum family whose intersection is guaranteed nonempty.
  let F_tail : QuorumFamily M [l₁] :=
    QuorumFamily.cons (M := M) (l := l₁) Oliv hOliv
      (QuorumFamily.nil M)
  let F : QuorumFamily M [l, l₁] :=
    QuorumFamily.cons (M := M) (l := l) Oφ hOφ F_tail
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
      ⟨M.history,p⟩ ⊨[M,σ] liveFormula liveSymb := by
    have := hAllLive p hpOliv
    simpa [ModalDistribution.Model.localView_full] using this
  -- `p` sees a past state satisfying `φ` thanks to the `[l]` guard.
  have hPastφ :
      ⟨M.history,p⟩ ⊨[M,σ] ↓ᶠ φ := by
    have := hAllφ p hpOφ
    simpa [ModalDistribution.Model.localView_full] using this
  -- Unfold the past witness and extract the predecessor event.
  unfold Sat at hPastφ
  rcases hPastφ with ⟨Hpast, hBeforePast, hSatφ⟩
  rcases hBeforePast with ⟨evtPast, hMemPast⟩
  -- Transport liveness to the predecessor history.
  have hLivePast :
      ⟨Hpast,p⟩ ⊨[M,σ] liveFormula liveSymb :=
    (live_always_equiv_part1 (M := M) (σ := σ)
      (hTheory := hTheory) (hMem := hMemPast)).mpr hLivePresent
  -- Combine the predecessor facts to witness `(live ∧ φ)` in the past.
  have hConjPast :
      ⟨Hpast,p⟩ ⊨[M,σ]
        (liveFormula liveSymb) ∧ᶠ φ :=
    Sat.and_intro (M := M) (σ := σ)
      (H := Hpast) (p := p)
      (φ := liveFormula liveSymb) (ψ := φ)
      hLivePast hSatφ
  have hPastConj :
      ⟨M.history,p⟩ ⊨[M,σ]
        ↓ᶠ ((liveFormula liveSymb) ∧ᶠ φ) :=
    Sat.past_intro_of_prefix (M := M) (σ := σ)
      (H := M.history) (H' := Hpast) (p := p)
      ⟨evtPast, hMemPast⟩ hConjPast
  -- Package the past witness for the empty learner diamond.
  have hPastWitness :
      ∃ r : P,
        ⟨M.history,r⟩ ⊨[M ∣ᵥ M.history,σ]
          ↓ᶠ ((liveFormula liveSymb) ∧ᶠ φ) :=
    ⟨p, by simpa [ModalDistribution.Model.localView_full]
      using hPastConj⟩
  -- The chosen witness works for every evaluation point `p₀`.
  intro p₀
  have hDiamond :=
    sat_diamondEmpty_of_local (M := M) (σ := σ)
      (H := M.history) (p := p₀)
      (φ := ↓ᶠ ((liveFormula liveSymb) ∧ᶠ φ)) hPastWitness
  simpa [Formula.diamondPast, Formula.diamondEmpty, Term.ofValues]
    using hDiamond

end Results

end Examples
end ModalDistribution
