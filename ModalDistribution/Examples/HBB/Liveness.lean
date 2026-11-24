import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Properties

/-!
# Shared liveness lemmas

Lemmas 6.5.2 and 6.5.3 and their supporting lemmas. They depend only on
`thyLive`, so the three broadcast theories `HBBSafe`, `HBBSimp`, and `HBBCorr`
all use them.

- `past_end_of_sometime_imp`, `sometime_live_imp_of_sometime_imp`: the step
  shared by Lemma 6.5.2 and its variants, and its `live` form
- `boxPast_of_eventual_quorum`, `boxPast_live_of_eventual_quorum`:
  Lemma 6.5.2(1) and (2)
- `boxPast_mono_of_history`: `■_l` is monotone along implications that hold on
  the history
- `diamondPast_live_of_eventual`: the `♦` counterpart of Lemma 6.5.2(2)
- `live_eventually_consequent`: Lemma 6.5.3
-/

namespace ModalDistribution
namespace Examples
namespace HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

section Results

variable {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}

/-- One step of Lemma 6.5.2: if `↕φ ⇒ ↕ψ` holds at every world, a participant
that had `φ` at some event-tuple has `ψ` at some event-tuple. -/
theorem past_end_of_sometime_imp
    {φ ψ : Formula S} {q : P}
    (hImp : □W⊨[M]((↕ᶠ φ) ⇒ᶠ ↕ᶠψ))
    (hφ : ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]↓ᶠ φ) :
    ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]↓ᶠ ψ := by
  obtain ⟨t, ht, rfl, htφ⟩ := (Sat.past M _ _).1 hφ
  exact Sat.imp_elim M t (AllWorldValid.of_mem_history M hImp ht) (Sat.sometime_of_mem M ht htφ)

/-- Liveness survives an eventual consequence: by Lemma 5.2.9(2), if
`↕(live ∧ φ) ⇒ ↕ψ` holds at every world, so does `↕(live ∧ φ) ⇒ ↕(live ∧ ψ)`. -/
theorem sometime_live_imp_of_sometime_imp
    (hLiveTheory : M ⊨ᵀ thyLive liveSymb)
    {φ ψ : Formula S}
    (hImp : □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠψ)) :
    □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠ(predicate0 liveSymb ∧ᶠ ψ)) := by
  intro t ht
  refine Sat.imp_intro M t fun h => ?_
  obtain ⟨s, hs, hsPlace, hsLiveφ⟩ := (Sat.sometime M t _).1 h
  obtain ⟨s', hs', hs'Place, hψ⟩ := (Sat.sometime M t _).1 (Sat.imp_elim M t (hImp ht) h)
  exact (Sat.sometime M t _).2 ⟨s', hs', hs'Place, (Sat.and M s' _ _).2
    ⟨(always_live_equiv_backward hLiveTheory hs hs' (hsPlace.trans hs'Place.symm)).1
      ((Sat.and M s _ _).1 hsLiveφ).1, hψ⟩⟩

/-- Paper: Lemma 6.5.2(1). Quorum knowledge of `φ` and a
global implication to `ψ` lift `φ` to a future quorum of `ψ`. -/
theorem boxPast_of_eventual_quorum
    (φ ψ : Formula S)
    (l : Signature.Value S)
    (hQuorum : ⊨[M]□ᶠ↓[[l]]φ)
    (hImp : □W⊨[M]((↕ᶠ φ) ⇒ᶠ ↕ᶠψ)) :
    ⊨[M]□ᶠ↓[[l]] ψ := fun p =>
  -- Every member of the quorum that had `φ` eventually has `ψ`.
  Sat.box_of_imp [l] (fun _ => past_end_of_sometime_imp hImp) (hQuorum p)

/-- Paper: Lemma 6.5.2(2). The previous result under the
`thyLive` assumption. -/
theorem boxPast_live_of_eventual_quorum
    (hLiveTheory : M ⊨ᵀ thyLive liveSymb)
    (φ ψ : Formula S)
    (l : Signature.Value S)
    (hQuorum : ⊨[M]□ᶠ↓[[l]](predicate0 liveSymb ∧ᶠ φ))
    (hImp : □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠψ)) :
    ⊨[M]□ᶠ↓[[l]](predicate0 liveSymb ∧ᶠ ψ) :=
  boxPast_of_eventual_quorum _ _ l hQuorum (sometime_live_imp_of_sometime_imp hLiveTheory hImp)

/-- `■_l` is monotone along implications that hold at every event-tuple of
the model: the past event-tuples witnessing a quorum box all lie in `H`. -/
theorem boxPast_mono_of_history
    {φ ψ : Formula S} {l : Signature.Value S}
    (hImp : ∀ t ∈ M.history.val, (⟪t⟫ ⊨[M] φ) → ⟪t⟫ ⊨[M] ψ)
    (hQuorum : ⊨[M]□ᶠ↓[[l]]φ) :
    ⊨[M]□ᶠ↓[[l]]ψ := fun p =>
  Sat.box_of_imp [l] (fun _ => Sat.past_of_imp fun t ht _ => hImp t ht) (hQuorum p)

/-- The `♦` counterpart of Lemma 6.5.2(2): if some live participant had `φ`
at an event-tuple, and `↕(live ∧ φ) ⇒ ↕ψ` is valid, then some live
participant has `ψ` at an event-tuple. -/
theorem diamondPast_live_of_eventual
    (hLiveTheory : M ⊨ᵀ thyLive liveSymb)
    (φ ψ : Formula S)
    (hDiamond : ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ φ))
    (hImp : □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠψ)) :
    ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ ψ) := fun p =>
  Sat.diamond_of_imp []
    (fun _ => past_end_of_sometime_imp (sometime_live_imp_of_sometime_imp hLiveTheory hImp))
    (hDiamond p)

/-- Paper: Lemma 6.5.3. Composing eventual consequences at the end of
time. -/
theorem live_eventually_consequent
    (hLiveTheory : M ⊨ᵀ thyLive liveSymb)
    (φ ψ : Formula S)
    (hLive : ⊨[M](predicate0 liveSymb ⇒ᶠ ↕ᶠφ))
    (hImp : □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠψ)) :
    ⊨[M](predicate0 liveSymb ⇒ᶠ ↕ᶠψ) := by
  -- A live `p` has `φ` at some event-tuple `t`, which is live by Lemma 5.2.9(1);
  -- the implication at `t` gives `ψ` eventually.
  refine fun p => Sat.imp_intro M _ fun hpLive => ?_
  obtain ⟨t, ht, rfl, htφ⟩ :=
    (Sat.past M ⟨p, †, M.history.val⟩ φ).1 (Sat.imp_elim M _ (hLive p) hpLive)
  exact past_end_of_sometime_imp hImp ((Sat.past M _ _).2 ⟨t, ht, rfl,
    (Sat.and M t _ _).2 ⟨(always_live_equiv_forward hLiveTheory ht).2 hpLive, htφ⟩⟩)

end Results

end HBB
end Examples
end ModalDistribution
