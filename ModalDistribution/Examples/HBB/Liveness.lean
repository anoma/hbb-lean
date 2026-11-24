import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Properties

/-!
# Shared liveness lemmas

Lemmas 6.5.2 and 6.5.3 and their supporting lemmas. They depend only on
`ThyLive`, so the three broadcast theories `HBBSafe`, `HBBSimp`, and `HBBCorr`
all use them.

- `boxPast_of_eventual_quorum`, `boxPast_live_of_eventual_quorum`:
  Lemma 6.5.2(1) and (2)
- `boxPast_mono_of_history`: `■_l` is monotone along implications that hold on
  the history
- `diamondPast_live_of_eventual`: the `♦` counterpart of Lemma 6.5.2(2)
- `live_sometime_consequent_at`, `live_eventually_consequent`: Lemma 6.5.3 and
  its per-place core
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

/-- Paper: Lemma 6.5.2(1). Quorum knowledge of `φ` and a
global implication to `ψ` lift `φ` to a future quorum of `ψ`. -/
theorem boxPast_of_eventual_quorum
    (φ ψ : Formula S)
    (l : Signature.Value S)
    (hQuorum : ⊨[M]□ᶠ↓[[l]]φ)
    (hImp : □W⊨[M]((↕ᶠ φ) ⇒ᶠ ↕ᶠψ)) :
    ⊨[M]□ᶠ↓[[l]] ψ := by
  classical
  refine fun p => ?_
  let wₚ : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hBox_p :
      ⟪wₚ⟫ ⊨[M]
        □ᶠ[[l]] (Formula.past φ) := by
    simpa [Formula.boxPast, wₚ]
      using hQuorum p
  obtain ⟨O, hO, hAllφ⟩ :=
    (sat_box_singleton_exists (M := M)
        (w := wₚ) (l := l)
        (φ := Formula.past φ)).1 hBox_p
  have hImp_event : AllWorldValid M ((↕ᶠ φ) ⇒ᶠ ↕ᶠ ψ) := hImp
  refine
    (sat_box_singleton_exists (M := M)
        (w := wₚ) (l := l)
        (φ := Formula.past ψ)).2 ?_
  refine ⟨O, hO, ?_⟩
  intro q hqO
  have hPastφ :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] Formula.past φ := by
    simpa [wₚ]
      using hAllφ q hqO
  obtain ⟨tPast, ht_mem, ht_place, hφ_t⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := φ)).1 hPastφ
  rcases tPast with ⟨q', evtPast, HPast⟩
  have ht_mem_history :
      (q', evtPast, HPast) ∈ M.history.val := by
    simpa [World.time]
      using ht_mem
  have hImp_local :=
    AllWorldValid.of_mem_history
      (M := M) (φ := (↕ᶠ φ) ⇒ᶠ ↕ᶠ ψ)
      hImp_event ht_mem_history
  have hSometime :
      ⟪⟨q', evtPast, HPast⟩⟫ ⊨[M] ↕ᶠ ψ :=
    (Sat.imp (M := M)
      (w := ⟨q', evtPast, HPast⟩)
      (φ := ↕ᶠ φ) (ψ := ↕ᶠ ψ)).1 hImp_local
      (Sat.sometime_of_mem (M := M) ht_mem_history hφ_t)
  have hPastψ_end :
      ⟪⟨q', †, M.history.val⟩⟫ ⊨[M] Formula.past ψ :=
    (Sat.atEnd (M := M)
      (w := ⟨q', evtPast, HPast⟩)
      (φ := Formula.past ψ)).1
      (by
        simpa [Formula.sometime] using hSometime)
  have hPastψ :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] Formula.past ψ := by
    cases ht_place
    simpa using hPastψ_end
  simpa using hPastψ

/-- Paper: Lemma 6.5.2(2). The previous result under the
`ThyLive` assumption. -/
theorem boxPast_live_of_eventual_quorum
    (hLiveTheory : M ⊨ᵀ ThyLive liveSymb)
    (φ ψ : Formula S)
    (l : Signature.Value S)
    (hQuorum : ⊨[M]□ᶠ↓[[l]](predicate0 liveSymb ∧ᶠ φ))
    (hImp : □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠψ)) :
    ⊨[M]□ᶠ↓[[l]](predicate0 liveSymb ∧ᶠ ψ) := by
  classical
  refine fun p => ?_
  let wₚ : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hBox_p :
      ⟪wₚ⟫ ⊨[M]
        □ᶠ[[l]]
          (Formula.past (predicate0 liveSymb ∧ᶠ φ)) := by
    simpa [Formula.boxPast, wₚ]
      using hQuorum p
  obtain ⟨O, hO, hAllLiveφ⟩ :=
    (sat_box_singleton_exists (M := M)
        (w := wₚ) (l := l)
        (φ := Formula.past (predicate0 liveSymb ∧ᶠ φ))).1 hBox_p
  have hImp_event :
      AllWorldValid M ((↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠ ψ) := hImp
  refine
    (sat_box_singleton_exists (M := M)
        (w := wₚ) (l := l)
        (φ := Formula.past (predicate0 liveSymb ∧ᶠ ψ))).2 ?_
  refine ⟨O, hO, ?_⟩
  intro q hqO
  have hPastLiveφ :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
        Formula.past (predicate0 liveSymb ∧ᶠ φ) := by
    simpa [wₚ]
      using hAllLiveφ q hqO
  obtain ⟨tφ, htφ_mem, htφ_place, hLiveφ_tφ⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := predicate0 liveSymb ∧ᶠ φ)).1 hPastLiveφ
  rcases tφ with ⟨qφ, evtφ, Hφ⟩
  have htφ_place' : qφ = q := htφ_place
  have hLiveφ_split :=
    (Sat.and (M := M) (w := ⟨qφ, evtφ, Hφ⟩)
      (φ := predicate0 liveSymb) (ψ := φ)).1 hLiveφ_tφ
  have hLive_tφ :
      ⟪⟨qφ, evtφ, Hφ⟩⟫ ⊨[M] predicate0 liveSymb := hLiveφ_split.1
  have htφ_mem_history :
      (qφ, evtφ, Hφ) ∈ M.history.val := by
    simpa [World.time]
      using htφ_mem
  have hImp_local :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := (↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠ ψ)
      hImp_event htφ_mem_history
  have hSometime :
      ⟪⟨qφ, evtφ, Hφ⟩⟫ ⊨[M] ↕ᶠ ψ :=
    (Sat.imp (M := M)
      (w := ⟨qφ, evtφ, Hφ⟩)
      (φ := ↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) (ψ := ↕ᶠ ψ)).1
      hImp_local (Sat.sometime_of_mem (M := M) htφ_mem_history hLiveφ_tφ)
  have hPastψ :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] Formula.past ψ := by
    have hPastψ_end :
        ⟪⟨qφ, †, M.history.val⟩⟫ ⊨[M] Formula.past ψ :=
      (Sat.atEnd (M := M)
        (w := ⟨qφ, evtφ, Hφ⟩)
        (φ := Formula.past ψ)).1
        (by
          simpa [Formula.sometime] using hSometime)
    cases htφ_place'
    simpa using hPastψ_end
  obtain ⟨tψ, htψ_mem, htψ_place, hψ_tψ⟩ :=
    (Sat.past (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (φ := ψ)).1 hPastψ
  rcases tψ with ⟨qψ, evtψ, Hψ⟩
  have htψ_place' : qψ = q := htψ_place
  have hEquiv :=
      alwaysLiveEquivForward (M := M)
        (liveSymb := liveSymb)
        (hTheory := hLiveTheory)
        (t := ⟨qφ, evtφ, Hφ⟩)
        (ht := by simpa using htφ_mem)
  have hLive_global' :
      ⟪⟨qφ, †, M.history.val⟩⟫ ⊨[M] predicate0 liveSymb :=
    (hEquiv).1 hLive_tφ
  have htφ_place_copy := htφ_place'
  have hLive_global :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M] predicate0 liveSymb := by
    cases htφ_place_copy
    simpa using hLive_global'
  have hLive_global_qψ :
      ⟪⟨qψ, †, M.history.val⟩⟫ ⊨[M] predicate0 liveSymb := by
    have htψ_place_copy := htψ_place'
    cases htψ_place_copy
    simpa using hLive_global
  have hLive_tψ :
      ⟪⟨qψ, evtψ, Hψ⟩⟫ ⊨[M] predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
        (liveSymb := liveSymb)
        (hTheory := hLiveTheory)
        (t := ⟨qψ, evtψ, Hψ⟩)
        (ht := by simpa [World.time] using htψ_mem)).mpr hLive_global_qψ
  have hConj_tψ :
      ⟪⟨qψ, evtψ, Hψ⟩⟫ ⊨[M]
        (predicate0 liveSymb ∧ᶠ ψ) :=
    (Sat.and (M := M) (w := ⟨qψ, evtψ, Hψ⟩)
      (φ := predicate0 liveSymb) (ψ := ψ)).2
      ⟨hLive_tψ, hψ_tψ⟩
  have hPastLiveψ :
      ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
        Formula.past (predicate0 liveSymb ∧ᶠ ψ) :=
    (Sat.past_intro_of_prefix (M := M)
      (w := ⟨q, †, M.history.val⟩)
      (t := ⟨qψ, evtψ, Hψ⟩)
      (φ := predicate0 liveSymb ∧ᶠ ψ)
      (ht := by simpa [World.time] using htψ_mem)
      (hp := by simpa [World.place] using htψ_place)
      (hφ := hConj_tψ))
  simpa [wₚ]
    using hPastLiveψ

/-- `■_l` is monotone along implications that hold at every event-tuple of
the model: the past event-tuples witnessing a quorum box all lie in `H`. -/
theorem boxPast_mono_of_history
    {φ ψ : Formula S} {l : Signature.Value S}
    (hImp : ∀ t ∈ M.history.val, (⟪t⟫ ⊨[M] φ) → ⟪t⟫ ⊨[M] ψ)
    (hQuorum : ⊨[M]□ᶠ↓[[l]]φ) :
    ⊨[M]□ᶠ↓[[l]]ψ := by
  classical
  intro p
  have hBox :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] □ᶠ[[l]] (↓ᶠ φ) := by
    simpa [Formula.boxPast] using hQuorum p
  have hBoxψ :=
    Sat.box_of_imp (M := M) (w := ⟨p, †, M.history.val⟩) [l]
      (φ := ↓ᶠ φ) (ψ := ↓ᶠ ψ)
      (fun q hq =>
        Sat.past_of_imp (M := M) (w := ⟨q, †, M.history.val⟩)
          (fun t ht _ hφ => hImp t (by simpa [World.time] using ht) hφ) hq)
      hBox
  simpa [Formula.boxPast] using hBoxψ

/-- The `♦` counterpart of Lemma 6.5.2(2): if some live participant had `φ`
at an event-tuple, and `↕(live ∧ φ) ⇒ ↕ψ` is valid, then some live
participant has `ψ` at an event-tuple. -/
theorem diamondPast_live_of_eventual
    (hLiveTheory : M ⊨ᵀ ThyLive liveSymb)
    (φ ψ : Formula S)
    (hDiamond : ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ φ))
    (hImp : □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠψ)) :
    ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ ψ) := by
  classical
  let p₀ : P := Classical.choice inferInstance
  obtain ⟨q, hPast⟩ :=
    (Sat.diamond_nil (M := M) (w := ⟨p₀, †, M.history.val⟩)
      (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ φ))).1
      (by simpa [Formula.diamondPast] using hDiamond p₀)
  obtain ⟨t, ht, -, hConj⟩ :=
    (Sat.past (M := M) (w := ⟨q, †, M.history.val⟩)
      (φ := predicate0 liveSymb ∧ᶠ φ)).1 hPast
  have htH : t ∈ M.history.val := by simpa [World.time] using ht
  have hSome : ⟪t⟫ ⊨[M] ↕ᶠ ψ :=
    Sat.imp_elim (M := M) (w := t)
      (AllWorldValid.of_mem_history (M := M) hImp htH)
      (Sat.sometime_of_mem (M := M) htH hConj)
  obtain ⟨t', ht', hPlace, hψ⟩ :=
    (Sat.sometime (M := M) (w := t) (φ := ψ)).1 hSome
  have hLive' : ⟪t'⟫ ⊨[M] predicate0 liveSymb :=
    (alwaysLiveEquivBackward (M := M) (hTheory := hLiveTheory)
      (ht := htH) (ht' := ht') (hplace := hPlace.symm)).1
      ((Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb) (ψ := φ)).1 hConj).1
  have hPast' :
      ⟪⟨t'.place, †, M.history.val⟩⟫ ⊨[M]
        ↓ᶠ (predicate0 liveSymb ∧ᶠ ψ) :=
    Sat.past_intro_of_prefix (M := M)
      (w := ⟨t'.place, †, M.history.val⟩) (t := t')
      (ht := by simpa [World.time] using ht') (hp := rfl)
      (hφ := (Sat.and (M := M) (w := t')
        (φ := predicate0 liveSymb) (ψ := ψ)).2 ⟨hLive', hψ⟩)
  intro p
  simpa [Formula.diamondPast, Formula.diamondEmpty, id] using
    sat_diamondEmpty_of_local (M := M) (w := ⟨p, †, M.history.val⟩)
      (φ := ↓ᶠ (predicate0 liveSymb ∧ᶠ ψ)) ⟨t'.place, hPast'⟩

/-- The per-place core of Lemma 6.5.3: at a live end-of-time world, an
eventual `φ` combines with the implication `↕(live ∧ φ) ⇒ ↕ψ` to give an
eventual `ψ`. -/
theorem live_sometime_consequent_at
    (hLiveTheory : M ⊨ᵀ ThyLive liveSymb)
    {φ ψ : Formula S} {p : P}
    (hImp : □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠψ))
    (hLive_p : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]predicate0 liveSymb)
    (hSometimeφ : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]↕ᶠφ) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]↕ᶠψ := by
  classical
  let wₚ : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hImp_event : AllWorldValid M ((↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠ ψ) := hImp
  show ⟪wₚ⟫ ⊨[M] ↕ᶠ ψ
  have hPastφ :
      ⟪wₚ⟫ ⊨[M] Formula.past φ :=
    (Sat.atEnd (M := M)
      (w := wₚ)
      (φ := Formula.past φ)).1
      (by
        simpa [Formula.sometime] using hSometimeφ)
  obtain ⟨tφ, htφ_mem, htφ_place, hφ_tφ⟩ :=
    (Sat.past (M := M)
      (w := wₚ)
      (φ := φ)).1 hPastφ
  rcases tφ with ⟨qφ, evtφ, Hφ⟩
  have htφ_place' : qφ = p := htφ_place
  have htφ_place_copy1 := htφ_place'
  have htφ_place_copy2 := htφ_place'
  have hLive_local :
      ⟪⟨qφ, evtφ, Hφ⟩⟫ ⊨[M] predicate0 liveSymb :=
    (alwaysLiveEquivForward (M := M)
        (liveSymb := liveSymb)
        (hTheory := hLiveTheory)
      (t := ⟨qφ, evtφ, Hφ⟩)
        (ht := by simpa [World.time] using htφ_mem)).mpr
      (by
        cases htφ_place_copy1
        simpa using hLive_p)
  have htφ_mem_history :
      (qφ, evtφ, Hφ) ∈ M.history.val := by
    simpa [World.time]
      using htφ_mem
  have hImp_local :=
    AllWorldValid.of_mem_history
      (M := M)
      (φ := (↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠ ψ)
      hImp_event htφ_mem_history
  have hConj :
      ⟪⟨qφ, evtφ, Hφ⟩⟫ ⊨[M]
        (predicate0 liveSymb ∧ᶠ φ) :=
    (Sat.and (M := M) (w := ⟨qφ, evtφ, Hφ⟩)
      (φ := predicate0 liveSymb) (ψ := φ)).2
      ⟨hLive_local, hφ_tφ⟩
  have hSometimeψ_tφ :
      ⟪⟨qφ, evtφ, Hφ⟩⟫ ⊨[M] ↕ᶠ ψ :=
    (Sat.imp (M := M)
      (w := ⟨qφ, evtφ, Hφ⟩)
      (φ := ↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) (ψ := ↕ᶠ ψ)).1
      hImp_local (Sat.sometime_of_mem (M := M) htφ_mem_history hConj)
  have hPastψ_raw :
      ⟪⟨qφ, †, M.history.val⟩⟫ ⊨[M] Formula.past ψ :=
    (Sat.atEnd (M := M)
      (w := ⟨qφ, evtφ, Hφ⟩)
      (φ := Formula.past ψ)).1
      (by
        simpa [Formula.sometime] using hSometimeψ_tφ)
  have htφ_place_copy3 := htφ_place_copy2
  have hPastψ :
      ⟪wₚ⟫ ⊨[M] Formula.past ψ := by
    cases htφ_place_copy3
    simpa using hPastψ_raw
  exact
    (Sat.atEnd (M := M)
      (w := wₚ)
      (φ := Formula.past ψ)).2 hPastψ

/-- Paper: Lemma 6.5.3. Composing eventual consequences at the end of
time. -/
theorem live_eventually_consequent
    (hLiveTheory : M ⊨ᵀ ThyLive liveSymb)
    (φ ψ : Formula S)
    (hLive : ⊨[M](predicate0 liveSymb ⇒ᶠ ↕ᶠφ))
    (hImp : □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ φ)) ⇒ᶠ ↕ᶠψ)) :
    ⊨[M](predicate0 liveSymb ⇒ᶠ ↕ᶠψ) := by
  intro p
  refine
    (Sat.imp (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (φ := predicate0 liveSymb) (ψ := ↕ᶠ ψ)).2 ?_
  intro hLive_p
  exact
    live_sometime_consequent_at (M := M)
      (hLiveTheory := hLiveTheory) (hImp := hImp)
      hLive_p
      ((Sat.imp (M := M)
        (w := ⟨p, †, M.history.val⟩)
        (φ := predicate0 liveSymb) (ψ := ↕ᶠ φ)).1
        (hLive p) hLive_p)

end Results

end HBB
end Examples
end ModalDistribution
