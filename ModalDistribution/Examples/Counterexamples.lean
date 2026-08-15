import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties

/-!
# Counterexamples for the modal properties

The paper's Lemma 4.2.1(3,4) and Lemma 4.2.3(3) are negative observations:
certain modal implications do not hold in general. This file realises them in
concrete models.

The model for Lemma 4.2.1(3,4): two participants (`Bool`), the empty history,
and two learners whose quorum systems are the up-closures of `{true}` and
`{false}` respectively — so the pair of quorums `{true}`, `{false}` has empty
intersection.
-/

namespace ModalDistribution
namespace Examples
namespace Counterexamples

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

/-- A signature with no symbols and `Bool` as values/learners. -/
def sig : Signature := ⟨Empty, Empty, Bool⟩

/-- The up-closure of `{p}`: all sets containing `p`. A semifilter. -/
def upset (p : Bool) : Semifilter Bool where
  quorums := {O | p ∈ O}
  nonempty := ⟨Set.univ, trivial⟩
  upwardClosed := by
    intro O O' hO hsub
    exact hsub hO
  pairwiseInter := by
    intro O O' hO hO'
    exact ⟨p, hO, hO'⟩

/-- The empty prehistory is hereditarily transitive. -/
theorem empty_hered :
    isHereditarilyTransitive (P := Bool) (Event := Signature.EventType sig)
      (PreHistory.mk []) := by
  refine (isHereditarilyTransitive_unfold _).mpr ⟨?_, ?_⟩
  · intro h' hb
    rcases hb with ⟨p, e, hm⟩
    cases hm
  · intro h' hb
    rcases hb with ⟨p, e, hm⟩
    cases hm

/-- The empty model over two participants with disjoint-quorum learners. -/
noncomputable def M : Model sig Bool where
  history := ⟨PreHistory.mk [], empty_hered⟩
  predInterp := fun _ _ => ∅
  learner := fun v => upset v

/-- The world at participant `true` at the (empty) end of time. -/
def w0 : World Bool (Signature.EventType sig) :=
  ⟨true, †, PreHistory.mk []⟩

/-- The quorum pair with empty intersection: `{true}` for learner `true`. -/
theorem trueSet_mem : {b : Bool | b = true} ∈ (M.learner true).quorums := rfl

/-- ... and `{false}` for learner `false`. -/
theorem falseSet_mem : {b : Bool | b = false} ∈ (M.learner false).quorums := rfl

/-- Paper: Lemma 4.2.1(3). `□l₁…lₙφ` does not imply `♢φ`: with an empty
quorum intersection the box holds vacuously (even of `⊥`), while `♢⊥` fails. -/
theorem box_not_implies_diamondEmpty :
    (⟪w0⟫ ⊨[M] □ᶠ[[true, false]] (⊥ᶠ : Formula sig)) ∧
      ¬ (⟪w0⟫ ⊨[M] ♢ᶠ[] (⊥ᶠ : Formula sig)) := by
  constructor
  · refine Sat.not_intro (M := M) (w := w0)
      (φ := ♢ᶠ[[true, false]] (¬ᶠ (⊥ᶠ : Formula sig))) ?_
    intro hDiamond
    have hCheck :
        Sat.check M
          (fun q => ⟪⟨q, †, w0.time⟩⟫ ⊨[M] (¬ᶠ (⊥ᶠ : Formula sig)))
          [true, false] Set.univ :=
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := [true, false]) (φ := ¬ᶠ (⊥ᶠ : Formula sig)) (w := w0)).1 hDiamond
    have h1 :=
      (Sat.Sat_check_cons (M := M)
        (Q := fun q => ⟪⟨q, †, w0.time⟩⟫ ⊨[M] (¬ᶠ (⊥ᶠ : Formula sig)))
        (v := true) (vs := [false]) (acc := Set.univ)).1 hCheck
        {b : Bool | b = true} trueSet_mem
    have h2 :=
      (Sat.Sat_check_cons (M := M)
        (Q := fun q => ⟪⟨q, †, w0.time⟩⟫ ⊨[M] (¬ᶠ (⊥ᶠ : Formula sig)))
        (v := false) (vs := []) (acc := Set.univ ∩ {b : Bool | b = true})).1 h1
        {b : Bool | b = false} falseSet_mem
    obtain ⟨p, hpMem, _⟩ :=
      (Sat.Sat_check_nil (M := M)
        (Q := fun q => ⟪⟨q, †, w0.time⟩⟫ ⊨[M] (¬ᶠ (⊥ᶠ : Formula sig)))
        (acc := (Set.univ ∩ {b : Bool | b = true}) ∩ {b : Bool | b = false})).1 h2
    have hTrue : p = true := hpMem.1.2
    have hFalse : p = false := hpMem.2
    rw [hTrue] at hFalse
    cases hFalse
  · intro hDiamond
    obtain ⟨p, hp⟩ :=
      (Sat.diamondEmpty (M := M) (w := w0)
        (φ := (⊥ᶠ : Formula sig))).1 hDiamond
    exact hp

/-- Paper: Lemma 4.2.1(4). `φ` does not imply `♢l₁…lₙφ`: even `⊤` fails under
the diamond when some quorum intersection is empty. -/
theorem sat_not_implies_diamond :
    (⟪w0⟫ ⊨[M] (⊤ᶠ : Formula sig)) ∧
      ¬ (⟪w0⟫ ⊨[M] ♢ᶠ[[true, false]] (⊤ᶠ : Formula sig)) := by
  constructor
  · exact Sat.top (M := M) (w := w0)
  · intro hDiamond
    have hCheck :=
      (sat_diamond_iff_diamondCheck (M := M)
        (ls := [true, false]) (φ := (⊤ᶠ : Formula sig)) (w := w0)).1 hDiamond
    have h1 :=
      (Sat.Sat_check_cons (M := M)
        (Q := fun q => ⟪⟨q, †, w0.time⟩⟫ ⊨[M] (⊤ᶠ : Formula sig))
        (v := true) (vs := [false]) (acc := Set.univ)).1 hCheck
        {b : Bool | b = true} trueSet_mem
    have h2 :=
      (Sat.Sat_check_cons (M := M)
        (Q := fun q => ⟪⟨q, †, w0.time⟩⟫ ⊨[M] (⊤ᶠ : Formula sig))
        (v := false) (vs := []) (acc := Set.univ ∩ {b : Bool | b = true})).1 h1
        {b : Bool | b = false} falseSet_mem
    obtain ⟨p, hpMem, _⟩ :=
      (Sat.Sat_check_nil (M := M)
        (Q := fun q => ⟪⟨q, †, w0.time⟩⟫ ⊨[M] (⊤ᶠ : Formula sig))
        (acc := (Set.univ ∩ {b : Bool | b = true}) ∩ {b : Bool | b = false})).1 h2
    have hTrue : p = true := hpMem.1.2
    have hFalse : p = false := hpMem.2
    rw [hTrue] at hFalse
    cases hFalse


/-! ## Lemma 4.2.3(3): the collapsing implications do not reverse

The paper's model: one participant, three events `E₁, E₂, F`, one learner
whose quorums are all sets containing the participant, and the history

`H = {(p,F,H₁), (p,E₁,∅), (p,F,H₂), (p,E₂,∅)}` with `H₁ = {(p,E₁,∅)}`,
`H₂ = {(p,E₂,∅)}`.

At the end of time, `□↓F` holds (the participant has a past `F`), but
`↓□↓F` and `♢↓□↓F` both fail: at the time of every event-tuple in `H`, no
`F` has yet occurred.
-/

/-- A signature with three event symbols and a single value/learner. -/
def sig3 : Signature := ⟨Fin 3, Empty, Unit⟩

/-- The three events. -/
def evE₁ : Signature.EventType sig3 := ⟨(0 : Fin 3), []⟩
def evE₂ : Signature.EventType sig3 := ⟨(1 : Fin 3), []⟩
def evF : Signature.EventType sig3 := ⟨(2 : Fin 3), []⟩

def tE₁ : World Unit (Signature.EventType sig3) :=
  ((), MaybeEvent.some evE₁, PreHistory.mk [])
def tE₂ : World Unit (Signature.EventType sig3) :=
  ((), MaybeEvent.some evE₂, PreHistory.mk [])
def H₁ : PreHistory Unit (Signature.EventType sig3) := PreHistory.mk [tE₁]
def H₂ : PreHistory Unit (Signature.EventType sig3) := PreHistory.mk [tE₂]
def tF₁ : World Unit (Signature.EventType sig3) :=
  ((), MaybeEvent.some evF, H₁)
def tF₂ : World Unit (Signature.EventType sig3) :=
  ((), MaybeEvent.some evF, H₂)

/-- The full history `H₃ ∪ H₄` of the counterexample. -/
def bigH : PreHistory Unit (Signature.EventType sig3) :=
  PreHistory.mk [tF₁, tE₁, tF₂, tE₂]

theorem empty_hered₃ :
    isHereditarilyTransitive (P := Unit) (Event := Signature.EventType sig3)
      (PreHistory.mk []) := by
  refine (isHereditarilyTransitive_unfold _).mpr ⟨?_, ?_⟩ <;>
    · intro h' hb
      rcases hb with ⟨p, e, hm⟩
      cases hm

theorem singleton_hered (t : World Unit (Signature.EventType sig3))
    (ht : t.2.2 = PreHistory.mk []) :
    isHereditarilyTransitive (P := Unit) (Event := Signature.EventType sig3)
      (PreHistory.mk [t]) := by
  refine (isHereditarilyTransitive_unfold _).mpr ⟨?_, ?_⟩
  · intro h' hb
    rcases hb with ⟨p, e, hm⟩
    have hmL : (p, e, h') ∈ [t] := hm
    rcases List.mem_cons.1 hmL with heq | hnil
    · have hh : h' = t.2.2 := congrArg (fun x => x.2.2) heq
      rw [hh, ht]
      intro x hx
      cases hx
    · cases hnil
  · intro h' hb
    rcases hb with ⟨p, e, hm⟩
    have hmL : (p, e, h') ∈ [t] := hm
    rcases List.mem_cons.1 hmL with heq | hnil
    · have hh : h' = t.2.2 := congrArg (fun x => x.2.2) heq
      rw [hh, ht]
      exact empty_hered₃
    · cases hnil

theorem bigH_hered :
    isHereditarilyTransitive (P := Unit) (Event := Signature.EventType sig3)
      bigH := by
  have hsub₁ : (H₁ : PreHistory Unit (Signature.EventType sig3)) ⊆ bigH := by
    intro x hx
    have hxL : x ∈ [tE₁] := hx
    rcases List.mem_cons.1 hxL with heq | hnil
    · rw [heq]
      exact List.Mem.tail _ (List.Mem.head _)
    · cases hnil
  have hsub₂ : (H₂ : PreHistory Unit (Signature.EventType sig3)) ⊆ bigH := by
    intro x hx
    have hxL : x ∈ [tE₂] := hx
    rcases List.mem_cons.1 hxL with heq | hnil
    · rw [heq]
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    · cases hnil
  have hTimes :
      ∀ {p : Unit} {e : MaybeEvent (Signature.EventType sig3)}
        {h' : PreHistory Unit (Signature.EventType sig3)},
        (p, e, h') ∈ bigH →
          h' = H₁ ∨ h' = H₂ ∨ h' = PreHistory.mk [] := by
    intro p e h' hm
    have hmL : (p, e, h') ∈ [tF₁, tE₁, tF₂, tE₂] := hm
    rcases List.mem_cons.1 hmL with heq | h2
    · exact Or.inl (congrArg (fun x => x.2.2) heq)
    · rcases List.mem_cons.1 h2 with heq | h3
      · exact Or.inr (Or.inr (congrArg (fun x => x.2.2) heq))
      · rcases List.mem_cons.1 h3 with heq | h4
        · exact Or.inr (Or.inl (congrArg (fun x => x.2.2) heq))
        · rcases List.mem_cons.1 h4 with heq | hnil
          · exact Or.inr (Or.inr (congrArg (fun x => x.2.2) heq))
          · cases hnil
  refine (isHereditarilyTransitive_unfold _).mpr ⟨?_, ?_⟩
  · intro h' hb
    rcases hb with ⟨p, e, hm⟩
    rcases hTimes hm with rfl | rfl | rfl
    · exact hsub₁
    · exact hsub₂
    · intro x hx
      cases hx
  · intro h' hb
    rcases hb with ⟨p, e, hm⟩
    rcases hTimes hm with rfl | rfl | rfl
    · exact singleton_hered tE₁ rfl
    · exact singleton_hered tE₂ rfl
    · exact empty_hered₃

/-- The model of the Lemma 4.2.3(3) counterexample. -/
noncomputable def M₃ : Model sig3 Unit where
  history := ⟨bigH, bigH_hered⟩
  predInterp := fun _ _ => ∅
  learner := fun _ =>
    { quorums := {O | () ∈ O}
      nonempty := ⟨Set.univ, trivial⟩
      upwardClosed := by
        intro O O' hO hsub
        exact hsub hO
      pairwiseInter := by
        intro O O' hO hO'
        exact ⟨(), hO, hO'⟩ }

/-- The end-of-time world of the counterexample. -/
def w₃ : World Unit (Signature.EventType sig3) := ((), †, bigH)

/-- No `F` occurs at any time strictly inside the counterexample history:
`↓F` fails at any world whose time is `H₁`, `H₂`, or `∅`. -/
theorem no_past_F (x : MaybeEvent (Signature.EventType sig3))
    (T : PreHistory Unit (Signature.EventType sig3))
    (hT : T = H₁ ∨ T = H₂ ∨ T = PreHistory.mk []) :
    ¬ (⟪((), x, T)⟫ ⊨[M₃] ↓ᶠ (ofEvent evF)) := by
  intro h
  obtain ⟨t, ht_mem, _, ht_sat⟩ :=
    (Sat.past (M := M₃) (w := ((), x, T)) (φ := ofEvent evF)).1 h
  have hEvt : t.2.1 = MaybeEvent.some evF :=
    ((Sat.ofEvent (M := M₃) (w := t) (E := evF)).1 ht_sat).1
  rcases hT with rfl | rfl | rfl
  · have hmL : t ∈ [tE₁] := ht_mem
    rcases List.mem_cons.1 hmL with heq | hnil
    · rw [heq] at hEvt
      simp [tE₁, evE₁, evF] at hEvt
      exact (show (0 : Fin 3) ≠ (2 : Fin 3) by decide) hEvt
    · cases hnil
  · have hmL : t ∈ [tE₂] := ht_mem
    rcases List.mem_cons.1 hmL with heq | hnil
    · rw [heq] at hEvt
      simp [tE₂, evE₂, evF] at hEvt
      exact (show (1 : Fin 3) ≠ (2 : Fin 3) by decide) hEvt
    · cases hnil
  · have hmL : t ∈ ([] : List (World Unit (Signature.EventType sig3))) := ht_mem
    cases hmL

/-- Paper: Lemma 4.2.3(3). The collapsing implications of Lemma 4.2.3 do not
reverse: at the end of time `□↓F` holds, yet `↓□↓F` and `♢↓□↓F` both fail. -/
theorem pastBox_does_not_reverse :
    (⟪w₃⟫ ⊨[M₃] □ᶠ↓[[()]] (ofEvent evF)) ∧
      ¬ (⟪w₃⟫ ⊨[M₃] ↓ᶠ (□ᶠ↓[[()]] (ofEvent evF))) ∧
      ¬ (⟪w₃⟫ ⊨[M₃] ♢ᶠ↓[[()]] (□ᶠ↓[[()]] (ofEvent evF))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- □↓F at the end of time: every (the only) participant has a past F.
    have hPast : ⟪(((), †, bigH) : World Unit (Signature.EventType sig3))⟫
        ⊨[M₃] ↓ᶠ (ofEvent evF) := by
      refine (Sat.past (M := M₃) (w := ((), †, bigH))
        (φ := ofEvent evF)).2 ⟨tF₁, List.Mem.head _, rfl, ?_⟩
      refine (Sat.ofEvent (M := M₃) (w := tF₁) (E := evF)).2 ⟨rfl, ?_⟩
      exact List.Mem.head _
    have hBox :
        ⟪w₃⟫ ⊨[M₃] □ᶠ[[()]] (↓ᶠ (ofEvent evF)) :=
      (sat_box_singleton_exists (M := M₃) (w := w₃)
        (l := ()) (φ := ↓ᶠ (ofEvent evF))).2
        ⟨Set.univ, trivial, fun q _ => by
          cases q
          exact hPast⟩
    simpa [Formula.boxPast] using hBox
  · -- ¬↓□↓F: each event-tuple of H has time H₁, ∅, H₂, or ∅ — no past F there.
    intro h
    obtain ⟨t, ht_mem, _, ht_sat⟩ :=
      (Sat.past (M := M₃) (w := w₃)
        (φ := □ᶠ↓[[()]] (ofEvent evF))).1 h
    have hBox :
        ⟪t⟫ ⊨[M₃] □ᶠ[[()]] (↓ᶠ (ofEvent evF)) := by
      simpa [Formula.boxPast] using ht_sat
    obtain ⟨O, hO, hAll⟩ :=
      (sat_box_singleton_exists (M := M₃) (w := t)
        (l := ()) (φ := ↓ᶠ (ofEvent evF))).1 hBox
    have hPastF :
        ⟪(((), †, t.2.2) : World Unit (Signature.EventType sig3))⟫
          ⊨[M₃] ↓ᶠ (ofEvent evF) :=
      hAll () hO
    have hTimes : t.2.2 = H₁ ∨ t.2.2 = H₂ ∨ t.2.2 = PreHistory.mk [] := by
      have hmL : t ∈ [tF₁, tE₁, tF₂, tE₂] := ht_mem
      rcases List.mem_cons.1 hmL with heq | h2
      · exact Or.inl (congrArg (fun x => x.2.2) heq)
      · rcases List.mem_cons.1 h2 with heq | h3
        · exact Or.inr (Or.inr (congrArg (fun x => x.2.2) heq))
        · rcases List.mem_cons.1 h3 with heq | h4
          · exact Or.inr (Or.inl (congrArg (fun x => x.2.2) heq))
          · rcases List.mem_cons.1 h4 with heq | hnil
            · exact Or.inr (Or.inr (congrArg (fun x => x.2.2) heq))
            · cases hnil
    exact no_past_F † t.2.2 hTimes hPastF
  · -- ¬♢↓□↓F: the single-participant intersection witness would again need a
    -- past □↓F, refuted as above.
    intro h
    have hCheck :=
      (sat_diamond_iff_diamondCheck (M := M₃)
        (ls := [()]) (φ := ↓ᶠ (□ᶠ↓[[()]] (ofEvent evF))) (w := w₃)).1
        (by simpa [Formula.diamondPast] using h)
    have h1 :=
      (Sat.Sat_check_cons (M := M₃)
        (Q := fun q => ⟪⟨q, †, w₃.time⟩⟫ ⊨[M₃]
          ↓ᶠ (□ᶠ↓[[()]] (ofEvent evF)))
        (v := ()) (vs := []) (acc := Set.univ)).1 hCheck
        Set.univ trivial
    obtain ⟨q, _, hq⟩ :=
      (Sat.Sat_check_nil (M := M₃)
        (Q := fun q => ⟪⟨q, †, w₃.time⟩⟫ ⊨[M₃]
          ↓ᶠ (□ᶠ↓[[()]] (ofEvent evF)))
        (acc := Set.univ ∩ Set.univ)).1 h1
    cases q
    obtain ⟨t, ht_mem, _, ht_sat⟩ :=
      (Sat.past (M := M₃) (w := (((), †, w₃.time) : World Unit _))
        (φ := □ᶠ↓[[()]] (ofEvent evF))).1 hq
    have hBox :
        ⟪t⟫ ⊨[M₃] □ᶠ[[()]] (↓ᶠ (ofEvent evF)) := by
      simpa [Formula.boxPast] using ht_sat
    obtain ⟨O, hO, hAll⟩ :=
      (sat_box_singleton_exists (M := M₃) (w := t)
        (l := ()) (φ := ↓ᶠ (ofEvent evF))).1 hBox
    have hPastF :
        ⟪(((), †, t.2.2) : World Unit (Signature.EventType sig3))⟫
          ⊨[M₃] ↓ᶠ (ofEvent evF) :=
      hAll () hO
    have hTimes : t.2.2 = H₁ ∨ t.2.2 = H₂ ∨ t.2.2 = PreHistory.mk [] := by
      have hmL : t ∈ [tF₁, tE₁, tF₂, tE₂] := ht_mem
      rcases List.mem_cons.1 hmL with heq | h2
      · exact Or.inl (congrArg (fun x => x.2.2) heq)
      · rcases List.mem_cons.1 h2 with heq | h3
        · exact Or.inr (Or.inr (congrArg (fun x => x.2.2) heq))
        · rcases List.mem_cons.1 h3 with heq | h4
          · exact Or.inr (Or.inl (congrArg (fun x => x.2.2) heq))
          · rcases List.mem_cons.1 h4 with heq | hnil
            · exact Or.inr (Or.inr (congrArg (fun x => x.2.2) heq))
            · cases hnil
    exact no_past_F † t.2.2 hTimes hPastF

end Counterexamples
end Examples
end ModalDistribution
