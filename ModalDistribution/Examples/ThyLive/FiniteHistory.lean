import ModalDistribution.Examples.ThyLive

/-!
# Finite histories and unrestricted knowledge

Revised HBB4 proof note, Proposition 1.1. With the existing finite-history
semantics, `LiveAlways` and empty-index Knowledge alone exclude live events.
This diagnoses the progress assumptions; it makes no change to the semantics.
-/

namespace ModalDistribution.Examples.FiniteHistory

open ModalDistribution.Logic PreHistory History World
open scoped Formula

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {liveSymb : S.PredSymb}

/-- The closed formula asserting a causal predecessor chain of length `n`. -/
def causalDepthFormula : Nat → Formula S
  | 0 => ⊤ᶠ
  | n + 1 => ♢ᶠ↓[[]] (causalDepthFormula n)

/-- Unrestricted Knowledge and time-independent liveness exclude every
live event in a finite history. Only the depth-formula instances of Knowledge,
evaluated at end of time, are needed. -/
theorem no_live_event
    (hAlways : □W⊨[M] liveAlwaysAxiom liveSymb)
    (hKnowledge : ∀ n, ⊨[M] knowledgeDiamondAxiom liveSymb []
      (causalDepthFormula (S := S) n))
    {e : World P S.EventType} (he : e ∈ M.history.val) :
    ¬ (⟪e⟫ ⊨[M] Formula.predicate0 liveSymb) := by
  classical
  intro hLive
  have past_iff (w : World P S.EventType) (φ : Formula S) :
      (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] φ) ↔
        ∃ t ∈ w.time, ⟪t⟫ ⊨[M] φ := by
    change (⟪w⟫ ⊨[M] ♢ᶠ[[]] (↓ᶠ φ)) ↔ _
    rw [Sat.diamond_nil]
    constructor
    · rintro ⟨p, hp⟩
      obtain ⟨t, ht, _, hφ⟩ := (Sat.past M ⟨p, †, w.time⟩ φ).mp hp
      exact ⟨t, ht, hφ⟩
    · rintro ⟨t, ht, hφ⟩
      exact ⟨t.place, (Sat.past M ⟨t.place, †, w.time⟩ φ).mpr
        ⟨t, ht, rfl, hφ⟩⟩
  have depth_le (n : Nat) (w : World P S.EventType)
      (h : ⟪w⟫ ⊨[M] causalDepthFormula n) : n ≤ height w.time := by
    induction n generalizing w with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      obtain ⟨t, ht, hDepth⟩ := (past_iff w (causalDepthFormula n)).mp h
      have hlt := height_lt_of_accessible (t' := t) (t := w) ht
      have hle := ih t hDepth
      omega
  let wEnd : World P S.EventType := ⟨e.place, †, M.history.val⟩
  have hEnd : ⟪wEnd⟫ ⊨[M] Formula.predicate0 liveSymb :=
    (Sat.atEnd M e (Formula.predicate0 liveSymb)).mp
      (Sat.iff_mp M e (hAlways (M.time_le_of_mem he)) hLive)
  have witnesses (n : Nat) : ∃ t ∈ M.history.val,
      (⟪t⟫ ⊨[M] Formula.predicate0 liveSymb) ∧
      (⟪t⟫ ⊨[M] causalDepthFormula n) := by
    induction n with
    | zero => exact ⟨e, he, hLive, Sat.top M e⟩
    | succ n ih =>
      obtain ⟨t, ht, htLive, htDepth⟩ := ih
      have hPast : ⟪wEnd⟫ ⊨[M] ♢ᶠ↓[[]]
          (Formula.predicate0 liveSymb ∧ᶠ causalDepthFormula n) :=
        (past_iff wEnd _).mpr ⟨t, ht, Sat.and_intro M t htLive htDepth⟩
      have hKnow := hKnowledge n e.place
      have hSome : ⟪wEnd⟫ ⊨[M] ↕ᶠ (♢ᶠ↓[[]] (causalDepthFormula n)) :=
        Sat.imp_elim M wEnd
          (Sat.imp_elim M wEnd hKnow
            ((Sat.atEnd M wEnd _).mpr hPast)) hEnd
      obtain ⟨f, hf, hfPlace, hfDepth⟩ := (Sat.sometime M wEnd _).mp hSome
      have hfEnd : ⟪f⟫ ⊨[M] ⤒ᶠ (Formula.predicate0 liveSymb) := by
        apply (Sat.atEnd M f _).mpr
        simpa only [hfPlace] using hEnd
      have hfLive : ⟪f⟫ ⊨[M] Formula.predicate0 liveSymb :=
        Sat.iff_mpr M f (hAlways (M.time_le_of_mem hf)) hfEnd
      exact ⟨f, hf, hfLive, hfDepth⟩
  obtain ⟨t, ht, _, hDepth⟩ := witnesses (height M.history.val)
  have hle := depth_le (height M.history.val) t hDepth
  have hlt := height_lt_of_happensBefore (happensBefore_of_mem ht)
  exact (Nat.not_le_of_lt hlt) hle

/-- The obstruction applies to the repository's current `ThyLive` theory. -/
theorem thyLive_no_live_event
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    {e : World P S.EventType} (he : e ∈ M.history.val) :
    ¬ (⟪e⟫ ⊨[M] Formula.predicate0 liveSymb) := by
  exact no_live_event (thyLive_liveAlways hTheory)
    (fun n => AllWorldValid.at_end M
      (thyLive_knowledgeDiamond hTheory [] (causalDepthFormula n))) he

/-- In particular, the live-witness antecedent used by Liveness 1 is false,
regardless of the formula known at that witness. -/
theorem thyLive_no_live_witness
    (hTheory : M ⊨ᵀ ThyLive liveSymb) (φ : Formula S) :
    ⊨[M] ¬ᶠ (♢ᶠ↓[[]] (Formula.predicate0 liveSymb ∧ᶠ φ)) := by
  classical
  intro p
  apply (Sat.not M ⟨p, †, M.history.val⟩ _).mpr
  intro h
  obtain ⟨q, hq⟩ := (Sat.diamond_nil M ⟨p, †, M.history.val⟩ _).mp h
  obtain ⟨e, he, _, hBody⟩ := (Sat.past M ⟨q, †, M.history.val⟩ _).mp hq
  exact thyLive_no_live_event hTheory he (Sat.and_left M e hBody)

end ModalDistribution.Examples.FiniteHistory
