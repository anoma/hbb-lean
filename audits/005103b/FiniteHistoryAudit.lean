import ModalDistribution.Examples.ThyLive

/-! Historical audit of commit 005103b4. This file uses that commit's
unmodified definitions, including local-model diamonds and event-only validity. -/
namespace ModalDistribution.Examples.InitialCommitAudit
open ModalDistribution.Logic PreHistory History
open scoped Formula PreHistory

variable {S : Signature} [DecidableEq S.VarSymb]
variable {P : Type} [Nonempty P] {M : Model S P}
variable {σ : Assignment S} {liveSymb : S.PredSymb}

def causalDepthFormula : Nat → Formula S
  | 0 => ⊤ᶠ
  | n + 1 => ♢ᶠ↓[[]] (causalDepthFormula n)

/-- The formulas used in the obstruction satisfy the original closure check. -/
theorem causalDepthFormula_closed (n : Nat) :
    (causalDepthFormula (S := S) n).IsClosed := by
  induction n with
  | zero => simp [causalDepthFormula]
  | succ n ih => simpa [causalDepthFormula, Formula.diamondPast] using ih

/-- No live participant has an actual event even under the initial semantics. -/
theorem no_live_event
    (hTheory : M ⊨ᵀ ThyLive liveSymb)
    (H : History P S.EventType) (p : P) (evt : MaybeEvent S.EventType)
    (he : (p, evt, H.val) ∈ M.history.val) :
    ¬ (⟨H,p⟩ ⊨[M,σ] liveFormula liveSymb) := by
  classical
  intro hLive
  have depth_le (n : Nat) (N : Model S P) (K : History P S.EventType) (q : P)
      (h : ⟨K,q⟩ ⊨[N,σ] causalDepthFormula n) : n ≤ height K.val := by
    induction n generalizing N K q with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      simp only [causalDepthFormula, Formula.diamondPast, Sat, Sat.check] at h
      obtain ⟨r, _, J, ⟨ev, hmem⟩, hd⟩ := h
      have hlt := height_lt_of_happensBefore (h := ⟨r, ev, hmem⟩)
      have hle := ih (N.localView K) J r hd
      omega
  have always_at (K : History P S.EventType) (q : P) (ev : MaybeEvent S.EventType)
      (hm : (q, ev, K.val) ∈ M.history.val) :
      ⟨K,q⟩ ⊨[M,σ] (liveFormula liveSymb ⇔ᶠ ⤒ᶠ (liveFormula liveSymb)) := by
    exact hTheory (ax := liveAlwaysAxiom liveSymb) (Or.inl rfl) σ hm
  have hEnd : ⟨M.history,p⟩ ⊨[M,σ] liveFormula liveSymb :=
    (Sat.atEnd M σ H p _).mp
      (Sat.iff_mp M σ H p (always_at H p evt he) hLive)
  have witnesses (n : Nat) : ∃ (K : History P S.EventType) (q : P)
      (ev : MaybeEvent S.EventType), (q, ev, K.val) ∈ M.history.val ∧
      (⟨K,q⟩ ⊨[M,σ] liveFormula liveSymb) ∧
      (⟨K,q⟩ ⊨[M,σ] causalDepthFormula n) := by
    induction n with
    | zero => exact ⟨H, p, evt, he, hLive, Sat.top M σ H p⟩
    | succ n ih =>
      obtain ⟨K, q, ev, hm, hqLive, hqDepth⟩ := ih
      have hAnte : ⟨H,p⟩ ⊨[M,σ] ⤒ᶠ (♢ᶠ↓[[]]
          (liveFormula liveSymb ∧ᶠ causalDepthFormula n)) := by
        rw [Sat.atEnd]
        simp only [Formula.diamondPast, Sat.diamond_nil]
        refine ⟨q, ?_⟩
        rw [Sat]
        refine ⟨K, ⟨ev, hm⟩, ?_⟩
        rw [Model.localView_full]
        exact Sat.and_intro M σ K q hqLive hqDepth
      have hKnow : ⟨H,p⟩ ⊨[M,σ]
          (knowledgeDiamondAxiom liveSymb [] (causalDepthFormula n)
            (causalDepthFormula_closed n)).formula :=
        hTheory (ax := knowledgeDiamondAxiom liveSymb [] (causalDepthFormula n)
          (causalDepthFormula_closed n))
          (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨[], causalDepthFormula n, causalDepthFormula_closed n, rfl⟩)))) σ he
      have hSome : ⟨H,p⟩ ⊨[M,σ] ↕ᶠ (♢ᶠ↓[[]] (causalDepthFormula n)) :=
        Sat.imp_elim M σ H p (Sat.imp_elim M σ H p hKnow hAnte) hLive
      rw [Formula.sometime, Sat.atEnd, Sat] at hSome
      obtain ⟨J, ⟨ev', hmem⟩, hDepth⟩ := hSome
      have hjLive : ⟨J,p⟩ ⊨[M,σ] liveFormula liveSymb :=
        Sat.iff_mpr M σ J p (always_at J p ev' hmem)
          ((Sat.atEnd M σ J p _).mpr hEnd)
      exact ⟨J, p, ev', hmem, hjLive, hDepth⟩
  obtain ⟨K, q, ev, hm, _, hd⟩ := witnesses (height M.history.val)
  have hle := depth_le (height M.history.val) M K q hd
  have hlt := height_lt_of_happensBefore (h := ⟨q, ev, hm⟩)
  exact (Nat.not_le_of_lt hlt) hle

end ModalDistribution.Examples.InitialCommitAudit

/-- info: 'ModalDistribution.Examples.InitialCommitAudit.no_live_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ModalDistribution.Examples.InitialCommitAudit.no_live_event
