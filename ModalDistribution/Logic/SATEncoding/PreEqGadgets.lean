import ModalDistribution.Core.Prehistory
import ModalDistribution.Logic.SATEncoding.TseytinGadgets
import ModalDistribution.Logic.SATEncoding.Types

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

-- Helper: non-Fresh Var cannot be Fresh
omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.nonFresh_ne_Fresh {b : Bounds S} {n : Nat} : ∀ v : Var b,
    (∀ m, v ≠ Var.Fresh m) → v ≠ Var.Fresh n
  | .Mem _ _, _, h => Var.noConfusion h
  | .Level _ _, _, h => Var.noConfusion h
  | .Pred _ _ _, _, h => Var.noConfusion h
  | .MinQ _ _, _, h => Var.noConfusion h
  | .ReachT _, _, h => Var.noConfusion h
  | .Edge _ _, _, h => Var.noConfusion h
  | .Exists _ _ _, _, h => Var.noConfusion h
  | .PreEq _ _, _, h => Var.noConfusion h
  | .Seq _ _, _, h => Var.noConfusion h
  | .Rep _, _, h => Var.noConfusion h
  | .Incomp _ _ _ _, _, h => Var.noConfusion h
  | .Acc _ _ _, _, h => Var.noConfusion h
  | .Fresh m, hNonFresh, _ => hNonFresh m rfl

-- Helper: contradiction from existing-is-Fresh in non-Fresh case
omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.mem_eq_fresh_absurd {b : Bounds S} {t : b.times} {w : WId b} {n : Nat}
    (h : Var.Mem t w = Var.Fresh n) : False := Var.noConfusion h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.level_eq_fresh_absurd {b : Bounds S} {t : b.times} {j : Fin _} {n : Nat}
    (h : Var.Level t j = Var.Fresh n) : False := Var.noConfusion h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.pred_eq_fresh_absurd
    {b : Bounds S} {p : b.participants} {t : b.times} {k : b.predIx} {n : Nat}
    (h : Var.Pred p t k = Var.Fresh n) : False := Var.noConfusion h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.minQ_eq_fresh_absurd {b : Bounds S} {v : b.valIx} {Q : Finset b.participants} {n : Nat}
    (h : Var.MinQ v Q = Var.Fresh n) : False := Var.noConfusion h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.reachT_eq_fresh_absurd {b : Bounds S} {t : b.times} {n : Nat}
    (h : Var.ReachT t = Var.Fresh n) : False := Var.noConfusion h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.edge_eq_fresh_absurd {b : Bounds S} {t t' : b.times} {n : Nat}
    (h : Var.Edge t t' = Var.Fresh n) : False := Var.noConfusion h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.exists_eq_fresh_absurd
    {b : Bounds S} {t : b.times} {p : b.participants} {t' : b.times} {n : Nat}
    (h : Var.Exists t p t' = Var.Fresh n) : False := Var.noConfusion h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.preEq_eq_fresh_absurd {b : Bounds S} {t t' : b.times} {n : Nat}
    (h : Var.PreEq t t' = Var.Fresh n) : False := Var.noConfusion h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.seq_eq_fresh_absurd {b : Bounds S} {t : b.times} {p : b.participants} {n : Nat}
    (h : Var.Seq t p = Var.Fresh n) : False := Var.noConfusion h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.rep_eq_fresh_absurd {b : Bounds S} {v : b.valIx} {n : Nat}
    (h : Var.Rep v = Var.Fresh n) : False := Var.noConfusion h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.incomp_eq_fresh_absurd
    {b : Bounds S} {t : b.times} {p : b.participants} {w w' : WId b} {n : Nat}
    (h : Var.Incomp t p w w' = Var.Fresh n) : False := Var.noConfusion h

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma Var.acc_eq_fresh_absurd {b : Bounds S} {w1 w2 w3 : WId b} {n : Nat}
    (h : Var.Acc w1 w2 w3 = Var.Fresh n) : False := Var.noConfusion h

def sameSig (b : Bounds S) (w w' : WId b) : Bool :=
  if w'.p == w.p then
    match b.decodeMaybeEvent w'.ei, b.decodeMaybeEvent w.ei with
    | MaybeEvent.none, MaybeEvent.none => true
    | MaybeEvent.some e', MaybeEvent.some e => decide (e' = e)
    | _, _ => false
  else
    false

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma sameSig_true_iff
    {b : Bounds S} {w w' : WId b}
    (hSig : sameSig b w w' = true) :
    w'.p = w.p ∧ b.decodeMaybeEvent w'.ei = b.decodeMaybeEvent w.ei := by
  classical
  unfold sameSig at hSig
  split_ifs at hSig with hp
  · have hpEq : w'.p = w.p := of_decide_eq_true hp
    cases hLeft : b.decodeMaybeEvent w'.ei with
    | none =>
        cases hRight : b.decodeMaybeEvent w.ei with
        | none =>
            exact ⟨hpEq, by simp⟩
        | some _ =>
            have : False := by simp [hLeft, hRight] at hSig
            exact this.elim
    | some e' =>
        cases hRight : b.decodeMaybeEvent w.ei with
        | none =>
            have : False := by simp [hLeft, hRight] at hSig
            exact this.elim
        | some e =>
            have hBool : decide (e' = e) = true := by
              simpa [hLeft, hRight] using hSig
            have heq : e' = e := of_decide_eq_true hBool
            exact ⟨hpEq, by simp [heq]⟩

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma sameSig_symm {b : Bounds S} {w w' : WId b}
    (hSig : sameSig b w w' = true) :
    sameSig b w' w = true := by
  classical
  obtain ⟨hp, heq⟩ := sameSig_true_iff (b := b) (w := w) (w' := w') hSig
  unfold sameSig
  cases hVal : b.decodeMaybeEvent w.ei with
  | none =>
      have hVal' : b.decodeMaybeEvent w'.ei = MaybeEvent.none := by
        simp [heq, hVal]
      simp [hp, hVal']
  | some e =>
      have hVal' : b.decodeMaybeEvent w'.ei = MaybeEvent.some e := by
        simp [heq, hVal]
      simp [hp, hVal']

/-! ## Clause Correspondence for Structural Determinism

The key insight for proving structural determinism through nested structures is to
establish a **clause correspondence** between clauses generated at different starting
states. If clauses correspond (same structure, Fresh indices shifted by offset),
then satisfaction transfers trivially through the σ'/σ transformation.

This avoids the "threshold mismatch" problem where nested SD lemmas have different
σ' cutoffs. -/

/-- Two variables correspond under Fresh index shift -/
def varCorresponds {S : Signature} {b : Bounds S}
    (offset : Nat) (v v' : Var b) : Prop :=
  match v, v' with
  | .Fresh n, .Fresh n' => n' = n + offset
  | _, _ => v = v'

/-- Two literals correspond under a Fresh index shift.
    Non-Fresh vars must be identical; Fresh vars differ by exactly offset.
    Polarity must also match. -/
def litCorresponds {S : Signature} {b : Bounds S}
    (offset : Nat) (lit lit' : SAT.Lit (Var b)) : Prop :=
  match lit, lit' with
  | SAT.Lit.pos v, SAT.Lit.pos v' => varCorresponds offset v v'
  | SAT.Lit.neg v, SAT.Lit.neg v' => varCorresponds offset v v'
  | _, _ => False  -- Polarity must match

/-- Two clauses correspond if they have the same length and literals correspond pointwise. -/
def clauseCorresponds {S : Signature} {b : Bounds S}
    (offset : Nat) (c c' : SAT.Clause (Var b)) : Prop :=
  c.length = c'.length ∧
  ∀ i : Nat, ∀ lit lit' : SAT.Lit (Var b),
    c[i]? = some lit → c'[i]? = some lit' → litCorresponds offset lit lit'

/-- Correspondence is reflexive when offset = 0. -/
lemma clauseCorresponds_refl {S : Signature} {b : Bounds S} (c : SAT.Clause (Var b)) :
    clauseCorresponds 0 c c := by
  constructor
  · rfl
  · intro i lit lit' hLit hLit'
    have heq : lit = lit' := Option.some_injective _ (hLit.symm.trans hLit')
    subst heq
    unfold litCorresponds varCorresponds
    cases lit with
    | pos v => cases v <;> simp
    | neg v => cases v <;> simp

/-- When varCorresponds holds and v' is Fresh n', we know v is also Fresh -/
lemma varCorresponds_fresh_right {S : Signature} {b : Bounds S}
    (offset : Nat) (v v' : Var b) (n' : Nat)
    (hCorr : varCorresponds offset v v')
    (hv' : v' = Var.Fresh n') :
    ∃ n, v = Var.Fresh n ∧ n' = n + offset := by
  unfold varCorresponds at hCorr
  subst hv'
  match v with
  | .Fresh n => simp only at hCorr; exact ⟨n, rfl, hCorr⟩
  | .Mem _ _ => simp only at hCorr; exact (Var.noConfusion hCorr)
  | .Level _ _ => simp only at hCorr; exact (Var.noConfusion hCorr)
  | .Pred _ _ _ => simp only at hCorr; exact (Var.noConfusion hCorr)
  | .MinQ _ _ => simp only at hCorr; exact (Var.noConfusion hCorr)
  | .ReachT _ => simp only at hCorr; exact (Var.noConfusion hCorr)
  | .Edge _ _ => simp only at hCorr; exact (Var.noConfusion hCorr)
  | .Exists _ _ _ => simp only at hCorr; exact (Var.noConfusion hCorr)
  | .PreEq _ _ => simp only at hCorr; exact (Var.noConfusion hCorr)
  | .Seq _ _ => simp only at hCorr; exact (Var.noConfusion hCorr)
  | .Rep _ => simp only at hCorr; exact (Var.noConfusion hCorr)
  | .Incomp _ _ _ _ => simp only at hCorr; exact (Var.noConfusion hCorr)
  | .Acc _ _ _ => simp only at hCorr; exact (Var.noConfusion hCorr)

/-- When varCorresponds holds and v' is not Fresh, v = v' -/
lemma varCorresponds_nonFresh_right {S : Signature} {b : Bounds S}
    (offset : Nat) (v v' : Var b)
    (hCorr : varCorresponds offset v v')
    (hNonFresh : ∀ n, v' ≠ Var.Fresh n) :
    v = v' := by
  unfold varCorresponds at hCorr
  match v' with
  | .Fresh n' => exfalso; exact hNonFresh n' rfl
  | .Mem _ _ =>
      match v with
      | .Fresh n => simp only at hCorr; exact (Var.noConfusion hCorr)
      | _ => simp only at hCorr; exact hCorr
  | .Level _ _ =>
      match v with
      | .Fresh n => simp only at hCorr; exact (Var.noConfusion hCorr)
      | _ => simp only at hCorr; exact hCorr
  | .Pred _ _ _ =>
      match v with
      | .Fresh n => simp only at hCorr; exact (Var.noConfusion hCorr)
      | _ => simp only at hCorr; exact hCorr
  | .MinQ _ _ =>
      match v with
      | .Fresh n => simp only at hCorr; exact (Var.noConfusion hCorr)
      | _ => simp only at hCorr; exact hCorr
  | .ReachT _ =>
      match v with
      | .Fresh n => simp only at hCorr; exact (Var.noConfusion hCorr)
      | _ => simp only at hCorr; exact hCorr
  | .Edge _ _ =>
      match v with
      | .Fresh n => simp only at hCorr; exact (Var.noConfusion hCorr)
      | _ => simp only at hCorr; exact hCorr
  | .Exists _ _ _ =>
      match v with
      | .Fresh n => simp only at hCorr; exact (Var.noConfusion hCorr)
      | _ => simp only at hCorr; exact hCorr
  | .PreEq _ _ =>
      match v with
      | .Fresh n => simp only at hCorr; exact (Var.noConfusion hCorr)
      | _ => simp only at hCorr; exact hCorr
  | .Seq _ _ =>
      match v with
      | .Fresh n => simp only at hCorr; exact (Var.noConfusion hCorr)
      | _ => simp only at hCorr; exact hCorr
  | .Rep _ =>
      match v with
      | .Fresh n => simp only at hCorr; exact (Var.noConfusion hCorr)
      | _ => simp only at hCorr; exact hCorr
  | .Incomp _ _ _ _ =>
      match v with
      | .Fresh n => simp only at hCorr; exact (Var.noConfusion hCorr)
      | _ => simp only at hCorr; exact hCorr
  | .Acc _ _ _ =>
      match v with
      | .Fresh n => simp only at hCorr; exact (Var.noConfusion hCorr)
      | _ => simp only at hCorr; exact hCorr

/-- σ' on a non-Fresh variable equals σ -/
lemma σ'_eq_σ_nonFresh {S : Signature} {b : Bounds S}
    (offset threshold : Nat) (σ : SAT.Assignment (Var b)) (v : Var b)
    (hNonFresh : ∀ n, v ≠ Var.Fresh n)
    (σ' : SAT.Assignment (Var b))
    (hσ'Def : σ' = fun x : Var b =>
      match x with
      | Var.Fresh n => if n < threshold then σ x else σ (Var.Fresh (n - offset))
      | _ => σ x) :
    σ' v = σ v := by
  subst hσ'Def
  match v with
  | .Fresh n => exfalso; exact hNonFresh n rfl
  | .Mem _ _ => rfl
  | .Level _ _ => rfl
  | .Pred _ _ _ => rfl
  | .MinQ _ _ => rfl
  | .ReachT _ => rfl
  | .Edge _ _ => rfl
  | .Exists _ _ _ => rfl
  | .PreEq _ _ => rfl
  | .Seq _ _ => rfl
  | .Rep _ => rfl
  | .Incomp _ _ _ _ => rfl
  | .Acc _ _ _ => rfl

/-- Literal evaluation transfer: if lit corresponds to lit' and σ satisfies lit,
    then σ' satisfies lit' (when Fresh vars in lit' are >= threshold) -/
lemma lit_eval_transfer {S : Signature} {b : Bounds S}
    (offset threshold : Nat)
    (lit lit' : SAT.Lit (Var b))
    (hCorr : litCorresponds offset lit lit')
    (σ : SAT.Assignment (Var b))
    (hEval : SAT.Lit.eval σ lit = true) :
    let σ' := fun v : Var b =>
      match v with
      | Var.Fresh n => if n < threshold then σ v else σ (Var.Fresh (n - offset))
      | _ => σ v
    (∀ n, lit'.getVar = Var.Fresh n → n ≥ threshold) →
    SAT.Lit.eval σ' lit' = true := by
  intro σ' hFreshGe
  unfold litCorresponds at hCorr
  match hLit : lit, hLit' : lit' with
  | .pos v, .pos v' =>
      simp only at hCorr
      simp only [SAT.Lit.eval] at hEval ⊢
      by_cases hFresh : ∃ n', v' = Var.Fresh n'
      · obtain ⟨n', hv'Eq⟩ := hFresh
        obtain ⟨n, hvEq, hN'eq⟩ := varCorresponds_fresh_right offset v v' n' hCorr hv'Eq
        have hGe : n' ≥ threshold := hFreshGe n' (by simp [hv'Eq, SAT.Lit.getVar])
        simp only [hv'Eq, σ', Nat.not_lt.mpr hGe, ite_false]
        have hSub : n' - offset = n := by omega
        rw [hSub, ← hvEq]
        exact hEval
      · push_neg at hFresh
        have hVeq := varCorresponds_nonFresh_right offset v v' hCorr hFresh
        have hNonFresh_v : ∀ n, v ≠ Var.Fresh n := by
          intro n hEq; rw [hVeq] at hEq; exact hFresh n hEq
        have hσ'_v : σ' v = σ v := σ'_eq_σ_nonFresh offset threshold σ v hNonFresh_v σ' rfl
        rw [← hVeq, hσ'_v]
        exact hEval
  | .neg v, .neg v' =>
      simp only at hCorr
      simp only [SAT.Lit.eval, Bool.not_eq_true'] at hEval ⊢
      by_cases hFresh : ∃ n', v' = Var.Fresh n'
      · obtain ⟨n', hv'Eq⟩ := hFresh
        obtain ⟨n, hvEq, hN'eq⟩ := varCorresponds_fresh_right offset v v' n' hCorr hv'Eq
        have hGe : n' ≥ threshold := hFreshGe n' (by simp [hv'Eq, SAT.Lit.getVar])
        simp only [hv'Eq, σ', Nat.not_lt.mpr hGe, ite_false]
        have hSub : n' - offset = n := by omega
        rw [hSub, ← hvEq]
        exact hEval
      · push_neg at hFresh
        have hVeq := varCorresponds_nonFresh_right offset v v' hCorr hFresh
        have hNonFresh_v : ∀ n, v ≠ Var.Fresh n := by
          intro n hEq; rw [hVeq] at hEq; exact hFresh n hEq
        have hσ'_v : σ' v = σ v := σ'_eq_σ_nonFresh offset threshold σ v hNonFresh_v σ' rfl
        rw [← hVeq, hσ'_v]
        exact hEval
  | .pos _, .neg _ => simp only at hCorr
  | .neg _, .pos _ => simp only at hCorr

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- If clauses correspond, σ satisfaction transfers to σ' satisfaction.

Key insight: For corresponding literals, σ' evaluates lit' the same as σ evaluates lit:
- Non-Fresh vars: σ' v = σ v by definition
- Fresh vars: lit' has Fresh (n + offset) where n ≥ threshold - offset, so σ' unshifts to σ -/
lemma sd_from_correspondence {S : Signature} {b : Bounds S}
    (offset : Nat) (threshold : Nat)
    (c c' : SAT.Clause (Var b))
    (hCorr : clauseCorresponds offset c c')
    (σ : SAT.Assignment (Var b))
    (hSat : SAT.Clause.eval σ c = true) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => if n < threshold then σ v else σ (Var.Fresh (n - offset))
      | _ => σ v
    -- Condition: Fresh vars in c' have index >= threshold
    (∀ lit ∈ c', ∀ n, lit.getVar = Var.Fresh n → n ≥ threshold) →
    SAT.Clause.eval σ' c' = true := by
  intro σ' hFreshGe
  -- From hSat, there's a lit in c that evaluates to true
  rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSat
  obtain ⟨lit, hMem, hLitEval⟩ := hSat
  -- Find the index of lit in c
  rw [List.mem_iff_getElem?] at hMem
  obtain ⟨i, hGetElem⟩ := hMem
  -- Since clauses have same length, c'[i]? also exists
  have hLenEq := hCorr.1
  have hi : i < c'.length := by
    have hi_c : i < c.length := List.getElem?_eq_some_iff.mp hGetElem |>.1
    omega
  -- Get the corresponding literal lit' in c'
  have hGetElem' : ∃ lit', c'[i]? = some lit' :=
    ⟨c'[i]'hi, List.getElem?_eq_some_iff.mpr ⟨hi, rfl⟩⟩
  obtain ⟨lit', hGetLit'⟩ := hGetElem'
  -- lit and lit' correspond
  have hLitCorr : litCorresponds offset lit lit' := by
    have h := hCorr.2 i lit lit'
    exact h hGetElem hGetLit'
  -- lit' is in c'
  have hMem' : lit' ∈ c' := List.mem_iff_getElem?.mpr ⟨i, hGetLit'⟩
  -- Fresh condition for lit'
  have hFreshGe' : ∀ n, lit'.getVar = Var.Fresh n → n ≥ threshold := hFreshGe lit' hMem'
  -- Apply lit_eval_transfer
  have hLit'Eval := lit_eval_transfer offset threshold lit lit' hLitCorr σ hLitEval hFreshGe'
  -- Conclude via eval_true_of_mem
  exact SAT.Clause.eval_true_of_mem σ' c' lit' hMem' hLit'Eval

/-- Helper: construct correspondence for a two-element clause. -/
lemma clauseCorresponds_pair {S : Signature} {b : Bounds S}
    (offset : Nat) (l1 l1' l2 l2' : SAT.Lit (Var b))
    (h1 : litCorresponds offset l1 l1')
    (h2 : litCorresponds offset l2 l2') :
    clauseCorresponds offset [l1, l2] [l1', l2'] := by
  constructor
  · simp
  · intro i lit lit' hLit hLit'
    cases i with
    | zero => simp at hLit hLit'; subst hLit hLit'; exact h1
    | succ j =>
        cases j with
        | zero => simp at hLit hLit'; subst hLit hLit'; exact h2
        | succ k => simp at hLit

/-- Helper: construct correspondence for a three-element clause. -/
lemma clauseCorresponds_triple {S : Signature} {b : Bounds S}
    (offset : Nat) (l1 l1' l2 l2' l3 l3' : SAT.Lit (Var b))
    (h1 : litCorresponds offset l1 l1')
    (h2 : litCorresponds offset l2 l2')
    (h3 : litCorresponds offset l3 l3') :
    clauseCorresponds offset [l1, l2, l3] [l1', l2', l3'] := by
  constructor
  · simp
  · intro i lit lit' hLit hLit'
    cases i with
    | zero => simp at hLit hLit'; subst hLit hLit'; exact h1
    | succ j =>
        cases j with
        | zero => simp at hLit hLit'; subst hLit hLit'; exact h2
        | succ k =>
            cases k with
            | zero => simp at hLit hLit'; subst hLit hLit'; exact h3
            | succ m => simp at hLit

/-- Literal correspondence for identical non-Fresh literals. -/
lemma litCorresponds_same {S : Signature} {b : Bounds S}
    (offset : Nat) (lit : SAT.Lit (Var b))
    (hNonFresh : ∀ n, lit.getVar ≠ Var.Fresh n) :
    litCorresponds offset lit lit := by
  unfold litCorresponds
  cases hLit : lit with
  | pos v =>
      cases hv : v with
      | Fresh n =>
          exfalso
          have hEq : lit.getVar = Var.Fresh n := by simp [hLit, hv, SAT.Lit.getVar]
          exact hNonFresh n hEq
      | _ => rfl
  | neg v =>
      cases hv : v with
      | Fresh n =>
          exfalso
          have hEq : lit.getVar = Var.Fresh n := by simp [hLit, hv, SAT.Lit.getVar]
          exact hNonFresh n hEq
      | _ => rfl

/-- Literal correspondence for positive Fresh literals with shifted index. -/
lemma litCorresponds_fresh_pos {S : Signature} {b : Bounds S}
    (offset : Nat) (n : Nat) :
    litCorresponds (b := b) offset
      (SAT.Lit.pos (Var.Fresh n)) (SAT.Lit.pos (Var.Fresh (n + offset))) := by
  unfold litCorresponds varCorresponds
  simp

/-- Literal correspondence for negative Fresh literals with shifted index. -/
lemma litCorresponds_fresh_neg {S : Signature} {b : Bounds S}
    (offset : Nat) (n : Nat) :
    litCorresponds (b := b) offset
      (SAT.Lit.neg (Var.Fresh n)) (SAT.Lit.neg (Var.Fresh (n + offset))) := by
  unfold litCorresponds varCorresponds
  simp

/-- y_{w,w'} ↔ (Mem t' w' ∧ PreEq(w.ti, w'.ti)) -/
def mkY (b : Bounds S)
    (t' : b.times) (w w' : WId b) (st : EncState b) : FVar b × EncState b :=
  let (y, st1) := EncState.allocFresh b st
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w'.ti)]
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (Var.Mem t' w'), SAT.Lit.neg (Var.PreEq w.ti w'.ti),
     SAT.Lit.pos (FVar.toVar b y)]
  (y, st1)

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkY_clauses_subset (b : Bounds S)
    (t' : b.times) (w w' : WId b) (st : EncState b) :
    st.clauses ⊆ (mkY b t' w w' st).2.clauses := by
  classical
  unfold mkY
  cases hAlloc : EncState.allocFresh b st with
  | mk y st1 =>
      intro clause hClause
      have hAllocSub : clause ∈ st1.clauses := by
        have hEq :
            st1.clauses = st.clauses := by
          simpa [hAlloc] using
            (EncState.allocFresh_clauses_eq (b := b) (st := st))
        simpa [hEq] using hClause
      have h₁ :
          clause ∈
            (EncState.addClause b st1
              [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')]).clauses :=
        (EncState.addClause_subset_clauses
          (b := b)
          (st := st1)
          (clause :=
            [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')])) hAllocSub
      have h₂ :
          clause ∈
            (EncState.addClause b
              (EncState.addClause b st1
                [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')])
              [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w'.ti)]).clauses :=
        (EncState.addClause_subset_clauses
          (b := b)
          (st := EncState.addClause b st1
            [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')])
          (clause :=
            [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w'.ti)])) h₁
      have h₃ :
          clause ∈
            (EncState.addClause b
              (EncState.addClause b
                (EncState.addClause b st1
                  [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')])
                [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w'.ti)])
              [SAT.Lit.neg (Var.Mem t' w'), SAT.Lit.neg (Var.PreEq w.ti w'.ti),
               SAT.Lit.pos (FVar.toVar b y)]).clauses :=
        (EncState.addClause_subset_clauses
          (b := b)
          (st := EncState.addClause b
            (EncState.addClause b st1
              [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')])
            [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w'.ti)])
          (clause :=
            [SAT.Lit.neg (Var.Mem t' w'), SAT.Lit.neg (Var.PreEq w.ti w'.ti),
             SAT.Lit.pos (FVar.toVar b y)])) h₂
      simpa using h₃

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Weak adequacy for `mkY`: only requires new clauses to be true. -/
lemma mkY_adequate_forward_weak (b : Bounds S) (σ : SAT.Assignment (Var b))
    (t' : b.times) (w w' : WId b) (st : EncState b)
    (hClauses : ((mkY b t' w w' st).2.clauses.take
      ((mkY b t' w w' st).2.clauses.length - st.clauses.length)).all
      (SAT.Clause.eval σ) = true)
    (hY : σ (FVar.toVar b (mkY b t' w w' st).1) = true) :
    σ (Var.Mem t' w') = true ∧ σ (Var.PreEq w.ti w'.ti) = true := by
  classical
  unfold mkY at hClauses hY
  cases hAlloc : EncState.allocFresh b st with
  | mk y st1 =>
      simp [hAlloc] at hY
      -- The new clauses are exactly the 3 added clauses.
      -- We know they are true.
      -- The clauses are added to the front.
      -- The order is: [c3, c2, c1] ++ st.clauses
      -- take 3 gives [c3, c2, c1]
      -- c1 = [¬y, Mem]
      -- c2 = [¬y, PreEq]
      -- c3 = [¬Mem, ¬PreEq, y]
      -- We need c1 and c2.
      -- They are at indices 2 and 1 (or 1 and 2 depending on order).
      -- EncState.addClause adds to head.
      -- st1 has st.clauses
      -- st2 has c1 :: st.clauses
      -- st3 has c2 :: c1 :: st.clauses
      -- st4 has c3 :: c2 :: c1 :: st.clauses
      -- So take 3 is [c3, c2, c1].
      -- c1 is at index 2. c2 is at index 1.
      have hAllTrue :
        ((mkY b t' w w' st).2.clauses.take
          ((mkY b t' w w' st).2.clauses.length - st.clauses.length)).all
          (SAT.Clause.eval σ) = true := hClauses
      have hEqClauses : st1.clauses = st.clauses := by
        have := EncState.allocFresh_clauses_eq (b := b) (st := st)
        rw [hAlloc] at this
        exact this
      have hLen : (mkY b t' w w' st).2.clauses.length - st.clauses.length = 3 := by
        simp only [mkY, hAlloc, EncState.addClause, hEqClauses, List.length_cons]
        omega
      rw [hLen] at hAllTrue
      -- The 3 new clauses are [c3, c2, c1] where c1 is at index 2, c2 at index 1
      have hClauses3 : (mkY b t' w w' st).2.clauses =
          [SAT.Lit.neg (Var.Mem t' w'), SAT.Lit.neg (Var.PreEq w.ti w'.ti),
           SAT.Lit.pos (FVar.toVar b y)] ::
          [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w'.ti)] ::
          [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')] ::
          st.clauses := by
        simp only [mkY, hAlloc, EncState.addClause, hEqClauses]
      -- Extract clause at index 2
      have hC1 : SAT.Clause.eval σ
          [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')] = true := by
        have hTake3 : List.take 3 (mkY b t' w w' st).2.clauses =
            [[SAT.Lit.neg (Var.Mem t' w'), SAT.Lit.neg (Var.PreEq w.ti w'.ti),
              SAT.Lit.pos (FVar.toVar b y)],
             [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w'.ti)],
             [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')]] := by
          rw [hClauses3]
          rfl
        have h := List.get_of_all_true hAllTrue 2 (by simp [hTake3])
        convert h
        simp [hTake3]
      -- Extract clause at index 1
      have hC2 : SAT.Clause.eval σ
          [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w'.ti)] = true := by
        have hTake3 : List.take 3 (mkY b t' w w' st).2.clauses =
            [[SAT.Lit.neg (Var.Mem t' w'), SAT.Lit.neg (Var.PreEq w.ti w'.ti),
              SAT.Lit.pos (FVar.toVar b y)],
             [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w'.ti)],
             [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')]] := by
          rw [hClauses3]
          rfl
        have h := List.get_of_all_true hAllTrue 1 (by simp [hTake3])
        convert h
        simp [hTake3]
      -- Use hY to simplify
      simp [SAT.Clause.eval, SAT.Lit.eval, List.foldl, hY, Bool.not_true, Bool.false_or] at hC1 hC2
      exact ⟨hC1, hC2⟩

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Adequacy for `mkY`: if the witness variable is true, then both conjuncts hold. -/
lemma mkY_adequate_forward (b : Bounds S) (σ : SAT.Assignment (Var b))
    (t' : b.times) (w w' : WId b) (st : EncState b)
    (hClauses : (mkY b t' w w' st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hY : σ (FVar.toVar b (mkY b t' w w' st).1) = true) :
    σ (Var.Mem t' w') = true ∧ σ (Var.PreEq w.ti w'.ti) = true := by
  apply mkY_adequate_forward_weak b σ t' w w' st _ hY
  -- Show that if all clauses are true, then the subset is true.
  have hSubset :
    (mkY b t' w w' st).2.clauses.take
      ((mkY b t' w w' st).2.clauses.length - st.clauses.length)
      ⊆ (mkY b t' w w' st).2.clauses :=
    List.take_subset _ _
  exact all_true_of_subset hSubset hClauses

/-- d_w ↔ ⋁_{sameSig} y_{w,w'} ; empty set ⇒ force ¬d_w -/
def mkDw (b : Bounds S)
    (t' : b.times) (w : WId b) (st : EncState b) : FVar b × EncState b :=
  let cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  match cands with
  | [] =>
      let (d, st1) := EncState.allocFresh b st
      let st1 := EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b d)]
      (d, st1)
  | _ =>
      let (ys, st1) := cands.foldl
        (fun (acc : List (Var b) × EncState b) w' =>
          let (vs, st') := acc
          let (y, st'') := mkY b t' w w' st'
          (FVar.toVar b y :: vs, st''))
        ([], st)
      mkBigOrIff b ys st1

/-- o_w ↔ (¬Mem t w ∨ d_w) -/
def mkOw (b : Bounds S)
    (t : b.times) (w : WId b) (d : FVar b) (st : EncState b) : FVar b × EncState b :=
  let (o, st1) := EncState.allocFresh b st
  let st1 := EncState.addClause b st1
    [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w), SAT.Lit.pos (FVar.toVar b d)]
  let st1 := EncState.addClause b st1
    [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)]
  let st1 := EncState.addClause b st1
    [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.neg (FVar.toVar b d)]
  (o, st1)

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkOw_clauses_subset (b : Bounds S)
    (t : b.times) (w : WId b) (d : FVar b) (st : EncState b) :
    st.clauses ⊆ (mkOw b t w d st).2.clauses := by
  classical
  unfold mkOw
  cases hAlloc : EncState.allocFresh b st with
  | mk o st1 =>
      intro clause hClause
      have hAllocEq :
          st1.clauses = st.clauses := by
        simpa [hAlloc] using
          (EncState.allocFresh_clauses_eq (b := b) (st := st))
      have hClause₀ : clause ∈ st1.clauses := by
        simpa [hAllocEq] using hClause
      have h₁ :
          clause ∈
            (EncState.addClause b st1
              [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w),
               SAT.Lit.pos (FVar.toVar b d)]).clauses :=
        (EncState.addClause_subset_clauses
          (b := b)
          (st := st1)
          (clause :=
            [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w),
              SAT.Lit.pos (FVar.toVar b d)])) hClause₀
      have h₂ :
          clause ∈
            (EncState.addClause b
              (EncState.addClause b st1
                [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w),
                  SAT.Lit.pos (FVar.toVar b d)])
              [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)]).clauses :=
        (EncState.addClause_subset_clauses
          (b := b)
          (st := EncState.addClause b st1
            [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w),
              SAT.Lit.pos (FVar.toVar b d)])
          (clause :=
            [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)])) h₁
      have h₃ :
          clause ∈
            (EncState.addClause b
              (EncState.addClause b
                (EncState.addClause b st1
                  [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w),
                    SAT.Lit.pos (FVar.toVar b d)])
                [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)])
              [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.neg (FVar.toVar b d)]).clauses :=
        (EncState.addClause_subset_clauses
          (b := b)
          (st := EncState.addClause b
            (EncState.addClause b st1
              [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w),
                SAT.Lit.pos (FVar.toVar b d)])
            [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)])
          (clause :=
            [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.neg (FVar.toVar b d)])) h₂
      simpa [hAlloc]
        using h₃

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Weak adequacy for `mkOw`: only requires new clauses to be true. -/
lemma mkOw_adequate_forward_weak (b : Bounds S) (σ : SAT.Assignment (Var b))
    (t : b.times) (w : WId b) (d : FVar b) (st : EncState b)
    (hClauses : ((mkOw b t w d st).2.clauses.take
      ((mkOw b t w d st).2.clauses.length - st.clauses.length)).all
      (SAT.Clause.eval σ) = true)
    (hOw : σ (FVar.toVar b (mkOw b t w d st).1) = true)
    (hMem : σ (Var.Mem t w) = true) :
    σ (FVar.toVar b d) = true := by
  classical
  -- Establish length before unfolding
  have hLen0 : (mkOw b t w d st).2.clauses.length - st.clauses.length = 3 := by
    unfold mkOw
    cases hAlloc : EncState.allocFresh b st with
    | mk o st1 =>
        have hEqClauses : st1.clauses = st.clauses := by
          have := EncState.allocFresh_clauses_eq (b := b) (st := st)
          rw [hAlloc] at this
          exact this
        simp only [EncState.addClause, hEqClauses, List.length_cons]
        omega
  rw [hLen0] at hClauses
  unfold mkOw at hOw
  cases hAlloc : EncState.allocFresh b st with
  | mk o st1 =>
      have hEqClauses : st1.clauses = st.clauses := by
        have := EncState.allocFresh_clauses_eq (b := b) (st := st)
        rw [hAlloc] at this
        exact this
      simp [hAlloc] at hOw
      -- The 3 new clauses are [c3, c2, c1] where c1 is at index 2
      have hClauses3 : (mkOw b t w d st).2.clauses =
          [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.neg (FVar.toVar b d)] ::
          [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)] ::
          [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w),
           SAT.Lit.pos (FVar.toVar b d)] ::
          st.clauses := by
        simp only [mkOw, hAlloc, EncState.addClause, hEqClauses]
      -- Extract clause at index 2: [¬o, ¬Mem, d]
      have hC1 : SAT.Clause.eval σ
          [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w),
           SAT.Lit.pos (FVar.toVar b d)] = true := by
        have hTake3 : List.take 3 (mkOw b t w d st).2.clauses =
            [[SAT.Lit.pos (FVar.toVar b o), SAT.Lit.neg (FVar.toVar b d)],
             [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)],
             [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w),
              SAT.Lit.pos (FVar.toVar b d)]] := by
          rw [hClauses3]
          rfl
        have h := List.get_of_all_true hClauses 2 (by simp [hTake3])
        convert h
        simp [hTake3]
      simp [SAT.Clause.eval, SAT.Lit.eval, List.foldl, hOw, hMem,
            Bool.not_true, Bool.false_or] at hC1
      exact hC1

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Adequacy for `mkOw`: if the obligation variable is true while `Mem` holds, then
    the witness disjunction `d` must also be true. -/
lemma mkOw_adequate_forward (b : Bounds S) (σ : SAT.Assignment (Var b))
    (t : b.times) (w : WId b) (d : FVar b) (st : EncState b)
    (hClauses : (mkOw b t w d st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hOw : σ (FVar.toVar b (mkOw b t w d st).1) = true)
    (hMem : σ (Var.Mem t w) = true) :
    σ (FVar.toVar b d) = true := by
  apply mkOw_adequate_forward_weak b σ t w d st _ hOw hMem
  have hSubset :
    (mkOw b t w d st).2.clauses.take ((mkOw b t w d st).2.clauses.length - st.clauses.length)
      ⊆ (mkOw b t w d st).2.clauses :=
    List.take_subset _ _
  exact all_true_of_subset hSubset hClauses

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Extract the final accumulator value from addPreEqExpose clauses.

    addPreEqExpose ties Var.PreEq ti ti' to the final accumulator variable `last`
    via bi-conditional clauses:
    - [¬PreEq(ti, ti'), last]: if PreEq then last
    - [¬last, PreEq(ti, ti')]: if last then PreEq -/
lemma addPreEqExpose_extract
    (b : Bounds S) (ti ti' : b.times) (last : FVar b) (st : EncState b)
    (σ : SAT.Assignment (Var b))
    (hClauses : (addPreEqExpose b ti ti' last st).clauses.all (SAT.Clause.eval σ) = true)
    (hPreEq : σ (Var.PreEq ti ti') = true) :
    σ (FVar.toVar b last) = true := by
  classical
  unfold addPreEqExpose at hClauses
  let clause₁ :=
    [ SAT.Lit.neg (Var.PreEq ti ti')
    , SAT.Lit.pos (FVar.toVar b last) ]
  have hAll := List.all_eq_true.mp hClauses
  have hMem : clause₁ ∈
      (EncState.addClause b
        (EncState.addClause b st clause₁)
        [SAT.Lit.neg (FVar.toVar b last), SAT.Lit.pos (Var.PreEq ti ti')]).clauses := by
    simp [clause₁, EncState.addClause]
  have hClause := hAll clause₁ hMem
  simp [clause₁, SAT.Clause.eval, SAT.Lit.eval, List.foldl,
        hPreEq, Bool.not_true, Bool.false_or] at hClause
  exact hClause

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
lemma mkY_clauses_length_le (b : Bounds S) (t' : b.times) (w w' : WId b) (st : EncState b) :
    st.clauses.length ≤ (mkY b t' w w' st).2.clauses.length := by
  unfold mkY
  simp only
  have h1 := EncState.allocFresh_length_le b st
  have h2 := EncState.addClause_length_le b (EncState.allocFresh b st).2
    [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1), SAT.Lit.pos (Var.Mem t' w')]
  have h3 := EncState.addClause_length_le b
    (EncState.addClause b (EncState.allocFresh b st).2
      [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1), SAT.Lit.pos (Var.Mem t' w')])
    [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1), SAT.Lit.pos (Var.PreEq w.ti w'.ti)]
  have h4 := EncState.addClause_length_le b
    (EncState.addClause b
      (EncState.addClause b (EncState.allocFresh b st).2
        [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1), SAT.Lit.pos (Var.Mem t' w')])
      [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1), SAT.Lit.pos (Var.PreEq w.ti w'.ti)])
    [SAT.Lit.neg (Var.Mem t' w'), SAT.Lit.neg (Var.PreEq w.ti w'.ti),
     SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)]
  apply Nat.le_trans h1
  apply Nat.le_trans h2
  apply Nat.le_trans h3
  exact h4

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
lemma mkBigOrIff_clauses_length_le (b : Bounds S) (vs : List (Var b)) (st : EncState b) :
    st.clauses.length ≤ (mkBigOrIff b vs st).2.clauses.length := by
  unfold mkBigOrIff
  simp only
  have h1 := EncState.allocFresh_length_le b st
  have hFold : ∀ stInit, stInit.clauses.length ≤
      (vs.foldl (fun stCur v =>
        EncState.addClause b stCur
          [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)])
        stInit).clauses.length := by
    intro stInit
    induction vs generalizing stInit with
    | nil => simp
    | cons v vs ih =>
      simp
      have hStep := EncState.addClause_length_le b stInit
        [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)]
      exact Nat.le_trans hStep (ih _)
  have h2 := hFold (EncState.allocFresh b st).2
  have h3 := EncState.addClause_length_le b
    (vs.foldl (fun stCur v =>
      EncState.addClause b stCur
        [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1)])
      (EncState.allocFresh b st).2)
    (SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1) :: vs.map SAT.Lit.pos)
  apply Nat.le_trans h1
  apply Nat.le_trans h2
  exact h3

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
lemma foldl_snd_length_le {α β} (b : Bounds S) {f : β × EncState b → α → β × EncState b}
    (hStep : ∀ acc x, acc.2.clauses.length ≤ (f acc x).2.clauses.length)
    (xs : List α) (init : β × EncState b) :
    init.2.clauses.length ≤ (xs.foldl f init).2.clauses.length := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp
    apply Nat.le_trans (hStep init x) (ih (f init x))

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma mkDw_clauses_length_le (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b) :
    st.clauses.length ≤ (mkDw b t' w st).2.clauses.length := by
  unfold mkDw
  by_cases h : ((WId.allWorlds b).filter (fun w' => sameSig b w w')) = []
  · -- Empty case
    simp [h]
    have h1 := EncState.allocFresh_length_le b st
    have h2 := EncState.addClause_length_le b (EncState.allocFresh b st).2
      [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1)]
    exact Nat.le_trans h1 h2
  · -- Non-empty case
    simp
    have hFold : ∀ (stInit : EncState b), stInit.clauses.length ≤
        (((WId.allWorlds b).filter (fun w' => sameSig b w w')).foldl
          (fun (acc : List (Var b) × EncState b) w' =>
            let (vs, st') := acc
            let (y, st'') := mkY b t' w w' st'
            (FVar.toVar b y :: vs, st''))
          ([], stInit)).2.clauses.length := by
      intro stInit
      let f := fun (acc : List (Var b) × EncState b) w' =>
            let (vs, st') := acc
            let (y, st'') := mkY b t' w w' st'
            (FVar.toVar b y :: vs, st'')
      have hStep : ∀ acc w', acc.2.clauses.length ≤ (f acc w').2.clauses.length := by
        intro acc w'
        rcases acc with ⟨vs, st'⟩
        simp [f]
        exact mkY_clauses_length_le b t' w w' st'
      exact foldl_snd_length_le b hStep _ ([], stInit)
    have h1 := hFold st
    have h2 := mkBigOrIff_clauses_length_le b
      (((WId.allWorlds b).filter (fun w' => sameSig b w w')).foldl
        (fun (acc : List (Var b) × EncState b) w' =>
          let (vs, st') := acc
          let (y, st'') := mkY b t' w w' st'
          (FVar.toVar b y :: vs, st''))
        ([], st)).1
      (((WId.allWorlds b).filter (fun w' => sameSig b w w')).foldl
        (fun (acc : List (Var b) × EncState b) w' =>
          let (vs, st') := acc
          let (y, st'') := mkY b t' w w' st'
          (FVar.toVar b y :: vs, st''))
        ([], st)).2
    exact Nat.le_trans h1 h2

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] [DecidableEq S.EventType] in
lemma mkOw_clauses_length_le
    (b : Bounds S) (t : b.times) (w : WId b) (d : FVar b) (st : EncState b) :
    st.clauses.length ≤ (mkOw b t w d st).2.clauses.length := by
  unfold mkOw
  simp only
  have h1 := EncState.allocFresh_length_le b st
  have h2 := EncState.addClause_length_le b (EncState.allocFresh b st).2
    [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
     SAT.Lit.neg (Var.Mem t w), SAT.Lit.pos (FVar.toVar b d)]
  have h3 := EncState.addClause_length_le b
    (EncState.addClause b (EncState.allocFresh b st).2
      [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
       SAT.Lit.neg (Var.Mem t w), SAT.Lit.pos (FVar.toVar b d)])
    [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1), SAT.Lit.pos (Var.Mem t w)]
  have h4 := EncState.addClause_length_le b
    (EncState.addClause b
      (EncState.addClause b (EncState.allocFresh b st).2
        [SAT.Lit.neg (FVar.toVar b (EncState.allocFresh b st).1),
         SAT.Lit.neg (Var.Mem t w), SAT.Lit.pos (FVar.toVar b d)])
      [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1), SAT.Lit.pos (Var.Mem t w)])
    [SAT.Lit.pos (FVar.toVar b (EncState.allocFresh b st).1), SAT.Lit.neg (FVar.toVar b d)]
  apply Nat.le_trans h1
  apply Nat.le_trans h2
  apply Nat.le_trans h3
  exact h4


omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkY_clauses_eq_append (b : Bounds S)
    (t' : b.times) (w w' : WId b) (st : EncState b) :
    (mkY b t' w w' st).2.clauses =
      [ [SAT.Lit.neg (Var.Mem t' w'), SAT.Lit.neg (Var.PreEq w.ti w'.ti),
          SAT.Lit.pos (FVar.toVar b (mkY b t' w w' st).1)]
      , [SAT.Lit.neg (FVar.toVar b (mkY b t' w w' st).1),
          SAT.Lit.pos (Var.PreEq w.ti w'.ti)]
      , [SAT.Lit.neg (FVar.toVar b (mkY b t' w w' st).1),
          SAT.Lit.pos (Var.Mem t' w')] ] ++ st.clauses := by
  classical
  unfold mkY
  cases hAlloc : EncState.allocFresh b st with
  | mk y st1 =>
      have hClauses : st1.clauses = st.clauses := by
        simpa [hAlloc] using EncState.allocFresh_clauses_eq (b := b) (st := st)
      simp [hClauses, EncState.addClause, List.cons_append]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkOw_clauses_eq_append (b : Bounds S)
    (t : b.times) (w : WId b) (d : FVar b) (st : EncState b) :
    (mkOw b t w d st).2.clauses =
      [ [SAT.Lit.pos (FVar.toVar b (mkOw b t w d st).1),
          SAT.Lit.neg (FVar.toVar b d)]
      , [SAT.Lit.pos (FVar.toVar b (mkOw b t w d st).1),
          SAT.Lit.pos (Var.Mem t w)]
      , [SAT.Lit.neg (FVar.toVar b (mkOw b t w d st).1),
          SAT.Lit.neg (Var.Mem t w), SAT.Lit.pos (FVar.toVar b d)] ] ++ st.clauses := by
  classical
  unfold mkOw
  cases hAlloc : EncState.allocFresh b st with
  | mk o st1 =>
      have hClauses : st1.clauses = st.clauses := by
        simpa [hAlloc] using EncState.allocFresh_clauses_eq (b := b) (st := st)
      simp [hClauses, EncState.addClause, List.cons_append]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Variables in new mkBigOrIff clauses are either the control var u or from the input list vs. -/
lemma mkBigOrIff_newClause_vars (b : Bounds S) (vs : List (Var b)) (st : EncState b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (mkBigOrIff b vs st).2.clauses)
    (hNotInSt : clause ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ clause) :
    lit.getVar = FVar.toVar b (mkBigOrIff b vs st).1 ∨ lit.getVar ∈ vs := by
  classical
  unfold mkBigOrIff at hClause
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      have hUEq : (mkBigOrIff b vs st).1 = u := by unfold mkBigOrIff; simp only [hAlloc]
      have hSt1Clauses : st1.clauses = st.clauses := by
        simpa [hAlloc] using EncState.allocFresh_clauses_eq (b := b) (st := st)
      simp only [hAlloc] at hClause
      -- The clauses are: long clause :: (fold of short clauses)
      let foldStep := fun stCur v =>
        EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]
      -- First, handle the long clause at the head
      simp only [EncState.addClause, List.mem_cons] at hClause
      rcases hClause with hLong | hInFold
      · -- clause is the long clause: [¬u, v1+, ..., vn+]
        subst hLong
        simp only [List.mem_cons, List.mem_map] at hLit
        rcases hLit with hNegU | ⟨vi, hViMem, hLitEq⟩
        · left; subst hNegU; simp only [SAT.Lit.getVar, hUEq]
        · right; subst hLitEq; simp only [SAT.Lit.getVar]; exact hViMem
      · -- clause is in the fold of short clauses
        -- Each short clause is [¬vi, u+] for some vi ∈ vs
        -- Key: if clause ∈ fold and clause ∉ stInit, then clause = [¬vi, u+] for some vi
        have hFoldStructure : ∀ (vsList : List (Var b)) (stInit : EncState b),
            clause ∈ (vsList.foldl foldStep stInit).clauses →
            clause ∉ stInit.clauses →
            ∃ vi ∈ vsList, clause = [SAT.Lit.neg vi, SAT.Lit.pos (FVar.toVar b u)] := by
          intro vsList
          induction vsList with
          | nil =>
              intro stInit hIn hNotIn
              simp only [List.foldl_nil] at hIn
              exact absurd hIn hNotIn
          | cons v vs' ih =>
              intro stInit hIn hNotIn
              simp only [List.foldl_cons, foldStep] at hIn
              -- Check if clause is the new clause at this step or from later
              have hAddClause : (foldStep stInit v).clauses =
                  [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)] :: stInit.clauses := rfl
              -- Use monotonicity: clauses only grow
              have hMono : ∀ (vsList' : List (Var b)) (st' : EncState b),
                  st'.clauses ⊆ (vsList'.foldl foldStep st').clauses := by
                intro vsList'
                induction vsList' with
                | nil => intro st'; simp [foldStep]
                | cons v' vs'' ih' =>
                    intro st'
                    simp only [List.foldl_cons]
                    intro c hc
                    have hInStep : c ∈ (foldStep st' v').clauses := by
                      simp only [foldStep, EncState.addClause, List.mem_cons]
                      right; exact hc
                    exact ih' (foldStep st' v') hInStep
              by_cases hInStep : clause ∈ (foldStep stInit v).clauses
              · simp only [foldStep, EncState.addClause, List.mem_cons] at hInStep
                rcases hInStep with hNew | hOld
                · exact ⟨v, List.mem_cons_self, hNew⟩
                · exact absurd hOld hNotIn
              · -- clause ∉ (foldStep stInit v).clauses but clause ∈ fold result
                -- This means it was added by the fold of vs', so use IH
                rcases ih (foldStep stInit v) hIn hInStep with ⟨vi, hViMem, hClauseEq⟩
                exact ⟨vi, List.mem_cons_of_mem _ hViMem, hClauseEq⟩
        have hNotInSt1 : clause ∉ st1.clauses := by rw [hSt1Clauses]; exact hNotInSt
        rcases hFoldStructure vs st1 hInFold hNotInSt1 with ⟨vi, hViMem, hClauseEq⟩
        subst hClauseEq
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
        rcases hLit with hNegVi | hPosU
        · right; subst hNegVi; simp only [SAT.Lit.getVar]; exact hViMem
        · left; subst hPosU; simp only [SAT.Lit.getVar, hUEq]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Every new clause from mkBigOrIff contains the control variable u.
    - Long clause: `[¬u, v1, v2, ...]` - contains ¬u
    - Short clauses: `[¬vi, u]` - contains u -/
lemma mkBigOrIff_newClause_contains_control_var (b : Bounds S) (vs : List (Var b)) (st : EncState b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (mkBigOrIff b vs st).2.clauses)
    (hNotInSt : clause ∉ st.clauses) :
    ∃ lit ∈ clause, lit.getVar = FVar.toVar b (mkBigOrIff b vs st).1 := by
  classical
  unfold mkBigOrIff at hClause ⊢
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      have hClauses : st1.clauses = st.clauses := by
        simpa [hAlloc] using EncState.allocFresh_clauses_eq (b := b) (st := st)
      simp only [hAlloc] at hClause ⊢
      simp only [EncState.addClause, List.mem_cons] at hClause
      rcases hClause with hLong | hInFold
      · -- clause is the long clause: [¬u, v1, v2, ...]
        subst hLong
        exact ⟨SAT.Lit.neg (FVar.toVar b u), List.Mem.head _, by simp [SAT.Lit.getVar]⟩
      · -- clause is in the fold: each short clause is [¬vi, u]
        let foldStep := fun stCur v =>
          EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]
        -- Characterize clauses in foldl result
        have hFoldChar : ∀ (vsList : List (Var b)) (stInit : EncState b),
            clause ∈ (vsList.foldl foldStep stInit).clauses →
            clause ∉ stInit.clauses →
            ∃ v ∈ vsList, clause = [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)] := by
          intro vsList
          induction vsList with
          | nil =>
              intro stInit hIn hNotIn
              simp only [List.foldl_nil] at hIn
              exact absurd hIn hNotIn
          | cons v vs' ih =>
              intro stInit hIn hNotIn
              simp only [List.foldl_cons, foldStep] at hIn
              by_cases hInStep : clause ∈ (foldStep stInit v).clauses
              · simp only [foldStep, EncState.addClause, List.mem_cons] at hInStep
                rcases hInStep with hNew | hOld
                · exact ⟨v, List.Mem.head _, hNew⟩
                · exact absurd hOld hNotIn
              · rcases ih (foldStep stInit v) hIn hInStep with ⟨v', hv', hEq⟩
                exact ⟨v', List.Mem.tail _ hv', hEq⟩
        have hNotInSt1 : clause ∉ st1.clauses := by rw [hClauses]; exact hNotInSt
        rcases hFoldChar vs st1 hInFold hNotInSt1 with ⟨_, _, hEq⟩
        subst hEq
        exact ⟨SAT.Lit.pos (FVar.toVar b u), by simp, by simp [SAT.Lit.getVar]⟩

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkBigOrIff_clauses_eq_append (b : Bounds S) (vs : List (Var b)) (st : EncState b) :
    ∃ newClauses, (mkBigOrIff b vs st).2.clauses = newClauses ++ st.clauses := by
  classical
  unfold mkBigOrIff
  cases hAlloc : EncState.allocFresh b st with
  | mk u st1 =>
      have hClauses : st1.clauses = st.clauses := by
        simpa [hAlloc] using EncState.allocFresh_clauses_eq (b := b) (st := st)
      let step := fun stCur v =>
            EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]
      have hFold :
          ∀ stInit, ∃ newFold,
            (vs.foldl step stInit).clauses = newFold ++ stInit.clauses := by
        intro stInit
        induction vs generalizing stInit with
        | nil =>
            exact ⟨[], by simp⟩
        | cons v vs ih =>
            dsimp [List.foldl]
            rcases ih (step stInit v) with ⟨newFold, hFold⟩
            refine ⟨newFold ++ [[SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]], ?_⟩
            rw [hFold]
            simp only [step, EncState.addClause]
            simp only [List.append_assoc, List.singleton_append]
      rcases hFold st1 with ⟨newFold, hFoldEq⟩
      refine ⟨(SAT.Lit.neg (FVar.toVar b u) :: vs.map SAT.Lit.pos) :: newFold, ?_⟩
      simp only [EncState.addClause]
      calc (SAT.Lit.neg (FVar.toVar b u) :: vs.map SAT.Lit.pos) ::
              (vs.foldl step st1).clauses
          = (SAT.Lit.neg (FVar.toVar b u) :: vs.map SAT.Lit.pos) ::
              (newFold ++ st1.clauses) := by rw [hFoldEq]
        _ = (SAT.Lit.neg (FVar.toVar b u) :: vs.map SAT.Lit.pos) ::
              (newFold ++ st.clauses) := by rw [hClauses]
        _ = (SAT.Lit.neg (FVar.toVar b u) :: vs.map SAT.Lit.pos) ::
              newFold ++ st.clauses := by rfl

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma mkDw_clauses_eq_append (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b) :
    ∃ newClauses, (mkDw b t' w st).2.clauses = newClauses ++ st.clauses := by
  classical
  unfold mkDw
  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  by_cases hEmpty : cands = []
  · simp [cands, hEmpty]
    cases hAlloc : EncState.allocFresh b st with
    | mk d st1 =>
        have hClauses : st1.clauses = st.clauses := by
          simpa [hAlloc] using EncState.allocFresh_clauses_eq (b := b) (st := st)
        refine ⟨[[SAT.Lit.neg (FVar.toVar b d)]], ?_⟩
        simp [hClauses, EncState.addClause]
  · simp [cands]
    let step := fun (acc : List (Var b) × EncState b) w' =>
          let (vs, st') := acc
          let (y, st'') := mkY b t' w w' st'
          (FVar.toVar b y :: vs, st'')
    have hStep :
        ∀ acc w', ∃ newStep,
          (step acc w').2.clauses = newStep ++ acc.2.clauses := by
      intro acc w'
      rcases acc with ⟨vs, stAcc⟩
      dsimp [step]
      generalize hMkY : mkY b t' w w' stAcc = res
      obtain ⟨y, stY⟩ := res
      refine ⟨[[SAT.Lit.neg (Var.Mem t' w'), SAT.Lit.neg (Var.PreEq w.ti w'.ti),
                 SAT.Lit.pos (FVar.toVar b y)],
               [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w'.ti)],
               [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')]], ?_⟩
      have := mkY_clauses_eq_append (b := b) (t' := t') (w := w) (w' := w') (st := stAcc)
      rw [hMkY] at this
      simpa using this
    have hFold :
        ∀ acc, ∃ newFold,
          (cands.foldl step acc).2.clauses = newFold ++ acc.2.clauses := by
      intro acc
      induction cands generalizing acc with
      | nil =>
          cases acc
          exact ⟨[], by simp⟩
      | cons w' ws ih =>
          dsimp [List.foldl]
          rcases hStep acc w' with ⟨newHead, hHead⟩
          rcases ih (step acc w') with ⟨newTail, hTail⟩
          refine ⟨newTail ++ newHead, ?_⟩
          rw [hTail, hHead]
          simp [List.append_assoc]
    rcases hFold ([], st) with ⟨newFold, hFoldEq⟩
    rcases mkBigOrIff_clauses_eq_append
        (b := b)
        (vs :=
          (cands.foldl
            (fun (acc : List (Var b) × EncState b) w' =>
              let (vs, st') := acc
              let (y, st'') := mkY b t' w w' st'
              (FVar.toVar b y :: vs, st''))
            ([], st)).1)
        (st :=
          (cands.foldl
            (fun (acc : List (Var b) × EncState b) w' =>
              let (vs, st') := acc
              let (y, st'') := mkY b t' w w' st'
              (FVar.toVar b y :: vs, st''))
            ([], st)).2) with
    ⟨newBig, hBigEq⟩
    refine ⟨newBig ++ newFold, ?_⟩
    cases hFoldRes :
        cands.foldl
          (fun (acc : List (Var b) × EncState b) w' =>
            let (vs, st') := acc
            let (y, st'') := mkY b t' w w' st'
            (FVar.toVar b y :: vs, st''))
          ([], st) with
    | mk ys stYs =>
        have hClausesYs : stYs.clauses = newFold ++ st.clauses := by
          convert hFoldEq using 1
          exact congrArg (·.2.clauses) hFoldRes.symm
        simp [hFoldRes] at hBigEq
        simp [hBigEq, hClausesYs, List.append_assoc]

-- ============================================================================
-- nextFresh lemmas
-- ============================================================================

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkY_nextFresh (b : Bounds S) (t' : b.times) (w w' : WId b) (st : EncState b) :
    (mkY b t' w w' st).2.nextFresh = st.nextFresh + 1 := by
  unfold mkY
  simp only [EncState.allocFresh, EncState.addClause]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkOw_nextFresh (b : Bounds S) (t : b.times) (w : WId b) (d : FVar b) (st : EncState b) :
    (mkOw b t w d st).2.nextFresh = st.nextFresh + 1 := by
  unfold mkOw
  simp only [EncState.allocFresh, EncState.addClause]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkY_fst_id (b : Bounds S) (t' : b.times) (w w' : WId b) (st : EncState b) :
    (mkY b t' w w' st).1.id = st.nextFresh := by
  unfold mkY
  simp only [EncState.allocFresh]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkOw_fst_id (b : Bounds S) (t : b.times) (w : WId b) (d : FVar b) (st : EncState b) :
    (mkOw b t w d st).1.id = st.nextFresh := by
  unfold mkOw
  simp only [EncState.allocFresh]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkOw_fst (b : Bounds S) (t : b.times) (w : WId b) (d : FVar b) (st : EncState b) :
    (mkOw b t w d st).1 = ⟨st.nextFresh⟩ := by
  unfold mkOw
  simp only [EncState.allocFresh]

-- ============================================================================
-- mkDw nextFresh and fst lemmas
-- ============================================================================

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkDw_foldY_nextFresh_aux (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b)
    (vs : List (Var b)) (cands : List (WId b)) :
    (cands.foldl
      (fun acc w' => (FVar.toVar b (mkY b t' w w' acc.2).1 :: acc.1, (mkY b t' w w' acc.2).2))
      (vs, st)).2.nextFresh = st.nextFresh + cands.length := by
  induction cands generalizing st vs with
  | nil => simp
  | cons w' cands ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    rw [mkY_nextFresh]
    omega

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkDw_foldY_nextFresh (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b)
    (cands : List (WId b)) :
    (cands.foldl
      (fun acc w' => (FVar.toVar b (mkY b t' w w' acc.2).1 :: acc.1, (mkY b t' w w' acc.2).2))
      ([], st)).2.nextFresh = st.nextFresh + cands.length :=
  mkDw_foldY_nextFresh_aux b t' w st [] cands

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Alternative form of mkDw_foldY_nextFresh that takes initial accumulator. -/
lemma mkDw_fold_nextFresh (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (init : List (Var b) × EncState b) :
    (cands.foldl
      (fun acc w' =>
        let (vs, st'') := acc
        let (y, st''') := mkY b t' w w' st''
        (FVar.toVar b y :: vs, st'''))
      init).2.nextFresh = init.2.nextFresh + cands.length := by
  induction cands generalizing init with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hStep := mkY_nextFresh b t' w c init.2
    rw [ih]
    simp only [hStep]
    omega

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma mkDw_snd_nextFresh_eq (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b) :
    let cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
    (mkDw b t' w st).2.nextFresh =
      if cands.isEmpty then st.nextFresh + 1 else st.nextFresh + cands.length + 1 := by
  classical
  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w') with hCandsDef
  cases hCands : cands with
  | nil =>
    -- Empty case: allocFresh + addClause
    unfold mkDw
    simp only [← hCandsDef, hCands, EncState.allocFresh, EncState.addClause, List.isEmpty_nil,
        ↓reduceIte]
  | cons w0 ws =>
    -- Non-empty case: fold + mkBigOrIff
    unfold mkDw
    simp only [← hCandsDef, hCands, List.isEmpty_cons, mkBigOrIff_nextFresh]
    have hFold := mkDw_foldY_nextFresh b t' w st (w0 :: ws)
    simp only at hFold
    simp only [hFold, Bool.false_eq_true, ↓reduceIte]

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma mkDw_snd_nextFresh_ge (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b) :
    st.nextFresh + 1 ≤ (mkDw b t' w st).2.nextFresh := by
  classical
  have h := mkDw_snd_nextFresh_eq b t' w st
  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  simp only at h
  split at h <;> omega

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma mkDw_fst_id (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b) :
    let cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
    (mkDw b t' w st).1.id =
      if cands.isEmpty then st.nextFresh else st.nextFresh + cands.length := by
  classical
  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w') with hCandsDef
  cases hCands : cands with
  | nil =>
    -- Empty case: allocFresh
    unfold mkDw
    simp only [← hCandsDef, hCands, EncState.allocFresh, List.isEmpty_nil, ↓reduceIte]
  | cons w0 ws =>
    -- Non-empty case: fold + mkBigOrIff
    unfold mkDw
    simp only [← hCandsDef, hCands, List.isEmpty_cons, mkBigOrIff_fst]
    -- mkBigOrIff's fst.id = input.nextFresh = fold.2.nextFresh
    -- fold.2.nextFresh = st.nextFresh + cands.length
    have hFold := mkDw_foldY_nextFresh b t' w st (w0 :: ws)
    simp only at hFold
    simp only [hFold, Bool.false_eq_true, ↓reduceIte]

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma mkDw_fst_ge (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b) :
    st.nextFresh ≤ (mkDw b t' w st).1.id := by
  classical
  have h := mkDw_fst_id b t' w st
  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  simp only at h
  split at h <;> omega

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma mkDw_fst_lt_snd_nextFresh (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b) :
    (mkDw b t' w st).1.id < (mkDw b t' w st).2.nextFresh := by
  classical
  have hId := mkDw_fst_id b t' w st
  have hNext := mkDw_snd_nextFresh_eq b t' w st
  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  simp only at hId hNext
  cases hEmpty : cands.isEmpty
  · simp only [hEmpty, ↓reduceIte, Bool.false_eq_true] at hId hNext; omega
  · simp only [hEmpty, ↓reduceIte] at hId hNext; omega

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Fresh variables in new clauses of mkDw have index >= input state's nextFresh.
    This is because all Fresh vars are allocated starting at st.nextFresh. -/
lemma mkDw_newClauses_fresh_ge (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (mkDw b t' w st).2.clauses)
    (hNotInSt : clause ∉ st.clauses)
    (lit : SAT.Lit (Var b)) (hLit : lit ∈ clause)
    (n : Nat) (hFresh : lit.getVar = Var.Fresh n) :
    n ≥ st.nextFresh := by
  classical
  unfold mkDw at hClause
  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  by_cases hEmpty : cands = []
  · -- Empty case: single clause [neg d] where d.id = st.nextFresh
    simp only [hEmpty] at hClause
    cases hAlloc : EncState.allocFresh b st with
    | mk d st1 =>
        have hDId : d.id = st.nextFresh := by
          simpa [hAlloc] using EncState.allocFresh_fst (b := b) (st := st)
        have hSt1Clauses : st1.clauses = st.clauses := by
          simpa [hAlloc] using EncState.allocFresh_clauses_eq (b := b) (st := st)
        simp only [hAlloc] at hClause
        simp only [EncState.addClause, List.mem_cons] at hClause
        rcases hClause with hNew | hOld
        · -- clause = [neg d]
          subst hNew
          simp only [List.mem_singleton] at hLit
          subst hLit
          simp only [SAT.Lit.getVar, FVar.toVar] at hFresh
          have hN : n = d.id := by injection hFresh; omega
          rw [hN, hDId]
        · -- clause ∈ st1.clauses = st.clauses
          rw [hSt1Clauses] at hOld
          exact absurd hOld hNotInSt
  · -- Non-empty case: use mkDw_structural_determinism infrastructure
    -- The key insight: all Fresh vars allocated by mkDw have index >= st.nextFresh
    -- because mkY allocates at current nextFresh which starts at st.nextFresh
    have hCandsNe : cands ≠ [] := hEmpty
    simp only at hClause

    -- Use the fact that mkDw preserves well-formedness and allocates Fresh vars >= st.nextFresh
    -- All Fresh vars in new clauses are from:
    -- 1. mkY allocations (y.id = step's nextFresh >= st.nextFresh)
    -- 2. mkBigOrIff allocation (u.id = fold result's nextFresh >= st.nextFresh)

    -- Structural decomposition: mkDw adds newClauses ++ st.clauses
    rcases mkDw_clauses_eq_append (b := b) (t' := t') (w := w) (st := st) with ⟨newClauses, hAppend⟩
    unfold mkDw at hAppend
    simp only at hAppend

    -- hClause tells us clause ∈ (mkDw...).2.clauses
    -- hNotInSt tells us clause ∉ st.clauses
    -- So clause ∈ newClauses

    -- The proof strategy: trace that all Fresh vars in newClauses are >= st.nextFresh
    -- This requires tracking through the fold and mkBigOrIff
    -- For now, we use the fact that this is structurally guaranteed

    -- Define the fold step
    let step := fun (acc : List (Var b) × EncState b) w' =>
          let (vs, st') := acc
          let (y, st'') := mkY b t' w w' st'
          (FVar.toVar b y :: vs, st'')

    -- Key invariant: all Fresh vars allocated during the fold have id >= st.nextFresh
    -- This follows from:
    -- 1. mkY allocates y at st'.nextFresh
    -- 2. Fold starts with nextFresh = st.nextFresh
    -- 3. nextFresh only increases

    -- For the fold: each mkY step adds clauses with Fresh y where y.id >= st.nextFresh
    -- For mkBigOrIff: u.id = fold result's nextFresh >= st.nextFresh

    have hFoldNextFreshGe : (cands.foldl step ([], st)).2.nextFresh ≥ st.nextFresh := by
      have hMono : ∀ (candList : List (WId b)) (initVs : List (Var b)) (stI : EncState b),
          (candList.foldl step (initVs, stI)).2.nextFresh ≥ stI.nextFresh := by
        intro candList
        induction candList with
        | nil => intro initVs stI; simp [step]
        | cons w' ws ih =>
            intro initVs stI
            simp only [List.foldl_cons]
            -- step (initVs, stI) w' = (y :: initVs, mkY.2)
            have hStepEq : step (initVs, stI) w' =
                (FVar.toVar b (mkY b t' w w' stI).1 :: initVs, (mkY b t' w w' stI).2) := by
              simp only [step]
            rw [hStepEq]
            have hYNext := mkY_nextFresh b t' w w' stI
            have hIH := ih (FVar.toVar b (mkY b t' w w' stI).1 :: initVs) (mkY b t' w w' stI).2
            omega
      exact hMono cands [] st

    -- All Fresh vars in new clauses of mkBigOrIff are >= st.nextFresh
    -- because they are either u (at fold.2.nextFresh >= st.nextFresh)
    -- or from foldRes.1 (each is y from mkY with y.id >= st.nextFresh)

    -- Main fold invariant: Fresh vars in NEW clauses of the fold have index >= st.nextFresh
    have hFoldFreshGe : ∀ (candList : List (WId b)) (initVs : List (Var b)) (stI : EncState b),
        stI.nextFresh ≥ st.nextFresh →
        ∀ clause, clause ∈ (candList.foldl step (initVs, stI)).2.clauses →
        clause ∉ stI.clauses →
        ∀ (lit : SAT.Lit (Var b)), lit ∈ clause →
        ∀ m, lit.getVar = Var.Fresh m → m ≥ st.nextFresh := by
      intro candList
      induction candList with
      | nil =>
          intro initVs stI _ clause hClause hNotIn
          simp only [List.foldl_nil] at hClause
          exact absurd hClause hNotIn
      | cons w' cands' ih =>
          intro initVs stI hGeI clause hClause hNotIn lit hLit m hFreshM
          simp only [List.foldl_cons, step] at hClause
          have hYId := mkY_fst_id b t' w w' stI
          have hYNext := mkY_nextFresh b t' w w' stI
          have hAppendY := mkY_clauses_eq_append b t' w w' stI
          have hGeY : (mkY b t' w w' stI).2.nextFresh ≥ st.nextFresh := by omega
          -- Check if clause is in the clauses after mkY step
          by_cases hInMkY : clause ∈ (mkY b t' w w' stI).2.clauses
          · -- Clause is from mkY step (either new or inherited)
            by_cases hInStI : clause ∈ stI.clauses
            · -- Inherited from stI, but hNotIn says clause ∉ stI.clauses - contradiction
              exact absurd hInStI hNotIn
            · -- clause ∉ stI.clauses, so it's a NEW mkY clause
              rw [hAppendY] at hInMkY
              simp only [List.mem_append] at hInMkY
              rcases hInMkY with hNew | hOld
              · -- In new clauses: check which one
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hNew
                rcases hNew with hC1 | hC2 | hC3
                · -- Clause 1: [¬Mem t' w', ¬PreEq w.ti w'.ti, y]
                  subst hC1
                  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
                  rcases hLit with hL1 | hL2 | hL3
                  · subst hL1; simp only [SAT.Lit.getVar] at hFreshM; exact Var.noConfusion hFreshM
                  · subst hL2; simp only [SAT.Lit.getVar] at hFreshM; exact Var.noConfusion hFreshM
                  · subst hL3; simp only [SAT.Lit.getVar, FVar.toVar] at hFreshM
                    have hEq : m = (mkY b t' w w' stI).1.id := by injection hFreshM; omega
                    rw [hEq, hYId]; exact hGeI
                · -- Clause 2: [¬y, PreEq w.ti w'.ti]
                  subst hC2
                  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
                  rcases hLit with hL1 | hL2
                  · subst hL1; simp only [SAT.Lit.getVar, FVar.toVar] at hFreshM
                    have hEq : m = (mkY b t' w w' stI).1.id := by injection hFreshM; omega
                    rw [hEq, hYId]; exact hGeI
                  · subst hL2; simp only [SAT.Lit.getVar] at hFreshM; exact Var.noConfusion hFreshM
                · -- Clause 3: [¬y, Mem t' w']
                  subst hC3
                  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLit
                  rcases hLit with hL1 | hL2
                  · subst hL1; simp only [SAT.Lit.getVar, FVar.toVar] at hFreshM
                    have hEq : m = (mkY b t' w w' stI).1.id := by injection hFreshM; omega
                    rw [hEq, hYId]; exact hGeI
                  · subst hL2; simp only [SAT.Lit.getVar] at hFreshM; exact Var.noConfusion hFreshM
              · -- clause ∈ stI.clauses, but we said hInStI: clause ∉ stI.clauses
                exact absurd hOld hInStI
          · -- Clause is from later fold step (not in mkY output)
            exact ih (FVar.toVar b (mkY b t' w w' stI).1 :: initVs) (mkY b t' w w' stI).2
              hGeY clause hClause hInMkY lit hLit m hFreshM

    -- Apply the fold invariant to the actual fold starting with ([], st)
    have hFoldResult := hFoldFreshGe cands [] st (Nat.le_refl _)

    -- Now consider where clause came from
    -- clause is from mkBigOrIff applied to fold result
    set foldRes := cands.foldl step ([], st) with hFoldResDef

    -- Decompose mkBigOrIff clauses using the append lemma
    have hOrIffAppend := mkBigOrIff_clauses_eq_append b foldRes.1 foldRes.2
    rcases hOrIffAppend with ⟨newOrIff, hOrIffEq⟩
    rw [hOrIffEq] at hClause
    simp only [List.mem_append] at hClause
    rcases hClause with hNew | hOld
    · -- In new mkBigOrIff clauses (long clause or short clauses)
      -- Fresh vars are either u (id = foldRes.2.nextFresh >= st.nextFresh)
      -- or from foldRes.1 (each is Fresh y from mkY with id >= st.nextFresh)

      -- First, establish that all vars in foldRes.1 are Fresh with id >= st.nextFresh
      have hVarFreshGe : ∀ v ∈ foldRes.1, ∀ m, v = Var.Fresh m →
          m ≥ st.nextFresh ∧ m < foldRes.2.nextFresh := by
        intro v hVMem m hVFresh
        -- Prove by induction on cands
        have hFoldVars : ∀ (candList : List (WId b)) (initVs : List (Var b)) (stI : EncState b),
            stI.nextFresh ≥ st.nextFresh →
            ∀ v ∈ (candList.foldl step (initVs, stI)).1,
            ∀ m, v = Var.Fresh m →
            (v ∈ initVs ∨
              (m ≥ stI.nextFresh ∧ m < (candList.foldl step (initVs, stI)).2.nextFresh)) := by
          intro candList
          induction candList with
          | nil =>
              intro initVs stI _ v hv m hvm
              simp only [List.foldl_nil] at hv ⊢
              left; exact hv
          | cons w' ws ih =>
              intro initVs stI hGeI v hv m hvm
              simp only [List.foldl_cons, step] at hv ⊢
              have hYId := mkY_fst_id b t' w w' stI
              have hYNext := mkY_nextFresh b t' w w' stI
              have hGeY : (mkY b t' w w' stI).2.nextFresh ≥ st.nextFresh := by omega
              -- Apply IH: v came from the ws fold starting at (y::initVs, mkY.2)
              have hIH := ih (FVar.toVar b (mkY b t' w w' stI).1 :: initVs)
                  (mkY b t' w w' stI).2 hGeY v hv m hvm
              rcases hIH with hInInit | ⟨hGe, hLt⟩
              · -- v was in (y :: initVs)
                simp only [List.mem_cons] at hInInit
                rcases hInInit with hIsY | hInInitVs
                · -- v = y = FVar.toVar b (mkY b t' w w' stI).1 = Var.Fresh yId
                  right
                  have hVIsY := hIsY
                  simp only [FVar.toVar] at hVIsY hvm
                  have hMEqYId : m = (mkY b t' w w' stI).1.id := by
                    rw [hVIsY] at hvm; injection hvm; omega
                  -- Need: m ≥ stI.nextFresh ∧ m < (ws.foldl...).2.nextFresh
                  -- m = stI.nextFresh (since y.id = stI.nextFresh)
                  -- (ws.foldl...).2.nextFresh > stI.nextFresh (since mkY increases nextFresh)
                  have hMonoWs : (ws.foldl step
                      (FVar.toVar b (mkY b t' w w' stI).1 :: initVs,
                       (mkY b t' w w' stI).2)).2.nextFresh > stI.nextFresh := by
                    -- mkY increases nextFresh by 1
                    have hMkYGe : (mkY b t' w w' stI).2.nextFresh > stI.nextFresh := by
                      rw [hYNext]; omega
                    -- Fold is monotonic in nextFresh
                    have hFoldMono :
                        ∀ (cands' : List (WId b)) (initVs' : List (Var b)) (stI' : EncState b),
                        (cands'.foldl step (initVs', stI')).2.nextFresh ≥ stI'.nextFresh := by
                      intro cands'
                      induction cands' with
                      | nil => intro initVs' stI'; simp [step]
                      | cons w'' ws' ih' =>
                          intro initVs' stI'
                          simp only [List.foldl_cons]
                          have hStepEq : step (initVs', stI') w'' =
                              (FVar.toVar b (mkY b t' w w'' stI').1 :: initVs',
                               (mkY b t' w w'' stI').2) := by
                            simp [step]
                          rw [hStepEq]
                          have hMkYGe' : (mkY b t' w w'' stI').2.nextFresh > stI'.nextFresh := by
                            have := mkY_nextFresh b t' w w'' stI'; omega
                          have := ih' (FVar.toVar b (mkY b t' w w'' stI').1 :: initVs')
                                      (mkY b t' w w'' stI').2
                          omega
                    have := hFoldMono ws (FVar.toVar b (mkY b t' w w' stI).1 :: initVs)
                                         (mkY b t' w w' stI).2
                    omega
                  constructor
                  · rw [hMEqYId, hYId]
                  · rw [hMEqYId, hYId]; omega
                · -- v ∈ initVs
                  left; exact hInInitVs
              · -- v came from the ws fold proper
                right; constructor
                · omega
                · exact hLt
        have hApp := hFoldVars cands [] st (Nat.le_refl _) v hVMem m hVFresh
        simp only [List.not_mem_nil, false_or] at hApp
        exact hApp

      -- Now analyze the clause structure of mkBigOrIff
      -- The new clauses are: long clause [¬u, v1+, ..., vn+] and short clauses [¬vi, u+]
      have hUFVar : (mkBigOrIff b foldRes.1 foldRes.2).1 = ⟨foldRes.2.nextFresh⟩ :=
        mkBigOrIff_fst b foldRes.1 foldRes.2

      -- The clause is one of the new mkBigOrIff clauses
      -- lit ∈ clause, and lit.getVar = Var.Fresh n
      -- Fresh vars in these clauses are: u (id = foldRes.2.nextFresh) or from foldRes.1

      -- Case analysis: is lit the control var u or from foldRes.1?
      by_cases hLitIsU : lit.getVar = FVar.toVar b (mkBigOrIff b foldRes.1 foldRes.2).1
      · -- lit is u: n = foldRes.2.nextFresh >= st.nextFresh
        simp only [FVar.toVar, hUFVar] at hLitIsU hFresh
        rw [hLitIsU] at hFresh
        -- hFresh : Var.Fresh foldRes.2.nextFresh = Var.Fresh n
        have hNEq : n = foldRes.2.nextFresh := by injection hFresh; omega
        rw [hNEq]
        exact hFoldNextFreshGe
      · -- lit is not u, so it's from foldRes.1
        -- First check if clause also appears in foldRes.2.clauses
        by_cases hInFold : clause ∈ foldRes.2.clauses
        · -- If clause ∈ foldRes.2.clauses, use hFoldResult directly
          exact hFoldResult clause hInFold hNotInSt lit hLit n hFresh
        · -- clause ∉ foldRes.2.clauses, use mkBigOrIff_newClause_vars
          have hMem : clause ∈ (mkBigOrIff b foldRes.1 foldRes.2).2.clauses := by
            rw [hOrIffEq]; exact List.mem_append_left _ hNew
          have hVarOrVs := mkBigOrIff_newClause_vars b foldRes.1 foldRes.2 clause
                                                      hMem hInFold lit hLit
          rcases hVarOrVs with hIsU | hInVs
          · exact absurd hIsU hLitIsU
          · -- lit.getVar ∈ foldRes.1
            have ⟨hGe, _⟩ := hVarFreshGe lit.getVar hInVs n hFresh
            exact hGe
    · -- In fold clauses (inherited)
      by_cases hInSt : clause ∈ st.clauses
      · exact absurd hInSt hNotInSt
      · exact hFoldResult clause hOld hInSt lit hLit n hFresh

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- New clauses from mkDw have at least one Fresh variable with index >= st.nextFresh.
    This is the existential form of mkDw_newClauses_fresh_ge. -/
lemma mkDw_newClause_exists_fresh_ge (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (mkDw b t' w st).2.clauses)
    (hNotInSt : clause ∉ st.clauses) :
    ∃ lit ∈ clause, ∃ n, lit.getVar = Var.Fresh n ∧ n ≥ st.nextFresh := by
  classical
  -- Clauses have at least one lit (from encoding structure)
  -- All Fresh lits in new clauses have index >= st.nextFresh by mkDw_newClauses_fresh_ge
  -- We just need to find ONE Fresh lit in the clause
  unfold mkDw at hClause
  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  by_cases hEmpty : cands = []
  · -- Empty case: single clause [neg d] where d.id = st.nextFresh
    simp only [hEmpty] at hClause
    cases hAlloc : EncState.allocFresh b st with
    | mk d st1 =>
        have hDId : d.id = st.nextFresh := by
          simpa [hAlloc] using EncState.allocFresh_fst (b := b) (st := st)
        have hSt1Clauses : st1.clauses = st.clauses := by
          simpa [hAlloc] using EncState.allocFresh_clauses_eq (b := b) (st := st)
        simp only [hAlloc, EncState.addClause, List.mem_cons] at hClause
        rcases hClause with hNew | hOld
        · subst hNew
          exact ⟨SAT.Lit.neg (FVar.toVar b d), List.mem_singleton_self _, d.id, rfl, Nat.le_of_eq hDId.symm⟩
        · rw [hSt1Clauses] at hOld; exact absurd hOld hNotInSt
  · -- Non-empty case: fold mkY then mkBigOrIff
    obtain ⟨c0, cs, hCands⟩ := List.exists_cons_of_ne_nil hEmpty
    simp only [cands] at hCands
    simp only [hCands] at hClause
    -- Define the fold step
    let step := fun (acc : List (Var b) × EncState b) w' =>
          let (vs, st') := acc
          let (y, st'') := mkY b t' w w' st'
          (FVar.toVar b y :: vs, st'')
    -- Get fold result
    have hFoldNextFresh : ((c0 :: cs).foldl step ([], st)).2.nextFresh = st.nextFresh + (c0 :: cs).length :=
      mkDw_fold_nextFresh b t' w (c0 :: cs) ([], st)
    have hFoldGe : ((c0 :: cs).foldl step ([], st)).2.nextFresh ≥ st.nextFresh := by omega
    set foldRes := (c0 :: cs).foldl step ([], st) with hFoldResDef
    -- Check if clause is from the fold or from mkBigOrIff
    by_cases hInFold : clause ∈ foldRes.2.clauses
    · -- Clause is from the mkY fold - has Fresh y with id >= st.nextFresh
      -- Induction on the fold
      suffices h : ∀ (candList : List (WId b)) (initVs : List (Var b)) (stI : EncState b),
          stI.nextFresh ≥ st.nextFresh →
          clause ∈ (candList.foldl step (initVs, stI)).2.clauses →
          clause ∉ stI.clauses →
          ∃ lit ∈ clause, ∃ n, lit.getVar = Var.Fresh n ∧ n ≥ st.nextFresh by
        exact h (c0 :: cs) [] st (Nat.le_refl _) hInFold hNotInSt
      intro candList
      induction candList with
      | nil => intro _ _ _ hIn hNotIn; simp at hIn; exact absurd hIn hNotIn
      | cons w' ws ih =>
          intro initVs stI hStIGe hIn hNotIn
          simp only [List.foldl_cons, step] at hIn
          have hYNext : (mkY b t' w w' stI).2.nextFresh = stI.nextFresh + 1 := mkY_nextFresh b t' w w' stI
          by_cases hInY : clause ∈ (mkY b t' w w' stI).2.clauses
          · -- From this mkY step
            by_cases hInStI : clause ∈ stI.clauses
            · exact absurd hInStI hNotIn
            · -- New clause from mkY - all 3 clause types contain Fresh y
              unfold mkY at hInY hInStI
              cases hAllocY : EncState.allocFresh b stI with
              | mk y stY =>
                  have hYId : y.id = stI.nextFresh := by
                    simpa [hAllocY] using EncState.allocFresh_fst (b := b) (st := stI)
                  have hStYClauses : stY.clauses = stI.clauses := by
                    simpa [hAllocY] using EncState.allocFresh_clauses_eq (b := b) (st := stI)
                  simp only [hAllocY, EncState.addClause, List.mem_cons] at hInY
                  rcases hInY with h1 | h2 | h3 | hOld
                  · -- clause = [neg Mem, neg PreEq, pos y] - pos y is third element
                    subst h1
                    refine ⟨SAT.Lit.pos (FVar.toVar b y), ?_, y.id, rfl, ?_⟩
                    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr
                        (List.mem_singleton.mpr rfl))))
                    · rw [hYId]; exact hStIGe
                  · -- clause = [neg y, pos PreEq] - neg y is first element
                    subst h2
                    exact ⟨SAT.Lit.neg (FVar.toVar b y), List.mem_cons_self, y.id, rfl,
                      by rw [hYId]; exact hStIGe⟩
                  · -- clause = [neg y, pos Mem] - neg y is first element
                    subst h3
                    exact ⟨SAT.Lit.neg (FVar.toVar b y), List.mem_cons_self, y.id, rfl,
                      by rw [hYId]; exact hStIGe⟩
                  · rw [hStYClauses] at hOld; exact absurd hOld hInStI
          · -- From later fold steps
            have hYGe : (mkY b t' w w' stI).2.nextFresh ≥ st.nextFresh := by omega
            exact ih _ (mkY b t' w w' stI).2 hYGe hIn hInY
    · -- Clause is new from mkBigOrIff - has Fresh u with id = foldRes.2.nextFresh >= st.nextFresh
      -- Use mkBigOrIff_newClause_vars: every lit in new clause has var = u or in foldRes.1
      -- Since u.id = foldRes.2.nextFresh >= st.nextFresh, we're done
      -- Get membership in mkBigOrIff clauses
      have hMem : clause ∈ (mkBigOrIff b foldRes.1 foldRes.2).2.clauses := by
        simp only [cands, hCands] at hClause
        convert hClause using 2
      have hNotInFoldRes : clause ∉ foldRes.2.clauses := hInFold
      -- u.id = foldRes.2.nextFresh >= st.nextFresh
      have hUFst : (mkBigOrIff b foldRes.1 foldRes.2).1 = { id := foldRes.2.nextFresh } :=
        mkBigOrIff_fst b foldRes.1 foldRes.2
      have hUGe : (mkBigOrIff b foldRes.1 foldRes.2).1.id ≥ st.nextFresh := by
        simp only [hUFst]; exact hFoldGe
      -- All new clauses are non-empty (long clause has neg u, short have 2 elements)
      -- Pick any lit and use mkBigOrIff_newClause_vars
      -- The clause must be non-empty since it's from mkBigOrIff
      have hNe : clause ≠ [] := by
        intro hEmpty
        subst hEmpty
        -- Empty clause can't be in mkBigOrIff result
        unfold mkBigOrIff at hMem
        cases hAlloc : EncState.allocFresh b foldRes.2 with
        | mk u st1 =>
            simp only [hAlloc] at hMem
            -- Empty clause propagates backwards through the fold
            have hNotEmpty : ∀ (vs : List (Var b)) (stInit : EncState b),
                [] ∈ (vs.foldl (fun st' v => EncState.addClause b st'
                  [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]) stInit).clauses →
                [] ∈ stInit.clauses := by
              intro vs
              induction vs with
              | nil => intro _ h; exact h
              | cons v vs' ih =>
                  intro stInit h
                  simp only [List.foldl_cons] at h
                  -- h : [] ∈ (foldl step (addClause stInit short) vs').clauses
                  -- Apply ih to get [] ∈ (addClause stInit short).clauses
                  have hInAdd := ih (EncState.addClause b stInit
                    [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u)]) h
                  -- Now hInAdd : [] ∈ short :: stInit.clauses
                  simp only [EncState.addClause] at hInAdd
                  cases List.mem_cons.mp hInAdd with
                  | inl hEq => exact absurd hEq (List.cons_ne_nil _ _).symm
                  | inr hOld => exact hOld
            simp only [EncState.addClause] at hMem
            have hInFoldOrLong := List.mem_cons.mp hMem
            cases hInFoldOrLong with
            | inl hLong => exact absurd hLong (List.cons_ne_nil _ _).symm
            | inr hInFold =>
                have hInSt1 := hNotEmpty foldRes.1 st1 hInFold
                have hSt1Clauses : st1.clauses = foldRes.2.clauses := by
                  simpa [hAlloc] using EncState.allocFresh_clauses_eq (b := b) (st := foldRes.2)
                rw [hSt1Clauses] at hInSt1
                exact absurd hInSt1 hNotInFoldRes
      obtain ⟨lit, hLitMem⟩ := List.exists_mem_of_ne_nil clause hNe
      -- Apply mkBigOrIff_newClause_vars
      have hVarChoice := mkBigOrIff_newClause_vars b foldRes.1 foldRes.2 clause hMem hNotInFoldRes
        lit hLitMem
      rcases hVarChoice with hIsU | hInVs
      · -- lit.getVar = u, so lit is Fresh with index >= st.nextFresh
        exact ⟨lit, hLitMem, (mkBigOrIff b foldRes.1 foldRes.2).1.id, hIsU, hUGe⟩
      · -- lit.getVar ∈ foldRes.1 - these are all Fresh y vars from mkY with indices >= st.nextFresh
        -- foldRes.1 contains FVar.toVar b y for each y from mkY
        -- Each y.id >= st.nextFresh since mkY allocates fresh vars starting from st.nextFresh
        -- Prove by induction that all vars in foldRes.1 are Fresh with index >= st.nextFresh
        have hFoldVars : ∀ (candList : List (WId b)) (initVs : List (Var b)) (stI : EncState b),
            stI.nextFresh ≥ st.nextFresh →
            ∀ v ∈ (candList.foldl step (initVs, stI)).1,
            v ∈ initVs ∨ ∃ n, v = Var.Fresh n ∧ n ≥ st.nextFresh := by
          intro candList
          induction candList with
          | nil => intro initVs _ _ v hv; left; simp at hv; exact hv
          | cons w' ws ih =>
              intro initVs stI hStIGe v hv
              simp only [List.foldl_cons, step] at hv
              have hYId : (mkY b t' w w' stI).1.id = stI.nextFresh := mkY_fst_id b t' w w' stI
              have hYGe : (mkY b t' w w' stI).2.nextFresh ≥ st.nextFresh := by
                have := mkY_nextFresh b t' w w' stI
                omega
              rcases ih (FVar.toVar b (mkY b t' w w' stI).1 :: initVs)
                (mkY b t' w w' stI).2 hYGe v hv with hInit | ⟨n, hEq, hGe⟩
              · simp only [List.mem_cons] at hInit
                rcases hInit with hNew | hOld
                · right; exact ⟨(mkY b t' w w' stI).1.id, hNew, by rw [hYId]; exact hStIGe⟩
                · left; exact hOld
              · right; exact ⟨n, hEq, hGe⟩
        have hVarsResult := hFoldVars (c0 :: cs) [] st (Nat.le_refl _) lit.getVar hInVs
        rcases hVarsResult with hInit | ⟨n, hEq, hGe⟩
        · simp at hInit
        · exact ⟨lit, hLitMem, n, hEq, hGe⟩

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- New clauses from mkOw have at least one Fresh variable with index >= st.nextFresh.
    This is the existential form for mkOw's new clauses. -/
lemma mkOw_newClause_exists_fresh_ge (b : Bounds S) (t : b.times) (w : WId b)
    (d : FVar b) (st : EncState b)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ (mkOw b t w d st).2.clauses)
    (hNotInSt : clause ∉ st.clauses) :
    ∃ lit ∈ clause, ∃ n, lit.getVar = Var.Fresh n ∧ n ≥ st.nextFresh := by
  classical
  -- mkOw adds exactly 3 clauses, all containing the fresh var o with id = st.nextFresh
  let o := (mkOw b t w d st).1
  have hOId : o.id = st.nextFresh := mkOw_fst_id b t w d st
  have hAppend := mkOw_clauses_eq_append b t w d st
  rw [hAppend] at hClause
  cases List.mem_append.mp hClause with
  | inl hNew =>
      -- clause is one of the 3 new clauses
      simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hNew
      rcases hNew with h1 | h2 | h3
      · -- [pos o, neg d]
        subst h1
        refine ⟨SAT.Lit.pos (FVar.toVar b o), List.mem_cons_self, o.id, rfl, ?_⟩
        rw [hOId]
      · -- [pos o, pos Mem]
        subst h2
        refine ⟨SAT.Lit.pos (FVar.toVar b o), List.mem_cons_self, o.id, rfl, ?_⟩
        rw [hOId]
      · -- [neg o, neg Mem, pos d]
        subst h3
        refine ⟨SAT.Lit.neg (FVar.toVar b o), List.mem_cons_self, o.id, rfl, ?_⟩
        rw [hOId]
  | inr hOld =>
      exact absurd hOld hNotInSt

-- ============================================================================
-- Well-formedness lemmas
-- ============================================================================

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkY_wf (b : Bounds S) (t' : b.times) (w w' : WId b) (st : EncState b)
    (hWF : EncState.WellFormed st) :
    EncState.WellFormed (mkY b t' w w' st).2 := by
  -- mkY does: allocFresh, then 3 addClause operations
  -- Fresh y at index st.nextFresh; new nextFresh = st.nextFresh + 1
  -- Each new clause uses y at index st.nextFresh, which is < new nextFresh
  unfold mkY
  cases hAlloc : EncState.allocFresh b st with
  | mk y st1 =>
      -- y.id = st.nextFresh
      have hYId : y.id = st.nextFresh := by
        simpa [hAlloc] using EncState.allocFresh_fst (b := b) (st := st)
      -- st1.nextFresh = st.nextFresh + 1
      have hSt1Next : st1.nextFresh = st.nextFresh + 1 := by
        simpa [hAlloc] using EncState.allocFresh_nextFresh (b := b) (st := st)
      -- st1 is well-formed
      have hWF1 : EncState.WellFormed st1 := by
        simpa [hAlloc] using EncState.allocFresh_wf (b := b) (st := st) hWF
      -- y.id < st1.nextFresh
      have hYLt : y.id < st1.nextFresh := by omega
      simp only
      -- Helper: Fresh y is below st1.nextFresh
      have hYBelow : ∀ lit, lit.getVar = FVar.toVar b y → litFreshBelow lit st1.nextFresh := by
        intro lit hLitVar
        simp only [litFreshBelow, hLitVar, FVar.toVar, hYLt]
      -- Helper: non-Fresh literals are always fresh-below
      have hNonFreshBelow : ∀ (lit : SAT.Lit (Var b)), (∀ n, lit.getVar ≠ Var.Fresh n) →
          litFreshBelow lit st1.nextFresh := by
        intro lit hNonFresh
        unfold litFreshBelow
        cases hv : lit.getVar with
        | Fresh n => exact absurd hv (hNonFresh n)
        | _ => trivial
      -- Clause 1: [neg y, pos Mem t' w']
      have hC1 : clauseFreshBelow [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')]
          st1.nextFresh := by
        intro lit hLit
        cases hLit with
        | head => exact hYBelow _ rfl
        | tail _ h => cases h with
          | head => exact hNonFreshBelow _ (by simp [SAT.Lit.getVar])
          | tail _ h2 => cases h2
      have hWF2 : EncState.WellFormed (EncState.addClause b st1
          [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')]) :=
        EncState.addClause_wf hWF1 _ hC1
      -- Clause 2: [neg y, pos PreEq]
      have hC2 : clauseFreshBelow [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w'.ti)]
          st1.nextFresh := by
        intro lit hLit
        cases hLit with
        | head => exact hYBelow _ rfl
        | tail _ h => cases h with
          | head => exact hNonFreshBelow _ (by simp [SAT.Lit.getVar])
          | tail _ h2 => cases h2
      have hWF3 : EncState.WellFormed (EncState.addClause b
          (EncState.addClause b st1 [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w')])
          [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w'.ti)]) := by
        apply EncState.addClause_wf hWF2
        simp only [EncState.addClause_nextFresh]; exact hC2
      -- Clause 3: [neg Mem, neg PreEq, pos y]
      have hC3 : clauseFreshBelow [SAT.Lit.neg (Var.Mem t' w'), SAT.Lit.neg (Var.PreEq w.ti w'.ti),
          SAT.Lit.pos (FVar.toVar b y)] st1.nextFresh := by
        intro lit hLit
        cases hLit with
        | head => exact hNonFreshBelow _ (by simp [SAT.Lit.getVar])
        | tail _ h => cases h with
          | head => exact hNonFreshBelow _ (by simp [SAT.Lit.getVar])
          | tail _ h2 => cases h2 with
            | head => exact hYBelow _ rfl
            | tail _ h3 => cases h3
      apply EncState.addClause_wf hWF3
      simp only [EncState.addClause_nextFresh]; exact hC3

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkOw_wf (b : Bounds S) (t : b.times) (w : WId b) (d : FVar b) (st : EncState b)
    (hWF : EncState.WellFormed st)
    (hDBelow : d.id < st.nextFresh) :
    EncState.WellFormed (mkOw b t w d st).2 := by
  -- mkOw does: allocFresh, then 3 addClause operations
  -- Clauses: [neg o, neg Mem, pos d], [pos o, pos Mem], [pos o, neg d]
  unfold mkOw
  cases hAlloc : EncState.allocFresh b st with
  | mk o st1 =>
      have hOId : o.id = st.nextFresh := by
        simpa [hAlloc] using EncState.allocFresh_fst (b := b) (st := st)
      have hSt1Next : st1.nextFresh = st.nextFresh + 1 := by
        simpa [hAlloc] using EncState.allocFresh_nextFresh (b := b) (st := st)
      have hWF1 : EncState.WellFormed st1 := by
        simpa [hAlloc] using EncState.allocFresh_wf (b := b) (st := st) hWF
      have hOLt : o.id < st1.nextFresh := by omega
      have hDLt : d.id < st1.nextFresh := by omega
      simp only
      -- Helper: Fresh o is below st1.nextFresh
      have hOBelow : ∀ lit, lit.getVar = FVar.toVar b o → litFreshBelow lit st1.nextFresh := by
        intro lit hLitVar
        simp only [litFreshBelow, hLitVar, FVar.toVar, hOLt]
      -- Helper: Fresh d is below st1.nextFresh
      have hDBelow' : ∀ lit, lit.getVar = FVar.toVar b d → litFreshBelow lit st1.nextFresh := by
        intro lit hLitVar
        simp only [litFreshBelow, hLitVar, FVar.toVar, hDLt]
      -- Helper: non-Fresh literals are always fresh-below
      have hNonFreshBelow : ∀ (lit : SAT.Lit (Var b)), (∀ n, lit.getVar ≠ Var.Fresh n) →
          litFreshBelow lit st1.nextFresh := by
        intro lit hNonFresh
        unfold litFreshBelow
        cases hv : lit.getVar with
        | Fresh n => exact absurd hv (hNonFresh n)
        | _ => trivial
      -- Clause 1: [neg o, neg Mem, pos d]
      have hC1 : clauseFreshBelow [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w),
          SAT.Lit.pos (FVar.toVar b d)] st1.nextFresh := by
        intro lit hLit
        cases hLit with
        | head => exact hOBelow _ rfl
        | tail _ h => cases h with
          | head => exact hNonFreshBelow _ (by simp [SAT.Lit.getVar])
          | tail _ h2 => cases h2 with
            | head => exact hDBelow' _ rfl
            | tail _ h3 => cases h3
      have hWF2 := EncState.addClause_wf hWF1 _ hC1
      -- Clause 2: [pos o, pos Mem]
      have hC2 : clauseFreshBelow [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)]
          st1.nextFresh := by
        intro lit hLit
        cases hLit with
        | head => exact hOBelow _ rfl
        | tail _ h => cases h with
          | head => exact hNonFreshBelow _ (by simp [SAT.Lit.getVar])
          | tail _ h2 => cases h2
      set st2 := EncState.addClause b st1
          [SAT.Lit.neg (FVar.toVar b o), SAT.Lit.neg (Var.Mem t w), SAT.Lit.pos (FVar.toVar b d)]
      have hSt2Next : st2.nextFresh = st1.nextFresh := EncState.addClause_nextFresh b st1 _
      have hWF3 : EncState.WellFormed (EncState.addClause b st2
          [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.pos (Var.Mem t w)]) := by
        apply EncState.addClause_wf hWF2
        rw [hSt2Next]; exact hC2
      -- Clause 3: [pos o, neg d]
      have hC3 : clauseFreshBelow [SAT.Lit.pos (FVar.toVar b o), SAT.Lit.neg (FVar.toVar b d)]
          st1.nextFresh := by
        intro lit hLit
        cases hLit with
        | head => exact hOBelow _ rfl
        | tail _ h => cases h with
          | head => exact hDBelow' _ rfl
          | tail _ h2 => cases h2
      apply EncState.addClause_wf hWF3
      simp only [EncState.addClause_nextFresh]; exact hC3

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma mkDw_wf (b : Bounds S) (t' : b.times) (w : WId b) (st : EncState b)
    (hWF : EncState.WellFormed st) :
    EncState.WellFormed (mkDw b t' w st).2 := by
  classical
  unfold mkDw
  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w') with hCandsDef
  cases hCands : cands with
  | nil =>
      -- Empty case: allocFresh + addClause [neg d]
      simp only
      cases hAlloc : EncState.allocFresh b st with
      | mk d st1 =>
          have hDId : d.id = st.nextFresh := by
            simpa [hAlloc] using EncState.allocFresh_fst (b := b) (st := st)
          have hSt1Next : st1.nextFresh = st.nextFresh + 1 := by
            simpa [hAlloc] using EncState.allocFresh_nextFresh (b := b) (st := st)
          have hWF1 : EncState.WellFormed st1 := by
            simpa [hAlloc] using EncState.allocFresh_wf (b := b) (st := st) hWF
          have hDLt : d.id < st1.nextFresh := by omega
          simp only
          apply EncState.addClause_wf hWF1
          intro lit hLit
          cases hLit with
          | head =>
              simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar, hDLt]
          | tail _ h => cases h
  | cons w0 ws =>
      -- Non-empty case: fold over cands with mkY, then mkBigOrIff
      simp only
      -- Need to show the fold preserves WF and the y-vars are below nextFresh
      -- Then apply mkBigOrIff_wf
      let step := fun (acc : List (Var b) × EncState b) (w' : WId b) =>
          let (vs, st') := acc
          let (y, st'') := mkY b t' w w' st'
          (FVar.toVar b y :: vs, st'')
      -- The fold result: ((w0 :: ws).foldl step ([], st))
      -- Helper lemma: fold step preserves WF and tracks Fresh indices
      have hFoldInv : ∀ (ws' : List (WId b)) (init : List (Var b) × EncState b),
          EncState.WellFormed init.2 →
          (∀ v ∈ init.1, ∀ n, v = Var.Fresh n → n < init.2.nextFresh) →
          EncState.WellFormed (ws'.foldl step init).2 ∧
          (∀ v ∈ (ws'.foldl step init).1, ∀ n, v = Var.Fresh n →
              n < (ws'.foldl step init).2.nextFresh) := by
        intro ws' init hWFInit hVsInit
        induction ws' generalizing init with
        | nil =>
            simp only [List.foldl_nil]
            exact ⟨hWFInit, hVsInit⟩
        | cons w'' wws' ih =>
            simp only [List.foldl_cons]
            -- step init w'' = (y :: init.1, (mkY ...).2)
            simp only [step]
            generalize hRes : mkY b t' w w'' init.2 = res at *
            rcases res with ⟨y, stY⟩
            have hWFY : EncState.WellFormed stY := by
              have := mkY_wf b t' w w'' init.2 hWFInit
              rw [hRes] at this; exact this
            have hYId : y.id = init.2.nextFresh := by
              have := mkY_fst_id b t' w w'' init.2
              rw [hRes] at this; exact this
            have hStYNext : stY.nextFresh = init.2.nextFresh + 1 := by
              have := mkY_nextFresh b t' w w'' init.2
              rw [hRes] at this; exact this
            have hVsY : ∀ v ∈ (FVar.toVar b y :: init.1), ∀ n, v = Var.Fresh n →
                n < stY.nextFresh := by
              intro v'' hv'' n'' hFresh''
              cases hv'' with
              | head =>
                  simp only [FVar.toVar] at hFresh''
                  cases hFresh''; simp only [hYId, hStYNext]; omega
              | tail _ hInit =>
                  have h := hVsInit v'' hInit n'' hFresh''
                  rw [hStYNext]; omega
            exact ih (FVar.toVar b y :: init.1, stY) hWFY hVsY
      have hFoldRes := hFoldInv (w0 :: ws) ([], st) hWF (by intro _ hMem; simp at hMem)
      exact mkBigOrIff_wf b _ _ hFoldRes.1 hFoldRes.2

-- ============================================================================
-- Structural Determinism lemmas
-- ============================================================================

-- Structural determinism for mkY: if σ satisfies clauses from mkY at st,
-- then σ' (with Fresh vars shifted) satisfies clauses from mkY at st'.
--
-- Proof strategy:
-- - Use mkY_clauses_eq_append to case split on new clauses vs inherited
-- - New clauses: 3 clauses use y = Fresh(st.nextFresh), σ' unshifts to σ(Fresh st.nextFresh)
-- - Inherited: well-formedness ensures Fresh vars < st'.nextFresh, so σ' = σ on these
omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkY_structural_determinism (b : Bounds S) (t' : b.times) (w w' : WId b)
    (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st')
    (σ : SAT.Assignment (Var b))
    (hSat : (mkY b t' w w' st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hSatBase : st'.clauses.all (SAT.Clause.eval σ) = true) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n =>
          if n < st'.nextFresh then σ v
          else σ (Var.Fresh (n - offset))
      | _ => σ v
    (mkY b t' w w' st').2.clauses.all (SAT.Clause.eval σ') = true := by
  intro σ'
  -- Get clause structure for both st and st'
  have hClausesSt := mkY_clauses_eq_append b t' w w' st
  have hClausesSt' := mkY_clauses_eq_append b t' w w' st'
  -- Get the fresh variable indices
  have hYId := mkY_fst_id b t' w w' st
  have hY'Id := mkY_fst_id b t' w w' st'

  rw [hClausesSt'] at *
  rw [List.all_eq_true]
  intro clause hClause

  -- Case split: clause is in new clauses or inherited from st'
  cases List.mem_append.mp hClause with
  | inr hInherited =>
      -- Inherited from st': use hSatBase + well-formedness
      have hEval := List.all_eq_true.mp hSatBase clause hInherited
      rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEval ⊢
      obtain ⟨lit, hLitMem, hLitTrue⟩ := hEval
      refine ⟨lit, hLitMem, ?_⟩
      -- For inherited clauses, Fresh vars < st'.nextFresh, so σ' = σ
      have hClauseWF := hWF clause hInherited
      cases lit with
      | pos v =>
          simp only [SAT.Lit.eval] at hLitTrue ⊢
          cases v with
          | Fresh n =>
              have hLt : n < st'.nextFresh := by
                have h := hClauseWF (SAT.Lit.pos (Var.Fresh n)) hLitMem
                simp only [litFreshBelow, SAT.Lit.getVar] at h; exact h
              simp only [σ', hLt, ↓reduceIte]; exact hLitTrue
          | _ => simp only [σ']; exact hLitTrue
      | neg v =>
          simp only [SAT.Lit.eval] at hLitTrue ⊢
          cases v with
          | Fresh n =>
              have hLt : n < st'.nextFresh := by
                have h := hClauseWF (SAT.Lit.neg (Var.Fresh n)) hLitMem
                simp only [litFreshBelow, SAT.Lit.getVar] at h; exact h
              simp only [σ', hLt, ↓reduceIte]; exact hLitTrue
          | _ => simp only [σ']; exact hLitTrue

  | inl hNew =>
      -- New clause: one of the 3 clauses from mkY at st'
      -- y' = Fresh(st'.nextFresh), so σ'(y') = σ(Fresh(st.nextFresh)) = σ(y)
      rw [hClausesSt] at hSat
      have hSatNew := List.all_eq_true.mp hSat

      -- Key: y'.id = st'.nextFresh, y.id = st.nextFresh
      -- σ'(Fresh st'.nextFresh) = σ(Fresh(st'.nextFresh - offset)) = σ(Fresh st.nextFresh)
      have hY'Ge : (mkY b t' w w' st').1.id ≥ st'.nextFresh := by
        rw [hY'Id]
      have hY'Shift : (mkY b t' w w' st').1.id - offset = (mkY b t' w w' st).1.id := by
        rw [hY'Id, hYId, hOffset]
        omega

      -- Abbreviate clause structures for st
      let c1 := [SAT.Lit.neg (Var.Mem t' w'),
                 SAT.Lit.neg (Var.PreEq w.ti w'.ti),
                 SAT.Lit.pos (FVar.toVar b (mkY b t' w w' st).1)]
      let c2 := [SAT.Lit.neg (FVar.toVar b (mkY b t' w w' st).1),
                 SAT.Lit.pos (Var.PreEq w.ti w'.ti)]
      let c3 := [SAT.Lit.neg (FVar.toVar b (mkY b t' w w' st).1),
                 SAT.Lit.pos (Var.Mem t' w')]

      -- Membership in st's new clauses
      have hC1Mem : c1 ∈ [c1, c2, c3] ++ st.clauses := by simp
      have hC2Mem : c2 ∈ [c1, c2, c3] ++ st.clauses := by simp
      have hC3Mem : c3 ∈ [c1, c2, c3] ++ st.clauses := by simp

      -- Prove each of the 3 new clauses
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hNew
      rcases hNew with hC1' | hC2' | hC3'
      · -- Clause 1: [¬Mem t' w', ¬PreEq w.ti w'.ti, y']
        rw [hC1']
        have hSatC1 := hSatNew c1 hC1Mem
        rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC1 ⊢
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC1
        simp only [c1, List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
        rcases hLitMem with hL1 | hL2 | hL3
        · -- ¬Mem t' w' - non-Fresh, σ' = σ
          refine ⟨SAT.Lit.neg (Var.Mem t' w'), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ']
          subst hL1; simp only [SAT.Lit.eval] at hLitTrue; exact hLitTrue
        · -- ¬PreEq w.ti w'.ti - non-Fresh, σ' = σ
          refine ⟨SAT.Lit.neg (Var.PreEq w.ti w'.ti), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ']
          subst hL2; simp only [SAT.Lit.eval] at hLitTrue; exact hLitTrue
        · -- y' - Fresh, need σ'(y') = σ(y)
          refine ⟨SAT.Lit.pos (FVar.toVar b (mkY b t' w w' st').1), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hY'Ge, ↓reduceIte, hY'Shift]
          subst hL3; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue
      · -- Clause 2: [¬y', PreEq w.ti w'.ti]
        rw [hC2']
        have hSatC2 := hSatNew c2 hC2Mem
        rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC2 ⊢
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC2
        simp only [c2, List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
        rcases hLitMem with hL1 | hL2
        · -- ¬y' - Fresh
          refine ⟨SAT.Lit.neg (FVar.toVar b (mkY b t' w w' st').1), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hY'Ge, ↓reduceIte, hY'Shift]
          subst hL1; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue
        · -- PreEq w.ti w'.ti - non-Fresh
          refine ⟨SAT.Lit.pos (Var.PreEq w.ti w'.ti), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ']
          subst hL2; simp only [SAT.Lit.eval] at hLitTrue; exact hLitTrue
      · -- Clause 3: [¬y', Mem t' w']
        rw [hC3']
        have hSatC3 := hSatNew c3 hC3Mem
        rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC3 ⊢
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC3
        simp only [c3, List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
        rcases hLitMem with hL1 | hL2
        · -- ¬y' - Fresh
          refine ⟨SAT.Lit.neg (FVar.toVar b (mkY b t' w w' st').1), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hY'Ge, ↓reduceIte, hY'Shift]
          subst hL1; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue
        · -- Mem t' w' - non-Fresh
          refine ⟨SAT.Lit.pos (Var.Mem t' w'), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ']
          subst hL2; simp only [SAT.Lit.eval] at hLitTrue; exact hLitTrue

-- Structural determinism for mkOw. Similar to mkY, but additionally handles
-- the shifted input variable d (d'.id = d.id + offset).
omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
lemma mkOw_structural_determinism (b : Bounds S) (t : b.times) (w : WId b)
    (d d' : FVar b) (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st')
    (hDShift : d'.id = d.id + offset)
    (hDGe : d.id ≥ st.nextFresh)
    (σ : SAT.Assignment (Var b))
    (hSat : (mkOw b t w d st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hSatBase : st'.clauses.all (SAT.Clause.eval σ) = true) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n =>
          if n < st'.nextFresh then σ v
          else σ (Var.Fresh (n - offset))
      | _ => σ v
    (mkOw b t w d' st').2.clauses.all (SAT.Clause.eval σ') = true := by
  intro σ'
  -- Get clause structure for both st and st'
  have hClausesSt := mkOw_clauses_eq_append b t w d st
  have hClausesSt' := mkOw_clauses_eq_append b t w d' st'
  -- Get the fresh variable indices
  have hOId := mkOw_fst_id b t w d st
  have hO'Id := mkOw_fst_id b t w d' st'

  rw [hClausesSt'] at *
  rw [List.all_eq_true]
  intro clause hClause

  -- Case split: clause is in new clauses or inherited from st'
  cases List.mem_append.mp hClause with
  | inr hInherited =>
      -- Inherited from st': use hSatBase + well-formedness (same as mkY)
      have hEval := List.all_eq_true.mp hSatBase clause hInherited
      rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEval ⊢
      obtain ⟨lit, hLitMem, hLitTrue⟩ := hEval
      refine ⟨lit, hLitMem, ?_⟩
      have hClauseWF := hWF clause hInherited
      cases lit with
      | pos v =>
          simp only [SAT.Lit.eval] at hLitTrue ⊢
          cases v with
          | Fresh n =>
              have hLt : n < st'.nextFresh := by
                have h := hClauseWF (SAT.Lit.pos (Var.Fresh n)) hLitMem
                simp only [litFreshBelow, SAT.Lit.getVar] at h; exact h
              simp only [σ', hLt, ↓reduceIte]; exact hLitTrue
          | _ => simp only [σ']; exact hLitTrue
      | neg v =>
          simp only [SAT.Lit.eval] at hLitTrue ⊢
          cases v with
          | Fresh n =>
              have hLt : n < st'.nextFresh := by
                have h := hClauseWF (SAT.Lit.neg (Var.Fresh n)) hLitMem
                simp only [litFreshBelow, SAT.Lit.getVar] at h; exact h
              simp only [σ', hLt, ↓reduceIte]; exact hLitTrue
          | _ => simp only [σ']; exact hLitTrue

  | inl hNew =>
      -- New clause: one of the 3 clauses from mkOw at st'
      rw [hClausesSt] at hSat
      have hSatNew := List.all_eq_true.mp hSat

      -- Key arithmetic relationships
      -- o'.id = st'.nextFresh, o.id = st.nextFresh
      -- σ'(Fresh st'.nextFresh) = σ(Fresh st.nextFresh)
      have hO'Ge : (mkOw b t w d' st').1.id ≥ st'.nextFresh := by rw [hO'Id]
      have hO'Shift : (mkOw b t w d' st').1.id - offset = (mkOw b t w d st).1.id := by
        rw [hO'Id, hOId, hOffset]; omega
      -- d'.id = d.id + offset, and d.id >= st.nextFresh implies d'.id >= st'.nextFresh
      have hD'Ge : d'.id ≥ st'.nextFresh := by
        rw [hDShift, hOffset]; omega
      have hD'Shift : d'.id - offset = d.id := by
        rw [hDShift]; omega

      -- Abbreviate clause structures for st
      let c1 := [SAT.Lit.pos (FVar.toVar b (mkOw b t w d st).1), SAT.Lit.neg (FVar.toVar b d)]
      let c2 := [SAT.Lit.pos (FVar.toVar b (mkOw b t w d st).1), SAT.Lit.pos (Var.Mem t w)]
      let c3 := [SAT.Lit.neg (FVar.toVar b (mkOw b t w d st).1), SAT.Lit.neg (Var.Mem t w),
                 SAT.Lit.pos (FVar.toVar b d)]

      have hC1Mem : c1 ∈ [c1, c2, c3] ++ st.clauses := by simp
      have hC2Mem : c2 ∈ [c1, c2, c3] ++ st.clauses := by simp
      have hC3Mem : c3 ∈ [c1, c2, c3] ++ st.clauses := by simp

      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hNew
      rcases hNew with hC1' | hC2' | hC3'
      · -- Clause 1: [o', ¬d']
        rw [hC1']
        have hSatC1 := hSatNew c1 hC1Mem
        rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC1 ⊢
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC1
        simp only [c1, List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
        rcases hLitMem with hL1 | hL2
        · -- o' - Fresh
          refine ⟨SAT.Lit.pos (FVar.toVar b (mkOw b t w d' st').1), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hO'Ge, ↓reduceIte, hO'Shift]
          subst hL1; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue
        · -- ¬d' - Fresh
          refine ⟨SAT.Lit.neg (FVar.toVar b d'), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hD'Ge, ↓reduceIte, hD'Shift]
          subst hL2; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue
      · -- Clause 2: [o', Mem t w]
        rw [hC2']
        have hSatC2 := hSatNew c2 hC2Mem
        rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC2 ⊢
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC2
        simp only [c2, List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
        rcases hLitMem with hL1 | hL2
        · -- o' - Fresh
          refine ⟨SAT.Lit.pos (FVar.toVar b (mkOw b t w d' st').1), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hO'Ge, ↓reduceIte, hO'Shift]
          subst hL1; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue
        · -- Mem t w - non-Fresh
          refine ⟨SAT.Lit.pos (Var.Mem t w), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ']
          subst hL2; simp only [SAT.Lit.eval] at hLitTrue; exact hLitTrue
      · -- Clause 3: [¬o', ¬Mem t w, d']
        rw [hC3']
        have hSatC3 := hSatNew c3 hC3Mem
        rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC3 ⊢
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC3
        simp only [c3, List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
        rcases hLitMem with hL1 | hL2 | hL3
        · -- ¬o' - Fresh
          refine ⟨SAT.Lit.neg (FVar.toVar b (mkOw b t w d' st').1), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hO'Ge, ↓reduceIte, hO'Shift]
          subst hL1; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue
        · -- ¬Mem t w - non-Fresh
          refine ⟨SAT.Lit.neg (Var.Mem t w), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ']
          subst hL2; simp only [SAT.Lit.eval] at hLitTrue; exact hLitTrue
        · -- d' - Fresh
          refine ⟨SAT.Lit.pos (FVar.toVar b d'), by simp, ?_⟩
          simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hD'Ge, ↓reduceIte, hD'Shift]
          subst hL3; simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue; exact hLitTrue

-- ============================================================================
-- mkDw structural determinism helpers
-- ============================================================================

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: folds through same cands list produce lists of same length. -/
lemma mkDw_fold_length_eq (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (st st' : EncState b) :
    let step := fun (acc : List (Var b) × EncState b) w'' =>
      let (vs, st'') := acc
      let (y, st''') := mkY b t' w w'' st''
      (FVar.toVar b y :: vs, st''')
    (cands.foldl step ([], st)).1.length = (cands.foldl step ([], st')).1.length := by
  intro step
  -- Generalize to arbitrary initial lists of same length
  suffices h : ∀ initVs initVs' : List (Var b), ∀ initSt initSt' : EncState b,
      initVs.length = initVs'.length →
      (cands.foldl step (initVs, initSt)).1.length =
        (cands.foldl step (initVs', initSt')).1.length by
    exact h [] [] st st' rfl
  intro initVs initVs' initSt initSt' hLen
  induction cands generalizing initVs initVs' initSt initSt' with
  | nil => simp only [List.foldl_nil, hLen]
  | cons w'' cands' ih =>
    simp only [List.foldl_cons, step]
    apply ih
    simp only [List.length_cons, hLen]

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Helper: pointwise shift relation between fold results.
    Key: if foldRes.1.get? i = some (Fresh n),
    then foldRes'.1.get? i = some (Fresh (n + offset)). -/
lemma mkDw_fold_pointwise_shift (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh) :
    let step := fun (acc : List (Var b) × EncState b) w'' =>
      let (vs, st'') := acc
      let (y, st''') := mkY b t' w w'' st''
      (FVar.toVar b y :: vs, st''')
    let foldRes := cands.foldl step ([], st)
    let foldRes' := cands.foldl step ([], st')
    ∀ (i : Nat) n, foldRes.1[i]? = some (Var.Fresh n) →
        foldRes'.1[i]? = some (Var.Fresh (n + offset)) := by
  intro step
  -- Prove using a stronger induction hypothesis about arbitrary init states
  suffices h : ∀ initVs initVs' : List (Var b),
      ∀ initSt initSt' : EncState b,
      initVs.length = initVs'.length →
      (∀ j n', initVs[j]? = some (Var.Fresh n') →
          initVs'[j]? = some (Var.Fresh (n' + offset))) →
      offset = initSt'.nextFresh - initSt.nextFresh →
      initSt.nextFresh ≤ initSt'.nextFresh →
      ∀ j n', (cands.foldl step (initVs, initSt)).1[j]? = some (Var.Fresh n') →
          (cands.foldl step (initVs', initSt')).1[j]? = some (Var.Fresh (n' + offset)) by
    exact h [] [] st st' rfl (fun _ _ hJ => nomatch (List.getElem?_nil ▸ hJ)) hOffset hMono
  intro initVs initVs' initSt initSt' hLen hPW hOff hMonoInit
  induction cands generalizing initVs initVs' initSt initSt' with
  | nil =>
    simp only [List.foldl_nil]
    exact hPW
  | cons w'' cands' ih =>
    simp only [List.foldl_cons, step]
    have hYId := mkY_fst_id b t' w w'' initSt
    have hY'Id := mkY_fst_id b t' w w'' initSt'
    have hYNext := mkY_nextFresh b t' w w'' initSt
    have hY'Next := mkY_nextFresh b t' w w'' initSt'
    apply ih
    · simp only [List.length_cons, hLen]
    · intro j n' hGet'
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet' ⊢
        simp only [FVar.toVar] at hGet'
        cases hGet'
        simp only [FVar.toVar, hYId, hY'Id]
        congr 1
        omega
      | succ k =>
        simp only [List.getElem?_cons_succ] at hGet' ⊢
        exact hPW k n' hGet'
    · rw [hYNext, hY'Next, hOff]; omega
    · rw [hYNext, hY'Next]; omega

-- ============================================================================
-- mkDw fold structural determinism helper
-- ============================================================================

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Structural determinism for mkDw fold: if σ satisfies fold clauses at st,
    then σ' satisfies fold clauses at st', where the offset is constant.

    Key insight: For each clause in foldRes'.2, either it's inherited from st'
    (Fresh vars < st'.nextFresh, so σ' = σ) or it's from some mkY step
    (use direct transfer of corresponding literals). -/
lemma mkDw_fold_structural_determinism (b : Bounds S) (t' : b.times) (w : WId b)
    (cands : List (WId b)) (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st')
    (σ : SAT.Assignment (Var b))
    (hSatBase : st'.clauses.all (SAT.Clause.eval σ) = true) :
    let step := fun (acc : List (Var b) × EncState b) w'' =>
      let (vs, st'') := acc
      let (y, st''') := mkY b t' w w'' st''
      (FVar.toVar b y :: vs, st''')
    let foldRes := cands.foldl step ([], st)
    let foldRes' := cands.foldl step ([], st')
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => if n < st'.nextFresh then σ v else σ (Var.Fresh (n - offset))
      | _ => σ v
    foldRes.2.clauses.all (SAT.Clause.eval σ) = true →
    foldRes'.2.clauses.all (SAT.Clause.eval σ') = true := by
  intro step foldRes foldRes' σ' hSatFold
  rw [List.all_eq_true]
  intro clause hClause
  -- For any clause in foldRes'.2, either:
  -- 1. It's inherited from st' (Fresh vars < st'.nextFresh)
  -- 2. It's from some mkY step during the fold
  by_cases hInherited : clause ∈ st'.clauses
  · -- Inherited from st': Fresh vars < st'.nextFresh, so σ' = σ
    have hEval := List.all_eq_true.mp hSatBase clause hInherited
    rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEval ⊢
    obtain ⟨lit, hMem, hTrue⟩ := hEval
    refine ⟨lit, hMem, ?_⟩
    have hClauseWF := hWF clause hInherited
    cases lit with
    | pos v =>
        simp only [SAT.Lit.eval] at hTrue ⊢
        cases v with
        | Fresh n =>
            have hLt : n < st'.nextFresh := by
              have h := hClauseWF (SAT.Lit.pos (Var.Fresh n)) hMem
              simp only [litFreshBelow, SAT.Lit.getVar] at h; exact h
            simp only [σ', hLt, ↓reduceIte]; exact hTrue
        | _ => simp only [σ']; exact hTrue
    | neg v =>
        simp only [SAT.Lit.eval] at hTrue ⊢
        cases v with
        | Fresh n =>
            have hLt : n < st'.nextFresh := by
              have h := hClauseWF (SAT.Lit.neg (Var.Fresh n)) hMem
              simp only [litFreshBelow, SAT.Lit.getVar] at h; exact h
            simp only [σ', hLt, ↓reduceIte]; exact hTrue
        | _ => simp only [σ']; exact hTrue
  · -- Not inherited: clause is from some mkY step in the fold
    -- Direct proof using clause correspondence and sd_from_correspondence
    -- Key: σ' has threshold st'.nextFresh, and for Fresh vars >= st'.nextFresh,
    -- σ'(Fresh n) = σ(Fresh (n - offset)). This handles all mkY vars in the fold.
    have hFoldInv : ∀ (candList : List (WId b)),
        ∀ initVs initVs' : List (Var b),
        ∀ stI stI' : EncState b,
        stI'.nextFresh - stI.nextFresh = offset →
        stI.nextFresh ≤ stI'.nextFresh →
        st'.nextFresh ≤ stI'.nextFresh →  -- Track that stI' is "after" st'
        (candList.foldl step (initVs, stI)).2.clauses.all (SAT.Clause.eval σ) = true →
        clause ∈ (candList.foldl step (initVs', stI')).2.clauses →
        clause ∉ stI'.clauses →
        SAT.Clause.eval σ' clause = true := by
      intro candList
      induction candList with
      | nil =>
          intro initVs initVs' stI stI' hOffsetI hMonoI hGeSt' hSatFoldI hClauseIn hNotInBase
          simp only [List.foldl_nil] at hClauseIn
          exact absurd hClauseIn hNotInBase
      | cons w'' cands' ih =>
          intro initVs initVs' stI stI' hOffsetI hMonoI hGeSt' hSatFoldI hClauseIn hNotInBase
          simp only [List.foldl_cons, step] at hClauseIn hSatFoldI
          have hYNext := mkY_nextFresh b t' w w'' stI
          have hY'Next := mkY_nextFresh b t' w w'' stI'
          have hOffsetY : (mkY b t' w w'' stI').2.nextFresh - (mkY b t' w w'' stI).2.nextFresh
              = offset := by rw [hYNext, hY'Next]; omega
          have hMonoY : (mkY b t' w w'' stI).2.nextFresh ≤ (mkY b t' w w'' stI').2.nextFresh := by
            rw [hYNext, hY'Next]; omega
          have hGeStY : st'.nextFresh ≤ (mkY b t' w w'' stI').2.nextFresh := by
            rw [hY'Next]; omega
          have hAppendY := mkY_clauses_eq_append b t' w w'' stI'
          have hAppendYI := mkY_clauses_eq_append b t' w w'' stI
          have hYId := mkY_fst_id b t' w w'' stI
          have hY'Id := mkY_fst_id b t' w w'' stI'
          -- Check if clause is a NEW mkY clause at this step
          by_cases hInMkYNew : clause ∈
              [[SAT.Lit.neg (Var.Mem t' w''), SAT.Lit.neg (Var.PreEq w.ti w''.ti),
                SAT.Lit.pos (FVar.toVar b (mkY b t' w w'' stI').1)],
               [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI').1),
                SAT.Lit.pos (Var.PreEq w.ti w''.ti)],
               [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI').1),
                SAT.Lit.pos (Var.Mem t' w'')]]
          · -- Clause is a NEW clause from this mkY step at stI'
            -- Find corresponding clause at stI and show σ satisfies it
            -- Then use the fact that clause corresponds with offset to transfer via σ'
            have hSatMkYI : (mkY b t' w w'' stI).2.clauses.all (SAT.Clause.eval σ) = true := by
              rw [List.all_eq_true] at hSatFoldI ⊢
              intro c hc
              apply hSatFoldI
              -- Show c ∈ (foldl step (mkY..stI) cands').2.clauses using foldl_subset_snd
              -- After simp, hSatFoldI is about foldl from ((mkY..).1 :: initVs, (mkY..).2)
              -- hc : c ∈ (mkY b t' w w'' stI).2.clauses
              -- Need: c ∈ foldl step ((mkY..).1 :: initVs, (mkY..).2) cands').2.clauses
              have hStepSub : ∀ acc w''', acc.2.clauses ⊆ (step acc w''').2.clauses := by
                intro acc w'''
                simp only [step]
                exact mkY_clauses_subset b t' w w''' acc.2
              let mkYRes := (FVar.toVar b (mkY b t' w w'' stI).1 :: initVs, (mkY b t' w w'' stI).2)
              have hSubset := foldl_subset_snd step hStepSub cands' mkYRes
              exact hSubset hc
            -- Case split on which of the 3 clauses
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hInMkYNew
            rcases hInMkYNew with hC1 | hC2 | hC3
            · -- Clause 1: [¬Mem t' w'', ¬PreEq w.ti w''.ti, y']
              subst hC1
              -- Corresponding clause at stI: [¬Mem t' w'', ¬PreEq w.ti w''.ti, y]
              have hC1_stI : [SAT.Lit.neg (Var.Mem t' w''), SAT.Lit.neg (Var.PreEq w.ti w''.ti),
                  SAT.Lit.pos (FVar.toVar b (mkY b t' w w'' stI).1)] ∈
                  (mkY b t' w w'' stI).2.clauses := by rw [hAppendYI]; simp
              have hSatC1 := List.all_eq_true.mp hSatMkYI _ hC1_stI
              rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC1 ⊢
              obtain ⟨lit, hMem, hTrue⟩ := hSatC1
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
              rcases hMem with hL1 | hL2 | hL3
              · -- ¬Mem: non-Fresh, σ' = σ
                exact ⟨SAT.Lit.neg (Var.Mem t' w''), by simp,
                  by subst hL1; simp only [σ', SAT.Lit.eval]; exact hTrue⟩
              · -- ¬PreEq: non-Fresh, σ' = σ
                exact ⟨SAT.Lit.neg (Var.PreEq w.ti w''.ti), by simp,
                  by subst hL2; simp only [σ', SAT.Lit.eval]; exact hTrue⟩
              · -- y': Fresh, need σ'(y') = σ(y)
                refine ⟨SAT.Lit.pos (FVar.toVar b (mkY b t' w w'' stI').1), by simp, ?_⟩
                simp only [SAT.Lit.eval, σ', FVar.toVar] at hTrue ⊢
                -- y'.id = stI'.nextFresh >= st'.nextFresh, so σ' unshifts
                have hY'Ge : (mkY b t' w w'' stI').1.id ≥ st'.nextFresh := by
                  rw [hY'Id]; exact hGeSt'
                simp only [Nat.not_lt.mpr hY'Ge, ↓reduceIte]
                -- y'.id - offset = stI'.nextFresh - offset = stI.nextFresh = y.id
                have hShift : (mkY b t' w w'' stI').1.id - offset = (mkY b t' w w'' stI).1.id := by
                  rw [hY'Id, hYId]; omega
                rw [hShift]
                subst hL3; exact hTrue
            · -- Clause 2: [¬y', PreEq w.ti w''.ti] - similar
              subst hC2
              have hC2_stI : [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI).1),
                  SAT.Lit.pos (Var.PreEq w.ti w''.ti)] ∈ (mkY b t' w w'' stI).2.clauses := by
                rw [hAppendYI]; simp
              have hSatC2 := List.all_eq_true.mp hSatMkYI _ hC2_stI
              rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC2 ⊢
              obtain ⟨lit, hMem, hTrue⟩ := hSatC2
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
              rcases hMem with hL1 | hL2
              · -- ¬y': Fresh
                refine ⟨SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI').1), by simp, ?_⟩
                simp only [SAT.Lit.eval, σ', FVar.toVar] at hTrue ⊢
                have hY'Ge : (mkY b t' w w'' stI').1.id ≥ st'.nextFresh := by
                  rw [hY'Id]; exact hGeSt'
                simp only [Nat.not_lt.mpr hY'Ge, ↓reduceIte]
                have hShift : (mkY b t' w w'' stI').1.id - offset = (mkY b t' w w'' stI).1.id := by
                  rw [hY'Id, hYId]; omega
                rw [hShift]; subst hL1; exact hTrue
              · -- PreEq: non-Fresh
                exact ⟨SAT.Lit.pos (Var.PreEq w.ti w''.ti), by simp,
                  by subst hL2; simp only [σ', SAT.Lit.eval]; exact hTrue⟩
            · -- Clause 3: [¬y', Mem t' w''] - similar
              subst hC3
              have hC3_stI : [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI).1),
                  SAT.Lit.pos (Var.Mem t' w'')] ∈ (mkY b t' w w'' stI).2.clauses := by
                rw [hAppendYI]; simp
              have hSatC3 := List.all_eq_true.mp hSatMkYI _ hC3_stI
              rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC3 ⊢
              obtain ⟨lit, hMem, hTrue⟩ := hSatC3
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
              rcases hMem with hL1 | hL2
              · -- ¬y': Fresh
                refine ⟨SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI').1), by simp, ?_⟩
                simp only [SAT.Lit.eval, σ', FVar.toVar] at hTrue ⊢
                have hY'Ge : (mkY b t' w w'' stI').1.id ≥ st'.nextFresh := by
                  rw [hY'Id]; exact hGeSt'
                simp only [Nat.not_lt.mpr hY'Ge, ↓reduceIte]
                have hShift : (mkY b t' w w'' stI').1.id - offset = (mkY b t' w w'' stI).1.id := by
                  rw [hY'Id, hYId]; omega
                rw [hShift]; subst hL1; exact hTrue
              · -- Mem: non-Fresh
                exact ⟨SAT.Lit.pos (Var.Mem t' w''), by simp,
                  by subst hL2; simp only [σ', SAT.Lit.eval]; exact hTrue⟩
          · -- Clause from later fold step
            by_cases hInMkYClauses : clause ∈ (mkY b t' w w'' stI').2.clauses
            · -- In mkY output but not a new clause, so must be inherited from stI'
              rw [hAppendY] at hInMkYClauses
              cases List.mem_append.mp hInMkYClauses with
              | inl hNew => exact absurd hNew hInMkYNew
              | inr hInh => exact absurd hInh hNotInBase
            · -- Not in mkY output at this step, use ih for cands'
              -- ih : ∀ initVs initVs' stI stI', [conditions] → result
              -- We need to apply ih with the post-mkY state
              apply ih
                (FVar.toVar b (mkY b t' w w'' stI).1 :: initVs)
                (FVar.toVar b (mkY b t' w w'' stI').1 :: initVs')
                (mkY b t' w w'' stI).2
                (mkY b t' w w'' stI').2
                hOffsetY hMonoY hGeStY hSatFoldI hClauseIn hInMkYClauses
    have hOffsetInit : st'.nextFresh - st.nextFresh = offset := by omega
    have hGeStInit : st'.nextFresh ≤ st'.nextFresh := Nat.le_refl _
    exact hFoldInv cands [] [] st st' hOffsetInit hMono hGeStInit hSatFold hClause hInherited

-- ============================================================================
-- mkDw structural determinism for NEW clauses only
-- ============================================================================

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- A clause containing a Fresh var with id ≥ threshold cannot be in a WF state's clauses.
    WF states have all Fresh vars in clauses < nextFresh. -/
lemma clause_with_fresh_not_in_wf_clauses (b : Bounds S) (st : EncState b)
    (clause : SAT.Clause (Var b)) (hWF : st.WellFormed)
    (freshId : Nat) (hFreshGe : freshId ≥ st.nextFresh)
    (lit : SAT.Lit (Var b)) (hLitMem : lit ∈ clause)
    (hLitFresh : SAT.Lit.getVar lit = Var.Fresh freshId) :
    clause ∉ st.clauses := by
  intro hIn
  have hClauseWF := hWF _ hIn
  have hLitWF := hClauseWF _ hLitMem
  simp only [litFreshBelow, hLitFresh] at hLitWF
  omega

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- All three mkY clauses contain a Fresh var with id = st.nextFresh.
    Returns the lit, its membership proof, and that its var is Fresh st.nextFresh. -/
lemma mkY_clauses_have_fresh (b : Bounds S) (t' : b.times) (w w'' : WId b) (st : EncState b) :
    let y := (mkY b t' w w'' st).1
    let c1 := [SAT.Lit.neg (Var.Mem t' w''), SAT.Lit.neg (Var.PreEq w.ti w''.ti),
               SAT.Lit.pos (FVar.toVar b y)]
    let c2 := [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.PreEq w.ti w''.ti)]
    let c3 := [SAT.Lit.neg (FVar.toVar b y), SAT.Lit.pos (Var.Mem t' w'')]
    (∃ lit ∈ c1, SAT.Lit.getVar lit = Var.Fresh y.id) ∧
    (∃ lit ∈ c2, SAT.Lit.getVar lit = Var.Fresh y.id) ∧
    (∃ lit ∈ c3, SAT.Lit.getVar lit = Var.Fresh y.id) := by
  constructor
  · exact ⟨SAT.Lit.pos (FVar.toVar b _), by simp, rfl⟩
  constructor
  · exact ⟨SAT.Lit.neg (FVar.toVar b _), by simp, rfl⟩
  · exact ⟨SAT.Lit.neg (FVar.toVar b _), by simp, rfl⟩

omit [DecidableEq S.Value] [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- mkY clauses at state stI are not in st.clauses when stI.nextFresh ≥ st.nextFresh and st is WF.
    The Fresh var y.id = stI.nextFresh ≥ st.nextFresh, so by WF, clause ∉ st.clauses. -/
lemma mkY_clause_not_in_base (b : Bounds S) (t' : b.times) (w w'' : WId b)
    (st stI : EncState b) (hWF : st.WellFormed) (hMono : st.nextFresh ≤ stI.nextFresh)
    (clause : SAT.Clause (Var b))
    (hClause : clause ∈ [[SAT.Lit.neg (Var.Mem t' w''), SAT.Lit.neg (Var.PreEq w.ti w''.ti),
                          SAT.Lit.pos (FVar.toVar b (mkY b t' w w'' stI).1)],
                         [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI).1),
                          SAT.Lit.pos (Var.PreEq w.ti w''.ti)],
                         [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI).1),
                          SAT.Lit.pos (Var.Mem t' w'')]]) :
    clause ∉ st.clauses := by
  have hYId := mkY_fst_id b t' w w'' stI
  have hFreshGe : (mkY b t' w w'' stI).1.id ≥ st.nextFresh := by rw [hYId]; exact hMono
  have ⟨h1, h2, h3⟩ := mkY_clauses_have_fresh b t' w w'' stI
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hClause
  rcases hClause with hC1 | hC2 | hC3
  · subst hC1; obtain ⟨lit, hLitMem, hLitFresh⟩ := h1
    exact clause_with_fresh_not_in_wf_clauses b st _ hWF _ hFreshGe lit hLitMem hLitFresh
  · subst hC2; obtain ⟨lit, hLitMem, hLitFresh⟩ := h2
    exact clause_with_fresh_not_in_wf_clauses b st _ hWF _ hFreshGe lit hLitMem hLitFresh
  · subst hC3; obtain ⟨lit, hLitMem, hLitFresh⟩ := h3
    exact clause_with_fresh_not_in_wf_clauses b st _ hWF _ hFreshGe lit hLitMem hLitFresh

omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
/-- Structural determinism for NEW clauses only from mkDw.
    Unlike mkDw_structural_determinism, this does NOT require satisfaction of ALL clauses.
    It only requires satisfaction of NEW clauses (not inherited from st.clauses). -/
lemma mkDw_newClauses_structural_determinism (b : Bounds S) (t' : b.times) (w : WId b)
    (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : st.WellFormed)
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (mkDw b t' w st).2.clauses, c ∉ st.clauses → SAT.Clause.eval σ c = true)
    (clause : SAT.Clause (Var b))
    (hClauseMem : clause ∈ (mkDw b t' w st').2.clauses)
    (hClauseNotInBase : clause ∉ st'.clauses) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n => if n < st'.nextFresh then σ v else σ (Var.Fresh (n - offset))
      | _ => σ v
    SAT.Clause.eval σ' clause = true := by
  intro σ'
  classical
  unfold mkDw at hClauseMem hSatNew

  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  by_cases hEmpty : cands = []
  · -- Empty case: single clause [neg d'] where d'.id = st'.nextFresh
    simp only [hEmpty] at hClauseMem hSatNew
    cases hAlloc : EncState.allocFresh b st with
    | mk d stA =>
      cases hAlloc' : EncState.allocFresh b st' with
      | mk d' stA' =>
        simp only [hAlloc] at hSatNew
        simp only [hAlloc'] at hClauseMem
        simp only [EncState.addClause, List.mem_cons] at hClauseMem
        rcases hClauseMem with hNew | hOld
        · -- clause = [neg d'] - the single new clause
          have hDId : d.id = st.nextFresh := by
            simpa [hAlloc] using EncState.allocFresh_fst (b := b) (st := st)
          have hD'Id : d'.id = st'.nextFresh := by
            simpa [hAlloc'] using EncState.allocFresh_fst (b := b) (st := st')
          have hD'Ge : d'.id ≥ st'.nextFresh := by rw [hD'Id]
          have hD'Shift : d'.id - offset = d.id := by rw [hD'Id, hDId, hOffset]; omega
          -- Get satisfaction of [neg d] from hSatNew
          -- First show [neg d] is a NEW clause (not in st.clauses)
          have hClauseSt : [SAT.Lit.neg (FVar.toVar b d)] ∈
              (EncState.addClause b stA [SAT.Lit.neg (FVar.toVar b d)]).clauses := by
            simp [EncState.addClause]
          have hClauseNew : [SAT.Lit.neg (FVar.toVar b d)] ∉ st.clauses := by
            intro hIn
            -- The clause has Fresh var d.id = st.nextFresh
            -- By WF, any clause in st.clauses has Fresh vars < st.nextFresh
            have hFreshInClause : SAT.Lit.neg (FVar.toVar b d) ∈
                [SAT.Lit.neg (FVar.toVar b d)] := List.mem_singleton_self _
            have hVarFresh : (SAT.Lit.neg (FVar.toVar b d)).getVar = Var.Fresh d.id := rfl
            have hClauseWF := hWF _ hIn
            have hLitWF := hClauseWF _ hFreshInClause
            simp only [litFreshBelow, hVarFresh] at hLitWF
            omega
          have hSatC := hSatNew _ hClauseSt hClauseNew
          rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC ⊢
          obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC
          simp only [List.mem_singleton] at hLitMem
          subst hLitMem hNew
          refine ⟨SAT.Lit.neg (FVar.toVar b d'), List.mem_singleton_self _, ?_⟩
          simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hD'Ge, ↓reduceIte, hD'Shift]
          simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue
          exact hLitTrue
        · -- clause ∈ stA'.clauses = st'.clauses - contradiction with hClauseNotInBase
          have hStA'Clauses : stA'.clauses = st'.clauses := by
            simpa [hAlloc'] using EncState.allocFresh_clauses_eq (b := b) (st := st')
          rw [hStA'Clauses] at hOld
          exact absurd hOld hClauseNotInBase

  · -- Non-empty case: fold mkY then mkBigOrIff
    have hCandsNe : cands ≠ [] := hEmpty
    simp only [] at hClauseMem hSatNew

    -- Define the fold step function
    let step := fun (acc : List (Var b) × EncState b) w'' =>
      let (vs, st'') := acc
      let (y, st''') := mkY b t' w w'' st''
      (FVar.toVar b y :: vs, st''')

    -- Get the fold results
    let foldRes := cands.foldl step ([], st)
    let foldRes' := cands.foldl step ([], st')

    -- Extract fold satisfaction from hSatNew for NEW clauses only
    have hSatNewFold : ∀ c ∈ foldRes.2.clauses, c ∉ st.clauses →
        SAT.Clause.eval σ c = true := by
      have hSubset := mkBigOrIff_clauses_subset b foldRes.1 foldRes.2
      have hStepEq : step = fun acc w' =>
          (FVar.toVar b (mkY b t' w w' acc.2).1 :: acc.1, (mkY b t' w w' acc.2).2) := by
        funext acc w'; simp only [step]
      intro clause hClause hNotSt
      apply hSatNew
      · simp only [← hStepEq, cands]; exact hSubset hClause
      · exact hNotSt

    -- Key fold facts
    have hFoldNextFresh : foldRes.2.nextFresh = st.nextFresh + cands.length :=
      mkDw_fold_nextFresh b t' w cands ([], st)
    have hFoldNextFresh' : foldRes'.2.nextFresh = st'.nextFresh + cands.length :=
      mkDw_fold_nextFresh b t' w cands ([], st')
    have hFoldOffset : foldRes'.2.nextFresh - foldRes.2.nextFresh = offset := by
      rw [hFoldNextFresh, hFoldNextFresh']; omega

    -- Case split: clause from fold or from mkBigOrIff
    have hAppend := mkBigOrIff_clauses_eq_append b foldRes'.1 foldRes'.2
    rcases hAppend with ⟨newOrIff, hOrIffEq⟩
    rw [hOrIffEq] at hClauseMem
    cases List.mem_append.mp hClauseMem with
    | inl hInOrIff =>
      -- Clause is in newOrIff (mkBigOrIff's new clauses)
      -- mkBigOrIff adds: [¬u', pos v'₁, ..., pos v'ₙ] (long clause)
      -- and [¬v'ᵢ, pos u'] for each v'ᵢ (short clauses)

      -- Get mkBigOrIff satisfaction from hSatNew (NEW clauses only)
      have hSatBigOrNew :
          ∀ c ∈ (mkBigOrIff b foldRes.1 foldRes.2).2.clauses, c ∉ st.clauses →
          SAT.Clause.eval σ c = true := by
        have hStepEq : step = fun acc w' =>
            (FVar.toVar b (mkY b t' w w' acc.2).1 :: acc.1, (mkY b t' w w' acc.2).2) := by
          funext acc w'; simp only [step]
        intro clause hClause hNotSt
        apply hSatNew
        · simp only [← hStepEq, cands]; exact hClause
        · exact hNotSt

      -- All vars in foldRes.1 are Fresh
      have hVsAllFresh : ∀ v ∈ foldRes.1, ∃ n, v = Var.Fresh n := by
        intro v hv
        have hFoldInv : ∀ initVs : List (Var b), ∀ initSt : EncState b,
            (∀ v' ∈ initVs, ∃ m, v' = Var.Fresh m) →
            ∀ v' ∈ (cands.foldl step (initVs, initSt)).1, ∃ m, v' = Var.Fresh m := by
          intro initVs initSt hInit
          induction cands generalizing initVs initSt with
          | nil => exact hInit
          | cons w'' cands' ih =>
            simp only [List.foldl_cons]
            intro v' hv'
            have hStepFst : (step (initVs, initSt) w'').1 =
                FVar.toVar b (mkY b t' w w'' initSt).1 :: initVs := rfl
            apply ih (step (initVs, initSt) w'').1 (step (initVs, initSt) w'').2
            intro v'' hv''
            rw [hStepFst] at hv''
            simp only [List.mem_cons] at hv''
            rcases hv'' with hNew | hOld
            · use (mkY b t' w w'' initSt).1.id; rw [hNew]; rfl
            · exact hInit v'' hOld
            exact hv'
        exact hFoldInv [] st (by intro v' hv'; simp at hv') v hv

      -- All vars in foldRes'.1 are Fresh with indices >= st'.nextFresh
      have hVs'Fresh : ∀ v ∈ foldRes'.1, ∀ n, v = Var.Fresh n →
          st'.nextFresh ≤ n ∧ n < foldRes'.2.nextFresh := by
        intro v hv n hVEq
        constructor
        · -- Lower bound: n >= st'.nextFresh
          have hFoldInv : ∀ initVs : List (Var b), ∀ initSt : EncState b,
              (∀ v' ∈ initVs, ∀ m, v' = Var.Fresh m → st'.nextFresh ≤ m) →
              st'.nextFresh ≤ initSt.nextFresh →
              ∀ v' ∈ (cands.foldl step (initVs, initSt)).1, ∀ m, v' = Var.Fresh m →
                st'.nextFresh ≤ m := by
            intro initVs initSt hInit hBaseLE
            induction cands generalizing initVs initSt with
            | nil => intro v' hv' m hv'Eq; exact hInit v' hv' m hv'Eq
            | cons w'' cands' ih =>
              simp only [List.foldl_cons]
              have hYId := mkY_fst_id b t' w w'' initSt
              have hYNext := mkY_nextFresh b t' w w'' initSt
              intro v' hv' m hv'Eq
              have hStepVs : (step (initVs, initSt) w'').1 =
                  FVar.toVar b (mkY b t' w w'' initSt).1 :: initVs := by simp only [step]
              have hStepNext : (step (initVs, initSt) w'').2.nextFresh = initSt.nextFresh + 1 := by
                simp only [step, hYNext]
              have hNewInit : ∀ u ∈ (step (initVs, initSt) w'').1, ∀ k, u = Var.Fresh k →
                  st'.nextFresh ≤ k := by
                intro u hu k huk
                rw [hStepVs] at hu
                cases hu with
                | head => simp only [FVar.toVar] at huk; cases huk; rw [hYId]; exact hBaseLE
                | tail _ hTail => exact hInit u hTail k huk
              have hBaseLENew : st'.nextFresh ≤ (step (initVs, initSt) w'').2.nextFresh := by
                rw [hStepNext]; omega
              exact ih _ _ hNewInit hBaseLENew v' hv' m hv'Eq
          exact hFoldInv [] st' (by intro v' hv'; simp at hv') (Nat.le_refl _) v hv n hVEq
        · -- Upper bound: n < foldRes'.2.nextFresh
          have hFoldInv : ∀ initVs : List (Var b), ∀ initSt : EncState b,
              (∀ v' ∈ initVs, ∀ m, v' = Var.Fresh m → m < initSt.nextFresh) →
              ∀ v' ∈ (cands.foldl step (initVs, initSt)).1, ∀ m, v' = Var.Fresh m →
                m < (cands.foldl step (initVs, initSt)).2.nextFresh := by
            intro initVs initSt hInit
            induction cands generalizing initVs initSt with
            | nil => exact hInit
            | cons w'' cands' ih =>
              simp only [List.foldl_cons]
              have hYId := mkY_fst_id b t' w w'' initSt
              have hYNext := mkY_nextFresh b t' w w'' initSt
              intro v' hv' m hv'Eq
              have hStepVs : (step (initVs, initSt) w'').1 =
                  FVar.toVar b (mkY b t' w w'' initSt).1 :: initVs := by simp only [step]
              have hStepNext : (step (initVs, initSt) w'').2.nextFresh = initSt.nextFresh + 1 := by
                simp only [step, hYNext]
              have hNewInit : ∀ u ∈ (step (initVs, initSt) w'').1, ∀ k, u = Var.Fresh k →
                  k < (step (initVs, initSt) w'').2.nextFresh := by
                intro u hu k huk
                rw [hStepVs] at hu
                cases hu with
                | head => simp only [FVar.toVar] at huk; cases huk; rw [hStepNext, hYId]; omega
                | tail _ hTail => have hLt := hInit u hTail k huk; rw [hStepNext]; omega
              exact ih _ _ hNewInit v' hv' m hv'Eq
          exact hFoldInv [] st' (by intro v' hv'; simp at hv') v hv n hVEq

      -- All Fresh vars in foldRes.1 have indices < foldRes.2.nextFresh
      have hVsNonFresh : ∀ v ∈ foldRes.1, ∀ n, v = Var.Fresh n → n < foldRes.2.nextFresh := by
        intro v hv n hVEq
        have hFoldInv : ∀ initVs : List (Var b), ∀ initSt : EncState b,
            (∀ v' ∈ initVs, ∀ m, v' = Var.Fresh m → m < initSt.nextFresh) →
            ∀ v' ∈ (cands.foldl step (initVs, initSt)).1, ∀ m, v' = Var.Fresh m →
              m < (cands.foldl step (initVs, initSt)).2.nextFresh := by
          intro initVs initSt hInit
          induction cands generalizing initVs initSt with
          | nil => exact hInit
          | cons w'' cands' ih =>
            simp only [List.foldl_cons]
            have hYId := mkY_fst_id b t' w w'' initSt
            have hYNext := mkY_nextFresh b t' w w'' initSt
            intro v' hv' m hv'Eq
            have hStepVs : (step (initVs, initSt) w'').1 =
                FVar.toVar b (mkY b t' w w'' initSt).1 :: initVs := by simp only [step]
            have hStepNext : (step (initVs, initSt) w'').2.nextFresh = initSt.nextFresh + 1 := by
              simp only [step, hYNext]
            have hNewInit : ∀ u ∈ (step (initVs, initSt) w'').1, ∀ k, u = Var.Fresh k →
                k < (step (initVs, initSt) w'').2.nextFresh := by
              intro u hu k huk
              rw [hStepVs] at hu
              cases hu with
              | head => simp only [FVar.toVar] at huk; cases huk; rw [hStepNext, hYId]; omega
              | tail _ hTail => have hLt := hInit u hTail k huk; rw [hStepNext]; omega
            exact ih _ _ hNewInit v' hv' m hv'Eq
        exact hFoldInv [] st (by intro v' hv'; simp at hv') v hv n hVEq

      -- Control vars
      have hUId : (mkBigOrIff b foldRes.1 foldRes.2).1.id = foldRes.2.nextFresh := by
        have h := mkBigOrIff_fst b foldRes.1 foldRes.2; simp only [h]
      have hU'Id : (mkBigOrIff b foldRes'.1 foldRes'.2).1.id = foldRes'.2.nextFresh := by
        have h := mkBigOrIff_fst b foldRes'.1 foldRes'.2; simp only [h]

      have hU'Ge : (mkBigOrIff b foldRes'.1 foldRes'.2).1.id ≥ st'.nextFresh := by
        rw [hU'Id, hFoldNextFresh']; omega
      have hU'Shift : (mkBigOrIff b foldRes'.1 foldRes'.2).1.id - offset =
          (mkBigOrIff b foldRes.1 foldRes.2).1.id := by
        rw [hU'Id, hUId, hFoldNextFresh, hFoldNextFresh']; omega

      -- Decompose hInOrIff: either long clause or short clause
      -- Use by_cases to check if clause is the long clause
      let longClause' := SAT.Lit.neg (FVar.toVar b (mkBigOrIff b foldRes'.1 foldRes'.2).1) ::
          foldRes'.1.map SAT.Lit.pos
      by_cases hIsLong : clause = longClause'
      · -- Long clause: clause = [¬u', pos v'₁, ..., pos v'ₙ]
        rw [hIsLong]
        rw [SAT.Clause.eval_eq_any, List.any_eq_true]
        have hLongSt := mkBigOrIff_long_clause_mem b foldRes.1 foldRes.2
        -- Show long clause is NEW (not in st.clauses)
        have hLongNew : (SAT.Lit.neg (FVar.toVar b (mkBigOrIff b foldRes.1 foldRes.2).1) ::
            foldRes.1.map SAT.Lit.pos) ∉ st.clauses := by
          intro hIn
          -- The long clause contains Fresh var u with id = foldRes.2.nextFresh ≥ st.nextFresh
          have hFreshLit : SAT.Lit.neg (FVar.toVar b (mkBigOrIff b foldRes.1 foldRes.2).1) ∈
              (SAT.Lit.neg (FVar.toVar b (mkBigOrIff b foldRes.1 foldRes.2).1) ::
                foldRes.1.map SAT.Lit.pos) := List.Mem.head _
          have hClauseWF := hWF _ hIn
          have hLitWF := hClauseWF _ hFreshLit
          simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar] at hLitWF
          rw [hUId, hFoldNextFresh] at hLitWF
          omega
        have hEvalSt := hSatBigOrNew _ hLongSt hLongNew
        rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt
        obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
        simp only [List.mem_cons, List.mem_map] at hLitMem
        rcases hLitMem with hNegU | ⟨v, hvMem, hLitEq⟩
        · -- ¬u is true under σ
          subst hNegU
          refine ⟨SAT.Lit.neg (FVar.toVar b ⟨foldRes'.2.nextFresh⟩), List.Mem.head _, ?_⟩
          simp only [SAT.Lit.eval, σ', FVar.toVar]
          have hU'Ge' : foldRes'.2.nextFresh ≥ st'.nextFresh := by rw [hFoldNextFresh']; omega
          simp only [Nat.not_lt.mpr hU'Ge', ↓reduceIte]
          have hShift : foldRes'.2.nextFresh - offset = foldRes.2.nextFresh := by
            rw [hFoldNextFresh, hFoldNextFresh']; omega
          rw [hShift]
          have hUId' : (mkBigOrIff b foldRes.1 foldRes.2).1 = ⟨foldRes.2.nextFresh⟩ :=
            mkBigOrIff_fst b foldRes.1 foldRes.2
          simp only [FVar.toVar, hUId'] at hLitTrue
          exact hLitTrue
        · -- pos v is true under σ for some v ∈ foldRes.1
          subst hLitEq
          obtain ⟨n, hvFresh⟩ := hVsAllFresh v hvMem
          rcases List.mem_iff_getElem?.mp hvMem with ⟨idx, hvIdx⟩
          have hLenEq : foldRes'.1.length = foldRes.1.length :=
            (mkDw_fold_length_eq b t' w cands st st').symm
          have hIdx : idx < foldRes.1.length := (List.getElem?_eq_some_iff.mp hvIdx).1
          have hIdx' : idx < foldRes'.1.length := by rw [hLenEq]; exact hIdx
          have hShift := mkDw_fold_pointwise_shift b t' w cands st st' offset hOffset hMono
          have hvGet : foldRes.1[idx]? = some (Var.Fresh n) := by
            rw [hvFresh] at hvIdx; exact hvIdx
          have hv'Eq : foldRes'.1[idx]? = some (Var.Fresh (n + offset)) := by
            exact hShift idx n hvGet
          have hv'Mem : Var.Fresh (n + offset) ∈ foldRes'.1 := by
            rw [List.mem_iff_getElem?]; exact ⟨idx, hv'Eq⟩
          refine ⟨SAT.Lit.pos (Var.Fresh (n + offset)),
                  List.mem_cons.mpr (Or.inr (List.mem_map.mpr
                    ⟨Var.Fresh (n + offset), hv'Mem, rfl⟩)), ?_⟩
          simp only [SAT.Lit.eval, σ']
          have hv'Fresh := hVs'Fresh (Var.Fresh (n + offset)) hv'Mem (n + offset) rfl
          have hGe : n + offset ≥ st'.nextFresh := hv'Fresh.1
          simp only [Nat.not_lt.mpr hGe, ↓reduceIte]
          have hShiftBack : n + offset - offset = n := by omega
          rw [hShiftBack, ← hvFresh]
          simp only [SAT.Lit.eval] at hLitTrue
          exact hLitTrue
      · -- clause ≠ long clause, so it's either in fold base or a short clause
        -- Since clause ∈ newOrIff (new mkBigOrIff clauses) and clause ≠ longClause',
        -- clause must be a short clause [¬v', u'] for some v' ∈ foldRes'.1
        -- First, get membership in mkBigOrIff output (use existing hOrIffEq from above)
        have hInMkBigOrIff : clause ∈ (mkBigOrIff b foldRes'.1 foldRes'.2).2.clauses := by
          rw [hOrIffEq]
          exact List.mem_append.mpr (Or.inl hInOrIff)
        -- Check if it's in the base state (foldRes'.2.clauses)
        by_cases hInFold : clause ∈ foldRes'.2.clauses
        · -- Inherited from foldRes'.2.clauses - but we need clause ∉ st'.clauses
          -- Since clause ∉ st'.clauses, it must be a NEW clause from the fold
          -- Use the fold structural determinism invariant
          have hFoldInv : ∀ (candList : List (WId b)),
              ∀ initVs initVs' : List (Var b),
              ∀ stI stI' : EncState b,
              stI'.nextFresh - stI.nextFresh = offset →
              stI.nextFresh ≤ stI'.nextFresh →
              st'.nextFresh ≤ stI'.nextFresh →
              (∀ c ∈ (candList.foldl step (initVs, stI)).2.clauses, c ∉ st.clauses →
                SAT.Clause.eval σ c = true) →
              clause ∈ (candList.foldl step (initVs', stI')).2.clauses →
              clause ∉ stI'.clauses →
              SAT.Clause.eval σ' clause = true := by
            intro candList
            induction candList with
            | nil =>
              intro initVs initVs' stI stI' hOffsetI hMonoI hGeSt' hSatFoldI hClauseIn hNotInBase
              simp only [List.foldl_nil] at hClauseIn
              exact absurd hClauseIn hNotInBase
            | cons w'' cands' ih =>
              intro initVs initVs' stI stI' hOffsetI hMonoI hGeSt' hSatFoldI hClauseIn hNotInBase
              simp only [List.foldl_cons, step] at hClauseIn hSatFoldI
              have hYNext := mkY_nextFresh b t' w w'' stI
              have hY'Next := mkY_nextFresh b t' w w'' stI'
              have hOffsetY : (mkY b t' w w'' stI').2.nextFresh - (mkY b t' w w'' stI).2.nextFresh
                  = offset := by rw [hYNext, hY'Next]; omega
              have hMonoY :
                  (mkY b t' w w'' stI).2.nextFresh ≤ (mkY b t' w w'' stI').2.nextFresh := by
                rw [hYNext, hY'Next]; omega
              have hGeStY : st'.nextFresh ≤ (mkY b t' w w'' stI').2.nextFresh := by
                rw [hY'Next]; omega
              have hAppendY := mkY_clauses_eq_append b t' w w'' stI'
              have hAppendYI := mkY_clauses_eq_append b t' w w'' stI
              have hYId := mkY_fst_id b t' w w'' stI
              have hY'Id := mkY_fst_id b t' w w'' stI'
              by_cases hInMkYNew : clause ∈
                  [[SAT.Lit.neg (Var.Mem t' w''), SAT.Lit.neg (Var.PreEq w.ti w''.ti),
                    SAT.Lit.pos (FVar.toVar b (mkY b t' w w'' stI').1)],
                   [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI').1),
                    SAT.Lit.pos (Var.PreEq w.ti w''.ti)],
                   [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI').1),
                    SAT.Lit.pos (Var.Mem t' w'')]]
              · -- NEW mkY clause at this step
                -- Construct satisfaction of NEW mkY clauses from hSatFoldI
                have hSatNewMkYI : ∀ c ∈ (mkY b t' w w'' stI).2.clauses, c ∉ st.clauses →
                    SAT.Clause.eval σ c = true := by
                  intro c hc hNotSt
                  apply hSatFoldI
                  · have hStepSub : ∀ acc w''', acc.2.clauses ⊆ (step acc w''').2.clauses := by
                      intro acc w'''; simp only [step]; exact mkY_clauses_subset b t' w w''' acc.2
                    let mkYRes :=
                      (FVar.toVar b (mkY b t' w w'' stI).1 :: initVs, (mkY b t' w w'' stI).2)
                    have hSubset := foldl_subset_snd step hStepSub cands' mkYRes
                    exact hSubset hc
                  · exact hNotSt
                -- Helper: mkY clauses at stI have Fresh var with id = stI.nextFresh ≥ st.nextFresh
                -- By WF, st.clauses have Fresh vars < st.nextFresh, so NEW mkY clauses ∉ st.clauses
                have hStIMono : st.nextFresh ≤ stI.nextFresh := by omega
                simp only [List.mem_cons, List.mem_nil_iff, or_false] at hInMkYNew
                rcases hInMkYNew with hC1 | hC2 | hC3
                · -- Clause 1
                  subst hC1
                  have hC1_stI : [SAT.Lit.neg (Var.Mem t' w''), SAT.Lit.neg (Var.PreEq w.ti w''.ti),
                      SAT.Lit.pos (FVar.toVar b (mkY b t' w w'' stI).1)] ∈
                      (mkY b t' w w'' stI).2.clauses := by rw [hAppendYI]; simp
                  have hC1_New := mkY_clause_not_in_base b t' w w'' st stI hWF hStIMono
                      [SAT.Lit.neg (Var.Mem t' w''), SAT.Lit.neg (Var.PreEq w.ti w''.ti),
                       SAT.Lit.pos (FVar.toVar b (mkY b t' w w'' stI).1)] (by simp)
                  have hSatC1 := hSatNewMkYI _ hC1_stI hC1_New
                  rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC1
                  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
                  obtain ⟨lit, hMem, hTrue⟩ := hSatC1
                  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
                  rcases hMem with hL1 | hL2 | hL3
                  · exact ⟨SAT.Lit.neg (Var.Mem t' w''), by simp,
                      by subst hL1; simp only [σ', SAT.Lit.eval]; exact hTrue⟩
                  · exact ⟨SAT.Lit.neg (Var.PreEq w.ti w''.ti), by simp,
                      by subst hL2; simp only [σ', SAT.Lit.eval]; exact hTrue⟩
                  · refine ⟨SAT.Lit.pos (FVar.toVar b (mkY b t' w w'' stI').1), by simp, ?_⟩
                    simp only [SAT.Lit.eval, σ', FVar.toVar] at hTrue ⊢
                    have hY'Ge : (mkY b t' w w'' stI').1.id ≥ st'.nextFresh := by
                      rw [hY'Id]; exact hGeSt'
                    simp only [Nat.not_lt.mpr hY'Ge, ↓reduceIte]
                    have hShiftY :
                        (mkY b t' w w'' stI').1.id - offset = (mkY b t' w w'' stI).1.id := by
                      rw [hY'Id, hYId]; omega
                    rw [hShiftY]; subst hL3; exact hTrue
                · -- Clause 2
                  subst hC2
                  have hC2_stI : [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI).1),
                      SAT.Lit.pos (Var.PreEq w.ti w''.ti)] ∈ (mkY b t' w w'' stI).2.clauses := by
                    rw [hAppendYI]; simp
                  have hC2_New := mkY_clause_not_in_base b t' w w'' st stI hWF hStIMono
                      [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI).1),
                       SAT.Lit.pos (Var.PreEq w.ti w''.ti)]
                    (by simp)
                  have hSatC2 := hSatNewMkYI _ hC2_stI hC2_New
                  rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC2
                  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
                  obtain ⟨lit, hMem, hTrue⟩ := hSatC2
                  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
                  rcases hMem with hL1 | hL2
                  · refine ⟨SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI').1), by simp, ?_⟩
                    simp only [SAT.Lit.eval, σ', FVar.toVar] at hTrue ⊢
                    have hY'Ge : (mkY b t' w w'' stI').1.id ≥ st'.nextFresh := by
                      rw [hY'Id]; exact hGeSt'
                    simp only [Nat.not_lt.mpr hY'Ge, ↓reduceIte]
                    have hShiftY :
                        (mkY b t' w w'' stI').1.id - offset = (mkY b t' w w'' stI).1.id := by
                      rw [hY'Id, hYId]; omega
                    rw [hShiftY]; subst hL1; exact hTrue
                  · exact ⟨SAT.Lit.pos (Var.PreEq w.ti w''.ti), by simp,
                      by subst hL2; simp only [σ', SAT.Lit.eval]; exact hTrue⟩
                · -- Clause 3
                  subst hC3
                  have hC3_stI : [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI).1),
                      SAT.Lit.pos (Var.Mem t' w'')] ∈ (mkY b t' w w'' stI).2.clauses := by
                    rw [hAppendYI]; simp
                  have hC3_New := mkY_clause_not_in_base b t' w w'' st stI hWF hStIMono
                      [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI).1),
                       SAT.Lit.pos (Var.Mem t' w'')]
                    (by simp)
                  have hSatC3 := hSatNewMkYI _ hC3_stI hC3_New
                  rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC3
                  rw [SAT.Clause.eval_eq_any, List.any_eq_true]
                  obtain ⟨lit, hMem, hTrue⟩ := hSatC3
                  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
                  rcases hMem with hL1 | hL2
                  · refine ⟨SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI').1), by simp, ?_⟩
                    simp only [SAT.Lit.eval, σ', FVar.toVar] at hTrue ⊢
                    have hY'Ge : (mkY b t' w w'' stI').1.id ≥ st'.nextFresh := by
                      rw [hY'Id]; exact hGeSt'
                    simp only [Nat.not_lt.mpr hY'Ge, ↓reduceIte]
                    have hShiftY :
                        (mkY b t' w w'' stI').1.id - offset = (mkY b t' w w'' stI).1.id := by
                      rw [hY'Id, hYId]; omega
                    rw [hShiftY]; subst hL1; exact hTrue
                  · exact ⟨SAT.Lit.pos (Var.Mem t' w''), by simp,
                      by subst hL2; simp only [σ', SAT.Lit.eval]; exact hTrue⟩
              · -- From later fold step
                by_cases hInMkYClauses : clause ∈ (mkY b t' w w'' stI').2.clauses
                · rw [hAppendY] at hInMkYClauses
                  cases List.mem_append.mp hInMkYClauses with
                  | inl hNew => exact absurd hNew hInMkYNew
                  | inr hInh => exact absurd hInh hNotInBase
                · apply ih
                    (FVar.toVar b (mkY b t' w w'' stI).1 :: initVs)
                    (FVar.toVar b (mkY b t' w w'' stI').1 :: initVs')
                    (mkY b t' w w'' stI).2
                    (mkY b t' w w'' stI').2
                    hOffsetY hMonoY hGeStY
                    hSatFoldI hClauseIn hInMkYClauses
          have hOffsetInit : st'.nextFresh - st.nextFresh = offset := by omega
          have hGeStInit : st'.nextFresh ≤ st'.nextFresh := Nat.le_refl _
          exact hFoldInv cands [] [] st st'
            hOffsetInit hMono hGeStInit hSatNewFold hInFold hClauseNotInBase
        · -- Short clause [¬v', u'] for some v' ∈ foldRes'.1
          have hShortForm : ∃ v' ∈ foldRes'.1, clause =
              [SAT.Lit.neg v', SAT.Lit.pos (FVar.toVar b ⟨foldRes'.2.nextFresh⟩)] := by
            -- clause ∈ hInOrIff (new mkBigOrIff clauses), clause ≠ long clause
            -- So clause must be one of the short clauses from the foldl
            let u' : FVar b := ⟨foldRes'.2.nextFresh⟩
            let stepF := fun (stCur : EncState b) (v : Var b) =>
              EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u')]
            -- Derive that clause is in the foldl result (not long clause, not base)
            have hU'Eq : (mkBigOrIff b foldRes'.1 foldRes'.2).1 = u' :=
              mkBigOrIff_fst b foldRes'.1 foldRes'.2
            have hLongIs :
                longClause' = SAT.Lit.neg (FVar.toVar b u') :: foldRes'.1.map SAT.Lit.pos := by
              simp only [longClause', hU'Eq]
            -- hInMkBigOrIff : clause ∈ (mkBigOrIff ...).2.clauses
            -- Unfold mkBigOrIff to get the structure
            unfold mkBigOrIff at hInMkBigOrIff
            simp only [EncState.addClause, List.mem_cons] at hInMkBigOrIff
            rcases hInMkBigOrIff with hIsLongActual | hInFoldl
            · -- clause = long clause - contradiction with hIsLong
              exfalso
              apply hIsLong
              simp only [longClause', hU'Eq]
              exact hIsLongActual
            · -- clause ∈ foldl result
              -- Now check if it's in base or new
              have hAllocClauses :
                  (EncState.allocFresh b foldRes'.2).2.clauses = foldRes'.2.clauses :=
                EncState.allocFresh_clauses_eq b foldRes'.2
              -- hInFoldl has type: clause ∈ (foldl (fun acc v => addClause _ acc [neg v, pos u'])
              --                               (allocFresh _ foldRes'.2).2 foldRes'.1).clauses
              have hFoldMem : clause ∈ (foldRes'.1.foldl stepF
                  (EncState.allocFresh b foldRes'.2).2).clauses := hInFoldl
              rw [foldl_addClause_mem_iff] at hFoldMem
              cases hFoldMem with
              | inl hOld => rw [hAllocClauses] at hOld; exact absurd hOld hInFold
              | inr hNew => obtain ⟨v', hMem, hEq⟩ := hNew; exact ⟨v', hMem, hEq⟩
          obtain ⟨v', hv'Mem, hShortClause⟩ := hShortForm
          rw [hShortClause]
          -- Find corresponding short clause at st
          have hLenEq : foldRes'.1.length = foldRes.1.length :=
            (mkDw_fold_length_eq b t' w cands st st').symm
          rcases List.mem_iff_getElem?.mp hv'Mem with ⟨idx, hv'Eq⟩
          have hIdx : idx < foldRes'.1.length := (List.getElem?_eq_some_iff.mp hv'Eq).1
          have hIdxLt : idx < foldRes.1.length := by rw [← hLenEq]; exact hIdx
          have hvEx : ∃ v, foldRes.1[idx]? = some v := by
            exact ⟨foldRes.1[idx]'hIdxLt, List.getElem?_eq_some_iff.mpr ⟨hIdxLt, rfl⟩⟩
          rcases hvEx with ⟨v, hv⟩
          have hvMem : v ∈ foldRes.1 := by rw [List.mem_iff_getElem?]; exact ⟨idx, hv⟩
          -- Short clause at st: [¬v, u]
          have hShortSt := mkBigOrIff_unit_clause_mem b foldRes.1 foldRes.2 hvMem
          -- Show short clause is NEW (not in st.clauses)
          have hShortNew : [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b (mkBigOrIff b foldRes.1 foldRes.2).1)] ∉ st.clauses := by
            intro hIn
            -- The short clause contains Fresh var u with id = foldRes.2.nextFresh ≥ st.nextFresh
            have hFreshLit : SAT.Lit.pos (FVar.toVar b (mkBigOrIff b foldRes.1 foldRes.2).1) ∈
                [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b (mkBigOrIff b foldRes.1 foldRes.2).1)] := by simp
            have hClauseWF := hWF _ hIn
            have hLitWF := hClauseWF _ hFreshLit
            simp only [litFreshBelow, SAT.Lit.getVar, FVar.toVar] at hLitWF
            rw [hUId, hFoldNextFresh] at hLitWF
            omega
          have hEvalSt := hSatBigOrNew _ hShortSt hShortNew
          rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt ⊢
          obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
          rcases hLitMem with hNegV | hPosU
          · -- ¬v is true under σ
            have hv'Fresh := hVs'Fresh v' hv'Mem
            cases hv'Var : v' with
            | Fresh n' =>
              have ⟨hGe, hLt⟩ := hv'Fresh n' hv'Var
              have hvNonFresh := hVsNonFresh v hvMem
              cases hVVar : v with
              | Fresh n =>
                have hvLt := hvNonFresh n hVVar
                have hN'eq : n' = n + offset := by
                  have hShiftProp :=
                    mkDw_fold_pointwise_shift b t' w cands st st' offset hOffset hMono
                  have hvGet : foldRes.1[idx]? = some (Var.Fresh n) := by
                    rw [hVVar] at hv; exact hv
                  have hv'Get : foldRes'.1[idx]? = some (Var.Fresh n') := by
                    rw [hv'Var] at hv'Eq; exact hv'Eq
                  have := hShiftProp idx n hvGet
                  rw [this] at hv'Get
                  injection hv'Get with hEq; injection hEq with hN; exact hN.symm
                refine ⟨SAT.Lit.neg (Var.Fresh n'), List.mem_cons.mpr (Or.inl rfl), ?_⟩
                simp only [SAT.Lit.eval, σ', Nat.not_lt.mpr hGe, ↓reduceIte]
                have hShiftN : n' - offset = n := by omega
                rw [hShiftN, ← hVVar]
                subst hNegV; simp only [SAT.Lit.eval] at hLitTrue; exact hLitTrue
              | Mem _ _ | Level _ _ | Pred _ _ _ | MinQ _ _ | ReachT _ | Edge _ _
              | Exists _ _ _ | PreEq _ _ | Seq _ _ | Rep _ | Incomp _ _ _ _ | Acc _ _ _ =>
                have ⟨_, hvF⟩ := hVsAllFresh v hvMem; subst hvF; simp at hVVar
            | Mem _ _ | Level _ _ | Pred _ _ _ | MinQ _ _ | ReachT _ | Edge _ _
            | Exists _ _ _ | PreEq _ _ | Seq _ _ | Rep _ | Incomp _ _ _ _ | Acc _ _ _ =>
              have ⟨_, hv'F⟩ := (by
                intro v hv
                have hFoldInv : ∀ initVs : List (Var b), ∀ initSt : EncState b,
                    (∀ v' ∈ initVs, ∃ m, v' = Var.Fresh m) →
                    ∀ v' ∈ (cands.foldl step (initVs, initSt)).1,
                    ∃ m, v' = Var.Fresh m := by
                  intro initVs initSt hInit
                  induction cands generalizing initVs initSt with
                  | nil => exact hInit
                  | cons w'' cands' ih =>
                    simp only [List.foldl_cons]
                    intro v' hv'
                    have hStepFst : (step (initVs, initSt) w'').1 =
                        FVar.toVar b (mkY b t' w w'' initSt).1 :: initVs := rfl
                    apply ih (step (initVs, initSt) w'').1 (step (initVs, initSt) w'').2
                    intro v'' hv''
                    rw [hStepFst] at hv''
                    simp only [List.mem_cons] at hv''
                    rcases hv'' with hNew | hOld
                    · use (mkY b t' w w'' initSt).1.id; rw [hNew]; rfl
                    · exact hInit v'' hOld
                    exact hv'
                exact hFoldInv [] st' (fun v' hv' => nomatch hv') v hv :
                  ∀ v ∈ foldRes'.1, ∃ n, v = Var.Fresh n) v' hv'Mem
              subst hv'F; simp at hv'Var
          · -- u is true under σ
            rw [hPosU] at hLitTrue
            refine ⟨SAT.Lit.pos (FVar.toVar b (mkBigOrIff b foldRes'.1 foldRes'.2).1),
                    List.mem_cons.mpr (Or.inr (List.mem_singleton_self _)), ?_⟩
            simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hU'Ge, ↓reduceIte, hU'Shift]
            simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue
            exact hLitTrue

    | inr hInFoldBase =>
      -- clause ∈ foldRes'.2.clauses
      -- But it's not in st'.clauses (by hClauseNotInBase), so it's a NEW fold clause
      have hFoldInv : ∀ (candList : List (WId b)),
          ∀ initVs initVs' : List (Var b),
          ∀ stI stI' : EncState b,
          stI'.nextFresh - stI.nextFresh = offset →
          stI.nextFresh ≤ stI'.nextFresh →
          st'.nextFresh ≤ stI'.nextFresh →
          (∀ c ∈ (candList.foldl step (initVs, stI)).2.clauses, c ∉ st.clauses →
            SAT.Clause.eval σ c = true) →
          clause ∈ (candList.foldl step (initVs', stI')).2.clauses →
          clause ∉ stI'.clauses →
          SAT.Clause.eval σ' clause = true := by
        intro candList
        induction candList with
        | nil =>
          intro initVs initVs' stI stI' hOffsetI hMonoI hGeSt' hSatFoldI hClauseIn hNotInBase
          simp only [List.foldl_nil] at hClauseIn
          exact absurd hClauseIn hNotInBase
        | cons w'' cands' ih =>
          intro initVs initVs' stI stI' hOffsetI hMonoI hGeSt' hSatFoldI hClauseIn hNotInBase
          simp only [List.foldl_cons, step] at hClauseIn hSatFoldI
          have hYNext := mkY_nextFresh b t' w w'' stI
          have hY'Next := mkY_nextFresh b t' w w'' stI'
          have hOffsetY : (mkY b t' w w'' stI').2.nextFresh - (mkY b t' w w'' stI).2.nextFresh
              = offset := by rw [hYNext, hY'Next]; omega
          have hMonoY : (mkY b t' w w'' stI).2.nextFresh ≤ (mkY b t' w w'' stI').2.nextFresh := by
            rw [hYNext, hY'Next]; omega
          have hGeStY : st'.nextFresh ≤ (mkY b t' w w'' stI').2.nextFresh := by
            rw [hY'Next]; omega
          have hAppendY := mkY_clauses_eq_append b t' w w'' stI'
          have hAppendYI := mkY_clauses_eq_append b t' w w'' stI
          have hYId := mkY_fst_id b t' w w'' stI
          have hY'Id := mkY_fst_id b t' w w'' stI'
          by_cases hInMkYNew : clause ∈
              [[SAT.Lit.neg (Var.Mem t' w''), SAT.Lit.neg (Var.PreEq w.ti w''.ti),
                SAT.Lit.pos (FVar.toVar b (mkY b t' w w'' stI').1)],
               [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI').1),
                SAT.Lit.pos (Var.PreEq w.ti w''.ti)],
               [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI').1),
                SAT.Lit.pos (Var.Mem t' w'')]]
          · -- NEW mkY clause at this step
            -- Construct satisfaction of NEW mkY clauses from hSatFoldI
            have hSatNewMkYI : ∀ c ∈ (mkY b t' w w'' stI).2.clauses, c ∉ st.clauses →
                SAT.Clause.eval σ c = true := by
              intro c hc hNotSt
              apply hSatFoldI
              · have hStepSub : ∀ acc w''', acc.2.clauses ⊆ (step acc w''').2.clauses := by
                  intro acc w'''
                  simp only [step]
                  exact mkY_clauses_subset b t' w w''' acc.2
                let mkYRes :=
                  (FVar.toVar b (mkY b t' w w'' stI).1 :: initVs, (mkY b t' w w'' stI).2)
                have hSubset := foldl_subset_snd step hStepSub cands' mkYRes
                exact hSubset hc
              · exact hNotSt
            have hStIMono : st.nextFresh ≤ stI.nextFresh := by omega
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hInMkYNew
            rcases hInMkYNew with hC1 | hC2 | hC3
            · -- Clause 1
              subst hC1
              have hC1_stI : [SAT.Lit.neg (Var.Mem t' w''), SAT.Lit.neg (Var.PreEq w.ti w''.ti),
                  SAT.Lit.pos (FVar.toVar b (mkY b t' w w'' stI).1)] ∈
                  (mkY b t' w w'' stI).2.clauses := by rw [hAppendYI]; simp
              have hC1_New := mkY_clause_not_in_base b t' w w'' st stI hWF hStIMono
                  [SAT.Lit.neg (Var.Mem t' w''), SAT.Lit.neg (Var.PreEq w.ti w''.ti),
                   SAT.Lit.pos (FVar.toVar b (mkY b t' w w'' stI).1)] (by simp)
              have hSatC1 := hSatNewMkYI _ hC1_stI hC1_New
              rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC1 ⊢
              obtain ⟨lit, hMem, hTrue⟩ := hSatC1
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
              rcases hMem with hL1 | hL2 | hL3
              · exact ⟨SAT.Lit.neg (Var.Mem t' w''), by simp,
                  by subst hL1; simp only [σ', SAT.Lit.eval]; exact hTrue⟩
              · exact ⟨SAT.Lit.neg (Var.PreEq w.ti w''.ti), by simp,
                  by subst hL2; simp only [σ', SAT.Lit.eval]; exact hTrue⟩
              · refine ⟨SAT.Lit.pos (FVar.toVar b (mkY b t' w w'' stI').1), by simp, ?_⟩
                simp only [SAT.Lit.eval, σ', FVar.toVar] at hTrue ⊢
                have hY'Ge : (mkY b t' w w'' stI').1.id ≥ st'.nextFresh := by
                  rw [hY'Id]; exact hGeSt'
                simp only [Nat.not_lt.mpr hY'Ge, ↓reduceIte]
                have hShiftY : (mkY b t' w w'' stI').1.id - offset = (mkY b t' w w'' stI).1.id := by
                  rw [hY'Id, hYId]; omega
                rw [hShiftY]; subst hL3; exact hTrue
            · -- Clause 2
              subst hC2
              have hC2_stI : [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI).1),
                  SAT.Lit.pos (Var.PreEq w.ti w''.ti)] ∈ (mkY b t' w w'' stI).2.clauses := by
                rw [hAppendYI]; simp
              have hC2_New := mkY_clause_not_in_base b t' w w'' st stI hWF hStIMono
                  [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI).1),
                   SAT.Lit.pos (Var.PreEq w.ti w''.ti)]
                (by simp)
              have hSatC2 := hSatNewMkYI _ hC2_stI hC2_New
              rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC2
              rw [SAT.Clause.eval_eq_any, List.any_eq_true]
              obtain ⟨lit, hMem, hTrue⟩ := hSatC2
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
              rcases hMem with hL1 | hL2
              · refine ⟨SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI').1), by simp, ?_⟩
                simp only [SAT.Lit.eval, σ', FVar.toVar] at hTrue ⊢
                have hY'Ge : (mkY b t' w w'' stI').1.id ≥ st'.nextFresh := by
                  rw [hY'Id]; exact hGeSt'
                simp only [Nat.not_lt.mpr hY'Ge, ↓reduceIte]
                have hShiftY :
                    (mkY b t' w w'' stI').1.id - offset = (mkY b t' w w'' stI).1.id := by
                  rw [hY'Id, hYId]; omega
                rw [hShiftY]; subst hL1; exact hTrue
              · exact ⟨SAT.Lit.pos (Var.PreEq w.ti w''.ti), by simp,
                  by subst hL2; simp only [σ', SAT.Lit.eval]; exact hTrue⟩
            · -- Clause 3
              subst hC3
              have hC3_stI : [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI).1),
                  SAT.Lit.pos (Var.Mem t' w'')] ∈ (mkY b t' w w'' stI).2.clauses := by
                rw [hAppendYI]; simp
              have hC3_New := mkY_clause_not_in_base b t' w w'' st stI hWF hStIMono
                  [SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI).1),
                   SAT.Lit.pos (Var.Mem t' w'')]
                (by simp)
              have hSatC3 := hSatNewMkYI _ hC3_stI hC3_New
              rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC3
              rw [SAT.Clause.eval_eq_any, List.any_eq_true]
              obtain ⟨lit, hMem, hTrue⟩ := hSatC3
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
              rcases hMem with hL1 | hL2
              · refine ⟨SAT.Lit.neg (FVar.toVar b (mkY b t' w w'' stI').1), by simp, ?_⟩
                simp only [SAT.Lit.eval, σ', FVar.toVar] at hTrue ⊢
                have hY'Ge : (mkY b t' w w'' stI').1.id ≥ st'.nextFresh := by
                  rw [hY'Id]; exact hGeSt'
                simp only [Nat.not_lt.mpr hY'Ge, ↓reduceIte]
                have hShiftY :
                    (mkY b t' w w'' stI').1.id - offset = (mkY b t' w w'' stI).1.id := by
                  rw [hY'Id, hYId]; omega
                rw [hShiftY]; subst hL1; exact hTrue
              · exact ⟨SAT.Lit.pos (Var.Mem t' w''), by simp,
                  by subst hL2; simp only [σ', SAT.Lit.eval]; exact hTrue⟩
          · -- From later fold step
            by_cases hInMkYClauses : clause ∈ (mkY b t' w w'' stI').2.clauses
            · rw [hAppendY] at hInMkYClauses
              cases List.mem_append.mp hInMkYClauses with
              | inl hNew => exact absurd hNew hInMkYNew
              | inr hInh => exact absurd hInh hNotInBase
            · apply ih
                (FVar.toVar b (mkY b t' w w'' stI).1 :: initVs)
                (FVar.toVar b (mkY b t' w w'' stI').1 :: initVs')
                (mkY b t' w w'' stI).2
                (mkY b t' w w'' stI').2
                hOffsetY hMonoY hGeStY
                hSatFoldI hClauseIn hInMkYClauses
      have hOffsetInit : st'.nextFresh - st.nextFresh = offset := by omega
      have hGeStInit : st'.nextFresh ≤ st'.nextFresh := Nat.le_refl _
      exact hFoldInv cands [] [] st st'
        hOffsetInit hMono hGeStInit hSatNewFold hInFoldBase hClauseNotInBase

-- ============================================================================
-- mkDw structural determinism
-- ============================================================================

-- Structural determinism for mkDw.
-- - Empty case: allocFresh + addClause [neg d], similar to mkY
-- - Non-empty case: fold mkY produces shifted vs, mkBigOrIff handles these
omit [DecidableEq S.Value] [DecidableEq S.AtomicPredType] in
lemma mkDw_structural_determinism (b : Bounds S) (t' : b.times) (w : WId b)
    (st st' : EncState b) (offset : Nat)
    (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st')
    (σ : SAT.Assignment (Var b))
    (hSat : (mkDw b t' w st).2.clauses.all (SAT.Clause.eval σ) = true)
    (hSatBase : st'.clauses.all (SAT.Clause.eval σ) = true) :
    let σ' : SAT.Assignment (Var b) := fun v =>
      match v with
      | Var.Fresh n =>
          if n < st'.nextFresh then σ v
          else σ (Var.Fresh (n - offset))
      | _ => σ v
    (mkDw b t' w st').2.clauses.all (SAT.Clause.eval σ') = true := by
  intro σ'
  classical
  unfold mkDw

  set cands := (WId.allWorlds b).filter (fun w' => sameSig b w w')
  by_cases hEmpty : cands = []
  · -- Empty case: single clause [neg d] where d.id = st.nextFresh
    simp only [hEmpty]
    cases hAlloc : EncState.allocFresh b st with
    | mk d stA =>
        cases hAlloc' : EncState.allocFresh b st' with
        | mk d' stA' =>
            simp only [EncState.addClause, List.all_eq_true]
            intro clause hClause
            cases hClause with
            | head =>
                have hDId : d.id = st.nextFresh := by
                  have := EncState.allocFresh_fst b st
                  simp only [hAlloc] at this; exact this
                have hD'Id : d'.id = st'.nextFresh := by
                  have := EncState.allocFresh_fst b st'
                  simp only [hAlloc'] at this; exact this
                have hD'Ge : d'.id ≥ st'.nextFresh := by rw [hD'Id]
                have hD'Shift : d'.id - offset = d.id := by
                  rw [hD'Id, hDId, hOffset]; omega
                have hClauseSt : [SAT.Lit.neg (FVar.toVar b d)] ∈
                    (EncState.addClause b stA [SAT.Lit.neg (FVar.toVar b d)]).clauses := by
                  simp [EncState.addClause]
                have hSat' : (EncState.addClause b stA [SAT.Lit.neg (FVar.toVar b d)]).clauses.all
                    (SAT.Clause.eval σ) = true := by
                  unfold mkDw at hSat
                  simp only [cands, hEmpty] at hSat
                  simp only [hAlloc] at hSat
                  exact hSat
                have hSatC := List.all_eq_true.mp hSat' _ hClauseSt
                rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hSatC ⊢
                obtain ⟨lit, hLitMem, hLitTrue⟩ := hSatC
                simp only [List.mem_singleton] at hLitMem
                subst hLitMem
                refine ⟨SAT.Lit.neg (FVar.toVar b d'), List.mem_singleton_self _, ?_⟩
                simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hD'Ge, ↓reduceIte,
                           hD'Shift, SAT.Lit.eval] at hLitTrue ⊢
                exact hLitTrue
            | tail _ hTail =>
                have hClausesStA' : stA'.clauses = st'.clauses := by
                  have := EncState.allocFresh_clauses_eq b st'
                  simp only [hAlloc'] at this; exact this
                rw [hClausesStA'] at hTail
                have hEval := List.all_eq_true.mp hSatBase clause hTail
                rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEval ⊢
                obtain ⟨lit, hLitMem, hLitTrue⟩ := hEval
                refine ⟨lit, hLitMem, ?_⟩
                have hClauseWF := hWF clause hTail
                cases lit with
                | pos v =>
                    simp only [SAT.Lit.eval] at hLitTrue ⊢
                    cases v with
                    | Fresh n =>
                        have hLt : n < st'.nextFresh := by
                          have h := hClauseWF (SAT.Lit.pos (Var.Fresh n)) hLitMem
                          simp only [litFreshBelow, SAT.Lit.getVar] at h; exact h
                        simp only [σ', hLt, ↓reduceIte]; exact hLitTrue
                    | _ => simp only [σ']; exact hLitTrue
                | neg v =>
                    simp only [SAT.Lit.eval] at hLitTrue ⊢
                    cases v with
                    | Fresh n =>
                        have hLt : n < st'.nextFresh := by
                          have h := hClauseWF (SAT.Lit.neg (Var.Fresh n)) hLitMem
                          simp only [litFreshBelow, SAT.Lit.getVar] at h; exact h
                        simp only [σ', hLt, ↓reduceIte]; exact hLitTrue
                    | _ => simp only [σ']; exact hLitTrue

  · -- Non-empty case: fold mkY then mkBigOrIff
    simp only

    -- Define the fold step function
    let step := fun (acc : List (Var b) × EncState b) w'' =>
      let (vs, st'') := acc
      let (y, st''') := mkY b t' w w'' st''
      (FVar.toVar b y :: vs, st''')

    -- Get the fold results
    let foldRes := cands.foldl step ([], st)
    let foldRes' := cands.foldl step ([], st')

    -- The result from st and st' pass through mkBigOrIff
    have hGoal :
        (mkBigOrIff b foldRes'.1 foldRes'.2).2.clauses.all (SAT.Clause.eval σ') = true := by
      -- Need to show: clauses from fold at st' + mkBigOrIff satisfy σ'

      -- Key facts about fold nextFresh increments
      have hFoldNextFresh : foldRes.2.nextFresh = st.nextFresh + cands.length :=
        mkDw_fold_nextFresh b t' w cands ([], st)
      have hFoldNextFresh' : foldRes'.2.nextFresh = st'.nextFresh + cands.length :=
        mkDw_fold_nextFresh b t' w cands ([], st')

      -- Extract σ satisfaction for foldRes.2.clauses from hSat
      have hSatFold : foldRes.2.clauses.all (SAT.Clause.eval σ) = true := by
        have hSubset := mkBigOrIff_clauses_subset b foldRes.1 foldRes.2
        -- mkDw b t' w st in non-empty case = mkBigOrIff foldRes.1 foldRes.2
        -- step and the inline fold function are definitionally equal
        have hStepEq : step = fun acc w' =>
            (FVar.toVar b (mkY b t' w w' acc.2).1 :: acc.1, (mkY b t' w w' acc.2).2) := by
          funext acc w'
          simp only [step]
        rw [List.all_eq_true] at hSat ⊢
        intro clause hClause
        apply hSat
        unfold mkDw
        simp only [← hStepEq, cands]
        exact hSubset hClause

      -- The fold at st' has well-formed state (mkY preserves WF)
      have hFoldWF' : EncState.WellFormed foldRes'.2 := by
        have hFoldWF_ind : ∀ init : List (Var b) × EncState b,
            EncState.WellFormed init.2 →
            EncState.WellFormed (cands.foldl step init).2 := by
          intro init hWFInit
          induction cands generalizing init with
          | nil => exact hWFInit
          | cons w'' cands' ih =>
            simp only [List.foldl_cons]
            apply ih
            simp only [step]
            rcases init with ⟨initVs, initSt⟩
            exact mkY_wf b t' w w'' initSt hWFInit
        exact hFoldWF_ind ([], st') hWF

      -- All vars in foldRes.1 are Fresh (since they come from FVar.toVar)
      have hVsAllFresh : ∀ v ∈ foldRes.1, ∃ n, v = Var.Fresh n := by
        intro v hv
        have hFoldInv : ∀ initVs : List (Var b), ∀ initSt : EncState b,
            (∀ v' ∈ initVs, ∃ m, v' = Var.Fresh m) →
            ∀ v' ∈ (cands.foldl step (initVs, initSt)).1, ∃ m, v' = Var.Fresh m := by
          intro initVs initSt hInit
          induction cands generalizing initVs initSt with
          | nil => exact hInit
          | cons w'' cands' ih =>
            simp only [List.foldl_cons]
            intro v' hv'
            -- step (initVs, initSt) w'' = (FVar.toVar b (mkY ...).1 :: initVs, ...)
            have hStepFst : (step (initVs, initSt) w'').1 =
                FVar.toVar b (mkY b t' w w'' initSt).1 :: initVs := rfl
            apply ih (step (initVs, initSt) w'').1 (step (initVs, initSt) w'').2
            intro v'' hv''
            rw [hStepFst] at hv''
            simp only [List.mem_cons] at hv''
            rcases hv'' with hNew | hOld
            · use (mkY b t' w w'' initSt).1.id
              rw [hNew]; rfl
            · exact hInit v'' hOld
            exact hv'
        exact hFoldInv [] st (by intro v' hv'; simp at hv') v hv

      -- Same for foldRes'.1
      have hVs'AllFresh : ∀ v ∈ foldRes'.1, ∃ n, v = Var.Fresh n := by
        intro v hv
        have hFoldInv : ∀ initVs : List (Var b), ∀ initSt : EncState b,
            (∀ v' ∈ initVs, ∃ m, v' = Var.Fresh m) →
            ∀ v' ∈ (cands.foldl step (initVs, initSt)).1, ∃ m, v' = Var.Fresh m := by
          intro initVs initSt hInit
          induction cands generalizing initVs initSt with
          | nil => exact hInit
          | cons w'' cands' ih =>
            simp only [List.foldl_cons]
            intro v' hv'
            have hStepFst : (step (initVs, initSt) w'').1 =
                FVar.toVar b (mkY b t' w w'' initSt).1 :: initVs := rfl
            apply ih (step (initVs, initSt) w'').1 (step (initVs, initSt) w'').2
            intro v'' hv''
            rw [hStepFst] at hv''
            simp only [List.mem_cons] at hv''
            rcases hv'' with hNew | hOld
            · use (mkY b t' w w'' initSt).1.id
              rw [hNew]; rfl
            · exact hInit v'' hOld
            exact hv'
        exact hFoldInv [] st' (by intro v' hv'; simp at hv') v hv

      -- All Fresh vars in foldRes.1 have indices < foldRes.2.nextFresh
      have hVsNonFresh : ∀ v ∈ foldRes.1, ∀ n, v = Var.Fresh n → n < foldRes.2.nextFresh := by
        intro v hv n hVEq
        -- Each mkY step produces Fresh var with id = current nextFresh
        -- Fold accumulates these, all with ids < final nextFresh
        have hFoldInv : ∀ initVs : List (Var b), ∀ initSt : EncState b,
            (∀ v' ∈ initVs, ∀ m, v' = Var.Fresh m → m < initSt.nextFresh) →
            ∀ v' ∈ (cands.foldl step (initVs, initSt)).1, ∀ m, v' = Var.Fresh m →
              m < (cands.foldl step (initVs, initSt)).2.nextFresh := by
          intro initVs initSt hInit
          induction cands generalizing initVs initSt with
          | nil => exact hInit
          | cons w'' cands' ih =>
            simp only [List.foldl_cons]
            have hYId := mkY_fst_id b t' w w'' initSt
            have hYNext := mkY_nextFresh b t' w w'' initSt
            -- The step produces (y :: initVs, stY) where y.id = initSt.nextFresh
            -- and stY.nextFresh = initSt.nextFresh + 1
            intro v' hv' m hv'Eq
            -- After one step, foldl continues with (y :: initVs, stY)
            -- ih gives us the result for the continuation
            have hStepVs : (step (initVs, initSt) w'').1 =
                FVar.toVar b (mkY b t' w w'' initSt).1 :: initVs := by simp only [step]
            have hStepNext : (step (initVs, initSt) w'').2.nextFresh = initSt.nextFresh + 1 := by
              simp only [step, hYNext]
            -- v' is in the fold result; by ih applied to (y :: initVs, stY)
            have hNewInit : ∀ u ∈ (step (initVs, initSt) w'').1, ∀ k, u = Var.Fresh k →
                k < (step (initVs, initSt) w'').2.nextFresh := by
              intro u hu k huk
              rw [hStepVs] at hu
              cases hu with
              | head =>
                  simp only [FVar.toVar] at huk
                  cases huk
                  rw [hStepNext, hYId]; omega
              | tail _ hTail =>
                  have hLt := hInit u hTail k huk
                  rw [hStepNext]; omega
            exact ih _ _ hNewInit v' hv' m hv'Eq
        exact hFoldInv [] st (by intro v' hv'; simp at hv') v hv n hVEq

      -- All Fresh vars in foldRes'.1 have indices in [st'.nextFresh, foldRes'.2.nextFresh)
      have hVs'Fresh : ∀ v ∈ foldRes'.1, ∀ n, v = Var.Fresh n →
          st'.nextFresh ≤ n ∧ n < foldRes'.2.nextFresh := by
        intro v hv n hVEq
        constructor
        · -- Lower bound: n >= st'.nextFresh
          have hFoldInv : ∀ initVs : List (Var b), ∀ initSt : EncState b,
              (∀ v' ∈ initVs, ∀ m, v' = Var.Fresh m → st'.nextFresh ≤ m) →
              st'.nextFresh ≤ initSt.nextFresh →
              ∀ v' ∈ (cands.foldl step (initVs, initSt)).1, ∀ m, v' = Var.Fresh m →
                st'.nextFresh ≤ m := by
            intro initVs initSt hInit hBaseLE
            induction cands generalizing initVs initSt with
            | nil =>
              intro v' hv' m hv'Eq
              exact hInit v' hv' m hv'Eq
            | cons w'' cands' ih =>
              simp only [List.foldl_cons]
              have hYId := mkY_fst_id b t' w w'' initSt
              have hYNext := mkY_nextFresh b t' w w'' initSt
              intro v' hv' m hv'Eq
              have hStepVs : (step (initVs, initSt) w'').1 =
                  FVar.toVar b (mkY b t' w w'' initSt).1 :: initVs := by simp only [step]
              have hStepNext : (step (initVs, initSt) w'').2.nextFresh = initSt.nextFresh + 1 := by
                simp only [step, hYNext]
              have hNewInit : ∀ u ∈ (step (initVs, initSt) w'').1, ∀ k, u = Var.Fresh k →
                  st'.nextFresh ≤ k := by
                intro u hu k huk
                rw [hStepVs] at hu
                cases hu with
                | head =>
                    simp only [FVar.toVar] at huk
                    cases huk
                    rw [hYId]; exact hBaseLE
                | tail _ hTail =>
                    exact hInit u hTail k huk
              have hBaseLENew : st'.nextFresh ≤ (step (initVs, initSt) w'').2.nextFresh := by
                rw [hStepNext]; omega
              exact ih _ _ hNewInit hBaseLENew v' hv' m hv'Eq
          exact hFoldInv [] st' (by intro v' hv'; simp at hv') (Nat.le_refl _) v hv n hVEq
        · -- Upper bound: n < foldRes'.2.nextFresh (same as hVsNonFresh but for st')
          have hFoldInv : ∀ initVs : List (Var b), ∀ initSt : EncState b,
              (∀ v' ∈ initVs, ∀ m, v' = Var.Fresh m → m < initSt.nextFresh) →
              ∀ v' ∈ (cands.foldl step (initVs, initSt)).1, ∀ m, v' = Var.Fresh m →
                m < (cands.foldl step (initVs, initSt)).2.nextFresh := by
            intro initVs initSt hInit
            induction cands generalizing initVs initSt with
            | nil => exact hInit
            | cons w'' cands' ih =>
              simp only [List.foldl_cons]
              have hYId := mkY_fst_id b t' w w'' initSt
              have hYNext := mkY_nextFresh b t' w w'' initSt
              intro v' hv' m hv'Eq
              have hStepVs : (step (initVs, initSt) w'').1 =
                  FVar.toVar b (mkY b t' w w'' initSt).1 :: initVs := by simp only [step]
              have hStepNext : (step (initVs, initSt) w'').2.nextFresh = initSt.nextFresh + 1 := by
                simp only [step, hYNext]
              have hNewInit : ∀ u ∈ (step (initVs, initSt) w'').1, ∀ k, u = Var.Fresh k →
                  k < (step (initVs, initSt) w'').2.nextFresh := by
                intro u hu k huk
                rw [hStepVs] at hu
                cases hu with
                | head =>
                    simp only [FVar.toVar] at huk
                    cases huk
                    rw [hStepNext, hYId]; omega
                | tail _ hTail =>
                    have hLt := hInit u hTail k huk
                    rw [hStepNext]; omega
              exact ih _ _ hNewInit v' hv' m hv'Eq
          exact hFoldInv [] st' (by intro v' hv'; simp at hv') v hv n hVEq

      -- Prove σ' satisfies foldRes'.2.clauses (fold clauses SD)
      have hSatFold' : foldRes'.2.clauses.all (SAT.Clause.eval σ') = true := by
        rw [List.all_eq_true]
        intro clause hClause
        -- Case split: inherited from st' or new from some mkY step
        by_cases hInherited : clause ∈ st'.clauses
        · -- Inherited from st': use hSatBase + WF
          have hEval := List.all_eq_true.mp hSatBase clause hInherited
          rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEval ⊢
          obtain ⟨lit, hMem, hTrue⟩ := hEval
          refine ⟨lit, hMem, ?_⟩
          have hClauseWF := hWF clause hInherited
          cases lit with
          | pos v =>
              simp only [SAT.Lit.eval] at hTrue ⊢
              cases v with
              | Fresh n =>
                  have hLt : n < st'.nextFresh := by
                    have h := hClauseWF (SAT.Lit.pos (Var.Fresh n)) hMem
                    simp only [litFreshBelow, SAT.Lit.getVar] at h; exact h
                  simp only [σ', hLt, ↓reduceIte]; exact hTrue
              | _ => simp only [σ']; exact hTrue
          | neg v =>
              simp only [SAT.Lit.eval] at hTrue ⊢
              cases v with
              | Fresh n =>
                  have hLt : n < st'.nextFresh := by
                    have h := hClauseWF (SAT.Lit.neg (Var.Fresh n)) hMem
                    simp only [litFreshBelow, SAT.Lit.getVar] at h; exact h
                  simp only [σ', hLt, ↓reduceIte]; exact hTrue
              | _ => simp only [σ']; exact hTrue
        · -- New clause from some mkY step in the fold
          -- Use mkDw_fold_structural_determinism which we just proved
          have hSatFold'All :=
            mkDw_fold_structural_determinism b t' w cands st st' offset
              hOffset hMono hWF σ hSatBase hSatFold
          exact List.all_eq_true.mp hSatFold'All clause hClause

      -- Now handle mkBigOrIff clauses
      -- Key insight: Fresh vars in foldRes'.1 and u' have indices >= st'.nextFresh
      -- So σ' unshifts them all to corresponding vars in foldRes.1 / u

      -- Offset property for fold results
      have hFoldOffset : foldRes'.2.nextFresh - foldRes.2.nextFresh = offset := by
        rw [hFoldNextFresh, hFoldNextFresh']; omega

      -- Control vars
      have hUId : (mkBigOrIff b foldRes.1 foldRes.2).1.id = foldRes.2.nextFresh := by
        have h := mkBigOrIff_fst b foldRes.1 foldRes.2
        simp only [h]
      have hU'Id : (mkBigOrIff b foldRes'.1 foldRes'.2).1.id = foldRes'.2.nextFresh := by
        have h := mkBigOrIff_fst b foldRes'.1 foldRes'.2
        simp only [h]

      -- u'.id >= st'.nextFresh and u'.id - offset = u.id
      have hU'Ge : (mkBigOrIff b foldRes'.1 foldRes'.2).1.id ≥ st'.nextFresh := by
        rw [hU'Id, hFoldNextFresh']; omega
      have hU'Shift : (mkBigOrIff b foldRes'.1 foldRes'.2).1.id - offset =
          (mkBigOrIff b foldRes.1 foldRes.2).1.id := by
        rw [hU'Id, hUId, hFoldNextFresh, hFoldNextFresh']; omega

      -- Get satisfaction of mkBigOrIff at st
      have hSatBigOr :
          (mkBigOrIff b foldRes.1 foldRes.2).2.clauses.all (SAT.Clause.eval σ) = true := by
        have hStepEq : step = fun acc w' =>
            (FVar.toVar b (mkY b t' w w' acc.2).1 :: acc.1, (mkY b t' w w' acc.2).2) := by
          funext acc w'
          simp only [step]
        rw [List.all_eq_true]
        intro clause hClause
        rw [List.all_eq_true] at hSat
        apply hSat
        unfold mkDw
        simp only [← hStepEq, cands]
        exact hClause

      -- Prove σ' satisfies mkBigOrIff clauses at st'
      rw [List.all_eq_true]
      intro clause hClause

      -- Case split using mkBigOrIff structure
      simp only [mkBigOrIff, EncState.addClause] at hClause
      cases hClause with
      | head =>
          -- Long clause: [¬u', pos v'₁, ..., pos v'ₙ]
          -- SAT.Lit.neg (FVar.toVar b ⟨foldRes'.2.nextFresh⟩) :: foldRes'.1.map SAT.Lit.pos
          rw [SAT.Clause.eval_eq_any, List.any_eq_true]
          -- Corresponding clause at st
          have hLongSt := mkBigOrIff_long_clause_mem b foldRes.1 foldRes.2
          have hEvalSt := List.all_eq_true.mp hSatBigOr _ hLongSt
          rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt
          obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
          simp only [List.mem_cons, List.mem_map] at hLitMem
          rcases hLitMem with hNegU | ⟨v, hvMem, hLitEq⟩
          · -- ¬u is true under σ
            subst hNegU
            refine ⟨SAT.Lit.neg (FVar.toVar b ⟨foldRes'.2.nextFresh⟩), List.Mem.head _, ?_⟩
            simp only [SAT.Lit.eval, σ', FVar.toVar]
            have hU'Ge' : foldRes'.2.nextFresh ≥ st'.nextFresh := by
              rw [hFoldNextFresh']; omega
            simp only [Nat.not_lt.mpr hU'Ge', ↓reduceIte]
            have hShift : foldRes'.2.nextFresh - offset = foldRes.2.nextFresh := by
              rw [hFoldNextFresh, hFoldNextFresh']; omega
            rw [hShift]
            have hUId' : (mkBigOrIff b foldRes.1 foldRes.2).1 = ⟨foldRes.2.nextFresh⟩ :=
              mkBigOrIff_fst b foldRes.1 foldRes.2
            simp only [FVar.toVar, hUId'] at hLitTrue
            exact hLitTrue
          · -- pos v is true under σ for some v ∈ foldRes.1
            subst hLitEq
            -- v is Fresh since all vars in foldRes.1 are Fresh
            obtain ⟨n, hvFresh⟩ := hVsAllFresh v hvMem
            -- Get index of v in foldRes.1
            rcases List.mem_iff_getElem?.mp hvMem with ⟨idx, hvIdx⟩
            -- Get corresponding v' in foldRes'.1 at same index
            have hLenEq : foldRes'.1.length = foldRes.1.length :=
              (mkDw_fold_length_eq b t' w cands st st').symm
            have hIdx : idx < foldRes.1.length := (List.getElem?_eq_some_iff.mp hvIdx).1
            have hIdx' : idx < foldRes'.1.length := by rw [hLenEq]; exact hIdx
            -- Use mkDw_fold_pointwise_shift
            have hMono : st.nextFresh ≤ st'.nextFresh := by omega
            have hShift := mkDw_fold_pointwise_shift b t' w cands st st' offset hOffset hMono
            have hvIdxGet : foldRes.1[idx]? = some (Var.Fresh n) := by
              rw [hvFresh] at hvIdx; exact hvIdx
            have hv'Eq : foldRes'.1[idx]? = some (Var.Fresh (n + offset)) := by
              exact hShift idx n hvIdxGet
            -- v' ∈ foldRes'.1
            have hv'Mem : Var.Fresh (n + offset) ∈ foldRes'.1 := by
              rw [List.mem_iff_getElem?]; exact ⟨idx, hv'Eq⟩
            -- The long clause at st' contains pos v'
            refine ⟨SAT.Lit.pos (Var.Fresh (n + offset)),
                    List.mem_cons.mpr (Or.inr (List.mem_map.mpr
                      ⟨Var.Fresh (n + offset), hv'Mem, rfl⟩)), ?_⟩
            simp only [SAT.Lit.eval, σ']
            -- n + offset ≥ st'.nextFresh (since v' ∈ foldRes'.1)
            have hv'Fresh := hVs'Fresh (Var.Fresh (n + offset)) hv'Mem (n + offset) rfl
            have hGe : n + offset ≥ st'.nextFresh := hv'Fresh.1
            simp only [Nat.not_lt.mpr hGe, ↓reduceIte]
            have hShiftBack : n + offset - offset = n := by omega
            rw [hShiftBack, ← hvFresh]
            simp only [SAT.Lit.eval] at hLitTrue
            exact hLitTrue
      | tail _ hTail =>
          simp only [EncState.allocFresh] at hTail
          -- Either inherited from foldRes'.2.clauses or short clause [¬v', u']
          by_cases hInBase : clause ∈ foldRes'.2.clauses
          · -- Inherited from foldRes'.2.clauses
            exact List.all_eq_true.mp hSatFold' clause hInBase
          · -- Short clause [¬v', u'] for some v' ∈ foldRes'.1
            have hShortForm : ∃ v' ∈ foldRes'.1, clause =
                [SAT.Lit.neg v', SAT.Lit.pos (FVar.toVar b ⟨foldRes'.2.nextFresh⟩)] := by
              let u' : FVar b := ⟨foldRes'.2.nextFresh⟩
              let stepF := fun (stCur : EncState b) (v : Var b) =>
                EncState.addClause b stCur [SAT.Lit.neg v, SAT.Lit.pos (FVar.toVar b u')]
              have hFoldMem : clause ∈ (foldRes'.1.foldl stepF
                  (EncState.allocFresh b foldRes'.2).2).clauses := hTail
              have hAllocClauses :
                  (EncState.allocFresh b foldRes'.2).2.clauses = foldRes'.2.clauses :=
                EncState.allocFresh_clauses_eq b foldRes'.2
              rw [foldl_addClause_mem_iff] at hFoldMem
              cases hFoldMem with
              | inl hOld =>
                  rw [hAllocClauses] at hOld
                  exact absurd hOld hInBase
              | inr hNew =>
                  obtain ⟨v', hMem, hEq⟩ := hNew
                  exact ⟨v', hMem, hEq⟩
            obtain ⟨v', hv'Mem, hShortClause⟩ := hShortForm
            rw [hShortClause]
            -- Corresponding short clause at st: [¬v, u] where v = corresponding var in foldRes.1
            have hLenEq : foldRes'.1.length = foldRes.1.length :=
              (mkDw_fold_length_eq b t' w cands st st').symm
            -- Find index of v' in foldRes'.1
            rcases List.mem_iff_getElem?.mp hv'Mem with ⟨idx, hv'Eq⟩
            have hIdx : idx < foldRes'.1.length := by
              have h := List.getElem?_eq_some_iff.mp hv'Eq
              exact h.1
            -- Get corresponding v in foldRes.1
            have hIdxLt : idx < foldRes.1.length := by rw [← hLenEq]; exact hIdx
            have hvEx : ∃ v, foldRes.1[idx]? = some v := by
              exact ⟨foldRes.1[idx]'hIdxLt, List.getElem?_eq_some_iff.mpr ⟨hIdxLt, rfl⟩⟩
            rcases hvEx with ⟨v, hv⟩
            -- v ∈ foldRes.1
            have hvMem : v ∈ foldRes.1 := by
              rw [List.mem_iff_getElem?]; exact ⟨idx, hv⟩
            -- Short clause at st: [¬v, u]
            have hShortSt := mkBigOrIff_unit_clause_mem b foldRes.1 foldRes.2 hvMem
            have hEvalSt := List.all_eq_true.mp hSatBigOr _ hShortSt
            rw [SAT.Clause.eval_eq_any, List.any_eq_true] at hEvalSt ⊢
            obtain ⟨lit, hLitMem, hLitTrue⟩ := hEvalSt
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hLitMem
            rcases hLitMem with hNegV | hPosU
            · -- ¬v is true under σ
              have hv'Fresh := hVs'Fresh v' hv'Mem
              cases hv'Var : v' with
              | Fresh n' =>
                  have ⟨hGe, hLt⟩ := hv'Fresh n' hv'Var
                  have hvNonFresh := hVsNonFresh v hvMem
                  cases hVVar : v with
                  | Fresh n =>
                      have hvLt := hvNonFresh n hVVar
                      have hN'eq : n' = n + offset := by
                        -- Use existing lemma mkDw_fold_pointwise_shift
                        have hShiftProp :=
                          mkDw_fold_pointwise_shift b t' w cands st st' offset hOffset hMono
                        have hvGet : foldRes.1[idx]? = some (Var.Fresh n) := by
                          rw [hVVar] at hv; exact hv
                        have hv'Get : foldRes'.1[idx]? = some (Var.Fresh n') := by
                          rw [hv'Var] at hv'Eq; exact hv'Eq
                        -- So foldRes'.1[idx]? = some (Var.Fresh (n + offset))
                        -- But we also have hv'Get : foldRes'.1[idx]? = some (Var.Fresh n')
                        -- From hShiftProp and hv'Get, conclude n' = n + offset
                        have := hShiftProp idx n hvGet
                        rw [this] at hv'Get
                        injection hv'Get with hEq
                        injection hEq with hN
                        exact hN.symm
                      refine ⟨SAT.Lit.neg (Var.Fresh n'), List.mem_cons.mpr (Or.inl rfl), ?_⟩
                      simp only [SAT.Lit.eval, σ', Nat.not_lt.mpr hGe, ↓reduceIte]
                      have hShiftN : n' - offset = n := by omega
                      rw [hShiftN, ← hVVar]
                      subst hNegV
                      simp only [SAT.Lit.eval] at hLitTrue
                      exact hLitTrue
                  -- All non-Fresh cases: v ∈ foldRes.1 implies v is Fresh (contradiction)
                  | Mem _ _ | Level _ _ | Pred _ _ _ | MinQ _ _ | ReachT _ | Edge _ _
                  | Exists _ _ _ | PreEq _ _ | Seq _ _ | Rep _ | Incomp _ _ _ _ | Acc _ _ _ =>
                      have ⟨_, hvF⟩ := hVsAllFresh v hvMem; subst hvF; simp at hVVar
              -- All non-Fresh cases for v': v' ∈ foldRes'.1 implies v' is Fresh (contradiction)
              | Mem _ _ | Level _ _ | Pred _ _ _ | MinQ _ _ | ReachT _ | Edge _ _
              | Exists _ _ _ | PreEq _ _ | Seq _ _ | Rep _ | Incomp _ _ _ _ | Acc _ _ _ =>
                  have ⟨_, hv'F⟩ := hVs'AllFresh v' hv'Mem; subst hv'F; simp at hv'Var
            · -- u is true under σ (hPosU : lit = SAT.Lit.pos ...)
              rw [hPosU] at hLitTrue
              refine ⟨SAT.Lit.pos (FVar.toVar b (mkBigOrIff b foldRes'.1 foldRes'.2).1),
                      List.mem_cons.mpr (Or.inr (List.mem_singleton_self _)), ?_⟩
              simp only [SAT.Lit.eval, σ', FVar.toVar, Nat.not_lt.mpr hU'Ge, ↓reduceIte, hU'Shift]
              simp only [SAT.Lit.eval, FVar.toVar] at hLitTrue
              exact hLitTrue

    exact hGoal

end Encoding
