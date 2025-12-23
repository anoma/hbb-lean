import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Bot
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Eq
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Seq
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Imp
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Predicate
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Event
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.AtEnd
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Past
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Forall
import ModalDistribution.Logic.SATEncoding.Lemmas.NewClausesStructure.Diamond

/-!
# Main Structural Determinism Theorem for New Clauses

This file contains the main theorem that dispatches to individual constructor cases.
-/

open ModalDistribution
open ModalDistribution.Logic

namespace Encoding

variable {S : Signature}
variable [DecidableEq S.Value]
variable [DecidableEq S.EventType]
variable [DecidableEq S.AtomicPredType]

/-- Structural determinism for NEW clauses only.

Unlike the full `encodeFormula_structural_determinism`, this lemma:
- Only requires σ to satisfy NEW clauses from st-encoding (not inherited st.clauses)
- Only proves σ' satisfies NEW clauses from st'-encoding (not inherited st'.clauses)

This avoids the circular dependency where recursive IH would need σ to satisfy
intermediate state clauses that weren't present in the original state.

Usage in completeness: When composing witnesses for sequential encodings,
use this lemma for each sub-encoding's NEW clauses, then handle inherited
clauses separately via the clause accumulation property. -/
lemma encodeFormula_structural_determinism_new_clauses (b : Bounds S) (φ : Formula S) (w : WId b)
    (st st' : EncState b) (offset : Nat) (hOffset : offset = st'.nextFresh - st.nextFresh)
    (hMono : st.nextFresh ≤ st'.nextFresh)
    (hWF : EncState.WellFormed st) (hWF' : EncState.WellFormed st')
    (hNonFreshCompat : nonFreshClausesCompat st st')
    (σ : SAT.Assignment (Var b))
    (hSatNew : ∀ c ∈ (encodeFormula b φ w st).2.clauses, c ∉ st.clauses →
               SAT.Clause.eval σ c = true) :
    let σ' := shiftedAssignment b σ st'.nextFresh offset
    ∀ c ∈ (encodeFormula b φ w st').2.clauses, c ∉ st'.clauses →
      SAT.Clause.eval σ' c = true := by
  intro σ'
  classical
  induction φ generalizing w st st' offset with
  | bot =>
      exact structural_determinism_new_clauses_bot b w st st' offset hOffset hMono hWF σ hSatNew

  | eq v1 v2 =>
      exact structural_determinism_new_clauses_eq
        b v1 v2 w st st' offset hOffset hMono hWF σ hSatNew

  | seq =>
      exact structural_determinism_new_clauses_seq b w st st' offset hOffset hMono hWF σ hSatNew

  | imp φ1 φ2 ih1 ih2 =>
      exact structural_determinism_new_clauses_imp
        b φ1 φ2 w st st' offset hOffset hMono hWF hWF' hNonFreshCompat σ hSatNew ih1 ih2

  | predicate atom =>
      exact structural_determinism_new_clauses_predicate
        b atom w st st' offset hOffset hMono hWF hNonFreshCompat σ hSatNew

  | event atom =>
      exact structural_determinism_new_clauses_event
        b atom w st st' offset hOffset hMono hWF σ hSatNew

  | atEnd φ ih =>
      exact structural_determinism_new_clauses_atEnd
        b φ w st st' offset hOffset hMono hWF hWF' hNonFreshCompat σ hSatNew ih

  | past φ ih =>
      exact structural_determinism_new_clauses_past
        b φ w st st' offset hOffset hMono hWF hWF' hNonFreshCompat σ hSatNew ih

  | «forall» body ih =>
      exact structural_determinism_new_clauses_forall
        b body w st st' offset hOffset hMono hWF hWF' hNonFreshCompat σ hSatNew ih

  | diamond learners φ ih =>
      exact structural_determinism_new_clauses_diamond
        b learners φ w st st' offset hOffset hMono hWF hWF' hNonFreshCompat σ hSatNew ih

end Encoding
