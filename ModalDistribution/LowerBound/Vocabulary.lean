import ModalDistribution.LowerBound.Depth
import ModalDistribution.Examples.ThyHBB4.VM

/-!
# Vocabulary for the HBB4 depth lower bound

Exposure-based correlation relations, and a concrete HBB4 vocabulary, shared by the witness model (`Witness.lean`) and the
theorem (`HBB4.lean`).
-/

namespace ModalDistribution.LowerBound
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples.ThyHBB4
open scoped Formula PreHistory

variable {S : Signature} {P : Type}

/-- The participants exposed as non-sequential in a prehistory. -/
def NonSeq (h : PreHistory P S.EventType) : Set P :=
  fun p => ¬ isSequential (Event := S.EventType) p h

/-- A correlation relation that depends on a prehistory only through its set of
non-sequential participants. -/
def ExposureBased (κ : Correlation S P) : Prop :=
  ∃ f : S.Value → S.Value → Set P → Prop,
    ∀ p (h : PreHistory P S.EventType) a b, κ p h a b ↔ f a b (NonSeq h)

namespace HBB4

/-! ## A concrete vocabulary -/

/-- Event symbols: proposals, echoes, votes indexed by rank, deliveries. -/
inductive Symbol where
  | propose | echo | vote (rank : Nat) | deliver
  deriving DecidableEq

/-- Predicate symbols: liveness and correlation. -/
inductive Pred where
  | live | corr
  deriving DecidableEq

/-- Learners and values are natural numbers: learner `0` is `L`, learners
`1, …, D` are the `L_i`; two further values serve as broadcast values. -/
abbrev sig : Signature := ⟨Symbol, Pred, Nat⟩

/-- The protocol's reading of the vocabulary. -/
def symbols : ProtocolSignature sig where
  liveSymb := .live
  correlationSymb := .corr
  proposeSymb := .propose
  echoSymb := .echo
  voteSymb := Symbol.vote
  deliverSymb := .deliver

end HBB4
end ModalDistribution.LowerBound
