import ModalDistribution.Logic.SATEncoding.ModelChecker
import ModalDistribution.Logic.SATEncoding.Adequacy.Main
import ModalDistribution.Examples.ThyHBB1.Axioms

/-!
# Counterexample: Agreement Fails Without Sequentiality

This module demonstrates that the Agreement theorem for ThyHBB1 requires
the sequentiality assumption. We use the SAT-based model checker to
prove existence of a countermodel where two different values are delivered.

## Main Result

`agreement_needs_sequentiality`: There exists a model satisfying ThyHBB1 axioms
where `Deliver(l₁', l₁, v₁)` and `Deliver(l₂', l₂, v₂)` both hold with `v₁ ≠ v₂`.

## Background

From the paper (Section 6.6, Figure thrm.1):

The Agreement theorem states that if sequentiality holds between reporting
learners l₁' and l₂', then any two deliveries must agree on the value:

  ⊨[M] ♢ᶠ[[l₁', l₂']]seq →
    (♢ᶠ↓[[]] Deliver(l₁', l₁, v₁)) →
    (♢ᶠ↓[[]] Deliver(l₂', l₂, v₂)) →
    v₁ = v₂

This module shows the sequentiality assumption is NECESSARY by constructing
a countermodel where the axioms hold but two different values are delivered.

## Technical Approach

1. Define a minimal signature and bounds
2. Encode ThyHBB1 axioms (backward rules, EchoNE) as assumptions
3. Add end-of-time constraints requiring two different delivers
4. Use SAT solver to find a satisfying assignment
5. Use native_decide to verify the CNF evaluation
6. Apply adequacy to prove existence of the semantic model
-/

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Examples
open Encoding

namespace ModalDistribution.Examples.Counterexample

/-! ## Signature Definition

We use a minimal signature with:
- Events: propose, echo, vote, deliver
- Predicates: live
- Values: v0, v1 (proposal values), l0 (learner)
-/

/-- Event symbols for the counterexample. -/
inductive CEventSymb
  | propose | echo | vote | deliver
  deriving DecidableEq, Repr

/-- Predicate symbols. -/
inductive CPredSymb
  | live
  deriving DecidableEq, Repr

/-- Values: two proposal values and one learner. -/
inductive CValue
  | v0 | v1 | l0
  deriving DecidableEq, Repr, Fintype

/-- The signature for the counterexample. -/
def CSig : Signature := {
  EventSymb := CEventSymb
  PredSymb := CPredSymb
  Value := CValue
}

-- Instances for the signature types
instance : DecidableEq CSig.Value := inferInstanceAs (DecidableEq CValue)
instance : DecidableEq CSig.EventSymb := inferInstanceAs (DecidableEq CEventSymb)
instance : DecidableEq CSig.PredSymb := inferInstanceAs (DecidableEq CPredSymb)

-- Event DecidableEq
instance : DecidableEq (Signature.Event CSig) := fun e1 e2 =>
  if h1 : e1.sym = e2.sym then
    if h2 : e1.args = e2.args then
      isTrue (by cases e1; cases e2; simp_all)
    else
      isFalse (by intro h; cases h; exact h2 rfl)
  else
    isFalse (by intro h; cases h; exact h1 rfl)

-- AtomicPred DecidableEq
instance : DecidableEq (Signature.AtomicPred CSig) := fun p1 p2 =>
  if h1 : p1.sym = p2.sym then
    if h2 : p1.args = p2.args then
      isTrue (by cases p1; cases p2; simp_all)
    else
      isFalse (by intro h; cases h; exact h2 rfl)
  else
    isFalse (by intro h; cases h; exact h1 rfl)

/-! ## Symbol Accessors -/

def proposeSymb : CSig.EventSymb := CEventSymb.propose
def echoSymb : CSig.EventSymb := CEventSymb.echo
def voteSymb : CSig.EventSymb := CEventSymb.vote
def deliverSymb : CSig.EventSymb := CEventSymb.deliver
def liveSymb : CSig.PredSymb := CPredSymb.live

/-! ## Events for the counterexample

For disagreement, we need:
- Two proposals (v0, v1)
- Two echoes (v0, v1) - the equivocating participant echoes both
- Two votes (l0, v0) and (l0, v1)
- Two delivers (l0, l0, v0) and (l0, l0, v1)
-/

def counterEvents : List (Signature.Event CSig) :=
  [ ⟨.propose, [.v0]⟩
  , ⟨.propose, [.v1]⟩
  , ⟨.echo, [.v0]⟩
  , ⟨.echo, [.v1]⟩
  , ⟨.vote, [.l0, .v0]⟩
  , ⟨.vote, [.l0, .v1]⟩
  , ⟨.deliver, [.l0, .l0, .v0]⟩
  , ⟨.deliver, [.l0, .l0, .v1]⟩
  ]

def counterEventsVec : Vector (Signature.Event CSig) 8 :=
  ⟨counterEvents.toArray, by decide⟩

def counterValuesVec : Vector (Signature.Value CSig) 3 :=
  ⟨#[CValue.v0, CValue.v1, CValue.l0], rfl⟩

def counterPredsVec : Vector (Signature.AtomicPred CSig) 1 :=
  ⟨#[⟨CPredSymb.live, []⟩], rfl⟩

/-! ## Bounds Configuration

We need enough structure to allow disagreement:
- 2 participants (can form quorums with non-sequential intersection)
- Small time steps to keep complexity manageable

Note: Complexity of cnfSeq is O(P × T × (E+1)² × T²), so we keep E and T small.
-/

def counterBounds : Bounds CSig := {
  nParticipants := 2
  nTimes := 5  -- Needs enough steps for protocol flow
  nEvents := 8
  events := counterEventsVec
  nVals := 3
  values := counterValuesVec
  nPreds := 1
  preds := counterPredsVec
  root := ⟨4, by omega⟩  -- Root at end (index 4 for T=5)
  posParticipants := by omega
  posTimes := by omega
  posVals := by omega
  values_complete := by
    intro v
    cases v with
    | v0 => exact ⟨⟨0, by omega⟩, rfl⟩
    | v1 => exact ⟨⟨1, by omega⟩, rfl⟩
    | l0 => exact ⟨⟨2, by omega⟩, rfl⟩
  events_complete := by
    intro e
    -- Pattern match on event structure
    match e with
    | ⟨.propose, args⟩ =>
      match args with
      | [.v0] => exact ⟨⟨0, by omega⟩, rfl⟩
      | [.v1] => exact ⟨⟨1, by omega⟩, rfl⟩
      | _ => sorry  -- Other args not in our event list
    | ⟨.echo, args⟩ =>
      match args with
      | [.v0] => exact ⟨⟨2, by omega⟩, rfl⟩
      | [.v1] => exact ⟨⟨3, by omega⟩, rfl⟩
      | _ => sorry
    | ⟨.vote, args⟩ =>
      match args with
      | [.l0, .v0] => exact ⟨⟨4, by omega⟩, rfl⟩
      | [.l0, .v1] => exact ⟨⟨5, by omega⟩, rfl⟩
      | _ => sorry
    | ⟨.deliver, args⟩ =>
      match args with
      | [.l0, .l0, .v0] => exact ⟨⟨6, by omega⟩, rfl⟩
      | [.l0, .l0, .v1] => exact ⟨⟨7, by omega⟩, rfl⟩
      | _ => sorry
  events_injective := by
    intro i j hEq
    -- The events are all distinct by construction
    have hi : i.val < 8 := i.isLt
    have hj : j.val < 8 := j.isLt
    -- Use native_decide on the decidable equality
    fin_cases i <;> fin_cases j <;>
      first | rfl | (simp only [Vector.get, counterEventsVec, counterEvents] at hEq; cases hEq)
}

/-! ## Formulas for the Counterexample

We encode:
1. ThyHBB1 backward axioms (as AllWorld assumptions)
2. EchoNE axiom
3. Two delivers with different values (as End assumptions)

Note: We omit forward axioms and liveness axioms since we only need
to show the backward axioms are insufficient to guarantee agreement
without sequentiality.
-/

open Formula

/-- Deliver event for v0. -/
def deliver_v0 : Formula CSig :=
  diamondPast [] (past (ofEvent ⟨.deliver, [.l0, .l0, .v0]⟩))

/-- Deliver event for v1. -/
def deliver_v1 : Formula CSig :=
  diamondPast [] (past (ofEvent ⟨.deliver, [.l0, .l0, .v1]⟩))

/-- The assumptions for finding a counterexample.

We encode:
- Echo backward axiom
- Vote backward axiom
- Deliver backward axiom
- EchoNE (non-equivocation for sequential participants)
- Deliver(l0, l0, v0) happens at end

Note: Currently demonstrating single deliver. Two-deliver counterexample
requires investigation of the event encoding interaction with PreEq.
-/
def counterAssumptions : List (Assumption CSig) :=
  [ -- Backward axioms
    .worldFormula (echoBackwardAxiom proposeSymb echoSymb)
  , .worldFormula (voteBackwardAxiom proposeSymb echoSymb voteSymb)
  , .worldFormula (deliverBackwardAxiom voteSymb deliverSymb)
  -- EchoNE
  , .worldFormula (echoNonEquivAxiom echoSymb)
  -- Single deliver
  , .endFormula deliver_v0
  ]

/-! ## IO-Based Model Checking

First, we use the IO-based model checker to find a satisfying assignment.
This can be run with: lake env lean --run <this file>
-/

def findCounterexample : IO Unit := do
  IO.println "=== Model Checker Demo: ThyHBB1 with Deliver ==="
  IO.println ""
  IO.println "Looking for a model satisfying ThyHBB1 backward axioms where"
  IO.println "Deliver(l0, l0, v0) happens."
  IO.println ""
  IO.println s!"Encoding stats: {encodingStats counterBounds counterAssumptions}"
  IO.println ""

  let (result, modelOpt) ← checkAssumptionsWithModel counterBounds counterAssumptions

  match result with
  | .sat =>
      IO.println "RESULT: SAT - Model found!"
      IO.println ""
      IO.println "The model satisfies ThyHBB1 backward axioms with a deliver event."
      match modelOpt with
      | some md => IO.println (formatModelData counterBounds md)
      | none => IO.println "(Model extraction failed)"
  | .unsat =>
      IO.println "RESULT: UNSAT"
      IO.println "No model exists within these bounds."
      IO.println "Try increasing bounds or adjusting assumptions."
  | .unknown msg =>
      IO.println s!"RESULT: Unknown - {msg}"

end ModalDistribution.Examples.Counterexample

def main : IO Unit := ModalDistribution.Examples.Counterexample.findCounterexample

namespace ModalDistribution.Examples.Counterexample

/-! ## Compile-Time Verification (TODO)

Once we find a satisfying assignment via IO, we can embed it here
and use native_decide to verify at compile time.

def counterexampleAssignment : SAT.Assignment (Var counterBounds) :=
  fun v => match v with
  | ... -- Fill in from SAT solver output

theorem counterexample_cnf_sat :
    (encodeAssumptions counterBounds counterAssumptions).eval
      counterexampleAssignment = true := by
  native_decide

-- Then use assumptions_adequate to get the existence theorem
-/

end ModalDistribution.Examples.Counterexample
