import ModalDistribution.Core.Model
import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var
import ModalDistribution.Logic.SATEncoding.Structure
import ModalDistribution.Logic.SATEncoding.Decoder
import ModalDistribution.Logic.SATEncoding.Completeness.FitsInBounds
import ModalDistribution.Logic.SATEncoding.Adequacy.LearnerConstruction

/-!
# Assignment Construction for Completeness

This file constructs a SAT assignment from a semantic model that fits within bounds.
This is the encoder - the inverse of the decoder `modelOf`.

## Main Definitions

- `assignmentOf`: Constructs a SAT assignment from a model and FitsInBounds witness
- Semantic definitions for each variable type

## Strategy

Given a model M and FitsInBounds witness with EncodingView ev, we set:
- `Mem(H, w)` := the world w is in the prehistory at time index H
- `Level(ti, j)` := j ≤ height of prehistory at ti (monotone prefix)
- `Edge(H, H')` := there exists a world in H with time component H'
- `Pred(p, ti, k)` := predicate k holds for participant p at time ti
- `MinQ(v, Q)` := Q is a minimal quorum for value v in M.learner
- `ReachT(H)` := H is reachable from root
- etc.

## References

- FitsInBounds.lean for EncodingView and FitsInBounds structures
- Decoder.lean for modelOf (the function we're inverting)
-/

open ModalDistribution Encoding
open scoped PreHistory

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Semantic Helpers

Helper functions to extract semantic information from the model indexed by
time indices (via the EncodingView). -/

/-- Construct a WId from a semantic world using the encoding view. -/
noncomputable def widOfWorld
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (w : World (Fin b.nParticipants) (Signature.EventType S)) :
    WId b :=
  { p := w.place
  , ei := ev.evSelOf w.event
  , ti := ev.timeIndexOf w.time }

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)]
  [DecidableEq (Signature.Value S)] in
/-- The WId of a world has the same participant. -/
lemma widOfWorld_p
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (w : World (Fin b.nParticipants) (Signature.EventType S)) :
    (widOfWorld ev w).p = w.place := rfl

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)]
  [DecidableEq (Signature.Value S)] in
/-- The WId of a world has the same time index. -/
lemma widOfWorld_ti
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (w : World (Fin b.nParticipants) (Signature.EventType S)) :
    (widOfWorld ev w).ti = ev.timeIndexOf w.time := rfl

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)]
  [DecidableEq (Signature.Value S)] in
/-- The WId of a world decodes back to the same event. -/
lemma widOfWorld_event
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (w : World (Fin b.nParticipants) (Signature.EventType S)) :
    b.decodeMaybeEvent (widOfWorld ev w).ei = w.event :=
  ev.evSel_spec w.event

/-- Get the prehistory at a given time index (uses EncodingView).
    Returns empty for time indices not corresponding to reachable prehistories. -/
noncomputable def prehistoryOfTime
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (ti : b.times) :
    PreHistory (Fin b.nParticipants) (Signature.EventType S) :=
  prehistoryAt ev ti

/-- Check if a WId represents a world in the prehistory at time H. -/
noncomputable def worldInPrehistory
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) (w : WId b) : Bool := by
  classical
  -- Get the prehistory at time H
  let pH := prehistoryOfTime ev H
  -- Check if there exists a world in pH matching w's structure
  exact decide (∃ (sem : World (Fin b.nParticipants) (Signature.EventType S)),
    sem ∈ pH ∧
    sem.place = w.p ∧
    b.decodeMaybeEvent w.ei = sem.event ∧
    ev.timeIndexOf sem.time = w.ti)

/-- Check if time index H' is a happens-before predecessor of time index H. -/
noncomputable def hasEdge
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H H' : b.times) : Bool := by
  classical
  let pH := prehistoryOfTime ev H
  exact decide (∃ w ∈ pH, ev.timeIndexOf w.time = H')

/-- Check if time index H is reachable from root. -/
noncomputable def isReachableTime
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) : Bool := by
  classical
  exact decide (∃ pH ∈ reachablePreHistories M.history.val, ev.timeIndexOf pH = H)

/-- Get the fuel level for a time index (height of the corresponding prehistory). -/
noncomputable def fuelOfTime
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (ti : b.times) : ℕ :=
  rankPre (prehistoryOfTime ev ti)

/-- Check if j ≤ fuel level at ti (for Level variable). -/
noncomputable def levelAt
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (ti : b.times) (j : Fin (b.nTimes.succ)) : Bool :=
  decide (j.val ≤ fuelOfTime ev ti)

/-- Check if predicate k holds for participant p at time ti.

    This uses the Sat-style existential: true iff the predicate holds at SOME
    prehistory that is histEq to the prehistory at ti. This makes predHolds
    values automatically uniform across histEq-equivalent time indices. -/
noncomputable def predHolds
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (p : Fin b.nParticipants) (ti : b.times) (k : b.predIx) : Bool := by
  classical
  let pH := prehistoryOfTime ev ti
  let pred := b.preds.get k
  exact decide (∃ H', PreHistory.histEq H' pH ∧ pred ∈ M.predInterp p H')

/-- Check if two time indices correspond to histEq prehistories. -/
noncomputable def preEqAt
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H H' : b.times) : Bool := by
  classical
  exact decide (PreHistory.histEq (prehistoryOfTime ev H) (prehistoryOfTime ev H'))

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Key lemma: predHolds is invariant under histEq of prehistories.

    This is the critical property that makes the bidirectional transfer guards
    automatically satisfied by assignmentOf. When PreEq(ti, ti') = true (meaning
    the prehistories at ti and ti' are histEq), we have predHolds ti = predHolds ti'.

    Proof idea: predHolds uses the Sat-style existential over histEq-equivalent
    prehistories. When histEq pH pH', the set of prehistories histEq to pH is
    exactly the same as the set histEq to pH' (by transitivity and symmetry). -/
lemma predHolds_invariant_of_histEq
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (p : Fin b.nParticipants) (ti ti' : b.times) (k : b.predIx)
    (hEq : PreHistory.histEq (prehistoryOfTime ev ti) (prehistoryOfTime ev ti')) :
    predHolds ev p ti k = predHolds ev p ti' k := by
  simp only [predHolds]
  congr 1
  -- Show the existentials are equivalent
  ext
  constructor
  · intro ⟨H'', hEq'', hMem⟩
    -- H'' is histEq to pH, and pH is histEq to pH'
    -- So H'' is histEq to pH' by transitivity
    refine ⟨H'', ?_, hMem⟩
    exact PreHistory.histEq_trans hEq'' hEq
  · intro ⟨H'', hEq'', hMem⟩
    -- H'' is histEq to pH', and pH' is histEq to pH (by symmetry)
    refine ⟨H'', ?_, hMem⟩
    exact PreHistory.histEq_trans hEq'' (PreHistory.histEq_symm hEq)

/-- Check if participant p is sequential at time index H. -/
noncomputable def isSeqAt
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) (p : Fin b.nParticipants) : Bool := by
  classical
  exact decide (isSequential p (prehistoryOfTime ev H))

/-- Check if a set (as Finset) is a quorum in a semifilter. -/
noncomputable def isQuorum
    {b : Bounds S}
    (L : Semifilter (Fin b.nParticipants))
    (Q : Finset (Fin b.nParticipants)) : Bool := by
  classical
  exact decide ((Q : Set (Fin b.nParticipants)) ∈ L.quorums)

/-- Check if value index i is the representative (smallest) for its value class. -/
noncomputable def isRepresentative
    {b : Bounds S}
    (i : b.valIx) : Bool := by
  classical
  exact decide (∀ j : b.valIx, b.values.get j = b.values.get i → i ≤ j)

/-- Check if Q is a minimal quorum for value at index i.
    A quorum Q is minimal if it's in L.quorums and no proper subset is.
    Additionally, we only set MinQ to true when i is the representative for its value class.
    This is necessary for the gating constraint: MinQ(i,Q) → Rep(i). -/
noncomputable def isMinimalQuorum
    {b : Bounds S}
    (M : Model S (Fin b.nParticipants))
    (i : b.valIx) (Q : Finset (Fin b.nParticipants)) : Bool := by
  classical
  let v := b.values.get i
  let L := M.learner v
  -- Q is a quorum, no proper subset of Q is a quorum, AND i is the representative
  exact decide (
    isRepresentative i ∧
    (Q : Set (Fin b.nParticipants)) ∈ L.quorums ∧
    ∀ Q' : Finset (Fin b.nParticipants),
      (Q' : Set (Fin b.nParticipants)) ∈ L.quorums → Q' ⊆ Q → Q' = Q)

/-- Checks if any Acc(w₁, w₂, w₃) variable is true for some w₃ with
    w₃.p = w₁.p ∧ w₃.ei = w₁.ei.

    This directly matches the Acc disjunction in the incompBwd clause,
    ensuring that anyAccTrue w₁ w₂ = true iff some Acc(w₁,w₂,w₃) literal
    in the clause is true.

    Acc(w₁, w₂, w₃) = worldInPrehistory(w₂.ti, w₃) ∧ preEqAt(w₃.ti, w₁.ti)
      ∧ w₃.p = w₁.p ∧ w₃.ei = w₁.ei -/
noncomputable def anyAccTrue
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (w₁ w₂ : WId b) : Bool := by
  classical
  exact decide (∃ w₃ : WId b,
    w₃.p = w₁.p ∧ w₃.ei = w₁.ei ∧
    worldInPrehistory ev w₂.ti w₃ = true ∧
    preEqAt ev w₃.ti w₁.ti = true)

/-- Exists aggregator: there is some world in H with participant p and time t. -/
noncomputable def hasExists
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) (p : Fin b.nParticipants) (t : b.times) : Bool := by
  classical
  let pH := prehistoryOfTime ev H
  exact decide (∃ w ∈ pH, w.place = p ∧ ev.timeIndexOf w.time = t)

/-! ## World Reconstruction from WId -/

/-- Construct a semantic world from a WId using the EncodingView.
    This is the inverse of widOfWorld: worldOfWId ev (widOfWorld ev w) should be histEq to w
    (though not definitionally equal due to prehistoryAt vs original time). -/
noncomputable def worldOfWId
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (w : WId b) :
    World (Fin b.nParticipants) (Signature.EventType S) :=
  ⟨w.p, b.decodeMaybeEvent w.ei, prehistoryAt ev w.ti⟩

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)]
  [DecidableEq (Signature.Value S)] in
/-- The place of worldOfWId matches the WId's place. -/
lemma worldOfWId_place
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (w : WId b) :
    (worldOfWId ev w).place = w.p := rfl

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)]
  [DecidableEq (Signature.Value S)] in
/-- The event of worldOfWId matches the decoded event. -/
lemma worldOfWId_event
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (w : WId b) :
    (worldOfWId ev w).event = b.decodeMaybeEvent w.ei := rfl

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)]
  [DecidableEq (Signature.Value S)] in
/-- The time of worldOfWId is the prehistory at w.ti. -/
lemma worldOfWId_time
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (w : WId b) :
    (worldOfWId ev w).time = prehistoryAt ev w.ti := rfl

/-! ## Semantic-to-WId Lemmas -/

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)]
  [DecidableEq (Signature.Value S)] in
/-- If a semantic world is in the prehistory at H, then its WId is in worldInPrehistory. -/
lemma worldInPrehistory_of_mem
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) (sem : World (Fin b.nParticipants) (Signature.EventType S))
    (hMem : sem ∈ prehistoryOfTime ev H) :
    worldInPrehistory ev H (widOfWorld ev sem) = true := by
  classical
  unfold worldInPrehistory
  simp only [decide_eq_true_eq]
  refine ⟨sem, hMem, ?_, ?_, ?_⟩
  · exact (widOfWorld_p ev sem).symm
  · exact widOfWorld_event ev sem
  · exact (widOfWorld_ti ev sem).symm

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)]
  [DecidableEq (Signature.Value S)] in
/-- If hasExists is true, there exists a WId witness with worldInPrehistory true. -/
lemma hasExists_implies_worldInPrehistory
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) (p : Fin b.nParticipants) (t : b.times)
    (hEx : hasExists ev H p t = true) :
    ∃ w : WId b, w.p = p ∧ w.ti = t ∧
      w ∈ WId.allWorlds b ∧ worldInPrehistory ev H w = true := by
  classical
  unfold hasExists at hEx
  simp only [decide_eq_true_eq] at hEx
  obtain ⟨sem, hSemMem, hSemPlace, hSemTi⟩ := hEx
  let w := widOfWorld ev sem
  refine ⟨w, ?_, ?_, WId.mem_allWorlds b w, ?_⟩
  · exact hSemPlace
  · exact hSemTi
  · exact worldInPrehistory_of_mem ev H sem hSemMem

/-! ## Main Assignment Construction -/

/-- Construct a SAT assignment that encodes model M.

    For each variable type, we set its value based on the semantic model
    and the EncodingView from FitsInBounds.

    This is the inverse of `modelOf`: we aim to prove
    `modelOf b (assignmentOf b M hFits) hWF ≃ M` (modulo histEq). -/
noncomputable def assignmentOf
    (b : Bounds S)
    (M : Model S (Fin b.nParticipants))
    (hFits : FitsInBounds b M) :
    SAT.Assignment (Var b) :=
  let ev := hFits.view
  fun v =>
    match v with
    -- World membership: is the world w in the prehistory at time H?
    | Var.Mem H w => worldInPrehistory ev H w

    -- Fuel level: prefix-closed encoding of height
    | Var.Level ti j => levelAt ev ti j

    -- Predicate truth: does predicate k hold for participant p at time ti?
    | Var.Pred p ti k => predHolds ev p ti k

    -- Minimal quorum: is Q a minimal quorum for value at index i?
    | Var.MinQ i Q => isMinimalQuorum M i Q

    -- Time reachability: is H reachable from the root?
    | Var.ReachT H => isReachableTime ev H

    -- Edge: is there a world in H with time component H'?
    | Var.Edge H H' => hasEdge ev H H'

    -- Fresh Tseytin variables: set to false (don't affect WF)
    | Var.Fresh _ => false

    -- Exists aggregator: is there a world with given participant and time?
    | Var.Exists H p t => hasExists ev H p t

    -- PreEq: are the prehistories at H and H' extensionally equal?
    | Var.PreEq H H' => preEqAt ev H H'

    -- Seq: true iff participant p is sequential at prehistory H
    | Var.Seq H p => isSeqAt ev H p

    -- Rep: is this the representative index for its value class?
    | Var.Rep i => isRepresentative i

    -- Incomp: true iff pair (w₁,w₂) witnesses non-comparability at (H,p)
    -- Incomp is the negation of all escape conditions in incompBwd:
    --   - anyAccTrue w₁ w₂ = some Acc(w₁,w₂,w₃) is true
    --   - anyAccTrue w₂ w₁ = some Acc(w₂,w₁,w₃) is true
    --   - preEqAt = worlds have equal times (only relevant when events match)
    -- The PreEq escape is only included in the clause when w₁.ei = w₂.ei,
    -- because worldEq requires both same event AND same prehistory.
    -- So Incomp = Mem(H,w₁) ∧ Mem(H,w₂) ∧ ¬anyAccTrue(w₁,w₂) ∧
    --   ¬anyAccTrue(w₂,w₁) ∧ (ei match → ¬preEq)
    | Var.Incomp H _ w₁ w₂ =>
        worldInPrehistory ev H w₁ &&
        worldInPrehistory ev H w₂ &&
        !anyAccTrue ev w₁ w₂ &&
        !anyAccTrue ev w₂ w₁ &&
        (if w₁.ei = w₂.ei then !preEqAt ev w₁.ti w₂.ti else true)

    -- Acc: accessibility witness variable
    -- Acc(w₁, w₂, w₃) means w₃ witnesses that w₁ is accessible from w₂
    -- True iff Mem(w₂.ti, w₃) ∧ PreEq(w₃.ti, w₁.ti) ∧ w₃.p = w₁.p ∧ w₃.ei = w₁.ei
    | Var.Acc w₁ w₂ w₃ =>
        worldInPrehistory ev w₂.ti w₃ &&
        preEqAt ev w₃.ti w₁.ti &&
        decide (w₃.p = w₁.p) &&
        decide (w₃.ei = w₁.ei)

/-! ## Basic Properties of assignmentOf -/

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- Mem reflects actual world membership. -/
lemma assignmentOf_Mem
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) (w : WId b) :
    assignmentOf b M hFits (Var.Mem H w) = worldInPrehistory hFits.view H w := rfl

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- Level reflects fuel threshold. -/
lemma assignmentOf_Level
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (ti : b.times) (j : Fin (b.nTimes.succ)) :
    assignmentOf b M hFits (Var.Level ti j) = levelAt hFits.view ti j := rfl

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- Seq reflects sequentiality at the prehistory. -/
lemma assignmentOf_Seq
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) (p : Fin b.nParticipants) :
    assignmentOf b M hFits (Var.Seq H p) = isSeqAt hFits.view H p := rfl

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- ReachT reflects time reachability. -/
lemma assignmentOf_ReachT
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) :
    assignmentOf b M hFits (Var.ReachT H) = isReachableTime hFits.view H := rfl

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- Edge reflects happens-before between time indices. -/
lemma assignmentOf_Edge
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H H' : b.times) :
    assignmentOf b M hFits (Var.Edge H H') = hasEdge hFits.view H H' := rfl

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- Incomp reflects world-pair incomparability: both in prehistory, no Acc witness, and
    (if events match) no PreEq. The PreEq condition only matters when events match,
    since worldEq requires both same event AND same prehistory. -/
lemma assignmentOf_Incomp
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H : b.times) (p : Fin b.nParticipants) (w₁ w₂ : WId b) :
    assignmentOf b M hFits (Var.Incomp H p w₁ w₂) =
      (worldInPrehistory hFits.view H w₁ &&
       worldInPrehistory hFits.view H w₂ &&
       !anyAccTrue hFits.view w₁ w₂ &&
       !anyAccTrue hFits.view w₂ w₁ &&
       (if w₁.ei = w₂.ei then !preEqAt hFits.view w₁.ti w₂.ti else true)) := rfl

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- Pred reflects predHolds at a time index. -/
lemma assignmentOf_Pred
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (p : Fin b.nParticipants) (ti : b.times) (k : b.predIx) :
    assignmentOf b M hFits (Var.Pred p ti k) = predHolds hFits.view p ti k := rfl

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- PreEq reflects histEq between prehistories at two time indices. -/
lemma assignmentOf_PreEq
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (H H' : b.times) :
    assignmentOf b M hFits (Var.PreEq H H') = preEqAt hFits.view H H' := rfl

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- Acc reflects accessibility witness. -/
lemma assignmentOf_Acc
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    (w₁ w₂ w₃ : WId b) :
    assignmentOf b M hFits (Var.Acc w₁ w₂ w₃) =
      (worldInPrehistory hFits.view w₂.ti w₃ &&
       preEqAt hFits.view w₃.ti w₁.ti &&
       decide (w₃.p = w₁.p) &&
       decide (w₃.ei = w₁.ei)) := rfl

/-! ## Accessibility-to-Acc Linking Lemmas

These lemmas connect semantic accessibility to the Acc variable encoding.
They are critical for proving incompBwd_satisfied in completeness. -/

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If a semantic world `v` is in a prehistory at time H, and H is reachable,
    then the WId of `v` has worldInPrehistory = true at H. -/
lemma worldInPrehistory_of_mem_reachable
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    {H : PreHistory (Fin b.nParticipants) (Signature.EventType S)}
    (hReach : H ∈ reachablePreHistories M.history.val)
    {v : World (Fin b.nParticipants) (Signature.EventType S)}
    (hMem : v ∈ H) :
    worldInPrehistory ev (ev.timeIndexOf H) (widOfWorld ev v) = true := by
  classical
  unfold worldInPrehistory
  simp only [decide_eq_true_eq]
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · -- v ∈ prehistoryOfTime ev (ev.timeIndexOf H) = prehistoryAt ev (ev.timeIndexOf H) = H
    unfold prehistoryOfTime
    rw [prehistoryAt_of_reachable ev hReach]
    exact hMem
  · -- v.place = widOfWorld ev v |>.p
    exact (widOfWorld_p ev v).symm
  · -- decodeMaybeEvent = v.event
    exact widOfWorld_event ev v
  · -- timeIndexOf v.time = widOfWorld ev v |>.ti
    exact (widOfWorld_ti ev v).symm

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If two prehistories are histEq and both reachable,
    their time indices give histEq prehistoryAt. -/
lemma preEqAt_of_histEq_reachable
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    {H₁ H₂ : PreHistory (Fin b.nParticipants) (Signature.EventType S)}
    (hReach₁ : H₁ ∈ reachablePreHistories M.history.val)
    (hReach₂ : H₂ ∈ reachablePreHistories M.history.val)
    (hEq : PreHistory.histEq H₁ H₂) :
    preEqAt ev (ev.timeIndexOf H₁) (ev.timeIndexOf H₂) = true := by
  classical
  unfold preEqAt
  simp only [decide_eq_true_eq]
  unfold prehistoryOfTime
  rw [prehistoryAt_of_reachable ev hReach₁]
  rw [prehistoryAt_of_reachable ev hReach₂]
  exact hEq

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Key linking lemma: If semantic accessibility `t₁ ≪ t₂` holds between worlds
    whose times are reachable, then there exists a WId witness w₃ such that
    Acc(widOfWorld t₁, widOfWorld t₂, w₃) = true under assignmentOf.

    This is the critical lemma for proving incompBwd_satisfied. -/
lemma acc_true_of_accessible
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (hFits : FitsInBounds b M)
    {t₁ t₂ : World (Fin b.nParticipants) (Signature.EventType S)}
    (hReach₁ : t₁.time ∈ reachablePreHistories M.history.val)
    (hReach₂ : t₂.time ∈ reachablePreHistories M.history.val)
    (hAcc : World.accessible t₁ t₂) :
    ∃ w₃ : WId b,
      w₃.p = (widOfWorld hFits.view t₁).p ∧
      w₃.ei = (widOfWorld hFits.view t₁).ei ∧
      assignmentOf b M hFits
        (Var.Acc (widOfWorld hFits.view t₁) (widOfWorld hFits.view t₂) w₃)
        = true := by
  classical
  -- From accessibility: ∃ v ∈ t₂.time, worldEq t₁ v
  obtain ⟨v, hvMem, hvEq⟩ := hAcc
  -- The witness is widOfWorld ev v
  let ev := hFits.view
  let w₃ := widOfWorld ev v
  use w₃
  -- Extract worldEq properties
  have hvPlace : v.place = t₁.place := (PreHistory.worldEq_place hvEq).symm
  have hvEvent : v.event = t₁.event := by
    have := (PreHistory.worldEq_spec t₁ v).1 hvEq
    exact this.2.1.symm
  have hvTime : PreHistory.histEq v.time t₁.time := by
    have := (PreHistory.worldEq_spec t₁ v).1 hvEq
    exact PreHistory.histEq_symm this.2.2
  have hReachV : v.time ∈ reachablePreHistories M.history.val :=
    time_mem_reachablePreHistories_of_mem_history hReach₂ hvMem
  -- Show all three conjuncts
  -- w₃ = widOfWorld ev v, so w₃.p = v.place, w₃.ei = ev.evSelOf v.event
  -- widOfWorld ev t₁ has .p = t₁.place, .ei = ev.evSelOf t₁.event
  -- From hvPlace: v.place = t₁.place and hvEvent: v.event = t₁.event
  have hW3P : w₃.p = (widOfWorld ev t₁).p := hvPlace
  have hW3Ei : w₃.ei = (widOfWorld ev t₁).ei := by
    change ev.evSelOf v.event = ev.evSelOf t₁.event
    rw [hvEvent]
  refine ⟨hW3P, hW3Ei, ?_⟩
  -- Acc = true
  rw [assignmentOf_Acc]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  -- Structure: (((a && b) && c) && d) becomes (((a ∧ b) ∧ c) ∧ d) after simp
  -- Need: worldInPrehistory, preEqAt, w₃.p = w₁.p, w₃.ei = w₁.ei
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- worldInPrehistory ev (widOfWorld ev t₂).ti w₃ = true
    have hWip := worldInPrehistory_of_mem_reachable ev hReach₂ hvMem
    simp only [widOfWorld] at hWip ⊢
    exact hWip
  · -- preEqAt ev w₃.ti (widOfWorld ev t₁).ti = true
    have hPre := preEqAt_of_histEq_reachable ev hReachV hReach₁ hvTime
    simp only [widOfWorld] at hPre ⊢
    exact hPre
  · -- w₃.p = (widOfWorld ev t₁).p
    exact hW3P
  · -- w₃.ei = (widOfWorld ev t₁).ei
    exact hW3Ei

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- Converse direction: if two semantic worlds are worldEq, then preEqAt holds. -/
lemma preEqAt_of_worldEq
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    {t₁ t₂ : World (Fin b.nParticipants) (Signature.EventType S)}
    (hReach₁ : t₁.time ∈ reachablePreHistories M.history.val)
    (hReach₂ : t₂.time ∈ reachablePreHistories M.history.val)
    (hEq : PreHistory.worldEq t₁ t₂) :
    preEqAt ev (ev.timeIndexOf t₁.time) (ev.timeIndexOf t₂.time) = true := by
  have hTimeEq : PreHistory.histEq t₁.time t₂.time := by
    have := (PreHistory.worldEq_spec t₁ t₂).1 hEq
    exact this.2.2
  exact preEqAt_of_histEq_reachable ev hReach₁ hReach₂ hTimeEq

/-! ## worldInPrehistory Extraction Lemma -/

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)]
  [DecidableEq (Signature.Value S)] in
/-- Extract a semantic world from worldInPrehistory = true.

    If worldInPrehistory ev H w = true, there exists a semantic world sem in the
    prehistory at H that corresponds to w. -/
lemma extract_of_worldInPrehistory
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) (w : WId b)
    (hMem : worldInPrehistory ev H w = true) :
    ∃ sem : World (Fin b.nParticipants) (Signature.EventType S),
      sem ∈ prehistoryOfTime ev H ∧
      sem.place = w.p ∧
      b.decodeMaybeEvent w.ei = sem.event ∧
      ev.timeIndexOf sem.time = w.ti := by
  classical
  unfold worldInPrehistory at hMem
  simp only [decide_eq_true_eq] at hMem
  exact hMem

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If semantic accessibility holds (sem₁ ≪ sem₂), then anyAccTrue is true.

    sem₁ ≪ sem₂ means ∃ v ∈ sem₂.time with worldEq sem₁ v.
    This v witnesses anyAccTrue because:
    - v is in prehistory at sem₂.ti
    - v has same time as sem₁ (from worldEq), so preEqAt holds
    - v has same place/event as sem₁ (from worldEq)

    Note: This requires reachability to ensure the EncodingView can index the times. -/
lemma anyAccTrue_of_accessible
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    {sem₁ sem₂ : World (Fin b.nParticipants) (Signature.EventType S)}
    (hReach₁ : sem₁.time ∈ reachablePreHistories M.history.val)
    (hReach₂ : sem₂.time ∈ reachablePreHistories M.history.val)
    (hAcc : sem₁ ≪ sem₂) :
    anyAccTrue ev (widOfWorld ev sem₁) (widOfWorld ev sem₂) = true := by
  classical
  unfold World.accessible at hAcc
  obtain ⟨v, hvMem, hvEq⟩ := hAcc
  unfold anyAccTrue
  simp only [decide_eq_true_eq]
  -- Extract worldEq properties: v has same place/event as sem₁, and histEq times
  have hvPlace := PreHistory.worldEq_place hvEq
  have hvEvent := PreHistory.worldEq_event hvEq
  have hvTime := PreHistory.worldEq_time hvEq
  -- Show v.time is reachable (v ∈ sem₂.time which is reachable)
  have hReachV := time_mem_reachablePreHistories_of_mem_history hReach₂ hvMem
  -- Construct witness: w₃ = widOfWorld ev v
  use widOfWorld ev v
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- w₃.p = (widOfWorld ev sem₁).p
    simp only [widOfWorld, hvPlace]
  · -- w₃.ei = (widOfWorld ev sem₁).ei
    simp only [widOfWorld, hvEvent]
  · -- worldInPrehistory ev (widOfWorld ev sem₂).ti w₃ = true
    exact worldInPrehistory_of_mem_reachable ev hReach₂ hvMem
  · -- preEqAt ev w₃.ti (widOfWorld ev sem₁).ti = true
    exact preEqAt_of_histEq_reachable ev hReachV hReach₁ (PreHistory.histEq_symm hvTime)

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If semantic accessibility doesn't hold, then anyAccTrue is false.

    This is the forward direction needed for completeness of Incomp encoding. -/
lemma anyAccTrue_false_of_not_accessible
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    {sem₁ sem₂ : World (Fin b.nParticipants) (Signature.EventType S)}
    (hReach₁ : sem₁.time ∈ reachablePreHistories M.history.val)
    (hReach₂ : sem₂.time ∈ reachablePreHistories M.history.val)
    (hNoAcc : ¬(sem₁ ≪ sem₂)) :
    anyAccTrue ev (widOfWorld ev sem₁) (widOfWorld ev sem₂) = false := by
  by_contra hAnyAcc
  simp only [Bool.not_eq_false] at hAnyAcc
  have hAcc := anyAccTrue_of_accessible ev hReach₁ hReach₂
  -- If anyAccTrue = true but ¬accessible, we need a contradiction
  -- Actually, anyAccTrue_of_accessible goes: accessible → anyAccTrue = true
  -- So this can't directly give us a contradiction...
  -- We need to show: if anyAccTrue = true, then accessible
  -- This requires the reverse direction lemma or a different approach.
  -- Actually, we can use contraposition: anyAccTrue = false ↔ ¬accessible
  -- Since we already have anyAccTrue_of_accessible: accessible → anyAccTrue = true
  -- Contrapositive: anyAccTrue ≠ true → ¬accessible, i.e., anyAccTrue = false → ¬accessible
  -- But we need: ¬accessible → anyAccTrue = false
  -- This requires proving: anyAccTrue = true → accessible
  -- Let's prove this by unfolding anyAccTrue
  classical
  unfold anyAccTrue at hAnyAcc
  simp only [decide_eq_true_eq] at hAnyAcc
  obtain ⟨w₃, hW3p, hW3ei, hW3mem, hW3preEq⟩ := hAnyAcc
  -- w₃ witnesses: w₃.p = (widOfWorld sem₁).p = sem₁.place
  --               w₃.ei = (widOfWorld sem₁).ei = evSelOf sem₁.event
  --               worldInPrehistory (widOfWorld sem₂).ti w₃ = true
  --               preEqAt w₃.ti (widOfWorld sem₁).ti = true
  -- Extract semantic world from w₃
  unfold worldInPrehistory at hW3mem
  simp only [decide_eq_true_eq] at hW3mem
  obtain ⟨v, hvMem, hvPlace, hvEvent, hvTi⟩ := hW3mem
  -- v is in prehistoryAt ev (widOfWorld sem₂).ti
  -- widOfWorld sem₂ has .ti = ev.timeIndexOf sem₂.time
  -- So v ∈ prehistoryAt ev (ev.timeIndexOf sem₂.time)
  -- For reachable sem₂, prehistoryAt ev (ev.timeIndexOf sem₂.time) = sem₂.time
  -- So v ∈ sem₂.time
  have hVinSem2 : v ∈ sem₂.time := by
    have hPAEq := prehistoryAt_of_reachable ev hReach₂
    -- hvMem : v ∈ prehistoryOfTime ev (widOfWorld ev sem₂).ti
    -- (widOfWorld ev sem₂).ti = ev.timeIndexOf sem₂.time by definition
    -- prehistoryOfTime ev _ = prehistoryAt ev _ by definition
    -- prehistoryAt ev (ev.timeIndexOf sem₂.time) = sem₂.time by hPAEq
    unfold prehistoryOfTime at hvMem
    simp only [widOfWorld] at hvMem
    rw [hPAEq] at hvMem
    exact hvMem
  -- From preEqAt: prehistoryOfTime ev w₃.ti ≃ prehistoryOfTime ev (widOfWorld sem₁).ti
  -- i.e., prehistoryAt ev w₃.ti ≃ sem₁.time
  unfold preEqAt at hW3preEq
  simp only [decide_eq_true_eq] at hW3preEq
  -- hW3preEq : histEq (prehistoryOfTime ev w₃.ti) (prehistoryOfTime ev (widOfWorld sem₁).ti)
  -- prehistoryOfTime ev (widOfWorld sem₁).ti = sem₁.time (by reachability)
  have hSem1TimeEq : prehistoryOfTime ev (widOfWorld ev sem₁).ti = sem₁.time := by
    unfold prehistoryOfTime widOfWorld
    exact prehistoryAt_of_reachable ev hReach₁
  -- v.time = prehistoryAt ev w₃.ti
  -- We need: v.time ≃ sem₁.time
  -- From hvTi: ev.timeIndexOf v.time = w₃.ti
  -- So prehistoryAt ev w₃.ti = prehistoryAt ev (ev.timeIndexOf v.time)
  -- For reachable v.time, prehistoryAt ev (ev.timeIndexOf v.time) = v.time
  -- Need to show v.time is reachable
  have hReachV : v.time ∈ reachablePreHistories M.history.val :=
    time_mem_reachablePreHistories_of_mem_history hReach₂ hVinSem2
  have hVTimeEq : prehistoryOfTime ev w₃.ti = v.time := by
    unfold prehistoryOfTime
    rw [← hvTi]
    exact prehistoryAt_of_reachable ev hReachV
  -- Now: histEq v.time sem₁.time
  have hHistEq : PreHistory.histEq v.time sem₁.time := by
    rw [hVTimeEq, hSem1TimeEq] at hW3preEq
    exact hW3preEq
  -- v has: place = w₃.p = sem₁.place
  --        event decoded from w₃.ei = sem₁.event
  --        time ≃ sem₁.time
  -- So worldEq v sem₁
  have hvPlaceSem1 : v.place = sem₁.place := by
    rw [hvPlace, hW3p]
    rfl
  have hvEventSem1 : v.event = sem₁.event := by
    -- hW3ei : w₃.ei = (widOfWorld ev sem₁).ei = ev.evSelOf sem₁.event
    -- hvEvent : b.decodeMaybeEvent w₃.ei = v.event
    simp only [widOfWorld] at hW3ei
    rw [hW3ei] at hvEvent
    exact hvEvent.symm.trans (ev.evSel_spec sem₁.event)
  have hWorldEq : PreHistory.worldEq sem₁ v := by
    rw [PreHistory.worldEq_spec]
    exact ⟨hvPlaceSem1.symm, hvEventSem1.symm, PreHistory.histEq_symm hHistEq⟩
  -- sem₁ ≪ sem₂ via v ∈ sem₂.time with worldEq sem₁ v
  have hAcc : sem₁ ≪ sem₂ := ⟨v, hVinSem2, hWorldEq⟩
  exact hNoAcc hAcc

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If anyAccTrue is false, then semantic accessibility doesn't hold.

    This is the contrapositive form useful for proving sequentiality contradictions. -/
lemma not_accessible_of_anyAccTrue_false
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    {sem₁ sem₂ : World (Fin b.nParticipants) (Signature.EventType S)}
    (hReach₁ : sem₁.time ∈ reachablePreHistories M.history.val)
    (hReach₂ : sem₂.time ∈ reachablePreHistories M.history.val)
    (hNoAcc : anyAccTrue ev (widOfWorld ev sem₁) (widOfWorld ev sem₂) = false) :
    ¬(sem₁ ≪ sem₂) := by
  intro hAcc
  have := anyAccTrue_of_accessible ev hReach₁ hReach₂ hAcc
  rw [this] at hNoAcc
  simp at hNoAcc

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] [DecidableEq S.Value] in
/-- If worldEq doesn't hold between two worlds with the same event, then preEqAt is false.

    worldEq sem₁ sem₂ requires same place, same event, and same time (histEq).
    If events are the same but worldEq fails, it's because:
    - places differ, OR
    - times differ (so preEqAt is false)

    For worlds extracted from the same prehistory with the same event,
    if worldEq fails it must be because preEqAt fails. -/
lemma preEqAt_false_of_not_worldEq_same_event
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    {sem₁ sem₂ : World (Fin b.nParticipants) (Signature.EventType S)}
    (hReach₁ : sem₁.time ∈ reachablePreHistories M.history.val)
    (hReach₂ : sem₂.time ∈ reachablePreHistories M.history.val)
    (hSamePlace : sem₁.place = sem₂.place)
    (hSameEvent : sem₁.event = sem₂.event)
    (hNotEq : ¬PreHistory.worldEq sem₁ sem₂) :
    preEqAt ev (ev.timeIndexOf sem₁.time) (ev.timeIndexOf sem₂.time) = false := by
  by_contra hPreEq
  simp only [Bool.not_eq_false] at hPreEq
  -- preEqAt = true means histEq between the prehistories at those time indices
  unfold preEqAt at hPreEq
  simp only [decide_eq_true_eq] at hPreEq
  -- hPreEq : histEq (prehistoryOfTime ev ti₁) (prehistoryOfTime ev ti₂)
  -- We need histEq sem₁.time sem₂.time
  -- By reachability, prehistoryOfTime ev (timeIndexOf sem.time) = sem.time (def eq)
  have hEq₁ : prehistoryOfTime ev (ev.timeIndexOf sem₁.time) = sem₁.time := by
    unfold prehistoryOfTime
    exact prehistoryAt_of_reachable ev hReach₁
  have hEq₂ : prehistoryOfTime ev (ev.timeIndexOf sem₂.time) = sem₂.time := by
    unfold prehistoryOfTime
    exact prehistoryAt_of_reachable ev hReach₂
  -- Chain: sem₁.time = prehistoryOfTime ti₁ ≃ prehistoryOfTime ti₂ = sem₂.time
  have hHistEq : PreHistory.histEq sem₁.time sem₂.time := by
    rw [← hEq₁, ← hEq₂]
    exact hPreEq
  -- With same place, same event, and histEq times, worldEq should hold
  have hWorldEq : PreHistory.worldEq sem₁ sem₂ := by
    rw [PreHistory.worldEq_spec]
    exact ⟨hSamePlace, hSameEvent, hHistEq⟩
  exact hNotEq hWorldEq

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)]
  [DecidableEq (Signature.Value S)] in
/-- Sequentiality contradiction: If two p-worlds in a sequential prehistory are
    incomparable (no accessibility in either direction) and not worldEq, contradiction.

    This is the key semantic bridge lemma for seqToNoIncomp_satisfied. -/
lemma sequentiality_contradiction
    {b : Bounds S}
    {M : Model S (Fin b.nParticipants)}
    (ev : EncodingView b M)
    (H : b.times) (p : Fin b.nParticipants)
    (sem₁ sem₂ : World (Fin b.nParticipants) (Signature.EventType S))
    (hMem₁ : sem₁ ∈ prehistoryOfTime ev H)
    (hMem₂ : sem₂ ∈ prehistoryOfTime ev H)
    (hP₁ : sem₁.place = p)
    (hP₂ : sem₂.place = p)
    (hSeq : isSequential p (prehistoryOfTime ev H))
    (hNoAcc12 : ¬(sem₁ ≪ sem₂))
    (hNoAcc21 : ¬(sem₂ ≪ sem₁))
    (hNotEq : ¬PreHistory.worldEq sem₁ sem₂) : False := by
  have hComp := hSeq hMem₁ hMem₂ hP₁ hP₂
  rcases hComp with hAcc12 | hAcc21 | hWEq
  · exact hNoAcc12 hAcc12
  · exact hNoAcc21 hAcc21
  · exact hNotEq hWEq

/-! ## Helper lemmas for cnfLearners satisfaction -/

/-- Helper: if find? returns some y, there exists position i where xs[i] = y,
    p y = true, and all elements before position i have p = false. -/
private theorem find?_returns_first {α : Type*} (p : α → Bool) (xs : List α) (y : α)
    (hFind : xs.find? p = some y) :
    ∃ i : Fin xs.length, xs[i] = y ∧ p y = true ∧
      ∀ j : Fin xs.length, j < i → p xs[j] = false := by
  induction xs with
  | nil => simp at hFind
  | cons a as ih =>
    simp only [List.find?_cons] at hFind
    split at hFind
    case h_1 hPa =>
      injection hFind with hay
      subst hay
      refine ⟨⟨0, Nat.zero_lt_succ _⟩, rfl, hPa, ?_⟩
      intro j hj
      exact absurd hj (Nat.not_lt_zero j)
    case h_2 hNa =>
      obtain ⟨i, hi, hPy, hBefore⟩ := ih hFind
      refine ⟨⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩, ?_, hPy, ?_⟩
      · exact hi
      · intro j hj
        cases j with
        | mk jval hjlt =>
          cases jval with
          | zero => exact hNa
          | succ jval' =>
            have hJval'Lt : jval' < as.length := Nat.lt_of_succ_lt_succ hjlt
            have : (⟨jval', hJval'Lt⟩ : Fin as.length) < i := by
              simp only [Fin.lt_iff_val_lt_val] at hj ⊢
              omega
            exact hBefore ⟨jval', hJval'Lt⟩ this

/-- Helper: finRange element at position i is ⟨i.val, _⟩ for Fin index -/
private lemma finRange_getElem_fin {n : Nat} (i : Fin (List.finRange n).length) :
    (List.finRange n)[i] = ⟨i.val, by have := i.isLt; simp at this; exact this⟩ := by
  have hILt : i.val < n := by have := i.isLt; simp at this; exact this
  simp only [List.finRange]
  have h : (List.ofFn (fun i => i))[i.val]'(by simp; exact hILt) = ⟨i.val, hILt⟩ := by
    rw [List.getElem_ofFn]
  convert h using 1

/-- find? on finRange returns the smallest index satisfying the predicate. -/
lemma find?_finRange_min {n : Nat} (p : Fin n → Bool) (y : Fin n)
    (hFind : (List.finRange n).find? p = some y) :
    ∀ j : Fin n, p j = true → y ≤ j := by
  intro j hPj
  by_contra hNotLe
  push_neg at hNotLe
  have hJltY : j.val < y.val := hNotLe
  obtain ⟨i, hi, hPy, hBefore⟩ := find?_returns_first p (List.finRange n) y hFind
  have hYval : y.val = i.val := by
    rw [finRange_getElem_fin] at hi
    exact (Fin.ext_iff.mp hi.symm)
  have hJltI : j.val < i.val := by omega
  have hJidxLt : j.val < (List.finRange n).length := by
    simp only [List.length_finRange]
    exact j.isLt
  let jIdx : Fin (List.finRange n).length := ⟨j.val, hJidxLt⟩
  have hJidx : jIdx < i := by simp only [Fin.lt_iff_val_lt_val]; omega
  have hPjFalse := hBefore jIdx hJidx
  rw [finRange_getElem_fin] at hPjFalse
  have hContra : p j = false := hPjFalse
  rw [hPj] at hContra
  exact Bool.noConfusion hContra

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- findValueIndex returns the first (smallest) index for a value.
    This depends on the fact that find? on finRange returns the minimum index. -/
lemma findValueIndex_spec {b : Bounds S} (v : Signature.Value S)
    (hEx : ∃ i : b.valIx, b.values.get i = v) :
    b.values.get (b.findValueIndex v) = v ∧
    ∀ j : b.valIx, b.values.get j = v → b.findValueIndex v ≤ j := by
  classical
  unfold Bounds.findValueIndex
  -- Get predicate for find?
  let pred : b.valIx → Bool := fun i => decide (b.values.get i = v)
  -- Show Fin.find? succeeds because hEx guarantees v exists
  have hPredJ : ∃ j : b.valIx, pred j = true := by
    obtain ⟨j, hj⟩ := hEx
    exact ⟨j, by simp only [pred, decide_eq_true_eq]; exact hj⟩
  -- Fin.find? returns some when predicate is satisfiable
  have hFinFindSome : (Fin.find? pred).isSome := by
    rw [Fin.find?_isSome_iff]
    obtain ⟨j, hPredJ'⟩ := hPredJ
    exact ⟨j, by simp only [pred] at hPredJ' ⊢; exact hPredJ'⟩
  -- Get the actual index from Fin.find?
  have hFinFind : ∃ idx, Fin.find? pred = some idx := by
    cases h : Fin.find? pred with
    | none =>
      rw [h] at hFinFindSome
      simp at hFinFindSome
    | some idx => exact ⟨idx, rfl⟩
  obtain ⟨idx, hFind⟩ := hFinFind
  -- Convert to List.find? on finRange using Fin.find?_eq_find?_finRange
  have hListFind : (List.finRange b.nVals).find? pred = some idx := by
    rw [← Fin.find?_eq_find?_finRange]
    exact hFind
  rw [hListFind]
  constructor
  · -- Show b.values.get idx = v (using Fin.eq_true_of_find?_eq_some)
    have hPredIdx : pred idx = true := Fin.eq_true_of_find?_eq_some hFind
    simp only [pred, decide_eq_true_eq] at hPredIdx
    exact hPredIdx
  · -- Show idx is minimal
    intro j hj
    have hPredJ' : pred j = true := by simp only [pred, decide_eq_true_eq]; exact hj
    exact find?_finRange_min pred idx hListFind j hPredJ'

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- findValueIndex is its own representative. -/
lemma isRepresentative_findValueIndex {b : Bounds S} (v : Signature.Value S)
    (hEx : ∃ i : b.valIx, b.values.get i = v) :
    isRepresentative (b.findValueIndex v) = true := by
  classical
  unfold isRepresentative
  simp only [decide_eq_true_eq]
  intro j hj
  have ⟨hVal, hMin⟩ := findValueIndex_spec v hEx
  rw [hVal] at hj
  exact hMin j hj

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- findValueIndex is in the list of value indices for that value. -/
lemma findValueIndex_mem_valueIndices {b : Bounds S} (v : Signature.Value S)
    (hEx : ∃ i : b.valIx, b.values.get i = v) :
    b.findValueIndex v ∈ valueIndices b v := by
  simp only [valueIndices, List.mem_filterMap, List.mem_finRange, true_and]
  use b.findValueIndex v
  have ⟨hVal, _⟩ := findValueIndex_spec v hEx
  simp only [hVal, ↓reduceIte]

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- If an index has the same value as findValueIndex but is different,
    it is not a representative. -/
lemma isRepresentative_false_of_ne_findValueIndex
    {b : Bounds S} (i : b.valIx) (v : Signature.Value S)
    (hEx : ∃ j : b.valIx, b.values.get j = v)
    (hVal : b.values.get i = v)
    (hNe : i ≠ b.findValueIndex v) :
    isRepresentative i = false := by
  classical
  unfold isRepresentative
  simp only [decide_eq_false_iff_not, not_forall]
  -- Witness: findValueIndex v
  -- Goal: ∃ j, b.values.get j = b.values.get i ∧ ¬(i ≤ j)
  have ⟨hValIdx, hMin⟩ := findValueIndex_spec v hEx
  refine ⟨b.findValueIndex v, ?_, ?_⟩
  · -- b.values.get (findValueIndex v) = b.values.get i
    rw [hValIdx, hVal]
  · -- ¬(i ≤ findValueIndex v)
    -- We know findValueIndex v ≤ i (from minimality) and i ≠ findValueIndex v
    -- So findValueIndex v < i, which means ¬(i ≤ findValueIndex v)
    have hLe : b.findValueIndex v ≤ i := hMin i hVal
    -- hNe : i ≠ findValueIndex v means their Nat values are different
    have hNeNat : (b.findValueIndex v).val ≠ i.val := fun h => hNe (Fin.ext h.symm)
    -- From hLe and hNeNat, we get findValueIndex v < i
    have hLt : (b.findValueIndex v).val < i.val := Nat.lt_of_le_of_ne hLe hNeNat
    -- Therefore ¬(i ≤ findValueIndex v)
    exact Nat.not_le.mpr hLt

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)]
  [DecidableEq (Signature.Value S)] in
/-- For a semifilter over a finite type, there exists a minimal quorum (w.r.t. subset).
    A minimal quorum Q is one where no proper subset of Q is also a quorum. -/
lemma exists_minimal_quorum {n : Nat} (L : Semifilter (Fin n)) :
    ∃ Q : Finset (Fin n), (Q : Set (Fin n)) ∈ L.quorums ∧
      ∀ Q' : Finset (Fin n), (Q' : Set (Fin n)) ∈ L.quorums → Q' ⊆ Q → Q' = Q := by
  classical
  -- The quorums form a non-empty set
  obtain ⟨Q₀, hQ₀⟩ := L.nonempty
  -- Consider the set of quorums that are subsets of Q₀
  let quorumsBelow : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powerset.filter (fun Q =>
      (Q : Set (Fin n)) ∈ L.quorums ∧ Q ⊆ Q₀.toFinset)
  -- This set is non-empty (contains Q₀.toFinset)
  have hNonempty : quorumsBelow.Nonempty := by
    refine ⟨Q₀.toFinset, ?_⟩
    simp only [quorumsBelow, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
      true_and]
    exact ⟨by simp [hQ₀], Finset.Subset.refl _⟩
  -- Find the minimal element by cardinality
  have hMin := Finset.exists_min_image quorumsBelow Finset.card hNonempty
  obtain ⟨Qmin, hQminMem, hQminMin⟩ := hMin
  simp only [quorumsBelow, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
    true_and] at hQminMem
  refine ⟨Qmin, hQminMem.1, ?_⟩
  intro Q' hQ'Quorum hQ'Sub
  -- If Q' is a proper subset of Qmin, then Q'.card < Qmin.card
  -- But Q' ⊆ Qmin ⊆ Q₀.toFinset, so Q' is also in quorumsBelow
  by_contra hNe
  have hProper : Q' ⊂ Qmin := by
    refine ⟨hQ'Sub, ?_⟩
    intro hEq
    exact hNe (Finset.Subset.antisymm hQ'Sub hEq)
  have hQ'Card : Q'.card < Qmin.card := Finset.card_lt_card hProper
  have hQ'InBelow : Q' ∈ quorumsBelow := by
    simp only [quorumsBelow, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    exact ⟨hQ'Quorum, Finset.Subset.trans hQ'Sub hQminMem.2⟩
  have hContra := hQminMin Q' hQ'InBelow
  omega

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- For a representative index, there exists a minimal quorum
    that satisfies isMinimalQuorum. -/
lemma exists_minQ_for_representative {b : Bounds S}
    (M : Model S (Fin b.nParticipants))
    (i : b.valIx) (hRep : isRepresentative i = true) :
    ∃ Q : Finset (Fin b.nParticipants), isMinimalQuorum M i Q = true := by
  classical
  let v := b.values.get i
  let L := M.learner v
  obtain ⟨Q, hQuorum, hMinimal⟩ := exists_minimal_quorum L
  refine ⟨Q, ?_⟩
  unfold isMinimalQuorum
  simp only [decide_eq_true_eq]
  exact ⟨by simp [hRep], hQuorum, hMinimal⟩

omit [DecidableEq (Signature.EventType S)]
  [DecidableEq (Signature.AtomicPredType S)] in
/-- A minimal quorum can be represented as a bitmask. -/
lemma minQ_has_bitmask {b : Bounds S}
    (M : Model S (Fin b.nParticipants))
    (i : b.valIx) (Q : Finset (Fin b.nParticipants))
    (_ : isMinimalQuorum M i Q = true) :
    ∃ mask : Fin (Nat.shiftLeft 1 b.nParticipants),
      bitmaskToFinset b.nParticipants mask.val = Q := by
  let mask := finsetToBitmask Q
  have hLt : mask < Nat.shiftLeft 1 b.nParticipants := finsetToBitmask_lt Q
  refine ⟨⟨mask, hLt⟩, finsetToBitmask_inverse Q⟩

end Encoding
