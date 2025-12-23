import ModalDistribution.Logic.SATEncoding.Basic
import ModalDistribution.Logic.SATEncoding.Bounds
import ModalDistribution.Logic.SATEncoding.Var

/-!
# Structural CNF Constraints

This file implements the structural well-formedness constraints for bounded model checking:

1. **cnfAcyclic**: Well-founded time ordering (Mem(H,w) → w.ti < H)
2. **cnfReach**: Reachability from root via happens-before (for AllWorldValid gating)
3. **cnfEdge**: Optimized transitivity encoding using structural time fields
4. **cnfPathFwd**: Path forward closure (adequacy direction)
5. **cnfPathBack**: Path backward constraints with Step witnesses
6. **cnfPathWitness**: Path endpoint witness (connects Path to semantic ≪)
7. **cnfExists**: Canonical existence aggregation using structural fields
8. **cnfExists_back**: Reverse existence (completeness direction)
9. **cnfSeq**: World-level sequentiality constraints
10. **cnfLearners**: Semifilter constraints via minimal quorums with representative selection
11. **cnfLevel_monotone**: Prefix-closed fuel levels
12. **cnfLevel_decrease**: Strict increase along edges (termination fuel)
13. **cnfLevel_max_bound**: Fuel bounded strictly below b.nTimes
14. **cnfMemRequiresFuel**: Membership implies positive fuel
15. **cnfWellFormed**: Conjunction of all structural constraints

## References

- Plan.md sections 3-6 for detailed encoding specifications
- Basic.lean for CNF combinators and constraint helpers
-/

open ModalDistribution

namespace Encoding

variable {S : Signature}
variable [DecidableEq (Signature.EventType S)]
variable [DecidableEq (Signature.AtomicPredType S)]
variable [DecidableEq (Signature.Value S)]

/-! ## Acyclic Constraints

With canonical decoding using structural fields, the acyclic well-foundedness
constraint Mem(H, w) → w.ti.val < H.val must still be enforced via CNF.

The one-hot encoding for Place/EvSel/Time is unnecessary since worlds
use their structural fields directly.
-/

/-- Acyclic constraints: Mem(H, w) → w.ti.val < H.val.

    For every (H, w) pair where w.ti.val >= H.val, add clause ¬Mem(H, w).
    This ensures the decoded prehistory structure is well-founded.

    Complexity: O(T × W) clauses in the worst case. -/
def cnfAcyclic (b : Bounds S) : SAT.CNF (Var b) :=
  let clauses := (Bounds.timesL b).flatMap fun H =>
    (WId.allWorlds b).filterMap fun w =>
      if w.ti.val < H.val then none
      else some [SAT.Lit.neg (Var.Mem H w)]
  SAT.CNF.mk clauses

/-! ## Reachability from Root -/

/-- Reachability constraints for AllWorldValid gating.

    Captures the reflexive-transitive closure of happens-before from root:
    - Base: ReachT(root) = true
    - Horn closure: ReachT(H) ∧ Mem(H, w) → ReachT(w.ti)

    With canonical decoding, w.ti is the structural time field of the world.

    Complexity: O(T × W) clauses
-/
def cnfReach (b : Bounds S) : SAT.CNF (Var b) :=
  -- Base case: root is reachable
  let baseClause := [SAT.Lit.pos (Var.ReachT b.root)]

  -- Horn closure: propagate reachability along edges using structural times
  let hornClauses := (Bounds.timesL b).flatMap fun H =>
    (WId.allWorlds b).map fun w =>
      -- ReachT(H) ∧ Mem(H, w) → ReachT(w.ti)
      -- Clausified: ¬ReachT(H) ∨ ¬Mem(H, w) ∨ ReachT(w.ti)
      [ SAT.Lit.neg (Var.ReachT H),
        SAT.Lit.neg (Var.Mem H w),
        SAT.Lit.pos (Var.ReachT w.ti) ]

  SAT.CNF.mk (baseClause :: hornClauses)

/-! ## Optimized Transitivity Encoding -/

/-- Edge-optimized transitivity encoding using structural time fields.

    Two-step encoding using canonical decoding (eliminates Zedge auxiliary variables):

    Step 1 - Edge aggregation using structural times:
      Edge(H, H') ↔ ⋁_{w | w.ti = H'} Mem(H, w)
      Uses bi-directional clauses (O(W) clauses per (H, H') pair)

    Step 2 - Transitivity via edges:
      Edge(H, H') ∧ Mem(H', w) → Mem(H, w)
      One clause per (H, H', w) triple

    Complexity: O(T² × W) + O(T² × W) = O(P · (E+1) · T²)
-/
def cnfEdge (b : Bounds S) : SAT.CNF (Var b) :=
  -- Step 1: Edge aggregation using structural times
  let edgeClauses := (Bounds.timesL b).flatMap fun H =>
    (Bounds.timesL b).flatMap fun H' =>
      let witnesses := (WId.allWorlds b).filter (fun w => w.ti == H')
                       |>.map (Var.Mem H ·)
      -- Forward: Edge(H, H') → ⋁_{w | w.ti = H'} Mem(H, w)
      let fwd := SAT.Lit.neg (Var.Edge H H') :: witnesses.map SAT.Lit.pos
      -- Backward: each witness → Edge(H, H')
      let bwd := witnesses.map fun m => [SAT.Lit.neg m, SAT.Lit.pos (Var.Edge H H')]
      [fwd] ++ bwd

  -- Step 2: Transitivity using Edge
  let transitiveClauses := (Bounds.timesL b).flatMap fun H =>
    (Bounds.timesL b).flatMap fun H' =>
      (WId.allWorlds b).map fun w =>
        -- Edge(H, H') ∧ Mem(H', w) → Mem(H, w)
        -- Clausified: ¬Edge(H, H') ∨ ¬Mem(H', w) ∨ Mem(H, w)
        [ SAT.Lit.neg (Var.Edge H H'),
          SAT.Lit.neg (Var.Mem H' w),
          SAT.Lit.pos (Var.Mem H w) ]

  -- Combine both steps
  SAT.CNF.mk (edgeClauses ++ transitiveClauses)

/-! ## Sequentiality Encoding -/

/-- Canonical existence aggregation using structural fields.

    Forward direction: Mem(H,w) → Exists(H, w.p, w.ti)
    With structural fields, each world w directly specifies its participant (w.p)
    and time (w.ti), eliminating the need for Place/Time SAT variables.

    Complexity: O(T × W) clauses -/
def cnfExists (b : Bounds S) : SAT.CNF (Var b) :=
  let clauses :=
    (Bounds.timesL b).flatMap fun H =>
      (WId.allWorlds b).map fun w =>
        -- Mem(H, w) → Exists(H, w.p, w.ti)
        [ SAT.Lit.neg (Var.Mem H w),
          SAT.Lit.pos (Var.Exists H w.p w.ti) ]
  SAT.CNF.mk clauses

/-- Reverse Existence: Exists(H,p,t) → ∃ w, Mem(H,w) ∧ w.p=p ∧ w.ti=t.
    Ensures that if Exists is true, there is an actual witnessing world.

    Complexity: O(T × P × T) clauses (one per H,p,t triple). -/
def cnfExists_back (b : Bounds S) : SAT.CNF (Var b) :=
  let clauses :=
    (Bounds.timesL b).flatMap fun H =>
    (Bounds.partsL b).flatMap fun p =>
    (Bounds.timesL b).map fun t =>
      let ws :=
        (WId.allWorlds b).filter (fun w => (w.p = p) ∧ (w.ti = t))
      match ws with
      | [] =>
          -- domain is empty: Exists(H,p,t) must be false
          [SAT.Lit.neg (Var.Exists H p t)]
      | _  =>
          let memLits := ws.map (fun w => SAT.Lit.pos (Var.Mem H w))
          SAT.Lit.neg (Var.Exists H p t) :: memLits
  SAT.CNF.mk clauses

/-- World-level sequentiality at (H, p) using membership-based accessibility.

    Encodes sequentiality using actual accessibility witnesses:
      CmpWorld(w₁,w₂) := Acc(w₁,w₂) ∨ Acc(w₂,w₁) ∨ WorldEq(w₁,w₂)

    Where:
      Acc(w₁,w₂) = ∃ w₃, Mem(w₂.ti, w₃) ∧ w₃.p = w₁.p ∧ w₃.ei = w₁.ei ∧ PreEq(w₃.ti, w₁.ti)
      WorldEq(w₁,w₂) = w₁.ei = w₂.ei ∧ PreEq(w₁.ti, w₂.ti)  (place equality is given)

    The accessibility check `Acc(w₁,w₂)` captures semantic `w₁ ≪ w₂`:
      w₁ is accessible from w₂ iff there exists a world in w₂'s prehistory
      that is worldEq to w₁ (same place, same event, histEq times).

    We use auxiliary Acc(w₁,w₂,w₃) variables to witness individual accessibility:
      Acc(w₁,w₂,w₃) ↔ Mem(w₂.ti, w₃) ∧ PreEq(w₃.ti, w₁.ti)
    where w₃ ranges over worlds with w₃.p = w₁.p and w₃.ei = w₁.ei.

    Uses auxiliary Incomp(H,p,w₁,w₂) variables to witness incomparable pairs:
      Incomp(H,p,w₁,w₂) ↔ Mem(H,w₁) ∧ Mem(H,w₂) ∧ ¬(⋁_{w₃} Acc(w₁,w₂,w₃)) ∧ ...

    Then Seq is the conjunction of no incomparable pairs:
      Seq(H,p) ↔ ∧_{w₁,w₂} ¬Incomp(H,p,w₁,w₂)

    Complexity: O(T × P × W³) clauses (cubic due to accessibility witnesses). -/
def cnfSeq (b : Bounds S) : SAT.CNF (Var b) :=
  -- Generate all (H, p, w₁, w₂) tuples where w₁.p = w₂.p = p
  let allPairs :=
    (Bounds.timesL b).flatMap fun H =>
      (Bounds.partsL b).flatMap fun p =>
        let ws := (WId.allWorlds b).filter (fun w => w.p = p)
        ws.flatMap fun w₁ =>
          ws.map fun w₂ => (H, p, w₁, w₂)

  -- For accessibility Acc(w₁,w₂), we need witnesses w₃ with:
  --   w₃.p = w₁.p ∧ w₃.ei = w₁.ei (so decoded w₃ has same place/event as w₁)
  -- The witness must satisfy: Mem(w₂.ti, w₃) ∧ PreEq(w₃.ti, w₁.ti)
  let accWitnesses (w₁ : WId b) : List (WId b) :=
    (WId.allWorlds b).filter fun w₃ => w₃.p = w₁.p && w₃.ei = w₁.ei

  -- Acc variable definition clauses
  -- Acc(w₁,w₂,w₃) ↔ Mem(w₂.ti, w₃) ∧ PreEq(w₃.ti, w₁.ti)
  -- Forward: Acc → Mem ∧ PreEq (two clauses)
  -- Backward: Mem ∧ PreEq → Acc (one clause)
  let accDef := allPairs.flatMap fun ⟨_, _, w₁, w₂⟩ =>
    (accWitnesses w₁).flatMap fun w₃ =>
      [ -- Acc(w₁,w₂,w₃) → Mem(w₂.ti, w₃)
        [SAT.Lit.neg (Var.Acc w₁ w₂ w₃), SAT.Lit.pos (Var.Mem w₂.ti w₃)]
      , -- Acc(w₁,w₂,w₃) → PreEq(w₃.ti, w₁.ti)
        [SAT.Lit.neg (Var.Acc w₁ w₂ w₃), SAT.Lit.pos (Var.PreEq w₃.ti w₁.ti)]
      , -- Mem(w₂.ti, w₃) ∧ PreEq(w₃.ti, w₁.ti) → Acc(w₁,w₂,w₃)
        [SAT.Lit.neg (Var.Mem w₂.ti w₃), SAT.Lit.neg (Var.PreEq w₃.ti w₁.ti),
         SAT.Lit.pos (Var.Acc w₁ w₂ w₃)] ]

  -- Incomp definition clauses (forward: Incomp → each conjunct)
  -- Incomp(H,p,w₁,w₂) → Mem(H,w₁)
  -- Incomp(H,p,w₁,w₂) → Mem(H,w₂)
  -- Incomp(H,p,w₁,w₂) → ¬Acc(w₁,w₂,w₃) for each witness w₃
  -- Incomp(H,p,w₁,w₂) → ¬Acc(w₂,w₁,w₃) for each witness w₃
  -- Incomp(H,p,w₁,w₂) → ¬PreEq(w₁.ti,w₂.ti)  [only when w₁.ei = w₂.ei, for WorldEq]
  let incompFwd := allPairs.flatMap fun ⟨H, p, w₁, w₂⟩ =>
    let memClauses :=
      [ [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.pos (Var.Mem H w₁)]
      , [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.pos (Var.Mem H w₂)] ]
    -- Incomp → ¬Acc(w₁,w₂,w₃) for each witness w₃
    let acc12Clauses := (accWitnesses w₁).map fun w₃ =>
      [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.neg (Var.Acc w₁ w₂ w₃)]
    -- Incomp → ¬Acc(w₂,w₁,w₃) for each witness w₃
    let acc21Clauses := (accWitnesses w₂).map fun w₃ =>
      [SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.neg (Var.Acc w₂ w₁ w₃)]
    -- For WorldEq: only when events match
    let worldEqClauses :=
      if w₁.ei = w₂.ei then
        [[SAT.Lit.neg (Var.Incomp H p w₁ w₂), SAT.Lit.neg (Var.PreEq w₁.ti w₂.ti)]]
      else
        []
    memClauses ++ acc12Clauses ++ acc21Clauses ++ worldEqClauses

  -- Incomp definition clauses (backward: all conjuncts → Incomp)
  -- Mem(H,w₁) ∧ Mem(H,w₂) ∧ (∧_{w₃} ¬Acc(w₁,w₂,w₃)) ∧ (∧_{w₃} ¬Acc(w₂,w₁,w₃)) ∧ ¬WorldEq → Incomp
  -- Clausified: ¬Mem ∨ ¬Mem ∨ (⋁_{w₃} Acc(w₁,w₂,w₃)) ∨ (⋁_{w₃} Acc(w₂,w₁,w₃)) ∨ WorldEq ∨ Incomp
  let incompBwd := allPairs.map fun ⟨H, p, w₁, w₂⟩ =>
    let baseLits :=
      [ SAT.Lit.neg (Var.Mem H w₁)
      , SAT.Lit.neg (Var.Mem H w₂)
      , SAT.Lit.pos (Var.Incomp H p w₁ w₂) ]
    -- Acc escape: ⋁_{w₃} Acc(w₁,w₂,w₃)
    let acc12Lits := (accWitnesses w₁).map fun w₃ =>
      SAT.Lit.pos (Var.Acc w₁ w₂ w₃)
    let acc21Lits := (accWitnesses w₂).map fun w₃ =>
      SAT.Lit.pos (Var.Acc w₂ w₁ w₃)
    -- WorldEq escape: only when events match
    let worldEqLits :=
      if w₁.ei = w₂.ei then
        [SAT.Lit.pos (Var.PreEq w₁.ti w₂.ti)]
      else
        []
    baseLits ++ acc12Lits ++ acc21Lits ++ worldEqLits

  -- Seq → ¬Incomp for all pairs
  -- Clausified: ¬Seq(H,p) ∨ ¬Incomp(H,p,w₁,w₂)
  let seqToNoIncomp := allPairs.map fun ⟨H, p, w₁, w₂⟩ =>
    [SAT.Lit.neg (Var.Seq H p), SAT.Lit.neg (Var.Incomp H p w₁ w₂)]

  -- All ¬Incomp → Seq (one clause per (H,p) with all Incomp vars as positive)
  -- Clausified: Seq(H,p) ∨ Incomp(H,p,w₁,w₂) ∨ Incomp(H,p,w₃,w₄) ∨ ...
  let noIncompToSeq :=
    (Bounds.timesL b).flatMap fun H =>
      (Bounds.partsL b).map fun p =>
        let ws := (WId.allWorlds b).filter (fun w => w.p = p)
        let incompLits := ws.flatMap fun w₁ =>
          ws.map fun w₂ => SAT.Lit.pos (Var.Incomp H p w₁ w₂)
        SAT.Lit.pos (Var.Seq H p) :: incompLits

  SAT.CNF.mk (accDef ++ incompFwd ++ incompBwd ++ seqToNoIncomp ++ noIncompToSeq)

/-! ## Semifilter Constraints -/

/-! ### Learner Encoding Strategy

    Learner/semifilter encoding via minimal quorums with representative selection.

    Uses a representative index selection mechanism to handle duplicate values:

    1. Representative selection: One-hot Rep(i) per value equivalence class
       For each v in classValues(b): exo {Rep(i) | i ∈ valueIndices(b, v)}

    2. Gating: MinQ variables are only active at the chosen representative
       For all i, Q: MinQ(i,Q) → Rep(i)
       Clausified: ¬MinQ(i,Q) ∨ Rep(i)

    3. Conditional ALO: The chosen representative must have a minimal quorum
       For all i: Rep(i) → (∨Q MinQ(i,Q))
       Clausified: ¬Rep(i) ∨ MinQ(i,Q1) ∨ MinQ(i,Q2) ∨ ...

    4. Minimality (anti-chain): No strict subsets within an index
       For Q₂ ⊂ Q₁: ¬MinQ(i, Q₁) ∨ ¬MinQ(i, Q₂)

    5. Pairwise intersection: Disjoint pairs forbidden within an index
       For Finset.disjoint Q₁ Q₂: ¬MinQ(i, Q₁) ∨ ¬MinQ(i, Q₂)

    6. No empty quorums: Empty set cannot be a minimal quorum
       ¬MinQ(i, ∅)

    Decoding reconstructs semifilter from the chosen representative only:
      L_v.quorums := {O | ∃ Q, MinQ(pickRep(σ,v), Q) = true ∧ Q ⊆ O}
-/
/-- (a) One-hot representative selection per value class -/
def repExoClauses (b : Bounds S) : List (SAT.Clause (Var b)) :=
  (classValues b).flatMap fun v =>
    let is := valueIndices b v
    (SAT.exo (is.map Var.Rep)).clauses

/-- (b) Gating: MinQ(i,Q) ⇒ Rep(i) -/
def gatingClauses (b : Bounds S) : List (SAT.Clause (Var b)) :=
  (Bounds.valIxL b).flatMap fun i =>
    (Var.allMinQ b i).map fun v =>
      match v with
      | Var.MinQ _ _ => [SAT.Lit.neg v, SAT.Lit.pos (Var.Rep i)]
      | _            => []  -- Should not happen (allMinQ only builds MinQ)

/-- (b0) Pin each value's representative to its canonical index. -/
def repUnitClauses (b : Bounds S) : List (SAT.Clause (Var b)) :=
  (classValues b).map fun v =>
    [SAT.Lit.pos (Var.Rep (b.findValueIndex v))]

/-- (c) Conditional ALO: Rep(i) ⇒ (∨Q MinQ(i,Q)) -/
def condAloClauses (b : Bounds S) : List (SAT.Clause (Var b)) :=
  (Bounds.valIxL b).map fun i =>
    let quorumVars := Var.allMinQ b i
    SAT.Lit.neg (Var.Rep i) :: quorumVars.map SAT.Lit.pos

/-- (d) Within-index constraints: minimality, pairwise intersection, no-empty -/
def withinIndexClauses (b : Bounds S) : List (SAT.Clause (Var b)) :=
  (Bounds.valIxL b).flatMap fun i =>
    let quorumVars := Var.allMinQ b i

    -- Minimality: forbid strict subset pairs (Q2 ⊂ Q1)
    let minimalityClauses := quorumVars.flatMap fun q1 =>
      quorumVars.filterMap fun q2 =>
        match q1, q2 with
        | Var.MinQ _ Q1, Var.MinQ _ Q2 =>
            if Q2 ⊂ Q1 ∧ Q2 ≠ Q1 then
              some [SAT.Lit.neg q1, SAT.Lit.neg q2]
            else
              none
        | _, _ => none

    -- Pairwise intersection: forbid disjoint pairs
    let intersectionClauses := quorumVars.flatMap fun q1 =>
      quorumVars.filterMap fun q2 =>
        match q1, q2 with
        | Var.MinQ _ Q1, Var.MinQ _ Q2 =>
            if (Q1 ∩ Q2).card = 0 ∧ Q1 ≠ Q2 then
              some [SAT.Lit.neg q1, SAT.Lit.neg q2]
            else
              none
        | _, _ => none

    -- No empty quorums: forbid MinQ(i, ∅)
    let noEmptyClauses := quorumVars.filterMap fun q =>
      match q with
      | Var.MinQ _ Q =>
          if Q.card = 0 then
            some [SAT.Lit.neg q]
          else
            none
      | _ => none

    minimalityClauses ++ intersectionClauses ++ noEmptyClauses

/-- CNF encoding of learner constraints -/
def cnfLearners (b : Bounds S) : SAT.CNF (Var b) :=
  SAT.CNF.mk
    (repUnitClauses b ++ repExoClauses b ++ gatingClauses b
      ++ condAloClauses b ++ withinIndexClauses b)

/-! ## Combined Well-Formedness -/

/-! ## Fuel Level Constraints

Per-time fuel levels are encoded using prefix-closed (monotone) levels:
- Level(ti, 0) is always true (base level)
- Level(ti, j+1) → Level(ti, j) (monotone prefix)
- Mem(H, w) ∧ Level(w.ti, j+1) → Level(H, j) (decrease along edges)

The decoder uses the max true level, ensuring fuel alignment without uniqueness constraints.
-/

/-- Monotone prefix constraints: Level(ti, j+1) → Level(ti, j). -/
def cnfLevel_monotone (b : Bounds S) : SAT.CNF (Var b) :=
  let clauses := (Bounds.timesL b).flatMap fun ti =>
    -- Base: Level(ti, 0) = true
    let baseClause := [SAT.Lit.pos (Var.Level ti ⟨0, Nat.zero_lt_succ _⟩)]
    -- Monotone: for each j < nTimes, Level(ti, j+1) → Level(ti, j)
    let monotoneClauses := (List.range b.nTimes).filterMap fun j =>
      if h : j < b.nTimes ∧ j.succ < b.nTimes.succ then
        some [ SAT.Lit.neg (Var.Level ti ⟨j.succ, h.2⟩)
             , SAT.Lit.pos (Var.Level ti ⟨j, Nat.lt_succ_of_lt h.1⟩) ]
      else none
    baseClause :: monotoneClauses
  SAT.CNF.mk clauses

/-- Strict increase constraint: Mem(H,w) ∧ Level(w.ti, j) → Level(H, j+1).

    This ensures that if a world w is in prehistory H, then H has strictly more fuel
    than w.ti. This is necessary for termination of the fuel-based decoder.

    The constraint says: if the child time w.ti has fuel level j, then the parent
    prehistory H must have fuel level j+1. Since fuel is the maximum level, this
    ensures parent_fuel > child_fuel for all children in the prehistory. -/
def cnfLevel_decrease (b : Bounds S) : SAT.CNF (Var b) :=
  let clauses := (Bounds.timesL b).flatMap fun H =>
    (WId.allWorlds b).flatMap fun w =>
      (List.range b.nTimes).filterMap fun j =>
        if h : j < b.nTimes ∧ j.succ < b.nTimes.succ then
          some [ SAT.Lit.neg (Var.Mem H w)
               , SAT.Lit.neg (Var.Level w.ti ⟨j, Nat.lt_succ_of_lt h.1⟩)
               , SAT.Lit.pos (Var.Level H ⟨j.succ, h.2⟩) ]
        else none
  SAT.CNF.mk clauses

/-- Maximum fuel bound: Level(ti, b.nTimes) = false for all times.

    This constraint ensures that fuel values are strictly bounded by b.nTimes,
    never reaching the maximum index. This is necessary for the termination proof:
    when the increase constraint gives us Level(H, j+1) from Level(w.ti, j),
    we need room for j+1 to be a valid index with strict inequality.

    Without this constraint, assignments could set all Level variables to true,
    giving fuelOf(ti) = b.nTimes for all times, which would break the strict
    decrease property needed for decoder termination. -/
def cnfLevel_max_bound (b : Bounds S) : SAT.CNF (Var b) :=
  let clauses := (Bounds.timesL b).map fun ti =>
    [SAT.Lit.neg (Var.Level ti ⟨b.nTimes, Nat.lt_succ_self _⟩)]
  SAT.CNF.mk clauses

/-- Membership requires positive fuel: Mem(H, w) → Level(H, 1).

    This constraint ensures that if any world w is a member of prehistory H,
    then H has at least fuel level 1. This is necessary for decoder correspondence:
    decodePre only decodes members when fuel > 0, so Mem bits must imply positive fuel.

    Without this constraint, SAT could produce assignments with Mem(H, w) = true
    but fuelOf H = 0, causing decodePre H to return empty while Mem claims non-empty,
    breaking the fundamental invariant: Mem(H, w) = true ↔ (w.p, decodeMaybeEvent
    w.ei, decodePre w.ti) ∈ decodePre H.

    Note: This does NOT constrain w.ti to have positive fuel - leaf worlds with
    empty prehistories (fuel = 0) can still be members of parent prehistories. -/
def cnfMemRequiresFuel (b : Bounds S) : SAT.CNF (Var b) :=
  let clauses := (Bounds.timesL b).flatMap fun H =>
    (WId.allWorlds b).map fun w =>
      [SAT.Lit.neg (Var.Mem H w), SAT.Lit.pos (Var.Level H ⟨1, Nat.succ_lt_succ b.posTimes⟩)]
  SAT.CNF.mk clauses

/-- Combined structural well-formedness CNF.

    Conjunction of all structural constraints:
    - cnfAcyclic: well-founded time ordering (Mem(H,w) → w.ti < H)
    - cnfReach: reachability from root (using structural times)
    - cnfEdge: optimized transitivity encoding (using structural times)
    - cnfLearners: semifilter constraints via minimal quorums
    - cnfLevel_monotone: prefix-closed fuel levels
    - cnfLevel_decrease: acyclic decrease along edges
    - cnfLevel_max_bound: fuel bounded strictly below b.nTimes
    - cnfMemRequiresFuel: membership implies positive fuel
    - cnfExists: canonical existence aggregators (using structural fields)
    - cnfPathFwd: transitive happens-before closure (forward Horn rules)
    - cnfPathBack: path backward constraints with Step witnesses
    - cnfSeq: world-level sequentiality with event-aware comparability

    Note: With canonical decoding, one-hot encoding (Place/EvSel/Time) is
    unnecessary. Predicate coherence clauses are added locally during
    formula encoding. See FormulaEncoding.lean.
-/
def cnfWellFormed (b : Bounds S) : SAT.CNF (Var b) :=
  SAT.CNF.band
  [ cnfAcyclic b
  , cnfReach b
  , cnfEdge b
  , cnfLearners b
  , cnfLevel_monotone b
  , cnfLevel_decrease b
  , cnfLevel_max_bound b
  , cnfMemRequiresFuel b
  , cnfExists b
  , cnfExists_back b
  , cnfSeq b
  ]

omit [DecidableEq S.EventType] [DecidableEq S.AtomicPredType] in
/-- Extraction lemma: cnfWellFormed satisfaction iff all components satisfied.
    This avoids unfolding the entire structure during elaboration. -/
theorem cnfWellFormed_eval_iff (b : Bounds S) (σ : SAT.Assignment (Var b)) :
    (cnfWellFormed b).eval σ = true ↔
      (cnfAcyclic b).eval σ = true ∧
      (cnfReach b).eval σ = true ∧
      (cnfEdge b).eval σ = true ∧
      (cnfLearners b).eval σ = true ∧
      (cnfLevel_monotone b).eval σ = true ∧
      (cnfLevel_decrease b).eval σ = true ∧
      (cnfLevel_max_bound b).eval σ = true ∧
      (cnfMemRequiresFuel b).eval σ = true ∧
      (cnfExists b).eval σ = true ∧
      (cnfExists_back b).eval σ = true ∧
      (cnfSeq b).eval σ = true := by
  unfold cnfWellFormed
  rw [SAT.CNF.eval_band_true]
  simp only [List.mem_cons, forall_eq_or_imp]
  tauto

-- Make cnfWellFormed opaque to prevent further unfolding in proofs
attribute [irreducible] cnfWellFormed

/-- Well-formedness predicate: CNF is satisfied. -/
def WF (b : Bounds S) (σ : SAT.Assignment (Var b)) : Prop :=
  (cnfWellFormed b).eval σ = true

end Encoding
