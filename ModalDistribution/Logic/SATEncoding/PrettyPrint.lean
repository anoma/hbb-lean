import ModalDistribution.Logic.SATEncoding.Decoder

/-!
# Model Pretty-Printing

This file provides functions to format model data for console output.
Uses index-based naming (P0, P1, E0, V0) for generality.

## Main Definitions

- `formatMaybeEvent`: Format † or event with arguments
- `formatWorld`: Format a world triple
- `formatPreHistory`: Format prehistory as indented tree
- `formatLearnerData`: Format minimal quorum sets
- `formatModelData`: Format complete extracted model
-/

open ModalDistribution

namespace Encoding

variable {S : Signature}

/-! ## MaybeEvent Formatting -/

/-- Format a MaybeEvent. Uses † for none, "E<sym>(<args>)" for events. -/
def formatMaybeEvent (e : MaybeEvent (Signature.EventType S)) : String :=
  match e with
  | .none => "†"
  | .some evt =>
      let argsStr := evt.args.map (fun _ => "v") |> String.intercalate ", "
      s!"E({argsStr})"

/-- Format a MaybeEvent with more detail when Repr is available. -/
def formatMaybeEventRepr [Repr S.EventSymb] [Repr S.Value]
    (e : MaybeEvent (Signature.EventType S)) : String :=
  match e with
  | .none => "†"
  | .some evt =>
      let symStr := reprStr evt.sym
      let argsStr := evt.args.map reprStr |> String.intercalate ", "
      s!"{symStr}({argsStr})"

/-! ## World Formatting -/

/-- Format a world as "W(P<p>, <event>)". -/
def formatWorldSimple {P : Type*} [ToString P]
    (w : World P (Signature.EventType S)) : String :=
  s!"W(P{w.1}, {formatMaybeEvent w.2.1})"

/-! ## PreHistory Formatting -/

/-- Count worlds in a prehistory (for summary). -/
partial def countWorlds {P Event : Type*} : PreHistory P Event → Nat
  | .mk [] => 0
  | .mk (w :: ws) => 1 + countWorlds w.2.2 + countWorlds (.mk ws)

/-- Format a prehistory as an indented tree structure.
    Uses fuel to prevent infinite loops on malformed data. -/
partial def formatPreHistoryAux {n : Nat}
    (h : PreHistory (Fin n) (Signature.EventType S))
    (indent : Nat) (fuel : Nat) : String :=
  if fuel = 0 then
    String.replicate indent ' ' ++ "... (truncated)\n"
  else
    match h with
    | .mk [] => String.replicate indent ' ' ++ "(empty)\n"
    | .mk worlds =>
        worlds.foldl (fun acc w =>
          let pStr := s!"P{w.1.val}"
          let eStr := formatMaybeEvent w.2.1
          let worldLine := String.replicate indent ' ' ++ s!"- ({pStr}, {eStr})\n"
          let subTree := formatPreHistoryAux w.2.2 (indent + 4) (fuel - 1)
          acc ++ worldLine ++ subTree
        ) ""

/-- Format a prehistory with default fuel. -/
def formatPreHistory {n : Nat}
    (h : PreHistory (Fin n) (Signature.EventType S)) : String :=
  formatPreHistoryAux h 2 100

/-! ## Quorum/Learner Formatting -/

/-- Format a Finset of participants as {0, 1, 2}.
    Uses range iteration since Finset.toList is noncomputable. -/
def formatQuorum {n : Nat} (Q : Finset (Fin n)) : String :=
  -- Iterate over all possible participants and collect those in Q
  let indices := (List.finRange n).filter (· ∈ Q) |>.map (·.val)
  s!"\{{String.intercalate ", " (indices.map toString)}}"

/-- Format learner data showing minimal quorums per value index. -/
def formatLearnerData (b : Bounds S) (ld : LearnerData b) : String :=
  let lines := (List.finRange b.nVals).filterMap fun vIdx =>
    let quorums := ld.minimalQuorumsIx vIdx
    if quorums.isEmpty then none
    else
      let qStrs := quorums.map formatQuorum |> String.intercalate ", "
      some s!"  V{vIdx.val}: [{qStrs}]"
  if lines.isEmpty then "  (no minimal quorums)"
  else String.intercalate "\n" lines

/-! ## Full Model Formatting -/

/-- Format complete ModelData for console output. -/
def formatModelData (b : Bounds S) (md : ModelData S (Fin b.nParticipants) b) : String :=
  let header := "=== Found Model ===\n"
  let params := s!"Participants: {b.nParticipants}\n" ++
                s!"Time steps: {b.nTimes}\n" ++
                s!"Events: {b.nEvents}\n" ++
                s!"Values: {b.nVals}\n"
  let worldCount := countWorlds md.Hroot
  let preSection := s!"\n--- Prehistory ({worldCount} worlds) ---\n" ++
                    formatPreHistory md.Hroot
  let learnerSection := "\n--- Learner Quorums (minimal sets) ---\n" ++
                        formatLearnerData b md.learnData
  header ++ params ++ preSection ++ learnerSection

/-! ## Statistics -/

/-- Get a summary line for model data. -/
def modelSummary (b : Bounds S) (md : ModelData S (Fin b.nParticipants) b) : String :=
  let worldCount := countWorlds md.Hroot
  let quorumCount := (List.finRange b.nVals).foldl
    (fun acc vIdx => acc + (md.learnData.minimalQuorumsIx vIdx).length) 0
  s!"Model: {b.nParticipants} participants, {worldCount} worlds, {quorumCount} minimal quorums"

end Encoding
