import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyHBB1.Uniqueness
import ModalDistribution.Examples.ThyHBB3.Axioms
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.History
import ModalDistribution.Core.Prehistory
import ModalDistribution.Core.Semifilter
/-!
# ThyHBB3 Helper Lemmas

This file records the auxiliary lemmas used throughout Section~8 of the paper.
Each statement mirrors the corresponding labelled lemma in the text: the
interaction of the `3twined` axiom with sequential quorums, the extraction of
quorum witnesses from votes, and the behaviour of the correlation relation
$\mnta$.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB3

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open Set
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}
variable {correlationSymb : Signature.PredSymb S}

/-- Paper: Lemma 8.4.1. `3twined` combines three guarded box facts
into a joint diamond witness. -/
theorem threeTwined_boxes_intersect
    {l₁ l₂ l₃ : Signature.Value S}
    {φ₁ φ₂ φ₃ : Formula S} :
    ⊨[M]
      ((♢ᶠ[[l₁, l₂, l₃]] ⊤ᶠ) ⇒ᶠ
        ((□ᶠ[[l₁]] φ₁) ∧ᶠ (□ᶠ[[l₂]] φ₂) ∧ᶠ (□ᶠ[[l₃]] φ₃) ⇒ᶠ
          ♢ᶠ[] (φ₁ ∧ᶠ φ₂ ∧ᶠ φ₃))) := by
  classical
  intro p
  set w : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  -- Unpack the implication hypotheses step by step.
  refine
    Sat.imp_intro (M := M) (w := w)
      (φ := ♢ᶠ[[l₁, l₂, l₃]] ⊤ᶠ)
      (ψ := (((□ᶠ[[l₁]] φ₁) ∧ᶠ (□ᶠ[[l₂]] φ₂)) ∧ᶠ (□ᶠ[[l₃]] φ₃)) ⇒ᶠ
        ♢ᶠ[] (φ₁ ∧ᶠ φ₂ ∧ᶠ φ₃)) ?_
  intro hDiamond
  refine
    Sat.imp_intro (M := M) (w := w)
      (φ := ((□ᶠ[[l₁]] φ₁) ∧ᶠ (□ᶠ[[l₂]] φ₂)) ∧ᶠ (□ᶠ[[l₃]] φ₃))
      (ψ := ♢ᶠ[] (φ₁ ∧ᶠ φ₂ ∧ᶠ φ₃)) ?_
  intro hBoxes
  -- Separate the three `□` guards.
  have hPairAnd :=
    (Sat.and (M := M) (w := w)
      (φ := (□ᶠ[[l₁]] φ₁) ∧ᶠ (□ᶠ[[l₂]] φ₂))
      (ψ := □ᶠ[[l₃]] φ₃)).1 hBoxes
  have hPair₁₂ := hPairAnd.1
  have hBox₃ : ⟪w⟫ ⊨[M]□ᶠ[[l₃]] φ₃ := hPairAnd.2
  have hPair₁₂' :=
    (Sat.and (M := M) (w := w)
      (φ := □ᶠ[[l₁]] φ₁) (ψ := □ᶠ[[l₂]] φ₂)).1 hPair₁₂
  have hBox₁ : ⟪w⟫ ⊨[M]□ᶠ[[l₁]] φ₁ := hPair₁₂'.1
  have hBox₂ : ⟪w⟫ ⊨[M]□ᶠ[[l₂]] φ₂ := hPair₁₂'.2
  -- For each learner, pick a quorum whose members satisfy the guard. (`sat_box_singleton_exists`).
  obtain ⟨O₁, hO₁, hAll₁⟩ :=
    (sat_box_singleton_exists (M := M) (w := w)
      (l := l₁) (φ := φ₁)).1 hBox₁
  obtain ⟨O₂, hO₂, hAll₂⟩ :=
    (sat_box_singleton_exists (M := M) (w := w)
      (l := l₂) (φ := φ₂)).1 hBox₂
  obtain ⟨O₃, hO₃, hAll₃⟩ :=
    (sat_box_singleton_exists (M := M) (w := w)
      (l := l₃) (φ := φ₃)).1 hBox₃
  -- Triple intersection witness supplied by `sat_diamond_three_intersection`
  -- (captures `♢ᶠ[[l₁,l₂,l₃]] ⊤ᶠ`).
  obtain ⟨p₀, hp₁, hp₂, hp₃⟩ :=
    sat_diamond_three_intersection (M := M) (w := w)
      (hDiamond := hDiamond) (hO₁ := hO₁) (hO₂ := hO₂) (hO₃ := hO₃)
  -- Each guard holds at the common participant.
  have hφ₁ : ⟪⟨p₀, †, w.time⟩⟫ ⊨[M] φ₁ := hAll₁ _ hp₁
  have hφ₂ : ⟪⟨p₀, †, w.time⟩⟫ ⊨[M] φ₂ := hAll₂ _ hp₂
  have hφ₃ : ⟪⟨p₀, †, w.time⟩⟫ ⊨[M] φ₃ := hAll₃ _ hp₃
  -- Build the combined conjunction `(φ₁ ∧ φ₂ ∧ φ₃)` at the witness.
  have hφ₁₂ :
      ⟪⟨p₀, †, w.time⟩⟫ ⊨[M] φ₁ ∧ᶠ φ₂ :=
    Sat.and_intro (M := M) (w := ⟨p₀, †, w.time⟩)
      (φ := φ₁) (ψ := φ₂) hφ₁ hφ₂
  have hφAll :
      ⟪⟨p₀, †, w.time⟩⟫ ⊨[M] (φ₁ ∧ᶠ φ₂) ∧ᶠ φ₃ :=
    Sat.and_intro (M := M) (w := ⟨p₀, †, w.time⟩)
      (φ := φ₁ ∧ᶠ φ₂) (ψ := φ₃) hφ₁₂ hφ₃
  -- Witness the empty learner diamond via `sat_diamondEmpty_of_local`.
  have hWitness : ∃ q, ⟪⟨q, †, w.time⟩⟫ ⊨[M] φ₁ ∧ᶠ φ₂ ∧ᶠ φ₃ :=
    ⟨p₀, by simpa using hφAll⟩
  exact
    sat_diamondEmpty_of_local (M := M) (w := w)
      (φ := φ₁ ∧ᶠ φ₂ ∧ᶠ φ₃) hWitness

/-- The `threeTwined` axiom forces triple learner quorums to intersect. -/
theorem threeTwined_hasQuorumNonempty
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    (hHistory : ∃ t : World P (Signature.EventType S), t ∈ M.history.val)
    {l₁ l₂ l₃ : Signature.Value S} :
    hasQuorumNonempty (M := M) [l₁, l₂, l₃] := by
  classical
  obtain ⟨t, ht⟩ := hHistory
  exact
    (sat_diamond_top_iff_hasQuorumNonempty (M := M)
        (w := t) (ls := [l₁, l₂, l₃])).1
      (threeTwined_elim (M := M)
        (theory_threeTwined (M := M) hTheory)
        (M.time_le_of_mem ht))

/-- Inductive step for `vote_implies_echo_quorum_local`.  Assuming the result
for all worlds strictly before `w`, we obtain the required echo quorum for
`w`. -/
theorem vote_implies_echo_quorum_step
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {w : World P (Signature.EventType S)}
    (hMem : w ∈ M.history.val)
    (IH : ∀ {w' : World P (Signature.EventType S)},
        w'.time ≺− w.time →
        w' ∈ M.history.val →
        ∀ {learner value : Signature.Value S},
          (⟪w'⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩) →
            ∃ source : Signature.Value S,
              ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩))
    {learner value : Signature.Value S}
    (hVote : ⟪w⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩) :
    ∃ source : Signature.Value S,
      ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  -- Instantiate `(Vote?)` at `w`.
  have hDisj :=
    voteBackward_elim (M := M)
      (theory_voteBackward (M := M) hTheory)
      (M.time_le_of_mem hMem)
      (learner := learner) (value := value) hVote
  let φLeft := □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)
  let ψRight :=
    ∃ᶠ fun correlated =>
      ofPredicate ⟨correlationSymb, [correlated, learner]⟩ ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩)
  -- Record that the past of `w` embeds into the global history.
  have hBefore_history :
      w.time ≺− M.history.val :=
    History.happensBefore_of_mem
      (P := P) (Event := Signature.EventType S) hMem
  have hSubset_history : w.time ⊆ M.history.val :=
    History.subset_of_happensBefore (H := M.history) hBefore_history
  -- Split the disjunction between a local echo quorum and a correlated vote chain.
  have hCases :=
    sat_or_cases (M := M) (w := w)
      (φ := φLeft) (ψ := ψRight) hDisj
  cases hCases with
  | inl hEchoBox =>
      -- Lift the local echo quorum to end-of-time (`lift_boxPast_to_end`).
      have hEchoBox' :
          ⟪w⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) :=
        by simpa [φLeft]
      have hEchoGlobal :
          ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩) :=
        lift_boxPast_to_end (M := M) (t := w)
          (learner := learner) (φ := ofEvent ⟨echoSymb, [value]⟩)
          (hSubset := hSubset_history) (hBox := hEchoBox')
      exact ⟨learner, hEchoGlobal⟩
  | inr hExists =>
      -- Resolve the existential branch of `Vote?`.
      have hExists' :
          ⟪w⟫ ⊨[M]
            ∃ᶠ fun correlated =>
              ofPredicate ⟨correlationSymb, [correlated, learner]⟩ ∧ᶠ
                ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩) :=
        by simpa [ψRight] using hExists
      have hWitness :=
        (Sat.exists_iff (M := M) (w := w)
            (body := fun correlated =>
              ofPredicate ⟨correlationSymb, [correlated, learner]⟩ ∧ᶠ
                ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩))).1
          hExists'
      obtain ⟨correlated, hConj⟩ := hWitness
      have hVoteDiamond :
          ⟪w⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩) :=
        sat_and_right (M := M) (w := w)
          (φ := ofPredicate ⟨correlationSymb, [correlated, learner]⟩)
          (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩))
          hConj
      have hDiamondNil :
          ⟪w⟫ ⊨[M]♢ᶠ[[]](↓ᶠ (ofEvent ⟨voteSymb, [correlated, value]⟩)) :=
        by simpa [Formula.diamondPast] using hVoteDiamond
      -- Extract a predecessor world witnessing the vote (`Sat.diamond_nil`, `Sat.past`).
      obtain ⟨q, hPastVote⟩ :=
        (Sat.diamond_nil (M := M) (w := w)
          (φ := ↓ᶠ (ofEvent ⟨voteSymb, [correlated, value]⟩))).1
          hDiamondNil
      obtain ⟨tVote, ht_mem, ht_place, hVote_at⟩ :=
        (Sat.past (M := M)
          (w := ⟨q, †, w.time⟩)
          (φ := ofEvent ⟨voteSymb, [correlated, value]⟩)).1
          hPastVote
      -- Show the predecessor lies in the global history and has smaller height.
      have ht_mem_history : tVote ∈ M.history.val :=
        hSubset_history _ ht_mem
      have hBefore_vote :
          tVote.time ≺− w.time :=
        History.happensBefore_of_mem
          (P := P) (Event := Signature.EventType S) ht_mem
      -- Apply the induction hypothesis to the earlier vote witness.
      exact
        IH (w' := tVote) hBefore_vote ht_mem_history
          (learner := correlated) (value := value) hVote_at

/-- Paper: Lemma 8.4.2(1). a realised vote yields an
`Echo` quorum for the same value. -/
theorem vote_implies_echo_quorum_local
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {t : World P (Signature.EventType S)}
    {learner value : Signature.Value S}
    (hMem : t ∈ M.history.val)
    (hVote : ⟪t⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩) :
    ∃ source : Signature.Value S,
      ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  -- The paper's "simple inductive argument on time(w)": well-founded
  -- induction along `≺−`.
  have hMain :
      ∀ h : PreHistory P (Signature.EventType S),
        ∀ {w : World P (Signature.EventType S)},
          w.time = h → w ∈ M.history.val →
          ∀ {learner value : Signature.Value S},
            (⟪w⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩) →
              ∃ source : Signature.Value S,
                ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩) := by
    intro h
    induction h using
      (PreHistory.happensBefore_wellFounded
        (P := P) (Event := Signature.EventType S)).induction with
    | _ h IH =>
      intro w hw hMem learner value hVote
      refine
        vote_implies_echo_quorum_step
          (M := M) (liveSymb := liveSymb) (proposeSymb := proposeSymb)
          (echoSymb := echoSymb) (voteSymb := voteSymb)
          (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
          hTheory hMem ?_ hVote
      intro w' hBefore hMem' learner' value' hVote'
      exact
        IH w'.time (hw ▸ hBefore) rfl hMem' hVote'
  exact hMain t.time rfl hMem hVote

/-- Paper: Lemma 8.4.2(2). votes witnessed in the past
produce a global echo quorum. -/
theorem vote_implies_echo_quorum_end
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {learner value : Signature.Value S}
    (hVote : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [learner, value]⟩)) :
    ∃ source : Signature.Value S,
      ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩) := by
  classical
  -- Evaluate the past vote at an end-of-time world.
  let p : P := Classical.ofNonempty
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hVoteTop :
      ⟪wTop⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [learner, value]⟩) :=
    by simpa [wTop] using hVote p
  have hDiamondNil :
      ⟪wTop⟫ ⊨[M]♢ᶠ[[]](↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩)) :=
    by simpa [Formula.diamondPast] using hVoteTop
  -- Unpack the past diamond to obtain a witness world in the history.
  obtain ⟨q, hPastVote⟩ :=
    (Sat.diamond_nil (M := M)
        (w := wTop)
        (φ := ↓ᶠ (ofEvent ⟨voteSymb, [learner, value]⟩))).1
      hDiamondNil
  obtain ⟨tVote, ht_mem, _, hVote_at⟩ :=
    (Sat.past (M := M)
        (w := ⟨q, †, wTop.time⟩)
        (φ := ofEvent ⟨voteSymb, [learner, value]⟩)).1
      hPastVote
  -- The witness lies in the global history.
  have ht_mem_history : tVote ∈ M.history.val :=
    by simpa [wTop, World.time] using ht_mem
  -- Apply the local lemma to obtain the required echo quorum.
  exact
    vote_implies_echo_quorum_local
      (M := M) (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
      hTheory ht_mem_history hVote_at

/-- Deliveries witnessed at end of time yield the backing vote quorum. -/
theorem deliver_to_vote_box_end
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {learner value : Signature.Value S}
    {p : P}
    (hDeliver :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [learner, value]⟩)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
      □ᶠ↓[[learner]](ofEvent ⟨voteSymb, [learner, value]⟩) := by
  classical
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  have hDiamondNil :
      ⟪wTop⟫ ⊨[M]
        ♢ᶠ[[]](↓ᶠ (ofEvent ⟨deliverSymb, [learner, value]⟩)) :=
    by simpa [Formula.diamondPast, wTop] using hDeliver
  obtain ⟨qDeliver, hPastDeliver⟩ :=
    (Sat.diamond_nil (M := M)
      (w := wTop)
      (φ := ↓ᶠ (ofEvent ⟨deliverSymb, [learner, value]⟩))).1
      hDiamondNil
  obtain ⟨tDeliver, ht_mem, ht_place, hDeliver_at⟩ :=
    (Sat.past (M := M)
      (w := ⟨qDeliver, †, wTop.time⟩)
      (φ := ofEvent ⟨deliverSymb, [learner, value]⟩)).1
      hPastDeliver
  have ht_mem_history : tDeliver ∈ M.history.val :=
    by simpa [wTop, World.time] using ht_mem
  have hBox_at_event :
      ⟪tDeliver⟫ ⊨[M]
        □ᶠ↓[[learner]](ofEvent ⟨voteSymb, [learner, value]⟩) :=
    deliverBackward_elim (M := M)
      (theory_deliverBackward (M := M) hTheory)
      (M.time_le_of_mem ht_mem_history)
      hDeliver_at
  have hBefore_history : tDeliver.time ≺− M.history.val :=
    History.happensBefore_of_mem
      (P := P) (Event := Signature.EventType S) ht_mem_history
  have hSubset_history : tDeliver.time ⊆ M.history.val :=
    History.subset_of_happensBefore (H := M.history) hBefore_history
  have hLift :=
    lift_boxPast_to_end (M := M) (t := tDeliver)
      (learner := learner)
      (φ := ofEvent ⟨voteSymb, [learner, value]⟩)
      (hSubset := hSubset_history) (hBox := hBox_at_event)
  simpa [wTop] using hLift p

/-- One-sided application of `VoteNE`: a vote together with a past vote from a
correlated learner forces value equality. -/
theorem voteNonEquiv_local
    (hVoteNE : AllWorldValid M (voteNonEquivAxiom voteSymb correlationSymb))
    {w : World P (Signature.EventType S)}
    (hMem : w ∈ M.history.val)
    {learner correlated : Signature.Value S}
    {valNow valPast : Signature.Value S}
    (hVote_now :
      ⟪w⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, valNow]⟩)
    (hVote_past :
      ⟪w⟫ ⊨[M]↓ᶠ (ofEvent ⟨voteSymb, [correlated, valPast]⟩))
    (hCorr :
      ⟪w⟫ ⊨[M]ofPredicate ⟨correlationSymb, [learner, correlated]⟩) :
    valNow = valPast := by
  classical
  have hEqFormula :=
    voteNonEquiv_elim (M := M)
      (hAx := hVoteNE)
      (M.time_le_of_mem hMem)
      hVote_now hVote_past hCorr
  have hEq :=
    (Sat.eq (M := M) (w := w)
      (v₁ := valNow) (v₂ := valPast)).1 hEqFormula
  simpa [Sat] using hEq

/-- Paper: Lemma 8.4.3(1). sequential echo quorums fix the
broadcast value. -/
theorem echo_quorums_agree
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l l₁ l₂ : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq)
    (hEcho₁ : ⊨[M]□ᶠ↓[[l₁]](ofEvent ⟨echoSymb, [v₁]⟩))
    (hEcho₂ : ⊨[M]□ᶠ↓[[l₂]](ofEvent ⟨echoSymb, [v₂]⟩)) :
    v₁ = v₂ := by
  -- Any guarded echo quorum witnesses a concrete point in the global history.
  have hHistory :
      ∃ t : World P (Signature.EventType S), t ∈ M.history.val :=
    exists_history_mem_of_end_boxPast (M := M)
      (l := l₁)
      (φ := ofEvent ⟨echoSymb, [v₁]⟩)
      (hBox := hEcho₁)
  -- Intermediate sequential-collision step using sequential quorum intersection.
  have hSeqEchoDiamond :
      ⊨[M]
        ♢ᶠ[[]]
          ((Formula.seq ∧ᶠ
              ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)) ∧ᶠ
            ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)) := by
    classical
    have hThreeTwined :=
      threeTwined_boxes_intersect (M := M)
        (l₁ := l) (l₂ := l₁) (l₃ := l₂)
        (φ₁ := Formula.seq)
        (φ₂ := ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩))
        (φ₃ := ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩))
    have hTripleDiamond :
        ⊨[M] ♢ᶠ[[l, l₁, l₂]] ⊤ᶠ := by
      classical
      have hNonempty :=
        threeTwined_hasQuorumNonempty
          (M := M)
          (hTheory := hTheory)
          (hHistory := hHistory)
          (l₁ := l)
          (l₂ := l₁)
          (l₃ := l₂)
      intro p
      exact
        (sat_diamond_top_iff_hasQuorumNonempty (M := M)
            (w := ⟨p, †, M.history.val⟩)
            (ls := [l, l₁, l₂])).2 hNonempty
    have hEcho₁Box :
        ⊨[M]□ᶠ[[l₁]] (↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)) := by
      simpa [Formula.boxPast] using hEcho₁
    have hEcho₂Box :
        ⊨[M]□ᶠ[[l₂]] (↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)) := by
      simpa [Formula.boxPast] using hEcho₂
    intro p
    set w : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
    have hThreeTwined_w := hThreeTwined p
    have hTripleDiamond_w := hTripleDiamond p
    have hSeqBox_w := hSeq p
    have hEcho₁Box_w := hEcho₁Box p
    have hEcho₂Box_w := hEcho₂Box p
    have hImpDiamond :=
      Sat.imp_elim (M := M) (w := w)
        (φ := ♢ᶠ[[l, l₁, l₂]] ⊤ᶠ)
        (ψ :=
          (((□ᶠ[[l]] Formula.seq) ∧ᶠ
                □ᶠ[[l₁]] (↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩))) ∧ᶠ
              □ᶠ[[l₂]] (↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩))) ⇒ᶠ
            ♢ᶠ[]
              ((Formula.seq ∧ᶠ ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)) ∧ᶠ
                ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)))
        hThreeTwined_w hTripleDiamond_w
    have hBoxesPair :=
      Sat.and_intro (M := M) (w := w)
        (φ := □ᶠ[[l]] Formula.seq)
        (ψ := □ᶠ[[l₁]] (↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)))
        hSeqBox_w hEcho₁Box_w
    have hBoxesAll :=
      Sat.and_intro (M := M) (w := w)
        (φ := (□ᶠ[[l]] Formula.seq) ∧ᶠ
          (□ᶠ[[l₁]] (↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩))))
        (ψ := □ᶠ[[l₂]] (↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)))
        hBoxesPair hEcho₂Box_w
    exact
      Sat.imp_elim (M := M) (w := w)
        (φ := ((□ᶠ[[l]] Formula.seq) ∧ᶠ
                (□ᶠ[[l₁]] (↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)))) ∧ᶠ
              □ᶠ[[l₂]] (↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)))
        (ψ :=
          ♢ᶠ[]
            ((Formula.seq ∧ᶠ ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)) ∧ᶠ
              ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)))
        hImpDiamond hBoxesAll
  by_cases hEq : v₁ = v₂
  · simp [hEq]
  · have hNe : v₁ ≠ v₂ := hEq
    have hEventNe :
        (⟨echoSymb, [v₁]⟩ : Signature.EventType S) ≠
          ⟨echoSymb, [v₂]⟩ := by
      intro hEvt
      cases hEvt
      exact hNe rfl
    -- Evaluate the diamond at the global end-of-time world.
    let p₀ : P := Classical.ofNonempty
    set wTop : World P (Signature.EventType S) := ⟨p₀, †, M.history.val⟩
    have hDiamondTop :
        ⟪wTop⟫ ⊨[M]
          (♢ᶠ[[]]
            ((Formula.seq ∧ᶠ
                ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)) ∧ᶠ
              ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩))) :=
      by
        have := hSeqEchoDiamond p₀
        simpa [wTop]
          using this
    let φEcho :=
      (Formula.seq ∧ᶠ
          ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)) ∧ᶠ
        ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)
    have hWitnessPair :=
      Iff.mp
        (Sat.diamond_nil (M := M) (w := wTop) (φ := φEcho))
        hDiamondTop
    obtain ⟨pEcho, hWitness⟩ := hWitnessPair
    set wEcho : World P (Signature.EventType S) :=
      ⟨pEcho, †, wTop.time⟩
    have hSplit :=
      (Sat.and (M := M) (w := wEcho)
        (φ := Formula.seq ∧ᶠ ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩))
        (ψ := ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩))).1 hWitness
    have hSeqAnd := hSplit.1
    have hEcho₂_local := hSplit.2
    have hSeqSplit :=
      (Sat.and (M := M) (w := wEcho)
        (φ := Formula.seq)
        (ψ := ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩))).1 hSeqAnd
    have hSeq_local := hSeqSplit.1
    have hEcho₁_local := hSeqSplit.2
    -- Sequential order yields a collision diamond in one of the two directions.
    have hEchoCollision_local :
        ⟪wEcho⟫ ⊨[M]
          ((♢ᶠ↓[[]]
              ((ofEvent ⟨echoSymb, [v₁]⟩) ∧ᶠ
                ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩))) ∨ᶠ
            (♢ᶠ↓[[]]
              ((ofEvent ⟨echoSymb, [v₂]⟩) ∧ᶠ
                ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)))) :=
      seq_two_quorums_events (M := M)
        (w := wEcho)
        (evt := ⟨echoSymb, [v₁]⟩)
        (evt' := ⟨echoSymb, [v₂]⟩)
        (hSeq := hSeq_local)
        (hEvt_local := hEcho₁_local)
        (hEvt'_local := hEcho₂_local)
        (hDistinct := hEventNe)
    -- `EchoNE` turns the collision diamond into equality.
    have hEchoNE : AllWorldValid M (echoNonEquivAxiom echoSymb) :=
      theory_echoNonEquiv (M := M) hTheory
    have hSubset : wEcho.time ⊆trn M.history.val := by
      simpa [wEcho, wTop]
        using History.transitiveSubset_refl (H := M.history)
    have hEquality : v₁ = v₂ := by
      cases
          sat_or_cases (M := M) (w := wEcho)
            (φ := ♢ᶠ↓[[]]
                ((ofEvent ⟨echoSymb, [v₁]⟩) ∧ᶠ
                  ↓ᶠ (ofEvent ⟨echoSymb, [v₂]⟩)))
            (ψ := ♢ᶠ↓[[]]
                ((ofEvent ⟨echoSymb, [v₂]⟩) ∧ᶠ
                  ↓ᶠ (ofEvent ⟨echoSymb, [v₁]⟩)))
            hEchoCollision_local with
      | inl hLeft =>
          exact
            ThyHBB1.echoNonEquiv_diamond (M := M)
              (echoSymb := echoSymb)
              (hEchoNE := hEchoNE)
              (w := wEcho)
              (hSubset := hSubset)
              (valNow := v₁)
              (valPast := v₂)
              hLeft
      | inr hRight =>
          have hEq :=
            ThyHBB1.echoNonEquiv_diamond (M := M)
              (echoSymb := echoSymb)
              (hEchoNE := hEchoNE)
              (w := wEcho)
              (hSubset := hSubset)
              (valNow := v₂)
              (valPast := v₁)
              hRight
          exact hEq.symm
    exact hEquality

/-- Paper: Lemma 8.4.3(2). past votes also determine a unique
value once sequentiality holds. -/
theorem votes_eventually_agree
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l l₁ l₂ : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq)
    (hVote₁ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v₁]⟩))
    (hVote₂ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₂, v₂]⟩)) :
    v₁ = v₂ := by
  classical
  obtain ⟨source₁, hEcho₁⟩ :=
    vote_implies_echo_quorum_end
      (M := M)
      (hTheory := hTheory)
      (learner := l₁) (value := v₁)
      (hVote := hVote₁)
  obtain ⟨source₂, hEcho₂⟩ :=
    vote_implies_echo_quorum_end
      (M := M)
      (hTheory := hTheory)
      (learner := l₂) (value := v₂)
      (hVote := hVote₂)
  exact
    echo_quorums_agree
      (M := M)
      (hTheory := hTheory)
      (l := l) (l₁ := source₁) (l₂ := source₂)
      (v₁ := v₁) (v₂ := v₂)
      (hSeq := hSeq)
      (hEcho₁ := hEcho₁)
      (hEcho₂ := hEcho₂)

theorem always_corr_symm
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {w : World P (Signature.EventType S)}
    {l₁ l₂ : Signature.Value S} :
    (⟪w⟫ ⊨[M] ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) →
      (⟪w⟫ ⊨[M] ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) := by
  classical
  intro hAlways
  refine
    (Sat.everytime (M := M) (w := w)
      (φ := ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)).2 ?_
  intro t ht hp
  exact
    correlationSymm_elim (M := M)
      (theory_correlationSymm (M := M) hTheory)
      (M.time_le_of_mem ht)
      ((Sat.everytime (M := M) (w := w)
        (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)).1 hAlways t ht hp)

/-- End-of-time correlation together with the persistence axiom yields
correlation throughout each participant’s history. -/
theorem correlation_global_allPast
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    □W⊨[M] ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) := by
  classical
  intro t ht_le
  refine
    (Sat.everytime (M := M) (w := t)
      (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)).2 ?_
  intro s hs hp
  -- Correlation holds at the end of time at `s.place`…
  have hCorrTop :
      ⟪⟨s.place, †, M.history.val⟩⟫ ⊨[M]
        ofPredicate ⟨correlationSymb, [l₁, l₂]⟩ :=
    (EndValid.boxEmpty_guard (M := M)
      (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) hCorrelation) s.place
  -- …so, by `(≐⇓)`, it holds throughout that participant's past.
  have hAllPast :
      ⟪⟨s.place, †, M.history.val⟩⟫ ⊨[M]
        ⇓ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) :=
    correlationMonotone_elim (M := M)
      (theory_correlationMonotone (M := M) hTheory)
      (by simp [World.time])
      hCorrTop
  exact
    (Sat.allPast (M := M)
      (w := ⟨s.place, †, M.history.val⟩)
      (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)).1
      hAllPast s (by simpa [World.time] using hs) rfl

/-- Correlated learners admit a sequential intersection witness. -/
theorem correlation_seq_diamond
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    ⊨[M]♢ᶠ[[l₁, l₂]] Formula.seq := by
  classical
  intro p
  exact
    correlationSeq_elim (M := M)
      (theory_correlationSeq (M := M) hTheory)
      (by simp [World.time])
      ((EndValid.boxEmpty_guard (M := M)
        (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) hCorrelation) p)

/-- Helper: Split antecedent `(live ∧ corr) ∧ ◊vote` into components -/
theorem split_live_corr_vote_antecedent
    {w : World P (Signature.EventType S)}
    {l₁ l₂ v : Signature.Value S}
    (hAnte : ⟪w⟫ ⊨[M]((predicate0 liveSymb ∧ᶠ
          ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))) :
    (⟪w⟫ ⊨[M] predicate0 liveSymb) ∧
    (⟪w⟫ ⊨[M] ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) := by
  have hAnteSplit :=
    (Sat.and (M := M) (w := w)
        (φ := predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
        (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))).1
      hAnte
  have hLiveCorr :=
    (Sat.and (M := M) (w := w)
        (φ := predicate0 liveSymb)
        (ψ := ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))).1
      hAnteSplit.1
  exact ⟨hLiveCorr.1, hLiveCorr.2, hAnteSplit.2⟩

/-- Helper: Chain three forall eliminations for vote correlation axiom -/
theorem forall_elim_vote_correlated_chain
    {w : World P (Signature.EventType S)}
    {l₁ l₂ v : Signature.Value S}
    (hVoteCorrLocal : ⟪w⟫ ⊨[M]voteForwardCorrelatedAxiom liveSymb voteSymb correlationSymb) :
    ⟪w⟫ ⊨[M]
      (predicate0 liveSymb ∧ᶠ
          (⇕ᶠ (ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) ⇒ᶠ
        ∃ᶠ fun witnessed =>
          ↕ᶠ (ofEvent ⟨voteSymb, [l₂, witnessed]⟩) := by
  have hVoteCorrFor₁ :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner =>
        ∀ᶠ fun correlated => ∀ᶠ fun value =>
          (predicate0 liveSymb ∧ᶠ
              (⇕ᶠ (ofPredicate ⟨correlationSymb, [learner, correlated]⟩)) ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩)) ⇒ᶠ
            ∃ᶠ fun witnessed =>
              ↕ᶠ (ofEvent ⟨voteSymb, [learner, witnessed]⟩))
      (v := l₂) hVoteCorrLocal
  have hVoteCorrFor₂ :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun correlated => ∀ᶠ fun value =>
        (predicate0 liveSymb ∧ᶠ
            (⇕ᶠ (ofPredicate ⟨correlationSymb, [l₂, correlated]⟩)) ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [correlated, value]⟩)) ⇒ᶠ
          ∃ᶠ fun witnessed =>
            ↕ᶠ (ofEvent ⟨voteSymb, [l₂, witnessed]⟩))
      (v := l₁) hVoteCorrFor₁
  have hVoteCorrFor₃ :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun value =>
        (predicate0 liveSymb ∧ᶠ
            (⇕ᶠ (ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, value]⟩)) ⇒ᶠ
          ∃ᶠ fun witnessed =>
            ↕ᶠ (ofEvent ⟨voteSymb, [l₂, witnessed]⟩))
      (v := v) hVoteCorrFor₂
  simpa [voteForwardCorrelatedAxiom] using hVoteCorrFor₃

/-- Helper: Chain two forall eliminations for vote forward axiom -/
theorem forall_elim_vote_forward_chain
    {w : World P (Signature.EventType S)}
    {l v : Signature.Value S}
    (hVoteLocal : ⟪w⟫ ⊨[M]voteForwardAxiom liveSymb echoSymb voteSymb) :
    ⟪w⟫ ⊨[M]
      (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩)) ⇒ᶠ
        ∃ᶠ fun witnessed =>
          ↕ᶠ (ofEvent ⟨voteSymb, [l, witnessed]⟩) := by
  have hImpLearner :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun learner =>
        ∀ᶠ fun value =>
          (predicate0 liveSymb ∧ᶠ
              □ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
            ∃ᶠ fun witnessed =>
              ↕ᶠ (ofEvent ⟨voteSymb, [learner, witnessed]⟩))
      (v := l) hVoteLocal
  have hImpValue :=
    Sat.forall_elim (M := M) (w := w)
      (body := fun value =>
        (predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]](ofEvent ⟨echoSymb, [value]⟩)) ⇒ᶠ
          ∃ᶠ fun witnessed =>
            ↕ᶠ (ofEvent ⟨voteSymb, [l, witnessed]⟩))
      (v := v) hImpLearner
  exact hImpValue

/-- Helper: Lift local `↕vote` to global `◊↓vote` using subset reasoning -/
theorem lift_local_vote_to_global
    {t : World P (Signature.EventType S)}
    {l v : Signature.Value S}
    (ht : t.time ⪯ M.history.val)
    (hVote : ⟪t⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l, v]⟩)) :
    ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l, v]⟩) := by
  have hSubset_trn :
      t.time ⊆trn M.history.val :=
    ModalDistribution.Logic.time_subset_trn_history
      (M := M) (t := t) ht
  intro p
  simpa using
    (sat_diamondPast_nil_event_subset (M := M)
      (w := ⟨p, †, M.history.val⟩)
      (w' := t)
      (symb := voteSymb)
      (args := [l, v])
      (hSubset := hSubset_trn)
      hVote)

/-- Helper: Unpack existential vote witness and lift to global diamond -/
theorem vote_exists_to_global_diamond
    {t : World P (Signature.EventType S)}
    {l v : Signature.Value S}
    (hVote : ⟪t⟫ ⊨[M]↕ᶠ(ofEvent ⟨voteSymb, [l, v]⟩)) :
    ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l, v]⟩) := by
  have hSometimeVote :=
    (Sat.sometime (M := M) (w := t)
        (φ := ofEvent ⟨voteSymb, [l, v]⟩)).1 hVote
  obtain ⟨tVote, htVote_mem, htVote_place, hVote_event⟩ := hSometimeVote
  intro p
  have hPastVote :
      ⟪⟨tVote.place, †, M.history.val⟩⟫ ⊨[M]
        ↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩) := by
    refine
      (Sat.past (M := M)
          (w := ⟨tVote.place, †, M.history.val⟩)
          (φ := ofEvent ⟨voteSymb, [l, v]⟩)).2 ?_
    refine ⟨tVote, htVote_mem, rfl, hVote_event⟩
  have hDiamondTop :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
        ♢ᶠ[[]](↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) :=
    (Sat.diamond_nil (M := M)
        (w := ⟨p, †, M.history.val⟩)
        (φ := ↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).2
      ⟨tVote.place, hPastVote⟩
  simpa [Formula.diamondPast] using hDiamondTop

/-- Helper: splits the compound antecedent, obtains symmetric correlation,
and rebuilds the antecedent with swapped learners. -/
theorem split_and_swap_correlation
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {t : World P (Signature.EventType S)}
    {l₁ l₂ : Signature.Value S}
    {v : Signature.Value S}
    (hAnte : ⟪t⟫ ⊨[M]((predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))) :
    ⟪t⟫ ⊨[M]
      ((predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) := by
  -- Split antecedent into live, correlation, and vote components
  have ⟨hLive, hCorr₁, hVote₁⟩ :=
    split_live_corr_vote_antecedent (M := M)
      (liveSymb := liveSymb) (correlationSymb := correlationSymb) (voteSymb := voteSymb)
      (w := t) (l₁ := l₁) (l₂ := l₂) (v := v) hAnte
  -- Get symmetric correlation
  have hCorr₂ :=
    always_corr_symm (M := M)
      (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
      (hTheory := hTheory) (w := t)
      (l₁ := l₁) (l₂ := l₂) hCorr₁
  -- Build swapped antecedent
  have hLiveCorrSym :=
    (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb)
        (ψ := ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₂, l₁]⟩))).2
      ⟨hLive, hCorr₂⟩
  exact
    (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₂, l₁]⟩))
        (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))).2
      ⟨hLiveCorrSym, hVote₁⟩

/-- Helper: applies the voteForwardCorrelatedAxiom via forall elimination
and extracts the witness value from the existential. -/
theorem apply_vote_corr_and_extract_witness
    {t : World P (Signature.EventType S)}
    {l₁ l₂ : Signature.Value S}
    {v : Signature.Value S}
    (hVoteCorrLocal : ⟪t⟫ ⊨[M](voteForwardCorrelatedAxiom liveSymb voteSymb correlationSymb))
    (hVoteAnte : ⟪t⟫ ⊨[M]((predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))) :
    ∃ v₂ : Signature.Value S,
      ⟪t⟫ ⊨[M] (↕ᶠ (ofEvent ⟨voteSymb, [l₂, v₂]⟩)) := by
  -- Apply vote correlation axiom via forall elimination chain
  have hVoteImp :=
    (Sat.imp (M := M) (w := t)
        (φ :=
          ((predicate0 liveSymb ∧ᶠ
                ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)))
        (ψ :=
          ∃ᶠ fun witnessed =>
            ↕ᶠ (ofEvent ⟨voteSymb, [l₂, witnessed]⟩))).1
      (forall_elim_vote_correlated_chain (M := M)
        (liveSymb := liveSymb) (voteSymb := voteSymb) (correlationSymb := correlationSymb)
        (w := t) (l₁ := l₁) (l₂ := l₂) (v := v) hVoteCorrLocal)
  have hVoteExists := hVoteImp hVoteAnte
  -- Extract witness value
  exact
    (Sat.exists_iff (M := M) (w := t)
        (body := fun witnessed =>
          ↕ᶠ (ofEvent ⟨voteSymb, [l₂, witnessed]⟩))).1
      hVoteExists

/-- Helper: lifts both votes to global and applies agreement to prove
the values are equal. -/
theorem agree_on_correlated_votes
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {t : World P (Signature.EventType S)}
    (ht : t.time ⪯ M.history.val)
    {l : Signature.Value S}
    {l₁ l₂ : Signature.Value S}
    {v v₂ : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq)
    (hVote₁ : ⟪t⟫ ⊨[M](♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)))
    (hVote₂ : ⟪t⟫ ⊨[M](↕ᶠ(ofEvent ⟨voteSymb, [l₂, v₂]⟩))) :
    v = v₂ := by
  -- Lift both votes to global
  have hVote₁_global :=
    lift_local_vote_to_global (M := M)
      (voteSymb := voteSymb)
      (t := t) (l := l₁) (v := v) ht hVote₁
  have hVote₂_global :=
    vote_exists_to_global_diamond (M := M)
      (voteSymb := voteSymb)
      (t := t) (l := l₂) (v := v₂) hVote₂
  -- Apply agreement lemma
  exact
    votes_eventually_agree (M := M)
      (liveSymb := liveSymb)
      (proposeSymb := proposeSymb) (echoSymb := echoSymb)
      (voteSymb := voteSymb) (deliverSymb := deliverSymb)
      (correlationSymb := correlationSymb)
      (hTheory := hTheory)
      (l := l) (l₁ := l₁) (l₂ := l₂)
      (v₁ := v) (v₂ := v₂)
      (hSeq := hSeq)
      (hVote₁ := hVote₁_global) (hVote₂ := hVote₂_global)

/-- Paper: Lemma 8.4.3(3). correlated live knowledge of a vote
forces eventual votes for the correlated learner. -/
theorem correlated_vote_eventually
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l : Signature.Value S}
    {l₁ l₂ : Signature.Value S}
    {v : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq) :
    □W⊨[M]
      (((predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) ⇒ᶠ
        ↕ᶠ (ofEvent ⟨voteSymb, [l₂, v]⟩)) := by
  classical
  have hVoteCorrAx :
      AllWorldValid M
        (voteForwardCorrelatedAxiom liveSymb voteSymb correlationSymb) :=
    theory_voteForwardCorrelated (M := M) hTheory
  intro t ht
  have hVoteCorrLocal := hVoteCorrAx ht
  refine
    Sat.imp_intro (M := M) (w := t)
      (φ :=
        ((predicate0 liveSymb ∧ᶠ
              ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
            ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)))
      (ψ := ↕ᶠ (ofEvent ⟨voteSymb, [l₂, v]⟩)) ?_
  intro hAnte
  -- Split antecedent and swap correlation
  have hVoteAnte := split_and_swap_correlation hTheory hAnte
  -- Extract original vote for agreement
  have hVote₁ :=
    (split_live_corr_vote_antecedent (M := M)
      (liveSymb := liveSymb) (correlationSymb := correlationSymb) (voteSymb := voteSymb)
      (w := t) (l₁ := l₁) (l₂ := l₂) (v := v) hAnte).2.2
  -- Apply axiom and extract witness
  obtain ⟨v₂, hVote₂⟩ := apply_vote_corr_and_extract_witness hVoteCorrLocal hVoteAnte
  -- Prove values agree
  have hValueEq : v = v₂ :=
    agree_on_correlated_votes hTheory ht hSeq hVote₁ hVote₂
  cases hValueEq
  simpa using hVote₂

/-- Helper: applies the voteForwardAxiom via forall elimination
and extracts the witness value from the existential. -/
theorem apply_vote_forward_and_extract_witness
    {t : World P (Signature.EventType S)}
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hVoteLocal : ⟪t⟫ ⊨[M](voteForwardAxiom liveSymb echoSymb voteSymb))
    (hLive : ⟪t⟫ ⊨[M](predicate0 liveSymb))
    (hEchoLocal : ⟪t⟫ ⊨[M](□ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩))) :
    ∃ v₂ : Signature.Value S,
      ⟪t⟫ ⊨[M] (↕ᶠ (ofEvent ⟨voteSymb, [l, v₂]⟩)) := by
  -- Apply vote forward axiom via forall elimination chain
  have hVoteImp :=
    (Sat.imp (M := M) (w := t)
        (φ :=
          predicate0 liveSymb ∧ᶠ
            □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩))
        (ψ :=
          ∃ᶠ fun witnessed =>
            ↕ᶠ (ofEvent ⟨voteSymb, [l, witnessed]⟩))).1
      (forall_elim_vote_forward_chain (M := M)
        (liveSymb := liveSymb) (echoSymb := echoSymb) (voteSymb := voteSymb)
        (w := t) (l := l) (v := v) hVoteLocal)
  have hVoteAnte' :=
    (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩))).2
      ⟨hLive, hEchoLocal⟩
  have hVoteExists := hVoteImp hVoteAnte'
  -- Extract witness value
  exact
    (Sat.exists_iff (M := M) (w := t)
        (body := fun witnessed =>
          ↕ᶠ (ofEvent ⟨voteSymb, [l, witnessed]⟩))).1
      hVoteExists

/-- Helper: lifts vote to global, extracts echo source, applies agreement,
and returns simplified result. -/
theorem agree_on_echo_and_vote
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {t : World P (Signature.EventType S)}
    (hSubset : t.time ⊆ M.history.val)
    {l : Signature.Value S}
    {v v₂ : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq)
    (hEchoLocal : ⟪t⟫ ⊨[M](□ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩)))
    (hVote₂ : ⟪t⟫ ⊨[M](↕ᶠ(ofEvent ⟨voteSymb, [l, v₂]⟩))) :
    ⟪t⟫ ⊨[M] (↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
  -- Lift echo to global
  have hEchoGlobal :=
    lift_boxPast_to_end (M := M)
      (t := t) (learner := l)
      (φ := ofEvent ⟨echoSymb, [v]⟩)
      (hSubset := hSubset) (hBox := hEchoLocal)
  -- Lift vote to global
  have hVote₂_global :=
    vote_exists_to_global_diamond (M := M)
      (voteSymb := voteSymb)
      (t := t) (l := l) (v := v₂) hVote₂
  -- Extract echo source from vote
  obtain ⟨sourceEcho, hEchoVote⟩ :=
    vote_implies_echo_quorum_end
      (M := M)
      (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
      (hTheory := hTheory)
      (learner := l) (value := v₂)
      (hVote := hVote₂_global)
  -- Apply echo agreement
  have hValueEq' : v = v₂ :=
    echo_quorums_agree (M := M)
      (liveSymb := liveSymb) (proposeSymb := proposeSymb)
      (echoSymb := echoSymb) (voteSymb := voteSymb)
      (deliverSymb := deliverSymb) (correlationSymb := correlationSymb)
      (hTheory := hTheory)
      (l := l) (l₁ := l) (l₂ := sourceEcho)
      (v₁ := v) (v₂ := v₂)
      (hSeq := hSeq)
      (hEcho₁ := hEchoGlobal)
      (hEcho₂ := hEchoVote)
  have hValueEq : v₂ = v := hValueEq'.symm
  simpa [hValueEq] using hVote₂

/-- Paper: Lemma 8.4.3(4). a live echo quorum yields eventual
votes for the same learner. -/
theorem live_echo_eventually_vote
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq) :
    □W⊨[M]
      ((predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩)) ⇒ᶠ
        ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
  classical
  have hVoteAx : AllWorldValid M (voteForwardAxiom liveSymb echoSymb voteSymb) :=
    theory_voteForward (M := M) hTheory
  intro t htMem
  have hVoteLocal := hVoteAx htMem
  refine
    Sat.imp_intro (M := M) (w := t)
      (φ :=
        predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩))
      (ψ := ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) ?_
  intro hAnte
  -- Split antecedent
  have hLiveEcho :=
    (Sat.and (M := M) (w := t)
        (φ := predicate0 liveSymb)
        (ψ := □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩))).1 hAnte
  have hLive := hLiveEcho.1
  have hEchoLocal := hLiveEcho.2
  -- Compute subset for later use
  have hSubset_history_trn :
      t.time ⊆trn M.history.val :=
    ModalDistribution.Logic.time_subset_trn_history
      (M := M) (t := t) htMem
  have hSubset_history : t.time ⊆ M.history.val :=
    History.transitiveSubset_subset hSubset_history_trn
  -- Apply axiom and extract witness
  obtain ⟨v₂, hVote₂⟩ := apply_vote_forward_and_extract_witness hVoteLocal hLive hEchoLocal
  -- Prove values agree and simplify
  exact agree_on_echo_and_vote hTheory hSubset_history hSeq hEchoLocal hVote₂

/-- Paper: Lemma 8.4.4(1). If someone believes `l₁` correlates with `l₂`, then their quorums
intersect. This is the paper's Lemma 8.4.4(1), proved from the `(≐seq)`
axiom at the believing participant. -/
theorem correlationImpliesPairwiseQuorumIntersection
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S}
    (hSomeone : ⊨[M]♢ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    ⊨[M]♢ᶠ[[l₁, l₂]] ⊤ᶠ := by
  classical
  intro p
  set wTop : World P (Signature.EventType S) := ⟨p, †, M.history.val⟩
  obtain ⟨q, hq⟩ :=
    (Sat.diamondEmpty (M := M) (w := wTop)
      (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)).1
      (by simpa [wTop] using hSomeone p)
  set wq : World P (Signature.EventType S) := ⟨q, †, M.history.val⟩
  have hSeqDiamond : ⟪wq⟫ ⊨[M] ♢ᶠ[[l₁, l₂]] Formula.seq :=
    correlationSeq_elim (M := M)
      (theory_correlationSeq (M := M) hTheory)
      (by simp [wq, World.time])
      (by simpa [wq, wTop] using hq)
  have hTopDiamond : ⟪wq⟫ ⊨[M] ♢ᶠ[[l₁, l₂]] ⊤ᶠ :=
    Sat.diamond_of_imp (M := M) (w := wq)
      (ts := [l₁, l₂])
      (h := fun r _ => Sat.top (M := M) (w := ⟨r, †, wq.time⟩))
      hSeqDiamond
  simpa [wq, wTop] using hTopDiamond

/-- Paper: Lemma 8.4.4(2). Universal correlation implies quorum intersection. This is the paper's
Lemma 8.4.4(2), derived from part 1 by weakening `□` to `♢`. -/
theorem correlationImpliesQuorumIntersection
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
    {l₁ l₂ : Signature.Value S}
    (hEveryone : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    ⊨[M]♢ᶠ[[l₁, l₂]] ⊤ᶠ := by
  classical
  have hSomeone :
      ⊨[M]♢ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩) := by
    intro p
    have hAll :=
      (Sat.boxEmpty (M := M)
        (w := ⟨p, †, M.history.val⟩)
        (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)).1
        (hEveryone p)
    exact
      (Sat.diamondEmpty (M := M)
        (w := ⟨p, †, M.history.val⟩)
        (φ := ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)).2
        ⟨p, hAll p⟩
  exact
    correlationImpliesPairwiseQuorumIntersection
      (M := M) hTheory hSomeone


end ThyHBB3
end Examples
end ModalDistribution
