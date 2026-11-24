import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBB.Uniqueness
import ModalDistribution.Examples.HBBCorr.Axioms
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.History
/-!
# HBBCorr lemmas (Section 8.4)

The lemmas of Section 8.4 of the paper, used by Agreement (Proposition 8.3.1),
Cascade Termination (Proposition 8.4.5) and Happy Termination
(Proposition 8.5.1):

* Lemma 8.4.1: `(3twined)` makes three quorum boxes meet at one participant.
* Lemma 8.4.2: a vote is backed by an echo quorum for its value.
* Lemma 8.4.3: echo quorums, and therefore votes, agree on the value; votes
  propagate along correlation and from live echo quorums.
* Lemma 8.4.4: correlated learners have intersecting quorums.

They are preceded by a few facts about past events at the end of time, and by
the consequences of `(Deliver?)` and the correlation axioms that the proofs
use repeatedly.
-/

namespace ModalDistribution
namespace Examples
namespace HBBCorr

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}
variable {correlationSymb : Signature.PredSymb S}

/-! ### Past events at the end of time -/

section PastEvents

variable {w : World P (Signature.EventType S)} {φ : Formula S}

/-- `♢↓φ` holds at `w` exactly when `φ` holds at some event-tuple in the past
of `w`. -/
theorem sat_diamondPast_nil_iff :
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] φ) ↔ ∃ t ∈ w.time, ⟪t⟫ ⊨[M] φ := by
  constructor
  · intro h
    obtain ⟨_, h⟩ := (Sat.diamond_nil ..).1 h
    obtain ⟨t, ht, -, h⟩ := (Sat.past ..).1 h
    exact ⟨t, ht, h⟩
  · rintro ⟨t, ht, h⟩
    exact (Sat.diamond_nil ..).2 ⟨t.place, (Sat.past ..).2 ⟨t, ht, rfl, h⟩⟩

/-- `♢↓φ` is valid at the end of time exactly when `φ` holds at some
event-tuple of the model. -/
theorem endValid_diamondPast_nil_iff :
    (⊨[M] ♢ᶠ↓[[]] φ) ↔ ∃ t ∈ M.history.val, ⟪t⟫ ⊨[M] φ :=
  ⟨fun h => sat_diamondPast_nil_iff.1 (h Classical.ofNonempty),
   fun h _ => sat_diamondPast_nil_iff.2 h⟩

/-- What happened in the past of an event-tuple of the model happened in the
past of the end of time. -/
theorem endValid_diamondPast_nil_of_mem (hw : w ∈ M.history.val)
    (h : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] φ) : ⊨[M] ♢ᶠ↓[[]] φ :=
  let ⟨t, ht, hφ⟩ := sat_diamondPast_nil_iff.1 h
  endValid_diamondPast_nil_iff.2
    ⟨t, subset_of_happensBefore (happensBefore_of_mem hw) _ ht, hφ⟩

/-- What happens sometime happened in the past of the end of time. -/
theorem endValid_diamondPast_nil_of_sometime (h : ⟪w⟫ ⊨[M] ↕ᶠ φ) :
    ⊨[M] ♢ᶠ↓[[]] φ :=
  let ⟨t, ht, _, hφ⟩ := (Sat.sometime ..).1 h
  endValid_diamondPast_nil_iff.2 ⟨t, ht, hφ⟩

/-- `↕` is monotone along implications that hold at every event-tuple of the
model. -/
theorem sometime_mono {ψ : Formula S}
    (hImp : ∀ t ∈ M.history.val, (⟪t⟫ ⊨[M] φ) → ⟪t⟫ ⊨[M] ψ)
    (h : ⟪w⟫ ⊨[M] ↕ᶠ φ) : ⟪w⟫ ⊨[M] ↕ᶠ ψ :=
  let ⟨t, ht, hPlace, hφ⟩ := (Sat.sometime ..).1 h
  (Sat.sometime ..).2 ⟨t, ht, hPlace, hImp t ht hφ⟩

end PastEvents

/-! ### Lemma 8.4.1: three quorums meet -/

/-- Paper: Lemma 8.4.1. `3twined` combines three guarded box facts
into a joint diamond witness. -/
theorem three_twined_boxes_intersect
    {l₁ l₂ l₃ : Signature.Value S}
    {φ₁ φ₂ φ₃ : Formula S} :
    ⊨[M]
      ((♢ᶠ[[l₁, l₂, l₃]] ⊤ᶠ) ⇒ᶠ
        ((□ᶠ[[l₁]] φ₁) ∧ᶠ (□ᶠ[[l₂]] φ₂) ∧ᶠ (□ᶠ[[l₃]] φ₃) ⇒ᶠ
          ♢ᶠ[] (φ₁ ∧ᶠ φ₂ ∧ᶠ φ₃))) := by
  intro p hIntersect hBoxes
  -- Pick an `lᵢ`-quorum `Oᵢ` on which `φᵢ` holds, for each `i`.
  simp only [Sat.and, sat_box_singleton_exists] at hBoxes
  obtain ⟨⟨⟨O₁, hO₁, h₁⟩, O₂, hO₂, h₂⟩, O₃, hO₃, h₃⟩ := hBoxes
  -- The three quorums meet at some `q`, where all three `φᵢ` hold.
  obtain ⟨q, hq₁, hq₂, hq₃⟩ := sat_diamond_three_intersection M _ hIntersect hO₁ hO₂ hO₃
  exact sat_diamondEmpty_of_local M _ _
    ⟨q, (Sat.and ..).2 ⟨(Sat.and ..).2 ⟨h₁ q hq₁, h₂ q hq₂⟩, h₃ q hq₃⟩⟩

section Theory

variable (hTheory : M ⊨ᵀ
  theory liveSymb proposeSymb echoSymb voteSymb deliverSymb correlationSymb)
include hTheory

/-! ### Consequences of `(Deliver?)` and the correlation axioms -/

/-- `(Deliver?)` at the end of time: a past delivery for `learner` is backed by
a `learner`-quorum of votes for the same value. -/
theorem deliver_to_vote_box_end
    {learner value : Signature.Value S} {p : P}
    (hDeliver :
      ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [learner, value]⟩)) :
    ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]
      □ᶠ↓[[learner]](ofEvent ⟨voteSymb, [learner, value]⟩) := by
  obtain ⟨t, ht, hDeliver⟩ := sat_diamondPast_nil_iff.1 hDeliver
  exact lift_boxPast_to_end M (subset_of_happensBefore (happensBefore_of_mem ht))
    (theory_deliver_backward hTheory (M.time_le_of_mem ht) _ _ hDeliver) p

/-- `(≐⇓)`: a correlation that everyone holds at the end of time holds at every
event-tuple of the model. -/
theorem correlation_of_mem {l₁ l₂ : Signature.Value S}
    (hCorrelation : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩))
    {t : World P (Signature.EventType S)} (ht : t ∈ M.history.val) :
    ⟪t⟫ ⊨[M] ofPredicate ⟨correlationSymb, [l₁, l₂]⟩ :=
  (Sat.allPast ..).1
    (AllWorldValid.at_end M (theory_correlation_monotone hTheory) t.place l₁ l₂
      (EndValid.boxEmpty_guard M _ hCorrelation t.place))
    t ht rfl

/-- `(≐symm)` under `⇕`. -/
theorem everytime_correlation_symm {w : World P (Signature.EventType S)}
    {l₁ l₂ : Signature.Value S}
    (h : ⟪w⟫ ⊨[M] ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    ⟪w⟫ ⊨[M] ⇕ᶠ (ofPredicate ⟨correlationSymb, [l₂, l₁]⟩) :=
  (Sat.everytime ..).2 fun t ht hPlace =>
    theory_correlation_symm hTheory (M.time_le_of_mem ht) l₁ l₂
      ((Sat.everytime ..).1 h t ht hPlace)

/-! ### Lemmas 8.4.2 and 8.4.3: votes, echoes and agreement on the value -/

/-- Paper: Lemma 8.4.2(1). a realised vote yields an
`Echo` quorum for the same value. -/
theorem vote_implies_echo_quorum_local
    {t : World P (Signature.EventType S)}
    {learner value : Signature.Value S}
    (hMem : t ∈ M.history.val)
    (hVote : ⟪t⟫ ⊨[M]ofEvent ⟨voteSymb, [learner, value]⟩) :
    ∃ source : Signature.Value S,
      ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩) := by
  -- The paper's "simple inductive argument on time(w)": well-founded
  -- induction along `≺−`.
  induction hTime : t.time using PreHistory.happensBefore_wellFounded.induction
    generalizing t learner with
  | _ h IH =>
    have hPast : t.time ⊆ M.history.val :=
      subset_of_happensBefore (happensBefore_of_mem hMem)
    -- `(Vote?)` at `t`: an echo quorum, or a correlated vote in the past of `t`.
    rcases sat_or_cases (theory_vote_backward hTheory (M.time_le_of_mem hMem) _ _ hVote) with
      hEchoes | hCorrelatedVote
    · exact ⟨learner, lift_boxPast_to_end M hPast hEchoes⟩
    · obtain ⟨_, hCorrelatedVote⟩ := (Sat.exists_iff ..).1 hCorrelatedVote
      obtain ⟨s, hs, hVote'⟩ := sat_diamondPast_nil_iff.1 (sat_and_right hCorrelatedVote)
      exact IH s.time (hTime ▸ happensBefore_of_mem hs) (hPast _ hs) hVote' rfl

/-- Paper: Lemma 8.4.2(2). votes witnessed in the past
produce a global echo quorum. -/
theorem vote_implies_echo_quorum_end
    {learner value : Signature.Value S}
    (hVote : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [learner, value]⟩)) :
    ∃ source : Signature.Value S,
      ⊨[M]□ᶠ↓[[source]](ofEvent ⟨echoSymb, [value]⟩) :=
  let ⟨_, ht, hVote⟩ := endValid_diamondPast_nil_iff.1 hVote
  vote_implies_echo_quorum_local hTheory ht hVote

/-- Paper: Lemma 8.4.3(1). sequential echo quorums fix the
broadcast value. -/
theorem echo_quorums_agree
    {l l₁ l₂ : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq)
    (hEcho₁ : ⊨[M]□ᶠ↓[[l₁]](ofEvent ⟨echoSymb, [v₁]⟩))
    (hEcho₂ : ⊨[M]□ᶠ↓[[l₂]](ofEvent ⟨echoSymb, [v₂]⟩)) :
    v₁ = v₂ := by
  refine Classical.byContradiction fun hNe => ?_
  let p : P := Classical.ofNonempty
  -- Lemma 8.4.1 with `(3twined)`: some participant `q` is sequential and has
  -- seen an echo of `v₁` and an echo of `v₂`.
  obtain ⟨q, hq⟩ := (Sat.diamondEmpty ..).1
    (three_twined_boxes_intersect p
      (AllWorldValid.at_end M (theory_three_twined hTheory) p l l₁ l₂)
      ((Sat.and ..).2 ⟨(Sat.and ..).2 ⟨hSeq p, hEcho₁ p⟩, hEcho₂ p⟩))
  simp only [Sat.and] at hq
  obtain ⟨⟨hSeqAt, hEchoed₁⟩, hEchoed₂⟩ := hq
  -- By sequentiality one echo precedes the other; `(EchoNE)` at `q` equates
  -- their values.
  have hEchoNE {a b : Signature.Value S}
      (h : ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]
        ↓ᶠ (ofEvent ⟨echoSymb, [a]⟩ ∧ᶠ ↓ᶠ ofEvent ⟨echoSymb, [b]⟩)) : a = b :=
    echo_non_equiv_diamond (theory_echo_non_equiv hTheory) (transitiveSubset_refl _)
      (diamondPast_nil_of_past h)
  rcases sat_or_cases (seq_two_quorums_events hSeqAt hEchoed₁ hEchoed₂ (by simpa using hNe)) with
    h | h
  · exact hNe (hEchoNE h)
  · exact hNe (hEchoNE h).symm

/-- Paper: Lemma 8.4.3(2). past votes also determine a unique
value once sequentiality holds. -/
theorem votes_eventually_agree
    {l l₁ l₂ : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq)
    (hVote₁ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v₁]⟩))
    (hVote₂ : ⊨[M]♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₂, v₂]⟩)) :
    v₁ = v₂ := by
  -- Lemma 8.4.2(2) for each vote, then Lemma 8.4.3(1).
  obtain ⟨_, hEcho₁⟩ := vote_implies_echo_quorum_end hTheory hVote₁
  obtain ⟨_, hEcho₂⟩ := vote_implies_echo_quorum_end hTheory hVote₂
  exact echo_quorums_agree hTheory hSeq hEcho₁ hEcho₂

/-- Paper: Lemma 8.4.3(3). correlated live knowledge of a vote
forces eventual votes for the correlated learner. -/
theorem correlated_vote_eventually
    {l : Signature.Value S}
    {l₁ l₂ : Signature.Value S}
    {v : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq) :
    □W⊨[M]
      ((↕ᶠ ((predicate0 liveSymb ∧ᶠ
            ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩))) ⇒ᶠ
        ↕ᶠ (ofEvent ⟨voteSymb, [l₂, v]⟩)) := by
  intro t ht hKnows
  -- `(Vote'!)`, with `l₂ ≐ l₁` by `(≐symm)`: `l₂` votes for some value `v₂`.
  have hKnows' : ⟪t⟫ ⊨[M] ↕ᶠ ((predicate0 liveSymb ∧ᶠ
      ⇕ᶠ(ofPredicate ⟨correlationSymb, [l₂, l₁]⟩)) ∧ᶠ
        ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l₁, v]⟩)) :=
    sometime_mono (fun _ _ h => by
      simp only [Sat.and] at h ⊢
      exact ⟨⟨h.1.1, everytime_correlation_symm hTheory h.1.2⟩, h.2⟩) hKnows
  obtain ⟨v₂, hVote₂⟩ :=
    (Sat.exists_iff ..).1 (theory_vote_forward_correlated hTheory ht l₂ l₁ v hKnows')
  -- Lemma 8.4.3(2): `l₁` voted `v` and `l₂` voted `v₂`, so `v = v₂`.
  obtain ⟨s, hs, -, hKnowsAt⟩ := (Sat.sometime ..).1 hKnows
  obtain rfl := votes_eventually_agree hTheory hSeq
    (endValid_diamondPast_nil_of_mem hs (sat_and_right hKnowsAt))
    (endValid_diamondPast_nil_of_sometime hVote₂)
  exact hVote₂

/-- Paper: Lemma 8.4.3(4). a sometime-live echo quorum yields eventual
votes for the same learner. -/
theorem live_echo_eventually_vote
    {l : Signature.Value S}
    {v : Signature.Value S}
    (hSeq : ⊨[M]□ᶠ[[l]]Formula.seq) :
    □W⊨[M]
      ((↕ᶠ (predicate0 liveSymb ∧ᶠ
          □ᶠ↓[[l]](ofEvent ⟨echoSymb, [v]⟩))) ⇒ᶠ
        ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) := by
  intro t ht hKnows
  -- `(Vote!)`: `l` votes for some value `v₂`.
  obtain ⟨v₂, hVote₂⟩ :=
    (Sat.exists_iff ..).1 (theory_vote_forward hTheory ht l v hKnows)
  -- Lemma 8.4.2(2): that vote has an echo quorum for `v₂`; Lemma 8.4.3(1)
  -- against the echo quorum for `v` gives `v = v₂`.
  obtain ⟨_, hEcho₂⟩ :=
    vote_implies_echo_quorum_end hTheory (endValid_diamondPast_nil_of_sometime hVote₂)
  obtain ⟨s, hs, -, hKnowsAt⟩ := (Sat.sometime ..).1 hKnows
  obtain rfl := echo_quorums_agree hTheory hSeq
    (lift_boxPast_to_end M (subset_of_happensBefore (happensBefore_of_mem hs))
      (sat_and_right hKnowsAt))
    hEcho₂
  exact hVote₂

/-! ### Lemma 8.4.4: correlation and quorum intersection -/

/-- Paper: Lemma 8.4.4(1). If someone believes `l₁` correlates with `l₂`, then their quorums
intersect. This is the paper's Lemma 8.4.4(1), proved from the `(≐seq)`
axiom at the believing participant. -/
theorem correlation_implies_pairwise_quorum_intersection
    {l₁ l₂ : Signature.Value S}
    (hSomeone : ⊨[M]♢ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    ⊨[M]♢ᶠ[[l₁, l₂]] ⊤ᶠ := by
  intro p
  -- `(≐seq)` at a participant `q` who believes `l₁ ≐ l₂`; drop `seq` to `⊤`.
  obtain ⟨q, hq⟩ := (Sat.diamondEmpty ..).1 (hSomeone p)
  exact Sat.diamond_of_imp _ (fun _ _ => Sat.top _ _)
    (AllWorldValid.at_end M (theory_correlation_seq hTheory) q l₁ l₂ hq)

/-- Paper: Lemma 8.4.4(2). Universal correlation implies quorum intersection. This is the paper's
Lemma 8.4.4(2), derived from part 1 by weakening `□` to `♢`. -/
theorem correlation_implies_quorum_intersection
    {l₁ l₂ : Signature.Value S}
    (hEveryone : ⊨[M]□ᶠ[](ofPredicate ⟨correlationSymb, [l₁, l₂]⟩)) :
    ⊨[M]♢ᶠ[[l₁, l₂]] ⊤ᶠ :=
  correlation_implies_pairwise_quorum_intersection hTheory fun p =>
    (Sat.diamondEmpty ..).2 ⟨p, (Sat.boxEmpty ..).1 (hEveryone p) p⟩

end Theory

end HBBCorr
end Examples
end ModalDistribution
