import ModalDistribution.Examples.HBB.Uniqueness
import ModalDistribution.Examples.HBBSafe.Axioms
import ModalDistribution.Examples.ThyLive
import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties
import ModalDistribution.Core.History

/-!
# HBBSafe safety lemmas

Lemmas about the `safe` predicate of `HBBSafe` and the `Vote!` rule it guards:

- **Safety of a learner** (Lemma 6.5.1): `safe_monotone` (`safe` persists along
  in-place accessibility) and `safe_allPast` (`safe` implies it always held in the
  past). Both rest on `safeFormula_of_subset`: each disjunct of `safeFormula` survives
  restriction to a smaller history.

- **Uniqueness implies safety** (Lemma 6.6.2): `at_most_one_propose_safe`

- **`Vote!` instantiations**: `vote_forward_imp_of_everytime` and `vote_forward_imp`
  package the axiom together with its safety guard for the liveness proofs

The theory-independent lemmas these build on live in `HBB.Liveness` and
`HBB.Uniqueness`.
-/

namespace ModalDistribution
namespace Examples
namespace HBBSafe

open HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature.{0, 0, 0}}

section Results

variable {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb safeSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}
variable {w w' : World P (Signature.EventType S)}

/-- A sequential quorum intersection `♢[ls] seq` persists to a smaller history:
sequentiality of a participant only constrains the event-tuples present. -/
theorem diamond_seq_of_subset {ls : List S.Value}
    (hSubset : w'.time ⊆ w.time)
    (h : ⟪w⟫ ⊨[M] ♢ᶠ[ls] Formula.seq) :
    ⟪w'⟫ ⊨[M] ♢ᶠ[ls] Formula.seq :=
  Sat.check_of_imp (fun _ hSeq t₁ t₂ h₁ h₂ => hSeq t₁ t₂ (hSubset _ h₁) (hSubset _ h₂)) h

/-- `safeFormula` persists to a transitive subset of the history: at most one proposal
in the larger history leaves at most one in the smaller, and sequential quorum
intersections stay sequential. -/
theorem safeFormula_of_subset {l : S.Value}
    (hSubset : w'.time ⊆trn w.time)
    (h : ⟪w⟫ ⊨[M] safeFormula proposeSymb l) :
    ⟪w'⟫ ⊨[M] safeFormula proposeSymb l := by
  rcases (Sat.or ..).1 h with hUnique | hSeq
  · exact sat_or_of_left (unique_propose_monotone hSubset hUnique)
  · exact sat_or_of_right fun l' => diamond_seq_of_subset hSubset.1 (hSeq l')

/-- The time of a world accessible from a world of the model is a transitive subset
of that world's time. -/
theorem time_subset_trn_of_accessible
    (hW : w.time ⪯ M.history.val) (hAcc : w' ≪ w) :
    w'.time ⊆trn w.time :=
  have hHered := (time_subset_trn_history M hW).2
  have hBefore := PreHistory.happensBefore_of_accessible hAcc
  ⟨hHered.trans _ hBefore, hHered.desc hBefore⟩

/-- Paper: Lemma 6.5.1(1). Safety of a learner is monotone along in-place accessibility: if
`safe(l)` holds at a world of the model, it holds at every same-place predecessor. -/
theorem safe_monotone
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    (l : Signature.Value S)
    {w w' : World P (Signature.EventType S)}
    (hW : w.time ⪯ M.history.val)
    (hAcc : w' ≪⁻ w)
    (hSafe : ⟪w⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩) :
    ⟪w'⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩ :=
  -- (Safe) at `w`, `safeFormula_of_subset`, and (Safe) at `w'`.
  have hW' : w'.time ⪯ M.history.val := Or.inl (accessible_happensBefore_history hW hAcc.1)
  (safe_iff_safeFormula hTheory w' hW' l).2 <|
    safeFormula_of_subset (time_subset_trn_of_accessible hW hAcc.1)
      ((safe_iff_safeFormula hTheory w hW l).1 hSafe)

/-- Paper: Lemma 6.5.1(2). Safety of a learner at an event-tuple of the model implies it held at
every past event at the same place. -/
theorem safe_allPast
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    (l : Signature.Value S)
    {w : World P (Signature.EventType S)}
    (hW : w.time ⪯ M.history.val)
    (hSafe : ⟪w⟫ ⊨[M] ofPredicate ⟨safeSymb, [l]⟩) :
    ⟪w⟫ ⊨[M]⇓ᶠ (ofPredicate ⟨safeSymb, [l]⟩) :=
  (Sat.allPast ..).2 fun _ ht hPlace => safe_monotone hTheory l hW ⟨ht, hPlace⟩ hSafe

/-- Paper: Lemma 6.6.2. If at most one value is proposed, then every learner is everywhere and
always safe. -/
theorem at_most_one_propose_safe
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    (l : Signature.Value S) :
    ⊨[M](∃≤ᶠ1 v ↦
        (♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
        ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩) := by
  intro p hUnique
  refine (Sat.everytime ..).2 fun s hs _ => ?_
  -- At every event-tuple `s` at most one value has been proposed, so the first
  -- disjunct of (Safe) holds there.
  have hs : s.time ⪯ M.history.val := M.time_le_of_mem hs
  exact (safe_iff_safeFormula hTheory s hs l).2 <|
    sat_or_of_left (unique_propose_monotone (w := ⟨p, †, _⟩) (time_subset_trn_history M hs) hUnique)

/-- The instantiated `Vote!` implication, taking the everywhere-always safety
guard in the form axiom `Vote!` demands it. -/
theorem vote_forward_imp_of_everytime
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l v : Signature.Value S}
    (hSafeAlways : □W⊨[M] ⇕ᶠ (ofPredicate ⟨safeSymb, [l]⟩)) :
    □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) :=
  fun ht => theory_vote_forward hTheory ht l v (hSafeAlways ht)

/-- The instantiated `Vote!` implication used by the liveness proofs: when a
learner is safe at the end of time, any live participant holding an echo
quorum eventually votes. Safety persists to every relevant past world by
`safe_monotone` (Lemma 6.5.1). -/
theorem vote_forward_imp
    (hTheory : M ⊨ᵀ
      theory liveSymb safeSymb proposeSymb echoSymb voteSymb deliverSymb)
    {l v : Signature.Value S}
    (hSafe : ⊨[M] ofPredicate ⟨safeSymb, [l]⟩) :
    □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ
        □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))) ⇒ᶠ
      ↕ᶠ (ofEvent ⟨voteSymb, [l, v]⟩)) :=
  vote_forward_imp_of_everytime hTheory fun {t} _ => (Sat.everytime ..).2 fun s hs hPlace =>
    -- Lemma 6.5.1(2) at the end-of-time world of `t.place` gives safety at
    -- every event of that place, which is exactly `⇕safe` at `t`.
    (Sat.allPast M ⟨t.place, †, M.history.val⟩ _).1
      (safe_allPast hTheory l (happensBeforeEq_refl _) (hSafe t.place)) s hs hPlace

end Results

end HBBSafe
end Examples
end ModalDistribution
