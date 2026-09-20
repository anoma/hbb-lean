import ModalDistribution.Examples.ThyHBB2.Agreement
import ModalDistribution.Examples.ThyHBB2.Liveness_One
import ModalDistribution.Examples.ThyHBB2.Liveness_Two

/-!
# Correctness properties for ThyHBB2

The paper's Theorem 7.1.3 collects the three correctness properties of
`ThyHBB2` (Figure 10): Agreement, Liveness 1, and Liveness 2. This file
bundles the corresponding Lean theorems into a single statement.
-/

namespace ModalDistribution
namespace Examples
namespace ThyHBB2

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb deliverSymb : Signature.EventSymb S}

/-- Paper: Theorem 7.1.3 / Figure 10. The correctness properties of `ThyHBB2`, collected: Agreement
(Proposition 7.2.1), Liveness 1 (Proposition 7.2.3), and Liveness 2
(Proposition 7.2.2). -/
theorem correctness
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    (∀ {l₁ l₂ reporting₁ reporting₂ : Signature.Value S}
    {v₁ v₂ : Signature.Value S}
    (_hSeq : ∀ Q ∈ (M.learner l₁).quorums,
      ∀ R ∈ (M.learner l₂).quorums,
        ∃ p ∈ Q ∩ R, isSequential (Event := S.EventType) p M.history.val)
    (_hDeliver₁ : Occurs M (ofEvent ⟨deliverSymb, [reporting₁, l₁, v₁]⟩))
    (_hDeliver₂ : Occurs M (ofEvent ⟨deliverSymb, [reporting₂, l₂, v₂]⟩)),
    v₁ = v₂) ∧
    (∀ {l : Signature.Value S}
    {v : Signature.Value S}
    (_hLiveQuorum : ∃ Q ∈ (M.learner l).quorums,
      ∀ q ∈ Q, ⟪finalWorld M q⟫ ⊨[M] predicate0 liveSymb)
    (_hUnique : UniqueOccurrence M (fun value => ofEvent ⟨proposeSymb, [value]⟩))
    (_hKnownProposal : ∃ e ∈ M.history.val,
      (⟪e⟫ ⊨[M] predicate0 liveSymb) ∧
        ObservedAt M e (ofEvent ⟨proposeSymb, [v]⟩))
    (p : P) (_hLiveParticipant : ⟪finalWorld M p⟫ ⊨[M] predicate0 liveSymb),
    OccursAt M p (ofEvent ⟨deliverSymb, [l, l, v]⟩)) ∧
    (∀ {reporting₁ reporting₂ ℓ : Signature.Value S}
    {v : Signature.Value S}
    (_hIntersect : ∀ Q ∈ (M.learner reporting₁).quorums,
      ∀ R ∈ (M.learner reporting₂).quorums, ∃ q, q ∈ Q ∧ q ∈ R)
    (_hLive : ∃ Q ∈ (M.learner reporting₂).quorums,
      ∀ q ∈ Q, ⟪finalWorld M q⟫ ⊨[M] predicate0 liveSymb)
    (_hDelivered : Occurs M (ofEvent ⟨deliverSymb, [reporting₁, ℓ, v]⟩))
    (p : P) (_hLiveParticipant : ⟪finalWorld M p⟫ ⊨[M] predicate0 liveSymb),
    OccursAt M p (ofEvent ⟨deliverSymb, [reporting₂, ℓ, v]⟩)) := by
  exact ⟨fun hSeq hFirst hSecond => agreement hTheory hSeq hFirst hSecond,
    fun hQuorum hUnique hKnown p hLive => livenessOne hTheory hQuorum hUnique hKnown p hLive,
    fun hIntersect hQuorum hDelivered p hLive =>
      livenessTwo hTheory hIntersect hQuorum hDelivered p hLive⟩

/-- The paper-facing modal correctness summary. -/
theorem correctness_modal
    (hTheory : M ⊨ᵀ
      theory liveSymb proposeSymb echoSymb voteSymb deliverSymb) :
    -- Agreement
    (∀ {l₁ l₂ reporting₁ reporting₂ v₁ v₂ : Signature.Value S},
      (⊨[M]♢ᶠ[[l₁, l₂]]Formula.seq) →
      ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₁, l₁, v₁]⟩)) ⇒ᶠ
           (♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₂, l₂, v₂]⟩)) ⇒ᶠ
           (v₁ ≃ᶠ v₂)) ∧
    -- Liveness 1
    (∀ {l v : Signature.Value S},
      (⊨[M]□ᶠ[[l]]predicate0 liveSymb) →
      (⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩)) →
      ⊨[M](♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ
              ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
           predicate0 liveSymb ⇒ᶠ
           ↕ᶠ(ofEvent ⟨deliverSymb, [l, l, v]⟩)) ∧
    -- Liveness 2
    (∀ {reporting₁ reporting₂ l v : Signature.Value S},
      (⊨[M]♢ᶠ[[reporting₁, reporting₂]]⊤ᶠ) →
      (⊨[M]□ᶠ[[reporting₂]]predicate0 liveSymb) →
      ⊨[M](♢ᶠ↓[[]](ofEvent ⟨deliverSymb, [reporting₁, l, v]⟩)) ⇒ᶠ
           predicate0 liveSymb ⇒ᶠ
           ↕ᶠ(ofEvent ⟨deliverSymb, [reporting₂, l, v]⟩)) :=
  ⟨fun hSeq =>
      agreement_modal (M := M) (hTheory := hTheory) (hSeq := hSeq),
   fun hLiveQuorum hUnique =>
      livenessOne_modal (M := M) (hTheory := hTheory)
        (hLiveQuorum := hLiveQuorum) (hUnique := hUnique),
   fun hIntersect hLive =>
      livenessTwo_modal (M := M) (hTheory := hTheory)
        (hIntersect := hIntersect) (hLive := hLive)⟩


end ThyHBB2
end Examples
end ModalDistribution
