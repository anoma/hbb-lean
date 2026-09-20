import ModalDistribution.Examples.ThyHBB4.Semantics
import ModalDistribution.Examples.ThyHBB4.Safety
import ModalDistribution.Examples.ThyHBB1.Safety
import ModalDistribution.Examples.ThyHBB1.Uniqueness

namespace ModalDistribution.Examples.ThyHBB4

open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

/-- Atomic-vote Knowledge suffices to advance every admitted round. -/
theorem capped_round_progress (h : BaseProtocol M σ) {l s v : S.Value}
    (hlegal : ∀ p : P, Legal M σ ⟨p, †, M.history.val⟩ l v)
    (hsource : ∀ p : P, l = s ∨ Correlated M σ.correlationSymb ⟨p, †, M.history.val⟩ l s)
    (hzero : ⊨[M] □ᶠ↓[[l]] (σ.live ∧ᶠ σ.vote l s v 0)) :
    ∀ n, n ≤ maxDepth M (Correlated M σ.correlationSymb) l + 1 →
      ⊨[M] □ᶠ↓[[l]] (σ.live ∧ᶠ σ.vote l s v n) := by
  intro n
  induction n with
  | zero => intro _; exact hzero
  | succ n ih =>
    intro hn
    have hp := ih (by omega)
    apply ThyHBB1.boxPast_live_of_eventual_quorum h.thyLive
      (σ.fixedSourceCertificate l s v n) (σ.vote l s v (n + 1)) l
      (live_boxPast_nests (M := M) (hTheory := h.thyLive) (hAllowed := .event _) (hQuorum := hp))
    intro w hw
    apply Sat.imp_intro
    intro hboth
    obtain ⟨hlive, hcert⟩ := (Sat.and (M := M) (w := w) _ _).1 hboth
    exact h.voteSuccForward hw hn hlive (hlegal w.place) (hsource w.place) hcert

/-- Once rank zero is established, capped progress reaches delivery. -/
theorem deliver_of_live_zero_quorum (h : BaseProtocol M σ) {l s v : S.Value}
    (hlegal : ∀ p : P, Legal M σ ⟨p, †, M.history.val⟩ l v)
    (hsource : ∀ p : P, l = s ∨ Correlated M σ.correlationSymb ⟨p, †, M.history.val⟩ l s)
    (hzero : ⊨[M] □ᶠ↓[[l]] (σ.live ∧ᶠ σ.vote l s v 0)) :
    ⊨[M] σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) := by
  have hlast := capped_round_progress h hlegal hsource hzero
    (maxDepth M (Correlated M σ.correlationSymb) l + 1) (Nat.le_refl _)
  have hknow := live_eventually_knows_box (M := M) (hTheory := h.thyLive) (hAllowed := .event _) (hQuorum := hlast)
  have hforward : □W⊨[M]
      (σ.live ∧ᶠ σ.fixedSourceCertificate l s v (maxDepth M (Correlated M σ.correlationSymb) l + 1)) ⇒ᶠ
        ↕ᶠ (σ.deliver l v) := by
    intro w hw
    apply Sat.imp_intro
    intro hboth
    obtain ⟨hlive, hcert⟩ := (Sat.and (M := M) (w := w) _ _).1 hboth
    exact h.deliverForward hw hlive (fixedSourceCertificate_to_voteCertificate hcert)
  intro p
  apply Sat.imp_intro
  intro hlive
  exact ThyHBB1.live_sometime_consequent_at h.thyLive hforward hlive
    (Sat.imp_elim (M := M) (w := ⟨p, †, M.history.val⟩) (φ := σ.live)
      (ψ := ↕ᶠ (σ.fixedSourceCertificate l s v (maxDepth M (Correlated M σ.correlationSymb) l + 1)))
      (hknow p) hlive)

/-- A unique proposal known at a live event initializes the self-sourced round-zero quorum. -/
theorem live_zero_quorum_of_unique_proposal (h : BaseProtocol M σ) {l v : S.Value}
    (hlegal : ∀ p : P, Legal M σ ⟨p, †, M.history.val⟩ l v)
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live)
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u))
    (hEvent : ⊨[M] ♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) :
    ⊨[M] □ᶠ↓[[l]] (σ.live ∧ᶠ σ.vote l l v 0) := by
  have heimp : □W⊨[M] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v)) ⇒ᶠ ↕ᶠ (σ.echo v) := by
    intro w hw
    apply Sat.imp_intro
    intro hboth
    obtain ⟨hlive, hproposal⟩ := (Sat.and ..).mp hboth
    apply occursAt_iff.mp
    exact HBB.echo_of_unique_proposal
      (fun w hw u hl hp => by
        obtain ⟨x, hx⟩ := h.echoForward hw hl (observedAt_iff.mp hp)
        exact ⟨x, occursAt_iff.mpr hx⟩)
      (fun e he u hu => observedAt_iff.mpr (h.echoBackward (M.time_le_of_mem he) hu))
      ((uniqueOccurrence_iff_end σ.propose).mpr hUnique) hw hlive
      (observedAt_iff.mpr hproposal)
  have hprop := live_eventually_knows_event (M := M) (hTheory := h.thyLive)
    (hLive := hLiveQuorum) (hEvent := hEvent)
  have hequorum := ThyHBB1.boxPast_live_of_eventual_quorum h.thyLive
    (♢ᶠ↓[[]] (σ.propose v)) (σ.echo v) l hprop heimp
  apply ThyHBB1.boxPast_live_of_eventual_quorum h.thyLive
    (σ.echoCertificate l v) (σ.vote l l v 0) l
    (live_boxPast_nests (M := M) (hTheory := h.thyLive)
      (hAllowed := .event _) (hQuorum := hequorum))
  intro w hw
  apply Sat.imp_intro
  intro hboth
  obtain ⟨hlive, hcert⟩ := (Sat.and (M := M) (w := w) _ _).1 hboth
  exact h.voteZeroEchoForward hw hlive (hlegal w.place) hcert

/-- Provenance makes every competing vote incompatible with the unique proposal. -/
theorem legal_of_unique_proposal (h : BaseProtocol M σ) {l v : S.Value}
    (hUnique : UniqueOccurrence M σ.propose)
    (hKnown : Occurs M (σ.propose v)) :
    ∀ p, Legal M σ (finalWorld M p) l v := by
  obtain ⟨value, _, hOnly⟩ := hUnique
  intro p b u n _ hne hbad
  obtain ⟨e, he, hvote⟩ := hbad
  obtain ⟨source, hvote⟩ := voteFromSomeSource_iff.mp hvote
  obtain ⟨t, ht, hprop⟩ := vote_provenance h (M.time_le_of_mem he) hvote
  have hOther : Occurs M (σ.propose u) :=
    ⟨t, History.subset_of_happensBefore (H := M.history) ⟨e.place, e.event, he⟩ t ht, hprop⟩
  exact False.elim (hne ((hOnly u hOther).trans (hOnly v hKnown).symm))

/-- Liveness 1: a uniquely proposed value known by a live participant is delivered sometime in the history. -/
theorem livenessOne (h : BaseProtocol M σ) {l v : S.Value}
    (hLiveQuorum : ∃ Q ∈ (M.learner l).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hUnique : UniqueOccurrence M σ.propose)
    (hObserved : ∃ e ∈ M.history.val,
      (⟪e⟫ ⊨[M] σ.live) ∧ ObservedAt M e (σ.propose v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver l v) := by
  obtain ⟨e, he, hlive, hproposal⟩ := hObserved
  have hEvent : ⊨[M] ♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v)) :=
    occurs_iff_end_diamondPast.mp ⟨e, he,
      Sat.and_intro M e hlive (observedAt_iff.mp hproposal)⟩
  obtain ⟨t, ht, hprop⟩ := hproposal
  have hKnown : Occurs M (σ.propose v) :=
      ⟨t, History.subset_of_happensBefore (H := M.history) ⟨e.place, e.event, he⟩ t ht, hprop⟩
  have hlegal := legal_of_unique_proposal (l := l) h hUnique hKnown
  have hzero := live_zero_quorum_of_unique_proposal h hlegal
    (quorum_final_iff_end.mp hLiveQuorum)
    (uniqueOccurrence_iff_end σ.propose |>.mp hUnique) hEvent
  apply (occursAt_iff (w := finalWorld M p)).mpr
  exact Sat.imp_elim (M := M) (w := finalWorld M p) (deliver_of_live_zero_quorum h hlegal (fun _ => Or.inl rfl) hzero p) hLive

/-- The paper formulation, derived from the semantic correctness theorem. -/
theorem livenessOne_modal (h : BaseProtocol M σ) {l v : S.Value}
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live)
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ⇒ᶠ
      σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) := by
  apply occurrence_liveness_iff.mp
  rintro ⟨e, he, hboth⟩ p hlive
  obtain ⟨hl, hp⟩ := (Sat.and ..).mp hboth
  exact livenessOne h (quorum_final_iff_end.mpr hLiveQuorum)
    ((uniqueOccurrence_iff_end σ.propose).mpr hUnique)
    ⟨e, he, hl, observedAt_iff.mpr hp⟩ p hlive

end ModalDistribution.Examples.ThyHBB4
