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
    (hsource : ∀ p : P, l = s ∨ Corr M σ ⟨p, †, M.history.val⟩ l s)
    (hzero : ⊨[M] □ᶠ↓[[l]] (σ.live ∧ᶠ σ.vote l s v 0)) :
    ∀ n, n ≤ maxDepth M (Corr M σ) l + 1 →
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
    (hsource : ∀ p : P, l = s ∨ Corr M σ ⟨p, †, M.history.val⟩ l s)
    (hzero : ⊨[M] □ᶠ↓[[l]] (σ.live ∧ᶠ σ.vote l s v 0)) :
    ⊨[M] σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) := by
  have hlast := capped_round_progress h hlegal hsource hzero
    (maxDepth M (Corr M σ) l + 1) (Nat.le_refl _)
  have hknow := live_eventually_knows_box (M := M) (hTheory := h.thyLive) (hAllowed := .event _) (hQuorum := hlast)
  have hforward : □W⊨[M]
      (σ.live ∧ᶠ σ.fixedSourceCertificate l s v (maxDepth M (Corr M σ) l + 1)) ⇒ᶠ
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
      (ψ := ↕ᶠ (σ.fixedSourceCertificate l s v (maxDepth M (Corr M σ) l + 1)))
      (hknow p) hlive)

/-- A unique proposal known at a live event initializes the self-sourced round-zero quorum. -/
theorem live_zero_quorum_of_unique_proposal (h : BaseProtocol M σ) {l v : S.Value}
    (hlegal : ∀ p : P, Legal M σ ⟨p, †, M.history.val⟩ l v)
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live)
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u))
    (hEvent : ⊨[M] ♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) :
    ⊨[M] □ᶠ↓[[l]] (σ.live ∧ᶠ σ.vote l l v 0) := by
  have heback : □W⊨[M] HBB.echoBackwardAxiom σ.proposeSymb σ.echoSymb := by
    intro w hw
    apply Sat.forall_intro
    intro u
    apply Sat.imp_intro
    exact h.echoBackward hw
  have heforward : □W⊨[M] HBB.echoForwardAxiom σ.liveSymb σ.proposeSymb σ.echoSymb := by
    intro w hw
    apply Sat.forall_intro
    intro u
    apply Sat.imp_intro
    intro hboth
    obtain ⟨hlive, hprop⟩ := (Sat.and (M := M) (w := w) _ _).1 hboth
    exact (Sat.exists_iff (M := M) (w := w) _).mpr (h.echoForward hw hlive hprop)
  have heimp : □W⊨[M] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v)) ⇒ᶠ ↕ᶠ (σ.echo v) :=
    ThyHBB1.uniquePropose_eventually_echo (M := M)
    (value := v) (hEcho := heforward) (hEchoBack := heback) (hUnique := hUnique)
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
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u))
    (hKnown : ⊨[M] ♢ᶠ↓[[]] (σ.propose v)) :
    ∀ p : P, Legal M σ ⟨p, †, M.history.val⟩ l v := by
  intro p b u n _ hne hbad
  obtain ⟨e, he, hvote⟩ := past_exists_iff.mp hbad
  obtain ⟨s, hvote⟩ := voteFromSomeSource_iff.mp hvote
  have hp := vote_provenance h (predecessor_possible (PreHistory.happensBeforeEq_refl _) he) hvote
  obtain ⟨t, ht, hprop⟩ := past_exists_iff.mp hp
  have hknownu : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose u) :=
    past_exists_iff.mpr ⟨t, accessible_trans (PreHistory.happensBeforeEq_refl _) ht he, hprop⟩
  exact False.elim (hne (ThyHBB1.uniquePropose_equal_values u v
    (ThyHBB1.uniquePropose_guard_at_history (hUnique p)) hknownu (hKnown p)))

/-- Liveness 1: a uniquely proposed value known by a live participant is delivered sometime in the history. -/
theorem livenessOne (h : BaseProtocol M σ) {l v : S.Value}
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live)
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ⇒ᶠ
      σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) := by
  intro p
  apply Sat.imp_intro
  intro hante
  obtain ⟨e, he, hboth⟩ :=
    (past_exists_iff (φ := σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))).mp hante
  obtain ⟨hlive, hproposal⟩ := (Sat.and (M := M) (w := e) _ _).1 hboth
  have hEvent : ⊨[M] ♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v)) := by
    intro q
    apply past_exists_iff.mpr
    exact ⟨e, he, hboth⟩
  obtain ⟨t, ht, hprop⟩ := past_exists_iff.mp hproposal
  have hKnown : ⊨[M] ♢ᶠ↓[[]] (σ.propose v) := by
    intro q
    apply past_exists_iff.mpr
    exact ⟨t, accessible_trans (PreHistory.happensBeforeEq_refl _) ht he, hprop⟩
  have hlegal := legal_of_unique_proposal (l := l) h hUnique hKnown
  have hzero := live_zero_quorum_of_unique_proposal h hlegal hLiveQuorum hUnique hEvent
  exact deliver_of_live_zero_quorum h hlegal (fun _ => Or.inl rfl) hzero p

end ModalDistribution.Examples.ThyHBB4
