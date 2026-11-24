import ModalDistribution.Examples.HBB.Liveness
import ModalDistribution.Examples.HBB.Uniqueness
import ModalDistribution.Logic.Properties.Modalities

/-!
# Shared steps of the termination proofs

The Happy and Cascade Termination proofs of `HBBSafe`, `HBBSimp`, and `HBBCorr`
(Propositions 6.5.5, 6.6.3, 7.3.2, 7.3.3, 8.4.5, and 8.5.1) share most of their
steps; each theory differs only in its vote rules. The shared steps are proved
here once, with each theory's vote rule taken as a hypothesis where a step
needs it.

- `unique_propose_live_nested_echo_quorum`: the Happy Termination steps from a
  live participant knowing a unique proposal to a live quorum knowing of an
  echo quorum (Lemma 6.6.1, Proposition 5.2.8, (Echo?) with Lemma 4.2.2,
  Lemma 6.5.2(2), and Lemma 5.2.11)
- `boxPast_live_knows_of_intersecting`: the Cascade Termination steps from a
  quorum of events to a live quorum knowing of one of them (Propositions 5.2.10
  and 5.2.8)
- `boxPast_live_knows_vote_knows_echo_quorum`: (Vote?) with Lemma 4.2.3(1), given
  the theory's (Vote?) instance
- `live_quorum_eventually_consequent`: Lemma 6.5.3 applied to (Knowledge□↓),
  the last step of every termination proof
-/

namespace ModalDistribution
namespace Examples
namespace HBB

open ModalDistribution
open ModalDistribution.Logic
open ModalDistribution.Logic.Formula
open History
open PreHistory
open World
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

section Results

variable {P : Type} [Nonempty P]
variable {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {proposeSymb echoSymb voteSymb : Signature.EventSymb S}

/-- The Happy Termination steps shared by the three theories: if some live
participant knows of a proposal of `v`, the proposal is unique, and learner `l`
has a live quorum, then a live `l`-quorum knows of an `l`-quorum of echoes of
`v`. Lemma 6.6.1 gives a live echo of `v`; Proposition 5.2.8 makes a live
`l`-quorum know of it; (Echo?) with Lemma 4.2.2 makes that quorum know of the
proposal; Lemma 6.5.2(2) with Lemma 6.6.1 makes it echo `v`; Lemma 5.2.11 nests
the echo quorum. -/
theorem unique_propose_live_nested_echo_quorum
    (hLiveTheory : M ⊨ᵀ thyLive liveSymb)
    (hEcho : □W⊨[M]echoForwardAxiom liveSymb proposeSymb echoSymb)
    (hEchoBack : □W⊨[M]echoBackwardAxiom proposeSymb echoSymb)
    {l v : Signature.Value S}
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]predicate0 liveSymb)
    (hUnique : ⊨[M]∃!ᶠ w ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [w]⟩))
    (hKnown :
      ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) :
    ⊨[M]□ᶠ↓[[l]](predicate0 liveSymb ∧ᶠ □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) := by
  classical
  -- Lemma 6.6.1: live knowledge of the proposal eventually yields an echo of it.
  have hImpEcho :
      □W⊨[M]
        ((↕ᶠ (predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))) ⇒ᶠ
          ↕ᶠ (ofEvent ⟨echoSymb, [v]⟩)) :=
    unique_propose_eventually_echo (M := M) (value := v)
      (hEcho := hEcho) (hEchoBack := hEchoBack) (hUnique := hUnique)
  -- Some live participant echoes `v`.
  have hLiveEcho :
      ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ ofEvent ⟨echoSymb, [v]⟩) :=
    diamondPast_live_of_eventual (M := M)
      (hLiveTheory := hLiveTheory)
      (φ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
      (ψ := ofEvent ⟨echoSymb, [v]⟩)
      (hDiamond := hKnown) (hImp := hImpEcho)
  -- Proposition 5.2.8: a live `l`-quorum knows of that echo.
  have hKnowsEcho :
      ⊨[M]□ᶠ↓[[l]]
        (predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨echoSymb, [v]⟩)) := by
    intro q
    simpa using
      live_eventually_knows (P := P) (M := M) (liveSymb := liveSymb)
        (l := l) (evt := ⟨echoSymb, [v]⟩)
        (hTheory := hLiveTheory) (hLive := by simpa using hLiveQuorum)
        (hEvent := hLiveEcho) q
  -- (Echo?) and Lemma 4.2.2: that quorum knows of the proposal.
  have hKnowsPropose :
      ⊨[M]□ᶠ↓[[l]]
        (predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :=
    boxPast_live_knows_echo_knows_propose (M := M)
      (hEchoBack := hEchoBack) (hQuorum := hKnowsEcho)
  -- Lemma 6.5.2(2) and Lemma 6.6.1: that quorum echoes `v`.
  have hEchoQuorum :
      ⊨[M]□ᶠ↓[[l]](predicate0 liveSymb ∧ᶠ ofEvent ⟨echoSymb, [v]⟩) :=
    boxPast_live_of_eventual_quorum (M := M)
      (hLiveTheory := hLiveTheory)
      (φ := ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
      (ψ := ofEvent ⟨echoSymb, [v]⟩)
      (l := l) (hQuorum := hKnowsPropose) (hImp := hImpEcho)
  -- Lemma 5.2.11: the quorum knows of an `l`-quorum of echoes.
  exact
    live_boxPast_nests (M := M) (liveSymb := liveSymb)
      (l := l) (evt := ⟨echoSymb, [v]⟩)
      (hTheory := hLiveTheory) (hQuorum := hEchoQuorum)

/-- The Cascade Termination steps shared by the three theories: an
`l₁`-quorum of `evt` events, intersecting `l₁`- and `l₂`-quorums, and a live
`l₂`-quorum give a live `l₂`-quorum that knows of `evt`. Proposition 5.2.10
exposes a live participant with `evt`; Proposition 5.2.8 spreads the knowledge
of it. -/
theorem boxPast_live_knows_of_intersecting
    (hLiveTheory : M ⊨ᵀ thyLive liveSymb)
    {l₁ l₂ : Signature.Value S} {evt : Signature.EventType S}
    (hIntersect : ⊨[M]♢ᶠ[[l₁, l₂]]⊤ᶠ)
    (hLive : ⊨[M]□ᶠ[[l₂]]predicate0 liveSymb)
    (hQuorum : ⊨[M]□ᶠ↓[[l₁]](ofEvent evt)) :
    ⊨[M]□ᶠ↓[[l₂]](predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent evt)) := by
  classical
  -- Proposition 5.2.10: the intersecting live quorum exposes a live witness.
  have hLiveEvent :
      ⊨[M]♢ᶠ↓[[]](predicate0 liveSymb ∧ᶠ ofEvent evt) := by
    intro q
    simpa using
      intertwined_two_quorums (P := P) (M := M)
        (liveSymb := liveSymb) (l := l₁) (l₁ := l₂)
        (φ := ofEvent evt)
        (hTheory := hLiveTheory)
        (hIntersect := by intro r; simpa using hIntersect r)
        (hLiveQuorum := by intro r; simpa using hLive r)
        (hWitness := by intro r; simpa using hQuorum r) q
  -- Proposition 5.2.8: the live `l₂`-quorum eventually knows of it.
  intro q
  simpa using
    live_eventually_knows (P := P) (M := M) (liveSymb := liveSymb)
      (l := l₂) (evt := evt)
      (hTheory := hLiveTheory)
      (hLive := by intro r; simpa using hLive r)
      (hEvent := hLiveEvent) q

/-- (Vote?) with Lemma 4.2.3(1): if a live `l'`-quorum knows of a vote of
learner `l` for `v`, it knows of an `l`-quorum of echoes of `v`. The theory's
(Vote?) rule enters as `hVoteEcho`: at every vote event-tuple of the model, an
`l`-quorum has echoed `v`. -/
theorem boxPast_live_knows_vote_knows_echo_quorum
    {l l' v : Signature.Value S}
    (hVoteEcho :
      ∀ t ∈ M.history.val,
        (⟪t⟫ ⊨[M] ofEvent ⟨voteSymb, [l, v]⟩) →
          ⟪t⟫ ⊨[M] □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
    (hQuorum :
      ⊨[M]□ᶠ↓[[l']]
        (predicate0 liveSymb ∧ᶠ ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l, v]⟩))) :
    ⊨[M]□ᶠ↓[[l']]
      (predicate0 liveSymb ∧ᶠ □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) := by
  classical
  refine boxPast_mono_of_history (M := M) (fun t ht hConj => ?_) hQuorum
  have hSplit :=
    (Sat.and (M := M) (w := t) (φ := predicate0 liveSymb)
      (ψ := ♢ᶠ↓[[]](ofEvent ⟨voteSymb, [l, v]⟩))).1 hConj
  obtain ⟨q, hPastVote⟩ :=
    (Sat.diamond_nil (M := M) (w := t)
      (φ := ↓ᶠ (ofEvent ⟨voteSymb, [l, v]⟩))).1
      (by simpa [Formula.diamondPast] using hSplit.2)
  -- (Vote?) at the vote event-tuple.
  have hPastEcho :=
    Sat.past_of_imp (M := M) (w := ⟨q, †, t.time⟩)
      (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))
      (fun t' _ _ hVote =>
        hVoteEcho t' (Sat.mem_of_ofEvent (M := M) hVote) hVote)
      hPastVote
  have hKnowsEcho :
      ⟪t⟫ ⊨[M] ♢ᶠ↓[[]] (□ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)) := by
    simpa [Formula.diamondPast] using
      (Sat.diamond_nil (M := M) (w := t)
        (φ := ↓ᶠ (□ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩)))).2 ⟨q, hPastEcho⟩
  -- Lemma 4.2.3(1) collapses the known past quorum to a present one.
  exact
    (Sat.and (M := M) (w := t) (φ := predicate0 liveSymb)
      (ψ := □ᶠ↓[[l]] (ofEvent ⟨echoSymb, [v]⟩))).2
      ⟨hSplit.1,
        past_diamond_box_collapses_to_present_box (M := M) t l _ ht hKnowsEcho⟩

/-- Lemma 6.5.3 applied to (Knowledge□↓): if a live `l`-quorum has `evt`
events and `↕(live ∧ ■_l evt) ⇒ ↕ψ` is valid, every live participant
eventually has `ψ`. With the theory's (Deliver!) implication for `ψ` this is the
last step of every termination proof. -/
theorem live_quorum_eventually_consequent
    (hLiveTheory : M ⊨ᵀ thyLive liveSymb)
    {l : Signature.Value S} {evt : Signature.EventType S} {ψ : Formula S}
    (hQuorum : ⊨[M]□ᶠ↓[[l]](predicate0 liveSymb ∧ᶠ ofEvent evt))
    (hImp :
      □W⊨[M]((↕ᶠ (predicate0 liveSymb ∧ᶠ □ᶠ↓[[l]] (ofEvent evt))) ⇒ᶠ ↕ᶠψ)) :
    ⊨[M](predicate0 liveSymb ⇒ᶠ ↕ᶠψ) :=
  live_eventually_consequent (M := M)
    (hLiveTheory := hLiveTheory)
    (φ := □ᶠ↓[[l]] (ofEvent evt)) (ψ := ψ)
    (hLive :=
      live_eventually_knows_box (M := M) (liveSymb := liveSymb)
        (l := l) (evt := evt)
        (hTheory := hLiveTheory) (hQuorum := hQuorum))
    (hImp := hImp)

end Results

end HBB
end Examples
end ModalDistribution
