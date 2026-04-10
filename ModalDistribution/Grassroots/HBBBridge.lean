import ModalDistribution.Grassroots.Abstract
import ModalDistribution.Grassroots.Coalescent

/-!
# HBB-flavoured DTS bridge: a positive obliviousness result

This file builds the bridge between the abstract grassroots framework
(`Grassroots/Abstract.lean`) and the existing HBB modal-logic infrastructure
(`Grassroots/Coalescent.lean`). It provides a concrete *positive* result:
an HBB-style distributed multiagent transition system whose step relation
includes the *existential-over-quorums* constraint that mirrors ThyHBB1's
`voteBackwardAxiom` IS `IsOblivious` under any coalescent learner family.

## The corrected story

Earlier working notes contained a "Conjecture C" claiming that ThyHBB1
fails obliviousness because of the `□ᶠ↓` modality in `voteBackwardAxiom`.
That claim was based on a misreading of Murdoch–Sheff's `□`: I assumed
the standard modal box ("∀ accessible world"), which would have been the
universal-over-quorums-and-members shape `∀ quorum, ∀ member`. But
**Murdoch–Sheff's `□` is actually existential-over-quorums**:

```
□[ℓ] φ  ≡  ∃ ℓ-quorum O, ∀ p ∈ O, φ at p
```

This is confirmed by `Logic/Properties/Modalities.lean:357`'s lemma
`sat_box_singleton_exists`, whose docstring reads "*Singleton learner
boxes exhibit a quorum whose members satisfy the guard*", and by every
single use site in `Examples/ThyHBB1/{Safety,Liveness_One,Liveness_Two}.lean`
following the pattern `obtain ⟨O, hO, hAll⟩ := (sat_box_singleton_exists ...).1`.

The existential-over-quorums shape is **lift-friendly under coalescence**:
the witness quorum at the small universe lifts via `IsCoalescent.lift_quorum`
to a witness quorum at the large universe, and lifting preserves all the
events at the original agents. This is what we prove in this file.

## What we formalise

We do NOT literally embed `Examples/ThyHBB1` into the abstract DTS
framework — that would require choosing how to express HBB models
(with their histories, predicate interpretations, and learner families)
as `Abstract.Config` values, which is a substantial design choice and
arguably should wait until the formal correspondence between modal-logic
satisfaction and operational steps is more fleshed out. Instead, we
construct an **HBB-flavoured** DTS that captures the structural pattern
of `voteBackwardAxiom`:

- Agents perform `BroadcastEvent`s (echo a value, vote a value).
- A `vote v` event is only valid if there *exists* a learner-quorum
  whose members have all already echoed `v`.
- This is the existential-over-quorums shape of `□ᶠ↓[[ℓ]] echo(v)`.

The main theorem `broadcastDTS_oblivious` shows: under any coalescent
learner family, this DTS is `IsOblivious`. The proof reuses
`IsCoalescent.lift_quorum` to transport the witness quorum from the
small universe to the large one.

## Main definitions

* `BroadcastEvent V` — events: echo a value, or vote a value.
* `BroadcastState V` — local state = event log.
* `broadcastStep F l P` — step relation parameterised by a learner
  family `F` and the chosen learner `l`.
* `broadcastDTS F l` — the packaged DTS.

## Main theorem

* `broadcastDTS_oblivious` — the HBB-flavoured DTS is `Abstract.IsOblivious`
  under any coalescent learner family. This is the **positive corrected
  Conjecture C′** from the working notes.

## Helper

* `liftConfig_apply_lift` — applying a lifted configuration at a lifted
  agent recovers the original. The `Sequentiality.liftAgent` analogue of
  `Abstract.liftConfig_inP` (which is stated in terms of `Abstract.embed`,
  the same function under a different name).
-/

namespace ModalDistribution
namespace Grassroots
namespace HBBBridge

universe u v

variable {A : Type u} {V : Type v}

/-! ## §1. Broadcast events -/

/-- The minimal event vocabulary needed to encode the structural pattern
of `voteBackwardAxiom`: an agent can echo a value or vote a value. -/
inductive BroadcastEvent (V : Type v) where
  | echo (v : V)
  | vote (v : V)

/-- An agent's local state is its event log. -/
abbrev BroadcastState (V : Type v) := List (BroadcastEvent V)

/-! ## §2. The HBB-flavoured DTS step relation -/

/-- A step at participant set `P` is: pick an agent `p ∈ P`, append a new
event to their event log. The validity constraint is that *if* the new
event is `vote v` for some value `v`, then there must exist a learner-quorum
at `P` (via `F` at `l`) all of whose members have already echoed `v` in
their local state.

This is the existential-over-quorums shape that `□ᶠ↓[[ℓ]] echo(v)` reduces
to via `sat_box_singleton_exists`. -/
noncomputable def broadcastStep
    (F : LearnerFamily V A) (l : V) (P : Set A)
    (c c' : Abstract.Config P (BroadcastState V)) : Prop :=
  ∃ (hNE : Nonempty ↥P) (p : ↥P) (e : BroadcastEvent V),
    c' p = e :: c p ∧
    (∀ q : ↥P, q ≠ p → c' q = c q) ∧
    (∀ v, e = BroadcastEvent.vote v →
      ∃ O ∈ (@LearnerFamily.σ V A F P hNE l).quorums,
        ∀ q ∈ O, BroadcastEvent.echo v ∈ c q)

/-- The HBB-flavoured DTS, parameterised by a learner family and a chosen
learner. The initial local state is the empty event log. -/
noncomputable def broadcastDTS
    (F : LearnerFamily V A) (l : V) :
    Abstract.DTS A (BroadcastState V) where
  initial := []
  step := broadcastStep F l

/-! ## §3. Helper: applying the lifted configuration to a lifted agent

`Abstract.liftConfig_inP` is stated in terms of `Abstract.embed`, which
is definitionally identical to `Sequentiality.liftAgent` (and to
`Coalescent.liftQuorumSet`'s underlying agent map) but lives in a
different namespace. To stay consistent with the `Coalescent` infrastructure
we use `liftAgent` throughout this file, and provide a small bridge
lemma. -/

lemma liftConfig_apply_lift {V : Type v} {P P' : Set A} (h : P ⊆ P')
    (init : BroadcastState V)
    (c : Abstract.Config P (BroadcastState V))
    (a : ↥P) :
    Abstract.liftConfig h init c (liftAgent h a) = c a := by
  classical
  unfold Abstract.liftConfig liftAgent
  simp only [dif_pos a.property]

/-! ## §4. Obliviousness — the positive concrete result

The structural pattern of ThyHBB1's `voteBackwardAxiom` is preserved by
lifting under coalescence. This is the corrected Conjecture C′ — the
*positive* result that the original Conjecture C should have been. -/

/-- **The HBB-flavoured DTS is oblivious** under any coalescent learner
family. The proof exhibits the lifted vote witness quorum via
`IsCoalescent.lift_quorum`, which is what the existential-over-quorums
semantics of `□ᶠ↓` makes possible. -/
theorem broadcastDTS_oblivious
    (F : LearnerFamily V A) [IsCoalescent F] (l : V) :
    Abstract.IsOblivious (broadcastDTS F l) := by
  intro P P' h c c' hStep
  -- Extract the small-universe step's data.
  obtain ⟨hNE, p, e, hpEq, hOther, hVoteValid⟩ := hStep
  -- Promote `hNE` to an instance for `(F.σ P l).quorums` resolution.
  haveI := hNE
  -- Construct a `Nonempty ↥P'` instance from the lifted `p`.
  haveI hNE' : Nonempty ↥P' := ⟨liftAgent h p⟩
  -- Provide the witness for the lifted step.
  refine ⟨hNE', liftAgent h p, e, ?_, ?_, ?_⟩
  · -- Lifted c' at lifted p equals e :: lifted c at lifted p.
    rw [liftConfig_apply_lift, liftConfig_apply_lift]
    exact hpEq
  · -- Other lifted agents are unchanged.
    intro q' hq'ne
    by_cases hq'P : q'.val ∈ P
    · -- q' is the lift of some `q : ↥P`, with q ≠ p.
      have hq'eq : q' = liftAgent h ⟨q'.val, hq'P⟩ := by
        rcases q' with ⟨v, hv⟩
        rfl
      have hqne : (⟨q'.val, hq'P⟩ : ↥P) ≠ p := by
        intro heq
        apply hq'ne
        rw [hq'eq, heq]
      rw [hq'eq, liftConfig_apply_lift, liftConfig_apply_lift]
      exact hOther _ hqne
    · -- q'.val ∉ P, so both lifted configurations equal `initial = []`.
      rw [Abstract.liftConfig_outP h _ c' q' hq'P,
          Abstract.liftConfig_outP h _ c q' hq'P]
  · -- Vote validity at the lifted level: lift the witness quorum.
    intro v hev
    obtain ⟨O, hO_quor, hO_echoed⟩ := hVoteValid v hev
    refine ⟨liftQuorumSet h O,
            IsCoalescent.lift_quorum (F := F) h l hO_quor, ?_⟩
    intro q' hq'_in
    -- q' ∈ liftQuorumSet h O = liftAgent h '' O
    obtain ⟨q, hq_in, hq_eq⟩ := hq'_in
    rw [← hq_eq, liftConfig_apply_lift]
    exact hO_echoed q hq_in

/-! ## §5. Discussion: how this corresponds to ThyHBB1

The DTS we built captures the structural pattern of `voteBackwardAxiom`
in `Examples/ThyHBB1/Axioms.lean`:

```
∀ᶠ (fun learner => ∀ᶠ (fun value =>
  ofEvent ⟨voteSymb, [learner, value]⟩ ⇒ᶠ
    (safeFormula proposeSymb learner ∧ᶠ
      □ᶠ↓[[learner]] (ofEvent ⟨echoSymb, [value]⟩))))
```

The key sub-formula `□ᶠ↓[[learner]] echo(value)` reduces (via
`sat_box_singleton_exists` from `Logic/Properties/Modalities.lean:357`)
to:

```
∃ O ∈ (M.learner learner).quorums, ∀ q ∈ O, ↓ᶠ echo(value) at q
```

Compare with our DTS step's vote-validity clause:

```lean
∀ v, e = BroadcastEvent.vote v →
  ∃ O ∈ (F.σ P l).quorums,
    ∀ q ∈ O, BroadcastEvent.echo v ∈ c q
```

The shapes are identical: existential over quorums, universal over
quorum members, with each member required to have echoed in the past.
The "in the past" is encoded by the fact that `c q` is the agent's
already-existing event log at the time of the vote.

`broadcastDTS_oblivious` is therefore a faithful proof of the structural
pattern that makes ThyHBB1's vote backward axiom *grassroots-friendly*.
The same proof — with appropriate translation between `BroadcastEvent`
and the HBB `Event` grammar — would carry over to a literal embedding
of ThyHBB1 into the `Abstract.DTS` framework.

A literal embedding (state = full HBB model, step = single-event
extension preserving all of ThyHBB1) would be a substantially larger
file (~500-1000 lines) and is the natural next step if we want to
machine-check ThyHBB1 itself rather than its structural pattern.
-/

end HBBBridge
end Grassroots
end ModalDistribution
