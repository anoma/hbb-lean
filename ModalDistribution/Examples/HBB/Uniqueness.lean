import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.HBB.Liveness

/-!
# Uniqueness of proposals

Consequences of the uniqueness of proposals and of the shared echo axioms
`Echo?`, `EchoNE`, and `Echo!`, used by the three broadcast theories `HBBSafe`,
`HBBSimp`, and `HBBCorr`.

- **Uniqueness guard lemmas**:
  - `unique_propose_monotone`: at most one proposal persists in smaller histories
  - `unique_propose_guard_at_history`: uniqueness yields the at-most-one guard
  - `unique_propose_equal_values`: forces observed proposals to agree

- **Echo lemmas**:
  - `diamondPast_propose_of_echo`: (Echo?) at an echo event-tuple
  - `diamondPast_propose_at_end`: a proposal known at an event-tuple is known
    at the end of time
  - `boxPast_live_knows_echo_knows_propose`: (Echo?) under a live quorum
  - `box_echo_to_propose_diamond`: echo quorums imply proposal diamonds
  - `echo_non_equiv_diamond`: one-sided application of `EchoNE`

- **Lemma 6.6.1** (`unique_propose_eventually_echo`): a unique proposal
  guarantees eventual echoes of it
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
variable {proposeSymb echoSymb : Signature.EventSymb S}
variable {w w' : World P (Signature.EventType S)}

/-- Monotonicity of the at-most-one proposal condition. -/
theorem unique_propose_monotone
    (hSubset : w'.time ⊆trn w.time)
    (hUnique :
      ⟪w⟫ ⊨[M]∃≤ᶠ1 v ↦
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :
    ⟪w'⟫ ⊨[M]
      ∃≤ᶠ1 v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩) := fun v v' hv hv' =>
  -- Proposals known at `w'` are known at `w`, where at most one value is proposed.
  hUnique v v' (sat_diamondPast_nil_event_subset M w w' _ _ hSubset hv)
    (sat_diamondPast_nil_event_subset M w w' _ _ hSubset hv')

/-- Auxiliary: uniqueness at a fixed world yields the guarded at-most-one witness. -/
theorem unique_propose_guard_at_history
    {w : World P (Signature.EventType S)}
    (hUnique :
      ⟪w⟫ ⊨[M]∃!ᶠ v ↦
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :
    ⟪w⟫ ⊨[M]
      ∃≤ᶠ1 v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩) :=
  ((Sat.and M w _ _).1 hUnique).1

/-- Auxiliary: uniqueness of proposals forces observed proposal diamonds to agree. -/
theorem unique_propose_equal_values
    {w : World P (Signature.EventType S)}
    (value altValue : S.Value)
    (hAtMost : ⟪w⟫ ⊨[M]∃≤ᶠ1 v ↦ ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩))
    (hDiamond₁ : ⟪w⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))
    (hDiamond₂ : ⟪w⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [altValue]⟩)) :
    value = altValue :=
  hAtMost value altValue hDiamond₁ hDiamond₂

/-- (Echo?) at an echo event-tuple: whoever echoes `v` knows of a proposal
of `v`. -/
theorem diamondPast_propose_of_echo
    {value : S.Value}
    (hEchoBack : □W⊨[M]echoBackwardAxiom proposeSymb echoSymb)
    (hEvent : ⟪w⟫ ⊨[M]ofEvent ⟨echoSymb, [value]⟩) :
    ⟪w⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩) :=
  AllWorldValid.of_mem_history M hEchoBack (Sat.mem_of_ofEvent M hEvent) value hEvent

/-- A proposal known at an event-tuple of the model is known at the end of
time. -/
theorem diamondPast_propose_at_end
    {t : World P (Signature.EventType S)} {value : S.Value} (q : P)
    (ht : t ∈ M.history.val)
    (hKnown : ⟪t⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) :
    ⟪⟨q, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩) :=
  sat_diamondPast_nil_event_subset M ⟨q, †, M.history.val⟩ t _ _
    (time_subset_trn_history M (M.time_le_of_mem ht)) hKnown

/-- (Echo?) and Lemma 4.2.2 under a live quorum: a quorum of live
participants that know of `echo(v)` know of `propose(v)`. -/
theorem boxPast_live_knows_echo_knows_propose
    (hEchoBack : □W⊨[M]echoBackwardAxiom proposeSymb echoSymb)
    {l value : Signature.Value S}
    (hQuorum : ⊨[M]□ᶠ↓[[l]](predicate0 liveSymb ∧ᶠ
      ♢ᶠ↓[[]](ofEvent ⟨echoSymb, [value]⟩))) :
    ⊨[M]□ᶠ↓[[l]](predicate0 liveSymb ∧ᶠ
      ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩)) := by
  refine boxPast_mono_of_history (fun t ht h => ?_) hQuorum
  obtain ⟨hLive, hKnowsEcho⟩ := (Sat.and M t _ _).1 h
  -- (Echo?) at the known echo gives `♦↓♦↓ propose(v)`; Lemma 4.2.2 collapses it.
  exact (Sat.and M t _ _).2 ⟨hLive, diamondPast_idem M t _ ht <|
    Sat.diamond_of_imp []
      (fun _ => Sat.past_of_imp fun _ _ _ => diamondPast_propose_of_echo hEchoBack) hKnowsEcho⟩

theorem box_echo_to_propose_diamond
    {w : World P (Signature.EventType S)}
    (hSubset : w.time ⊆trn M.history.val)
    (hEchoBack :
      □W⊨[M]echoBackwardAxiom proposeSymb echoSymb)
    {learner : Signature.Value S}
    {value : S.Value}
    (hBox :
      ⟪w⟫ ⊨[M]□ᶠ↓[[learner]](ofEvent ⟨echoSymb, [value]⟩)) :
    ⟪w⟫ ⊨[M]
      ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩) := by
  -- Some member `q` of the (nonempty) quorum echoed `v` at an event-tuple `s` before `w`.
  obtain ⟨O, hO, hOEcho⟩ := (sat_box_singleton_exists M w learner _).1 hBox
  obtain ⟨q, hq⟩ := Semifilter.quorum_nonempty hO
  obtain ⟨s, hs, -, hsEcho⟩ := (Sat.past M _ _).1 (hOEcho q hq)
  -- (Echo?) at `s`: some `r` proposed `v` before `s`, hence before `w`.
  obtain ⟨r, hr⟩ := (Sat.diamond_nil M s _).1 (diamondPast_propose_of_echo hEchoBack hsEcho)
  exact (Sat.diamond_nil M w _).2
    ⟨r, Sat.past_of_time_subset (hSubset.2.trans _ (happensBefore_of_mem hs)) hr⟩

/-- One-sided application of `EchoNE`: an echo followed by a past echo must
share the same value. -/
theorem echo_non_equiv_diamond
    (hEchoNE : AllWorldValid M (echoNonEquivAxiom echoSymb))
    {w : World P (Signature.EventType S)}
    (hSubset : w.time ⊆trn M.history.val)
    {valNow valPast : Signature.Value S}
    (hDiamond :
      ⟪w⟫ ⊨[M]♢ᶠ↓[[]]((ofEvent ⟨echoSymb, [valNow]⟩) ∧ᶠ
            ↓ᶠ (ofEvent ⟨echoSymb, [valPast]⟩))) :
    valNow = valPast := by
  -- Some participant echoed `valNow` at an event-tuple `s` after echoing `valPast`.
  obtain ⟨q, hq⟩ := (Sat.diamond_nil M w _).1 hDiamond
  obtain ⟨s, hs, -, hsBoth⟩ := (Sat.past M _ _).1 hq
  obtain ⟨hNow, hPast⟩ := (Sat.and M s _ _).1 hsBoth
  -- (EchoNE) at `s`, an event-tuple of the model since `w.time ⊆ H`.
  exact AllWorldValid.of_mem_history M hEchoNE (hSubset.1 _ hs) valNow valPast hNow hPast

/-- Paper: Lemma 6.6.1. a unique proposal guarantees eventual echoes. -/
theorem unique_propose_eventually_echo
    (value : S.Value)
    (hEcho : □W⊨[M]echoForwardAxiom liveSymb proposeSymb echoSymb)
    (hEchoBack : □W⊨[M]echoBackwardAxiom proposeSymb echoSymb)
    (hUnique : ⊨[M]∃!ᶠ v ↦
        ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [v]⟩)) :
    □W⊨[M]
      (↕ᶠ (predicate0 liveSymb ∧ᶠ
          ♢ᶠ↓[[]](ofEvent ⟨proposeSymb, [value]⟩))) ⇒ᶠ
        ↕ᶠ(ofEvent ⟨echoSymb, [value]⟩) := by
  intro t ht
  refine Sat.imp_intro M t fun hKnown => ?_
  -- (Echo!): `t`'s participant eventually echoes some value `v'`, at some `s`.
  obtain ⟨v', hEcho'⟩ := (Sat.exists_iff t _).1 (hEcho ht value hKnown)
  obtain ⟨s, hs, hsPlace, hsEcho⟩ := (Sat.sometime M t _).1 hEcho'
  -- (Echo?): `v'` was proposed; so was `v`; by uniqueness `v' = v`.
  obtain ⟨s₀, hs₀, -, hs₀Known⟩ := (Sat.sometime M t _).1 hKnown
  have hv : v' = value :=
    unique_propose_equal_values _ _ (unique_propose_guard_at_history (hUnique t.place))
      (diamondPast_propose_at_end _ hs (diamondPast_propose_of_echo hEchoBack hsEcho))
      (diamondPast_propose_at_end _ hs₀ ((Sat.and M s₀ _ _).1 hs₀Known).2)
  exact (Sat.sometime M t _).2 ⟨s, hs, hsPlace, hv ▸ hsEcho⟩

end Results

end HBB
end Examples
end ModalDistribution
