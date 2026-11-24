import ModalDistribution.Logic.AxiomSystem
import ModalDistribution.Logic.Properties
import ModalDistribution.Logic.Syntax
import ModalDistribution.Core.Prehistory
import ModalDistribution.Core.History

/-!
# Theory `thyLive`

We formalise the liveness theory.  The theory is
parametrised by a distinguished predicate symbol `liveSymb`, and contains the
axioms `LiveAlways` and `LiveSeq`, together with two knowledge axiom
schemes indexed by events (and, for the quorum scheme, a learner).  This file
records the theory and the lemmas and propositions that depend on it.
-/

namespace ModalDistribution
namespace Examples

open ModalDistribution
open ModalDistribution.Logic
open History
open PreHistory
open World
open scoped Formula

set_option autoImplicit false

variable {S : Signature}

section Axioms

/-- Paper: Figure 7, axiom (LiveAlways). Axiom `LiveAlways`: being live is independent of time. -/
@[simp] def liveAlwaysAxiom
    (liveSymb : Signature.PredSymb S) :
    Formula S :=
  (Formula.predicate0 liveSymb) ⇔ᶠ
    ⤒ᶠ (Formula.predicate0 liveSymb)

/-- Paper: Figure 7, axiom (LiveSeq). Axiom `LiveSeq`: live participants act sequentially. -/
@[simp] def liveSeqAxiom
    (liveSymb : Signature.PredSymb S) :
    Formula S :=
  (Formula.predicate0 liveSymb) ⇒ᶠ Formula.seq

/-- Paper: Figure 7, axiom-scheme (Knowledge♢↓). One instance for each event `E`:
if a live participant ever performs `E`, then every live participant
eventually knows that `E` occurred. -/
@[simp] def knowledgeDiamondAxiom
    (liveSymb : Signature.PredSymb S)
    (evt : Signature.EventType S) :
    Formula S :=
  (⤒ᶠ (♢ᶠ↓[[]]
    ((Formula.predicate0 liveSymb) ∧ᶠ Formula.ofEvent evt))) ⇒ᶠ
    ((Formula.predicate0 liveSymb) ⇒ᶠ
      ↕ᶠ (♢ᶠ↓[[]] (Formula.ofEvent evt)))

/-- Paper: Figure 7, axiom-scheme (Knowledge□↓). One instance for each learner
`l` and event `E`: if an `l`-quorum of live participants performs `E`, then
every live participant eventually knows that an `l`-quorum performed `E`. -/
@[simp] def knowledgeBoxAxiom
    (liveSymb : Signature.PredSymb S)
    (l : Signature.Value S)
    (evt : Signature.EventType S) :
    Formula S :=
  (⤒ᶠ □ᶠ↓[[l]]
    ((Formula.predicate0 liveSymb) ∧ᶠ Formula.ofEvent evt)) ⇒ᶠ
    ((Formula.predicate0 liveSymb) ⇒ᶠ
      ↕ᶠ (□ᶠ↓[[l]] (Formula.ofEvent evt)))

/-- Paper: Definition 5.2.4 (the theory of liveness). The collection of liveness axioms
(`thyLive`). -/
@[simp] def thyLive
    (liveSymb : Signature.PredSymb S) :
    Set (Formula S) :=
  { φ |
      φ = liveAlwaysAxiom (S := S) liveSymb ∨
      φ = liveSeqAxiom (S := S) liveSymb ∨
      (∃ evt, φ = knowledgeDiamondAxiom (S := S) liveSymb evt) ∨
      (∃ l evt, φ = knowledgeBoxAxiom (S := S) liveSymb l evt) }

end Axioms

section Projections

variable {P : Type} [Nonempty P] {M : Model S P} {liveSymb : Signature.PredSymb S}

/-- Project validity of `(LiveAlways)` out of a model of `thyLive`. -/
theorem thyLive_live_always (hTheory : M ⊨ᵀ thyLive liveSymb) :
    □W⊨[M] liveAlwaysAxiom (S := S) liveSymb :=
  hTheory (Or.inl rfl)

/-- Project validity of `(LiveSeq)` out of a model of `thyLive`. -/
theorem thyLive_live_seq (hTheory : M ⊨ᵀ thyLive liveSymb) :
    □W⊨[M] liveSeqAxiom (S := S) liveSymb :=
  hTheory (Or.inr (Or.inl rfl))

/-- Project validity of a `(Knowledge♢↓)` instance out of a model of `thyLive`. -/
theorem thyLive_knowledge_diamond (hTheory : M ⊨ᵀ thyLive liveSymb)
    (evt : Signature.EventType S) :
    □W⊨[M] knowledgeDiamondAxiom (S := S) liveSymb evt :=
  hTheory (Or.inr (Or.inr (Or.inl ⟨evt, rfl⟩)))

/-- Project validity of a `(Knowledge□↓)` instance out of a model of `thyLive`. -/
theorem thyLive_knowledge_box (hTheory : M ⊨ᵀ thyLive liveSymb)
    (l : Signature.Value S) (evt : Signature.EventType S) :
    □W⊨[M] knowledgeBoxAxiom (S := S) liveSymb l evt :=
  hTheory (Or.inr (Or.inr (Or.inr ⟨l, evt, rfl⟩)))

end Projections

section Results

variable {P : Type} [Nonempty P] {M : Model S P}
variable {liveSymb : Signature.PredSymb S}
variable {φ : Formula S} {l l₁ : Signature.Value S} {evt : Signature.EventType S}

/-- Paper: Lemma 5.2.7. Sometime knowledge lifts to the end of time. -/
theorem sometime_past_end
    {w : World P (Signature.EventType S)}
    (hSat : ⟪w⟫ ⊨[M]↕ᶠ(♢ᶠ[]↓ᶠ (Formula.ofEvent evt))) :
    ⟪⟨w.place, †, M.history.val⟩⟫ ⊨[M] ♢ᶠ[]↓ᶠ (Formula.ofEvent evt) := by
  -- At some event-tuple `t` of `w`'s participant, some `q` had performed `E`
  -- before `t`; `t`'s past is part of the history, so `q` has `E` at the end.
  obtain ⟨t, ht, -, hDiamond⟩ := (Sat.sometime M w _).1 hSat
  obtain ⟨q, hq⟩ := (Sat.diamondEmpty M t _).1 hDiamond
  have hSub := time_subset_trn_history M (M.time_le_of_mem ht)
  exact (Sat.diamondEmpty M _ _).2 ⟨q, sat_past_event_of_subset_to_history M ⟨q, †, t.time⟩ evt
    hSub hq⟩

/-- Paper: Lemma 5.2.9(1). Liveness at world equivalent to liveness at end-of-time (Liveness
equivalence). Liveness does not depend on time: a participant is live at a specific world if and
only if it is live at the end-of-time world for that participant. This follows from the
liveness-always axiom (live ⇔ ⤒ live).

See also: `always_live_equiv_backward`, liveness-always axiom. -/
theorem always_live_equiv_forward
    (hTheory : M ⊨ᵀ thyLive liveSymb)
    {t : World P (Signature.EventType S)}
    (ht : t ∈ M.history.val) :
    (⟪t⟫ ⊨[M] Formula.predicate0 liveSymb) ↔
      (⟪⟨t.place, †, M.history.val⟩⟫ ⊨[M] Formula.predicate0 liveSymb) :=
  -- (LiveAlways) at `t` reads `live ⇔ ⤒live`.
  have h := AllWorldValid.of_mem_history M (thyLive_live_always hTheory) ht
  ⟨Sat.iff_mp M t h, Sat.iff_mpr M t h⟩

/-- Paper: Lemma 5.2.9(2). Liveness at any two worlds with same participant.
 Liveness does not depend on time: if two worlds have the same participant (place),
then liveness holds at one if and only if it holds at the other. This is a direct
consequence of the forward direction applied twice.

See also: `always_live_equiv_forward`, liveness-always axiom. -/
theorem always_live_equiv_backward
    (hTheory : M ⊨ᵀ thyLive liveSymb)
    {t t' : World P (Signature.EventType S)}
    (ht : t ∈ M.history.val)
    (ht' : t' ∈ M.history.val)
    (hplace : t.place = t'.place) :
    (⟪t⟫ ⊨[M] Formula.predicate0 liveSymb) ↔
      (⟪t'⟫ ⊨[M] Formula.predicate0 liveSymb) := by
  rw [always_live_equiv_forward hTheory ht, always_live_equiv_forward hTheory ht', hplace]

/-- Paper: Lemma 5.2.9(3). Liveness at an event-tuple of the model implies liveness at every past
event at the same place. -/
theorem live_allPast
    (hTheory : M ⊨ᵀ thyLive liveSymb)
    {t : World P (Signature.EventType S)}
    (ht : t ∈ M.history.val)
    (hLive : ⟪t⟫ ⊨[M] Formula.predicate0 liveSymb) :
    ⟪t⟫ ⊨[M]⇓ᶠ (Formula.predicate0 liveSymb) :=
  (Sat.allPast M t _).2 fun _t' ht' hplace =>
    (always_live_equiv_backward hTheory
      (History.subset_of_happensBefore (happensBefore_of_mem ht) _ ht') ht hplace).2 hLive

section LiveQuorumSeq

variable (P) (M)

/-- A quorum of live participants is a quorum of sequential participants,
by the `(LiveSeq)` axiom. -/
theorem live_quorum_seq
    (hTheory : M ⊨ᵀ thyLive liveSymb)
    (hLiveQuorum : ⊨[M]□ᶠ[[l]]Formula.predicate0 liveSymb) :
    ⊨[M]□ᶠ[[l]]Formula.seq := fun p =>
  Sat.box_of_imp [l]
    (fun q => Sat.imp_elim M _ (AllWorldValid.at_end M (thyLive_live_seq hTheory) q))
    (hLiveQuorum p)

end LiveQuorumSeq

/-- Instantiate `(Knowledge□↓)` at the end of time: if an `l`-quorum of live
participants performed `E`, every live participant sometime knows that an
`l`-quorum performed `E`. -/
theorem live_eventually_knows_box
    (hTheory : M ⊨ᵀ thyLive liveSymb)
    (hQuorum : ⊨[M]□ᶠ↓[[l]]((Formula.predicate0 liveSymb) ∧ᶠ (Formula.ofEvent evt))) :
    ⊨[M](Formula.predicate0 liveSymb) ⇒ᶠ ↕ᶠ (□ᶠ↓[[l]] (Formula.ofEvent evt)) := fun p =>
  Sat.imp_elim M _ (AllWorldValid.at_end M (thyLive_knowledge_box hTheory l evt) p) (hQuorum p)

/-- Paper: Lemma 5.2.11. Liveness quorum boxes promote to nested
quorum boxes under `thyLive`. -/
theorem live_boxPast_nests
    (hTheory : M ⊨ᵀ thyLive liveSymb)
    (hQuorum : ⊨[M]□ᶠ↓[[l]]((Formula.predicate0 liveSymb) ∧ᶠ (Formula.ofEvent evt))) :
    ⊨[M]□ᶠ↓[[l]]((Formula.predicate0 liveSymb) ∧ᶠ □ᶠ↓[[l]] (Formula.ofEvent evt)) := by
  -- Take the `l`-quorum from the hypothesis; each member `q` had `live ∧ E` at some `t`.
  refine fun p => Sat.box_of_imp [l] (fun q hq => ?_) (hQuorum p)
  obtain ⟨t, ht, rfl, htLiveE⟩ := (Sat.past M _ _).1 hq
  have htLive := ((Sat.and M t _ _).1 htLiveE).1
  -- (Knowledge□↓) at `t`: sometime `t.place` knows of the `l`-quorum of `E`.
  obtain ⟨s, hs, hsPlace, hsBox⟩ := (Sat.sometime M t _).1 <|
    Sat.imp_elim M t
      (Sat.imp_elim M t
        (AllWorldValid.of_mem_history M (thyLive_knowledge_box hTheory l evt) ht)
        (hQuorum t.place))
      htLive
  -- (LiveAlways), Lemma 5.2.9(2): `s` is live too.
  exact (Sat.past M _ _).2 ⟨s, hs, hsPlace, (Sat.and M s _ _).2
    ⟨(always_live_equiv_backward hTheory ht hs hsPlace.symm).1 htLive, hsBox⟩⟩

/-- Paper: Proposition 5.2.8. If some live participant performed `E`, then
an `l`-quorum of live participants eventually knows that `E` occurred. -/
theorem live_eventually_knows
    (hTheory : M ⊨ᵀ thyLive liveSymb)
    (hLive : ⊨[M]□ᶠ[[l]](Formula.predicate0 liveSymb))
    (hEvent : ⊨[M]♢ᶠ↓[[]]((Formula.predicate0 liveSymb) ∧ᶠ (Formula.ofEvent evt))) :
    ⊨[M]□ᶠ↓[[l]]
      ((Formula.predicate0 liveSymb) ∧ᶠ
        ♢ᶠ↓[[]] (Formula.ofEvent evt)) := by
  -- Each live member `q` of the `l`-quorum knows of `E` at some event-tuple `s`.
  refine fun p => Sat.box_of_imp [l] (fun q hq => ?_) (hLive p)
  -- (Knowledge♢↓) at the end of time: `q` sometime knows of `E`.
  obtain ⟨s, hs, hsPlace, hsKnows⟩ := (Sat.sometime M _ _).1 <|
    Sat.imp_elim M _
      (Sat.imp_elim M _ (AllWorldValid.at_end M (thyLive_knowledge_diamond hTheory evt) q)
        (hEvent q))
      hq
  -- (LiveAlways), Lemma 5.2.9(1): `s` is live, being an event-tuple of `q`.
  exact (Sat.past M _ _).2 ⟨s, hs, hsPlace, (Sat.and M s _ _).2
    ⟨(always_live_equiv_forward hTheory hs).2 (hsPlace ▸ hq), hsKnows⟩⟩

/-- Paper: Proposition 5.2.10. Live quorum intersections expose live witnesses. -/
theorem intertwined_two_quorums
    (hTheory : M ⊨ᵀ thyLive liveSymb)
    (hIntersect : ⊨[M]♢ᶠ[[l, l₁]]⊤ᶠ)
    (hLiveQuorum : ⊨[M]□ᶠ[[l₁]](Formula.predicate0 liveSymb))
    (hWitness : ⊨[M]□ᶠ↓[[l]]φ) :
    ⊨[M] ♢ᶠ↓[[]]
      ((Formula.predicate0 liveSymb) ∧ᶠ φ) := by
  intro p
  -- An `l`-quorum `O` whose members had `φ`, and an `l₁`-quorum `O'` of live members.
  obtain ⟨O, hO, hOφ⟩ := (sat_box_singleton_exists M _ l _).1 (hWitness p)
  obtain ⟨O', hO', hO'Live⟩ := (sat_box_singleton_exists M _ l₁ _).1 (hLiveQuorum p)
  -- They intersect in some `q`, which had `φ` at some event-tuple `t`.
  obtain ⟨q, ⟨hqO, hqO'⟩, -⟩ := (sat_diamond_pair_iff M _ l l₁ _).1 (hIntersect p) O hO O' hO'
  obtain ⟨t, ht, rfl, htφ⟩ := (Sat.past M _ _).1 (hOφ _ hqO)
  -- `t` is live by (LiveAlways), Lemma 5.2.9(1).
  exact sat_diamondEmpty_of_local M _ _ ⟨t.place, (Sat.past M _ _).2 ⟨t, ht, rfl,
    (Sat.and M t _ _).2 ⟨(always_live_equiv_forward hTheory ht).2 (hO'Live _ hqO'), htφ⟩⟩⟩

end Results

end Examples
end ModalDistribution
