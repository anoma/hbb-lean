import ModalDistribution.Logic.Semantics
import ModalDistribution.Logic.Properties.Quorums
import ModalDistribution.Logic.Properties.Satisfaction
import ModalDistribution.Core.Semifilter
import ModalDistribution.Core.History

/-!
# The modalities (paper Section 4)

The quorum intersection properties of Subsection 4.1 (Lemma 4.1.1 and
Notation 4.1.2, with their supporting lemmas) and the modal properties of
Subsection 4.2 (Lemmas 4.2.1-4.2.3), over the satisfaction machinery from
`Logic.Properties.Satisfaction`. The file ends with Lemma 6.5.4 and the
generic derivation lemmas for the boxed and diamond corollaries of the
liveness theorems.
-/

namespace ModalDistribution
namespace Logic

open Set
open History
open scoped Semifilter Formula History PreHistory Model

set_option autoImplicit false

variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]

section DiamondSection

/-! ## Quorum intersection properties (paper Subsection 4.1) -/

/-- Paper: Lemma 4.1.1(1). `⊨ ♢[l₁…lₙ]φ` holds exactly when every choice of
one quorum per learner has a common member satisfying `φ` at the end of time. -/
theorem n_way_quorum_intersection_witness
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] (♢ᶠ[ls] φ)) ↔ HasQuorumWitness (M := M) ls φ :=
  -- At the end of time the diamond does not depend on the participant.
  ⟨fun h => sat_diamond_iff_forall_quorumFamily.1 (h Classical.ofNonempty),
    fun h _ => sat_diamond_iff_forall_quorumFamily.2 h⟩

/-- Paper: Lemma 4.1.1(2). `⊨ ♢[l₁…lₙ]⊤` holds exactly when every choice of one
quorum per learner has a common member. -/
theorem n_way_quorum_intersection_nonempty
    (M : Model S P)
    (ls : List S.Value) :
    (⊨[M] (♢ᶠ[ls] ⊤ᶠ)) ↔ HasQuorumNonempty (M := M) ls :=
  ⟨fun h => (sat_diamond_top_iff_hasQuorumNonempty ..).1 (h Classical.ofNonempty),
    fun h _ => (sat_diamond_top_iff_hasQuorumNonempty ..).2 h⟩

/-- Paper: Lemma 4.1.1(3). `⊨ ♢[l₁…lₙ]φ` implies `⊨ ♢[l₁…lₙ]⊤`, since `φ`
implies `⊤`. -/
theorem EndValid.diamond_top_of_diamond
    (M : Model S P)
    (ls : List S.Value) (φ : Formula S) :
    (⊨[M] (♢ᶠ[ls] φ)) →
      (⊨[M] (♢ᶠ[ls] ⊤ᶠ)) := fun h p =>
  Sat.diamond_of_imp ls (fun _ _ => Sat.top M _) (h p)

/-- Paper: Notation 4.1.2 (nonempty quorum intersections). `l₁…lₙ` have
nonempty quorum intersections: `⊨ ♢[l₁…lₙ]⊤`. -/
@[simp] def HasNonemptyIntersections
    (M : Model S P) (ls : List S.Value) : Prop :=
  ⊨[M] (♢ᶠ[ls] ⊤ᶠ)

/-- Paper: Notation 4.1.2 (sequential quorum intersections). `l₁…lₙ` have
sequential quorum intersections: `⊨ ♢[l₁…lₙ]seq`. -/
@[simp] def HasSequentialIntersections
    (M : Model S P) (ls : List S.Value) : Prop :=
  ⊨[M] (♢ᶠ[ls] Formula.seq)

/-- Paper: Notation 4.1.2 (live quorum intersections). `l₁…lₙ` have live
quorum intersections: `⊨ ♢[l₁…lₙ]live`. -/
@[simp] def HasLiveIntersections
    (M : Model S P) (liveSymb : Signature.PredSymb S)
    (ls : List S.Value) : Prop :=
  ⊨[M] (♢ᶠ[ls] (Formula.predicate0 liveSymb))

/-- A quorum witness for `⊤` is the same as `⊨ ♢⇓[ls]⊤`, since `⇓⊤` always
holds. -/
theorem hasQuorumWitness_top_iff_diamondAllPast_top
    (M : Model S P)
    (ls : List S.Value) :
    HasQuorumWitness (M := M) ls ⊤ᶠ ↔
      (⊨[M] ♢ᶠ⇓[ls] ⊤ᶠ) :=
  (n_way_quorum_intersection_witness M ls ⊤ᶠ).symm.trans <| forall_congr' fun _ =>
    ⟨Sat.diamond_of_imp ls fun _ _ => (Sat.allPast ..).2 fun t _ _ => Sat.top M t,
      Sat.diamond_of_imp ls fun _ _ => Sat.top M _⟩

/-- When every participant is active (`⊨ □↓⊤`), a quorum witness for `⊤` is
the same as `⊨ ♢↓[ls]⊤`. -/
theorem hasQuorumWitness_top_iff_diamondPast_top
    (M : Model S P)
    (ls : List S.Value) :
    (⊨[M] □ᶠ[] (↓ᶠ ⊤ᶠ)) →
      (HasQuorumWitness (M := M) ls ⊤ᶠ ↔
        (⊨[M] ♢ᶠ↓[ls] ⊤ᶠ)) := fun hActive =>
  (n_way_quorum_intersection_witness M ls ⊤ᶠ).symm.trans <| forall_congr' fun _ =>
    ⟨Sat.diamond_of_imp ls fun q _ => EndValid.boxEmpty_guard M _ hActive q,
      Sat.diamond_of_imp ls fun _ _ => Sat.top M _⟩

/-- When every participant is active (`⊨ □↓⊤`), a quorum witness for `seq`
gives `⊨ ♢↓[ls]seq`. The converse fails: `↓seq` can hold through a sequential
earlier time even when the current one is not sequential. -/
theorem diamondPast_seq_of_hasQuorumWitness_seq
    (M : Model S P)
    (ls : List S.Value) :
    (⊨[M] □ᶠ[] (↓ᶠ ⊤ᶠ)) →
      (HasQuorumWitness (M := M) ls Formula.seq →
        (⊨[M] ♢ᶠ↓[ls] Formula.seq)) := fun hActive hWitness =>
  (n_way_quorum_intersection_witness M ls _).2
    (HasQuorumWitness.seq_to_past M ls hActive hWitness)

/-! ## Modal properties (paper Subsection 4.2) -/

/-- Paper: Lemma 4.2.1(1). `□↓[l]φ ⇒ ♦φ`, the analogue of the (D) axiom. -/
theorem singleton_box_implies_diamond
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S)
    (hBox : ⟪w⟫ ⊨[M]□ᶠ↓[[l]]φ) :
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] φ) :=
  sat_diamondEmpty_of_box_singleton hBox

/-- Paper: Lemma 4.2.1(2) (first part). `⊨ □φ ⇒ ♢φ`: the evaluating
participant is itself a witness. -/
theorem endValid_boxEmpty_imp_diamondEmpty
    (M : Model S P) (φ : Formula S) :
    ⊨[M] (□ᶠ[] φ) ⇒ᶠ ♢ᶠ[] φ := fun p hBox =>
  (Sat.diamondEmpty ..).2 ⟨p, (Sat.boxEmpty ..).1 hBox p⟩

/-- Paper: Lemma 4.2.1(2). If `□[l]φ` is valid then so is `♢φ`. -/
theorem global_singleton_box_implies_diamond
    (M : Model S P)
    (l : Signature.Value S) (φ : Formula S) :
    (⊨[M] □ᶠ[[l]] φ) → (⊨[M] ♢ᶠ[] φ) := fun hBox p =>
  sat_diamondEmpty_of_box_singleton (hBox p)

/-- Paper: Lemma 4.2.1(2). `□[l]φ ⇒ ♢φ` at the end of any history `H`; for the
model history this is `⊨ □[l]φ ⇒ ♢φ`. -/
theorem quorum_box_implies_empty_diamond
    (M : Model S P)
    (H : History P (Signature.EventType S)) (p : P)
    (l : Signature.Value S) (φ : Formula S) :
    (⟪⟨p, †, H.val⟩⟫ ⊨[M] □ᶠ[[l]] φ) →
      (⟪⟨p, †, H.val⟩⟫ ⊨[M] ♢ᶠ[] φ) :=
  sat_diamondEmpty_of_box_singleton

/-- Paper: Lemma 4.2.2 (the (4) axiom of S4). `♦♦φ ⇒ ♦φ` at a world of the
model, by transitivity of accessibility. -/
theorem diamondPast_idem
    (M : Model S P)
    (w : World P (Signature.EventType S)) (φ : Formula S)
    (hMem : w ∈ M.history.val) :
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (♢ᶠ↓[[]] φ)) →
      (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] φ) := fun hDiamond =>
  let ⟨_, ht, hInner⟩ := Sat.diamondPast_nil.1 hDiamond
  let ⟨t', ht', hφ⟩ := Sat.diamondPast_nil.1 hInner
  -- Proposition 3.4.5: `t' ≪ t ≪ w` gives `t' ≪ w`.
  Sat.diamondPast_nil.2 ⟨t', accessible_trans (M.time_le_of_mem hMem) ht' ht, hφ⟩

/-- `↓φ ⇒ ♦φ`: a past event-tuple at the current place is a past event-tuple
at some place. -/
theorem diamondPast_nil_of_past
    {M : Model S P}
    {w : World P (Signature.EventType S)}
    {φ : Formula S}
    (h : ⟪w⟫ ⊨[M]↓ᶠ φ) :
    ⟪w⟫ ⊨[M]♢ᶠ↓[[]] φ :=
  let ⟨t, ht, _, hφ⟩ := (Sat.past ..).1 h
  Sat.diamondPast_nil.2 ⟨t, ht, hφ⟩

/-- At the end of time `♦φ` does not depend on the place: if it holds at one
end-of-time world, it is valid. -/
theorem diamondPast_nil_valid_of_end
    {M : Model S P} {p : P} {φ : Formula S}
    (h : ⟪⟨p, †, M.history.val⟩⟫ ⊨[M]♢ᶠ↓[[]] φ) :
    ⊨[M]♢ᶠ↓[[]] φ := fun _ =>
  Sat.diamondPast_nil.2 (Sat.diamondPast_nil.1 h)

/-- Paper: Lemma 4.2.3(2). `♦□↓[l]φ ⇒ □↓[l]φ` at a world of the model, the
analogue of the (5) axiom: the quorum's past witnesses at an earlier world are
past witnesses now. -/
theorem past_diamond_box_collapses_to_present_box
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S)
    (hMem : w ∈ M.history.val) :
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (□ᶠ↓[[l]] φ)) →
      (⟪w⟫ ⊨[M] □ᶠ↓[[l]] φ) := by
  intro hDiamond
  obtain ⟨t, ht, hBox⟩ := Sat.diamondPast_nil.1 hDiamond
  obtain ⟨O, hO, hAll⟩ := (sat_box_singleton_exists ..).1 hBox
  -- Proposition 3.4.5: everything accessible from `t ≪ w` is accessible from `w`.
  have hSub : t.time ⊆ w.time := fun _ hs => accessible_trans (M.time_le_of_mem hMem) hs ht
  exact (sat_box_singleton_exists ..).2
    ⟨O, hO, fun q hq => Sat.past_of_time_subset hSub (hAll q hq)⟩

/-- Paper: Lemma 4.2.3(1). `↓□↓[l]φ ⇒ □↓[l]φ` at a world of the model; it
follows from part (2) since `↓` implies `♦`. -/
theorem past_box_collapses_to_present_box
    (M : Model S P)
    (w : World P (Signature.EventType S))
    (l : Signature.Value S) (φ : Formula S)
    (hMem : w ∈ M.history.val) :
    (⟪w⟫ ⊨[M] ↓ᶠ (□ᶠ↓[[l]] φ)) →
      (⟪w⟫ ⊨[M] □ᶠ↓[[l]] φ) :=
  fun hPastBox =>
    past_diamond_box_collapses_to_present_box M w l φ hMem
      (diamondPast_nil_of_past hPastBox)

/-! ## Corollary derivation for the liveness theorems -/

/-- Paper: Lemma 6.5.4. `⊨ □[l]↕φ` coincides with `⊨ □↓[l]φ`. -/
theorem box_sometime_iff_boxPast
    (M : Model S P)
    (φ : Formula S)
    (l : Signature.Value S) :
    (⊨[M]□ᶠ[[l]] ↕ᶠφ) ↔
      (⊨[M]□ᶠ↓[[l]] φ) :=
  -- At the end of time `↕φ = ⤒↓φ` is `↓φ`, since `⤒` evaluates at the end of time.
  Iff.rfl

/-- From an end-of-time implication `(♢↓[]ψ) ⇒ G ⇒ ↕D` and a guard quorum
`□[l]G`, conclude the past-box corollary `(♢↓[]ψ) ⇒ □↓[l]D`. This packages
the derivation of the boxed corollaries of the liveness theorems. -/
theorem endValid_boxPast_of_imp_sometime
    (M : Model S P)
    {l : Signature.Value S} {ψ G D : Formula S}
    (hGuard : ⊨[M]□ᶠ[[l]]G)
    (hMain : ⊨[M](♢ᶠ↓[[]]ψ) ⇒ᶠ (G ⇒ᶠ ↕ᶠ D)) :
    ⊨[M](♢ᶠ↓[[]]ψ) ⇒ᶠ □ᶠ↓[[l]]D := by
  intro p hAnte
  -- The antecedent `♦ψ` holds at every participant at the end of time ...
  have hAnteAll : ⊨[M]♢ᶠ↓[[]]ψ := diamondPast_nil_valid_of_end hAnte
  -- ... so every member of the guard quorum eventually sees `D`,
  have hBox : ⊨[M]□ᶠ[[l]](↕ᶠ D) := fun q =>
    Sat.box_of_imp [l] (fun r hG => hMain r (hAnteAll r) hG) (hGuard q)
  -- which by Lemma 6.5.4 is the past box.
  exact (box_sometime_iff_boxPast M D l).1 hBox p

/-- The diamond corollary of `endValid_boxPast_of_imp_sometime`:
`(♢↓[]ψ) ⇒ ♢↓[]D`. -/
theorem endValid_diamondPast_of_imp_sometime
    (M : Model S P)
    {l : Signature.Value S} {ψ G D : Formula S}
    (hGuard : ⊨[M]□ᶠ[[l]]G)
    (hMain : ⊨[M](♢ᶠ↓[[]]ψ) ⇒ᶠ (G ⇒ᶠ ↕ᶠ D)) :
    ⊨[M](♢ᶠ↓[[]]ψ) ⇒ᶠ ♢ᶠ↓[[]]D := fun p hAnte =>
  singleton_box_implies_diamond M _ l D
    (endValid_boxPast_of_imp_sometime M hGuard hMain p hAnte)

end DiamondSection

end Logic
end ModalDistribution
