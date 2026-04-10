import ModalDistribution.Core.Prehistory
import ModalDistribution.Core.History

/-!
# Grassroots Projection and Sequentiality Preservation

This file extends the HBB formalization with the **grassroots projection**
of prehistories and proves that **sequentiality is preserved** under it.

## Setting

Shapiro grassroots (arXiv:2301.04391, Definition 9) requires:
`TS(P) ⊊ TS(P')/P` for `P ⊂ P'`. The "non-interference" half says: any
behaviour of the small group survives when the small group is embedded in
the larger one. We instantiate this for HBB by:

1. Working with a global agent universe `A : Type` and treating each
   participant set as `↥(P : Set A)`.
2. Defining `projectListAux` / `projectPreHistory`, the analogue of
   Shapiro's `TS(P')/P` projection on history-structure-style prehistories:
   keep only event-tuples whose place lies in `P` and recursively project
   their times.
3. Proving the membership characterization
   `mem_projectPreHistory_iff` and the projection-preserves-accessibility
   lemma `accessible_project_of_accessible`.
4. Concluding `isSequential_projection`: if a participant `p ∈ ↥P` is
   sequential in the unprojected history `H'` over `↥P'`, then the
   re-coordinated `p` is sequential in `projectPreHistory h H'`.

The key intuition: projection is a forgetful operation that drops tuples
whose place lies outside `P`, but preserves the order on the surviving
tuples. Sequentiality is per-participant, so it cannot be broken by
removing tuples at *other* places.

## Main definitions

* `Grassroots.liftAgent` — inclusion `↥P → ↥P'` for `P ⊆ P'`.
* `Grassroots.projectPreHistory` — Shapiro projection on prehistories.
* `Grassroots.projectHistory` — same lifted to history structures.

## Main theorems

* `Grassroots.mem_projectPreHistory_iff` — characterisation of membership
  in a projected prehistory.
* `Grassroots.accessible_project_of_accessible` — projection is monotone
  with respect to accessibility (`≪`).
* `Grassroots.projectPreHistory_isHereditarilyTransitive` — projection
  preserves hereditary transitivity.
* `Grassroots.isSequential_projection` — projection-aware analogue of
  `History.sequentiality_monotone`: sequentiality at a participant is
  inherited by the projection.
-/

namespace ModalDistribution
namespace Grassroots

open scoped PreHistory

universe u v
variable {A : Type u} {Event : Type v}

/-! ## §1. Subtype embeddings -/

/-- Inclusion of subtypes induced by `P ⊆ P'`. -/
@[simp] def liftAgent {P P' : Set A} (h : P ⊆ P') : ↥P → ↥P' :=
  fun a => ⟨a.val, h a.property⟩

@[simp] lemma liftAgent_val {P P' : Set A} (h : P ⊆ P') (a : ↥P) :
    (liftAgent h a).val = a.val := rfl

/-! ## §2. Prehistory projection

`projectPreHistory h H'` is the prehistory over `↥P` obtained from `H'`
by keeping every tuple whose place lies in `P` and recursively projecting
its time component.

The mutual definition is structurally recursive: `projectListAux` recurses
on the underlying list, and inside the cons-case calls `projectPreHistory`
on the strictly-smaller `time` component of the head tuple. -/

open Classical in
mutual

/-- List-level helper for `projectPreHistory`. Discards tuples whose place
lies outside `P`, and recursively projects the time component of those
that survive. -/
noncomputable def projectListAux {P P' : Set A} (h : P ⊆ P') :
    List (World ↥P' Event) → List (World ↥P Event)
  | [] => []
  | (⟨a, _⟩, e, t) :: rest =>
      if ha : (a : A) ∈ P then
        (⟨a, ha⟩, e, projectPreHistory h t) :: projectListAux h rest
      else
        projectListAux h rest

/-- The Shapiro projection on prehistories: keep tuples whose place lies in
`P`, with recursively projected times. -/
noncomputable def projectPreHistory {P P' : Set A} (h : P ⊆ P') :
    PreHistory ↥P' Event → PreHistory ↥P Event
  | .mk l => .mk (projectListAux h l)

end

/-- Unfolding lemma: projection on `mk l`. -/
@[simp] lemma projectPreHistory_mk {P P' : Set A} (h : P ⊆ P')
    (l : List (World ↥P' Event)) :
    projectPreHistory (Event := Event) h (PreHistory.mk l) =
      PreHistory.mk (projectListAux h l) := by
  rfl

/-- Unfolding lemma: list projection on the empty list. -/
@[simp] lemma projectListAux_nil {P P' : Set A} (h : P ⊆ P') :
    projectListAux (Event := Event) (P := P) (P' := P') h [] = [] := by
  rfl

/-- Unfolding lemma: list projection on a cons whose place lies in `P`. -/
lemma projectListAux_cons_in {P P' : Set A} (h : P ⊆ P')
    {a : A} (ha' : a ∈ P') {e : MaybeEvent Event}
    {t : PreHistory ↥P' Event} {rest : List (World ↥P' Event)}
    (ha : a ∈ P) :
    projectListAux h ((⟨a, ha'⟩, e, t) :: rest) =
      (⟨a, ha⟩, e, projectPreHistory h t) :: projectListAux h rest := by
  classical
  conv_lhs => unfold projectListAux
  simp [ha]

/-- Unfolding lemma: list projection on a cons whose place is *not* in `P`. -/
lemma projectListAux_cons_out {P P' : Set A} (h : P ⊆ P')
    {a : A} (ha' : a ∈ P') {e : MaybeEvent Event}
    {t : PreHistory ↥P' Event} {rest : List (World ↥P' Event)}
    (ha : a ∉ P) :
    projectListAux h ((⟨a, ha'⟩, e, t) :: rest) =
      projectListAux h rest := by
  classical
  conv_lhs => unfold projectListAux
  simp [ha]

/-! ## §3. Membership characterisation

A tuple `s : World ↥P Event` lies in a projected prehistory iff it arises
as the projection of some original tuple whose place lies in `P`. -/

/-- Membership in the list-level projection. -/
lemma mem_projectListAux_iff
    {P P' : Set A} (h : P ⊆ P')
    (s : World ↥P Event) (l : List (World ↥P' Event)) :
    s ∈ projectListAux h l ↔
      ∃ (t : World ↥P' Event) (ht : (t.1.val : A) ∈ P),
        t ∈ l ∧
          ((⟨t.1.val, ht⟩, t.2.1, projectPreHistory h t.2.2)
            : World ↥P Event) = s := by
  classical
  induction l with
  | nil =>
      simp [projectListAux_nil]
  | cons head rest ih =>
      rcases head with ⟨⟨a, ha'⟩, e, t⟩
      by_cases ha : a ∈ P
      · rw [projectListAux_cons_in (ha' := ha') h ha]
        constructor
        · intro hMem
          rcases List.mem_cons.mp hMem with hHead | hRest
          · refine ⟨(⟨a, ha'⟩, e, t), ha, ?_, ?_⟩
            · exact List.mem_cons_self
            · exact hHead.symm
          · obtain ⟨t', ht', hin', heq⟩ := ih.mp hRest
            exact ⟨t', ht', List.mem_cons_of_mem _ hin', heq⟩
        · rintro ⟨t', ht', hin', heq⟩
          rcases List.mem_cons.mp hin' with hOrig | hRest
          · subst hOrig
            exact List.mem_cons.mpr (Or.inl heq.symm)
          · exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨t', ht', hRest, heq⟩))
      · rw [projectListAux_cons_out (ha' := ha') h ha]
        constructor
        · intro hMem
          obtain ⟨t', ht', hin', heq⟩ := ih.mp hMem
          exact ⟨t', ht', List.mem_cons_of_mem _ hin', heq⟩
        · rintro ⟨t', ht', hin', heq⟩
          rcases List.mem_cons.mp hin' with hOrig | hRest
          · -- contradiction: t' is the head, so t'.1.val = a ∉ P
            subst hOrig
            exact (ha ht').elim
          · exact ih.mpr ⟨t', ht', hRest, heq⟩

/-- Membership in a projected prehistory: exists a witness in the original
prehistory whose place lies in `P` and which projects to the given tuple. -/
lemma mem_projectPreHistory_iff
    {P P' : Set A} (h : P ⊆ P')
    (s : World ↥P Event) (H' : PreHistory ↥P' Event) :
    s ∈ projectPreHistory h H' ↔
      ∃ (t : World ↥P' Event) (ht : (t.1.val : A) ∈ P),
        t ∈ H' ∧
          ((⟨t.1.val, ht⟩, t.2.1, projectPreHistory h t.2.2)
            : World ↥P Event) = s := by
  classical
  cases H' with
  | mk l =>
      rw [projectPreHistory_mk]
      simp only [PreHistory.mem_mk]
      exact mem_projectListAux_iff h s l

/-! ## §4. Accessibility is preserved by projection -/

/-- Projection is monotone with respect to accessibility (`≪`):
if `s' ≪ t'` in `↥P'` and both endpoints have places in `P`, then their
projections are accessible in the projected `↥P`. -/
lemma accessible_project_of_accessible
    {P P' : Set A} (h : P ⊆ P')
    {s' t' : World ↥P' Event}
    (hs' : (s'.1.val : A) ∈ P) (ht' : (t'.1.val : A) ∈ P)
    (hacc : s' ≪ t') :
    ((⟨s'.1.val, hs'⟩, s'.2.1, projectPreHistory h s'.2.2)
      : World ↥P Event)
      ≪
    ((⟨t'.1.val, ht'⟩, t'.2.1, projectPreHistory h t'.2.2)
      : World ↥P Event) := by
  -- ≪ unfolds to "membership in time"
  change _ ∈ projectPreHistory h t'.2.2
  rw [mem_projectPreHistory_iff]
  exact ⟨s', hs', hacc, rfl⟩

/-! ## §5. Projection preserves hereditary transitivity -/

/-- Projection preserves the transitivity property of a single prehistory. -/
lemma isTransitive_project
    {P P' : Set A} (h : P ⊆ P')
    (H' : PreHistory ↥P' Event)
    (hH' : isTransitive H') :
    isTransitive (projectPreHistory h H') := by
  classical
  intro h₁ hbefore
  rcases hbefore with ⟨p, e, hin⟩
  rw [mem_projectPreHistory_iff] at hin
  obtain ⟨t', ht', hinH', heq⟩ := hin
  -- heq : (⟨t'.1.val, ht'⟩, t'.2.1, projectPreHistory h t'.2.2) = (p, e, h₁)
  -- so projectPreHistory h t'.2.2 = h₁
  have hh1 : projectPreHistory h t'.2.2 = h₁ := by
    have := congrArg (fun w : World ↥P Event => w.2.2) heq
    simpa using this
  -- Original tuple t' is in H', so t'.2.2 ≺− H'
  have hbeforeOrig : t'.2.2 ≺− H' := by
    refine ⟨t'.1, t'.2.1, ?_⟩
    rcases t' with ⟨a, e0, t0⟩
    exact hinH'
  -- By transitivity of H', t'.2.2 ⊆ H'
  have hsub : t'.2.2 ⊆ H' := hH' _ hbeforeOrig
  -- Now show: h₁ ⊆ projectPreHistory h H'
  intro u hu
  rw [← hh1] at hu
  rw [mem_projectPreHistory_iff] at hu
  obtain ⟨v, hvP, hvIn, hvProj⟩ := hu
  rw [mem_projectPreHistory_iff]
  exact ⟨v, hvP, hsub _ hvIn, hvProj⟩

/-- Projection preserves hereditary transitivity. The proof is by
well-founded recursion using `PreHistory.happensBefore_wellFounded`. -/
theorem projectPreHistory_isHereditarilyTransitive
    {P P' : Set A} (h : P ⊆ P')
    (H' : PreHistory ↥P' Event)
    (hH' : isHereditarilyTransitive H') :
    isHereditarilyTransitive (projectPreHistory h H') := by
  classical
  induction H' using
    (PreHistory.happensBefore_wellFounded (P := ↥P') (Event := Event)).induction with
  | _ H' ih =>
      have hUnfold := (isHereditarilyTransitive_unfold H').mp hH'
      have hTransH' : isTransitive H' := hUnfold.1
      have hHeredDesc : ∀ ⦃h₀ : PreHistory ↥P' Event⦄,
          h₀ ≺− H' → isHereditarilyTransitive h₀ := hUnfold.2
      rw [isHereditarilyTransitive_unfold]
      refine ⟨?_, ?_⟩
      · -- transitivity of the projection
        exact isTransitive_project h H' hTransH'
      · -- every predecessor of the projection is hereditarily transitive
        intro h₁ hbefore
        rcases hbefore with ⟨p, e, hin⟩
        rw [mem_projectPreHistory_iff] at hin
        obtain ⟨t', ht', hinH', heq⟩ := hin
        have hh1 : projectPreHistory h t'.2.2 = h₁ := by
          have := congrArg (fun w : World ↥P Event => w.2.2) heq
          simpa using this
        have hbeforeOrig : t'.2.2 ≺− H' := ⟨t'.1, t'.2.1, by
          rcases t' with ⟨a, e0, t0⟩; exact hinH'⟩
        have hHeredOrig := hHeredDesc hbeforeOrig
        have := ih t'.2.2 hbeforeOrig hHeredOrig
        rw [← hh1]
        exact this

/-- Projection on histories. -/
noncomputable def projectHistory {P P' : Set A} (h : P ⊆ P')
    (H' : History ↥P' Event) : History ↥P Event :=
  ⟨projectPreHistory h H'.val,
   projectPreHistory_isHereditarilyTransitive h H'.val H'.hered⟩

/-! ## §6. Sequentiality is preserved by projection

The main positive result: a participant `p ∈ ↥P` that is sequential in
the unprojected history is sequential (re-coordinated) in the projected
history. The proof structure mirrors `History.sequentiality_monotone`
(`Core/History.lean:500`) but the lifting step crosses subtypes via
`mem_projectPreHistory_iff` rather than via subset inclusion. -/

/-- **Sequentiality is preserved by grassroots projection.** If
`liftAgent h p` is sequential in `H'` (i.e. all of its event-tuples in
`H'` are linearly ordered by accessibility), then `p` is sequential in
`projectPreHistory h H'`. -/
theorem isSequential_projection
    {P P' : Set A} (h : P ⊆ P') (p : ↥P)
    (H' : PreHistory ↥P' Event)
    (hSeq : isSequential (liftAgent h p) H') :
    isSequential p (projectPreHistory h H') := by
  classical
  intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
  -- Step 1: lift each projected tuple to a witness in the original history.
  rw [mem_projectPreHistory_iff] at ht₁ ht₂
  obtain ⟨t₁', ht₁'P, hin₁', hproj₁⟩ := ht₁
  obtain ⟨t₂', ht₂'P, hin₂', hproj₂⟩ := ht₂
  -- Step 2: show the lifted places equal liftAgent h p.
  have hpp₁ : World.place t₁' = liftAgent h p := by
    -- hp₁ : World.place t₁ = p, and t₁ is the projection of t₁'
    have hFst : ((⟨t₁'.1.val, ht₁'P⟩ : ↥P), t₁'.2.1, projectPreHistory h t₁'.2.2).1
                = t₁.1 := by
      rw [hproj₁]
    have hPlace : (⟨t₁'.1.val, ht₁'P⟩ : ↥P) = p := by
      simp at hFst
      rw [hFst]
      exact hp₁
    -- Now ⟨t₁'.1.val, _⟩ = p, so t₁'.1 = liftAgent h p (extensionality on subtypes)
    change t₁'.1 = liftAgent h p
    apply Subtype.ext
    have := congrArg Subtype.val hPlace
    simp at this
    simpa using this
  have hpp₂ : World.place t₂' = liftAgent h p := by
    have hFst : ((⟨t₂'.1.val, ht₂'P⟩ : ↥P), t₂'.2.1, projectPreHistory h t₂'.2.2).1
                = t₂.1 := by
      rw [hproj₂]
    have hPlace : (⟨t₂'.1.val, ht₂'P⟩ : ↥P) = p := by
      simp at hFst
      rw [hFst]
      exact hp₂
    change t₂'.1 = liftAgent h p
    apply Subtype.ext
    have := congrArg Subtype.val hPlace
    simp at this
    simpa using this
  -- Step 3: apply sequentiality of H' at liftAgent h p.
  rcases hSeq hin₁' hin₂' hpp₁ hpp₂ with hlt | hgt | heq
  · -- Case t₁' ≪ t₂'. Push the projection through.
    left
    have hAcc :=
      accessible_project_of_accessible h ht₁'P ht₂'P hlt
    rw [hproj₁, hproj₂] at hAcc
    exact hAcc
  · -- Case t₂' ≪ t₁'. Symmetric.
    right; left
    have hAcc :=
      accessible_project_of_accessible h ht₂'P ht₁'P hgt
    rw [hproj₁, hproj₂] at hAcc
    exact hAcc
  · -- Case t₁' = t₂'. Their projections agree.
    right; right
    rw [← hproj₁, ← hproj₂]
    -- Goal: (⟨t₁'.1.val, ht₁'P⟩, t₁'.2.1, projectPreHistory h t₁'.2.2)
    --     = (⟨t₂'.1.val, ht₂'P⟩, t₂'.2.1, projectPreHistory h t₂'.2.2)
    -- which follows by congruence from heq : t₁' = t₂'
    subst heq
    rfl

/-- **Sequentiality is preserved by grassroots projection (history version).**
Wraps `isSequential_projection` to operate on `History` rather than the
underlying `PreHistory`. -/
theorem History_isSequential_project
    {P P' : Set A} (h : P ⊆ P') (p : ↥P)
    (H' : History ↥P' Event)
    (hSeq : isSequential (liftAgent h p) H'.val) :
    isSequential p (projectHistory h H').val :=
  isSequential_projection h p H'.val hSeq

end Grassroots
end ModalDistribution
