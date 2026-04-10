import ModalDistribution.Core.Prehistory
import ModalDistribution.Core.History
import ModalDistribution.Grassroots.Sequentiality

/-!
# Lifting HBB prehistories along participant-set inclusions

This file defines the *dual* of `Grassroots/Sequentiality.lean`'s
`projectPreHistory` operation: a lift `liftPreHistory h : PreHistory ↥P
Event → PreHistory ↥P' Event` that takes a prehistory over the smaller
participant subtype and re-tags every agent reference using `liftAgent h`.

Unlike projection (which can drop tuples whose place is not in the
smaller set), lifting is total: every tuple survives, just with its
agent-component lifted to the larger subtype. So the lifted prehistory
contains exactly the lifts of the original tuples — no more, no fewer.

## Why we need this

For the semantic preservation meta-theorem
`IsLiftable φ → (M_P ⊨ φ) → (canonicalLift F h M_P ⊨ φ)`, we need a
canonical way to "lift" an HBB model from `↥P` to `↥P'`. The history
component of that lift is `liftPreHistory h M_P.history.val`. This file
provides the construction and the basic structural lemmas.

The `Sequentiality.lean` file gives us the dual *projection* operation
(for the grassroots non-interference / Shapiro safety direction). This
file gives us the *lift* (for the canonical lifting direction needed by
`IsLiftable.preserved_by_lift`).

## Main definitions

* `liftPreHistory h : PreHistory ↥P Event → PreHistory ↥P' Event` — the
  structural lift over the underlying list of event-tuples.
* `liftHistory h : History ↥P Event → History ↥P' Event` — wraps
  `liftPreHistory` and preserves hereditary transitivity.
* `liftWorld h : World ↥P Event → World ↥P' Event` — lifts an
  event-tuple by re-tagging its agent component and recursively lifting
  its time component.

## Main theorems

* `mem_liftPreHistory_of_mem` — `t ∈ H` implies `liftWorld h t ∈ liftPreHistory h H`.
* `mem_liftPreHistory_iff_lifted_of_mem` — the converse: every member of
  `liftPreHistory h H` is `liftWorld h t` for some `t ∈ H`.
* `liftPreHistory_isHereditarilyTransitive` — lifting preserves
  hereditary transitivity.
* `liftHistory` — the lifted history-structure.
* `projectPreHistory_liftPreHistory_eq` — the round-trip identity:
  projecting the lift recovers the original.
* `isSequential_lift` — sequentiality at a participant is preserved by
  lifting (the dual of `isSequential_projection` from
  `Sequentiality.lean`).
-/

namespace ModalDistribution
namespace Grassroots

open scoped PreHistory

universe u v
variable {A : Type u} {Event : Type v}

/-! ## §1. The lift operation

Mutual structural recursion: lifting a list of tuples handles each tuple
by lifting its agent and recursively lifting its time component. Lifting
a prehistory unwraps the constructor and applies the list-level lift.

Unlike `projectPreHistory`, this is total — there is no `if-then-else`
to skip tuples — so we don't need `Classical` or `noncomputable`. -/

mutual

/-- List-level helper for `liftPreHistory`: re-tag each tuple's agent
via `liftAgent` and recursively lift its time component. -/
def liftListAux {P P' : Set A} (h : P ⊆ P') :
    List (World ↥P Event) → List (World ↥P' Event)
  | [] => []
  | (a, e, t) :: rest =>
      (liftAgent h a, e, liftPreHistory h t) :: liftListAux h rest

/-- The lift of a prehistory along the inclusion `P ⊆ P'`: every tuple
survives, with its agent component re-tagged via `liftAgent` and its time
component recursively lifted. -/
def liftPreHistory {P P' : Set A} (h : P ⊆ P') :
    PreHistory ↥P Event → PreHistory ↥P' Event
  | .mk l => .mk (liftListAux h l)

end

/-! ## §2. Unfolding lemmas -/

@[simp] lemma liftPreHistory_mk {P P' : Set A} (h : P ⊆ P')
    (l : List (World ↥P Event)) :
    liftPreHistory h (PreHistory.mk l) = PreHistory.mk (liftListAux h l) := rfl

@[simp] lemma liftListAux_nil {P P' : Set A} (h : P ⊆ P') :
    liftListAux (P := P) (P' := P') (Event := Event) h [] = [] := rfl

@[simp] lemma liftListAux_cons {P P' : Set A} (h : P ⊆ P')
    (a : ↥P) (e : MaybeEvent Event) (t : PreHistory ↥P Event)
    (rest : List (World ↥P Event)) :
    liftListAux h ((a, e, t) :: rest) =
      (liftAgent h a, e, liftPreHistory h t) :: liftListAux h rest := rfl

/-! ## §3. Lifting individual worlds -/

/-- Lift a single event-tuple by lifting its agent and recursively
lifting its time component. -/
@[simp] def liftWorld {P P' : Set A} (h : P ⊆ P')
    (t : World ↥P Event) : World ↥P' Event :=
  (liftAgent h t.1, t.2.1, liftPreHistory h t.2.2)

@[simp] lemma liftWorld_mk {P P' : Set A} (h : P ⊆ P')
    (a : ↥P) (e : MaybeEvent Event) (t : PreHistory ↥P Event) :
    liftWorld h (a, e, t) = (liftAgent h a, e, liftPreHistory h t) := rfl

/-! ## §4. Membership: forward direction -/

/-- If `t` is in the original list, its lift is in the lifted list. -/
lemma mem_liftListAux_of_mem {P P' : Set A} (h : P ⊆ P')
    {t : World ↥P Event} {l : List (World ↥P Event)}
    (htMem : t ∈ l) :
    liftWorld h t ∈ liftListAux h l := by
  induction l with
  | nil => cases htMem
  | cons head rest ih =>
      rcases head with ⟨a, e, t'⟩
      rw [liftListAux_cons]
      rcases List.mem_cons.mp htMem with heq | hRest
      · subst heq
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hRest)

/-- If `t ∈ H` then `liftWorld h t ∈ liftPreHistory h H`. -/
lemma mem_liftPreHistory_of_mem {P P' : Set A} (h : P ⊆ P')
    {t : World ↥P Event} {H : PreHistory ↥P Event}
    (htMem : t ∈ H) :
    liftWorld h t ∈ liftPreHistory h H := by
  cases H with
  | mk l =>
      rw [liftPreHistory_mk]
      have hl : t ∈ l := by simpa [PreHistory.mem_mk] using htMem
      have hLifted := mem_liftListAux_of_mem h hl
      simpa [PreHistory.mem_mk] using hLifted

/-! ## §5. Membership: characterisation -/

/-- Every member of `liftListAux h l` is `liftWorld h t` for some `t ∈ l`.
This is the converse to `mem_liftListAux_of_mem`. -/
lemma exists_mem_of_mem_liftListAux {P P' : Set A} (h : P ⊆ P')
    {s : World ↥P' Event} {l : List (World ↥P Event)}
    (hsMem : s ∈ liftListAux h l) :
    ∃ t : World ↥P Event, t ∈ l ∧ liftWorld h t = s := by
  induction l with
  | nil =>
      simp [liftListAux_nil] at hsMem
  | cons head rest ih =>
      rcases head with ⟨a, e, t'⟩
      rw [liftListAux_cons] at hsMem
      rcases List.mem_cons.mp hsMem with heq | hRest
      · subst heq
        exact ⟨(a, e, t'), List.mem_cons_self, rfl⟩
      · obtain ⟨t, htMem, htEq⟩ := ih hRest
        exact ⟨t, List.mem_cons_of_mem _ htMem, htEq⟩

/-- Membership iff at the list level. -/
lemma mem_liftListAux_iff {P P' : Set A} (h : P ⊆ P')
    (s : World ↥P' Event) (l : List (World ↥P Event)) :
    s ∈ liftListAux h l ↔
      ∃ t : World ↥P Event, t ∈ l ∧ liftWorld h t = s := by
  constructor
  · exact exists_mem_of_mem_liftListAux h
  · rintro ⟨t, htMem, rfl⟩
    exact mem_liftListAux_of_mem h htMem

/-- Membership characterisation for the lifted prehistory. -/
lemma mem_liftPreHistory_iff {P P' : Set A} (h : P ⊆ P')
    (s : World ↥P' Event) (H : PreHistory ↥P Event) :
    s ∈ liftPreHistory h H ↔
      ∃ t : World ↥P Event, t ∈ H ∧ liftWorld h t = s := by
  cases H with
  | mk l =>
      rw [liftPreHistory_mk]
      simp only [PreHistory.mem_mk]
      exact mem_liftListAux_iff h s l

/-! ## §6. Hereditary transitivity preservation -/

/-- Lifting preserves the (single-level) transitivity property. -/
lemma isTransitive_lift {P P' : Set A} (h : P ⊆ P')
    {H : PreHistory ↥P Event} (hH : isTransitive H) :
    isTransitive (liftPreHistory h H) := by
  classical
  intro h₁ hbefore
  -- hbefore : h₁ ≺− liftPreHistory h H
  rcases hbefore with ⟨p, e, hin⟩
  -- (p, e, h₁) ∈ liftPreHistory h H, so (p, e, h₁) is the lift of some (p₀, e, t₀) ∈ H.
  rw [mem_liftPreHistory_iff] at hin
  obtain ⟨t₀, ht₀Mem, ht₀Eq⟩ := hin
  -- t₀ : World ↥P Event, ht₀Mem : t₀ ∈ H,
  -- ht₀Eq : liftWorld h t₀ = (p, e, h₁)
  rcases t₀ with ⟨p₀, e₀, t₀H⟩
  -- liftWorld h (p₀, e₀, t₀H) = (liftAgent h p₀, e₀, liftPreHistory h t₀H)
  -- so p = liftAgent h p₀, e = e₀, h₁ = liftPreHistory h t₀H
  simp only [liftWorld_mk, Prod.mk.injEq] at ht₀Eq
  obtain ⟨_, _, hh1Eq⟩ := ht₀Eq
  -- hh1Eq : liftPreHistory h t₀H = h₁
  -- t₀H ≺− H by membership of (p₀, e₀, t₀H) in H
  have hbeforeOrig : t₀H ≺− H := ⟨p₀, e₀, ht₀Mem⟩
  -- transitivity of H gives t₀H ⊆ H
  have hsub : t₀H ⊆ H := hH _ hbeforeOrig
  -- Now show: h₁ ⊆ liftPreHistory h H.
  -- Equivalently: every member of h₁ is in liftPreHistory h H.
  intro u hu
  -- u ∈ h₁ = liftPreHistory h t₀H, so u = liftWorld h v for some v ∈ t₀H
  rw [← hh1Eq] at hu
  rw [mem_liftPreHistory_iff] at hu
  obtain ⟨v, hvMem, hvEq⟩ := hu
  -- v ∈ t₀H ⊆ H, so v ∈ H
  rw [mem_liftPreHistory_iff]
  exact ⟨v, hsub _ hvMem, hvEq⟩

/-- Lifting preserves hereditary transitivity. The proof is by
well-founded induction on the underlying prehistory using
`PreHistory.happensBefore_wellFounded`. -/
theorem liftPreHistory_isHereditarilyTransitive
    {P P' : Set A} (h : P ⊆ P')
    (H : PreHistory ↥P Event)
    (hH : isHereditarilyTransitive H) :
    isHereditarilyTransitive (liftPreHistory h H) := by
  classical
  induction H using
    (PreHistory.happensBefore_wellFounded (P := ↥P) (Event := Event)).induction with
  | _ H ih =>
      have hUnfold := (isHereditarilyTransitive_unfold H).mp hH
      have hTransH : isTransitive H := hUnfold.1
      have hHeredDesc : ∀ ⦃h₀ : PreHistory ↥P Event⦄,
          h₀ ≺− H → isHereditarilyTransitive h₀ := hUnfold.2
      rw [isHereditarilyTransitive_unfold]
      refine ⟨?_, ?_⟩
      · -- transitivity of liftPreHistory h H
        exact isTransitive_lift h hTransH
      · -- every predecessor of liftPreHistory h H is hereditarily transitive
        intro h₁ hbefore
        rcases hbefore with ⟨p, e, hin⟩
        rw [mem_liftPreHistory_iff] at hin
        obtain ⟨t₀, ht₀Mem, ht₀Eq⟩ := hin
        rcases t₀ with ⟨p₀, e₀, t₀H⟩
        simp only [liftWorld_mk, Prod.mk.injEq] at ht₀Eq
        obtain ⟨_, _, hh1Eq⟩ := ht₀Eq
        -- t₀H ≺− H so by hHeredDesc, t₀H is hereditarily transitive
        have hbeforeOrig : t₀H ≺− H := ⟨p₀, e₀, ht₀Mem⟩
        have hHeredt₀H := hHeredDesc hbeforeOrig
        -- by ih, lift of t₀H is hereditarily transitive
        have hLiftedHered := ih t₀H hbeforeOrig hHeredt₀H
        -- and h₁ = liftPreHistory h t₀H
        rw [← hh1Eq]
        exact hLiftedHered

/-! ## §7. Wrapping in History -/

/-- Lift a `History` (a hereditarily-transitive prehistory). -/
def liftHistory {P P' : Set A} (h : P ⊆ P')
    (H : History ↥P Event) : History ↥P' Event :=
  ⟨liftPreHistory h H.val,
   liftPreHistory_isHereditarilyTransitive h H.val H.hered⟩

/-- Unfolding lemma for `liftHistory.val`. -/
@[simp] lemma liftHistory_val {P P' : Set A} (h : P ⊆ P')
    (H : History ↥P Event) :
    (liftHistory h H).val = liftPreHistory h H.val := rfl

/-! ## §8. liftAgent injectivity

A small helper: `liftAgent h` is injective on its `.val` component, so
two lifted agents with equal images are equal as subtype elements. -/

lemma liftAgent_injective {P P' : Set A} (h : P ⊆ P') :
    Function.Injective (liftAgent h : ↥P → ↥P') := by
  intro a b hab
  apply Subtype.ext
  have : (liftAgent h a).val = (liftAgent h b).val := congrArg Subtype.val hab
  simpa [liftAgent] using this

/-! ## §9. Sequentiality is preserved by lifting

The dual of `isSequential_projection` from `Sequentiality.lean`. -/

/-- Sequentiality at a participant is preserved by lifting: if `p` is
sequential in `H`, then `liftAgent h p` is sequential in `liftPreHistory h H`. -/
theorem isSequential_lift {P P' : Set A} (h : P ⊆ P') (p : ↥P)
    (H : PreHistory ↥P Event)
    (hSeq : isSequential p H) :
    isSequential (liftAgent h p) (liftPreHistory h H) := by
  classical
  intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
  -- Each tᵢ is in liftPreHistory h H, so it lifts from some sᵢ ∈ H.
  rw [mem_liftPreHistory_iff] at ht₁ ht₂
  obtain ⟨s₁, hs₁Mem, hs₁Eq⟩ := ht₁
  obtain ⟨s₂, hs₂Mem, hs₂Eq⟩ := ht₂
  -- s₁'s place lifts to p, hence s₁'s place IS p (by liftAgent injectivity).
  have hps₁ : World.place s₁ = p := by
    have hPlaceLifted : liftAgent h (World.place s₁) = liftAgent h p := by
      have hFst : (liftWorld h s₁).1 = t₁.1 := by rw [hs₁Eq]
      have : liftAgent h (World.place s₁) = (liftWorld h s₁).1 := by
        simp [liftWorld, World.place]
      rw [this, hFst]
      exact hp₁
    exact liftAgent_injective h hPlaceLifted
  have hps₂ : World.place s₂ = p := by
    have hPlaceLifted : liftAgent h (World.place s₂) = liftAgent h p := by
      have hFst : (liftWorld h s₂).1 = t₂.1 := by rw [hs₂Eq]
      have : liftAgent h (World.place s₂) = (liftWorld h s₂).1 := by
        simp [liftWorld, World.place]
      rw [this, hFst]
      exact hp₂
    exact liftAgent_injective h hPlaceLifted
  -- Apply sequentiality at p in H.
  rcases hSeq hs₁Mem hs₂Mem hps₁ hps₂ with hlt | hgt | heq
  · -- s₁ ≪ s₂, i.e. s₁ ∈ time s₂. Lift: t₁ = liftWorld h s₁ ∈ time t₂.
    left
    have : liftWorld h s₁ ∈ World.time (liftWorld h s₂) := by
      change liftWorld h s₁ ∈ liftPreHistory h (World.time s₂)
      exact mem_liftPreHistory_of_mem h hlt
    rw [hs₁Eq, hs₂Eq] at this
    exact this
  · right; left
    have : liftWorld h s₂ ∈ World.time (liftWorld h s₁) := by
      change liftWorld h s₂ ∈ liftPreHistory h (World.time s₁)
      exact mem_liftPreHistory_of_mem h hgt
    rw [hs₁Eq, hs₂Eq] at this
    exact this
  · right; right
    rw [← hs₁Eq, ← hs₂Eq, heq]

/-- The history-level version. -/
theorem History_isSequential_lift {P P' : Set A} (h : P ⊆ P') (p : ↥P)
    (H : History ↥P Event)
    (hSeq : isSequential p H.val) :
    isSequential (liftAgent h p) (liftHistory h H).val := by
  rw [liftHistory_val]
  exact isSequential_lift h p H.val hSeq

end Grassroots
end ModalDistribution
