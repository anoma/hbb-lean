import ModalDistribution.LowerBound.Histories

/-!
# The stage schedule

Given the causal cone `X` of the delivery and the fuses `q 1, q 2, …`, the
adversary adds `X` to its constructed executions in stages: `Y 1 = ∅`, and
`Y (t+2)` is the largest downward-closed subset of `X` containing no event of
`q (t+1)` outside `Y (t+1)` — so that `q (t+1)`, which becomes live at stage
`t+1`, is never exposed by events added at stage `t+2`.

The key fact (`Y_depth`): an event of `X` outside `Y (t+1)` lies above a chain
`x₁ ≪ x₂ ≪ ⋯ ≪ x_t` of events by `q 1, …, q t`, hence has causal depth at least
`t`. So a cone of depth `n` is covered by `Y (n+2)` (`cone_subset_Y`).
-/

namespace ModalDistribution.LowerBound
open scoped PreHistory

variable {P : Type} {E : Type}

/-- The stage schedule. -/
def Y (q : Nat → P) (X : History P E) : Nat → Set (World P E)
  | 0 => fun _ => False
  | 1 => fun _ => False
  | t + 2 => fun e => e ∈ X.val ∧
      ¬ ∃ x : World P E, (x ≪ e ∨ x = e) ∧ World.place x = q (t + 1) ∧ x ∉ Y q X (t + 1)

theorem height_pos (h : PreHistory P E) : 1 ≤ PreHistory.height h := by
  cases h with
  | mk l => show _ + 1 ≥ 1; omega

variable (q : Nat → P) (X : History P E)

theorem Y_subset : ∀ t, ∀ e ∈ Y q X t, e ∈ X.val
  | 0, _, h => nomatch h
  | 1, _, h => nomatch h
  | _ + 2, _, h => h.1

/-- Each stage is downward closed. -/
theorem Y_down : ∀ t, ∀ e ∈ Y q X t, ∀ u, u ≪ e → u ∈ Y q X t
  | 0, _, h, _, _ => nomatch h
  | 1, _, h, _, _ => nomatch h
  | t + 2, e, ⟨he, hno⟩, u, hu => by
    refine ⟨X.time_subset he u hu, ?_⟩
    rintro ⟨x, hx, hxq, hxY⟩
    apply hno
    refine ⟨x, ?_, hxq, hxY⟩
    rcases hx with hx | rfl
    · exact Or.inl (accessible_trans (H := X) (PreHistory.happensBeforeEq_of_mem he) hx hu)
    · exact Or.inl hu

theorem Y_mono : ∀ t, ∀ e ∈ Y q X t, e ∈ Y q X (t + 1)
  | 0, _, h => nomatch h
  | 1, _, h => nomatch h
  | t + 2, e, he => by
    refine ⟨he.1, ?_⟩
    rintro ⟨x, hx, _, hxY⟩
    apply hxY
    rcases hx with hx | rfl
    · exact Y_down q X (t + 2) e he x hx
    · exact he

theorem Y_mono_le {t t' : Nat} (h : t ≤ t') : ∀ e ∈ Y q X t, e ∈ Y q X t' := by
  induction h with
  | refl => intro e he; exact he
  | step _ ih => intro e he; exact Y_mono q X _ e (ih e he)

/-- Events of `q (t+1)` in `Y (t+2)` were already in `Y (t+1)`. -/
theorem Y_avoid (t : Nat) (e : World P E) (he : e ∈ Y q X (t + 2))
    (hq : World.place e = q (t + 1)) : e ∈ Y q X (t + 1) :=
  Classical.byContradiction fun h => he.2 ⟨e, Or.inr rfl, hq, h⟩

/-- An event outside `Y (t+1)` sits above an event of `q t` of depth `≥ t`. -/
theorem Y_depth (hq : Function.Injective q) : ∀ t, 1 ≤ t → ∀ e ∈ X.val, e ∉ Y q X (t + 1) →
    ∃ x : World P E, (x ≪ e ∨ x = e) ∧ x ∈ X.val ∧ World.place x = q t ∧ t ≤ PreHistory.height (World.time x)
  | 0, h, _, _, _ => absurd h (by omega)
  | 1, _, e, he, hne => by
    have : ∃ x : World P E, (x ≪ e ∨ x = e) ∧ World.place x = q 1 ∧ x ∉ Y q X 1 :=
      Classical.byContradiction fun hc => hne ⟨he, hc⟩
    obtain ⟨x, hx, hxq, _⟩ := this
    refine ⟨x, hx, ?_, hxq, ?_⟩
    · rcases hx with hx | rfl
      · exact X.time_subset he x hx
      · exact he
    · exact height_pos _
  | t + 2, _, e, he, hne => by
    have : ∃ x : World P E, (x ≪ e ∨ x = e) ∧ World.place x = q (t + 2) ∧ x ∉ Y q X (t + 2) :=
      Classical.byContradiction fun hc => hne ⟨he, hc⟩
    obtain ⟨x, hx, hxq, hxY⟩ := this
    have hxX : x ∈ X.val := by
      rcases hx with hx | rfl
      · exact X.time_subset he x hx
      · exact he
    obtain ⟨y, hy, _, hyq, hyd⟩ := Y_depth hq (t + 1) (by omega) x hxX hxY
    have hyx : y ≪ x := by
      rcases hy with hy | rfl
      · exact hy
      · exfalso
        have : q (t + 1) = q (t + 2) := hyq.symm.trans hxq
        have := hq this
        omega
    have := PreHistory.height_lt_of_accessible hyx
    exact ⟨x, hx, hxX, hxq, by omega⟩

/-- Events of depth `< t` are in `Y (t+1)`. -/
theorem Y_covers (hq : Function.Injective q) (t : Nat) (ht : 1 ≤ t) (e : World P E)
    (he : e ∈ X.val) (hd : PreHistory.height (World.time e) < t) : e ∈ Y q X (t + 1) := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨x, hx, _, _, hxd⟩ := Y_depth q X hq t ht e he hne
  rcases hx with hx | rfl
  · have := PreHistory.height_lt_of_accessible hx; omega
  · omega

end ModalDistribution.LowerBound
