import ModalDistribution.LowerBound.Depth

/-!
# History constructions for the lower-bound argument

Unions of histories, the causal cone of a world as a history, downward-closed
sub-histories, singletons, and the empty history, each with its membership
characterization; plus the transfer of sequentiality between prehistories.
-/

namespace ModalDistribution.LowerBound
open scoped PreHistory

variable {P : Type} {E : Type}

/-- The underlying list of a prehistory. -/
def _root_.PreHistory.toList (h : PreHistory P E) : List (World P E) :=
  match h with
  | .mk l => l

theorem mem_toList {h : PreHistory P E} {t : World P E} : t ∈ h.toList ↔ t ∈ h := by
  cases h; exact Iff.rfl

/-- A list whose members' times are included in it and hereditarily transitive
spans a hereditarily transitive prehistory. -/
theorem hered_of_closed (l : List (World P E))
    (hsub : ∀ t ∈ l, World.time t ⊆ PreHistory.mk l)
    (hhered : ∀ t ∈ l, isHereditarilyTransitive (World.time t)) :
    isHereditarilyTransitive (PreHistory.mk l) := by
  rw [isHereditarilyTransitive_unfold]
  constructor
  · rintro h ⟨p, e, hmem⟩
    exact hsub (p, e, h) hmem
  · rintro h ⟨p, e, hmem⟩
    exact hhered (p, e, h) hmem

/-- Members of a history have hereditarily transitive times included in it. -/
theorem _root_.History.time_subset (H : History P E) {t : World P E} (ht : t ∈ H.val) :
    World.time t ⊆ H.val :=
  History.transitive H _ (History.happensBefore_of_mem ht)

theorem _root_.History.time_hered (H : History P E) {t : World P E} (ht : t ∈ H.val) :
    isHereditarilyTransitive (World.time t) :=
  isHereditarilyTransitive.desc H.hered (History.happensBefore_of_mem ht)

/-! ## Constructions -/

/-- The empty history. -/
def emptyHist : History P E :=
  ⟨.mk [], hered_of_closed [] (fun _ h => nomatch h) (fun _ h => nomatch h)⟩

theorem mem_emptyHist (t : World P E) : t ∉ (emptyHist : History P E).val := fun h => nomatch h

/-- The history of a single world with empty past. -/
def singleHist (p : P) (e : MaybeEvent E) : History P E :=
  ⟨.mk [(p, e, .mk [])], hered_of_closed _
    (by
      intro t ht u hu
      have : t = (p, e, PreHistory.mk []) := List.mem_singleton.mp ht
      subst this
      exact absurd hu (fun h => nomatch h))
    (by
      intro t ht
      have : t = (p, e, PreHistory.mk []) := List.mem_singleton.mp ht
      subst this
      exact emptyHist.hered)⟩

theorem mem_singleHist {p : P} {e : MaybeEvent E} {t : World P E} :
    t ∈ (singleHist p e).val ↔ t = (p, e, .mk []) := by
  show t ∈ [(p, e, PreHistory.mk [])] ↔ _
  exact List.mem_singleton

/-- The union of two histories. -/
def unionHist (H₁ H₂ : History P E) : History P E :=
  ⟨.mk (H₁.val.toList ++ H₂.val.toList), by
    apply hered_of_closed
    · intro t ht u hu
      rcases List.mem_append.mp ht with h | h
      · exact List.mem_append.mpr (Or.inl (mem_toList.mpr
          (H₁.time_subset (mem_toList.mp h) u hu)))
      · exact List.mem_append.mpr (Or.inr (mem_toList.mpr
          (H₂.time_subset (mem_toList.mp h) u hu)))
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact H₁.time_hered (mem_toList.mp h)
      · exact H₂.time_hered (mem_toList.mp h)⟩

theorem mem_unionHist {H₁ H₂ : History P E} {t : World P E} :
    t ∈ (unionHist H₁ H₂).val ↔ t ∈ H₁.val ∨ t ∈ H₂.val := by
  show t ∈ H₁.val.toList ++ H₂.val.toList ↔ _
  rw [List.mem_append, mem_toList, mem_toList]

/-- The causal cone of a member of a history, as a history. -/
def coneHist (H : History P E) (d : World P E) (hd : d ∈ H.val) : History P E :=
  ⟨cone d, by
    rcases d with ⟨p, e, l⟩
    cases l with
    | mk l =>
      apply hered_of_closed
      · intro t ht u hu
        rcases List.mem_cons.mp ht with rfl | ht
        · exact List.mem_cons_of_mem _ hu
        · have hsub : World.time t ⊆ PreHistory.mk l :=
            History.transitive (History.predecessorHistory (H := H)
              (History.happensBefore_of_mem hd)) _ (History.happensBefore_of_mem ht)
          exact List.mem_cons_of_mem _ (hsub u hu)
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact H.time_hered hd
        · exact (History.predecessorHistory (H := H)
            (History.happensBefore_of_mem hd)).time_hered ht⟩

theorem mem_coneHist {H : History P E} {d : World P E} {hd : d ∈ H.val} {t : World P E} :
    t ∈ (coneHist H d hd).val ↔ t = d ∨ t ≪ d := mem_cone

theorem coneHist_val {H : History P E} {d : World P E} {hd : d ∈ H.val} :
    (coneHist H d hd).val = cone d := rfl

/-- A downward-closed sub-history. -/
noncomputable def filterHist (H : History P E) (Pr : World P E → Prop)
    (hdown : ∀ t ∈ H.val, Pr t → ∀ u ∈ World.time t, Pr u) : History P E := by
  classical
  exact ⟨.mk (H.val.toList.filter (fun t => decide (Pr t))), by
    apply hered_of_closed
    · intro t ht u hu
      rw [List.mem_filter] at ht
      have ht' := mem_toList.mp ht.1
      have hPt : Pr t := of_decide_eq_true ht.2
      apply List.mem_filter.mpr
      refine ⟨mem_toList.mpr (H.time_subset ht' u hu), ?_⟩
      exact decide_eq_true (hdown t ht' hPt u hu)
    · intro t ht
      rw [List.mem_filter] at ht
      exact H.time_hered (mem_toList.mp ht.1)⟩

theorem mem_filterHist {H : History P E} {Pr : World P E → Prop} {hdown} {t : World P E} :
    t ∈ (filterHist H Pr hdown).val ↔ t ∈ H.val ∧ Pr t := by
  classical
  show t ∈ H.val.toList.filter _ ↔ _
  rw [List.mem_filter, mem_toList]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, of_decide_eq_true h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, decide_eq_true h2⟩

/-! ## Sequentiality transfer -/

/-- If all of `p`'s events in `H` lie in `H'`, sequentiality in `H'` gives
sequentiality in `H`. -/
theorem isSequential_of_events_in {p : P} {H H' : PreHistory P E}
    (h : ∀ t ∈ H, World.place t = p → t ∈ H')
    (hs : isSequential (Event := E) p H') : isSequential (Event := E) p H :=
  fun t₁ t₂ h₁ h₂ hp₁ hp₂ => hs t₁ t₂ (h t₁ h₁ hp₁) (h t₂ h₂ hp₂) hp₁ hp₂

end ModalDistribution.LowerBound
