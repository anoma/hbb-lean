import ModalDistribution.Examples.ThyHBB4.Depth

namespace ModalDistribution.Examples.ThyHBB4

open scoped PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {R : World P S.EventType → S.Value → S.Value → Prop}

/-- The earlier row strictly contains the later row. -/
def StrictRow (R : World P S.EventType → S.Value → S.Value → Prop)
    (a : S.Value) (e w : World P S.EventType) : Prop :=
  (∀ b, R w a b → R e a b) ∧ ∃ b, R e a b ∧ ¬ R w a b

/-- Unlike an arbitrary distinct-row chain, this chain retains strict inclusion. -/
def StrictEndingDepthChain (M : Model S P)
    (R : World P S.EventType → S.Value → S.Value → Prop)
    (a : S.Value) (w : World P S.EventType) (n : Nat) : Prop :=
  ∃ ws : Fin (n + 1) → World P S.EventType,
    (∀ i, (ws i).time ⪯ M.history.val) ∧
    (∀ i j, i < j → ws i ≪ ws j) ∧
    (∀ i j, i < j → StrictRow R a (ws i) (ws j)) ∧
    (∀ i, ∃ b, R (ws i) a b) ∧ ws (Fin.last n) = w

theorem strictEndingDepthChain_zero {a : S.Value} {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) (hne : ∃ b, R w a b) :
    StrictEndingDepthChain M R a w 0 := by
  refine ⟨fun _ => w, fun _ => hw, ?_, ?_, fun _ => hne, rfl⟩
  all_goals
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hij' : i.val < j.val := hij
    omega

theorem strictEndingDepthChain_le {a : S.Value} {w : World P S.EventType} {n : Nat}
    (h : StrictEndingDepthChain M R a w n) : n + 1 ≤ maxDepth M R a := by
  obtain ⟨ws, hp, hc, hr, _, _⟩ := h
  apply le_maxDepth
  refine ⟨ws, hp, hc, ?_⟩
  intro i j hij heq
  obtain ⟨b, hbi, hbj⟩ := (hr i j hij).2
  exact hbj (Eq.mp (congrFun heq b) hbi)

theorem strictEndingDepthChain_append {a : S.Value} {e w : World P S.EventType} {n : Nat}
    (chain : StrictEndingDepthChain M R a e n) (hew : e ≪ w)
    (hw : w.time ⪯ M.history.val) (hrow : StrictRow R a e w)
    (hne : ∃ b, R w a b) : StrictEndingDepthChain M R a w (n + 1) := by
  obtain ⟨ws, hp, hc, hr, hn, hend⟩ := chain
  have old : ∀ i, ws i ≪ e ∨ ws i = e := by
    intro i
    by_cases hi : i.val < n
    · left
      rw [← hend]
      exact hc i (Fin.last n) hi
    · right
      rw [Fin.eq_last_of_not_lt hi, hend]
  have oldrow : ∀ i, StrictRow R a (ws i) w := by
    intro i
    have hincl : ∀ b, R e a b → R (ws i) a b := by
      intro b hb
      by_cases hi : i.val < n
      · exact (hr i (Fin.last n) hi).1 b (hend ▸ hb)
      · simpa only [Fin.eq_last_of_not_lt hi, hend] using hb
    refine ⟨fun b hb => hincl b (hrow.1 b hb), ?_⟩
    obtain ⟨b, hbe, hbw⟩ := hrow.2
    exact ⟨b, hincl b hbe, hbw⟩
  refine ⟨Fin.lastCases w ws, ?_, ?_, ?_, ?_, Fin.lastCases_last⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hw
    · simpa using hp j
  · intro i j hij
    revert hij
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hij
      have hj := j.isLt
      have hij' : n + 1 < j.val := hij
      omega
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro _
        simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
        rcases old i with hi | hi
        · exact accessible_trans hw hi hew
        · simpa [hi] using hew
      · intro hij
        simpa using hc i j (Fin.castSucc_lt_castSucc_iff.mp hij)
  · intro i j hij
    revert hij
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hij
      have hj := j.isLt
      have hij' : n + 1 < j.val := hij
      omega
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · intro _
        simpa using oldrow i
      · intro hij
        simpa using hr i j (Fin.castSucc_lt_castSucc_iff.mp hij)
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hne
    · simpa using hn j

end ModalDistribution.Examples.ThyHBB4
