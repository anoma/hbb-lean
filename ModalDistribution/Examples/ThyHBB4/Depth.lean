import ModalDistribution.Core.Model

namespace ModalDistribution.Examples.ThyHBB4

open scoped PreHistory

variable {S : Signature} {P : Type _} [Nonempty P]

/-- The correlation row at a world for an anchor learner. -/
def correlationRow (R : World P S.EventType → S.Value → S.Value → Prop)
    (a : S.Value) (w : World P S.EventType) : S.Value → Prop := R w a

/-- A chain of possible worlds whose anchor correlation rows are pairwise distinct.
The length counts worlds, including the final world. -/
def DepthChain (M : Model S P)
    (R : World P S.EventType → S.Value → S.Value → Prop)
    (a : S.Value) (n : Nat) : Prop :=
  ∃ ws : Fin n → World P S.EventType,
    (∀ i, World.time (ws i) ⪯ M.history.val) ∧
    (∀ i j, i < j → ws i ≪ ws j) ∧
    (∀ i j, i < j → correlationRow R a (ws i) ≠ correlationRow R a (ws j))

theorem depthChain_zero (M : Model S P)
    (R : World P S.EventType → S.Value → S.Value → Prop) (a : S.Value) :
    DepthChain M R a 0 := by
  exact ⟨Fin.elim0, (fun i => Fin.elim0 i),
    (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩

/-- History height bounds every chain, independently of the size of the learner type. -/
theorem depthChain_bounded {M : Model S P}
    {R : World P S.EventType → S.Value → S.Value → Prop} {a : S.Value} {n : Nat}
    (h : DepthChain M R a n) : n ≤ PreHistory.height M.history.val + 1 := by
  obtain ⟨ws, hpossible, hchain, _⟩ := h
  have lower : ∀ (k : Nat) (hk : k < n),
      k ≤ PreHistory.height (World.time (ws ⟨k, hk⟩)) := by
    intro k
    induction k with
    | zero => intro hk; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hprev := ih hk'
      have hstep := PreHistory.height_lt_of_accessible
        (hchain ⟨k, hk'⟩ ⟨k + 1, hk⟩ (by show k < k + 1; omega))
      omega
  cases n with
  | zero => omega
  | succ n =>
    have hn : n < n + 1 := by omega
    have hlo := lower n hn
    have hhi : PreHistory.height (World.time (ws ⟨n, hn⟩)) ≤
        PreHistory.height M.history.val := by
      rcases (PreHistory.happensBeforeEq_iff _ _).1 (hpossible ⟨n, hn⟩) with hlt | heq
      · exact Nat.le_of_lt (PreHistory.height_lt_of_happensBefore hlt)
      · rw [heq]
        exact Nat.le_refl _
    omega

private theorem bounded_maximum (A : Nat → Prop) (bound : Nat)
    (hzero : A 0) (hbound : ∀ n, A n → n ≤ bound) :
    ∃ n, A n ∧ ∀ k, A k → k ≤ n := by
  classical
  induction bound with
  | zero => exact ⟨0, hzero, hbound⟩
  | succ b ih =>
    by_cases hb : A (b + 1)
    · exact ⟨b + 1, hb, hbound⟩
    · apply ih
      intro n hn
      have hle := hbound n hn
      have hne : n ≠ b + 1 := by intro heq; subst n; exact hb hn
      omega

theorem exists_maxDepth (M : Model S P)
    (R : World P S.EventType → S.Value → S.Value → Prop) (a : S.Value) :
    ∃ n, DepthChain M R a n ∧ ∀ k, DepthChain M R a k → k ≤ n := by
  exact bounded_maximum (DepthChain M R a) (PreHistory.height M.history.val + 1)
    (depthChain_zero M R a) (fun _ h => depthChain_bounded h)

/-- The actual maximum chain length of the model, not a supplied proof budget. -/
noncomputable def maxDepth (M : Model S P)
    (R : World P S.EventType → S.Value → S.Value → Prop) (a : S.Value) : Nat :=
  Classical.choose (exists_maxDepth M R a)

theorem maxDepth_attained (M : Model S P)
    (R : World P S.EventType → S.Value → S.Value → Prop) (a : S.Value) :
    DepthChain M R a (maxDepth M R a) :=
  (Classical.choose_spec (exists_maxDepth M R a)).1

theorem le_maxDepth {M : Model S P}
    {R : World P S.EventType → S.Value → S.Value → Prop} {a : S.Value} {n : Nat}
    (h : DepthChain M R a n) : n ≤ maxDepth M R a :=
  (Classical.choose_spec (exists_maxDepth M R a)).2 n h

/-- Every model has a possible final world, hence a one-world chain. -/
theorem depthChain_one (M : Model S P)
    (R : World P S.EventType → S.Value → S.Value → Prop) (a : S.Value) :
    DepthChain M R a 1 := by
  classical
  refine ⟨fun _ => (Classical.choice inferInstance, MaybeEvent.none, M.history.val), ?_, ?_, ?_⟩
  · intro i
    exact PreHistory.happensBeforeEq_refl _
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hij' : i.val < j.val := hij
    omega
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hij' : i.val < j.val := hij
    omega

theorem maxDepth_pos (M : Model S P)
    (R : World P S.EventType → S.Value → S.Value → Prop) (a : S.Value) :
    0 < maxDepth M R a :=
  le_maxDepth (depthChain_one M R a)

theorem maxDepth_bounded (M : Model S P)
    (R : World P S.EventType → S.Value → S.Value → Prop) (a : S.Value) :
    maxDepth M R a ≤ PreHistory.height M.history.val + 1 :=
  depthChain_bounded (maxDepth_attained M R a)

/-- A chain of `n + 1` distinct rows ending at the designated world. -/
def EndingDepthChain (M : Model S P)
    (R : World P S.EventType → S.Value → S.Value → Prop)
    (a : S.Value) (w : World P S.EventType) (n : Nat) : Prop :=
  ∃ ws : Fin (n + 1) → World P S.EventType,
    (∀ i, World.time (ws i) ⪯ M.history.val) ∧
    (∀ i j, i < j → ws i ≪ ws j) ∧
    (∀ i j, i < j → correlationRow R a (ws i) ≠ correlationRow R a (ws j)) ∧
    ws (Fin.last n) = w

theorem endingDepthChain_le {M : Model S P}
    {R : World P S.EventType → S.Value → S.Value → Prop} {a : S.Value}
    {w : World P S.EventType} {n : Nat} (h : EndingDepthChain M R a w n) :
    n + 1 ≤ maxDepth M R a := by
  obtain ⟨ws, hp, hc, hr, _⟩ := h
  exact le_maxDepth ⟨ws, hp, hc, hr⟩

theorem endingDepthChain_zero {M : Model S P}
    (R : World P S.EventType → S.Value → S.Value → Prop) (a : S.Value)
    {w : World P S.EventType} (hw : World.time w ⪯ M.history.val) :
    EndingDepthChain M R a w 0 := by
  refine ⟨fun _ => w, fun _ => hw, ?_, ?_, rfl⟩
  all_goals
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    have hij' : i.val < j.val := hij
    omega

theorem endingDepthChain_append {M : Model S P}
    {R : World P S.EventType → S.Value → S.Value → Prop} {a : S.Value}
    {e w : World P S.EventType} {n : Nat}
    (h : EndingDepthChain M R a e n) (hew : e ≪ w)
    (hw : World.time w ⪯ M.history.val)
    (hrows : ∀ u, (u ≪ e ∨ u = e) → correlationRow R a u ≠ correlationRow R a w) :
    EndingDepthChain M R a w (n + 1) := by
  obtain ⟨ws, hp, hc, hr, hend⟩ := h
  have old : ∀ i, ws i ≪ e ∨ ws i = e := by
    intro i
    by_cases hi : i.val < n
    · left
      rw [← hend]
      exact hc i (Fin.last n) hi
    · right
      rw [Fin.eq_last_of_not_lt hi, hend]
  refine ⟨Fin.lastCases w ws, ?_, ?_, ?_, Fin.lastCases_last⟩
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
        simpa using hrows (ws i) (old i)
      · intro hij
        simpa using hr i j (Fin.castSucc_lt_castSucc_iff.mp hij)

end ModalDistribution.Examples.ThyHBB4
