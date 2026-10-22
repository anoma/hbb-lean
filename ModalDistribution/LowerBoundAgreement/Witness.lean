import ModalDistribution.LowerBoundAgreement.Vocabulary

/-!
# The witness model for the ThyAgreement depth lower bound

A causally monotone ThyAgreement model, parametric in the depth budget `D`, in which
learner `L = 0` realizes `maxDepth = D` while its quorum `Q = {0}` delivers at
world-depth exactly `D + 4`.

Participants are natural numbers. Participant `0` (`a₀`) is the only live one;
participants `1, …, D` (`e₁, …, e_D`) are equivocating proposers: each `eᵢ` has
two causally incomparable `propose` events (values `0` and `1`, both with empty
past). Participant `a₀` performs the chain

  `A 0 = propose 0`, `A 1 = echo 0`, `A (r+2) = vote 0 0 r` for `r ≤ D`,
  `A (D+3) = deliver 0 0`,

each seeing exactly the previous `A`-worlds, so the delivery is `Q`-only and has
depth `D + 4`. Afterwards `a₀` has `D + 1` silent worlds `A (D+3+i)`,
`i = 1, …, D+1`: the `i`-th (for `i ≤ D`) additionally sees both proposals of
`eᵢ`, exposing it as an equivocator. The history is the prehistory of all these
worlds.

Learner `l` has quorums `{O | 0 ∈ O ∧ l ∈ O}`. Learners `a, b ≤ D` are
correlated at a prehistory iff both are sequential there (and every learner is
correlated with itself), so the correlation relation is exposure-based, and the
row of `L` loses `eᵢ`'s learner at the `i`-th exposure: `D` row changes along
`a₀`'s chain, and no chain has more.
-/

namespace ModalDistribution.LowerBoundAgreement.Witness
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples ModalDistribution.Examples.ThyAgreement
open scoped Formula PreHistory
open PreHistory History World

@[simp] theorem symbols_live (D : Nat) : (symbols D).liveSymb = .live := rfl
@[simp] theorem symbols_corr (D : Nat) : (symbols D).correlationSymb = .corr := rfl
@[simp] theorem symbols_propose (D : Nat) : (symbols D).proposeSymb = .propose := rfl
@[simp] theorem symbols_echo (D : Nat) : (symbols D).echoSymb = .echo := rfl
@[simp] theorem symbols_vote (D n : Nat) : (symbols D).voteSymb n = .vote n := rfl
@[simp] theorem symbols_deliver (D : Nat) : (symbols D).deliverSymb = .deliver := rfl
@[simp] theorem symbols_depthBound (D l : Nat) : (symbols D).depthBound l = D := rfl

/-- Worlds and prehistories of the witness. -/
abbrev Wd := World Nat sig.EventType
abbrev Ph := PreHistory Nat sig.EventType

/-! ## The worlds -/

/-- The labels of `a₀`'s chain. -/
def lab (D : Nat) : Nat → MaybeEvent sig.EventType
  | 0 => .some ⟨.propose, [0]⟩
  | 1 => .some ⟨.echo, [0]⟩
  | k + 2 => if k ≤ D then .some ⟨.vote k, [0, 0]⟩
      else if k = D + 1 then .some ⟨.deliver, [0, 0]⟩ else †

/-- The equivocating proposals of `eᵢ`. -/
def Ew (i b : Nat) : Wd := (i, .some ⟨.propose, [b]⟩, .mk [])

/-- The proposals first seen at index `k` of `a₀`'s chain. -/
def newE (D k : Nat) : List Wd :=
  if 1 ≤ k - (D + 3) ∧ k - (D + 3) ≤ D then [Ew (k - (D + 3)) 0, Ew (k - (D + 3)) 1]
  else []

/-- The members of `a₀`'s `k`-th prehistory. -/
def entries (D : Nat) : Nat → List Wd
  | 0 => []
  | k + 1 => (0, lab D k, .mk (entries D k)) :: (newE D (k + 1) ++ entries D k)

/-- `a₀`'s `k`-th prehistory. -/
def TA (D k : Nat) : Ph := .mk (entries D k)

/-- `a₀`'s `k`-th world. -/
def A (D k : Nat) : Wd := (0, lab D k, TA D k)

@[simp] theorem mem_mk (t : Wd) (xs : List Wd) : t ∈ PreHistory.mk xs ↔ t ∈ xs := Iff.rfl

theorem mem_newE (D k : Nat) (t : Wd) :
    t ∈ newE D k ↔ ∃ i, 1 ≤ i ∧ i ≤ D ∧ D + 3 + i = k ∧ (t = Ew i 0 ∨ t = Ew i 1) := by
  unfold newE
  by_cases h : 1 ≤ k - (D + 3) ∧ k - (D + 3) ≤ D
  · rw [if_pos h]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro ht; exact ⟨k - (D + 3), h.1, h.2, by omega, ht⟩
    · rintro ⟨i, _, _, hi, ht⟩
      have : i = k - (D + 3) := by omega
      subst this; exact ht
  · rw [if_neg h]
    simp only [List.not_mem_nil, false_iff]
    rintro ⟨i, h1, h2, h3, _⟩
    exact h ⟨by omega, by omega⟩

theorem mem_TA (D k : Nat) (t : Wd) :
    t ∈ TA D k ↔ (∃ j, j < k ∧ t = A D j) ∨
      (∃ i, 1 ≤ i ∧ i ≤ D ∧ D + 3 + i ≤ k ∧ (t = Ew i 0 ∨ t = Ew i 1)) := by
  induction k with
  | zero =>
    simp only [TA, entries, mem_mk, List.not_mem_nil, false_iff, not_or]
    constructor
    · rintro ⟨j, hj, _⟩; omega
    · rintro ⟨i, _, _, h, _⟩; omega
  | succ k ih =>
    have hstep : t ∈ TA D (k + 1) ↔ t = A D k ∨ t ∈ newE D (k + 1) ∨ t ∈ TA D k := by
      change t ∈ (0, lab D k, .mk (entries D k)) :: (newE D (k + 1) ++ entries D k) ↔ _
      rw [List.mem_cons, List.mem_append]
      rfl
    rw [hstep, ih, mem_newE]
    constructor
    · rintro (rfl | ⟨i, h1, h2, h3, ht⟩ | ⟨j, hj, rfl⟩ | ⟨i, h1, h2, h3, ht⟩)
      · exact Or.inl ⟨k, by omega, rfl⟩
      · exact Or.inr ⟨i, h1, h2, by omega, ht⟩
      · exact Or.inl ⟨j, by omega, rfl⟩
      · exact Or.inr ⟨i, h1, h2, by omega, ht⟩
    · rintro (⟨j, hj, rfl⟩ | ⟨i, h1, h2, h3, ht⟩)
      · by_cases hjk : j = k
        · subst hjk; exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl ⟨j, by omega, rfl⟩))
      · by_cases hik : D + 3 + i = k + 1
        · exact Or.inr (Or.inl ⟨i, h1, h2, hik, ht⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨i, h1, h2, by omega, ht⟩))

theorem A_mem {D j k : Nat} (h : j < k) : A D j ∈ TA D k :=
  (mem_TA D k _).mpr (Or.inl ⟨j, h, rfl⟩)

theorem Ew_mem {D i k b : Nat} (h1 : 1 ≤ i) (h2 : i ≤ D) (h3 : D + 3 + i ≤ k) (hb : b ≤ 1) :
    Ew i b ∈ TA D k := by
  refine (mem_TA D k _).mpr (Or.inr ⟨i, h1, h2, h3, ?_⟩)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem TA_mono {D k k' : Nat} (h : k ≤ k') : TA D k ⊆ TA D k' := by
  intro t ht
  rcases (mem_TA D k t).mp ht with ⟨j, hj, rfl⟩ | ⟨i, h1, h2, h3, ht⟩
  · exact A_mem (by omega)
  · exact (mem_TA D k' t).mpr (Or.inr ⟨i, h1, h2, by omega, ht⟩)

@[simp] theorem A_place (D k : Nat) : (A D k).1 = 0 := rfl
@[simp] theorem A_time (D k : Nat) : (A D k).2.2 = TA D k := rfl
@[simp] theorem A_event (D k : Nat) : (A D k).2.1 = lab D k := rfl
@[simp] theorem Ew_place (i b : Nat) : (Ew i b).1 = i := rfl
@[simp] theorem Ew_time (i b : Nat) : (Ew i b).2.2 = PreHistory.mk [] := rfl
@[simp] theorem Ew_event (i b : Nat) : (Ew i b).2.1 = .some ⟨.propose, [b]⟩ := rfl

theorem TA_zero (D : Nat) : TA D 0 = PreHistory.mk [] := rfl

/-- Hereditary transitivity of every `TA D k`. -/
theorem hered (D : Nat) : ∀ k, isHereditarilyTransitive (TA D k) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rw [isHereditarilyTransitive_unfold]
    have key : ∀ h : Ph, h ≺− TA D k →
        (∃ j, j < k ∧ h = TA D j) ∨ (0 < k ∧ h = TA D 0) := by
      rintro h ⟨p, e, hmem⟩
      rcases (mem_TA D k _).mp hmem with ⟨j, hj, he⟩ | ⟨i, _, _, h3, he | he⟩
      · exact Or.inl ⟨j, hj, congrArg World.time he⟩
      · exact Or.inr ⟨by omega, congrArg World.time he⟩
      · exact Or.inr ⟨by omega, congrArg World.time he⟩
    constructor
    · intro h hh
      rcases key h hh with ⟨j, hj, rfl⟩ | ⟨_, rfl⟩
      · exact TA_mono (by omega)
      · exact TA_mono (by omega)
    · intro h hh
      rcases key h hh with ⟨j, hj, rfl⟩ | ⟨hk, rfl⟩
      · exact ih j hj
      · exact ih 0 hk

/-! ## Sequentiality -/

theorem A_ne_Ew (D j i b : Nat) (hi : 1 ≤ i) : A D j ≠ Ew i b := by
  intro h
  have := congrArg World.place h
  simp at this
  omega

theorem seq_zero (D k : Nat) : isSequential (Event := sig.EventType) 0 (TA D k) := by
  intro t₁ t₂ h₁ h₂ hp₁ hp₂
  have hA : ∀ t : Wd, t ∈ TA D k → t.place = 0 → ∃ j, j < k ∧ t = A D j := by
    intro t ht hp
    rcases (mem_TA D k t).mp ht with h | ⟨i, h1, _, _, rfl | rfl⟩
    · exact h
    · simp at hp; omega
    · simp at hp; omega
  obtain ⟨j₁, hj₁, rfl⟩ := hA t₁ h₁ hp₁
  obtain ⟨j₂, hj₂, rfl⟩ := hA t₂ h₂ hp₂
  rcases Nat.lt_trichotomy j₁ j₂ with h | h | h
  · exact Or.inl (A_mem h)
  · subst h; exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl (A_mem h))

theorem Ew_zero_ne_one (i : Nat) : Ew i 0 ≠ Ew i 1 := by
  intro h
  have := congrArg World.event h
  simp at this

theorem not_seq_exposed {D i k : Nat} (h1 : 1 ≤ i) (h2 : i ≤ D) (h3 : D + 3 + i ≤ k) :
    ¬ isSequential (Event := sig.EventType) i (TA D k) := by
  intro hseq
  rcases hseq (Ew i 0) (Ew i 1) (Ew_mem h1 h2 h3 (by omega)) (Ew_mem h1 h2 h3 (by omega))
      rfl rfl with h | h | h
  · exact (List.not_mem_nil (show Ew i 0 ∈ ([] : List Wd) from h)).elim
  · exact (List.not_mem_nil (show Ew i 1 ∈ ([] : List Wd) from h)).elim
  · exact Ew_zero_ne_one i h

theorem seq_unexposed {D i k : Nat} (hi : i ≠ 0) (h : ¬ (1 ≤ i ∧ i ≤ D ∧ D + 3 + i ≤ k)) :
    isSequential (Event := sig.EventType) i (TA D k) := by
  intro t₁ t₂ h₁ _ hp₁ _
  exfalso
  rcases (mem_TA D k t₁).mp h₁ with ⟨j, _, rfl⟩ | ⟨i', h1, h2, h3, rfl | rfl⟩
  · simp at hp₁; exact hi hp₁.symm
  · simp at hp₁; subst hp₁; exact h ⟨h1, h2, h3⟩
  · simp at hp₁; subst hp₁; exact h ⟨h1, h2, h3⟩

/-- Sequentiality at `TA D k`, for every participant. -/
theorem seq_iff (D k i : Nat) :
    isSequential (Event := sig.EventType) i (TA D k) ↔ ¬ (1 ≤ i ∧ i ≤ D ∧ D + 3 + i ≤ k) := by
  constructor
  · intro hs ⟨h1, h2, h3⟩; exact not_seq_exposed h1 h2 h3 hs
  · intro h
    by_cases hi : i = 0
    · subst hi; exact seq_zero D k
    · exact seq_unexposed hi h

/-! ## Height -/

theorem height_TA_ge (D : Nat) : ∀ k, k + 1 ≤ PreHistory.height (TA D k) := by
  intro k
  induction k with
  | zero =>
    have := worldDepth_pos (S := sig) (P := Nat) (0, †, TA D 0)
    simpa [worldDepth] using this
  | succ k ih =>
    have hlt : PreHistory.height (TA D k) < PreHistory.height (TA D (k + 1)) :=
      PreHistory.height_lt_of_happensBefore ⟨0, lab D k, A_mem (Nat.lt_succ_self k)⟩
    omega

theorem height_TA_le (D : Nat) : ∀ k, k ≤ D + 3 → PreHistory.height (TA D k) ≤ k + 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    have h : ∀ t ∈ ([] : List Wd), PreHistory.height t.2.2 ≤ 0 := by
      intro t ht; cases ht
    exact PreHistory.height_mk_le h
  | succ k ih =>
    intro hk
    apply PreHistory.height_mk_le
    intro t ht
    have ht' : t ∈ TA D (k + 1) := ht
    rcases (mem_TA D (k + 1) t).mp ht' with ⟨j, hj, rfl⟩ | ⟨i, h1, _, h3, _⟩
    · have := ih (by omega)
      show PreHistory.height (TA D j) ≤ k + 1
      have hmono : PreHistory.height (TA D j) ≤ PreHistory.height (TA D k) := by
        by_cases hjk : j = k
        · subst hjk; exact Nat.le_refl _
        · exact Nat.le_of_lt (PreHistory.height_lt_of_happensBefore
            ⟨0, lab D j, A_mem (by omega)⟩)
      omega
    · omega

theorem height_TA (D k : Nat) (hk : k ≤ D + 3) : PreHistory.height (TA D k) = k + 1 :=
  Nat.le_antisymm (height_TA_le D k hk) (height_TA_ge D k)


theorem height_TA_lt {D k k' : Nat} (h : k < k') :
    PreHistory.height (TA D k) < PreHistory.height (TA D k') :=
  PreHistory.height_lt_of_happensBefore ⟨0, lab D k, A_mem h⟩

theorem TA_inj {D k k' : Nat} (h : TA D k = TA D k') : k = k' := by
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · have := height_TA_lt (D := D) hlt; rw [h] at this; omega
  · exact heq
  · have := height_TA_lt (D := D) hgt; rw [h] at this; omega

/-! ## The model -/

/-- The end-of-time index: `a₀`'s worlds are `A D k` for `k < N D`. -/
def N (D : Nat) : Nat := 2 * D + 6

/-- The history of the witness. -/
def hist (D : Nat) : History Nat sig.EventType := ⟨TA D (N D), hered D _⟩

/-- Correlation at a prehistory: a learner with itself, or two learners `≤ D`
both sequential there. -/
def corr (D : Nat) (h : Ph) (a b : Nat) : Prop :=
  a = b ∨ (a ≤ D ∧ b ≤ D ∧ isSequential (Event := sig.EventType) a h ∧
    isSequential (Event := sig.EventType) b h)

/-- The predicate interpretation: `a₀` alone is live; `corr` as above. -/
def interp (D : Nat) (p : Nat) (h : Ph) : Set sig.AtomicPredType :=
  fun x => (x.sym = .live ∧ p = 0) ∨ (x.sym = .corr ∧ ∃ a b, x.args = [a, b] ∧ corr D h a b)

/-- Learner `l`'s quorums: the sets containing both `a₀` and `l`. -/
def quorums (l : Nat) : Semifilter Nat where
  quorums := fun O => 0 ∈ O ∧ l ∈ O
  nonempty := ⟨Set.univ, trivial, trivial⟩
  upwardClosed := fun {_ _} hO hsub => ⟨hsub hO.1, hsub hO.2⟩
  pairwiseInter := fun {_ _} hO hO' => ⟨0, hO.1, hO'.1⟩

/-- The witness model. -/
def model (D : Nat) : Model sig Nat where
  history := hist D
  predInterp := interp D
  learner := quorums

theorem hist_val (D : Nat) : (model D).history.val = TA D (N D) := rfl

/-! ## Semantics in the witness -/

theorem check_iff (D : Nat) (Q : Nat → Prop) (ls : List Nat) (acc : Set Nat) :
    Sat.check (model D) Q ls acc ↔ ∃ p ∈ acc, (∀ l ∈ ls, p = 0 ∨ p = l) ∧ Q p := by
  induction ls generalizing acc with
  | nil => simp [Sat.check]
  | cons l ls ih =>
    simp only [Sat.check]
    constructor
    · intro h
      obtain ⟨p, ⟨hacc, hO⟩, hls, hQ⟩ :=
        (ih _).mp (h (fun p => p = 0 ∨ p = l) ⟨Or.inl rfl, Or.inr rfl⟩)
      refine ⟨p, hacc, ?_, hQ⟩
      intro l' hl'
      rcases List.mem_cons.mp hl' with rfl | hl'
      · exact hO
      · exact hls l' hl'
    · rintro ⟨p, hacc, hls, hQ⟩ O hO
      refine (ih _).mpr ⟨p, ⟨hacc, ?_⟩, fun l' hl' => hls l' (List.mem_cons_of_mem _ hl'), hQ⟩
      rcases hls l (List.mem_cons_self ..) with rfl | rfl
      · exact hO.1
      · exact hO.2

theorem diamondPast_iff (D : Nat) (w : Wd) (ls : List Nat) (φ : Formula sig) :
    (⟪w⟫ ⊨[model D] ♢ᶠ↓[ls] φ) ↔
      ∃ t ∈ w.time, (∀ l ∈ ls, t.place = 0 ∨ t.place = l) ∧ (⟪t⟫ ⊨[model D] φ) := by
  change Sat.check (model D) (fun p' => Sat (model D) p' † w.time (↓ᶠ φ)) ls Set.univ ↔ _
  rw [check_iff]
  simp only [Set.mem_univ, true_and]
  constructor
  · rintro ⟨p, hls, hp⟩
    obtain ⟨t, ht, htp, hφ⟩ := (Sat.past (model D) ⟨p, †, w.time⟩ φ).mp hp
    refine ⟨t, ht, ?_, hφ⟩
    change t.place = p at htp
    rw [htp]; exact hls
  · rintro ⟨t, ht, hls, hφ⟩
    exact ⟨t.place, hls, (Sat.past (model D) ⟨t.place, †, w.time⟩ φ).mpr ⟨t, ht, rfl, hφ⟩⟩

theorem boxPast_iff (D : Nat) (w : Wd) (ls : List Nat) (φ : Formula sig) :
    (⟪w⟫ ⊨[model D] □ᶠ↓[ls] φ) ↔
      ∀ p, (∀ l ∈ ls, p = 0 ∨ p = l) →
        ∃ t ∈ w.time, t.place = p ∧ (⟪t⟫ ⊨[model D] φ) := by
  classical
  change ¬ Sat.check (model D) (fun p' => Sat (model D) p' † w.time (¬ᶠ ↓ᶠ φ)) ls Set.univ ↔ _
  rw [check_iff]
  simp only [Set.mem_univ, true_and, not_exists, not_and]
  constructor
  · intro h p hls
    have h2 : ⟪⟨p, †, w.time⟩⟫ ⊨[model D] ↓ᶠ φ :=
      Classical.byContradiction fun hc =>
        h p hls ((Sat.not (model D) ⟨p, †, w.time⟩ (↓ᶠ φ)).mpr hc)
    exact (Sat.past (model D) ⟨p, †, w.time⟩ φ).mp h2
  · intro h p hls hn
    obtain ⟨t, ht, htp, hφ⟩ := h p hls
    exact (Sat.not (model D) ⟨p, †, w.time⟩ (↓ᶠ φ)).mp hn
      ((Sat.past (model D) ⟨p, †, w.time⟩ φ).mpr ⟨t, ht, htp, hφ⟩)

theorem diamond_iff (D : Nat) (w : Wd) (ls : List Nat) (φ : Formula sig) :
    (⟪w⟫ ⊨[model D] ♢ᶠ[ls] φ) ↔
      ∃ p, (∀ l ∈ ls, p = 0 ∨ p = l) ∧ (⟪⟨p, †, w.time⟩⟫ ⊨[model D] φ) := by
  change Sat.check (model D) (fun p' => Sat (model D) p' † w.time φ) ls Set.univ ↔ _
  rw [check_iff]
  simp only [Set.mem_univ, true_and]
  exact Iff.rfl

theorem live_iff (D : Nat) (w : Wd) : (⟪w⟫ ⊨[model D] (symbols D).live) ↔ w.place = 0 := by
  change (Pred.live = Pred.live ∧ w.place = 0) ∨
    (Pred.live = Pred.corr ∧ ∃ a b, ([] : List Nat) = [a, b] ∧ corr D w.time a b) ↔ _
  simp

theorem corr_iff (D : Nat) (w : Wd) (a b : Nat) :
    Correlated (model D) Pred.corr w a b ↔ corr D w.time a b := by
  change (Pred.corr = Pred.live ∧ w.place = 0) ∨
    (Pred.corr = Pred.corr ∧ ∃ a' b', [a, b] = [a', b'] ∧ corr D w.time a' b') ↔ _
  simp only [reduceCtorEq, false_and, false_or, true_and, List.cons.injEq, and_true]
  constructor
  · rintro ⟨a', b', ⟨rfl, rfl⟩, h⟩; exact h
  · intro h; exact ⟨a, b, ⟨rfl, rfl⟩, h⟩

/-- Possible worlds have times `TA D k` with `k ≤ N D`. -/
theorem possible {D : Nat} {w : Wd} (hw : w.time ⪯ (model D).history.val) :
    ∃ k, k ≤ N D ∧ w.time = TA D k := by
  rcases (PreHistory.happensBeforeEq_iff _ _).1 hw with ⟨p, e, hmem⟩ | heq
  · rcases (mem_TA D (N D) _).mp hmem with ⟨j, hj, he⟩ | ⟨i, _, _, _, he | he⟩
    · exact ⟨j, by omega, congrArg World.time he⟩
    · exact ⟨0, by omega, congrArg World.time he⟩
    · exact ⟨0, by omega, congrArg World.time he⟩
  · exact ⟨N D, Nat.le_refl _, heq⟩

theorem TA_possible {D k : Nat} (hk : k ≤ N D) : TA D k ⪯ (model D).history.val := by
  by_cases h : k = N D
  · subst h; exact Or.inr rfl
  · exact Or.inl ⟨0, lab D k, A_mem (by omega)⟩

theorem isSequential_mono {p : Nat} {h h' : Ph} (hsub : h' ⊆ h)
    (hs : isSequential (Event := sig.EventType) p h) :
    isSequential (Event := sig.EventType) p h' :=
  fun t₁ t₂ h₁ h₂ hp₁ hp₂ => hs t₁ t₂ (hsub _ h₁) (hsub _ h₂) hp₁ hp₂

/-- Predecessors of a world with time `TA D k`. -/
theorem pred_of_time {D k : Nat} {u w : Wd} (hw : w.time = TA D k) (hu : u ≪ w) :
    (∃ j, j < k ∧ u = A D j) ∨ (∃ i b, 1 ≤ i ∧ i ≤ D ∧ b ≤ 1 ∧ u = Ew i b) := by
  have hmem : u ∈ TA D k := by rw [← hw]; exact hu
  rcases (mem_TA D k u).mp hmem with h | ⟨i, h1, h2, _, rfl | rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, 0, h1, h2, by omega, rfl⟩
  · exact Or.inr ⟨i, 1, h1, h2, by omega, rfl⟩

theorem time_subset_of_accessible {D : Nat} {u w : Wd}
    (hw : w.time ⪯ (model D).history.val) (hu : u ≪ w) : u.time ⊆ w.time := by
  obtain ⟨k, _, hk⟩ := possible hw
  rw [hk]
  rcases pred_of_time hk hu with ⟨j, hj, rfl⟩ | ⟨i, b, _, _, _, rfl⟩
  · exact TA_mono (by omega)
  · intro t ht; cases ht

theorem corr_mono {D : Nat} {u w : Wd} (hw : w.time ⪯ (model D).history.val) (hu : u ≪ w)
    {a b : Nat} (h : corr D w.time a b) : corr D u.time a b := by
  rcases h with rfl | ⟨ha, hb, sa, sb⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨ha, hb, isSequential_mono (time_subset_of_accessible hw hu) sa,
      isSequential_mono (time_subset_of_accessible hw hu) sb⟩

/-! ## Event worlds -/

theorem lab_cases {D j : Nat} {E : sig.EventType} (h : lab D j = .some E) :
    (j = 0 ∧ E = ⟨.propose, [0]⟩) ∨ (j = 1 ∧ E = ⟨.echo, [0]⟩) ∨
    (∃ r, r ≤ D ∧ j = r + 2 ∧ E = ⟨.vote r, [0, 0]⟩) ∨
    (j = D + 3 ∧ E = ⟨.deliver, [0, 0]⟩) := by
  match j, h with
  | 0, h => exact Or.inl ⟨rfl, by cases h; rfl⟩
  | 1, h => exact Or.inr (Or.inl ⟨rfl, by cases h; rfl⟩)
  | k + 2, h =>
    simp only [lab] at h
    by_cases hk : k ≤ D
    · rw [if_pos hk] at h
      exact Or.inr (Or.inr (Or.inl ⟨k, hk, rfl, by cases h; rfl⟩))
    · rw [if_neg hk] at h
      by_cases hk' : k = D + 1
      · rw [if_pos hk'] at h
        exact Or.inr (Or.inr (Or.inr ⟨by omega, by cases h; rfl⟩))
      · rw [if_neg hk'] at h
        cases h

theorem lab_some_le {D j : Nat} {E : sig.EventType} (h : lab D j = .some E) : j ≤ D + 3 := by
  rcases lab_cases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨r, hr, rfl, _⟩ | ⟨rfl, _⟩ <;> omega

/-- Worlds of the history carrying an event. -/
theorem event_mem {D k : Nat} {t : Wd} {E : sig.EventType} (ht : t ∈ TA D k)
    (he : t.event = .some E) :
    (∃ j, j ≤ D + 3 ∧ t = A D j ∧ lab D j = .some E) ∨
    (∃ i b, 1 ≤ i ∧ i ≤ D ∧ b ≤ 1 ∧ t = Ew i b ∧ E = ⟨.propose, [b]⟩) := by
  rcases (mem_TA D k t).mp ht with ⟨j, _, rfl⟩ | ⟨i, h1, h2, _, rfl | rfl⟩
  · have he' : lab D j = .some E := he
    exact Or.inl ⟨j, lab_some_le he', rfl, he'⟩
  · exact Or.inr ⟨i, 0, h1, h2, by omega, rfl, by cases he; rfl⟩
  · exact Or.inr ⟨i, 1, h1, h2, by omega, rfl, by cases he; rfl⟩

/-- Every event world of the history is already seen by `A D (2D+4)`. -/
theorem event_early {D k : Nat} {t : Wd} {E : sig.EventType} (ht : t ∈ TA D k)
    (he : t.event = .some E) : t ∈ TA D (2 * D + 4) := by
  rcases event_mem ht he with ⟨j, hj, rfl, _⟩ | ⟨i, b, h1, h2, hb, rfl, _⟩
  · exact A_mem (by omega)
  · exact Ew_mem h1 h2 (by omega) hb

theorem event_index {D : Nat} {w : Wd} {E : sig.EventType}
    (h : ⟪w⟫ ⊨[model D] Formula.ofEvent E) : w ∈ TA D (N D) ∧ w.event = .some E := by
  obtain ⟨he, hm⟩ := (Sat.ofEvent (model D) w E).mp h
  rcases w with ⟨p, e, H⟩
  change e = .some E at he
  subst e
  exact ⟨hm, rfl⟩

theorem actual {D k : Nat} (hk : k < N D) {E : sig.EventType} (hE : lab D k = .some E) :
    ⟪A D k⟫ ⊨[model D] Formula.ofEvent E := by
  refine (Sat.ofEvent (model D) (A D k) E).mpr ⟨hE, ?_⟩
  show (0, .some E, TA D k) ∈ TA D (N D)
  rw [← hE]
  exact A_mem hk

theorem propose_actual (D : Nat) : ⟪A D 0⟫ ⊨[model D] (symbols D).propose 0 :=
  actual (by show 0 < 2 * D + 6; omega) rfl

theorem echo_actual (D : Nat) : ⟪A D 1⟫ ⊨[model D] (symbols D).echo 0 :=
  actual (by show 1 < 2 * D + 6; omega) rfl

theorem vote_actual (D : Nat) {r : Nat} (hr : r ≤ D) :
    ⟪A D (r + 2)⟫ ⊨[model D] (symbols D).vote 0 0 r :=
  actual (by show r + 2 < 2 * D + 6; omega) (by simp [lab, hr])

theorem deliver_actual (D : Nat) : ⟪A D (D + 3)⟫ ⊨[model D] (symbols D).deliver 0 0 :=
  actual (by show D + 3 < 2 * D + 6; omega) (by
    show lab D (D + 1 + 2) = _
    simp [lab])

theorem propose_world {D : Nat} {w : Wd} {v : Nat} (h : ⟪w⟫ ⊨[model D] (symbols D).propose v) :
    (w = A D 0 ∧ v = 0) ∨ (∃ i, 1 ≤ i ∧ i ≤ D ∧ v ≤ 1 ∧ w = Ew i v) := by
  obtain ⟨hm, he⟩ := event_index h
  rcases event_mem hm he with ⟨j, _, rfl, hl⟩ | ⟨i, b, h1, h2, hb, rfl, hE⟩
  · rcases lab_cases hl with ⟨rfl, hE⟩ | ⟨_, hE⟩ | ⟨r, _, _, hE⟩ | ⟨_, hE⟩ <;> simp at hE
    exact Or.inl ⟨rfl, hE⟩
  · simp at hE
    subst hE
    exact Or.inr ⟨i, h1, h2, hb, rfl⟩

theorem echo_world {D : Nat} {w : Wd} {v : Nat} (h : ⟪w⟫ ⊨[model D] (symbols D).echo v) :
    w = A D 1 ∧ v = 0 := by
  obtain ⟨hm, he⟩ := event_index h
  rcases event_mem hm he with ⟨j, _, rfl, hl⟩ | ⟨i, b, _, _, _, rfl, hE⟩
  · rcases lab_cases hl with ⟨_, hE⟩ | ⟨rfl, hE⟩ | ⟨r, _, _, hE⟩ | ⟨_, hE⟩ <;> simp at hE
    exact ⟨rfl, hE⟩
  · simp at hE

theorem vote_world {D : Nat} {w : Wd} {l v n : Nat}
    (h : ⟪w⟫ ⊨[model D] (symbols D).vote l v n) :
    w = A D (n + 2) ∧ l = 0 ∧ v = 0 ∧ n ≤ D := by
  obtain ⟨hm, he⟩ := event_index h
  rcases event_mem hm he with ⟨j, _, rfl, hl⟩ | ⟨i, b, _, _, _, rfl, hE⟩
  · rcases lab_cases hl with ⟨_, hE⟩ | ⟨_, hE⟩ | ⟨r, hr, rfl, hE⟩ | ⟨_, hE⟩ <;> simp at hE
    obtain ⟨rfl, rfl, rfl⟩ := hE
    exact ⟨rfl, rfl, rfl, hr⟩
  · simp at hE

theorem deliver_world {D : Nat} {w : Wd} {l v : Nat}
    (h : ⟪w⟫ ⊨[model D] (symbols D).deliver l v) :
    w = A D (D + 3) ∧ l = 0 ∧ v = 0 := by
  obtain ⟨hm, he⟩ := event_index h
  rcases event_mem hm he with ⟨j, _, rfl, hl⟩ | ⟨i, b, _, _, _, rfl, hE⟩
  · rcases lab_cases hl with ⟨_, hE⟩ | ⟨_, hE⟩ | ⟨r, _, _, hE⟩ | ⟨rfl, hE⟩ <;> simp at hE
    exact ⟨rfl, hE.1, hE.2⟩
  · simp at hE


/-! ## Rows and depth -/

/-- The exposure level of `a₀`'s `k`-th prehistory: how many of `e₁, …, e_D` are
exposed there. -/
def lvl (D k : Nat) : Nat := min (k - (D + 3)) D

/-- The row of learner `l` at exposure level `e`. -/
def G (D l e b : Nat) : Prop :=
  l = b ∨ (l ≤ D ∧ b ≤ D ∧ (l = 0 ∨ e < l) ∧ (b = 0 ∨ e < b))

theorem seq_TA_iff_le {D k x : Nat} (hx : x ≤ D) :
    isSequential (Event := sig.EventType) x (TA D k) ↔ (x = 0 ∨ lvl D k < x) := by
  rw [seq_iff]; unfold lvl; omega

theorem corr_TA_iff (D k l b : Nat) : corr D (TA D k) l b ↔ G D l (lvl D k) b := by
  unfold corr G
  constructor
  · rintro (h | ⟨hl, hb, sl, sb⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hl, hb, (seq_TA_iff_le hl).mp sl, (seq_TA_iff_le hb).mp sb⟩
  · rintro (h | ⟨hl, hb, el, eb⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hl, hb, (seq_TA_iff_le hl).mpr el, (seq_TA_iff_le hb).mpr eb⟩

/-- The row of a learner at a world depends only on the world's exposure level. -/
theorem row_eq_G {D k : Nat} {w : Wd} (hw : w.time = TA D k) (l : Nat) :
    correlationRow (Correlated (model D) Pred.corr) l w = G D l (lvl D k) := by
  funext b
  apply propext
  show Correlated (model D) Pred.corr w l b ↔ _
  rw [corr_iff, hw, corr_TA_iff]

/-- No chain has more than `D` row changes. -/
theorem depthChain_le {D l n : Nat}
    (h : DepthChain (model D) (Correlated (model D) Pred.corr) l n) : n ≤ D := by
  obtain ⟨ws, hposs, hchain, hrows⟩ := h
  have hk : ∀ i, ∃ k, k ≤ N D ∧ (ws i).time = TA D k := fun i => possible (hposs i)
  let K : Fin (n + 1) → Nat := fun i => Classical.choose (hk i)
  have hK : ∀ i, (ws i).time = TA D (K i) := fun i => (Classical.choose_spec (hk i)).2
  have hmono : ∀ i j, i < j → lvl D (K i) < lvl D (K j) := by
    intro i j hij
    have hne : lvl D (K i) ≠ lvl D (K j) := by
      intro heq
      apply hrows i j hij
      rw [row_eq_G (hK i), row_eq_G (hK j), heq]
    have hle : K i ≤ K j := by
      rcases pred_of_time (hK j) (hchain i j hij) with ⟨m, hm, hm'⟩ | ⟨i', b, _, _, _, hE⟩
      · have : TA D (K i) = TA D m := by rw [← hK i, hm']; rfl
        have := TA_inj this; omega
      · have : TA D (K i) = TA D 0 := by rw [← hK i, hE]; rfl
        have := TA_inj this; omega
    have : lvl D (K i) ≤ lvl D (K j) := by unfold lvl; omega
    omega
  have hge : ∀ m (hm : m < n + 1), m ≤ lvl D (K ⟨m, hm⟩) := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih =>
      intro hm
      have h1 := hmono ⟨m, by omega⟩ ⟨m + 1, hm⟩ (by show m < m + 1; omega)
      have h2 := ih (by omega)
      omega
  have h1 := hge n (Nat.lt_succ_self n)
  have h2 : lvl D (K ⟨n, Nat.lt_succ_self n⟩) ≤ D := Nat.min_le_right _ _
  omega

/-- `a₀`'s worlds `A (D+3), …, A (2D+3)` form a chain with `D` row changes for `L`. -/
theorem depthChain_D (D : Nat) : DepthChain (model D) (Correlated (model D) Pred.corr) 0 D := by
  refine ⟨fun i => A D (D + 3 + i.val), ?_, ?_, ?_⟩
  · intro i
    have := i.isLt
    exact TA_possible (by show D + 3 + i.val ≤ 2 * D + 6; omega)
  · intro i j hij
    have hij' : i.val < j.val := hij
    exact A_mem (by omega)
  · intro i j hij
    have hij' : i.val < j.val := hij
    have hj := j.isLt
    rw [row_eq_G rfl, row_eq_G rfl]
    intro heq
    have hl : G D 0 (lvl D (D + 3 + i.val)) (i.val + 1) := by unfold G lvl; omega
    have hr : ¬ G D 0 (lvl D (D + 3 + j.val)) (i.val + 1) := by unfold G lvl; omega
    exact hr (heq ▸ hl)

theorem maxDepth_eq (D : Nat) : maxDepth (model D) (Correlated (model D) Pred.corr) 0 = D :=
  Nat.le_antisymm (depthChain_le (maxDepth_attained _ _ _)) (le_maxDepth (depthChain_D D))

/-! ## The liveness theory -/

/-- Any Knowledge body true at a world of `a₀` is true at a world seen by `A D (2D+5)`. -/
theorem early {D : Nat} {t : Wd} (_ht : t ∈ TA D (N D)) (hp : t.place = 0) {φ : Formula sig}
    (hφ : KnowledgeBody φ) (h : ⟪t⟫ ⊨[model D] φ) :
    ∃ u ∈ TA D (2 * D + 5), u.place = 0 ∧ (⟪u⟫ ⊨[model D] φ) := by
  have hlt : 2 * D + 4 < 2 * D + 5 := by omega
  cases hφ with
  | event E =>
    obtain ⟨hm, he⟩ := event_index h
    exact ⟨t, TA_mono (by omega) _ (event_early hm he), hp, h⟩
  | known E =>
    obtain ⟨t', _, _, hE⟩ := (diamondPast_iff D t [] _).mp h
    obtain ⟨hm, he⟩ := event_index hE
    refine ⟨A D (2 * D + 4), A_mem hlt, rfl, ?_⟩
    exact (diamondPast_iff D _ [] _).mpr
      ⟨t', event_early hm he, (fun _ hl => nomatch hl), hE⟩
  | quorum l E =>
    have h' := (boxPast_iff D t [l] _).mp h
    refine ⟨A D (2 * D + 4), A_mem hlt, rfl, ?_⟩
    apply (boxPast_iff D _ [l] _).mpr
    intro p hp'
    obtain ⟨t', _, htp, hE⟩ := h' p hp'
    obtain ⟨hm, he⟩ := event_index hE
    exact ⟨t', event_early hm he, htp, hE⟩

theorem live_iff' (D : Nat) (w : Wd) :
    (⟪w⟫ ⊨[model D] Formula.predicate0 Pred.live) ↔ w.place = 0 := live_iff D w

theorem sometime_at {D k : Nat} {w : Wd} (hw : w.place = 0) (hk : k < N D) {φ : Formula sig}
    (h : ⟪A D k⟫ ⊨[model D] φ) : ⟪w⟫ ⊨[model D] ↕ᶠ φ :=
  (Sat.sometime (model D) w φ).mpr ⟨A D k, A_mem hk, by rw [hw]; rfl, h⟩

theorem live_theory (D : Nat) : Theory.Valid (M := model D) (ThyLive Pred.live) := by
  have hlt : 2 * D + 5 < N D := by show 2 * D + 5 < 2 * D + 6; omega
  intro ax hax w hw
  rcases hax with rfl | rfl | ⟨ls, φ, ha, rfl⟩ | ⟨ls, φ, ha, rfl⟩
  · show ⟪w⟫ ⊨[model D] ((Formula.predicate0 Pred.live) ⇔ᶠ ⤒ᶠ (Formula.predicate0 Pred.live))
    apply Sat.and_intro
    · apply Sat.imp_intro
      intro h
      exact (Sat.atEnd (model D) w _).mpr ((live_iff' D _).mpr ((live_iff' D w).mp h))
    · apply Sat.imp_intro
      intro h
      exact (live_iff' D w).mpr
        ((live_iff' D ⟨w.place, †, (model D).history.val⟩).mp ((Sat.atEnd (model D) w _).mp h))
  · apply Sat.imp_intro
    intro h
    apply (Sat.seq (model D) w).mpr
    rw [(live_iff' D w).mp h]
    obtain ⟨k, _, hk⟩ := possible hw
    rw [hk]
    exact seq_zero D k
  · apply Sat.imp_intro
    intro h1
    apply Sat.imp_intro
    intro h2
    have hw0 := (live_iff' D w).mp h2
    obtain ⟨t, ht, _, hlφ⟩ := (diamondPast_iff D _ ls _).mp ((Sat.atEnd (model D) w _).mp h1)
    obtain ⟨hlt', hφt⟩ := (Sat.and (model D) t _ _).mp hlφ
    obtain ⟨u, hu, hu0, hφ⟩ := early ht ((live_iff' D t).mp hlt') ha hφt
    apply sometime_at hw0 hlt
    exact (diamondPast_iff D _ ls _).mpr ⟨u, hu, fun _ _ => Or.inl hu0, hφ⟩
  · apply Sat.imp_intro
    intro h1
    apply Sat.imp_intro
    intro h2
    have hw0 := (live_iff' D w).mp h2
    have h' := (boxPast_iff D _ ls _).mp ((Sat.atEnd (model D) w _).mp h1)
    obtain ⟨t, ht, _, hlφ⟩ := h' 0 (fun _ _ => Or.inl rfl)
    obtain ⟨hlt', hφt⟩ := (Sat.and (model D) t _ _).mp hlφ
    obtain ⟨u, hu, hu0, hφ⟩ := early ht ((live_iff' D t).mp hlt') ha hφt
    apply sometime_at hw0 hlt
    apply (boxPast_iff D _ ls _).mpr
    intro p hp
    by_cases hp0 : p = 0
    · subst hp0
      exact ⟨u, hu, hu0, hφ⟩
    · exfalso
      obtain ⟨t', _, ht'p, hl⟩ := h' p hp
      have := (live_iff' D t').mp ((Sat.and (model D) t' _ _).mp hl).1
      exact hp0 (ht'p ▸ this)

/-! ## The protocol rules -/

theorem corr_iff' (D : Nat) (w : Wd) (a b : Nat) :
    Correlated (model D) (symbols D).correlationSymb w a b ↔ corr D w.time a b :=
  corr_iff D w a b

/-- A certificate for learner `l` forces `l = 0`, `v = 0`: participant `l` must have
acted. -/
theorem cert_elim {D : Nat} {w : Wd} {l : Nat} {φ : Formula sig}
    (h : ⟪w⟫ ⊨[model D] □ᶠ↓[[l]] φ) : ∃ t ∈ w.time, t.place = l ∧ (⟪t⟫ ⊨[model D] φ) :=
  (boxPast_iff D w [l] φ).mp h l (fun _ hl' => Or.inr (List.mem_singleton.mp hl').symm)

theorem cert_intro {D k j : Nat} {w : Wd} (hw : w.time = TA D k) (hj : j < k) {φ : Formula sig}
    (h : ⟪A D j⟫ ⊨[model D] φ) : ⟪w⟫ ⊨[model D] □ᶠ↓[[0]] φ := by
  apply (boxPast_iff D w [0] φ).mpr
  intro p hp
  rcases hp 0 (List.mem_singleton.mpr rfl) with rfl | rfl
  · exact ⟨A D j, by rw [hw]; exact A_mem hj, rfl, h⟩
  · exact ⟨A D j, by rw [hw]; exact A_mem hj, rfl, h⟩

/-- A learner with a live quorum is `L = 0`: its quorums contain it, and only `a₀`
is live. -/
theorem live_quorum_zero {D l : Nat}
    (hQ : ∃ Q ∈ ((model D).learner l).quorums, ∀ p ∈ Q, ⟪finalWorld (model D) p⟫ ⊨[model D] (symbols D).live) :
    l = 0 := by
  obtain ⟨Q, hQ, hlive⟩ := hQ
  exact (live_iff D _).mp (hlive l hQ.2)

/-- Proposals for two values occur, so no proposal is unique (when `D ≥ 1`). -/
theorem not_unique_propose {D : Nat} (hD : 1 ≤ D) :
    ¬ UniqueOccurrence (model D) (symbols D).propose := by
  rintro ⟨v, _, huniq⟩
  have h0 : Occurs (model D) ((symbols D).propose 0) :=
    ⟨A D 0, A_mem (by show 0 < 2 * D + 6; omega), propose_actual D⟩
  have h1 : Occurs (model D) ((symbols D).propose 1) :=
    ⟨Ew 1 1, Ew_mem (Nat.le_refl 1) hD (by show D + 3 + 1 ≤ 2 * D + 6; omega) (Nat.le_refl 1),
      (Sat.ofEvent (model D) (Ew 1 1) _).mpr ⟨rfl,
        Ew_mem (Nat.le_refl 1) hD (by show D + 3 + 1 ≤ 2 * D + 6; omega) (Nat.le_refl 1)⟩⟩
  have h01 : (0 : Nat) = 1 := (huniq 0 h0).trans (huniq 1 h1).symm
  exact absurd h01 (by decide)

theorem protocol (D : Nat) : ProtocolCM (model D) (symbols D) := by
  have hN : ∀ k, k ≤ D + 3 → k < N D := by intro k hk; show k < 2 * D + 6; omega
  have hdel : ∀ p : Nat, p = 0 → OccursAt (model D) p ((symbols D).deliver 0 0) := by
    rintro p rfl
    exact ⟨A D (D + 3), A_mem (hN _ (Nat.le_refl _)), rfl, deliver_actual D⟩
  refine {
    thyLive := live_theory D
    depthBound_dominates := fun l => depthChain_le (maxDepth_attained _ _ _)
    correlationSeq := ?_
    correlationSymm := ?_
    correlationTrans := ?_
    correlationPast := ?_
    agreement := ?_
    livenessOne := ?_
    livenessTwo := ?_
    causalMonotone := fun {w} hw {a b} h {u} hu =>
      (corr_iff' D u a b).mpr (corr_mono hw hu ((corr_iff' D w a b).mp h)) }
  · intro w hw a b _
    obtain ⟨k, _, hk⟩ := possible hw
    apply (diamond_iff D w [a, b] _).mpr
    refine ⟨0, fun _ _ => Or.inl rfl, ?_⟩
    apply (Sat.seq (model D) _).mpr
    show isSequential (Event := sig.EventType) 0 w.time
    rw [hk]
    exact seq_zero D k
  · intro w _ a b h
    rcases (corr_iff' D w a b).mp h with rfl | ⟨ha, hb, sa, sb⟩
    · exact (corr_iff' D w a a).mpr (Or.inl rfl)
    · exact (corr_iff' D w b a).mpr (Or.inr ⟨hb, ha, sb, sa⟩)
  · intro w _ a b c h1 h2
    rcases (corr_iff' D w a b).mp h1 with hab | ⟨ha, _, sa, _⟩
    · subst hab; exact h2
    · rcases (corr_iff' D w b c).mp h2 with hbc | ⟨_, hc, _, sc⟩
      · subst hbc; exact h1
      · exact (corr_iff' D w a c).mpr (Or.inr ⟨ha, hc, sa, sc⟩)
  · intro w hw a b h u hu _
    exact (corr_iff' D u a b).mpr (corr_mono hw hu ((corr_iff' D w a b).mp h))
  · -- agreement: every delivery is `deliver 0 0`
    intro a b v u _ hv hu
    obtain ⟨d, _, hd⟩ := hv
    obtain ⟨e, _, he⟩ := hu
    obtain ⟨_, _, rfl⟩ := deliver_world hd
    obtain ⟨_, _, rfl⟩ := deliver_world he
    rfl
  · -- Liveness 1
    intro l v hQ hU hO p hp
    obtain rfl := live_quorum_zero hQ
    obtain rfl := (live_iff D _).mp hp
    obtain ⟨e, _, _, t, _, ht⟩ := hO
    rcases propose_world ht with ⟨_, rfl⟩ | ⟨i, hi, hiD, _, _⟩
    · exact hdel 0 rfl
    · exact absurd hU (not_unique_propose (by omega))
  · -- Liveness 2
    intro a b v _ hQ hD p hp
    obtain rfl := live_quorum_zero hQ
    obtain rfl := (live_iff D _).mp hp
    obtain ⟨d, _, hd⟩ := hD
    obtain ⟨_, _, rfl⟩ := deliver_world hd
    exact hdel 0 rfl

/-! ## The witness -/

/-- **Nonvacuity.** A topology, an exposure-based correlation relation, a learner
`L` with a proper quorum `Q`, and a causally monotone ThyAgreement model with budget `D`
in which `L` realizes depth `D` and `Q` delivers at world-depth `D + 4`. -/
theorem agreement_witness (D : Nat) :
    ∃ (P : Type) (_ : Nonempty P) (T : Topology sig P) (κ : Correlation sig P)
      (L : Nat) (Q : Set P),
      Q ∈ (T L).quorums ∧ (∃ q, q ∉ Q) ∧ ExposureBased κ ∧
      ∃ M' : Model sig P, ProtocolCM M' (symbols D) ∧
        M'.learner = T ∧ corrOf (symbols D) M' = κ ∧
        maxDepth M' (Correlated M' Pred.corr) L = D ∧
        (∀ w : World P sig.EventType, w.time ⪯ M'.history.val →
          Correlated M' Pred.corr w L L) ∧
        ∃ v : Nat, ∀ p ∈ Q, ∃ d ∈ M'.history.val, d.place = p ∧
          (⟪d⟫ ⊨[M'] (symbols D).deliver L v) ∧ worldDepth d = D + 4 := by
  refine ⟨Nat, inferInstance, quorums, fun _ h a b => corr D h a b, 0, fun p => p = 0,
    ⟨rfl, rfl⟩, ⟨1, fun h => Nat.one_ne_zero h⟩, ?_, model D, protocol D, rfl, ?_,
    maxDepth_eq D, fun w _ => (corr_iff D w 0 0).mpr (Or.inl rfl), 0, ?_⟩
  · refine ⟨fun a b E => a = b ∨ (a ≤ D ∧ b ≤ D ∧ a ∉ E ∧ b ∉ E), fun p h a b => ?_⟩
    show corr D h a b ↔ _
    unfold corr
    constructor
    · rintro (h | ⟨ha, hb, sa, sb⟩)
      · exact Or.inl h
      · exact Or.inr ⟨ha, hb, fun hn => hn sa, fun hn => hn sb⟩
    · rintro (h | ⟨ha, hb, na, nb⟩)
      · exact Or.inl h
      · exact Or.inr ⟨ha, hb, Classical.byContradiction fun hs => na hs,
          Classical.byContradiction fun hs => nb hs⟩
  · funext p h a b
    exact propext (corr_iff D ⟨p, †, h⟩ a b)
  · intro p hp
    have hp0 : p = 0 := hp
    subst hp0
    refine ⟨A D (D + 3), A_mem (by show D + 3 < 2 * D + 6; omega), rfl, deliver_actual D, ?_⟩
    show PreHistory.height (TA D (D + 3)) = D + 4
    rw [height_TA D (D + 3) (Nat.le_refl _)]

end ModalDistribution.LowerBoundAgreement.Witness
