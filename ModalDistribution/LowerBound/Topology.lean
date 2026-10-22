import ModalDistribution.LowerBound.Statement

/-!
# The adversary's topology and correlation relation

For the depth lower bound the adversary fixes, from injections `f : ℕ → P`
(participants) and `g : ℕ → Value` (learners/values) and the depth `D`:

* the hub `c = f 0` and the fuses `qᵢ = f i` for `1 ≤ i ≤ D`;
* the learner `L = g 0` with quorum `Q = {q₁, …, q_D}`, and learners `Lᵢ = g i`
  with quorums `{qᵢ, c}`; every other learner has quorum `{c}` (quorums are the
  supersets of these bases);
* the correlation relation `κ`: every learner is correlated with itself; `L` and
  the `Lᵢ` are correlated with each other exactly when their fuses are
  sequential in the observed prehistory (`L` needs no fuse) — exposing `qᵢ` as
  an equivocator disconnects `Lᵢ`, and nothing else.

`EnvOK` for a model on `(T, κ)` reduces to: at every possible time, the hub is
sequential and some fuse is sequential (`envOK_of`). `κ` is causally monotone
because sequentiality is inherited by causal predecessors.
-/

namespace ModalDistribution.LowerBound
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples.ThyHBB4 (ProtocolSignature maxDepth maxDepth_attained correlationRow)
open scoped Formula PreHistory

variable {S : Signature} {P : Type}

/-- The adversary's parameters. -/
structure Params (S : Signature) (P : Type) where
  f : Nat → P
  g : Nat → S.Value
  D : Nat
  f_inj : Function.Injective f
  g_inj : Function.Injective g
  D_pos : 1 ≤ D

namespace Params

variable (π : Params S P)

/-- Fuse indices. -/
def isFuse (i : Nat) : Prop := 1 ≤ i ∧ i ≤ π.D

/-- The base of learner `l`'s quorums. -/
def base (l : S.Value) : Set P :=
  fun p => (l ≠ π.g 0 ∧ p = π.f 0) ∨ ∃ i, π.isFuse i ∧ p = π.f i ∧ (l = π.g 0 ∨ l = π.g i)

theorem base_nonempty (l : S.Value) : ∃ p, p ∈ π.base l := by
  by_cases h : l = π.g 0
  · exact ⟨π.f 1, Or.inr ⟨1, ⟨Nat.le_refl 1, π.D_pos⟩, rfl, Or.inl h⟩⟩
  · exact ⟨π.f 0, Or.inl ⟨h, rfl⟩⟩

/-- The topology: learner `l`'s quorums are the supersets of `base l`. -/
def T (l : S.Value) : Semifilter P where
  quorums := fun O => ∀ p ∈ π.base l, p ∈ O
  nonempty := ⟨Set.univ, fun _ _ => trivial⟩
  upwardClosed := fun {_ _} hO hsub p hp => hsub (hO p hp)
  pairwiseInter := fun {O O'} hO hO' => by
    obtain ⟨q, hq⟩ := π.base_nonempty l
    exact ⟨q, hO q hq, hO' q hq⟩

/-- `L`'s quorum `Q = {q₁, …, q_D}`. -/
def Q : Set P := π.base (π.g 0)

theorem mem_Q {p : P} : p ∈ π.Q ↔ ∃ i, π.isFuse i ∧ p = π.f i := by
  constructor
  · rintro (⟨h, _⟩ | ⟨i, hi, rfl, _⟩)
    · exact absurd rfl h
    · exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact Or.inr ⟨i, hi, rfl, Or.inl rfl⟩

theorem Q_quorum : π.Q ∈ (π.T (π.g 0)).quorums := fun _ hp => hp

theorem g_ne {i j : Nat} (h : i ≠ j) : π.g i ≠ π.g j := fun e => h (π.g_inj e)
theorem f_ne {i j : Nat} (h : i ≠ j) : π.f i ≠ π.f j := fun e => h (π.f_inj e)

theorem fuse_ne_zero {i : Nat} (hi : π.isFuse i) : i ≠ 0 := by
  intro h; have := hi.1; omega

theorem isSequential_mono {p : P} {h h' : PreHistory P S.EventType} (hsub : h' ⊆ h)
    (hs : isSequential (Event := S.EventType) p h) :
    isSequential (Event := S.EventType) p h' :=
  fun t₁ t₂ h₁ h₂ hp₁ hp₂ => hs t₁ t₂ (hsub _ h₁) (hsub _ h₂) hp₁ hp₂

/-- The quorum base of a fuse learner. -/
theorem mem_base_fuse {i : Nat} (hi : π.isFuse i) {p : P} :
    p ∈ π.base (π.g i) ↔ p = π.f i ∨ p = π.f 0 := by
  constructor
  · rintro (⟨_, rfl⟩ | ⟨j, _, rfl, h | h⟩)
    · exact Or.inr rfl
    · exact absurd h (π.g_ne (π.fuse_ne_zero hi))
    · rw [π.g_inj h]; exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact Or.inr ⟨i, hi, rfl, Or.inr rfl⟩
    · exact Or.inl ⟨π.g_ne (π.fuse_ne_zero hi), rfl⟩

theorem fuse_quorum {i : Nat} (hi : π.isFuse i) :
    (fun p => p = π.f i ∨ p = π.f 0) ∈ (π.T (π.g i)).quorums :=
  fun _ hp => (π.mem_base_fuse hi).mp hp

/-- A learner whose fuse (if any) is intact. -/
def fuseOk (h : PreHistory P S.EventType) (a : S.Value) : Prop :=
  a = π.g 0 ∨ ∃ i, π.isFuse i ∧ a = π.g i ∧ isSequential (Event := S.EventType) (π.f i) h

/-- The correlation relation. -/
def κ : Correlation S P := fun _ h a b => a = b ∨ (π.fuseOk h a ∧ π.fuseOk h b)

/-- `EnvOK` at a single time, for models on `(T, κ)`. -/
def EnvOKAt (h : PreHistory P S.EventType) : Prop :=
  isSequential (Event := S.EventType) (π.f 0) h ∧
    ∃ i, π.isFuse i ∧ isSequential (Event := S.EventType) (π.f i) h

/-! ## Models on `(T, κ)` -/

variable [Nonempty P] {σ : ProtocolSignature S}

theorem correlated_iff {M : Model S P} (hκ : corrOf σ M = π.κ) (w : World P S.EventType)
    (a b : S.Value) : Correlated M σ.correlationSymb w a b ↔ π.κ w.place w.time a b := by
  have := congrFun (congrFun (congrFun (congrFun hκ w.place) w.time) a) b
  exact Iff.of_eq this

/-- The time of a predecessor of a possible world is included in the world's time. -/
theorem time_subset_of_accessible {M : Model S P} {u w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) (hu : u ≪ w) : u.time ⊆ w.time := by
  have hbefore : u.time ≺− w.time :=
    PreHistory.happensBefore_of_accessible (P := P) (Event := S.EventType) hu
  have htrans : isTransitive (World.time w) := by
    rcases (PreHistory.happensBeforeEq_iff _ _).1 hw with hlt | heq
    · exact (History.predecessor_data (H := M.history) hlt).1
    · rw [heq]; exact History.transitive M.history
  exact htrans _ hbefore

omit [Nonempty P] in
theorem fuseOk_mono {h h' : PreHistory P S.EventType} (hsub : h' ⊆ h) {a : S.Value}
    (ha : π.fuseOk h a) : π.fuseOk h' a := by
  rcases ha with ha | ⟨i, hi, rfl, hs⟩
  · exact Or.inl ha
  · exact Or.inr ⟨i, hi, rfl, isSequential_mono hsub hs⟩

/-- `κ` is causally monotone. -/
theorem causallyMonotone : CausallyMonotone σ π.κ := by
  intro M hκ w hw a b hab u hu
  rw [π.correlated_iff hκ] at hab ⊢
  have hsub := time_subset_of_accessible hw hu
  rcases hab with h | ⟨ha, hb⟩
  · exact Or.inl h
  · exact Or.inr ⟨π.fuseOk_mono hsub ha, π.fuseOk_mono hsub hb⟩

/-- `EnvOK` follows from `EnvOKAt` at every possible time. -/
theorem envOK_of {M : Model S P} (hT : M.learner = π.T) (hκ : corrOf σ M = π.κ)
    (h : ∀ t : PreHistory P S.EventType, t ⪯ M.history.val → π.EnvOKAt t) : EnvOK σ M := by
  intro w hw a b hab
  obtain ⟨hc, i, hi, hqi⟩ := h w.time hw
  rw [π.correlated_iff hκ] at hab
  -- a common sequential member of the two bases
  have key : ∃ p, p ∈ π.base a ∧ p ∈ π.base b ∧ isSequential (Event := S.EventType) p w.time := by
    rcases hab with rfl | ⟨ha, hb⟩
    · by_cases h0 : a = π.g 0
      · subst h0; exact ⟨π.f i, Or.inr ⟨i, hi, rfl, Or.inl rfl⟩, Or.inr ⟨i, hi, rfl, Or.inl rfl⟩, hqi⟩
      · exact ⟨π.f 0, Or.inl ⟨h0, rfl⟩, Or.inl ⟨h0, rfl⟩, hc⟩
    · rcases ha with rfl | ⟨i, hi, rfl, hsi⟩
      · rcases hb with rfl | ⟨j, hj, rfl, hsj⟩
        · exact ⟨π.f i, Or.inr ⟨i, hi, rfl, Or.inl rfl⟩, Or.inr ⟨i, hi, rfl, Or.inl rfl⟩, hqi⟩
        · exact ⟨π.f j, Or.inr ⟨j, hj, rfl, Or.inl rfl⟩, Or.inr ⟨j, hj, rfl, Or.inr rfl⟩, hsj⟩
      · rcases hb with rfl | ⟨j, hj, rfl, hsj⟩
        · exact ⟨π.f i, Or.inr ⟨i, hi, rfl, Or.inr rfl⟩, Or.inr ⟨i, hi, rfl, Or.inl rfl⟩, hsi⟩
        · exact ⟨π.f 0, Or.inl ⟨π.g_ne (π.fuse_ne_zero hi), rfl⟩,
            Or.inl ⟨π.g_ne (π.fuse_ne_zero hj), rfl⟩, hc⟩
  obtain ⟨p, hpa, hpb, hps⟩ := key
  change Sat.check M (fun p => isSequential (Event := S.EventType) p w.time) [a, b] Set.univ
  intro O hO O' hO'
  rw [hT] at hO hO'
  exact ⟨p, ⟨⟨trivial, hO p hpa⟩, hO' p hpb⟩, hps⟩

/-- Conversely, `EnvOK` on `(T, κ)` yields `EnvOKAt` at every possible time: take the
pairs `(L, L)` and `(l, l)` for a learner `l = g (D+1)` that is neither `L` nor a
fuse learner. -/
theorem envOKAt_of_envOK {M : Model S P} (hT : M.learner = π.T) (hκ : corrOf σ M = π.κ)
    (hEnv : EnvOK σ M) {t : PreHistory P S.EventType} (ht : t ⪯ M.history.val) :
    π.EnvOKAt t := by
  have p₀ : P := Classical.ofNonempty
  have key : ∀ a : S.Value, ∃ p, p ∈ π.base a ∧ isSequential (Event := S.EventType) p t := by
    intro a
    have hcorr : Correlated M σ.correlationSymb (p₀, †, t) a a :=
      (π.correlated_iff hκ (p₀, †, t) a a).mpr (Or.inl rfl)
    have hseq := hEnv (w := (p₀, †, t)) ht hcorr
    change Sat.check M (fun p => isSequential (Event := S.EventType) p t) [a, a] Set.univ at hseq
    have hbase : π.base a ∈ (M.learner a).quorums := by rw [hT]; exact fun _ hp => hp
    obtain ⟨p, ⟨⟨_, hp⟩, _⟩, hps⟩ := hseq (π.base a) hbase (π.base a) hbase
    exact ⟨p, hp, hps⟩
  constructor
  · obtain ⟨p, hp, hps⟩ := key (π.g (π.D + 1))
    rcases hp with ⟨_, rfl⟩ | ⟨i, hi, _, h | h⟩
    · exact hps
    · exact absurd (π.g_inj h) (by omega)
    · exact absurd (π.g_inj h) (by have := hi.2; omega)
  · obtain ⟨p, hp, hps⟩ := key (π.g 0)
    rcases hp with ⟨h, _⟩ | ⟨i, hi, rfl, _⟩
    · exact absurd rfl h
    · exact ⟨i, hi, hps⟩

/-- `κ` is coherent in every model carrying it. -/
theorem coherent {M : Model S P} (hκ : corrOf σ M = π.κ) : Coherent σ M where
  symm := by
    intro w _ a b h
    rw [π.correlated_iff hκ] at h ⊢
    rcases h with rfl | ⟨ha, hb⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hb, ha⟩
  trans := by
    intro w _ a b c h1 h2
    rw [π.correlated_iff hκ] at h1 h2 ⊢
    rcases h1 with rfl | ⟨ha, hb⟩
    · exact h2
    · rcases h2 with rfl | ⟨_, hc⟩
      · exact Or.inr ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hc⟩
  past := by
    intro w hw a b h u hu _
    exact π.causallyMonotone M hκ hw h hu
  mono := π.causallyMonotone M hκ

/-! ## The realized depth on `(T, κ)` is at most `D` -/

omit [Nonempty P] in
theorem countP_lt_of {α : Type} (l : List α) (p q : α → Bool)
    (hmono : ∀ x ∈ l, p x = true → q x = true)
    (hex : ∃ x ∈ l, q x = true ∧ p x = false) : l.countP p < l.countP q := by
  induction l with
  | nil => obtain ⟨x, hx, _⟩ := hex; exact absurd hx (List.not_mem_nil)
  | cons a l ih =>
    rw [List.countP_cons, List.countP_cons]
    have hle : l.countP p ≤ l.countP q :=
      List.countP_mono_left (fun x hx => hmono x (List.mem_cons_of_mem _ hx))
    obtain ⟨x, hx, hqx, hpx⟩ := hex
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hqx, hpx]; simp; omega
    · have := ih (fun y hy => hmono y (List.mem_cons_of_mem _ hy)) ⟨x, hx, hqx, hpx⟩
      have hpa : p a = true → q a = true := hmono a (List.mem_cons_self ..)
      cases hp : p a <;> cases hq : q a <;> simp_all <;> omega

/-- The number of exposed fuses at a prehistory. -/
noncomputable def exposed (h : PreHistory P S.EventType) : Nat := by
  classical
  exact (List.range π.D).countP
    (fun i => decide (¬ isSequential (Event := S.EventType) (π.f (i + 1)) h))

omit [Nonempty P] in
theorem exposed_le (h : PreHistory P S.EventType) : π.exposed h ≤ π.D := by
  unfold exposed
  exact Nat.le_trans List.countP_le_length (by simp)

omit [Nonempty P] in
theorem exposed_lt {u w : PreHistory P S.EventType} (hsub : u ⊆ w)
    (hdiff : ∃ i, π.isFuse i ∧ isSequential (Event := S.EventType) (π.f i) u ∧
      ¬ isSequential (Event := S.EventType) (π.f i) w) :
    π.exposed u < π.exposed w := by
  classical
  unfold exposed
  apply countP_lt_of
  · intro i _ hp
    simp only [decide_eq_true_eq] at hp ⊢
    intro hs
    exact hp (isSequential_mono hsub hs)
  · obtain ⟨i, hi, hu, hw⟩ := hdiff
    refine ⟨i - 1, List.mem_range.mpr (by have := hi.1; have := hi.2; omega), ?_, ?_⟩
    · simp only [decide_eq_true_eq]
      rw [show i - 1 + 1 = i by have := hi.1; omega]
      exact hw
    · simp only [decide_eq_false_iff_not, Classical.not_not]
      rw [show i - 1 + 1 = i by have := hi.1; omega]
      exact hu

/-- Rows of `κ` depend on the time only through fuse sequentiality. -/
theorem row_eq_of_agree {M : Model S P} (hκ : corrOf σ M = π.κ) {u w : World P S.EventType}
    (hagree : ∀ i, π.isFuse i →
      (isSequential (Event := S.EventType) (π.f i) u.time ↔
        isSequential (Event := S.EventType) (π.f i) w.time)) (l : S.Value) :
    correlationRow (Correlated M σ.correlationSymb) l u =
      correlationRow (Correlated M σ.correlationSymb) l w := by
  have hok : ∀ a, π.fuseOk u.time a ↔ π.fuseOk w.time a := by
    intro a
    unfold fuseOk
    constructor
    · rintro (h | ⟨i, hi, rfl, hs⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, rfl, (hagree i hi).mp hs⟩
    · rintro (h | ⟨i, hi, rfl, hs⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i, hi, rfl, (hagree i hi).mpr hs⟩
  funext b
  apply propext
  show Correlated M σ.correlationSymb u l b ↔ Correlated M σ.correlationSymb w l b
  rw [π.correlated_iff hκ, π.correlated_iff hκ]
  show l = b ∨ (π.fuseOk u.time l ∧ π.fuseOk u.time b) ↔
    l = b ∨ (π.fuseOk w.time l ∧ π.fuseOk w.time b)
  rw [hok l, hok b]

/-- On `(T, κ)`, no learner's realized depth exceeds `D`. -/
theorem depthLE {M : Model S P} (hκ : corrOf σ M = π.κ) : DepthLE σ M π.D := by
  intro l
  have h := maxDepth_attained M (Correlated M σ.correlationSymb) l
  generalize maxDepth M (Correlated M σ.correlationSymb) l = n at h ⊢
  obtain ⟨ws, hposs, hchain, hrows⟩ := h
  have hstep : ∀ i j : Fin (n + 1), i < j →
      π.exposed (World.time (ws i)) < π.exposed (World.time (ws j)) := by
    intro i j hij
    have hsub := time_subset_of_accessible (hposs j) (hchain i j hij)
    apply π.exposed_lt hsub
    refine Classical.byContradiction fun hno => ?_
    apply hrows i j hij
    apply π.row_eq_of_agree hκ
    intro k hk
    constructor
    · intro hs
      exact Classical.byContradiction fun hw => hno ⟨k, hk, hs, hw⟩
    · intro hs
      exact isSequential_mono hsub hs
  have hge : ∀ k (hk : k < n + 1), k ≤ π.exposed (World.time (ws ⟨k, hk⟩)) := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have h1 := hstep ⟨k, by omega⟩ ⟨k + 1, hk⟩ (by show k < k + 1; omega)
      have h2 := ih (by omega)
      omega
  have := hge n (Nat.lt_succ_self n)
  have := π.exposed_le (World.time (ws ⟨n, Nat.lt_succ_self n⟩))
  omega

/-- The standard model on `(T, κ)` with a given history and live set. -/
def mkModel (σ : ProtocolSignature S) (H : History P S.EventType) (Live : Set P) : Model S P where
  history := H
  predInterp := fun p h => fun x =>
    (x = ⟨σ.liveSymb, []⟩ ∧ p ∈ Live) ∨ ∃ a b, x = ⟨σ.correlationSymb, [a, b]⟩ ∧ π.κ p h a b
  learner := π.T

theorem mkModel_learner (H : History P S.EventType) (Live : Set P) :
    (π.mkModel σ H Live).learner = π.T := rfl

theorem mkModel_hist (H : History P S.EventType) (Live : Set P) :
    (π.mkModel σ H Live).history = H := rfl

theorem mkModel_corrOf (H : History P S.EventType) (Live : Set P) :
    corrOf σ (π.mkModel σ H Live) = π.κ := by
  funext p h a b
  apply propext
  change ((⟨σ.correlationSymb, [a, b]⟩ : S.AtomicPredType) = ⟨σ.liveSymb, []⟩ ∧ p ∈ Live) ∨
    (∃ a' b', (⟨σ.correlationSymb, [a, b]⟩ : S.AtomicPredType) = ⟨σ.correlationSymb, [a', b']⟩ ∧
      π.κ p h a' b') ↔ π.κ p h a b
  constructor
  · rintro (⟨h1, _⟩ | ⟨a', b', h1, h2⟩)
    · exact absurd (congrArg Signature.AtomicPred.args h1) (by simp)
    · have := congrArg Signature.AtomicPred.args h1
      simp only [List.cons.injEq, and_true] at this
      obtain ⟨rfl, rfl⟩ := this
      exact h2
  · intro h1; exact Or.inr ⟨a, b, rfl, h1⟩

theorem mkModel_isLive (H : History P S.EventType) (Live : Set P) (p : P)
    (h : PreHistory P S.EventType) : IsLive σ (π.mkModel σ H Live) p h ↔ p ∈ Live := by
  change ((⟨σ.liveSymb, []⟩ : S.AtomicPredType) = ⟨σ.liveSymb, []⟩ ∧ p ∈ Live) ∨
    (∃ a' b', (⟨σ.liveSymb, []⟩ : S.AtomicPredType) = ⟨σ.correlationSymb, [a', b']⟩ ∧
      π.κ p h a' b') ↔ p ∈ Live
  constructor
  · rintro (⟨_, h1⟩ | ⟨a', b', h1, _⟩)
    · exact h1
    · exact absurd (congrArg Signature.AtomicPred.args h1) (by simp)
  · intro h1; exact Or.inl ⟨rfl, h1⟩

end Params
end ModalDistribution.LowerBound
