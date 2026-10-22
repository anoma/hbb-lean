import ModalDistribution.LowerBound.Topology
import ModalDistribution.LowerBound.Schedule

/-!
# The depth lower bound: proof

Fix a correct protocol and the adversary's `(T, κ)` (`Topology.lean`). Suppose an
`EnvOK` execution `M` has an honest `Q`-only `L`-delivery `d` of `v` with depth
`n < D`, and let `X` be its causal cone. Writing `qⱼ = f j`, `c = f 0`,
`Lⱼ = g j`, and `v₁ ≠ v`, the adversary builds executions `E₁, …, E_{n+1}`:

* `E₁` is a fair completion, with `{q₁, c}` live, of the single proposal of `v₁`
  by `c`; Liveness 1 makes `c` `L₁`-deliver `v₁`.
* `E_{j+1}` is a fair completion, with `{q_{j+1}, c}` live, of `E_j ∪ Y (j+1)`,
  where `Y` is the stage schedule (`Schedule.lean`); it is an execution by
  locality, `EnvOK` because `c` and `q_{j+1}` are sequential, and Liveness 2 —
  `Lⱼ ⋈ L_{j+1}` holds at the end because neither fuse is exposed — makes `c`
  `L_{j+1}`-deliver `v₁`.
* Finally `E_{n+1} ∪ X` is an execution in which `d` and `c`'s `L_{n+1}`-delivery
  of `v₁` coexist while `L ⋈ L_{n+1}` (`q_{n+1}`'s events of `X` were all added by
  stage `n+1`, since `X ⊆ Y (n+2)`), contradicting agreement.

The invariant `Inv j E` records what is needed of `E_j`.
-/

namespace ModalDistribution.LowerBound
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples.ThyHBB4 (ProtocolSignature)
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P] {σ : ProtocolSignature S}

/-! ## Generic satisfaction facts -/

theorem ofEvent_iff {M : Model S P} {t : World P S.EventType} {E : S.EventType} :
    (⟪t⟫ ⊨[M] Formula.ofEvent E) ↔ t.event = .some E ∧ t ∈ M.history.val := by
  rcases t with ⟨p, e, h⟩
  rw [Sat.ofEvent]
  constructor
  · rintro ⟨he, hm⟩
    change e = .some E at he
    subst he
    exact ⟨rfl, hm⟩
  · rintro ⟨he, hm⟩
    change e = .some E at he
    subst he
    exact ⟨rfl, hm⟩

theorem ofEvent_transfer {M M' : Model S P} {t : World P S.EventType} {E : S.EventType}
    (h : ⟪t⟫ ⊨[M] Formula.ofEvent E) (ht : t ∈ M'.history.val) :
    ⟪t⟫ ⊨[M'] Formula.ofEvent E :=
  ofEvent_iff.mpr ⟨(ofEvent_iff.mp h).1, ht⟩

theorem live_iff_isLive {M : Model S P} (w : World P S.EventType) :
    (⟪w⟫ ⊨[M] σ.live) ↔ IsLive σ M w.place w.time := Iff.rfl

/-! ## The context of a shallow delivery -/

/-- A shallow honest `Q`-only `L`-delivery in an `EnvOK` execution on `(T, κ)`,
together with a value `v₁` different from the delivered one. -/
structure Ctx (π : Params S P) (Proto : Protocol S P σ) where
  /-- The protocol's environment assumptions follow from the standard ones. -/
  henv : ∀ N : Model S P, EnvOK σ N → Coherent σ N → DepthLE σ N π.D → Proto.env N
  /-- … and include `correlationSeq`. -/
  henv' : ∀ N : Model S P, Proto.env N → EnvOK σ N
  M : Model S P
  hM : M ∈ Proto.executions
  hEnv : EnvOK σ M
  hT : M.learner = π.T
  hκ : corrOf σ M = π.κ
  d : World P S.EventType
  hd : d ∈ M.history.val
  v : S.Value
  hdel : ⟪d⟫ ⊨[M] σ.deliver (π.g 0) v
  hQ : UsesOnly π.Q d
  hHon : HonestCone d
  v1 : S.Value
  hv1 : v1 ≠ v

namespace Ctx

variable {π : Params S P} {Proto : Protocol S P σ} (c : Ctx π Proto)

include c in
/-- Environment assumptions for any `EnvOK` model on `(T, κ)`. -/
theorem envOf {N : Model S P} (hκ : corrOf σ N = π.κ) (hEnv : EnvOK σ N) : Proto.env N :=
  c.henv N hEnv (π.coherent hκ) (π.depthLE hκ)

/-- The causal cone of the delivery, as a history. -/
def X : History P S.EventType := coneHist c.M.history c.d c.hd

theorem mem_X {t : World P S.EventType} : t ∈ c.X.val ↔ t = c.d ∨ t ≪ c.d := mem_cone

theorem X_sub_M {t : World P S.EventType} (ht : t ∈ c.X.val) : t ∈ c.M.history.val := by
  rcases c.mem_X.mp ht with rfl | ht
  · exact c.hd
  · exact c.M.history.time_subset c.hd t ht

theorem X_place {t : World P S.EventType} (ht : t ∈ c.X.val) : ∃ i, π.isFuse i ∧ t.place = π.f i := by
  apply π.mem_Q.mp
  rcases c.mem_X.mp ht with rfl | ht
  · exact c.hQ.1
  · exact c.hQ.2 t ht

theorem X_place_ne_c {t : World P S.EventType} (ht : t ∈ c.X.val) : t.place ≠ π.f 0 := by
  obtain ⟨i, hi, hp⟩ := c.X_place ht
  rw [hp]
  exact π.f_ne (π.fuse_ne_zero hi)

theorem X_seq (p : P) : isSequential (Event := S.EventType) p c.X.val := c.hHon p

theorem X_depth {t : World P S.EventType} (ht : t ∈ c.X.val) : worldDepth t ≤ worldDepth c.d := by
  rcases c.mem_X.mp ht with rfl | ht
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (worldDepth_lt_of_accessible ht)

/-- The stage-`j` part of the cone, as a history. -/
noncomputable def YH (j : Nat) : History P S.EventType :=
  filterHist c.X (fun e => e ∈ Y π.f c.X j) (fun t _ ht u hu => Y_down π.f c.X j t ht u hu)

theorem mem_YH {j : Nat} {t : World P S.EventType} : t ∈ (c.YH j).val ↔ t ∈ Y π.f c.X j := by
  rw [YH, mem_filterHist]
  exact ⟨fun h => h.2, fun h => ⟨Y_subset π.f c.X j t h, h⟩⟩

/-- The merged model `E ∪ Y j` with live set `Live`. -/
noncomputable def Z (E : Model S P) (j : Nat) (Live : Set P) : Model S P :=
  π.mkModel σ (unionHist E.history (c.YH j)) Live

theorem mem_Z {E : Model S P} {j : Nat} {Live : Set P} {t : World P S.EventType} :
    t ∈ (c.Z E j Live).history.val ↔ t ∈ E.history.val ∨ t ∈ Y π.f c.X j := by
  show t ∈ (unionHist E.history (c.YH j)).val ↔ _
  rw [mem_unionHist, mem_YH]

/-- The final merged model `E ∪ X`. -/
noncomputable def Zfull (E : Model S P) (Live : Set P) : Model S P :=
  π.mkModel σ (unionHist E.history c.X) Live

theorem mem_Zfull {E : Model S P} {Live : Set P} {t : World P S.EventType} :
    t ∈ (c.Zfull E Live).history.val ↔ t ∈ E.history.val ∨ t ∈ c.X.val := by
  show t ∈ (unionHist E.history c.X).val ↔ _
  rw [mem_unionHist]

/-- The invariant carried from stage to stage. -/
structure Inv (j : Nat) (E : Model S P) : Prop where
  exec : E ∈ Proto.executions
  env : EnvOK σ E
  learner : E.learner = π.T
  corr : corrOf σ E = π.κ
  Ysub : ∀ e ∈ Y π.f c.X j, e ∈ E.history.val
  places : ∀ t ∈ E.history.val,
    t ∈ Y π.f c.X j ∨ t.place = π.f 0 ∨ ∃ i, 1 ≤ i ∧ i ≤ j ∧ t.place = π.f i
  seq_c : isSequential (Event := S.EventType) (π.f 0) E.history.val
  seq_q : isSequential (Event := S.EventType) (π.f j) E.history.val
  deliv : OccursAt E (π.f 0) (σ.deliver (π.g j) c.v1)

/-! ## Merged models are `EnvOK` executions -/

theorem Z_exec {E : Model S P} (hE : E ∈ Proto.executions) (hT : E.learner = π.T)
    (hκ : corrOf σ E = π.κ) (j : Nat) (Live : Set P) : c.Z E j Live ∈ Proto.executions := by
  apply Proto.local_closure
  intro w hw _ _
  rcases c.mem_Z.mp hw with hw | hw
  · exact ⟨E, hE, hT.trans (π.mkModel_learner _ _).symm, hκ.trans (π.mkModel_corrOf _ _).symm, hw⟩
  · exact ⟨c.M, c.hM, c.hT.trans (π.mkModel_learner _ _).symm,
      c.hκ.trans (π.mkModel_corrOf _ _).symm, c.X_sub_M (Y_subset π.f c.X j w hw)⟩

theorem Z_envOK {E : Model S P} (hE : EnvOK σ E) (hT : E.learner = π.T) (hκ : corrOf σ E = π.κ)
    {j : Nat} {Live : Set P}
    (hc : isSequential (Event := S.EventType) (π.f 0) (c.Z E j Live).history.val)
    (hq : ∃ i, π.isFuse i ∧ isSequential (Event := S.EventType) (π.f i) (c.Z E j Live).history.val) :
    EnvOK σ (c.Z E j Live) := by
  apply π.envOK_of (π.mkModel_learner _ _) (π.mkModel_corrOf _ _)
  intro t ht
  rcases (PreHistory.happensBeforeEq_iff _ _).1 ht with ⟨p, e, hmem⟩ | heq
  · rcases c.mem_Z.mp hmem with h | h
    · exact π.envOKAt_of_envOK hT hκ hE (PreHistory.happensBeforeEq_of_mem h)
    · exact π.envOKAt_of_envOK c.hT c.hκ c.hEnv
        (PreHistory.happensBeforeEq_of_mem (c.X_sub_M (Y_subset π.f c.X j _ h)))
  · subst heq
    exact ⟨hc, hq⟩

theorem Zfull_exec {E : Model S P} (hE : E ∈ Proto.executions) (hT : E.learner = π.T)
    (hκ : corrOf σ E = π.κ) (Live : Set P) : c.Zfull E Live ∈ Proto.executions := by
  apply Proto.local_closure
  intro w hw _ _
  rcases c.mem_Zfull.mp hw with hw | hw
  · exact ⟨E, hE, hT.trans (π.mkModel_learner _ _).symm, hκ.trans (π.mkModel_corrOf _ _).symm, hw⟩
  · exact ⟨c.M, c.hM, c.hT.trans (π.mkModel_learner _ _).symm,
      c.hκ.trans (π.mkModel_corrOf _ _).symm, c.X_sub_M hw⟩

theorem Zfull_envOK {E : Model S P} (hE : EnvOK σ E) (hT : E.learner = π.T) (hκ : corrOf σ E = π.κ)
    {Live : Set P}
    (hc : isSequential (Event := S.EventType) (π.f 0) (c.Zfull E Live).history.val)
    (hq : ∃ i, π.isFuse i ∧ isSequential (Event := S.EventType) (π.f i) (c.Zfull E Live).history.val) :
    EnvOK σ (c.Zfull E Live) := by
  apply π.envOK_of (π.mkModel_learner _ _) (π.mkModel_corrOf _ _)
  intro t ht
  rcases (PreHistory.happensBeforeEq_iff _ _).1 ht with ⟨p, e, hmem⟩ | heq
  · rcases c.mem_Zfull.mp hmem with h | h
    · exact π.envOKAt_of_envOK hT hκ hE (PreHistory.happensBeforeEq_of_mem h)
    · exact π.envOKAt_of_envOK c.hT c.hκ c.hEnv
        (PreHistory.happensBeforeEq_of_mem (c.X_sub_M h))
  · subst heq
    exact ⟨hc, hq⟩

/-! ## The inductive step -/

theorem step (hProto : Proto.Correct) {j : Nat} (hj : 1 ≤ j) (hjD : j + 1 ≤ π.D)
    {E : Model S P} (hI : c.Inv j E) : ∃ E', c.Inv (j + 1) E' := by
  let Live : Set P := fun p => p = π.f (j + 1) ∨ p = π.f 0
  have hLive : ∀ p, p ∈ Live ↔ (p = π.f (j + 1) ∨ p = π.f 0) := fun _ => Iff.rfl
  have hfj : π.isFuse j := ⟨hj, by omega⟩
  have hfj1 : π.isFuse (j + 1) := ⟨by omega, hjD⟩
  -- events of `q_j` in the merge are events of `E`
  have ha : ∀ t ∈ (c.Z E (j + 1) Live).history.val, t.place = π.f j → t ∈ E.history.val := by
    intro t ht hp
    rcases c.mem_Z.mp ht with h | h
    · exact h
    · have h' : t ∈ Y π.f c.X (j - 1 + 2) := by rw [show j - 1 + 2 = j + 1 by omega]; exact h
      have := Y_avoid π.f c.X (j - 1) t h' (by rw [show j - 1 + 1 = j by omega]; exact hp)
      rw [show j - 1 + 1 = j by omega] at this
      exact hI.Ysub t this
  have hseq_j : isSequential (Event := S.EventType) (π.f j) (c.Z E (j + 1) Live).history.val :=
    isSequential_of_events_in ha hI.seq_q
  -- events of `q_{j+1}` in the merge are events of the cone
  have hc1 : ∀ t ∈ (c.Z E (j + 1) Live).history.val, t.place = π.f (j + 1) → t ∈ c.X.val := by
    intro t ht hp
    rcases c.mem_Z.mp ht with h | h
    · rcases hI.places t h with h | h | ⟨i, _, hi2, h⟩
      · exact Y_subset π.f c.X _ _ h
      · exact absurd (hp.symm.trans h) (π.f_ne (by omega))
      · have := π.f_inj (hp.symm.trans h); omega
    · exact Y_subset π.f c.X _ _ h
  have hseq_j1 : isSequential (Event := S.EventType) (π.f (j + 1)) (c.Z E (j + 1) Live).history.val :=
    isSequential_of_events_in hc1 (c.X_seq _)
  -- events of `c` in the merge are events of `E`
  have hcE : ∀ t ∈ (c.Z E (j + 1) Live).history.val, t.place = π.f 0 → t ∈ E.history.val := by
    intro t ht hp
    rcases c.mem_Z.mp ht with h | h
    · exact h
    · exact absurd hp (c.X_place_ne_c (Y_subset π.f c.X _ _ h))
  have hseq_c : isSequential (Event := S.EventType) (π.f 0) (c.Z E (j + 1) Live).history.val :=
    isSequential_of_events_in hcE hI.seq_c
  have hZexec := c.Z_exec hI.exec hI.learner hI.corr (j + 1) Live
  have hZenv : EnvOK σ (c.Z E (j + 1) Live) :=
    c.Z_envOK hI.env hI.learner hI.corr hseq_c ⟨j + 1, hfj1, hseq_j1⟩
  have hLiveSeq : ∀ p ∈ Live, isSequential (Event := S.EventType) p (c.Z E (j + 1) Live).history.val := by
    intro p hp
    rcases (hLive p).mp hp with rfl | rfl
    · exact hseq_j1
    · exact hseq_c
  obtain ⟨E', hE'exec, hfair, hE'penv, hE'T, hE'κ, hE'live, hZsub, hnew⟩ :=
    Proto.fair_completion _ hZexec (c.envOf (π.mkModel_corrOf _ _) hZenv) Live hLiveSeq
  have hT' : E'.learner = π.T := hE'T
  have hκ' : corrOf σ E' = π.κ := hE'κ.trans (π.mkModel_corrOf _ _)
  have hE'env : EnvOK σ E' := c.henv' E' hE'penv
  have hliveC : IsLive σ E' (π.f 0) E'.history.val := (hE'live _ _).mpr (Or.inr rfl)
  have hliveQ : IsLive σ E' (π.f (j + 1)) E'.history.val := (hE'live _ _).mpr (Or.inl rfl)
  have ha' : ∀ t ∈ E'.history.val, t.place = π.f j → t ∈ E.history.val := by
    intro t ht hp
    by_cases hZ : t ∈ (c.Z E (j + 1) Live).history.val
    · exact ha t hZ hp
    · obtain ⟨hl, _⟩ := hnew t ht hZ
      rcases (hLive _).mp hl with h | h
      · exact absurd (hp.symm.trans h) (π.f_ne (by omega))
      · exact absurd (hp.symm.trans h) (π.f_ne (by omega))
  have hseq_j' : isSequential (Event := S.EventType) (π.f j) E'.history.val :=
    isSequential_of_events_in ha' hI.seq_q
  have hseq_q' : isSequential (Event := S.EventType) (π.f (j + 1)) E'.history.val :=
    Proto.fair_sequential E' hfair _ hliveQ
  refine ⟨E', ?_⟩
  refine
    { exec := hE'exec
      env := hE'env
      learner := hT'
      corr := hκ'
      Ysub := ?_
      places := ?_
      seq_c := Proto.fair_sequential E' hfair _ hliveC
      seq_q := hseq_q'
      deliv := ?_ }
  · intro e he
    exact hZsub e (c.mem_Z.mpr (Or.inr he))
  · intro t ht
    by_cases hZ : t ∈ (c.Z E (j + 1) Live).history.val
    · rcases c.mem_Z.mp hZ with h | h
      · rcases hI.places t h with h | h | ⟨i, hi1, hi2, h⟩
        · exact Or.inl (Y_mono π.f c.X j t h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨i, hi1, by omega, h⟩)
      · exact Or.inl h
    · obtain ⟨hl, _⟩ := hnew t ht hZ
      rcases (hLive _).mp hl with h | h
      · exact Or.inr (Or.inr ⟨j + 1, by omega, Nat.le_refl _, h⟩)
      · exact Or.inr (Or.inl h)
  · -- Liveness 2 transfers `c`'s delivery from `L_j` to `L_{j+1}`
    have hcorr : ∀ p, Correlated E' σ.correlationSymb (finalWorld E' p) (π.g j) (π.g (j + 1)) := by
      intro p
      rw [π.correlated_iff hκ']
      exact Or.inr ⟨Or.inr ⟨j, hfj, rfl, hseq_j'⟩, Or.inr ⟨j + 1, hfj1, rfl, hseq_q'⟩⟩
    have hquorum : ∃ Q ∈ (E'.learner (π.g (j + 1))).quorums,
        ∀ p ∈ Q, ⟪finalWorld E' p⟫ ⊨[E'] σ.live := by
      refine ⟨Live, by rw [hT']; exact π.fuse_quorum hfj1, ?_⟩
      intro p hp
      exact (hE'live p _).mpr hp
    have hdeliv : Occurs E' (σ.deliver (π.g j) c.v1) := by
      obtain ⟨e, he, _, hs⟩ := hI.deliv
      have he' : e ∈ E'.history.val := hZsub e (c.mem_Z.mpr (Or.inl he))
      exact ⟨e, he', ofEvent_transfer hs he'⟩
    exact hProto.2.2 E' hE'exec hE'penv hfair (π.g j) (π.g (j + 1)) c.v1 hcorr hquorum hdeliv
      (π.f 0) hliveC

/-! ## The base case -/

omit [Nonempty P] in
theorem isSequential_single (p q : P) (e : MaybeEvent S.EventType) :
    isSequential (Event := S.EventType) p (singleHist q e).val := by
  intro t₁ t₂ h₁ h₂ _ _
  have h₁' := mem_singleHist.mp h₁
  have h₂' := mem_singleHist.mp h₂
  subst h₁' h₂'
  exact Or.inr (Or.inr rfl)

omit [Nonempty P] in
theorem isSequential_empty (p : P) : isSequential (Event := S.EventType) p (emptyHist : History P S.EventType).val :=
  fun t _ h => absurd h (mem_emptyHist t)

theorem base (hProto : Proto.Correct) : ∃ E, c.Inv 1 E := by
  let Live : Set P := fun p => p = π.f 1 ∨ p = π.f 0
  have hLive : ∀ p, p ∈ Live ↔ (p = π.f 1 ∨ p = π.f 0) := fun _ => Iff.rfl
  have hf1 : π.isFuse 1 := ⟨Nat.le_refl 1, π.D_pos⟩
  let w : World P S.EventType := (π.f 0, .some ⟨σ.proposeSymb, [c.v1]⟩, .mk [])
  let B : Model S P := π.mkModel σ (singleHist (π.f 0) (.some ⟨σ.proposeSymb, [c.v1]⟩)) Live
  let M0 : Model S P := π.mkModel σ emptyHist Live
  have hmemB : ∀ t, t ∈ B.history.val ↔ t = w := fun t => mem_singleHist
  have hM0 : M0 ∈ Proto.executions :=
    Proto.local_closure M0 (fun t ht => absurd ht (mem_emptyHist t))
  have hB : B ∈ Proto.executions := by
    refine Proto.propose_free M0 B hM0 rfl rfl w c.v1 rfl ?_
    intro t
    rw [hmemB]
    constructor
    · intro h; exact Or.inr h
    · rintro (h | h)
      · exact absurd h (mem_emptyHist t)
      · exact h
  have hBenv : EnvOK σ B := by
    apply π.envOK_of (π.mkModel_learner _ _) (π.mkModel_corrOf _ _)
    intro t ht
    rcases (PreHistory.happensBeforeEq_iff _ _).1 ht with ⟨p, e, hmem⟩ | heq
    · have := hmemB (p, e, t) |>.mp hmem
      have ht0 : t = PreHistory.mk [] := congrArg World.time this
      subst ht0
      exact ⟨isSequential_empty _, 1, hf1, isSequential_empty _⟩
    · subst heq
      exact ⟨isSequential_single _ _ _, 1, hf1, isSequential_single _ _ _⟩
  have hLiveSeq : ∀ p ∈ Live, isSequential (Event := S.EventType) p B.history.val :=
    fun p _ => isSequential_single p _ _
  obtain ⟨E, hEexec, hfair, hEpenv, hET, hEκ, hElive, hBsub, hnew⟩ :=
    Proto.fair_completion B hB (c.envOf (π.mkModel_corrOf _ _) hBenv) Live hLiveSeq
  have hT' : E.learner = π.T := hET
  have hκ' : corrOf σ E = π.κ := hEκ.trans (π.mkModel_corrOf _ _)
  have hEenv : EnvOK σ E := c.henv' E hEpenv
  have hliveC : IsLive σ E (π.f 0) E.history.val := (hElive _ _).mpr (Or.inr rfl)
  have hliveQ : IsLive σ E (π.f 1) E.history.val := (hElive _ _).mpr (Or.inl rfl)
  have hwE : w ∈ E.history.val := hBsub w ((hmemB w).mpr rfl)
  refine ⟨E, ?_⟩
  refine
    { exec := hEexec
      env := hEenv
      learner := hT'
      corr := hκ'
      Ysub := fun e he => nomatch he
      places := ?_
      seq_c := Proto.fair_sequential E hfair _ hliveC
      seq_q := Proto.fair_sequential E hfair _ hliveQ
      deliv := ?_ }
  · intro t ht
    by_cases hBt : t ∈ B.history.val
    · have := (hmemB t).mp hBt
      subst this
      exact Or.inr (Or.inl rfl)
    · obtain ⟨hl, _⟩ := hnew t ht hBt
      rcases (hLive _).mp hl with h | h
      · exact Or.inr (Or.inr ⟨1, Nat.le_refl 1, Nat.le_refl 1, h⟩)
      · exact Or.inr (Or.inl h)
  · -- Liveness 1 makes `c` deliver `v₁` for `L₁`
    have hquorum : ∃ Q ∈ (E.learner (π.g 1)).quorums, ∀ p ∈ Q, ⟪finalWorld E p⟫ ⊨[E] σ.live := by
      refine ⟨Live, by rw [hT']; exact π.fuse_quorum hf1, ?_⟩
      intro p hp
      exact (hElive p _).mpr hp
    have hpropose : ⟪w⟫ ⊨[E] σ.propose c.v1 := ofEvent_iff.mpr ⟨rfl, hwE⟩
    have hunique : UniqueOccurrence E σ.propose := by
      refine ⟨c.v1, ⟨w, hwE, hpropose⟩, ?_⟩
      intro u hu
      obtain ⟨e, he, hs⟩ := hu
      have hev := (ofEvent_iff.mp hs).1
      by_cases hBe : e ∈ B.history.val
      · have := (hmemB e).mp hBe
        subst this
        have h2 := MaybeEvent.some.inj hev
        have h3 := congrArg Signature.Event.args h2
        simp only [List.cons.injEq, and_true] at h3
        exact h3.symm
      · obtain ⟨_, hnp⟩ := hnew e he hBe
        exact absurd hev (hnp u)
    have hobs : ∃ e ∈ E.history.val, (⟪e⟫ ⊨[E] σ.live) ∧ ObservedAt E e (σ.propose c.v1) := by
      obtain ⟨e, he, hep, hobs⟩ := Proto.fair_observes E hfair (π.f 0) hliveC w hwE _ rfl
        ((hElive _ _).mpr (Or.inr rfl))
      refine ⟨e, he, ?_, hobs⟩
      show IsLive σ E e.place e.time
      rw [hep]
      exact (hElive _ _).mpr (Or.inr rfl)
    exact hProto.2.1 E hEexec hEpenv hfair (π.g 1) c.v1 hquorum hunique hobs (π.f 0) hliveC

/-! ## The final merge and the contradiction -/

theorem final (hProto : Proto.Correct) {n : Nat} (hn : worldDepth c.d = n) (hnD : n + 1 ≤ π.D)
    {E : Model S P} (hI : c.Inv (n + 1) E) : False := by
  let Live : Set P := fun p => p = π.f 0
  have hfn : π.isFuse (n + 1) := ⟨by omega, hnD⟩
  have hXY : ∀ t ∈ c.X.val, t ∈ Y π.f c.X (n + 2) := by
    intro t ht
    apply Y_covers π.f c.X π.f_inj (n + 1) (by omega) t ht
    have := c.X_depth ht
    show PreHistory.height t.time < n + 1
    unfold worldDepth at this hn
    omega
  have ha : ∀ t ∈ (c.Zfull E Live).history.val, t.place = π.f (n + 1) → t ∈ E.history.val := by
    intro t ht hp
    rcases c.mem_Zfull.mp ht with h | h
    · exact h
    · exact hI.Ysub t (Y_avoid π.f c.X n t (hXY t h) hp)
  have hseq_q : isSequential (Event := S.EventType) (π.f (n + 1)) (c.Zfull E Live).history.val :=
    isSequential_of_events_in ha hI.seq_q
  have hcE : ∀ t ∈ (c.Zfull E Live).history.val, t.place = π.f 0 → t ∈ E.history.val := by
    intro t ht hp
    rcases c.mem_Zfull.mp ht with h | h
    · exact h
    · exact absurd hp (c.X_place_ne_c h)
  have hseq_c : isSequential (Event := S.EventType) (π.f 0) (c.Zfull E Live).history.val :=
    isSequential_of_events_in hcE hI.seq_c
  have hexec := c.Zfull_exec hI.exec hI.learner hI.corr Live
  have henv : EnvOK σ (c.Zfull E Live) :=
    c.Zfull_envOK hI.env hI.learner hI.corr hseq_c ⟨n + 1, hfn, hseq_q⟩
  have hcorr : ∀ p, Correlated (c.Zfull E Live) σ.correlationSymb (finalWorld (c.Zfull E Live) p)
      (π.g 0) (π.g (n + 1)) := by
    intro p
    have hκZ : corrOf σ (c.Zfull E Live) = π.κ := π.mkModel_corrOf _ _
    rw [π.correlated_iff hκZ]
    exact Or.inr ⟨Or.inl rfl, Or.inr ⟨n + 1, hfn, rfl, hseq_q⟩⟩
  have hdX : c.d ∈ (c.Zfull E Live).history.val := c.mem_Zfull.mpr (Or.inr (c.mem_X.mpr (Or.inl rfl)))
  have hv : Occurs (c.Zfull E Live) (σ.deliver (π.g 0) c.v) := ⟨c.d, hdX, ofEvent_transfer c.hdel hdX⟩
  have hv1 : Occurs (c.Zfull E Live) (σ.deliver (π.g (n + 1)) c.v1) := by
    obtain ⟨e, he, _, hs⟩ := hI.deliv
    have he' : e ∈ (c.Zfull E Live).history.val := c.mem_Zfull.mpr (Or.inl he)
    exact ⟨e, he', ofEvent_transfer hs he'⟩
  exact c.hv1 (hProto.1 _ hexec (c.envOf (π.mkModel_corrOf _ _) henv) _ _ _ _ hcorr hv hv1).symm

theorem inv_exists (hProto : Proto.Correct) : ∀ j, 1 ≤ j → j ≤ π.D → ∃ E, c.Inv j E := by
  intro j
  induction j with
  | zero => intro h; exact absurd h (by omega)
  | succ j ih =>
    intro _ hD
    cases j with
    | zero => exact c.base hProto
    | succ j =>
      obtain ⟨E, hE⟩ := ih (by omega) (by omega)
      exact c.step hProto (by omega) hD hE

/-- A shallow honest `Q`-only delivery is impossible. -/
theorem no_shallow (hProto : Proto.Correct) (hshallow : worldDepth c.d < π.D) : False := by
  obtain ⟨E, hE⟩ := c.inv_exists hProto (worldDepth c.d + 1) (by omega) hshallow
  exact c.final hProto rfl hshallow hE

end Ctx
end ModalDistribution.LowerBound
