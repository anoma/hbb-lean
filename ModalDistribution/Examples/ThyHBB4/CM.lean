import ModalDistribution.Examples.ThyHBB4.LivenessTwo

namespace ModalDistribution.Examples.ThyHBB4.CM
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

theorem endingDepthChain_append_of_lost_correlation (h : ProtocolCM M σ) {w e : World P S.EventType}
    (hw : w.time ⪯ M.history.val) (he : e ≪ w) {a c : S.Value} {n : Nat}
    (hc : Correlated M σ.correlationSymb e a c) (hnc : ¬ Correlated M σ.correlationSymb w a c)
    (chain : EndingDepthChain M (Correlated M σ.correlationSymb) a e n) :
    EndingDepthChain M (Correlated M σ.correlationSymb) a w (n + 1) := by
  apply endingDepthChain_append chain he hw
  intro u hu heq
  have huCorr : Correlated M σ.correlationSymb u a c := by
    rcases hu with hu | rfl
    · exact h.causalMonotone (predecessor_possible hw he) hc hu
    · exact hc
  exact hnc (Eq.mp (congrFun heq c) huCorr)

/-- Conflicting ranks force a chain of strictly changing correlation rows. -/
theorem conflict_yields_depth_chain (h : ProtocolCM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {r n k : Nat}
    (hb : Correlated M σ.correlationSymb w a b) (hc : Correlated M σ.correlationSymb w a c) (hvu : v ≠ u)
    (hn : r ≤ n) (hk : r ≤ k)
    (hv : ObservedAt M w (σ.voteFromSomeSource b v n))
    (hu : ObservedAt M w (σ.voteFromSomeSource c u k)) :
    EndingDepthChain M (Correlated M σ.correlationSymb) a w (r + 1) := by
  induction r generalizing w b c v u n k with
  | zero =>
    obtain ⟨V⟩ := minimal_vote h hw hb hn hv
    obtain ⟨U⟩ := minimal_vote h hw hc hk hu
    have outside : ∀ {x}, (X : MinimalVote (M := M) (σ := σ) w a x 0) →
        ¬ Correlated M σ.correlationSymb w a X.source → EndingDepthChain M (Correlated M σ.correlationSymb) a w 1 := by
      intro x X hnot
      have hX := predecessor_possible hw X.before
      have hcorr : Correlated M σ.correlationSymb X.event a X.source := by
        have hab := h.causalMonotone hw X.correlated X.before
        rcases h.voteSource hX X.vote with heq | hsrc
        · exact False.elim (hnot (heq ▸ X.correlated))
        · exact h.correlationTrans hX hab hsrc
      exact endingDepthChain_append_of_lost_correlation h hw X.before hcorr hnot
        (endingDepthChain_zero _ _ hX)
    by_cases hV : Correlated M σ.correlationSymb w a V.source
    · by_cases hU : Correlated M σ.correlationSymb w a U.source
      · have echo : ∀ {x}, (X : MinimalVote (M := M) (σ := σ) w a x 0) →
            Correlated M σ.correlationSymb w a X.source → (⟪w⟫ ⊨[M] σ.echoCertificate X.target x) := by
          intro x X hsrc
          rcases h.voteZeroBackward (predecessor_possible hw X.before) X.vote with he | hv
          · exact quorum_lift hw X.before he.2
          · obtain ⟨e, he, hv⟩ := quorum_witness hv
            obtain ⟨s, hv⟩ := (Sat.exists_iff _ _).mp hv
            exact False.elim (X.minimal e he X.source s _ hsrc (Nat.zero_le _) hv)
        have hVU := h.correlationTrans hw (h.correlationSymm hw V.correlated) U.correlated
        obtain ⟨e, f, he, hf, hp, hve, huf, hord⟩ :=
          quorum_pair h hw hVU (echo V hV) (echo U hU)
        have eq : v = u := by
          rcases hord with hef | hfe | rfl
          · exact (h.echoNonEquivocation (predecessor_possible hw hf) huf
              ((Sat.past _ _ _).mpr ⟨e, hef, hp, hve⟩)).symm
          · exact h.echoNonEquivocation (predecessor_possible hw he) hve
              ((Sat.past _ _ _).mpr ⟨f, hfe, hp.symm, huf⟩)
          · have heq := ((Sat.ofEvent _ _ _).mp hve).1.symm.trans
              ((Sat.ofEvent _ _ _).mp huf).1
            have ha := congrArg (fun e : MaybeEvent S.EventType =>
              match e with | .none => [] | .some x => x.args) heq
            exact (List.cons.inj ha).1
        exact False.elim (hvu eq)
      · exact outside U hU
    · exact outside V hV
  | succ r ih =>
    obtain ⟨V⟩ := minimal_vote h hw hb hn hv
    obtain ⟨U⟩ := minimal_vote h hw hc hk hu
    have hVU := h.correlationTrans hw (h.correlationSymm hw V.correlated) U.correlated
    obtain ⟨e, f, he, hf, _, hve, huf, hord⟩ := quorum_pair_before h hw V.before U.before hVU
      (h.voteSuccBackward (predecessor_possible hw V.before) V.vote)
      (h.voteSuccBackward (predecessor_possible hw U.before) U.vote)
    have step : ∀ {v u}, v ≠ u →
        (V : MinimalVote (M := M) (σ := σ) w a v (r + 1)) →
        (U : MinimalVote (M := M) (σ := σ) w a u (r + 1)) →
        ∀ e f, e ≪ V.event → f ≪ U.event →
        (⟪e⟫ ⊨[M] σ.vote V.target V.source v r) →
        (⟪f⟫ ⊨[M] σ.vote U.target U.source u r) → e ≪ f →
        EndingDepthChain M (Correlated M σ.correlationSymb) a w (r + 1 + 1) := by
      intro v u hvu V U e f he hf hve huf hef
      have hfw := accessible_trans hw hf U.before
      have hfpos := predecessor_possible hw hfw
      have haV := h.causalMonotone hw V.correlated hfw
      have haU := h.causalMonotone hw U.correlated hfw
      have hVU := h.correlationTrans hfpos (h.correlationSymm hfpos haV) haU
      have hPast : ObservedAt M f (σ.voteFromSomeSource V.target v r) :=
        ⟨e, hef, (Sat.exists_iff _ _).mpr ⟨V.source, hve⟩⟩
      obtain ⟨c, k, hrk, hcU, hcv⟩ := h.voteLegal hfpos huf V.target v r hVU hvu hPast
      have hac := h.correlationTrans hfpos haU (h.correlationSymm hfpos hcU)
      have hnot : ¬ Correlated M σ.correlationSymb w a c := by
        intro hc
        obtain ⟨g, hgf, hgv⟩ := hcv
        obtain ⟨s, hgv⟩ := (Sat.exists_iff _ _).mp hgv
        exact U.minimal g (accessible_trans (predecessor_possible hw U.before) hgf hf)
          c s k hc (by omega) hgv
      have chain := ih hfpos haV hac hvu (Nat.le_refl r) (by omega : r ≤ k) hPast hcv
      exact endingDepthChain_append_of_lost_correlation h hw hfw hac hnot chain
    rcases hord with hef | hfe | heq
    · exact step hvu V U e f he hf hve huf hef
    · exact step (Ne.symm hvu) U V f e hf he huf hve hfe
    · subst f
      exact False.elim (hvu (vote_value_eq hve huf))

/-- A vote at the depth threshold dominates all conflicting votes in its row. -/
theorem conflicting_rank_lt (h : ProtocolCM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {n k : Nat}
    (hb : Correlated M σ.correlationSymb w a b) (hc : Correlated M σ.correlationSymb w a c) (hvu : v ≠ u)
    (hn : maxDepth M (Correlated M σ.correlationSymb) a - 1 ≤ n)
    (hv : ObservedAt M w (σ.voteFromSomeSource b v n))
    (hu : ObservedAt M w (σ.voteFromSomeSource c u k)) :
    k < maxDepth M (Correlated M σ.correlationSymb) a - 1 := by
  by_cases hk : k < maxDepth M (Correlated M σ.correlationSymb) a - 1
  · exact hk
  have hchain := conflict_yields_depth_chain h hw hb hc hvu hn (by omega) hv hu
  have hbound := endingDepthChain_le hchain
  have hpos := maxDepth_pos M (Correlated M σ.correlationSymb) a
  omega

/-- The dominating vote is the witness required by every legality clause. -/
theorem high_vote_legal (h : ProtocolCM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v : S.Value} {n : Nat}
    (hb : Correlated M σ.correlationSymb w a b) (hc : Correlated M σ.correlationSymb w a c)
    (hn : maxDepth M (Correlated M σ.correlationSymb) a - 1 ≤ n)
    (hv : ObservedAt M w (σ.voteFromSomeSource b v n)) : Legal M σ w c v := by
  intro d u k hdc huv hu
  have had := h.correlationTrans hw hc (h.correlationSymm hw hdc)
  have hlt := conflicting_rank_lt h hw hb had (Ne.symm huv) hn hv hu
  exact ⟨b, n, by omega, h.correlationTrans hw (h.correlationSymm hw hb) hc, hv⟩

/-- Deliveries observed at a correlated world agree, even with unequal depths. -/
theorem agreement_at (h : ProtocolCM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b v u : S.Value}
    (hab : Correlated M σ.correlationSymb w a b)
    (hv : ObservedAt M w (σ.deliver a v))
    (hu : ObservedAt M w (σ.deliver b u)) : v = u := by
  have hv' := observed_vote_of_observed_delivery h.toBaseProtocol hw hv
  have hu' := observed_vote_of_observed_delivery h.toBaseProtocol hw hu
  by_cases heq : v = u
  · exact heq
  apply False.elim
  by_cases hle : maxDepth M (Correlated M σ.correlationSymb) a ≤ maxDepth M (Correlated M σ.correlationSymb) b
  · have haa := h.correlationTrans hw hab (h.correlationSymm hw hab)
    have hlt := conflicting_rank_lt h hw haa hab heq (by omega) hv' hu'
    omega
  · have hba := h.correlationSymm hw hab
    have hbb := h.correlationTrans hw hba hab
    have hlt := conflicting_rank_lt h hw hbb hba (Ne.symm heq) (by omega) hu' hv'
    omega

/-- End-of-time agreement when every final participant correlates the learners. -/
theorem agreement (h : ProtocolCM M σ) {a b v u : S.Value}
    (hab : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hv : Occurs M (σ.deliver a v)) (hu : Occurs M (σ.deliver b u)) : v = u := by
  exact agreement_at h (PreHistory.happensBeforeEq_refl _)
    (hab (Classical.ofNonempty)) hv hu

/-- Liveness 1 under causal monotonicity. -/
theorem livenessOne (h : ProtocolCM M σ) {l v : S.Value}
    (hLiveQuorum : ∃ Q ∈ (M.learner l).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hUnique : UniqueOccurrence M σ.propose)
    (hObserved : ∃ e ∈ M.history.val,
      (⟪e⟫ ⊨[M] σ.live) ∧ ObservedAt M e (σ.propose v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver l v) := by
  exact ThyHBB4.livenessOne h.toBaseProtocol hLiveQuorum hUnique hObserved p hLive

/-- Causal monotonicity makes a delivered value legal throughout its correlation row. -/
theorem delivery_legal (h : ProtocolCM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b v : S.Value}
    (hab : Correlated M σ.correlationSymb w a b)
    (hdel : ObservedAt M w (σ.deliver a v)) : Legal M σ w b v := by
  have hvote := observed_vote_of_observed_delivery h.toBaseProtocol hw hdel
  have haa := h.correlationTrans hw hab (h.correlationSymm hw hab)
  exact high_vote_legal h hw haa hab (by omega) hvote

/-- Liveness 2 for the causal-monotonicity theory. -/
theorem livenessTwo (h : ProtocolCM M σ) {a b v : S.Value}
    (hCorrelation : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hLiveQuorum : ∃ Q ∈ (M.learner b).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hDelivered : Occurs M (σ.deliver a v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver b v) := by
  exact livenessTwo_of_delivery_legal h.toBaseProtocol (delivery_legal h) hCorrelation hLiveQuorum hDelivered p hLive

/-- Agreement in the paper's modal notation. -/
theorem agreement_modal (h : ProtocolCM M σ) {a b v u : S.Value}
    (hab : ⊨[M] □ᶠ[] (σ.correlation a b)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ
      (♢ᶠ↓[[]] (σ.deliver b u)) ⇒ᶠ (v ≃ᶠ u) := by
  exact occurrence_agreement_iff.mp (agreement h (correlated_final_iff_end.mpr hab))

/-- Liveness 1 in the paper's modal notation. -/
theorem livenessOne_modal (h : ProtocolCM M σ) {l v : S.Value}
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live)
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ⇒ᶠ
      σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) := by
  exact ThyHBB4.livenessOne_modal h.toBaseProtocol hLiveQuorum hUnique

/-- Liveness 2 in the paper's modal notation. -/
theorem livenessTwo_modal (h : ProtocolCM M σ) {a b v : S.Value}
    (hCorrelation : ⊨[M] □ᶠ[] (σ.correlation a b))
    (hLiveQuorum : ⊨[M] □ᶠ[[b]] σ.live) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ σ.live ⇒ᶠ ↕ᶠ (σ.deliver b v) := by
  exact occurrence_liveness_iff.mp (livenessTwo h
    (correlated_final_iff_end.mpr hCorrelation) (quorum_final_iff_end.mpr hLiveQuorum))

end ModalDistribution.Examples.ThyHBB4.CM
