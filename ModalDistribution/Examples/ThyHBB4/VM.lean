import ModalDistribution.Examples.ThyHBB4.LivenessTwo
import ModalDistribution.Examples.ThyHBB4.StrictDepth

/-!
# HBB4 correctness under vote monotonicity

`ProtocolVM` isolates the instances of causal monotonicity that the CM proofs
actually use, in a single axiom `VoteMonotonicity`: the target of an observed
vote keeps the observer's correlations at the vote event, for every round-zero
vote (the base case) and for the later vote of a same-signer, same-round switch
between correlated learners (the inductive step). The chains are strict, so no monotonicity is needed when
extending them. Agreement, Liveness 1 and Liveness 2 all follow, with the same
single-vote conflict bound as under CM.
-/

namespace ModalDistribution.Examples.ThyHBB4.VM
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

/-- Conflicting votes of ranks `≥ r` for learners in the observer's row force a
strict chain of index `r + 1` ending at the observer. -/
theorem conflict_yields_strict_depth_chain (h : ProtocolVM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {r n k : Nat}
    (hb : Correlated M σ.correlationSymb w a b) (hc : Correlated M σ.correlationSymb w a c) (hvu : v ≠ u)
    (hn : r ≤ n) (hk : r ≤ k)
    (hv : ObservedAt M w (σ.vote b v n))
    (hu : ObservedAt M w (σ.vote c u k)) :
    StrictEndingDepthChain M (Correlated M σ.correlationSymb) a w (r + 1) := by
  induction r generalizing w b c v u n k with
  | zero =>
    obtain ⟨V⟩ := minimal_vote h.toBaseProtocol hw hb hn hv
    obtain ⟨U⟩ := minimal_vote h.toBaseProtocol hw hc hk hu
    -- A minimal rank-zero vote is echo-based, or its transfer source lies outside
    -- the observer's row and (by vote monotonicity) inside the row at the vote.
    have classify : ∀ {x}, (X : MinimalVote (M := M) (σ := σ) w a x 0) →
        (⟪w⟫ ⊨[M] σ.echoCertificate X.target x) ∨
          StrictEndingDepthChain M (Correlated M σ.correlationSymb) a w 1 := by
      intro x X
      have hX := predecessor_possible hw X.before
      rcases h.voteZeroBackward hX X.vote with he | ⟨s, _, hls, ht⟩
      · exact Or.inl (quorum_lift hw X.before he)
      · by_cases hs : Correlated M σ.correlationSymb w a s
        · obtain ⟨e, he, hv⟩ := observedAt_iff.mpr ht
          exact False.elim (X.minimal e he s _ hs (Nat.zero_le _) hv)
        · have hmono := h.voteMonotone hw X.before X.vote (Or.inl rfl)
          have hta : Correlated M σ.correlationSymb X.event X.target a :=
            hmono a (h.correlationSymm hw X.correlated)
          have hincl : ∀ y, Correlated M σ.correlationSymb w a y →
              Correlated M σ.correlationSymb X.event a y := by
            intro y hy
            exact h.correlationTrans hX (h.correlationSymm hX hta)
              (hmono y (h.correlationTrans hw (h.correlationSymm hw X.correlated) hy))
          have has : Correlated M σ.correlationSymb X.event a s :=
            h.correlationTrans hX (h.correlationSymm hX hta) hls
          exact Or.inr (strictEndingDepthChain_append
            (strictEndingDepthChain_zero hX ⟨X.target, h.correlationSymm hX hta⟩)
            X.before hw ⟨hincl, s, has, hs⟩ ⟨X.target, X.correlated⟩)
    rcases classify V with hV | hV
    · rcases classify U with hU | hU
      · have hVU := h.correlationTrans hw (h.correlationSymm hw V.correlated) U.correlated
        obtain ⟨e, f, he, hf, hp, hve, huf, hord⟩ := quorum_pair h.toBaseProtocol hw hVU hV hU
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
      · exact hU
    · exact hV
  | succ r ih =>
    obtain ⟨V⟩ := minimal_vote h.toBaseProtocol hw hb hn hv
    obtain ⟨U⟩ := minimal_vote h.toBaseProtocol hw hc hk hu
    have hVU := h.correlationTrans hw (h.correlationSymm hw V.correlated) U.correlated
    obtain ⟨e, f, he, hf, hplace, hve, huf, hord⟩ :=
      quorum_pair_before h.toBaseProtocol hw V.before U.before hVU
        (h.voteSuccBackward (predecessor_possible hw V.before) V.vote)
        (h.voteSuccBackward (predecessor_possible hw U.before) U.vote)
    have step : ∀ {v u}, v ≠ u →
        (V : MinimalVote (M := M) (σ := σ) w a v (r + 1)) →
        (U : MinimalVote (M := M) (σ := σ) w a u (r + 1)) →
        ∀ e f, e ≪ V.event → f ≪ U.event →
        (⟪e⟫ ⊨[M] σ.vote V.target v r) →
        (⟪f⟫ ⊨[M] σ.vote U.target u r) → e ≪ f → e.place = f.place →
        StrictEndingDepthChain M (Correlated M σ.correlationSymb) a w (r + 1 + 1) := by
      intro v u hvu V U e f he hf hve huf hef hplace
      have hfw := accessible_trans hw hf U.before
      have hfpos := predecessor_possible hw hfw
      have hVUw := h.correlationTrans hw (h.correlationSymm hw V.correlated) U.correlated
      -- Vote monotonicity at the later vote of the switch: `U.target`'s row at `f`
      -- contains its row at `w`.
      have hsw := h.voteMonotone hw hfw huf
        (Or.inr ⟨V.target, v, hvu, hVUw, (Sat.past _ _ _).mpr ⟨e, hef, hplace, hve⟩⟩)
      have hUa : Correlated M σ.correlationSymb f U.target a :=
        hsw a (h.correlationSymm hw U.correlated)
      have hincl : ∀ y, Correlated M σ.correlationSymb w a y →
          Correlated M σ.correlationSymb f a y := by
        intro y hy
        exact h.correlationTrans hfpos (h.correlationSymm hfpos hUa)
          (hsw y (h.correlationTrans hw (h.correlationSymm hw U.correlated) hy))
      have haV := hincl V.target V.correlated
      have haU := h.correlationSymm hfpos hUa
      have hVU := h.correlationTrans hfpos (h.correlationSymm hfpos haV) haU
      have hPast : ObservedAt M f (σ.vote V.target v r) := ⟨e, hef, hve⟩
      obtain ⟨c, k, hrk, hcU, hcv⟩ := h.voteNonEquivocation hfpos huf
        ((Sat.past _ _ _).mpr ⟨e, hef, hplace, hve⟩) (h.correlationSymm hfpos hVU) hvu
      have hcv := observedAt_iff.mpr hcv
      have hac := h.correlationTrans hfpos haU hcU
      have hnot : ¬ Correlated M σ.correlationSymb w a c := by
        intro hc
        obtain ⟨g, hgf, hgv⟩ := hcv
        exact U.minimal g (accessible_trans (predecessor_possible hw U.before) hgf hf)
          c k hc (by omega) hgv
      have chain := ih hfpos haV hac hvu (Nat.le_refl r) (by omega : r ≤ k) hPast hcv
      exact strictEndingDepthChain_append chain hfw hw ⟨hincl, c, hac, hnot⟩
        ⟨V.target, V.correlated⟩
    rcases hord with hef | hfe | heq
    · exact step hvu V U e f he hf hve huf hef hplace
    · exact step (Ne.symm hvu) U V f e hf he huf hve hfe hplace.symm
    · subst f
      exact False.elim (hvu (vote_value_eq hve huf))

/-- A vote at the depth threshold dominates all conflicting votes in its row. -/
theorem conflicting_rank_lt (h : ProtocolVM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {n k : Nat}
    (hb : Correlated M σ.correlationSymb w a b) (hc : Correlated M σ.correlationSymb w a c) (hvu : v ≠ u)
    (hn : maxDepth M (Correlated M σ.correlationSymb) a ≤ n)
    (hv : ObservedAt M w (σ.vote b v n))
    (hu : ObservedAt M w (σ.vote c u k)) :
    k < maxDepth M (Correlated M σ.correlationSymb) a := by
  by_cases hk : k < maxDepth M (Correlated M σ.correlationSymb) a
  · exact hk
  have hchain := conflict_yields_strict_depth_chain h hw hb hc hvu hn (by omega) hv hu
  have hbound := strictEndingDepthChain_le hchain
  omega

/-- Deliveries observed at a correlated world agree, even with unequal depths. -/
theorem agreement_at (h : ProtocolVM M σ) {w : World P S.EventType}
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
theorem agreement (h : ProtocolVM M σ) {a b v u : S.Value}
    (hab : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hv : Occurs M (σ.deliver a v)) (hu : Occurs M (σ.deliver b u)) : v = u := by
  exact agreement_at h (PreHistory.happensBeforeEq_refl _)
    (hab (Classical.ofNonempty)) hv hu

/-- Liveness 1. -/
theorem livenessOne (h : ProtocolVM M σ) {l v : S.Value}
    (hLiveQuorum : ∃ Q ∈ (M.learner l).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hUnique : UniqueOccurrence M σ.propose)
    (hObserved : ∃ e ∈ M.history.val,
      (⟪e⟫ ⊨[M] σ.live) ∧ ObservedAt M e (σ.propose v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver l v) := by
  exact ThyHBB4.livenessOne h.toBaseProtocol hLiveQuorum hUnique hObserved p hLive

/-- A delivered value is `UncontestedOrDelivered` throughout its correlation row. -/
theorem uncontestedOrDelivered_of_delivery (h : ProtocolVM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b v : S.Value}
    (hab : Correlated M σ.correlationSymb w a b)
    (hdel : ObservedAt M w (σ.deliver a v)) : UncontestedOrDelivered M σ w b v := by
  have hvote := observed_vote_of_observed_delivery h.toBaseProtocol hw hdel
  have haa := h.correlationTrans hw hab (h.correlationSymm hw hab)
  intro d u k hdb huv hu
  have had := h.correlationTrans hw hab (h.correlationSymm hw hdb)
  have hlt := conflicting_rank_lt h hw haa had (Ne.symm huv) (Nat.le_refl _) hvote hu
  exact ⟨a, hlt, hab, hdel⟩

/-- Liveness 2. -/
theorem livenessTwo (h : ProtocolVM M σ) {a b v : S.Value}
    (hCorrelation : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hLiveQuorum : ∃ Q ∈ (M.learner b).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hDelivered : Occurs M (σ.deliver a v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver b v) := by
  exact livenessTwo_of_uncontestedOrDelivered h.toBaseProtocol (uncontestedOrDelivered_of_delivery h) hCorrelation hLiveQuorum hDelivered p hLive

/-- Agreement in the paper's modal notation. -/
theorem agreement_modal (h : ProtocolVM M σ) {a b v u : S.Value}
    (hab : ⊨[M] □ᶠ[] (σ.correlation a b)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ
      (♢ᶠ↓[[]] (σ.deliver b u)) ⇒ᶠ (v ≃ᶠ u) := by
  exact occurrence_agreement_iff.mp (agreement h (correlated_final_iff_end.mpr hab))

/-- Liveness 1 in the paper's modal notation. -/
theorem livenessOne_modal (h : ProtocolVM M σ) {l v : S.Value}
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live)
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ⇒ᶠ
      σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) := by
  exact ThyHBB4.livenessOne_modal h.toBaseProtocol hLiveQuorum hUnique

/-- Liveness 2 in the paper's modal notation. -/
theorem livenessTwo_modal (h : ProtocolVM M σ) {a b v : S.Value}
    (hCorrelation : ⊨[M] □ᶠ[] (σ.correlation a b))
    (hLiveQuorum : ⊨[M] □ᶠ[[b]] σ.live) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ σ.live ⇒ᶠ ↕ᶠ (σ.deliver b v) := by
  exact occurrence_liveness_iff.mp (livenessTwo h
    (correlated_final_iff_end.mpr hCorrelation) (quorum_final_iff_end.mpr hLiveQuorum))

end ModalDistribution.Examples.ThyHBB4.VM

namespace ModalDistribution.Examples.ThyHBB4
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

/-- Causal monotonicity gives vote monotonicity. -/
theorem ProtocolCM.voteMonotone (h : ProtocolCM M σ) : VoteMonotonicity M σ := by
  intro w hw g c v n hg _ _ a ha
  exact h.causalMonotone hw ha hg

/-- CM ⇒ VM. -/
def ProtocolCM.toVM (h : ProtocolCM M σ) : ProtocolVM M σ :=
  { h.toBaseProtocol with voteMonotone := h.voteMonotone }

end ModalDistribution.Examples.ThyHBB4
