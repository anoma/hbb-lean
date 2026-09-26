import ModalDistribution.Examples.ThyHBB4.LivenessTwo
import ModalDistribution.Examples.ThyHBB4.FastPath

namespace ModalDistribution.Examples.ThyHBB4
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

/-- Causal monotonicity gives vote monotonicity. -/
theorem ProtocolCM.voteMonotone (h : ProtocolCM M σ) : VoteMonotonicity M σ := by
  intro w hw g c v n hg _ _ a ha
  exact h.causalMonotone hw ha hg

end ModalDistribution.Examples.ThyHBB4

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
    (hv : ObservedAt M w (σ.vote b v n))
    (hu : ObservedAt M w (σ.vote c u k)) :
    EndingDepthChain M (Correlated M σ.correlationSymb) a w (r + 1) := by
  induction r generalizing w b c v u n k with
  | zero =>
    obtain ⟨V⟩ := minimal_vote h hw hb hn hv
    obtain ⟨U⟩ := minimal_vote h hw hc hk hu
    -- A minimal rank-zero vote is echo-based, or its transfer source lies outside
    -- the observer's row and (by causal monotonicity) inside the row at the vote.
    have classify : ∀ {x}, (X : MinimalVote (M := M) (σ := σ) w a x 0) →
        (⟪w⟫ ⊨[M] σ.echoCertificate X.target x) ∨
          EndingDepthChain M (Correlated M σ.correlationSymb) a w 1 := by
      intro x X
      have hX := predecessor_possible hw X.before
      rcases h.voteZeroBackward hX X.vote with he | ⟨s, _, hls, ht⟩
      · exact Or.inl (quorum_lift hw X.before he)
      · by_cases hs : Correlated M σ.correlationSymb w a s
        · obtain ⟨e, he, hv⟩ := observedAt_iff.mpr ht
          exact False.elim (X.minimal e he s _ hs (Nat.zero_le _) hv)
        · have hcorr : Correlated M σ.correlationSymb X.event a s :=
            h.correlationTrans hX (h.causalMonotone hw X.correlated X.before) hls
          exact Or.inr (endingDepthChain_append_of_lost_correlation h hw X.before hcorr hs
            (endingDepthChain_zero _ _ hX))
    rcases classify V with hV | hV
    · rcases classify U with hU | hU
      · have hVU := h.correlationTrans hw (h.correlationSymm hw V.correlated) U.correlated
        obtain ⟨e, f, he, hf, hp, hve, huf, hord⟩ := quorum_pair h hw hVU hV hU
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
    obtain ⟨V⟩ := minimal_vote h hw hb hn hv
    obtain ⟨U⟩ := minimal_vote h hw hc hk hu
    have hVU := h.correlationTrans hw (h.correlationSymm hw V.correlated) U.correlated
    obtain ⟨e, f, he, hf, hplace, hve, huf, hord⟩ := quorum_pair_before h hw V.before U.before hVU
      (h.voteSuccBackward (predecessor_possible hw V.before) V.vote)
      (h.voteSuccBackward (predecessor_possible hw U.before) U.vote)
    have step : ∀ {v u}, v ≠ u →
        (V : MinimalVote (M := M) (σ := σ) w a v (r + 1)) →
        (U : MinimalVote (M := M) (σ := σ) w a u (r + 1)) →
        ∀ e f, e ≪ V.event → f ≪ U.event →
        (⟪e⟫ ⊨[M] σ.vote V.target v r) →
        (⟪f⟫ ⊨[M] σ.vote U.target u r) → e ≪ f → e.place = f.place →
        EndingDepthChain M (Correlated M σ.correlationSymb) a w (r + 1 + 1) := by
      intro v u hvu V U e f he hf hve huf hef hplace
      have hfw := accessible_trans hw hf U.before
      have hfpos := predecessor_possible hw hfw
      have haV := h.causalMonotone hw V.correlated hfw
      have haU := h.causalMonotone hw U.correlated hfw
      have hVU := h.correlationTrans hfpos (h.correlationSymm hfpos haV) haU
      have hPast : ObservedAt M f (σ.vote V.target v r) := ⟨e, hef, hve⟩
      obtain ⟨c, k, hrk, hcU, hcv⟩ := h.voteNonEquivocation hfpos huf
        ((Sat.past _ _ _).mpr ⟨e, hef, hplace, hve⟩) (h.correlationSymm hfpos hVU) hvu
      have hcv := observedAt_iff.mpr hcv
      have hcU := h.correlationSymm hfpos hcU
      have hac := h.correlationTrans hfpos haU (h.correlationSymm hfpos hcU)
      have hnot : ¬ Correlated M σ.correlationSymb w a c := by
        intro hc
        obtain ⟨g, hgf, hgv⟩ := hcv
        exact U.minimal g (accessible_trans (predecessor_possible hw U.before) hgf hf)
          c k hc (by omega) hgv
      have chain := ih hfpos haV hac hvu (Nat.le_refl r) (by omega : r ≤ k) hPast hcv
      exact endingDepthChain_append_of_lost_correlation h hw hfw hac hnot chain
    rcases hord with hef | hfe | heq
    · exact step hvu V U e f he hf hve huf hef hplace
    · exact step (Ne.symm hvu) U V f e hf he huf hve hfe hplace.symm
    · subst f
      exact False.elim (hvu (vote_value_eq hve huf))

/-- A vote at the depth threshold dominates all conflicting votes in its row. -/
theorem conflicting_rank_lt (h : ProtocolCM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {n k : Nat}
    (hb : Correlated M σ.correlationSymb w a b) (hc : Correlated M σ.correlationSymb w a c) (hvu : v ≠ u)
    (hn : maxDepth M (Correlated M σ.correlationSymb) a ≤ n)
    (hv : ObservedAt M w (σ.vote b v n))
    (hu : ObservedAt M w (σ.vote c u k)) :
    k < maxDepth M (Correlated M σ.correlationSymb) a := by
  by_cases hk : k < maxDepth M (Correlated M σ.correlationSymb) a
  · exact hk
  have hchain := conflict_yields_depth_chain h hw hb hc hvu hn (by omega) hv hu
  have hbound := endingDepthChain_le hchain
  omega

/-- Deliveries observed at a correlated world agree, even with unequal depths. The
learners must be correlated at every final world so that the fast clause's
end-of-time guarantee applies. -/
theorem agreement_at (h : ProtocolCM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b v u : S.Value}
    (habFinal : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hab : Correlated M σ.correlationSymb w a b)
    (hv : ObservedAt M w (σ.deliver a v))
    (hu : ObservedAt M w (σ.deliver b u)) : v = u := by
  have hba := h.correlationSymm hw hab
  have haa := h.correlationTrans hw hab hba
  have hbb := h.correlationTrans hw hba hab
  -- Sequential quorums for `a` and `b` at `w`, from the fast clause's guarantee.
  have hQa : ∀ {e : World P S.EventType},
      (⟪e⟫ ⊨[M] ⤒ᶠ (σ.correlation a a ⇒ᶠ □ᶠ[[a]] Formula.seq)) → SequentialQuorumAt M a w := by
    intro e hg
    have hf := habFinal e.place
    have hpos : (finalWorld M e.place).time ⪯ M.history.val := PreHistory.happensBeforeEq_refl _
    exact sequentialQuorumAt_of_guarantee hw hg
      (h.correlationTrans hpos hf (h.correlationSymm hpos hf))
  have hQb : ∀ {e : World P S.EventType},
      (⟪e⟫ ⊨[M] ⤒ᶠ (σ.correlation b b ⇒ᶠ □ᶠ[[b]] Formula.seq)) → SequentialQuorumAt M b w := by
    intro e hg
    have hf := habFinal e.place
    have hpos : (finalWorld M e.place).time ⪯ M.history.val := PreHistory.happensBeforeEq_refl _
    exact sequentialQuorumAt_of_guarantee hw hg
      (h.correlationTrans hpos (h.correlationSymm hpos hf) hf)
  rcases delivery_cases h.toBaseProtocol hw hv with hca | ⟨hechoa, ea, _, hga⟩
  · rcases delivery_cases h.toBaseProtocol hw hu with hcb | ⟨hechob, eb, _, hgb⟩
    · -- Both deliveries at the decision rank: the depth argument.
      have hv' := quorum_witness hca
      have hu' := quorum_witness hcb
      by_cases heq : v = u
      · exact heq
      apply False.elim
      by_cases hle : maxDepth M (Correlated M σ.correlationSymb) a ≤ maxDepth M (Correlated M σ.correlationSymb) b
      · have hlt := conflicting_rank_lt h hw haa hab heq (by omega) hv' hu'
        omega
      · have hlt := conflicting_rank_lt h hw hbb hba (Ne.symm heq) (by omega) hu' hv'
        omega
    · -- `b` delivered fast, and `a` has an observed `v`-vote.
      exact value_of_echo_unanimity_at h.toBaseProtocol h.voteMonotone hw (hQb hgb) hechob hba
        (quorum_witness hca)
  · rcases delivery_cases h.toBaseProtocol hw hu with hcb | ⟨hechob, _, _, _⟩
    · -- `a` delivered fast, and `b` has an observed `u`-vote.
      exact (value_of_echo_unanimity_at h.toBaseProtocol h.voteMonotone hw (hQa hga) hechoa hab
        (quorum_witness hcb)).symm
    · -- Both fast: a member of `a`'s sequential quorum echoed both values.
      obtain ⟨Q, hQ, hQseq⟩ := hQa hga
      obtain ⟨q, hq⟩ := Semifilter.quorum_nonempty hQ
      have hseq := hQseq q hq
      obtain ⟨e, he, heq, hve⟩ := hechoa q hseq
      obtain ⟨f, hf, hfq, huf⟩ := hechob q hseq
      exact echo_unique_of_sequential h.toBaseProtocol hw hseq he hf heq hfq hve huf

/-- End-of-time agreement when every final participant correlates the learners. -/
theorem agreement (h : ProtocolCM M σ) {a b v u : S.Value}
    (hab : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hv : Occurs M (σ.deliver a v)) (hu : Occurs M (σ.deliver b u)) : v = u := by
  exact agreement_at h (PreHistory.happensBeforeEq_refl _) hab
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

/-- A delivered value is `UncontestedOrDelivered` throughout its correlation row:
every conflicting vote in the row is outranked by the source's decision rank
(`conflicting_rank_lt`). -/
theorem uncontestedOrDelivered_of_delivery (h : ProtocolCM M σ) {a b v : S.Value}
    (hab : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b) (q : P)
    (hdel : ObservedAt M (finalWorld M q) (σ.deliver a v)) :
    UncontestedOrDelivered M σ (finalWorld M q) b v := by
  have hw : (finalWorld M q).time ⪯ M.history.val := PreHistory.happensBeforeEq_refl _
  have habq := hab q
  have haa := h.correlationTrans hw habq (h.correlationSymm hw habq)
  intro d u k hdb huv hu
  have had := h.correlationTrans hw habq (h.correlationSymm hw hdb)
  rcases delivery_cases h.toBaseProtocol hw hdel with hcert | ⟨hecho, e, _, hg⟩
  · have hlt := conflicting_rank_lt h hw haa had (Ne.symm huv) (Nat.le_refl _)
      (quorum_witness hcert) hu
    exact ⟨a, hlt, habq, hdel⟩
  · have hf := hab e.place
    have hpos : (finalWorld M e.place).time ⪯ M.history.val := PreHistory.happensBeforeEq_refl _
    have hQa := sequentialQuorumAt_of_guarantee hw hg
      (h.correlationTrans hpos hf (h.correlationSymm hpos hf))
    exact absurd (value_of_echo_unanimity_at h.toBaseProtocol h.voteMonotone hw hQa hecho had hu) huv

/-- Liveness 2 for the causal-monotonicity theory. -/
theorem livenessTwo (h : ProtocolCM M σ) {a b v : S.Value}
    (hCorrelation : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hLiveQuorum : ∃ Q ∈ (M.learner b).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hDelivered : Occurs M (σ.deliver a v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver b v) := by
  exact livenessTwo_of_uncontestedOrDelivered h.toBaseProtocol (uncontestedOrDelivered_of_delivery h hCorrelation) hCorrelation hLiveQuorum hDelivered p hLive

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
