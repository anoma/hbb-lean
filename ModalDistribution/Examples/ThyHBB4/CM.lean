import ModalDistribution.Examples.ThyHBB4.LivenessTwo

namespace ModalDistribution.Examples.ThyHBB4.CM
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

theorem endingDepthChain_append_of_lost_correlation (h : ProtocolCM M σ) {w e : World P S.EventType}
    (hw : w.time ⪯ M.history.val) (he : e ≪ w) {a c : S.Value} {n : Nat}
    (hc : Corr M σ e a c) (hnc : ¬ Corr M σ w a c)
    (chain : EndingDepthChain M (Corr M σ) a e n) :
    EndingDepthChain M (Corr M σ) a w (n + 1) := by
  apply endingDepthChain_append chain he hw
  intro u hu heq
  have huCorr : Corr M σ u a c := by
    rcases hu with hu | rfl
    · exact h.causalMonotone (predecessor_possible hw he) hc hu
    · exact hc
  exact hnc (Eq.mp (congrFun heq c) huCorr)

/-- Conflicting ranks force a chain of strictly changing correlation rows. -/
theorem conflict_depth (h : ProtocolCM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {r n k : Nat}
    (hb : Corr M σ w a b) (hc : Corr M σ w a c) (hvu : v ≠ u)
    (hn : r ≤ n) (hk : r ≤ k)
    (hv : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.voteFromSomeSource b v n))
    (hu : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.voteFromSomeSource c u k)) :
    EndingDepthChain M (Corr M σ) a w (r + 1) := by
  induction r generalizing w b c v u n k with
  | zero =>
    obtain ⟨V⟩ := minimal_vote h hw hb hn hv
    obtain ⟨U⟩ := minimal_vote h hw hc hk hu
    have outside : ∀ {x}, (X : MinimalVote (M := M) (σ := σ) w a x 0) →
        ¬ Corr M σ w a X.source → EndingDepthChain M (Corr M σ) a w 1 := by
      intro x X hnot
      have hX := predecessor_possible hw X.before
      have hcorr : Corr M σ X.event a X.source := by
        have hab := h.causalMonotone hw X.correlated X.before
        rcases h.voteSource hX X.vote with heq | hsrc
        · exact False.elim (hnot (heq ▸ X.correlated))
        · exact h.correlationTrans hX hab hsrc
      exact endingDepthChain_append_of_lost_correlation h hw X.before hcorr hnot
        (endingDepthChain_zero _ _ hX)
    by_cases hV : Corr M σ w a V.source
    · by_cases hU : Corr M σ w a U.source
      · have echo : ∀ {x}, (X : MinimalVote (M := M) (σ := σ) w a x 0) →
            Corr M σ w a X.source → (⟪w⟫ ⊨[M] σ.echoCertificate X.target x) := by
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
        EndingDepthChain M (Corr M σ) a w (r + 1 + 1) := by
      intro v u hvu V U e f he hf hve huf hef
      have hfw := accessible_trans hw hf U.before
      have hfpos := predecessor_possible hw hfw
      have haV := h.causalMonotone hw V.correlated hfw
      have haU := h.causalMonotone hw U.correlated hfw
      have hVU := h.correlationTrans hfpos (h.correlationSymm hfpos haV) haU
      have hPast : ⟪f⟫ ⊨[M] ♢ᶠ↓[[]] (σ.voteFromSomeSource V.target v r) :=
        past_exists_iff.mpr ⟨e, hef, (Sat.exists_iff _ _).mpr ⟨V.source, hve⟩⟩
      obtain ⟨c, k, hrk, hcU, hcv⟩ := h.voteLegal hfpos huf V.target v r hVU hvu hPast
      have hac := h.correlationTrans hfpos haU (h.correlationSymm hfpos hcU)
      have hnot : ¬ Corr M σ w a c := by
        intro hc
        obtain ⟨g, hgf, hgv⟩ := past_exists_iff.mp hcv
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
    (hb : Corr M σ w a b) (hc : Corr M σ w a c) (hvu : v ≠ u)
    (hn : maxDepth M (Corr M σ) a - 1 ≤ n)
    (hv : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.voteFromSomeSource b v n))
    (hu : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.voteFromSomeSource c u k)) :
    k < maxDepth M (Corr M σ) a - 1 := by
  by_cases hk : k < maxDepth M (Corr M σ) a - 1
  · exact hk
  have hchain := conflict_depth h hw hb hc hvu hn (by omega) hv hu
  have hbound := endingDepthChain_le hchain
  have hpos := maxDepth_pos M (Corr M σ) a
  omega

/-- The dominating vote is the witness required by every legality clause. -/
theorem high_vote_legal (h : ProtocolCM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v : S.Value} {n : Nat}
    (hb : Corr M σ w a b) (hc : Corr M σ w a c)
    (hn : maxDepth M (Corr M σ) a - 1 ≤ n)
    (hv : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.voteFromSomeSource b v n)) : Legal M σ w c v := by
  intro d u k hdc huv hu
  have had := h.correlationTrans hw hc (h.correlationSymm hw hdc)
  have hlt := conflicting_rank_lt h hw hb had (Ne.symm huv) hn hv hu
  exact ⟨b, n, by omega, h.correlationTrans hw (h.correlationSymm hw hb) hc, hv⟩

/-- Deliveries observed at a correlated world agree, even with unequal depths. -/
theorem agreement_at (h : ProtocolCM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b v u : S.Value}
    (hab : Corr M σ w a b)
    (hv : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver a v))
    (hu : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver b u)) : v = u := by
  have hv' := observed_vote_of_observed_delivery h.toBaseProtocol hw hv
  have hu' := observed_vote_of_observed_delivery h.toBaseProtocol hw hu
  by_cases heq : v = u
  · exact heq
  apply False.elim
  by_cases hle : maxDepth M (Corr M σ) a ≤ maxDepth M (Corr M σ) b
  · have haa := h.correlationTrans hw hab (h.correlationSymm hw hab)
    have hlt := conflicting_rank_lt h hw haa hab heq (by omega) hv' hu'
    omega
  · have hba := h.correlationSymm hw hab
    have hbb := h.correlationTrans hw hba hab
    have hlt := conflicting_rank_lt h hw hbb hba (Ne.symm heq) (by omega) hu' hv'
    omega

/-- End-of-time agreement under the manuscript's permanent-correlation premise. -/
theorem agreement (h : ProtocolCM M σ) {a b v u : S.Value}
    (hab : ∀ p : P, Corr M σ ⟨p, †, M.history.val⟩ a b) :
    ∀ p : P, (⟪(p, †, M.history.val)⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver a v)) →
      (⟪(p, †, M.history.val)⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver b u)) → v = u := by
  intro p hv hu
  exact agreement_at h (PreHistory.happensBeforeEq_refl _) (hab p) hv hu
/-- Liveness 1 under causal monotonicity. -/
theorem livenessOne (h : ProtocolCM M σ) {l v : S.Value}
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live)
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ⇒ᶠ
      σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) := by
  exact ThyHBB4.livenessOne h.toBaseProtocol hLiveQuorum hUnique

/-- Causal monotonicity makes a delivered value legal throughout its correlation row. -/
theorem delivery_legal (h : ProtocolCM M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b v : S.Value}
    (hab : Corr M σ w a b)
    (hdel : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver a v)) : Legal M σ w b v := by
  have hvote := observed_vote_of_observed_delivery h.toBaseProtocol hw hdel
  have haa := h.correlationTrans hw hab (h.correlationSymm hw hab)
  exact high_vote_legal h hw haa hab (by omega) hvote

/-- Liveness 2 for the causal-monotonicity theory. -/
theorem livenessTwo (h : ProtocolCM M σ) {a b v : S.Value}
    (hCorrelation : ⊨[M] □ᶠ[] (σ.correlation a b))
    (hLiveQuorum : ⊨[M] □ᶠ[[b]] σ.live) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ σ.live ⇒ᶠ ↕ᶠ (σ.deliver b v) := by
  exact livenessTwo_of_delivery_legal h (delivery_legal h) hCorrelation hLiveQuorum

end ModalDistribution.Examples.ThyHBB4.CM
