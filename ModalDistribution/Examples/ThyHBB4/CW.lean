import ModalDistribution.Examples.ThyHBB4.LivenessTwo
import ModalDistribution.Examples.ThyHBB4.StrictDepth

namespace ModalDistribution.Examples.ThyHBB4.CW

open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped PreHistory Formula

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

/-- Under CW, conflicting votes at ranks at least `r + 1` force `r + 1`
strictly decreasing nonempty rows. -/
theorem conflict_yields_strict_depth_chain (h : ProtocolCW M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {r n k : Nat}
    (hb : Correlated M σ.correlationSymb w a b) (hc : Correlated M σ.correlationSymb w a c) (hvu : v ≠ u)
    (hn : r + 1 ≤ n) (hk : r + 1 ≤ k)
    (hv : ObservedAt M w (σ.voteFromSomeSource b v n))
    (hu : ObservedAt M w (σ.voteFromSomeSource c u k)) :
    StrictEndingDepthChain M (Correlated M σ.correlationSymb) a w r := by
  induction r generalizing w b c v u n k with
  | zero => exact strictEndingDepthChain_zero hw ⟨b, hb⟩
  | succ r ih =>
    obtain ⟨V⟩ := minimal_vote h.toBaseProtocol hw hb hn hv
    obtain ⟨U⟩ := minimal_vote h.toBaseProtocol hw hc hk hu
    have hVU := h.correlationTrans hw (h.correlationSymm hw V.correlated) U.correlated
    obtain ⟨e, f, he, hf, hve, huf, hord⟩ :=
      h.comparisonWitness hw V.before U.before (by omega) hvu hVU V.vote U.vote
    have step : ∀ {v u}, v ≠ u →
        (V : MinimalVote (M := M) (σ := σ) w a v (r + 1 + 1)) →
        (U : MinimalVote (M := M) (σ := σ) w a u (r + 1 + 1)) →
        ∀ e f, e ≪ V.event → f ≪ U.event →
        (⟪e⟫ ⊨[M] σ.vote V.target V.source v (r + 1)) →
        (⟪f⟫ ⊨[M] σ.vote U.target U.source u (r + 1)) → e ≪ f →
        (∀ d, Correlated M σ.correlationSymb w V.target d → Correlated M σ.correlationSymb f U.target d) →
        StrictEndingDepthChain M (Correlated M σ.correlationSymb) a w (r + 1) := by
      intro v u hvu V U e f he hf hve huf hef hinc
      have hfw := accessible_trans hw hf U.before
      have hfpos := predecessor_possible hw hfw
      have haU : Correlated M σ.correlationSymb f a U.target :=
        h.correlationSymm hfpos (hinc a (h.correlationSymm hw V.correlated))
      have hincl : ∀ d, Correlated M σ.correlationSymb w a d → Correlated M σ.correlationSymb f a d := by
        intro d hd
        exact h.correlationTrans hfpos haU
          (hinc d (h.correlationTrans hw (h.correlationSymm hw V.correlated) hd))
      have haV := hincl V.target V.correlated
      have hVU := h.correlationTrans hfpos (h.correlationSymm hfpos haV) haU
      have hPast : ObservedAt M f (σ.voteFromSomeSource V.target v (r + 1)) :=
        ⟨e, hef, (Sat.exists_iff _ _).mpr ⟨V.source, hve⟩⟩
      obtain ⟨d, j, hrj, hdU, hdv⟩ :=
        h.voteLegal hfpos huf V.target v (r + 1) hVU hvu hPast
      have had := h.correlationTrans hfpos haU (h.correlationSymm hfpos hdU)
      have hnot : ¬ Correlated M σ.correlationSymb w a d := by
        intro hd
        obtain ⟨g, hgf, hgv⟩ := hdv
        obtain ⟨s, hgv⟩ := (Sat.exists_iff _ _).mp hgv
        exact U.minimal g (accessible_trans (predecessor_possible hw U.before) hgf hf)
          d s j hd (by omega) hgv
      have chain := ih hfpos haV had hvu (Nat.le_refl (r + 1)) (by omega : r + 1 ≤ j)
        hPast hdv
      exact strictEndingDepthChain_append chain hfw hw ⟨hincl, d, had, hnot⟩
        ⟨V.target, V.correlated⟩
    rcases hord with ⟨hef, hinc⟩ | ⟨hfe, hinc⟩
    · exact step hvu V U e f he hf (by simpa using hve) (by simpa using huf) hef hinc
    · apply step (Ne.symm hvu) U V f e hf he (by simpa using huf) (by simpa using hve) hfe
      intro d hd
      exact hinc d (h.correlationTrans hw hVU hd)

/-- Lemma 3.1: positive-rank conflicts consume at least their rank in depth. -/
theorem conflict_rank_le_depth (h : ProtocolCW M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {r n k : Nat}
    (hr : 1 ≤ r) (hb : Correlated M σ.correlationSymb w a b) (hc : Correlated M σ.correlationSymb w a c) (hvu : v ≠ u)
    (hn : r ≤ n) (hk : r ≤ k)
    (hv : ObservedAt M w (σ.voteFromSomeSource b v n))
    (hu : ObservedAt M w (σ.voteFromSomeSource c u k)) :
    r ≤ maxDepth M (Correlated M σ.correlationSymb) a := by
  have hchain := conflict_yields_strict_depth_chain h hw hb hc hvu
    (by omega : r - 1 + 1 ≤ n) (by omega : r - 1 + 1 ≤ k) hv hu
  have hbound := strictEndingDepthChain_le hchain
  omega

/-- The delivery-vote threshold excludes rivals above the anchor's depth. -/
theorem conflicting_rank_le (h : ProtocolCW M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {n k : Nat}
    (hb : Correlated M σ.correlationSymb w a b) (hc : Correlated M σ.correlationSymb w a c) (hvu : v ≠ u)
    (hn : maxDepth M (Correlated M σ.correlationSymb) a + 1 ≤ n)
    (hv : ObservedAt M w (σ.voteFromSomeSource b v n))
    (hu : ObservedAt M w (σ.voteFromSomeSource c u k)) :
    k ≤ maxDepth M (Correlated M σ.correlationSymb) a := by
  by_cases hk : k ≤ maxDepth M (Correlated M σ.correlationSymb) a
  · exact hk
  have hbound := conflict_rank_le_depth h hw (by omega) hb hc hvu hn (by omega) hv hu
  omega

/-- A delivery-rank vote supplies each existential witness in legality. -/
theorem high_vote_legal (h : ProtocolCW M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v : S.Value} {n : Nat}
    (hb : Correlated M σ.correlationSymb w a b) (hc : Correlated M σ.correlationSymb w a c)
    (hn : maxDepth M (Correlated M σ.correlationSymb) a + 1 ≤ n)
    (hv : ObservedAt M w (σ.voteFromSomeSource b v n)) : Legal M σ w c v := by
  intro d u k hdc huv hu
  have had := h.correlationTrans hw hc (h.correlationSymm hw hdc)
  have hle := conflicting_rank_le h hw hb had (Ne.symm huv) hn hv hu
  exact ⟨b, n, by omega, h.correlationTrans hw (h.correlationSymm hw hb) hc, hv⟩

/-- Deliveries observed at a correlated world agree, without equal-depth assumptions. -/
theorem agreement_at (h : ProtocolCW M σ) {w : World P S.EventType}
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
    have hlt := conflicting_rank_le h hw haa hab heq (by omega) hv' hu'
    omega
  · have hba := h.correlationSymm hw hab
    have hbb := h.correlationTrans hw hba hab
    have hlt := conflicting_rank_le h hw hbb hba (Ne.symm heq) (by omega) hu' hv'
    omega

/-- End-of-time agreement when every final participant correlates the learners. -/
theorem agreement (h : ProtocolCW M σ) {a b v u : S.Value}
    (hab : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hv : Occurs M (σ.deliver a v)) (hu : Occurs M (σ.deliver b u)) : v = u := by
  exact agreement_at h (PreHistory.happensBeforeEq_refl _)
    (hab (Classical.ofNonempty)) hv hu

/-- A source delivery makes its value legal throughout the observer's target row. -/
theorem delivery_legal (h : ProtocolCW M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b v : S.Value}
    (hab : Correlated M σ.correlationSymb w a b)
    (hv : ObservedAt M w (σ.deliver a v)) : Legal M σ w b v := by
  have hvote := observed_vote_of_observed_delivery h.toBaseProtocol hw hv
  have haa := h.correlationTrans hw hab (h.correlationSymm hw hab)
  exact high_vote_legal h hw haa hab (Nat.le_refl _) hvote

/-- Liveness 1 under comparison-witness coherence. -/
theorem livenessOne (h : ProtocolCW M σ) {l v : S.Value}
    (hLiveQuorum : ∃ Q ∈ (M.learner l).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hUnique : UniqueOccurrence M σ.propose)
    (hObserved : ∃ e ∈ M.history.val,
      (⟪e⟫ ⊨[M] σ.live) ∧ ObservedAt M e (σ.propose v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver l v) := by
  exact ThyHBB4.livenessOne h.toBaseProtocol hLiveQuorum hUnique hObserved p hLive

/-- Liveness 2 under comparison-witness coherence. -/
theorem livenessTwo (h : ProtocolCW M σ) {a b v : S.Value}
    (hCorrelation : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hLiveQuorum : ∃ Q ∈ (M.learner b).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hDelivered : Occurs M (σ.deliver a v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver b v) := by
  exact livenessTwo_of_delivery_legal h.toBaseProtocol (delivery_legal h) hCorrelation hLiveQuorum hDelivered p hLive

/-- Agreement in the paper's modal notation. -/
theorem agreement_modal (h : ProtocolCW M σ) {a b v u : S.Value}
    (hab : ⊨[M] □ᶠ[] (σ.correlation a b)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ
      (♢ᶠ↓[[]] (σ.deliver b u)) ⇒ᶠ (v ≃ᶠ u) := by
  exact occurrence_agreement_iff.mp (agreement h (correlated_final_iff_end.mpr hab))

/-- Liveness 1 in the paper's modal notation. -/
theorem livenessOne_modal (h : ProtocolCW M σ) {l v : S.Value}
    (hLiveQuorum : ⊨[M] □ᶠ[[l]] σ.live)
    (hUnique : ⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) :
    ⊨[M] (♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ⇒ᶠ
      σ.live ⇒ᶠ ↕ᶠ (σ.deliver l v) := by
  exact ThyHBB4.livenessOne_modal h.toBaseProtocol hLiveQuorum hUnique

/-- Liveness 2 in the paper's modal notation. -/
theorem livenessTwo_modal (h : ProtocolCW M σ) {a b v : S.Value}
    (hCorrelation : ⊨[M] □ᶠ[] (σ.correlation a b))
    (hLiveQuorum : ⊨[M] □ᶠ[[b]] σ.live) :
    ⊨[M] (♢ᶠ↓[[]] (σ.deliver a v)) ⇒ᶠ σ.live ⇒ᶠ ↕ᶠ (σ.deliver b v) := by
  exact occurrence_liveness_iff.mp (livenessTwo h
    (correlated_final_iff_end.mpr hCorrelation) (quorum_final_iff_end.mpr hLiveQuorum))

end ModalDistribution.Examples.ThyHBB4.CW
