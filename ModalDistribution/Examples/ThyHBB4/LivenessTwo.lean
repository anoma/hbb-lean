import ModalDistribution.Examples.ThyHBB4.Liveness

namespace ModalDistribution.Examples.ThyHBB4
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

/-- A live fixed-source transfer certificate seeds the destination's rank-zero quorum.
Only `Q_a E` instances of Knowledge are used. -/
theorem transfer_zero_quorum (h : BaseProtocol M σ) {a b s v : S.Value}
    (hlegal : ∀ p : P, Legal M σ ⟨p, †, M.history.val⟩ b v)
    (hcorr : ∀ p : P, Correlated M σ.correlationSymb ⟨p, †, M.history.val⟩ b a)
    (hlive : ⊨[M] □ᶠ[[b]] σ.live)
    (hcert : ⊨[M] ♢ᶠ↓[[]] (σ.live ∧ᶠ
      σ.fixedSourceCertificate a s v (maxDepth M (Correlated M σ.correlationSymb) a))) :
    ⊨[M] □ᶠ↓[[b]] (σ.live ∧ᶠ σ.vote b a v 0) := by
  have hlearn : ⊨[M] □ᶠ↓[[b]] (σ.live ∧ᶠ
      σ.fixedSourceCertificate a s v (maxDepth M (Correlated M σ.correlationSymb) a)) :=
    live_eventually_knows_quorum (M := M) (hTheory := h.thyLive) (hLive := hlive) (hQuorum := hcert)
  apply ThyHBB1.boxPast_live_of_eventual_quorum h.thyLive
    (σ.fixedSourceCertificate a s v (maxDepth M (Correlated M σ.correlationSymb) a)) (σ.vote b a v 0) b hlearn
  intro w hw
  apply Sat.imp_intro
  intro hboth
  obtain ⟨hl, hc⟩ := (Sat.and (M := M) (w := w) _ _).mp hboth
  exact h.voteZeroTransferForward hw hl (hlegal w.place) (hcorr w.place)
    (fixedSourceCertificate_to_voteCertificate hc)

/-- A delivery quorum meets the destination's live quorum at a live vote.
Its backward justification is a fixed-source certificate admissible for Knowledge. -/
theorem delivery_live_fixedSourceCertificate (h : BaseProtocol M σ) {a b v : S.Value}
    (hcorr : ∀ p : P, Correlated M σ.correlationSymb ⟨p, †, M.history.val⟩ a b)
    (hlive : ⊨[M] □ᶠ[[b]] σ.live)
    {d : World P S.EventType} (hd : d ∈ M.history.val)
    (hdel : ⟪d⟫ ⊨[M] σ.deliver a v) :
    ∃ s, ⊨[M] ♢ᶠ↓[[]] (σ.live ∧ᶠ
      σ.fixedSourceCertificate a s v (maxDepth M (Correlated M σ.correlationSymb) a)) := by
  have hdpos := M.time_le_of_mem hd
  have hdback := h.deliverBackward hdpos hdel
  obtain ⟨Q, hQ, hVotes⟩ := (sat_box_singleton_exists (M := M) (w := d)
    (l := a) (φ := ↓ᶠ (σ.voteFromSomeSource a v (maxDepth M (Correlated M σ.correlationSymb) a + 1)))).mp hdback
  let w : World P S.EventType := ⟨d.place, †, M.history.val⟩
  obtain ⟨T, hT, hLives⟩ := (sat_box_singleton_exists (M := M) (w := w)
    (l := b) (φ := σ.live)).mp (hlive d.place)
  have hinter := h.correlationSeq (PreHistory.happensBeforeEq_refl _) (hcorr d.place)
  obtain ⟨p, hp, _⟩ := (sat_diamond_pair_iff (M := M) (w := w)
    (l := a) (l' := b) (φ := Formula.seq)).mp hinter Q hQ T hT
  obtain ⟨t, ht, hplace, hsome⟩ := (Sat.past (M := M)
    (w := ⟨p, †, d.time⟩) _).mp (hVotes p hp.1)
  have htmem : t ∈ M.history.val :=
    History.subset_of_happensBefore (History.happensBefore_of_mem hd) t ht
  obtain ⟨s, hvote⟩ := voteFromSomeSource_iff.mp hsome
  have hcert := h.voteSuccBackward (M.time_le_of_mem htmem) hvote
  have hlEnd : ⟪t⟫ ⊨[M] ⤒ᶠ σ.live := by
    apply (Sat.atEnd M t _).mpr
    simpa only [hplace] using hLives p hp.2
  have hlt : ⟪t⟫ ⊨[M] σ.live :=
    Sat.iff_mpr M t (thyLive_liveAlways h.thyLive (M.time_le_of_mem htmem)) hlEnd
  refine ⟨s, ?_⟩
  intro q
  apply (Sat.diamond_nil (M := M) (w := ⟨q, †, M.history.val⟩) _).mpr
  refine ⟨t.place, ?_⟩
  apply (Sat.past (M := M) (w := ⟨t.place, †, M.history.val⟩) _).mpr
  exact ⟨t, htmem, rfl, Sat.and_intro M t hlt hcert⟩

/-- Liveness 2: delivery transfers between permanently correlated learners
when the destination has a live quorum. -/
theorem livenessTwo_of_delivery_legal (h : BaseProtocol M σ)
    (hDeliveryLegal : ∀ {w : World P S.EventType}, w.time ⪯ M.history.val →
      ∀ {a b v : S.Value}, Correlated M σ.correlationSymb w a b →
      ObservedAt M w (σ.deliver a v) → Legal M σ w b v)
    {a b v : S.Value}
    (hCorrelation : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hLiveQuorum : ∃ Q ∈ (M.learner b).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hDelivered : Occurs M (σ.deliver a v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver b v) := by
  obtain ⟨d, hd, hdval⟩ := hDelivered
  have hlegal : ∀ q, Legal M σ (finalWorld M q) b v := fun q =>
    hDeliveryLegal (PreHistory.happensBeforeEq_refl _) (hCorrelation q) ⟨d, hd, hdval⟩
  have hlive := quorum_final_iff_end.mp hLiveQuorum
  obtain ⟨s, hcert⟩ := delivery_live_fixedSourceCertificate h hCorrelation hlive hd hdval
  have hsource : ∀ q, Correlated M σ.correlationSymb (finalWorld M q) b a :=
    fun q => h.correlationSymm (PreHistory.happensBeforeEq_refl _) (hCorrelation q)
  have hzero := transfer_zero_quorum h hlegal hsource hlive hcert
  apply (occursAt_iff (w := finalWorld M p)).mpr
  exact Sat.imp_elim (M := M) (w := finalWorld M p) (deliver_of_live_zero_quorum h hlegal (fun q => Or.inr (hsource q)) hzero p) hLive

end ModalDistribution.Examples.ThyHBB4
