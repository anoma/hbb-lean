import ModalDistribution.Examples.ThyHBB4.Liveness

namespace ModalDistribution.Examples.ThyHBB4
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

variable {S : Signature} {P : Type} [Nonempty P]
variable {M : Model S P} {σ : ProtocolSignature S}

/-- A live observed vote at the source's decision rank seeds the destination's
rank-zero quorum. Only `Q_b E` and `known` instances of Knowledge are used. -/
theorem transfer_zero_quorum (h : BaseProtocol M σ) {a b v : S.Value}
    (huod : ∀ p : P, UncontestedOrDelivered M σ ⟨p, †, M.history.val⟩ b v)
    (hcorr : ∀ p : P, Correlated M σ.correlationSymb ⟨p, †, M.history.val⟩ b a)
    (hlive : ⊨[M] □ᶠ[[b]] σ.live)
    (hvote : ⊨[M] ♢ᶠ↓[[]] (σ.live ∧ᶠ σ.vote a v (σ.depthBound a))) :
    ⊨[M] □ᶠ↓[[b]] (σ.live ∧ᶠ σ.vote b v 0) := by
  have hlearn : ⊨[M] □ᶠ↓[[b]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.vote a v (σ.depthBound a))) :=
    live_eventually_knows_performed (M := M) (hTheory := h.thyLive) (hLive := hlive) (hEvent := hvote)
  apply ThyHBB1.boxPast_live_of_eventual_quorum h.thyLive
    (♢ᶠ↓[[]] (σ.vote a v (σ.depthBound a))) (σ.vote b v 0) b hlearn
  intro w hw
  apply Sat.imp_intro
  intro hboth
  obtain ⟨hl, hc⟩ := (Sat.and (M := M) (w := w) _ _).mp hboth
  exact h.voteZeroTransferForward hw hl (huod w.place) (hcorr w.place) hc

/-- Members of the destination's live quorum are live at all their events. -/
theorem live_at_event_of_live_quorum (h : BaseProtocol M σ) {b : S.Value}
    (hlive : ⊨[M] □ᶠ[[b]] σ.live) {q : P} :
    ∃ T ∈ (M.learner b).quorums, ∀ p ∈ T, ∀ {t : World P S.EventType},
      t ∈ M.history.val → t.place = p → (⟪t⟫ ⊨[M] σ.live) := by
  obtain ⟨T, hT, hLives⟩ := (sat_box_singleton_exists (M := M) (w := ⟨q, †, M.history.val⟩)
    (l := b) (φ := σ.live)).mp (hlive q)
  refine ⟨T, hT, fun p hp t htmem hplace => ?_⟩
  have hlEnd : ⟪t⟫ ⊨[M] ⤒ᶠ σ.live := by
    apply (Sat.atEnd M t _).mpr
    simpa only [hplace] using hLives p hp
  exact Sat.iff_mpr M t (thyLive_liveAlways h.thyLive (M.time_le_of_mem htmem)) hlEnd

/-- A decision-rank delivery certificate meets the destination's live quorum at a
live vote at the delivery rank, which is exactly the transfer premise. -/
theorem delivery_live_vote (h : BaseProtocol M σ) {a b v : S.Value}
    (hcorr : ∀ p : P, Correlated M σ.correlationSymb ⟨p, †, M.history.val⟩ a b)
    (hlive : ⊨[M] □ᶠ[[b]] σ.live)
    {d : World P S.EventType} (hd : d ∈ M.history.val)
    (hcert : ⟪d⟫ ⊨[M] σ.voteCertificate a v (σ.depthBound a)) :
    ⊨[M] ♢ᶠ↓[[]] (σ.live ∧ᶠ σ.vote a v (σ.depthBound a)) := by
  obtain ⟨Q, hQ, hVotes⟩ := (sat_box_singleton_exists (M := M) (w := d)
    (l := a) (φ := ↓ᶠ (σ.vote a v (σ.depthBound a)))).mp hcert
  let w : World P S.EventType := ⟨d.place, †, M.history.val⟩
  obtain ⟨T, hT, hLives⟩ := live_at_event_of_live_quorum h hlive (q := d.place)
  have hinter := h.correlationSeq (PreHistory.happensBeforeEq_refl _) (hcorr d.place)
  obtain ⟨p, hp, _⟩ := (sat_diamond_pair_iff (M := M) (w := w)
    (l := a) (l' := b) (φ := Formula.seq)).mp hinter Q hQ T hT
  obtain ⟨t, ht, hplace, hvote⟩ := (Sat.past (M := M)
    (w := ⟨p, †, d.time⟩) _).mp (hVotes p hp.1)
  have htmem : t ∈ M.history.val :=
    History.subset_of_happensBefore (History.happensBefore_of_mem hd) t ht
  have hlt : ⟪t⟫ ⊨[M] σ.live := hLives p hp.2 htmem hplace
  intro q
  apply (Sat.diamond_nil (M := M) (w := ⟨q, †, M.history.val⟩) _).mpr
  refine ⟨t.place, ?_⟩
  apply (Sat.past (M := M) (w := ⟨t.place, †, M.history.val⟩) _).mpr
  exact ⟨t, htmem, rfl, Sat.and_intro M t hlt hvote⟩

/-- A participant live at the end is live at every possible world of its own. -/
theorem live_at_of_live_final (h : BaseProtocol M σ) {p : P}
    (hl : ⟪(⟨p, †, M.history.val⟩ : World P S.EventType)⟫ ⊨[M] σ.live)
    {t : World P S.EventType} (ht : t.time ⪯ M.history.val) (htp : t.place = p) :
    ⟪t⟫ ⊨[M] σ.live := by
  have hlEnd : ⟪t⟫ ⊨[M] ⤒ᶠ σ.live := by
    apply (Sat.atEnd M t _).mpr
    simpa only [htp] using hl
  exact Sat.iff_mpr M t (thyLive_liveAlways h.thyLive ht) hlEnd

/-- A participant live at the end is sequential in the past of every possible
world (`LiveSeq`). -/
theorem sequential_of_live_final (h : BaseProtocol M σ) {p : P}
    (hl : ⟪(⟨p, †, M.history.val⟩ : World P S.EventType)⟫ ⊨[M] σ.live)
    {d : World P S.EventType} (hdpos : d.time ⪯ M.history.val) :
    isSequential (Event := S.EventType) p d.time := by
  let t : World P S.EventType := ⟨p, †, d.time⟩
  have htpos : t.time ⪯ M.history.val := hdpos
  have hlt : ⟪t⟫ ⊨[M] σ.live := live_at_of_live_final h hl htpos rfl
  exact (Sat.seq M t).mp (Sat.imp_elim (M := M) (w := t) (thyLive_liveSeq h.thyLive htpos) hlt)

/-- The fast-path justification at a delivery gives the destination a live echo
quorum: its live members are sequential there, hence have echoed. -/
theorem live_echo_quorum_of_sequentialEchoes (h : BaseProtocol M σ) {b v : S.Value}
    (hlive : ⊨[M] □ᶠ[[b]] σ.live)
    {d : World P S.EventType} (hd : d ∈ M.history.val)
    (hecho : SequentialEchoes M σ d v) :
    ⊨[M] □ᶠ↓[[b]] (σ.live ∧ᶠ σ.echo v) := by
  intro q
  obtain ⟨T, hT, hLives⟩ := (sat_box_singleton_exists (M := M) (w := ⟨q, †, M.history.val⟩)
    (l := b) (φ := σ.live)).mp (hlive q)
  apply (sat_box_singleton_exists (M := M) (w := ⟨q, †, M.history.val⟩) (l := b) _).mpr
  refine ⟨T, hT, fun p hp => ?_⟩
  have hseq := sequential_of_live_final h (hLives p hp) (M.time_le_of_mem hd)
  obtain ⟨t, ht, hplace, hv⟩ := hecho p hseq
  have htmem : t ∈ M.history.val :=
    History.subset_of_happensBefore (History.happensBefore_of_mem hd) t ht
  apply (Sat.past (M := M) (w := ⟨p, †, M.history.val⟩) _).mpr
  exact ⟨t, htmem, hplace, Sat.and_intro M t
    (live_at_of_live_final h (hLives p hp) (M.time_le_of_mem htmem) hplace) hv⟩

/-- Either justification of a source delivery seeds the destination's live
round-zero quorum: a decision-rank certificate through transfer, the fast path
through the echo rule. -/
theorem zero_quorum_of_delivery (h : BaseProtocol M σ) {a b v : S.Value}
    (huod : ∀ p : P, UncontestedOrDelivered M σ ⟨p, †, M.history.val⟩ b v)
    (hcorr : ∀ p : P, Correlated M σ.correlationSymb ⟨p, †, M.history.val⟩ a b)
    (hlive : ⊨[M] □ᶠ[[b]] σ.live)
    {d : World P S.EventType} (hd : d ∈ M.history.val)
    (hdel : ⟪d⟫ ⊨[M] σ.deliver a v) :
    ⊨[M] □ᶠ↓[[b]] (σ.live ∧ᶠ σ.vote b v 0) := by
  rcases h.deliverBackward (M.time_le_of_mem hd) hdel with hcert | ⟨hecho, _⟩
  · have hsource : ∀ q, Correlated M σ.correlationSymb (finalWorld M q) b a :=
      fun q => h.correlationSymm (PreHistory.happensBeforeEq_refl _) (hcorr q)
    exact transfer_zero_quorum h huod hsource hlive (delivery_live_vote h hcorr hlive hd hcert)
  · exact zero_quorum_of_live_echo_quorum h huod
      (live_echo_quorum_of_sequentialEchoes h hlive hd (sequentialEchoes_iff.mp hecho))

/-- Liveness 2: delivery transfers between permanently correlated learners
when the destination has a live quorum. -/
theorem livenessTwo_of_uncontestedOrDelivered (h : BaseProtocol M σ) {a b v : S.Value}
    (hUodOfDelivery : ∀ q : P, ObservedAt M (finalWorld M q) (σ.deliver a v) →
      UncontestedOrDelivered M σ (finalWorld M q) b v)
    (hCorrelation : ∀ p, Correlated M σ.correlationSymb (finalWorld M p) a b)
    (hLiveQuorum : ∃ Q ∈ (M.learner b).quorums,
      ∀ p ∈ Q, ⟪finalWorld M p⟫ ⊨[M] σ.live)
    (hDelivered : Occurs M (σ.deliver a v))
    (p : P) (hLive : ⟪finalWorld M p⟫ ⊨[M] σ.live) :
    OccursAt M p (σ.deliver b v) := by
  obtain ⟨d, hd, hdval⟩ := hDelivered
  have huod : ∀ q, UncontestedOrDelivered M σ (finalWorld M q) b v := fun q =>
    hUodOfDelivery q ⟨d, hd, hdval⟩
  have hlive := quorum_final_iff_end.mp hLiveQuorum
  have hzero := zero_quorum_of_delivery h huod hCorrelation hlive hd hdval
  apply (occursAt_iff (w := finalWorld M p)).mpr
  exact Sat.imp_elim (M := M) (w := finalWorld M p) (deliver_of_live_zero_quorum h huod hzero p) hLive

end ModalDistribution.Examples.ThyHBB4
