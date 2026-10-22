import ModalDistribution.LowerBound.Basic
import ModalDistribution.Examples.ThyHBB4.Safety

/-!
# Causal depth of HBB4 events

Generic consequences of the HBB4 backward rules for `worldDepth`: an echo is at
least `2` deep, a rank-`n` vote at least `n + 3` deep, and a delivery backed by
a certificate at rank `r` at least `r + 4` deep. The fast path is unavailable to
a delivery whose causal history lies within a set `Q` that misses some
participant: that participant is vacuously sequential in the delivering world's
past but has echoed nothing there. Together these give the lower-bound half of
`HBB4.hbb4_depth_lower_bound` for *every* `BaseProtocol` model, without any
hypothesis on the topology or the correlation relation.
-/

namespace ModalDistribution.LowerBound
open ModalDistribution.Logic ModalDistribution.Logic.Formula
open ModalDistribution.Examples.ThyHBB4
open scoped Formula PreHistory

variable {S : Signature} {P : Type}

/-- Every world has depth at least `1`. -/
theorem worldDepth_pos (w : World P S.EventType) : 1 ≤ worldDepth w := by
  unfold worldDepth
  rcases w with ⟨p, e, h⟩
  cases h with
  | mk l => show _ + 1 ≥ 1; omega

/-- A participant with no event in a prehistory is sequential in it. -/
theorem isSequential_of_absent {q : P} {H : PreHistory P S.EventType}
    (hq : ∀ t ∈ H, t.place ≠ q) : isSequential (Event := S.EventType) q H := by
  intro t₁ t₂ h₁ _ hp₁ _
  exact absurd hp₁ (hq t₁ h₁)

/-- Depth strictly increases along accessibility. -/
theorem worldDepth_lt_of_accessible {u w : World P S.EventType} (h : u ≪ w) :
    worldDepth u < worldDepth w :=
  PreHistory.height_lt_of_accessible h

variable [Nonempty P] {M : Model S P} {σ : ProtocolSignature S}

/-- An echo has a proposal in its past, so is at least `2` deep. -/
theorem echo_depth (h : BaseProtocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {v : S.Value}
    (he : ⟪w⟫ ⊨[M] σ.echo v) : 2 ≤ worldDepth w := by
  obtain ⟨u, hu, _⟩ := observedAt_iff.mpr (h.echoBackward hw he)
  have := worldDepth_lt_of_accessible hu
  have := worldDepth_pos u
  omega

/-- A rank-`n` vote is at least `n + 3` deep: it sits above a rank-`(n-1)` vote
(`voteSuccBackward`), and a rank-`0` vote sits above an echo or above another
vote (`voteZeroBackward`). -/
theorem vote_depth (h : BaseProtocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {l v : S.Value} {n : Nat}
    (hv : ⟪w⟫ ⊨[M] σ.vote l v n) : n + 3 ≤ worldDepth w := by
  have go : ∀ k, ∀ w : World P S.EventType, worldDepth w = k →
      w.time ⪯ M.history.val → ∀ l v n,
      (⟪w⟫ ⊨[M] σ.vote l v n) → n + 3 ≤ worldDepth w := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro w hk hw l v n hv
      cases n with
      | zero =>
        rcases h.voteZeroBackward hw hv with he | ⟨s, m, _, ht⟩
        · obtain ⟨u, hu, he⟩ := quorum_witness he
          have := echo_depth h (predecessor_possible hw hu) he
          have := worldDepth_lt_of_accessible hu
          omega
        · obtain ⟨u, hu, hv'⟩ := observedAt_iff.mpr ht
          have := ih _ (hk ▸ worldDepth_lt_of_accessible hu) u rfl
            (predecessor_possible hw hu) s v m hv'
          have := worldDepth_lt_of_accessible hu
          omega
      | succ n =>
        obtain ⟨u, hu, hv'⟩ := quorum_witness (h.voteSuccBackward hw hv)
        have := ih _ (hk ▸ worldDepth_lt_of_accessible hu) u rfl
          (predecessor_possible hw hu) l v n hv'
        have := worldDepth_lt_of_accessible hu
        omega
  exact go _ w rfl hw l v n hv

/-- The fast path is closed to a delivery whose causal history lies inside a set
`Q` missing some participant. -/
theorem no_fast_path_of_usesOnly {Q : Set P} (hQ : ∃ q, q ∉ Q)
    {d : World P S.EventType} (hd : UsesOnly Q d) {v : S.Value}
    (hfast : ⟪d⟫ ⊨[M] □ᶠ[] (Formula.seq ⇒ᶠ ↓ᶠ (σ.echo v))) : False := by
  obtain ⟨q, hq⟩ := hQ
  have hseq : isSequential (Event := S.EventType) q d.time :=
    isSequential_of_absent fun t ht hqt => hq (hqt ▸ hd.2 t ht)
  obtain ⟨t, ht, htq, _⟩ := sequentialEchoes_iff.mp hfast q hseq
  exact hq (htq ▸ hd.2 t ht)

/-- **Lower bound.** In any `BaseProtocol` model, a delivery for `l` whose causal
history lies inside a set `Q` missing some participant is at least
`maxDepth l + 4` deep. -/
theorem delivery_depth_of_usesOnly (h : BaseProtocol M σ) {Q : Set P}
    (hQ : ∃ q, q ∉ Q) {d : World P S.EventType} (hd : d.time ⪯ M.history.val)
    {l v : S.Value} (hdel : ⟪d⟫ ⊨[M] σ.deliver l v) (hu : UsesOnly Q d) :
    maxDepth M (Correlated M σ.correlationSymb) l + 4 ≤ worldDepth d := by
  rcases h.deliverBackward hd hdel with hcert | ⟨hfast, _⟩
  · obtain ⟨u, hu', hv⟩ := quorum_witness hcert
    have := vote_depth h (predecessor_possible hd hu') hv
    have := worldDepth_lt_of_accessible hu'
    omega
  · exact (no_fast_path_of_usesOnly hQ hu hfast).elim

end ModalDistribution.LowerBound
