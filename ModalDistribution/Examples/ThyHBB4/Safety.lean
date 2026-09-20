import ModalDistribution.Examples.ThyHBB4.Axioms

namespace ModalDistribution.Examples.ThyHBB4

open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped PreHistory Formula

variable {S : Signature} {P : Type} [Nonempty P]

omit [Nonempty P] in
/-- A nonempty collection of event worlds has a causally minimal member. -/
theorem exists_causally_minimal
    (A : World P S.EventType → Prop) (hA : ∃ w, A w) :
    ∃ w, A w ∧ ∀ u, u ≪ w → ¬ A u := by
  classical
  obtain ⟨w, hw⟩ := hA
  have go : ∀ n, ∀ w, PreHistory.height w.time = n → A w →
      ∃ t, A t ∧ ∀ u, u ≪ t → ¬ A u := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro w hn hw
      by_cases h : ∃ u, u ≪ w ∧ A u
      · obtain ⟨u, huw, hu⟩ := h
        exact ih (PreHistory.height u.time)
          (hn ▸ PreHistory.height_lt_of_accessible huw) u rfl hu
      · exact ⟨w, hw, fun u huw hu => h ⟨u, huw, hu⟩⟩
  exact go _ w rfl hw

variable {M : Model S P} {σ : ProtocolSignature S}

theorem past_exists_iff {w : World P S.EventType} {φ : Formula S} :
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] φ) ↔ ∃ u, u ≪ w ∧ (⟪u⟫ ⊨[M] φ) := by
  simp only [Formula.diamondPast, Sat.diamond_nil, Sat.past]
  constructor
  · rintro ⟨p, u, hu, _, hφ⟩
    exact ⟨u, hu, hφ⟩
  · rintro ⟨u, hu, hφ⟩
    exact ⟨u.place, u, hu, rfl, hφ⟩

theorem quorum_exists_iff {w : World P S.EventType} {l : S.Value} {φ : Formula S} :
    (⟪w⟫ ⊨[M] □ᶠ↓[[l]] φ) ↔
      ∃ Q ∈ (M.learner l).quorums, ∀ p ∈ Q,
        ∃ u, u ≪ w ∧ u.place = p ∧ (⟪u⟫ ⊨[M] φ) := by
  simp only [Formula.boxPast, sat_box_singleton_exists, Sat.past]
  rfl

theorem quorum_witness {w : World P S.EventType} {l : S.Value} {φ : Formula S}
    (h : ⟪w⟫ ⊨[M] □ᶠ↓[[l]] φ) : ∃ u, u ≪ w ∧ (⟪u⟫ ⊨[M] φ) := by
  obtain ⟨Q, hQ, h⟩ := quorum_exists_iff.mp h
  obtain ⟨p, hp⟩ := Semifilter.quorum_nonempty hQ
  obtain ⟨u, hu, _, hφ⟩ := h p hp
  exact ⟨u, hu, hφ⟩

theorem predecessor_possible {w u : World P S.EventType}
    (hw : w.time ⪯ M.history.val) (hu : u ≪ w) : u.time ⪯ M.history.val :=
  (PreHistory.happensBeforeEq_iff _ _).2
    (Or.inl (accessible_happensBefore_history hw hu))

/-- Every vote has a proposal of the same value in its causal past. -/
theorem vote_provenance (h : Protocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {l s v : S.Value} {n : Nat}
    (hv : ⟪w⟫ ⊨[M] σ.vote l s v n) :
    ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v) := by
  have go : ∀ k, ∀ w : World P S.EventType, PreHistory.height w.time = k →
      w.time ⪯ M.history.val → ∀ l s v n,
      (⟪w⟫ ⊨[M] σ.vote l s v n) →
      (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v)) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro w hk hw l s v n hv
      have liftProposal : ∀ u, u ≪ w →
          (⟪u⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v)) →
          (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v)) := by
        intro u hu hp
        obtain ⟨t, ht, hp⟩ := past_exists_iff.mp hp
        exact past_exists_iff.mpr ⟨t, accessible_trans hw ht hu, hp⟩
      have fromVote : ∀ u, u ≪ w → ∀ l s n,
          (⟪u⟫ ⊨[M] σ.vote l s v n) →
          (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v)) := by
        intro u hu l s n hv
        exact liftProposal u hu (ih _ (hk ▸ PreHistory.height_lt_of_accessible hu)
          u rfl (predecessor_possible hw hu) l s v n hv)
      cases n with
      | zero =>
        rcases h.voteZeroBackward hw hv with ⟨_, he⟩ | ht
        · obtain ⟨u, hu, he⟩ := quorum_witness he
          exact liftProposal u hu (h.echoBackward (predecessor_possible hw hu) he)
        · obtain ⟨u, hu, hv⟩ := quorum_witness ht
          obtain ⟨s', hv⟩ := (Sat.exists_iff _ _).mp hv
          exact fromVote u hu _ s' _ hv
      | succ n =>
        obtain ⟨u, hu, hv⟩ := quorum_witness (h.voteSuccBackward hw hv)
        exact fromVote u hu l s n hv
  exact go _ w rfl hw l s v n hv

/-- Minimal votes are chosen among every target in the observer's row. -/
structure MinimalVote (w : World P S.EventType) (a v : S.Value) (r : Nat) where
  event : World P S.EventType
  target : S.Value
  source : S.Value
  before : event ≪ w
  correlated : Corr M σ w a target
  vote : ⟪event⟫ ⊨[M] σ.vote target source v r
  minimal : ∀ u, u ≪ event → ∀ b s n, Corr M σ w a b → r ≤ n →
    ¬ (⟪u⟫ ⊨[M] σ.vote b s v n)

theorem minimal_vote (h : Protocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b v : S.Value} {r n : Nat}
    (hb : Corr M σ w a b) (hn : r ≤ n)
    (hv : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.someVote b v n)) :
    Nonempty (MinimalVote (M := M) (σ := σ) w a v r) := by
  let A := fun e : World P S.EventType => e ≪ w ∧
    ∃ b s n, Corr M σ w a b ∧ r ≤ n ∧ (⟪e⟫ ⊨[M] σ.vote b s v n)
  obtain ⟨e, he, hv⟩ := past_exists_iff.mp hv
  obtain ⟨s, hv⟩ := (Sat.exists_iff _ _).mp hv
  obtain ⟨e, ⟨hew, b, s, n, hb, hn, hv⟩, hmin⟩ :=
    exists_causally_minimal A ⟨e, he, b, s, n, hb, hn, hv⟩
  have minimal : ∀ u, u ≪ e → ∀ b s n, Corr M σ w a b → r ≤ n →
      ¬ (⟪u⟫ ⊨[M] σ.vote b s v n) := by
    intro u hue b s n hb hn hv
    exact hmin u hue ⟨accessible_trans hw hue hew, b, s, n, hb, hn, hv⟩
  have hnr : n = r := by
    by_cases hne : n = r
    · exact hne
    apply False.elim
    have hlt : r < n := by omega
    cases n with
    | zero => omega
    | succ k =>
      obtain ⟨u, hue, hv'⟩ := quorum_witness
        (h.voteSuccBackward (predecessor_possible hw hew) hv)
      exact minimal u hue b s k hb (by omega) hv'
  subst n
  exact ⟨⟨e, b, s, hew, hb, hv, minimal⟩⟩

theorem quorum_pair (h : Protocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b : S.Value} {φ ψ : Formula S}
    (hab : Corr M σ w a b)
    (hφ : ⟪w⟫ ⊨[M] □ᶠ↓[[a]] φ) (hψ : ⟪w⟫ ⊨[M] □ᶠ↓[[b]] ψ) :
    ∃ e f, e ≪ w ∧ f ≪ w ∧ e.place = f.place ∧
      (⟪e⟫ ⊨[M] φ) ∧ (⟪f⟫ ⊨[M] ψ) ∧ (e ≪ f ∨ f ≪ e ∨ e = f) := by
  obtain ⟨Q, hQ, hφ⟩ := quorum_exists_iff.mp hφ
  obtain ⟨T, hT, hψ⟩ := quorum_exists_iff.mp hψ
  have hs := h.correlationSeq hw hab
  have hs' := (sat_diamond_pair_iff (M := M) (w := w) (l := a) (l' := b)
    (φ := Formula.seq)).mp hs
  obtain ⟨p, hp, hseq⟩ := hs' Q hQ T hT
  obtain ⟨e, he, hep, hφ⟩ := hφ p hp.1
  obtain ⟨f, hf, hfp, hψ⟩ := hψ p hp.2
  exact ⟨e, f, he, hf, hep.trans hfp.symm, hφ, hψ, hseq e f he hf hep hfp⟩

theorem quorum_pair_before (h : Protocol M σ) {w x y : World P S.EventType}
    (hw : w.time ⪯ M.history.val) (hx : x ≪ w) (hy : y ≪ w)
    {a b : S.Value} {φ ψ : Formula S} (hab : Corr M σ w a b)
    (hφ : ⟪x⟫ ⊨[M] □ᶠ↓[[a]] φ) (hψ : ⟪y⟫ ⊨[M] □ᶠ↓[[b]] ψ) :
    ∃ e f, e ≪ x ∧ f ≪ y ∧
      (⟪e⟫ ⊨[M] φ) ∧ (⟪f⟫ ⊨[M] ψ) ∧ (e ≪ f ∨ f ≪ e ∨ e = f) := by
  obtain ⟨Q, hQ, hφ⟩ := quorum_exists_iff.mp hφ
  obtain ⟨T, hT, hψ⟩ := quorum_exists_iff.mp hψ
  obtain ⟨p, hp, hseq⟩ :=
    (sat_diamond_pair_iff (M := M) (w := w) (l := a) (l' := b)
      (φ := Formula.seq)).mp (h.correlationSeq hw hab) Q hQ T hT
  obtain ⟨e, he, hep, hφ⟩ := hφ p hp.1
  obtain ⟨f, hf, hfp, hψ⟩ := hψ p hp.2
  exact ⟨e, f, he, hf, hφ, hψ,
    hseq e f (accessible_trans hw he hx) (accessible_trans hw hf hy) hep hfp⟩

theorem quorum_lift {w e : World P S.EventType}
    (hw : w.time ⪯ M.history.val) (he : e ≪ w) {a : S.Value} {φ : Formula S}
    (hφ : ⟪e⟫ ⊨[M] □ᶠ↓[[a]] φ) : ⟪w⟫ ⊨[M] □ᶠ↓[[a]] φ := by
  obtain ⟨Q, hQ, hφ⟩ := quorum_exists_iff.mp hφ
  apply quorum_exists_iff.mpr
  refine ⟨Q, hQ, ?_⟩
  intro p hp
  obtain ⟨f, hf, hfp, hφ⟩ := hφ p hp
  exact ⟨f, accessible_trans hw hf he, hfp, hφ⟩

theorem vote_value_eq {w : World P S.EventType} {l s v b t u : S.Value} {n k : Nat}
    (hv : ⟪w⟫ ⊨[M] σ.vote l s v n) (hu : ⟪w⟫ ⊨[M] σ.vote b t u k) : v = u := by
  have he := ((Sat.ofEvent _ _ _).mp hv).1.symm.trans ((Sat.ofEvent _ _ _).mp hu).1
  have ha := congrArg (fun e : MaybeEvent S.EventType =>
    match e with | .none => [] | .some a => a.args) he
  exact (List.cons.inj (List.cons.inj (List.cons.inj ha).2).2).1

theorem ending_chain_strict_append (h : Protocol M σ) {w e : World P S.EventType}
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
theorem conflict_depth (h : Protocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {r n k : Nat}
    (hb : Corr M σ w a b) (hc : Corr M σ w a c) (hvu : v ≠ u)
    (hn : r ≤ n) (hk : r ≤ k)
    (hv : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.someVote b v n))
    (hu : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.someVote c u k)) :
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
      exact ending_chain_strict_append h hw X.before hcorr hnot
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
          · exact (h.echoNonEquiv (predecessor_possible hw hf) huf
              ((Sat.past _ _ _).mpr ⟨e, hef, hp, hve⟩)).symm
          · exact h.echoNonEquiv (predecessor_possible hw he) hve
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
    obtain ⟨e, f, he, hf, hve, huf, hord⟩ := quorum_pair_before h hw V.before U.before hVU
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
      have hPast : ⟪f⟫ ⊨[M] ♢ᶠ↓[[]] (σ.someVote V.target v r) :=
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
      exact ending_chain_strict_append h hw hfw hac hnot chain
    rcases hord with hef | hfe | heq
    · exact step hvu V U e f he hf hve huf hef
    · exact step (Ne.symm hvu) U V f e hf he huf hve hfe
    · subst f
      exact False.elim (hvu (vote_value_eq hve huf))

/-- A vote at the depth threshold dominates all conflicting votes in its row. -/
theorem conflicting_rank_lt (h : Protocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v u : S.Value} {n k : Nat}
    (hb : Corr M σ w a b) (hc : Corr M σ w a c) (hvu : v ≠ u)
    (hn : maxDepth M (Corr M σ) a - 1 ≤ n)
    (hv : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.someVote b v n))
    (hu : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.someVote c u k)) :
    k < maxDepth M (Corr M σ) a - 1 := by
  by_cases hk : k < maxDepth M (Corr M σ) a - 1
  · exact hk
  have hchain := conflict_depth h hw hb hc hvu hn (by omega) hv hu
  have hbound := endingDepthChain_le hchain
  have hpos := maxDepth_pos M (Corr M σ) a
  omega

/-- The dominating vote is the witness required by every legality clause. -/
theorem high_vote_legal (h : Protocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b c v : S.Value} {n : Nat}
    (hb : Corr M σ w a b) (hc : Corr M σ w a c)
    (hn : maxDepth M (Corr M σ) a - 1 ≤ n)
    (hv : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.someVote b v n)) : Legal M σ w c v := by
  intro d u k hdc huv hu
  have had := h.correlationTrans hw hc (h.correlationSymm hw hdc)
  have hlt := conflicting_rank_lt h hw hb had (Ne.symm huv) hn hv hu
  exact ⟨b, n, by omega, h.correlationTrans hw (h.correlationSymm hw hb) hc, hv⟩

/-- A delivered value has an actual proposal in the delivery's causal past. -/
theorem deliver_provenance (h : Protocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {l v : S.Value}
    (hv : ⟪w⟫ ⊨[M] σ.deliver l v) :
    ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v) := by
  obtain ⟨e, he, hv⟩ := quorum_witness (h.deliverBackward hw hv)
  obtain ⟨s, hv⟩ := (Sat.exists_iff _ _).mp hv
  obtain ⟨f, hf, hp⟩ := past_exists_iff.mp
    (vote_provenance h (predecessor_possible hw he) hv)
  exact past_exists_iff.mpr ⟨f, accessible_trans hw hf he, hp⟩

/-- Deliveries observed at a correlated world agree, even with unequal depths. -/
theorem agreement_at (h : Protocol M σ) {w : World P S.EventType}
    (hw : w.time ⪯ M.history.val) {a b v u : S.Value}
    (hab : Corr M σ w a b)
    (hv : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver a v))
    (hu : ⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver b u)) : v = u := by
  have votes : ∀ {a v}, (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver a v)) →
      (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.someVote a v (maxDepth M (Corr M σ) a + 1))) := by
    intro a v hv
    obtain ⟨e, he, hd⟩ := past_exists_iff.mp hv
    exact past_exists_iff.mpr (quorum_witness
      (quorum_lift hw he (h.deliverBackward (predecessor_possible hw he) hd)))
  have hv' := votes hv
  have hu' := votes hu
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
theorem agreement (h : Protocol M σ) {a b v u : S.Value}
    (hab : ∀ p : P, Corr M σ ⟨p, †, M.history.val⟩ a b) :
    ∀ p : P, (⟪(p, †, M.history.val)⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver a v)) →
      (⟪(p, †, M.history.val)⟫ ⊨[M] ♢ᶠ↓[[]] (σ.deliver b u)) → v = u := by
  intro p hv hu
  exact agreement_at h (PreHistory.happensBeforeEq_refl _) (hab p) hv hu

end ModalDistribution.Examples.ThyHBB4
