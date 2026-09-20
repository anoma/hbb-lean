import ModalDistribution.Examples.ThyHBB4.Semantics

/-! A finite completed execution for the capped CM protocol. -/
namespace ModalDistribution.Examples.ThyHBB4.FiniteModel
open ModalDistribution.Logic PreHistory History World
open scoped Formula

private inductive Symbol where
  | propose | echo | vote (rank : Nat) | deliver
  deriving DecidableEq
private def signature : Signature := ⟨Symbol, Unit, Unit⟩
private def atom (s : Symbol) (args : List Unit) : signature.EventType := ⟨s, args⟩
private def label : Nat → MaybeEvent signature.EventType
  | 0 => .some (atom .propose [()])
  | 1 => .some (atom .echo [()])
  | 2 => .some (atom (.vote 0) [(), (), ()])
  | 3 => .some (atom (.vote 1) [(), (), ()])
  | 4 => .some (atom (.vote 2) [(), (), ()])
  | 5 => .some (atom .deliver [(), ()])
  | _ => †
private def entries : Nat → List (World Unit signature.EventType)
  | 0 => []
  | n + 1 => ((), label n, .mk (entries n)) :: entries n
private def time (n : Nat) : PreHistory Unit signature.EventType := .mk (entries n)
private def event (n : Nat) : World Unit signature.EventType := ((), label n, time n)

@[local simp] private theorem mem_mk (t : World Unit signature.EventType) (xs) :
    t ∈ PreHistory.mk xs ↔ t ∈ xs := Iff.rfl
private theorem mem_time (t : World Unit signature.EventType) (n : Nat) :
    t ∈ time n ↔ ∃ i, i < n ∧ t = event i := by
  induction n with
  | zero => simp [time, entries]
  | succ n ih =>
    have he : t ∈ time (n + 1) ↔ t = event n ∨ t ∈ time n := by
      change t ∈ event n :: entries n ↔ _
      exact List.mem_cons
    rw [he]
    rw [ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨n, by omega, rfl⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      by_cases h : i = n
      · subst i; exact Or.inl rfl
      · exact Or.inr ⟨i, by omega, rfl⟩

private theorem time_subset {i n : Nat} (h : i ≤ n) : time i ⊆ time n := by
  intro t ht
  obtain ⟨j, hj, rfl⟩ := (mem_time t i).mp ht
  exact (mem_time _ n).mpr ⟨j, by omega, rfl⟩

private theorem hered (n : Nat) : isHereditarilyTransitive (time n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [isHereditarilyTransitive_unfold]
    constructor
    · rintro h ⟨p, e, ht⟩
      obtain ⟨i, hi, he⟩ := (mem_time (p, e, h) n).mp ht
      have hh : h = time i := congrArg World.time he
      rw [hh]
      exact time_subset (by omega)
    · rintro h ⟨p, e, ht⟩
      obtain ⟨i, hi, he⟩ := (mem_time (p, e, h) n).mp ht
      have hh : h = time i := congrArg World.time he
      rw [hh]
      exact ih i hi

private theorem sequential (n : Nat) : isSequential () (time n) := by
  intro a b ha hb _ _
  obtain ⟨i, hi, rfl⟩ := (mem_time a n).mp ha
  obtain ⟨j, hj, rfl⟩ := (mem_time b n).mp hb
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact Or.inl ((mem_time _ j).mpr ⟨i, h, rfl⟩)
  · subst j; exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl ((mem_time _ i).mpr ⟨j, h, rfl⟩))

private def model : Model signature Unit where
  history := ⟨time 8, hered 8⟩
  predInterp := fun _ _ => Set.univ
  learner := fun _ => {
    quorums := {O | () ∈ O}
    nonempty := ⟨Set.univ, trivial⟩
    upwardClosed := fun {_ _} hO hsub => hsub hO
    pairwiseInter := fun {_ _} hO hO' => ⟨(), hO, hO'⟩ }

@[local simp] private theorem unit_exists (Q : Unit → Prop) :
    (∃ u, Q u) ↔ Q () := ⟨fun ⟨u, h⟩ => by cases u; exact h, fun h => ⟨(), h⟩⟩

private theorem check (Q : Unit → Prop) (ls : List signature.Value) (acc : Set Unit) :
    Sat.check model Q ls acc ↔ (() ∈ acc ∧ Q ()) := by
  induction ls generalizing acc with
  | nil => simp [Sat.check]
  | cons l ls ih =>
    simp only [Sat.check, ih]
    constructor
    · intro h
      exact ⟨(h Set.univ trivial).1.1, (h Set.univ trivial).2⟩
    · rintro ⟨ha, hq⟩ O ho
      exact ⟨⟨ha, ho⟩, hq⟩

private theorem diamondPast (w : World Unit signature.EventType)
    (ls : List signature.Value) (φ : Formula signature) :
    (⟪w⟫ ⊨[model] ♢ᶠ↓[ls] φ) ↔ ∃ t ∈ w.time, ⟪t⟫ ⊨[model] φ := by
  simp only [Formula.diamondPast, Sat, check, Set.mem_univ, true_and]

private theorem boxPast (w : World Unit signature.EventType)
    (ls : List signature.Value) (φ : Formula signature) :
    (⟪w⟫ ⊨[model] □ᶠ↓[ls] φ) ↔ ∃ t ∈ w.time, ⟪t⟫ ⊨[model] φ := by
  classical
  simp only [Formula.boxPast, Formula.box, Formula.not, Sat, check,
    Set.mem_univ, true_and]
  simp

private theorem event_actual (i : Nat) (hi : i < 8) (E : signature.EventType) :
    (⟪event i⟫ ⊨[model] Formula.ofEvent E) ↔ label i = .some E := by
  rw [Sat.ofEvent]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    have hm : event i ∈ model.history.val := (mem_time _ 8).mpr ⟨i, hi, rfl⟩
    simpa only [event, h] using hm

private theorem atom_early {t : World Unit signature.EventType} {E : signature.EventType}
    (ht : t ∈ time 8) (hE : ⟪t⟫ ⊨[model] Formula.ofEvent E) : t ∈ time 6 := by
  obtain ⟨i, hi, rfl⟩ := (mem_time _ _).mp ht
  have he := (event_actual i hi E).mp hE
  have hi6 : i < 6 := by
    by_cases hh : i < 6
    · exact hh
    have hn : label i = † := by
      cases i with
      | zero => omega
      | succ i => cases i with
        | zero => omega
        | succ i => cases i with
          | zero => omega
          | succ i => cases i with
            | zero => omega
            | succ i => cases i with
              | zero => omega
              | succ i => cases i with
                | zero => omega
                | succ i => rfl
    rw [hn] at he
    contradiction
  exact (mem_time _ 6).mpr ⟨i, hi6, rfl⟩

private theorem allowed_early {φ : Formula signature} (hφ : KnowledgeBody φ)
    (h : ∃ t ∈ time 8, ⟪t⟫ ⊨[model] φ) :
    ∃ t ∈ time 7, ⟪t⟫ ⊨[model] φ := by
  obtain ⟨t, ht, hs⟩ := h
  cases hφ with
  | event E => exact ⟨t, time_subset (show 6 ≤ 7 by omega) t (atom_early ht hs), hs⟩
  | known E =>
    obtain ⟨u, hu, hus⟩ := (diamondPast t [] _).mp hs
    have hu8 := History.subset_of_happensBefore (H := model.history) ⟨t.place, t.event, ht⟩ u hu
    refine ⟨event 6, (mem_time _ 7).mpr ⟨6, by omega, rfl⟩, ?_⟩
    exact (diamondPast (event 6) [] _).mpr ⟨u, atom_early hu8 hus, hus⟩
  | quorum l E =>
    obtain ⟨u, hu, hus⟩ := (boxPast t [l] _).mp hs
    have hu8 := History.subset_of_happensBefore (H := model.history) ⟨t.place, t.event, ht⟩ u hu
    refine ⟨event 6, (mem_time _ 7).mpr ⟨6, by omega, rfl⟩, ?_⟩
    exact (boxPast (event 6) [l] _).mpr ⟨u, atom_early hu8 hus, hus⟩

private theorem live_theory : Theory.Valid (M := model) (ThyLive ()) := by
  classical
  intro ax hax w hw
  rcases hax with rfl | rfl | ⟨ls, φ, ha, rfl⟩ | ⟨ls, φ, ha, rfl⟩
  · simp [liveAlwaysAxiom, Formula.iff, Formula.and, Formula.not,
      Formula.predicate0, Sat, model, Set.mem_univ]
  · change True → isSequential w.place w.time
    intro _
    have hp : w.place = () := Subsingleton.elim _ _
    rw [hp]
    rcases hw with hw | hw
    · exact History.sequentiality_of_predecessor (H := model.history) hw (sequential 8)
    · rw [hw]; exact sequential 8
  · change (⟪endWorld model w⟫ ⊨[model] ♢ᶠ↓[ls] (Formula.predicate0 () ∧ᶠ φ)) → _
    intro h _
    obtain ⟨t, ht, hs⟩ := (diamondPast (endWorld model w) ls _).mp h
    obtain ⟨u, hu, hus⟩ := allowed_early ha ⟨t, ht, (Sat.and ..).mp hs |>.2⟩
    apply (Sat.sometime model w _).mpr
    refine ⟨event 7, (mem_time _ 8).mpr ⟨7, by omega, rfl⟩, Subsingleton.elim _ _, ?_⟩
    exact (diamondPast (event 7) ls φ).mpr ⟨u, hu, hus⟩
  · change (⟪endWorld model w⟫ ⊨[model] □ᶠ↓[ls] (Formula.predicate0 () ∧ᶠ φ)) → _
    intro h _
    obtain ⟨t, ht, hs⟩ := (boxPast (endWorld model w) ls _).mp h
    obtain ⟨u, hu, hus⟩ := allowed_early ha ⟨t, ht, (Sat.and ..).mp hs |>.2⟩
    apply (Sat.sometime model w _).mpr
    refine ⟨event 7, (mem_time _ 8).mpr ⟨7, by omega, rfl⟩, Subsingleton.elim _ _, ?_⟩
    exact (boxPast (event 7) ls φ).mpr ⟨u, hu, hus⟩

private def symbols : ProtocolSignature signature where
  liveSymb := ()
  correlationSymb := ()
  proposeSymb := .propose
  echoSymb := .echo
  voteSymb := Symbol.vote
  deliverSymb := .deliver

private theorem corr (w : World Unit signature.EventType) (a b : signature.Value) :
    Corr model symbols w a b := Set.mem_univ _

private theorem legal (w : World Unit signature.EventType) (l v : signature.Value) :
    Legal model symbols w l v := by
  intro b u n _ hne _
  exact False.elim (hne (by cases u; cases v; rfl))

private theorem depth (a : signature.Value) : maxDepth model (Corr model symbols) a = 1 := by
  apply maxDepth_eq_one_of_constant
  intro w u
  funext b
  exact propext ⟨fun _ => corr u a b, fun _ => corr w a b⟩

private theorem event_index {w : World Unit signature.EventType} {E : signature.EventType}
    (h : ⟪w⟫ ⊨[model] Formula.ofEvent E) :
    ∃ i, i < 8 ∧ w = event i ∧ label i = .some E := by
  obtain ⟨he, hm⟩ := (Sat.ofEvent model w E).mp h
  have hw : w ∈ time 8 := by
    rcases w with ⟨p, e, H⟩
    change e = .some E at he
    subst e
    exact hm
  obtain ⟨i, hi, rfl⟩ := (mem_time _ 8).mp hw
  exact ⟨i, hi, rfl, he⟩

private theorem echo_world {w : World Unit signature.EventType} {v : signature.Value}
    (h : ⟪w⟫ ⊨[model] symbols.echo v) : w = event 1 := by
  cases v
  obtain ⟨i, hi, rfl, he⟩ := event_index h
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [symbols, label, atom] at he ⊢

private theorem deliver_world {w : World Unit signature.EventType} {l v : signature.Value}
    (h : ⟪w⟫ ⊨[model] symbols.deliver l v) : w = event 5 := by
  cases l; cases v
  obtain ⟨i, hi, rfl, he⟩ := event_index h
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [symbols, label, atom] at he ⊢

private theorem vote_world {w : World Unit signature.EventType} {l s v : signature.Value} {n : Nat}
    (h : ⟪w⟫ ⊨[model] symbols.vote l s v n) : w = event (n + 2) ∧ n ≤ 2 := by
  cases l; cases s; cases v
  obtain ⟨i, hi, rfl, he⟩ := event_index h
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [symbols, label, atom] at he ⊢
  all_goals injection he with hn; subst n; simp

private theorem propose_actual : ⟪event 0⟫ ⊨[model] symbols.propose () :=
  (event_actual 0 (by omega) _).mpr rfl
private theorem echo_actual : ⟪event 1⟫ ⊨[model] symbols.echo () :=
  (event_actual 1 (by omega) _).mpr rfl
private theorem deliver_actual : ⟪event 5⟫ ⊨[model] symbols.deliver () () :=
  (event_actual 5 (by omega) _).mpr rfl
private theorem vote_actual (n : Nat) (hn : n ≤ 2) :
    ⟪event (n + 2)⟫ ⊨[model] symbols.vote () () () n := by
  apply (event_actual (n + 2) (by omega) _).mpr
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;> rfl

private theorem sometime_actual (w : World Unit signature.EventType)
    (i : Nat) (hi : i < 8) {φ : Formula signature} (h : ⟪event i⟫ ⊨[model] φ) :
    ⟪w⟫ ⊨[model] ↕ᶠ φ :=
  (Sat.sometime model w φ).mpr
    ⟨event i, (mem_time _ 8).mpr ⟨i, hi, rfl⟩, Subsingleton.elim _ _, h⟩

private theorem fixed_at (n k : Nat) (hn : n ≤ 2) (hk : n + 2 < k) :
    ⟪event k⟫ ⊨[model] symbols.fixedCertificate () () () n := by
  apply (boxPast (event k) [()] _).mpr
  exact ⟨event (n + 2), (mem_time _ k).mpr ⟨n + 2, hk, rfl⟩, vote_actual n hn⟩

private theorem protocol : Protocol model symbols := by
  refine {
    thyLive := live_theory
    echoBackward := ?_
    voteZeroBackward := ?_
    voteSuccBackward := ?_
    deliverBackward := ?_
    echoNonEquiv := ?_
    voteLegal := ?_
    voteSource := ?_
    voteCap := ?_
    correlationSeq := ?_
    correlationSymm := ?_
    correlationTrans := ?_
    causalMonotone := ?_
    echoForward := ?_
    voteZeroEchoForward := ?_
    voteZeroTransferForward := ?_
    voteSuccForward := ?_
    deliverForward := ?_ }
  · intro w _ v hv
    cases v
    rw [echo_world hv]
    exact (diamondPast (event 1) [] _).mpr
      ⟨event 0, (mem_time _ 1).mpr ⟨0, by omega, rfl⟩, propose_actual⟩
  · intro w _ l s v hv
    cases l; cases s; cases v
    left
    refine ⟨rfl, ?_⟩
    rw [(vote_world hv).1]
    exact (boxPast (event 2) [()] _).mpr
      ⟨event 1, (mem_time _ 2).mpr ⟨1, by omega, rfl⟩, echo_actual⟩
  · intro w _ l s v n hv
    cases l; cases s; cases v
    obtain ⟨hw, hn⟩ := vote_world hv
    rw [hw]
    exact fixed_at n (n + 1 + 2) (by omega) (by omega)
  · intro w _ l v hv
    cases l; cases v
    rw [deliver_world hv, depth]
    exact fixedCertificate_to_certificate (fixed_at 2 5 (by omega) (by omega))
  · intro w _ v u _ _
    cases v; cases u; rfl
  · intro w _ l s v n _
    exact legal w l v
  · intro w _ l s v n _
    exact Or.inr (corr w l s)
  · intro w _ l s v n hv
    rw [depth]
    exact (vote_world hv).2
  · intro w hw a b _
    change Sat.check model (fun p => isSequential p w.time) [a, b] Set.univ
    apply (check _ _ _).mpr
    refine ⟨trivial, ?_⟩
    rcases hw with hw | hw
    · exact History.sequentiality_of_predecessor (H := model.history) hw (sequential 8)
    · rw [hw]; exact sequential 8
  · intro w _ a b _
    exact corr w b a
  · intro w _ a b c _ _
    exact corr w a c
  · intro w _ a b _ u _
    exact corr u a b
  · intro w _ v _ _
    exact ⟨(), sometime_actual w 1 (by omega) echo_actual⟩
  · intro w _ l v _ _ _
    cases l; cases v
    exact sometime_actual w 2 (by omega) (vote_actual 0 (by omega))
  · intro w _ l s v _ _ _ _
    cases l; cases s; cases v
    exact sometime_actual w 2 (by omega) (vote_actual 0 (by omega))
  · intro w _ l s v n hn _ _ _ _
    cases l; cases s; cases v
    rw [depth] at hn
    exact sometime_actual w (n + 1 + 2) (by omega) (vote_actual (n + 1) hn)
  · intro w _ l v _ _
    cases l; cases v
    exact sometime_actual w 5 (by omega) deliver_actual

/-- The capped CM axioms admit a finite model with both liveness antecedents.
The participant, learner, and value sorts here are singletons. -/
theorem finite_protocol_nonvacuous :
    ∃ (S : Signature) (M : Model S Unit) (σ : ProtocolSignature S) (l v : S.Value),
      Protocol M σ ∧
      (⊨[M] □ᶠ[[l]] σ.live) ∧
      (⊨[M] ∃!ᶠ u ↦ ♢ᶠ↓[[]] (σ.propose u)) ∧
      (⊨[M] ♢ᶠ↓[[]] (σ.live ∧ᶠ ♢ᶠ↓[[]] (σ.propose v))) ∧
      (⊨[M] □ᶠ[] (σ.correlation l l)) ∧
      (⊨[M] ♢ᶠ↓[[]] (σ.deliver l v)) ∧
      (∃ e ∈ M.history.val, (⟪e⟫ ⊨[M] σ.live) ∧
        (⟪e⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v))) ∧
      (∃ e ∈ M.history.val, ⟪e⟫ ⊨[M] σ.deliver l v) := by
  have hknown : ⟪event 1⟫ ⊨[model] ♢ᶠ↓[[]] (symbols.propose ()) :=
    (diamondPast (event 1) [] _).mpr
      ⟨event 0, (mem_time _ 1).mpr ⟨0, by omega, rfl⟩, propose_actual⟩
  have hlive : ∀ w : World Unit signature.EventType, ⟪w⟫ ⊨[model] symbols.live :=
    fun _ => Set.mem_univ _
  refine ⟨signature, model, symbols, (), (), protocol, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    apply (sat_box_singleton_exists model ⟨p, †, model.history.val⟩ () symbols.live).mpr
    exact ⟨Set.univ, trivial, fun q _ => hlive _⟩
  · intro p
    apply Sat.and_intro
    · change ∀ u v : signature.Value, _
      intro u v _ _
      cases u; cases v
      rfl
    · apply Sat.exists_intro
      refine ⟨(), ?_⟩
      exact (diamondPast ⟨p, †, model.history.val⟩ [] _).mpr
        ⟨event 0, (mem_time _ 8).mpr ⟨0, by omega, rfl⟩, propose_actual⟩
  · intro p
    apply (diamondPast ⟨p, †, model.history.val⟩ [] _).mpr
    exact ⟨event 1, (mem_time _ 8).mpr ⟨1, by omega, rfl⟩,
      Sat.and_intro model (event 1) (hlive _) hknown⟩
  · intro p
    apply (Sat.boxEmpty model ⟨p, †, model.history.val⟩ (symbols.correlation () ())).mpr
    intro q
    exact corr _ () ()
  · intro p
    exact (diamondPast ⟨p, †, model.history.val⟩ [] _).mpr
      ⟨event 5, (mem_time _ 8).mpr ⟨5, by omega, rfl⟩, deliver_actual⟩
  · exact ⟨event 1, (mem_time _ 8).mpr ⟨1, by omega, rfl⟩, hlive _, hknown⟩
  · exact ⟨event 5, (mem_time _ 8).mpr ⟨5, by omega, rfl⟩, deliver_actual⟩

end ModalDistribution.Examples.ThyHBB4.FiniteModel
