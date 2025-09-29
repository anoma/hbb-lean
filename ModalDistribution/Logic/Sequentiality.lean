import ModalDistribution.Logic.Semantics
import ModalDistribution.Core.History
import ModalDistribution.Logic.Properties

/-!
# Sequentiality lemmas

This module packages the lemmas and propositions whose primary focus is the
sequentiality modality `Formula.seq`.  They were originally developed inside
`Properties.lean` (Section 5.1) but are isolated here so that future work on the
sequential fragment can build on a dedicated library.
-/

namespace ModalDistribution
namespace Logic

open Set
open scoped Formula History PreHistory

set_option autoImplicit false

universe u₁ u₂ u₃ u₄ u₅ u₆

variable {S : Signature} {P : Type u₆}

/-- Package a `p`-event from the current history as a witnessed predecessor
history together with the associated structural data. -/
lemma local_event_predecessor
    {H : History P (Signature.EventType S)}
    {t : EventTuple P (Signature.EventType S)}
    (p : P) (ht : t ∈ H.val)
    (hp : EventTuple.participant t = p) :
    ∃ H' : History P (Signature.EventType S),
      H'.val = EventTuple.time t ∧
        H'.val ≺ₚ[p]H.val := by
  classical
  rcases t with ⟨p_t, evt_t, h_t⟩
  have ht_mem : (p_t, evt_t, h_t) ∈ H.val := by simpa using ht
  have hp_t : p_t = p := by simpa [EventTuple.participant] using hp
  have hBeforeAt : h_t ≺ₚ[p] H.val := by
    simpa [hp_t] using
      (PreHistory.happensBeforeAt_of_mem (P := P)
        (Event := Signature.EventType S) ht_mem)
  have hBefore : h_t ≺− H.val :=
    PreHistory.happensBefore_of_happensBeforeAt (P := P)
      (Event := Signature.EventType S) hBeforeAt
  refine ⟨History.predecessorHistory (H := H) hBefore, ?_, ?_⟩
  · simp [EventTuple.time, History.predecessorHistory]
  · simpa [EventTuple.time, History.predecessorHistory, hp_t] using hBeforeAt

variable [Nonempty P]
variable [DecidableEq S.VarSymb]
variable {M : Model S P} {σ : Assignment S}
variable {H H' : History P (Signature.EventType S)} {p : P}
variable {evt evt' : Signature.EventType S}
variable {ψ φ φ' : Formula S}
variable {l l' : Signature.Value S}

/-- Lemma 5.1.1(1): sequentiality persists when restricting to a smaller history. -/
lemma seq_monotone_of_subset
    (hSub : H'.val ⊆trn H.val)
    (hSeq : ⟨H,p⟩ ⊨[M,σ]Formula.seq) :
    ⟨H',p⟩ ⊨[M,σ]Formula.seq := by
  classical
  have hSeq' : isSequential (P := P) (Event := Signature.EventType S) p H.val := by
    simpa [Sat] using hSeq
  unfold Sat
  exact
    sequentiality_monotone
      (P := P) (Event := Signature.EventType S)
      (p := p) (h := H) (h' := H') hSub hSeq'

/-- Lemma 5.1.1(2): sequentiality implies `⇓ᶠ`-sequentiality. -/
lemma seq_monotone_allItp
    (hSeq : ⟨H,p⟩ ⊨[M,σ]Formula.seq) :
    ⟨H,p⟩ ⊨[M,σ]⇓ᶠFormula.seq := by
  classical
  refine Sat.not_intro (M := M) (σ := σ) (H := H) (p := p) ?_ -- deny any counterexample in the past
  intro hPast
  unfold Sat at hPast
  rcases hPast with ⟨H', hBefore, hNotSeq⟩
  have hSub : H'.val ⊆trn H.val :=
    happensBeforeAt_implies_transitiveSubset (P := P)
      (Event := Signature.EventType S) H' H p hBefore
  -- `H'` is a prefix of `H`, so sequentiality transfers
  have hSeq'' : ⟨H',p⟩ ⊨[M,σ]Formula.seq := by
    have := seq_monotone_of_subset
      (M := M) (σ := σ) (H := H) (H' := H') (p := p) hSub hSeq
    simpa using this
  -- `H'` cannot simultaneously refute sequentiality
  exact
    Sat.not_elim (M := M) (σ := σ) (H := H') (p := p)
      (φ := Formula.seq) hNotSeq hSeq''

/-- Proposition 5.1.2(1): quorum intersections furnish a joint witness. -/
theorem two_quorums_exists
    (hψ : ⟨H,p⟩ ⊨[M,σ]♢ᶠ[Term.ofValues [l, l']]ψ)
    (hφ : ⟨H,p⟩ ⊨[M,σ]□ᶠ[Term.ofValues [l]]φ)
    (hφ' : ⟨H,p⟩ ⊨[M,σ]□ᶠ[Term.ofValues [l']]φ') :
    ⟨H,p⟩ ⊨[M,σ]♢ᶠ[] ((ψ ∧ᶠ φ) ∧ᶠ φ') := by
  classical
  obtain ⟨O, hO, hO_all⟩ :=
    (sat_box_singleton_exists (M := M) (σ := σ)
      (H := H) (p := p) (l := l) (φ := φ)).1 hφ
  obtain ⟨O', hO', hO'_all⟩ :=
    (sat_box_singleton_exists (M := M) (σ := σ)
      (H := H) (p := p) (l := l') (φ := φ')).1 hφ'
  obtain ⟨q, hqMem, hqψ⟩ :=
    (sat_diamond_pair_iff (M := M) (σ := σ)
      (H := H) (p := p) (l := l) (l' := l') (φ := ψ)).1 hψ
      O hO O' hO'
  have hqφ : ⟨H,q⟩ ⊨[M ∣ᵥ H,σ] φ :=
    hO_all q (Set.mem_of_mem_inter_left hqMem)
  have hqφ' : ⟨H,q⟩ ⊨[M ∣ᵥ H,σ] φ' :=
    hO'_all q (Set.mem_of_mem_inter_right hqMem)
  have hψφ : ⟨H,q⟩ ⊨[M ∣ᵥ H,σ] (ψ ∧ᶠ φ) :=
    Sat.and_intro (M := M ∣ᵥ H) (σ := σ)
      (H := H) (p := q) hqψ hqφ
  have hConj : ⟨H,q⟩ ⊨[M ∣ᵥ H,σ] ((ψ ∧ᶠ φ) ∧ᶠ φ') :=
    Sat.and_intro (M := M ∣ᵥ H) (σ := σ)
      (H := H) (p := q) hψφ hqφ'
  exact
    sat_diamondEmpty_of_local (M := M) (σ := σ) (H := H) (p := p)
      (φ := ((ψ ∧ᶠ φ) ∧ᶠ φ')) ⟨q, hConj⟩

/-- Local views preserve the sequentiality of a participant. -/
lemma seq_localView_of_seq
    {H H_bar : History P (Signature.EventType S)}
    (hSeq : ⟨H,p⟩ ⊨[M,σ]Formula.seq) :
    ⟨H_bar ∣ᵥ H,p⟩ ⊨[M,σ]Formula.seq := by
  classical
  have hSeq' :
      isSequential (P := P) (Event := Signature.EventType S) p H.val := by
    simpa [Sat] using hSeq
  have hSeqLV :
      isSequential (P := P) (Event := Signature.EventType S) p
        (H_bar ∣ᵥ H).val :=
    sequentiality_forward (p := p) (H := H) (H_bar := H_bar) hSeq'
  unfold Sat
  exact hSeqLV

/-- Sequentiality on a local view lifts back to the full history when the
local view comes from a super-history. -/
lemma seq_of_localView_of_superset
    {H H_bar : History P (Signature.EventType S)}
    (hSub : H ⊆trn H_bar.val)
    (hSeq : ⟨H_bar ∣ᵥ H,p⟩ ⊨[M,σ]Formula.seq) :
    ⟨H,p⟩ ⊨[M,σ]Formula.seq := by
  classical
  have hSeqLV :
      isSequential (P := P) (Event := Signature.EventType S) p
        (H_bar ∣ᵥ H).val := by
    simpa [Sat] using hSeq
  have hSeqH :
      isSequential (P := P) (Event := Signature.EventType S) p H.val :=
    sequentiality_backward (p := p) (H := H) (H_bar := H_bar)
      hSub hSeqLV
  unfold Sat
  exact hSeqH

/-- Sequentiality is invariant under taking local views along histories that extend the
current one. -/
lemma seq_localView_iff
    {H H_bar : History P (Signature.EventType S)}
    (hSub : H ⊆trn H_bar.val) :
    (⟨H,p⟩ ⊨[M,σ]Formula.seq) ↔
      (⟨H_bar ∣ᵥ H,p⟩ ⊨[M,σ]Formula.seq) := by
  constructor
  · intro hSeq
    exact seq_localView_of_seq (M := M) (σ := σ) (H := H) (H_bar := H_bar)
      (p := p) hSeq
  · intro hSeqLV
    exact seq_of_localView_of_superset (M := M) (σ := σ)
      (H := H) (H_bar := H_bar) (p := p) hSub hSeqLV

/-- Sequentiality propagates to predecessors that happen before the current history. -/
lemma seq_preHistory_of_happensBefore
    {H : History P (Signature.EventType S)}
    {h' : PreHistory P (Signature.EventType S)}
    (hSeq : ⟨H,p⟩ ⊨[M,σ]Formula.seq)
    (hBefore : h' ≺− H.val) :
    isSequential (P := P) (Event := Signature.EventType S) p h' := by
  classical
  have hSeq' :
      isSequential (P := P) (Event := Signature.EventType S) p H.val := by
    simpa [Sat] using hSeq
  have hsubset : h' ⊆ H.val := History.transitive H h' hBefore
  intro t₁ t₂ ht₁ ht₂ hp₁ hp₂
  have ht₁' : t₁ ∈ H.val := hsubset _ ht₁
  have ht₂' : t₂ ∈ H.val := hsubset _ ht₂
  exact hSeq' ht₁' ht₂' hp₁ hp₂

/-- Any two `p`-prefixes of a sequential history are comparable. -/
lemma seq_compare_prefixes
    {H : History P (Signature.EventType S)}
    (hSeq : ⟨H,p⟩ ⊨[M,σ]Formula.seq)
    {H₁ H₂ : PreHistory P (Signature.EventType S)}
    (h₁ : H₁ ≺ₚ[p]H.val)
    (h₂ : H₂ ≺ₚ[p]H.val) :
    H₁ ⪯ H₂ ∨ H₂ ⪯ H₁ := by
  classical
  have hSeq' :
      isSequential (P := P) (Event := Signature.EventType S) p H.val := by
    simpa [Sat] using hSeq
  rcases h₁ with ⟨e₁, hmem₁⟩
  rcases h₂ with ⟨e₂, hmem₂⟩
  let t₁ : EventTuple P (Signature.EventType S) := (p, e₁, H₁)
  let t₂ : EventTuple P (Signature.EventType S) := (p, e₂, H₂)
  have ht₁ : t₁ ∈ H.val := by simpa [t₁]
    using hmem₁
  have ht₂ : t₂ ∈ H.val := by simpa [t₂]
    using hmem₂
  rcases hSeq' ht₁ ht₂ (by rfl) (by rfl) with hIn | hInEq
  · have hIn' : (p, e₁, H₁) ∈ H₂ := by
      simpa [EventTuple.time, t₁, t₂] using hIn
    have hBeforeAt : H₁ ≺ₚ[p] H₂ := ⟨e₁, hIn'⟩
    have hBefore : H₁ ≺− H₂ :=
      PreHistory.happensBefore_of_happensBeforeAt (P := P)
        (Event := Signature.EventType S) hBeforeAt
    exact Or.inl (Or.inl hBefore)
  · rcases hInEq with hIn | hEq
    · have hIn' : (p, e₂, H₂) ∈ H₁ := by
        simpa [EventTuple.time, t₁, t₂] using hIn
      have hBeforeAt : H₂ ≺ₚ[p] H₁ := ⟨e₂, hIn'⟩
      have hBefore : H₂ ≺− H₁ :=
        PreHistory.happensBefore_of_happensBeforeAt (P := P)
          (Event := Signature.EventType S) hBeforeAt
      exact Or.inr (Or.inl hBefore)
    · have hEqTime : H₁ = H₂ := by
        have := congrArg EventTuple.time hEq
        simpa [EventTuple.time, t₁, t₂] using this
      exact Or.inl (Or.inr hEqTime)

/-- Local events owned by `p` are totally preordered under sequentiality. -/
lemma seq_compare_event_times
    {H : History P (Signature.EventType S)}
    (hSeq : ⟨H,p⟩ ⊨[M,σ]Formula.seq)
    {t₁ t₂ : EventTuple P (Signature.EventType S)}
    (h₁ : t₁ ∈ H.val)
    (h₂ : t₂ ∈ H.val)
    (hp₁ : EventTuple.participant t₁ = p)
    (hp₂ : EventTuple.participant t₂ = p) :
    EventTuple.time t₁ ⪯ EventTuple.time t₂ ∨
      EventTuple.time t₂ ⪯ EventTuple.time t₁ := by
  classical
  rcases t₁ with ⟨p₁, e₁, h₁_time⟩
  rcases t₂ with ⟨p₂, e₂, h₂_time⟩
  have hp₁' : p₁ = p := by
    simpa [EventTuple.participant] using hp₁
  have hp₂' : p₂ = p := by
    simpa [EventTuple.participant] using hp₂
  have hSeq' :
      isSequential (P := P) (Event := Signature.EventType S) p H.val := by
    simpa [Sat] using hSeq
  have hmem₁ : (p₁, e₁, h₁_time) ∈ H.val := by
    simpa using h₁
  have hmem₂ : (p₂, e₂, h₂_time) ∈ H.val := by
    simpa using h₂
  have hCompare := hSeq' hmem₁ hmem₂ hp₁ hp₂
  rcases hCompare with hIn | hInEq
  · have hIn' : (p, e₁, h₁_time) ∈ h₂_time := by
      simpa [hp₁'] using hIn
    have hBeforeAt : h₁_time ≺ₚ[p] h₂_time := ⟨e₁, hIn'⟩
    have hBefore : h₁_time ≺− h₂_time :=
      PreHistory.happensBefore_of_happensBeforeAt (P := P)
        (Event := Signature.EventType S) hBeforeAt
    exact Or.inl (Or.inl (by simpa [EventTuple.time] using hBefore))
  · rcases hInEq with hIn | hEq
    · have hIn' : (p, e₂, h₂_time) ∈ h₁_time := by
        simpa [hp₂'] using hIn
      have hBeforeAt : h₂_time ≺ₚ[p] h₁_time := ⟨e₂, hIn'⟩
      have hBefore : h₂_time ≺− h₁_time :=
        PreHistory.happensBefore_of_happensBeforeAt (P := P)
          (Event := Signature.EventType S) hBeforeAt
      exact Or.inr (Or.inl (by simpa [EventTuple.time] using hBefore))
    · have hEqTime : h₁_time = h₂_time := by
        have := congrArg EventTuple.time hEq
        simpa [EventTuple.time] using this
      exact Or.inl (Or.inr (by simpa [EventTuple.time] using hEqTime))

/-- The local time of any `p`-event inherits sequentiality. -/
lemma seq_event_time_sequential
    {H : History P (Signature.EventType S)}
    (hSeq : ⟨H,p⟩ ⊨[M,σ]Formula.seq)
    {t : EventTuple P (Signature.EventType S)}
    (ht : t ∈ H.val)
    (hp : EventTuple.participant t = p) :
    isSequential (P := P) (Event := Signature.EventType S) p (EventTuple.time t) := by
  classical
  rcases t with ⟨p₁, e₁, h₁⟩
  have hp₁ : p₁ = p := by simpa [EventTuple.participant] using hp
  have hSeq' :
      isSequential (P := P) (Event := Signature.EventType S) p H.val := by
    simpa [Sat] using hSeq
  have hmem : (p₁, e₁, h₁) ∈ H.val := by simpa using ht
  have hmem' : (p, e₁, h₁) ∈ H.val := by simpa [hp₁] using hmem
  have hBefore : h₁ ≺− H.val :=
    (PreHistory.happensBefore_of_happensBeforeAt (P := P)
        (Event := Signature.EventType S))
      (PreHistory.happensBeforeAt_of_mem (P := P)
        (Event := Signature.EventType S) hmem')
  have hSeqTime :
      isSequential (P := P) (Event := Signature.EventType S) p h₁ :=
    seq_preHistory_of_happensBefore (M := M) (σ := σ)
      (H := H) (p := p) (hSeq := hSeq) (hBefore := hBefore)
  change isSequential (P := P) (Event := Signature.EventType S) p h₁
  exact hSeqTime

/-- Sequential participants with a local `p`-event admit a strict past witness of sequentiality. -/
lemma seq_down_of_seq
    {H : History P (Signature.EventType S)}
    (hLocal : ∃ t ∈ H.val, EventTuple.participant t = p)
    (hSeq : ⟨H,p⟩ ⊨[M,σ]Formula.seq) :
    ⟨H,p⟩ ⊨[M,σ]↓ᶠ Formula.seq := by
  classical
  obtain ⟨t, ht, hp_t⟩ := hLocal
  obtain ⟨H', hTime, hBefore⟩ :=
    local_event_predecessor (H := H) (p := p)
      (t := t) ht hp_t
  have hBeforeStrict : H'.val ≺− H.val :=
    PreHistory.happensBefore_of_happensBeforeAt (P := P)
      (Event := Signature.EventType S) hBefore
  have hSeq' :
      isSequential (P := P) (Event := Signature.EventType S) p H'.val :=
    seq_preHistory_of_happensBefore (M := M) (σ := σ)
      (H := H) (p := p) (hSeq := hSeq) (hBefore := hBeforeStrict)
  unfold Sat
  refine ⟨H', hBefore, ?_⟩
  unfold Sat
  exact hSeq'

/-- Once every prefix is sequential, iterating the past modality is redundant. -/
lemma seq_allPast_idem
    {H : History P (Signature.EventType S)}
    (hPast : ⟨H,p⟩ ⊨[M,σ]⇓ᶠFormula.seq) :
    ⟨H,p⟩ ⊨[M,σ]⇓ᶠ⇓ᶠFormula.seq := by
  classical
  exact
    Sat.eventuallyPast_of_imp (M := M) (σ := σ)
      (H := H) (p := p)
      (φ := Formula.seq)
      (ψ := ⇓ᶠFormula.seq)
      (h := fun H' hSeq =>
        seq_monotone_allItp (M := M) (σ := σ)
          (H := H') (p := p) hSeq)
      hPast

lemma sat_diamondPast_empty
    {H' : History P (Signature.EventType S)}
    (hBefore : H'.val ≺ₚ[p]H.val)
    (hφ : ⟨H',p⟩ ⊨[M ∣ᵥ H,σ]φ) :
    ⟨H,p⟩ ⊨[M,σ]♢ᶠ↓[Term.ofValues []]φ := by
  classical
  refine
    (sat_diamondPast_nil_iff (M := M) (σ := σ)
      (H := H) (p := p) (φ := φ)).2
      ⟨p, H', hBefore, ⟨happensBeforeAt_implies_transitiveSubset H' H p hBefore, hφ⟩⟩

/-- Sequentiality together with a local `p`-event yields a witness for the empty
past diamond. -/
lemma seq_diamond_empty_of_seq
    {H : History P (Signature.EventType S)}
    (hSeq : ⟨H,p⟩ ⊨[M,σ]Formula.seq)
    (hLocal : ∃ t ∈ H.val, EventTuple.participant t = p) :
    ⟨H,p⟩ ⊨[M,σ]♢ᶠ↓[Term.ofValues []]Formula.seq := by
  classical
  obtain ⟨t, ht_mem, ht_part⟩ := hLocal
  obtain ⟨H', hEq, hBefore⟩ :=
    local_event_predecessor (H := H) (p := p)
      (t := t) ht_mem ht_part
  have hBeforeStrict : H'.val ≺− H.val :=
    PreHistory.happensBefore_of_happensBeforeAt (P := P)
      (Event := Signature.EventType S) hBefore
  have hSeqH' :
      isSequential (P := P) (Event := Signature.EventType S) p H'.val :=
    seq_preHistory_of_happensBefore (M := M) (σ := σ)
      (H := H) (p := p) (hSeq := hSeq) (hBefore := hBeforeStrict)
  have hLocalSeq : ⟨H',p⟩ ⊨[M ∣ᵥ H,σ]Formula.seq := by
    unfold Sat
    exact hSeqH'
  have hSubset : H'.val ⊆trn H.val :=
    ⟨History.transitive H H'.val hBeforeStrict,
      History.hereditarilyTransitive H'⟩
  exact
    sat_diamondPast_empty (M := M) (σ := σ)
      (H := H) (p := p) (φ := Formula.seq)
      (H' := H') hBefore hLocalSeq

/-- A diamond proof of sequentiality yields a concrete participant witness. -/
lemma seq_exists_local_witness
    {H : History P (Signature.EventType S)}
    (hSeq : ⟨H,p⟩ ⊨[M,σ]♢ᶠ[Term.ofValues []]Formula.seq) :
    ∃ q, ⟨H,q⟩ ⊨[M ∣ᵥ H,σ]Formula.seq := by
  classical
  have hDiamondEmpty : ⟨H,p⟩ ⊨[M,σ]♢ᶠ[[]]Formula.seq := by
    simpa [Term.ofValues] using hSeq
  exact
    (Sat.diamond_nil (M := M) (σ := σ)
        (H := H) (p := p) (φ := Formula.seq)).1 hDiamondEmpty

/-- Sequentiality is preserved when evaluating in the local-view model. -/
lemma seq_model_localView
    {H : History P (Signature.EventType S)}
    (hSeq : ⟨H,p⟩ ⊨[M,σ]Formula.seq) :
    ⟨H,p⟩ ⊨[M ∣ᵥ H,σ]Formula.seq := by
  classical
  unfold Sat at hSeq ⊢
  exact hSeq

/-- Evaluating sequentiality in the local-view model is equivalent to doing so globally. -/
lemma seq_iff_model_localView
    {H : History P (Signature.EventType S)} :
    (⟨H,p⟩ ⊨[M,σ]Formula.seq) ↔
      (⟨H,p⟩ ⊨[M ∣ᵥ H,σ]Formula.seq) := by
  classical
  constructor <;> intro h
  · unfold Sat at h ⊢; exact h
  · unfold Sat at h ⊢; exact h

/-- Sequentiality in the local-view model implies global sequentiality. -/
lemma seq_of_model_localView
    {H : History P (Signature.EventType S)}
    (hSeq : ⟨H,p⟩ ⊨[M ∣ᵥ H,σ]Formula.seq) :
    ⟨H,p⟩ ⊨[M,σ]Formula.seq := by
  classical
  unfold Sat at hSeq ⊢
  exact hSeq

/-- The sequentiality formula has no free variables. -/
lemma seq_freeVars :
    Formula.freeVars (S := S) Formula.seq = ∅ := by
  simp [Formula.freeVars]

/-- `Formula.seq` is closed under the free-variable predicate. -/
lemma seq_isClosed :
    (Formula.seq : Formula S).IsClosed := by
  classical
  simp [Formula.IsClosed]

/-- Value substitution leaves the sequentiality formula unchanged. -/
lemma seq_substValue (a : S.VarSymb) (v : Signature.Value S) :
    Formula.substValue (S := S) a v Formula.seq = Formula.seq := by
  simp [Formula.substValue]

/-- Satisfaction of `seq` does not depend on the assignment. -/
lemma seq_assignment_invariant
    {H : History P (Signature.EventType S)}
    (σ' : Assignment S)
    (hSeq : ⟨H,p⟩ ⊨[M,σ]Formula.seq) :
    ⟨H,p⟩ ⊨[M,σ']Formula.seq := by
  classical
  unfold Sat at hSeq ⊢
  exact hSeq

/-- Changing the assignment leaves `seq` satisfaction unchanged. -/
lemma seq_assignment_iff
    {H : History P (Signature.EventType S)}
    (σ σ' : Assignment S) :
    (⟨H,p⟩ ⊨[M,σ]Formula.seq) ↔
      (⟨H,p⟩ ⊨[M,σ']Formula.seq) := by
  classical
  constructor <;> intro h
  · unfold Sat at h ⊢; exact h
  · unfold Sat at h ⊢; exact h

/-- Lift satisfaction of the left disjunct to the full disjunction formula. -/
lemma sat_or_of_left
    {φ ψ : Formula S}
    (hφ : ⟨H,p⟩ ⊨[M,σ]φ) :
    ⟨H,p⟩ ⊨[M,σ] (φ ∨ᶠ ψ) := by
  classical
  have hImp :
      (⟨H,p⟩ ⊨[M,σ] ¬ᶠ φ) → (⟨H,p⟩ ⊨[M,σ]ψ) := by
    intro hNot
    have hFalse :=
      (Sat.not_elim (M := M) (σ := σ) (H := H) (p := p)
        (φ := φ)) hNot hφ
    exact hFalse.elim
  exact
    (Sat.imp (M := M) (σ := σ) (H := H) (p := p)
      (φ := ¬ᶠ φ) (ψ := ψ)).2 hImp

/-- Lift satisfaction of the right disjunct to the full disjunction formula. -/
lemma sat_or_of_right
    {φ ψ : Formula S}
    (hψ : ⟨H,p⟩ ⊨[M,σ]ψ) :
    ⟨H,p⟩ ⊨[M,σ] (φ ∨ᶠ ψ) := by
  classical
  have hImp :
      (⟨H,p⟩ ⊨[M,σ] ¬ᶠ φ) → (⟨H,p⟩ ⊨[M,σ]ψ) := by
    intro _; exact hψ
  exact
    (Sat.imp (M := M) (σ := σ) (H := H) (p := p)
      (φ := ¬ᶠ φ) (ψ := ψ)).2 hImp

/-- Resolve a satisfied disjunction into propositional alternatives. -/
lemma sat_or_cases
    {φ ψ : Formula S}
    (h : ⟨H,p⟩ ⊨[M,σ](φ ∨ᶠ ψ)) :
    (⟨H,p⟩ ⊨[M,σ] φ) ∨ (⟨H,p⟩ ⊨[M,σ] ψ) := by
  classical
  have hImp :
      (⟨H,p⟩ ⊨[M,σ] ¬ᶠ φ) → (⟨H,p⟩ ⊨[M,σ] ψ) :=
    (Sat.imp (M := M) (σ := σ) (H := H) (p := p)
      (φ := ¬ᶠ φ) (ψ := ψ)).1
      (by simpa [Formula.or] using h)
  by_cases hφ : ⟨H,p⟩ ⊨[M,σ] φ
  · exact Or.inl hφ
  · have hNotφ : ⟨H,p⟩ ⊨[M,σ] ¬ᶠ φ :=
      Sat.not_intro (M := M) (σ := σ) (H := H) (p := p)
        (φ := φ) (fun hφ' => (hφ hφ').elim)
    exact Or.inr (hImp hNotφ)

/-- Extract the left conjunct from a satisfied conjunction. -/
lemma sat_and_left
    {φ ψ : Formula S}
    (h : ⟨H,p⟩ ⊨[M,σ](φ ∧ᶠ ψ)) :
    ⟨H,p⟩ ⊨[M,σ] φ := by
  classical
  have hNotImp :
      ⟨H,p⟩ ⊨[M,σ] ¬ᶠ (φ ⇒ᶠ ¬ᶠ ψ) := by
    simpa [Formula.and]
      using h
  by_contra hNotφ
  have hImp :
      ⟨H,p⟩ ⊨[M,σ] φ ⇒ᶠ ¬ᶠ ψ :=
    (Sat.imp (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ) (ψ := ¬ᶠ ψ)).2 fun hφ =>
        (Sat.not_intro (M := M) (σ := σ) (H := H) (p := p)
          (φ := ψ) (fun _ => (hNotφ hφ).elim))
  exact
    (Sat.not_elim (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ ⇒ᶠ ¬ᶠ ψ)) hNotImp hImp

/-- Extract the right conjunct from a satisfied conjunction. -/
lemma sat_and_right
    {φ ψ : Formula S}
    (h : ⟨H,p⟩ ⊨[M,σ](φ ∧ᶠ ψ)) :
    ⟨H,p⟩ ⊨[M,σ] ψ := by
  classical
  have hNotImp :
      ⟨H,p⟩ ⊨[M,σ] ¬ᶠ (φ ⇒ᶠ ¬ᶠ ψ) := by
    simpa [Formula.and]
      using h
  by_contra hNotψ
  have hImp :
      ⟨H,p⟩ ⊨[M,σ] φ ⇒ᶠ ¬ᶠ ψ :=
    (Sat.imp (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ) (ψ := ¬ᶠ ψ)).2 fun _ =>
        Sat.not_intro (M := M) (σ := σ) (H := H) (p := p)
          (φ := ψ) hNotψ
  exact
    (Sat.not_elim (M := M) (σ := σ) (H := H) (p := p)
      (φ := φ ⇒ᶠ ¬ᶠ ψ)) hNotImp hImp

/-- Satisfaction of the empty past diamond is independent of the distinguished participant. -/
lemma sat_diamondPast_empty_participant_iff
    (p q : P) (φ : Formula S) :
    (⟨H,p⟩ ⊨[M,σ] ♢ᶠ↓[Term.ofValues []] φ) ↔
      (⟨H,q⟩ ⊨[M,σ] ♢ᶠ↓[Term.ofValues []] φ) := by
  classical
  simp [Formula.diamondPast, Sat, Sat.check, Set.mem_univ]

/-- Proposition 5.1.2(2): sequential participants order any two local events. -/
theorem seq_two_quorums_events
    (hSeq : ⟨H,p⟩ ⊨[M,σ]Formula.seq)
    (hEvt_local : ⟨H,p⟩ ⊨[M ∣ᵥ H,σ]↓ᶠ (Formula.ofEvent evt))
    (hEvt'_local : ⟨H,p⟩ ⊨[M ∣ᵥ H,σ]↓ᶠ (Formula.ofEvent evt'))
    (hDistinct : evt ≠ evt') :
    ⟨H,p⟩ ⊨[M,σ]
      ((♢ᶠ↓[Term.ofValues []]((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt'))) ∨ᶠ
        (♢ᶠ↓[Term.ofValues []]((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))) := by
  classical
  have hEvt_local' := hEvt_local
  have hEvt'_local' := hEvt'_local
  unfold Sat at hEvt_local' hEvt'_local'
  obtain ⟨H₁, hBefore₁, hEvent₁⟩ := hEvt_local'
  obtain ⟨H₂, hBefore₂, hEvent₂⟩ := hEvt'_local'
  have hSeq' :
      isSequential (P := P) (Event := Signature.EventType S) p H.val := by
    simpa [Sat] using hSeq
  set eEvt₁ : Signature.EventType S :=
      ⟨evt.sym, Term.evalList σ (evt.args.map Term.ofValue)⟩
  set eEvt₂ : Signature.EventType S :=
      ⟨evt'.sym, Term.evalList σ (evt'.args.map Term.ofValue)⟩
  have hMem₁ :
      (p,
        MaybeEvent.some eEvt₁,
        H₁.val) ∈ H.val := by
    simpa [Formula.ofEvent, eEvt₁]
      using
        (Sat.event (M := M ∣ᵥ H) (σ := σ) (H := H₁) (p := p)
          (evt := ⟨evt.sym, evt.args.map Term.ofValue⟩)).1 hEvent₁
  have hMem₂ :
      (p,
        MaybeEvent.some eEvt₂,
        H₂.val) ∈ H.val := by
    simpa [Formula.ofEvent, eEvt₂]
      using
        (Sat.event (M := M ∣ᵥ H) (σ := σ) (H := H₂) (p := p)
          (evt := ⟨evt'.sym, evt'.args.map Term.ofValue⟩)).1 hEvent₂
  set t₁ : EventTuple P (Signature.EventType S) :=
      (p, MaybeEvent.some eEvt₁, H₁.val)
  set t₂ : EventTuple P (Signature.EventType S) :=
      (p, MaybeEvent.some eEvt₂, H₂.val)
  have ht₁_mem : t₁ ∈ H.val := by simpa [t₁] using hMem₁
  have ht₂_mem : t₂ ∈ H.val := by simpa [t₂] using hMem₂
  have hp₁ : EventTuple.participant t₁ = p := by
    simp [EventTuple.participant, t₁]
  have hp₂ : EventTuple.participant t₂ = p := by
    simp [EventTuple.participant, t₂]
  have hOrder := hSeq' ht₁_mem ht₂_mem hp₁ hp₂
  cases hOrder with
  | inl hIn =>
      -- Event `evt` appears in the timeline of `evt'`, so witness the right disjunct.
      have hBefore₁₂ : H₁.val ≺ₚ[p] H₂.val := by
        refine ⟨MaybeEvent.some eEvt₁, ?_⟩
        simpa [EventTuple.time, t₁, t₂]
          using hIn
      have hDown_evt :
          ⟨H₂,p⟩ ⊨[M ∣ᵥ H,σ] ↓ᶠ (Formula.ofEvent evt) :=
        Sat.past_intro_of_prefix (M := M ∣ᵥ H) (σ := σ)
          (H := H₂) (H' := H₁) (p := p) hBefore₁₂ hEvent₁
      have hConj :
          ⟨H₂,p⟩ ⊨[M ∣ᵥ H,σ]
            ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)) :=
        Sat.and_intro (M := M ∣ᵥ H) (σ := σ) (H := H₂) (p := p)
          hEvent₂ hDown_evt
      have hDiamond :
          ⟨H,p⟩ ⊨[M,σ]
            ♢ᶠ↓[Term.ofValues []]
              ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)) :=
        sat_diamondPast_empty (M := M) (σ := σ) (H := H) (p := p)
          (H' := H₂) hBefore₂ hConj
      exact
        sat_or_of_right (M := M) (σ := σ) (H := H) (p := p)
          (φ := ♢ᶠ↓[Term.ofValues []]
                    ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt')))
          (ψ := ♢ᶠ↓[Term.ofValues []]
                    ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))
          hDiamond
  | inr hInOrEq =>
      cases hInOrEq with
      | inl hIn =>
          -- Symmetric case: `evt'` precedes `evt`, witness the left disjunct.
          have hBefore₂₁ : H₂.val ≺ₚ[p] H₁.val := by
            refine ⟨MaybeEvent.some eEvt₂, ?_⟩
            simpa [EventTuple.time, t₁, t₂]
              using hIn
          have hDown_evt' :
              ⟨H₁,p⟩ ⊨[M ∣ᵥ H,σ] ↓ᶠ (Formula.ofEvent evt') :=
            Sat.past_intro_of_prefix (M := M ∣ᵥ H) (σ := σ)
              (H := H₁) (H' := H₂) (p := p) hBefore₂₁ hEvent₂
          have hConj :
              ⟨H₁,p⟩ ⊨[M ∣ᵥ H,σ]
                ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt')) :=
            Sat.and_intro (M := M ∣ᵥ H) (σ := σ) (H := H₁) (p := p)
              hEvent₁ hDown_evt'
          have hDiamond :
              ⟨H,p⟩ ⊨[M,σ]
                ♢ᶠ↓[Term.ofValues []]
                  ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt')) :=
            sat_diamondPast_empty (M := M) (σ := σ) (H := H) (p := p)
              (H' := H₁) hBefore₁ hConj
          exact
            sat_or_of_left (M := M) (σ := σ) (H := H) (p := p)
              (φ := ♢ᶠ↓[Term.ofValues []]
                        ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt')))
              (ψ := ♢ᶠ↓[Term.ofValues []]
                        ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))
              hDiamond
      | inr hEq =>
          -- Equality contradicts the distinct-event hypothesis.
          have hSecond : t₁.2 = t₂.2 := congrArg Prod.snd hEq
          have hMaybe : MaybeEvent.some eEvt₁ = MaybeEvent.some eEvt₂ :=
            congrArg Prod.fst hSecond
          have hEvts : eEvt₁ = eEvt₂ := MaybeEvent.some.inj hMaybe
          have hSym : evt.sym = evt'.sym := by
            simpa [eEvt₁, eEvt₂] using
              congrArg Signature.Event.sym hEvts
          have hArgs : evt.args = evt'.args := by
            have hId : Term.eval σ ∘ Term.ofValue = (id : Signature.Value S → _) := by
              funext v
              simp [Function.comp]
            simpa [eEvt₁, eEvt₂, Term.evalList, Term.ofValues, hId]
              using congrArg Signature.Event.args hEvts
          have hFalse : False := by
            have hEq : evt = evt' := by
              cases evt with
              | mk sym args =>
                cases evt' with
                | mk sym' args' =>
                  cases hSym
                  cases hArgs
                  rfl
            exact (hDistinct hEq).elim
          cases hFalse

/-- Proposition 5.1.2(3): quorum intersections inherit the sequencing dichotomy. -/
theorem seq_two_quorums_eventually
    (hSeq : ⟨H,p⟩ ⊨[M,σ]♢ᶠ[Term.ofValues [l, l']]Formula.seq)
    (hEvt : ⟨H,p⟩ ⊨[M,σ]□ᶠ↓[Term.ofValues [l]](Formula.ofEvent evt))
    (hEvt' : ⟨H,p⟩ ⊨[M,σ]□ᶠ↓[Term.ofValues [l']](Formula.ofEvent evt'))
    (hDistinct : evt ≠ evt') :
    ⟨H,p⟩ ⊨[M,σ]
      ((♢ᶠ↓[Term.ofValues []] ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt'))) ∨ᶠ
        (♢ᶠ↓[Term.ofValues []] ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))) := by
  classical
  have hWitness :=
    two_quorums_exists (M := M) (σ := σ) (H := H) (p := p)
      (ψ := Formula.seq)
      (φ := ↓ᶠ (Formula.ofEvent evt))
      (φ' := ↓ᶠ (Formula.ofEvent evt'))
      hSeq hEvt hEvt'
  obtain ⟨q, hLocal⟩ :=
    (Sat.diamond_nil (M := M) (σ := σ) (H := H) (p := p)
      (φ :=
        ((Formula.seq ∧ᶠ ↓ᶠ (Formula.ofEvent evt)) ∧ᶠ
          ↓ᶠ (Formula.ofEvent evt')))).1
      (by simpa [Formula.diamondEmpty] using hWitness)
  have hSeqEvt :=
    sat_and_left (M := M ∣ᵥ H) (σ := σ) (H := H) (p := q) hLocal
  have hSeq_local :=
    sat_and_left (M := M ∣ᵥ H) (σ := σ) (H := H) (p := q) hSeqEvt
  have hEvt_local :=
    sat_and_right (M := M ∣ᵥ H) (σ := σ) (H := H) (p := q) hSeqEvt
  have hEvt'_local :=
    sat_and_right (M := M ∣ᵥ H) (σ := σ) (H := H) (p := q) hLocal
  have hSeq_global : ⟨H,q⟩ ⊨[M,σ] Formula.seq :=
    seq_of_model_localView (M := M) (σ := σ) (H := H) (p := q) hSeq_local
  have hDisj_q :=
    seq_two_quorums_events (M := M) (σ := σ) (H := H) (p := q)
      hSeq_global hEvt_local hEvt'_local hDistinct
  set φ₁ :=
      ♢ᶠ↓[Term.ofValues []]
        ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt'))
    with hφ₁
  set φ₂ :=
      ♢ᶠ↓[Term.ofValues []]
        ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt))
    with hφ₂
  have hCases :=
    sat_or_cases (M := M) (σ := σ) (H := H) (p := q)
      (φ := φ₁) (ψ := φ₂) hDisj_q
  cases hCases with
  | inl hφ₁_q =>
      have hφ₁_p : ⟨H,p⟩ ⊨[M,σ] φ₁ := by
        have :=
          (sat_diamondPast_empty_participant_iff
            (M := M) (σ := σ) (H := H) (p := q) (q := p)
            (φ := ((Formula.ofEvent evt) ∧ᶠ ↓ᶠ (Formula.ofEvent evt')))).1 hφ₁_q
        simpa [hφ₁] using this
      exact
        sat_or_of_left (M := M) (σ := σ) (H := H) (p := p)
          (φ := φ₁) (ψ := φ₂) hφ₁_p
  | inr hφ₂_q =>
      have hφ₂_p : ⟨H,p⟩ ⊨[M,σ] φ₂ := by
        have :=
          (sat_diamondPast_empty_participant_iff
            (M := M) (σ := σ) (H := H) (p := q) (q := p)
            (φ := ((Formula.ofEvent evt') ∧ᶠ ↓ᶠ (Formula.ofEvent evt)))).1 hφ₂_q
        simpa [hφ₂] using this
      exact
        sat_or_of_right (M := M) (σ := σ) (H := H) (p := p)
          (φ := φ₁) (ψ := φ₂) hφ₂_p

end Logic
end ModalDistribution
