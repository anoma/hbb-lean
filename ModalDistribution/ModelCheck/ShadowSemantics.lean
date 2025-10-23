import Mathlib.Data.List.Range
import Mathlib.Data.List.Lemmas
import ModalDistribution.Core.Prehistory
import ModalDistribution.Core.Model
import ModalDistribution.Core.History
import ModalDistribution.Logic.Syntax
import ModalDistribution.Logic.Semantics

/-
# Shadow reconstruction scaffolding

This module currently reconstructs concrete worlds and prehistories from a finite
solver shadow.  Subsequent commits will add the shadow satisfaction semantics and
the equivalence lemmas requested in the design sketch.
-/

namespace ModalDistribution.ModelCheck

open Set ModalDistribution.Logic

section Depth

variable {S : Signature.{0, 0, 0}}

@[simp] private noncomputable def depth : Formula S → Nat
  | .bot => 0
  | .imp φ ψ => 1 + max (depth φ) (depth ψ)
  | .eq _ _ => 0
  | .forall body =>
      by
        classical
        exact
          if h : Nonempty S.Value then
            1 + depth (body (Classical.choice h))
          else
            0
  | .event _ => 0
  | .predicate _ => 0
  | .past φ => 1 + depth φ
  | .atEnd φ => 1 + depth φ
  | .diamond _ φ => 1 + depth φ
  | .seq => 0

private axiom depth_uniform [Nonempty S.Value]
    (body : S.Value → Formula S) (v₁ v₂ : S.Value) :
    depth (body v₁) = depth (body v₂)

private lemma depth_forall_body (body : S.Value → Formula S) (v : S.Value) :
    depth (body v) < depth (.forall body) := by
  classical
  by_cases h : Nonempty S.Value
  · have hdepth := depth_uniform (body := body) v (Classical.choice h)
    simp [depth, h, hdepth]
  · simpa [depth, h] using (absurd ⟨v⟩ h : False)

private lemma depth_diamond_body (ls : List S.Value) (φ : Formula S) :
    depth φ < depth (.diamond ls φ) := by
  simp [depth];

private lemma depth_past_body (φ : Formula S) :
    depth φ < depth (.past φ) := by
  simp [depth];

private lemma depth_atEnd_body (φ : Formula S) :
    depth φ < depth (.atEnd φ) := by
  simp [depth];

private lemma depth_imp_left (φ ψ : Formula S) :
    depth φ < depth (.imp φ ψ) := by
  simp [depth]; omega

private lemma depth_imp_right (φ ψ : Formula S) :
    depth ψ < depth (.imp φ ψ) := by
  simp [depth]; omega

end Depth

set_option linter.unusedVariables false

/-- Finite shadow frame describing a bounded history. -/
structure Shadow (P Event : Type) where
  nW    : Nat
  place : Nat → P
  evt   : Nat → MaybeEvent Event
  time  : Nat → Nat → Bool

namespace Shadow

variable {P Event : Type} (sh : Shadow P Event)

/-- Auxiliary builder used to reconstruct all worlds `0 .. n-1`. -/
private def buildWorlds (sh : Shadow P Event) :
    (n : Nat) → {l : List (World P Event) // l.length = n}
  | 0 => ⟨[], by simp⟩
  | n + 1 =>
      let ih := buildWorlds sh n
      let l := ih.1
      have hl : l.length = n := ih.2
      let timeList :
          List (World P Event) :=
        (List.range n).filterMap fun j =>
          if hj : j < n then
            if sh.time n j then
              some (l.get ⟨j, by
                have := hj
                simpa [hl] using this⟩)
            else
              none
          else
            none
      let world : World P Event :=
        (sh.place n, sh.evt n, PreHistory.mk timeList)
      ⟨l ++ [world], by
        simp [hl, List.length_append]⟩

private def worldListAt (sh : Shadow P Event) (n : Nat) : List (World P Event) :=
  (buildWorlds sh n).1

private lemma worldListAt_length (sh : Shadow P Event) (n : Nat) :
    (worldListAt sh n).length = n :=
  (buildWorlds sh n).2

private def timeListAt (sh : Shadow P Event) (n : Nat) : List (World P Event) :=
  (List.range n).filterMap fun j =>
    if hj : j < n then
      if sh.time n j then
        some ((worldListAt sh n).get
          ⟨j, by
            have : j < (worldListAt sh n).length := by
              simpa [worldListAt_length] using hj
            simpa using this⟩)
      else
        none
    else
      none

private lemma worldListAt_succ (sh : Shadow P Event) (n : Nat) :
    worldListAt sh (n + 1) =
      worldListAt sh n ++
        [ (sh.place n,
            sh.evt n,
            PreHistory.mk (timeListAt sh n)) ] := by
  simp [worldListAt, buildWorlds, timeListAt]

private def worldAtIdx (sh : Shadow P Event) {n : Nat} (i : Fin n) :
    World P Event :=
  (worldListAt sh n).get
    ⟨i.1, by simp [worldListAt_length]⟩

private lemma mem_timeListAt {n : Nat} {t : World P Event} :
    t ∈ timeListAt sh n ↔
      ∃ j : Fin n,
        sh.time n j = true ∧
        t = (worldListAt sh n).get
            ⟨(j : Nat), by simp [worldListAt_length]⟩ := by
  classical
  unfold timeListAt
  constructor
  · intro h
    obtain ⟨j, hj_mem, hj_eq⟩ := List.mem_filterMap.mp h
    have hj_lt : j < n := by
      simpa [List.mem_range] using hj_mem
    have hj_index : j < (worldListAt sh n).length := by
      simpa [worldListAt_length] using hj_lt
    have hj_eq' :
        (if sh.time n j then some ((worldListAt sh n).get ⟨j, hj_index⟩) else none)
          = some t := by
      simpa [hj_lt] using hj_eq
    cases htime : sh.time n j with
    | false =>
        have : False := by simp [htime] at hj_eq'
        exact this.elim
    | true =>
        have hval : (worldListAt sh n).get ⟨j, hj_index⟩ = t := by
          simpa [htime] using hj_eq'
        refine ⟨⟨j, hj_lt⟩, by simp [htime], hval.symm⟩
  · rintro ⟨j, hj_time, hj_val⟩
    have hj_index : (j : Nat) < (worldListAt sh n).length := by
      simp [worldListAt_length]
    refine List.mem_filterMap.mpr ?_
    refine ⟨(j : Nat), ?_, ?_⟩
    · simp [List.mem_range]
    · have hval : (worldListAt sh n).get ⟨(j : Nat), hj_index⟩ = t := by
        simpa [worldListAt_length, j.is_lt] using hj_val.symm
      simpa [j.is_lt, hj_time, hval]

def worldList : List (World P Event) :=
  worldListAt sh sh.nW

lemma worldList_length :
    sh.worldList.length = sh.nW :=
  worldListAt_length sh sh.nW

/-- Reconstructed world at index `i`. -/
noncomputable def worldAt (i : Fin sh.nW) : World P Event :=
  worldAtIdx sh i

/-- Prehistory reconstructed from the entire shadow frame. -/
noncomputable def preHistory : PreHistory P Event :=
  PreHistory.mk (List.ofFn fun i : Fin sh.nW => sh.worldAt i)

lemma worldAt_mem_preHistory (i : Fin sh.nW) :
    sh.worldAt i ∈ sh.preHistory := by
  classical
  simp [preHistory, List.mem_ofFn]

/-- Convenience wrapper providing the `i`-th reconstructed world from a natural
index together with the proof that it lies inside the bounds. -/
noncomputable def worldAtNat (i : Nat) (hi : i < sh.nW) : World P Event :=
  sh.worldAt ⟨i, hi⟩

lemma worldAtNat_mem_preHistory {i : Nat} {hi : i < sh.nW} :
    sh.worldAtNat i hi ∈ sh.preHistory :=
  sh.worldAt_mem_preHistory ⟨i, hi⟩

lemma worldListAt_get (n j : Nat) (hj : j < n) :
    (worldListAt sh n).get ⟨j, by simpa [worldListAt_length] using hj⟩ =
      (sh.place j, sh.evt j, PreHistory.mk (timeListAt sh j)) := by
  classical
  revert j
  induction n with
  | zero =>
      intro j hj
      exact (Nat.not_lt_zero _ hj).elim
  | succ n ih =>
      intro j hj
      have hj_le : j ≤ n := Nat.le_of_lt_succ hj
      have hj_cases := Nat.eq_or_lt_of_le hj_le
      have hlen : (worldListAt sh n).length = n := worldListAt_length sh n
      cases hj_cases with
      | inl hEq =>
          subst hEq
          simp [worldListAt_succ, hlen]
      | inr hj_lt =>
          have hlt : j < (worldListAt sh n).length := by
            simpa [worldListAt_length] using hj_lt
          have hj_append :
              j <
                (worldListAt sh n ++
                  [(sh.place n, sh.evt n, PreHistory.mk (timeListAt sh n))]).length := by
            have : j < (worldListAt sh n).length := hlt
            have : j < (worldListAt sh n).length + 1 := Nat.lt_succ_of_lt this
            simpa [List.length_append] using this
          have hElem :
              (worldListAt sh (n + 1))[j] =
                (worldListAt sh n)[j] := by
            simpa [worldListAt_succ] using
              List.getElem_append_left
                (as := worldListAt sh n)
                (bs := [(sh.place n, sh.evt n, PreHistory.mk (timeListAt sh n))])
                (i := j)
                (h := hlt)
                (h' := hj_append)
          have hlen' :
              j < (worldListAt sh (n + 1)).length := by
            have : j < (worldListAt sh n).length := hlt
            have : j < (worldListAt sh n).length + 1 := Nat.lt_succ_of_lt this
            simpa [worldListAt_succ, List.length_append] using this
          have hget :
              (worldListAt sh (n + 1)).get ⟨j, hlen'⟩ =
                (worldListAt sh n).get ⟨j, hlt⟩ := by
            calc
              (worldListAt sh (n + 1)).get ⟨j, hlen'⟩
                  = (worldListAt sh (n + 1))[j] :=
                    (List.get_eq_getElem
                      (l := worldListAt sh (n + 1))
                      (i := ⟨j, hlen'⟩)).symm
              _ = (worldListAt sh n)[j] := hElem
              _ = (worldListAt sh n).get ⟨j, hlt⟩ :=
                    List.get_eq_getElem (l := worldListAt sh n) (i := ⟨j, hlt⟩)
          have hw :
              (worldListAt sh n).get ⟨j, hlt⟩ =
                (sh.place j, sh.evt j, PreHistory.mk (timeListAt sh j)) :=
            ih (j := j) hj_lt
          exact hget ▸ hw

lemma worldAtNat_eq (i : Nat) (hi : i < sh.nW) :
    worldAtNat sh i hi =
      (sh.place i, sh.evt i, PreHistory.mk (timeListAt sh i)) := by
  classical
  have := worldListAt_get (sh := sh) (n := sh.nW) (j := i) hi
  simpa [worldAtNat, worldAt, worldAtIdx, worldList] using this

lemma worldAtNat_time (i : Nat) (hi : i < sh.nW) :
    (worldAtNat sh i hi).2.2 = PreHistory.mk (timeListAt sh i) := by
  have h := worldAtNat_eq (sh := sh) i hi
  simp [h]

lemma worldAt_eq_worldAtNat (i : Fin sh.nW) :
    sh.worldAt i = sh.worldAtNat i i.is_lt := by
  rfl

lemma worldAt_place (i : Fin sh.nW) :
    World.place (sh.worldAt i) = sh.place i := by
  simp [worldAt_eq_worldAtNat, worldAtNat_eq]

lemma worldAt_event (i : Fin sh.nW) :
    World.event (sh.worldAt i) = sh.evt i := by
  simp [worldAt_eq_worldAtNat, worldAtNat_eq]

lemma worldAt_time (i : Fin sh.nW) :
    World.time (sh.worldAt i) = PreHistory.mk (timeListAt sh i) := by
  simp [worldAt_eq_worldAtNat, worldAtNat_eq]

lemma worldAtNat_place (i : Nat) (hi : i < sh.nW) :
    (worldAtNat sh i hi).1 = sh.place i := by
  have h := worldAtNat_eq (sh := sh) i hi
  simp [h]

lemma worldAtNat_event (i : Nat) (hi : i < sh.nW) :
    (worldAtNat sh i hi).2.1 = sh.evt i := by
  have h := worldAtNat_eq (sh := sh) i hi
  simp [h]

lemma mem_worldAt_time {i : Nat} {hi : i < sh.nW} {t : World P Event} :
    t ∈ (worldAtNat sh i hi).2.2 ↔
      ∃ j : Fin i,
        sh.time i j = true ∧
        t = (worldListAt sh i).get
            ⟨(j : Nat), by
              simp [worldListAt_length]⟩ := by
  classical
  simp [worldAtNat_time (sh := sh) i hi, mem_timeListAt]

lemma mem_worldAt_time_nat {i : Nat} {hi : i < sh.nW} {t : World P Event} :
    t ∈ (worldAtNat sh i hi).2.2 ↔
      ∃ j : Fin i,
        sh.time i j = true ∧
        t = sh.worldAtNat j (Nat.lt_trans j.is_lt hi) := by
  classical
  constructor
  · intro ht
    rcases (mem_worldAt_time (sh := sh) (hi := hi) (t := t)).1 ht with ⟨j, hj_time, hj_val⟩
    have hget := worldListAt_get (sh := sh) (n := i) (j := (j : Nat)) j.is_lt
    have hnat := worldAtNat_eq (sh := sh) (i := j) (hi := Nat.lt_trans j.is_lt hi)
    have hrewrite :
        (worldListAt sh i).get
          ⟨(j : Nat), by simp [worldListAt_length]⟩ =
          sh.worldAtNat j (Nat.lt_trans j.is_lt hi) := by
      simpa [hnat] using hget
    refine ⟨j, hj_time, hj_val.trans hrewrite⟩
  · rintro ⟨j, hj_time, hj_val⟩
    have hget := worldListAt_get (sh := sh) (n := i) (j := (j : Nat)) j.is_lt
    have hnat := worldAtNat_eq (sh := sh) (i := j) (hi := Nat.lt_trans j.is_lt hi)
    have hrewrite :
        (worldListAt sh i).get
          ⟨(j : Nat), by simp [worldListAt_length]⟩ =
          sh.worldAtNat j (Nat.lt_trans j.is_lt hi) := by
      simpa [hnat] using hget
    have hlist :
        (worldListAt sh i).get
          ⟨(j : Nat), by simp [worldListAt_length]⟩ =
          sh.worldAtNat j (Nat.lt_trans j.is_lt hi) := by
      simpa [hnat] using hget
    have : t = (worldListAt sh i).get
        ⟨(j : Nat), by simp [worldListAt_length]⟩ :=
      hj_val.trans hlist.symm
    exact (mem_worldAt_time (sh := sh) (hi := hi) (t := t)).2 ⟨j, hj_time, this⟩

lemma mem_preHistory_iff (t : World P Event) :
    t ∈ sh.preHistory ↔ ∃ i : Fin sh.nW, sh.worldAt i = t := by
  classical
  simp [preHistory, List.mem_ofFn]

lemma seq_condition_world {i : Nat} {hi : i < sh.nW} {p : P} :
    (∀ {j₁ j₂ : Fin i},
        sh.place (j₁ : Nat) = p →
        sh.place (j₂ : Nat) = p →
        sh.worldAtNat j₁ (Nat.lt_trans j₁.is_lt hi) ∈ (worldAtNat sh i hi).2.2 →
        sh.worldAtNat j₂ (Nat.lt_trans j₂.is_lt hi) ∈ (worldAtNat sh i hi).2.2 →
          (sh.worldAtNat j₁ (Nat.lt_trans j₁.is_lt hi) ∈
              (worldAtNat sh (j₂ : Nat) (Nat.lt_trans j₂.is_lt hi)).2.2 ∨
            sh.worldAtNat j₂ (Nat.lt_trans j₂.is_lt hi) ∈
              (worldAtNat sh (j₁ : Nat) (Nat.lt_trans j₁.is_lt hi)).2.2 ∨
            sh.worldAtNat j₁ (Nat.lt_trans j₁.is_lt hi) =
              sh.worldAtNat j₂ (Nat.lt_trans j₂.is_lt hi))) ↔
      isSequential p (worldAtNat sh i hi).2.2 := by
  classical
  constructor
  · intro hSeq t₁ t₂ ht₁ ht₂ hplace₁ hplace₂
    obtain ⟨j₁, hj₁_time, hj₁_eq⟩ :=
      (mem_worldAt_time_nat (sh := sh) (hi := hi) (t := t₁)).1 ht₁
    obtain ⟨j₂, hj₂_time, hj₂_eq⟩ :=
      (mem_worldAt_time_nat (sh := sh) (hi := hi) (t := t₂)).1 ht₂
    have hdisj :=
      hSeq
        (j₁ := j₁)
        (j₂ := j₂)
        (by simpa [hj₁_eq, worldAtNat_place] using hplace₁)
        (by simpa [hj₂_eq, worldAtNat_place] using hplace₂)
        (by simpa [hj₁_eq] using ht₁)
        (by simpa [hj₂_eq] using ht₂)
    rcases hdisj with hdisj | hdisj | hdisj
    · have : t₁ ∈ World.time t₂ := by
        simpa [World.time, hj₁_eq, hj₂_eq] using hdisj
      exact Or.inl (by simpa [World.accessible] using this)
    · rcases hdisj with hdisj
      have : t₂ ∈ World.time t₁ := by
        simpa [World.time, hj₁_eq, hj₂_eq] using hdisj
      exact Or.inr (Or.inl (by simpa [World.accessible] using this))
    · exact Or.inr (Or.inr (by simpa [hj₁_eq, hj₂_eq] using hdisj))
  · intro hSeq j₁ j₂ hplace₁ hplace₂ hmem₁ hmem₂
    let t₁ := sh.worldAtNat j₁ (Nat.lt_trans j₁.is_lt hi)
    let t₂ := sh.worldAtNat j₂ (Nat.lt_trans j₂.is_lt hi)
    have hseq := hSeq
      (t₁ := t₁)
      (t₂ := t₂)
      hmem₁
      hmem₂
      (by simpa [t₁, worldAtNat_place] using hplace₁)
      (by simpa [t₂, worldAtNat_place] using hplace₂)
    rcases hseq with hseq | hseq | hseq
    · exact Or.inl (by simpa [World.accessible])
    · rcases hseq with hseq
      exact Or.inr (Or.inl (by simpa [World.accessible]))
    · exact Or.inr (Or.inr hseq)

lemma seq_condition_global {p : P} :
    (∀ {i j : Nat} (hi : i < sh.nW) (hj : j < sh.nW),
        sh.place i = p →
        sh.place j = p →
          (sh.worldAtNat i hi ∈ (worldAtNat sh j hj).2.2 ∨
            sh.worldAtNat j hj ∈ (worldAtNat sh i hi).2.2 ∨
            sh.worldAtNat i hi = sh.worldAtNat j hj)) ↔
      isSequential p sh.preHistory := by
  classical
  constructor
  · intro hSeq t₁ t₂ ht₁ ht₂ hplace₁ hplace₂
    obtain ⟨i, hi_eq⟩ := (Shadow.mem_preHistory_iff (sh := sh) (t := t₁)).1 ht₁
    obtain ⟨j, hj_eq⟩ := (Shadow.mem_preHistory_iff (sh := sh) (t := t₂)).1 ht₂
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    have hi_eq' : sh.worldAtNat i hi = t₁ := by
      simpa [worldAt_eq_worldAtNat] using hi_eq
    have hj_eq' : sh.worldAtNat j hj = t₂ := by
      simpa [worldAt_eq_worldAtNat] using hj_eq
    have hplace₁_eq : sh.place i = t₁.place := by
      simpa [worldAtNat_place] using congrArg World.place hi_eq'
    have hplace₂_eq : sh.place j = t₂.place := by
      simpa [worldAtNat_place] using congrArg World.place hj_eq'
    have hplace₁' : sh.place i = p := hplace₁_eq.trans hplace₁
    have hplace₂' : sh.place j = p := hplace₂_eq.trans hplace₂
    have hdisj := hSeq (i := i) (j := j) hi hj hplace₁' hplace₂'
    rcases hdisj with hdisj | hdisj | hdisj
    · have : t₁ ∈ World.time t₂ := by
        simpa [World.time, hi_eq', hj_eq'] using hdisj
      exact Or.inl (by simpa [World.accessible] using this)
    · rcases hdisj with hdisj
      have : t₂ ∈ World.time t₁ := by
        simpa [World.time, hi_eq', hj_eq'] using hdisj
      exact Or.inr (Or.inl (by simpa [World.accessible] using this))
    · exact Or.inr (Or.inr (by simpa [hi_eq', hj_eq'] using hdisj))
  · intro hSeq i j hi hj hplace₁ hplace₂
    have hi_mem : sh.worldAtNat i hi ∈ sh.preHistory :=
      sh.worldAtNat_mem_preHistory (i := i)
    have hj_mem : sh.worldAtNat j hj ∈ sh.preHistory :=
      sh.worldAtNat_mem_preHistory (i := j)
    have hdisj := hSeq
      (t₁ := sh.worldAtNat i hi)
      (t₂ := sh.worldAtNat j hj)
      hi_mem
      hj_mem
      (by simpa [worldAtNat_place] using hplace₁)
      (by simpa [worldAtNat_place] using hplace₂)
    rcases hdisj with hdisj | hdisj | hdisj
    · exact Or.inl (by simpa [World.accessible])
    · rcases hdisj with hdisj
      exact Or.inr (Or.inl (by simpa [World.accessible]))
    · exact Or.inr (Or.inr hdisj)
end Shadow

section Semantics

variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]

namespace Shadow

variable (sh : Shadow P (Signature.EventType S)) (M : Model S P)

mutual
  noncomputable def SatWCore (i : Nat) (hi : i < sh.nW) : Formula S → Prop
  | .bot => False
  | .imp φ ψ => SatWCore i hi φ → SatWCore i hi ψ
  | .eq v w => v = w
  | .forall body => ∀ v : S.Value, SatWCore i hi (body v)
  | .event a =>
      sh.evt i = MaybeEvent.some ⟨a.sym, a.args⟩
  | .predicate p =>
      ⟨p.sym, p.args⟩ ∈ M.predInterp (sh.place i) (worldAtNat sh i hi).2.2
  | .past φ =>
      ∃ j : Fin i,
        sh.time i (j : Nat) = true ∧
        sh.place (j : Nat) = sh.place i ∧
        SatWCore (j : Nat) (Nat.lt_trans j.is_lt hi) φ
  | .atEnd φ =>
      SatEGlobalCore (sh.place i) φ
  | .diamond ls φ =>
      let rec check : List S.Value → Set P → Prop
        | [], acc => ∃ p' ∈ acc, SatELocalCore i hi p' φ
        | ℓ :: rest, acc =>
            ∀ O ∈ (M.learner ℓ).quorums, check rest (acc ∩ O)
      termination_by ls => (depth φ, 1 + ls.length)
      check ls Set.univ
  | .seq =>
      ∀ {j₁ j₂ : Fin i},
        sh.place (j₁ : Nat) = sh.place i →
        sh.place (j₂ : Nat) = sh.place i →
        sh.worldAtNat j₁ (Nat.lt_trans j₁.is_lt hi) ∈ (worldAtNat sh i hi).2.2 →
        sh.worldAtNat j₂ (Nat.lt_trans j₂.is_lt hi) ∈ (worldAtNat sh i hi).2.2 →
          (sh.worldAtNat j₁ (Nat.lt_trans j₁.is_lt hi) ∈
              (worldAtNat sh (j₂ : Nat) (Nat.lt_trans j₂.is_lt hi)).2.2 ∨
            sh.worldAtNat j₂ (Nat.lt_trans j₂.is_lt hi) ∈
              (worldAtNat sh (j₁ : Nat) (Nat.lt_trans j₁.is_lt hi)).2.2 ∨
            sh.worldAtNat j₁ (Nat.lt_trans j₁.is_lt hi) =
              sh.worldAtNat j₂ (Nat.lt_trans j₂.is_lt hi))
  termination_by φ => (depth φ, 0)
  decreasing_by
    all_goals simp_wf
    all_goals (try omega)
    all_goals (try (apply Prod.Lex.left; exact depth_forall_body (body := _) _))

  noncomputable def SatELocalCore (i : Nat) (hi : i < sh.nW) (p : P) :
      Formula S → Prop
  | .bot => False
  | .imp φ ψ => SatELocalCore i hi p φ → SatELocalCore i hi p ψ
  | .eq v w => v = w
  | .forall body => ∀ v : S.Value, SatELocalCore i hi p (body v)
  | .event _ => False
  | .predicate q =>
      ⟨q.sym, q.args⟩ ∈ M.predInterp p (worldAtNat sh i hi).2.2
  | .past φ =>
      ∃ j : Fin i,
        sh.time i (j : Nat) = true ∧
        sh.place (j : Nat) = p ∧
        SatWCore (j : Nat) (Nat.lt_trans j.is_lt hi) φ
  | .atEnd φ =>
      SatEGlobalCore p φ
  | .diamond ls φ =>
      let rec check : List S.Value → Set P → Prop
        | [], acc => ∃ p' ∈ acc, SatELocalCore i hi p' φ
        | ℓ :: rest, acc =>
            ∀ O ∈ (M.learner ℓ).quorums, check rest (acc ∩ O)
      termination_by ls => (depth φ, 1 + ls.length)
      check ls Set.univ
  | .seq =>
      ∀ {j₁ j₂ : Fin i},
        sh.place (j₁ : Nat) = p →
        sh.place (j₂ : Nat) = p →
        sh.worldAtNat j₁ (Nat.lt_trans j₁.is_lt hi) ∈ (worldAtNat sh i hi).2.2 →
        sh.worldAtNat j₂ (Nat.lt_trans j₂.is_lt hi) ∈ (worldAtNat sh i hi).2.2 →
          (sh.worldAtNat j₁ (Nat.lt_trans j₁.is_lt hi) ∈
              (worldAtNat sh (j₂ : Nat) (Nat.lt_trans j₂.is_lt hi)).2.2 ∨
            sh.worldAtNat j₂ (Nat.lt_trans j₂.is_lt hi) ∈
              (worldAtNat sh (j₁ : Nat) (Nat.lt_trans j₁.is_lt hi)).2.2 ∨
            sh.worldAtNat j₁ (Nat.lt_trans j₁.is_lt hi) =
              sh.worldAtNat j₂ (Nat.lt_trans j₂.is_lt hi))
  termination_by φ => (depth φ, 0)
  decreasing_by
    all_goals simp_wf
    all_goals (try omega)
    all_goals (try (apply Prod.Lex.left; exact depth_forall_body (body := _) _))

  noncomputable def SatEGlobalCore (p : P) : Formula S → Prop
  | .bot => False
  | .imp φ ψ => SatEGlobalCore p φ → SatEGlobalCore p ψ
  | .eq v w => v = w
  | .forall body => ∀ v : S.Value, SatEGlobalCore p (body v)
  | .event _ => False
  | .predicate q =>
      ⟨q.sym, q.args⟩ ∈ M.predInterp p (sh.preHistory)
  | .past φ =>
      ∃ (i : Nat) (hi : i < sh.nW),
        sh.place i = p ∧ SatWCore i hi φ
  | .atEnd φ =>
      SatEGlobalCore p φ
  | .diamond ls φ =>
      let rec check : List S.Value → Set P → Prop
        | [], acc => ∃ p' ∈ acc, SatEGlobalCore p' φ
        | ℓ :: rest, acc =>
            ∀ O ∈ (M.learner ℓ).quorums, check rest (acc ∩ O)
      termination_by ls => (depth φ, 1 + ls.length)
      check ls Set.univ
  | .seq =>
      ∀ {i j : Nat} (hi : i < sh.nW) (hj : j < sh.nW),
        sh.place i = p →
        sh.place j = p →
          (sh.worldAtNat i hi ∈ (worldAtNat sh j hj).2.2 ∨
            sh.worldAtNat j hj ∈ (worldAtNat sh i hi).2.2 ∨
            sh.worldAtNat i hi = sh.worldAtNat j hj)
  termination_by φ => (depth φ, 0)
  decreasing_by
    all_goals simp_wf
    all_goals (try omega)
    all_goals (try (apply Prod.Lex.left; exact depth_forall_body (body := _) _))
end

variable {sh M}

def SatW (sh : Shadow P (Signature.EventType S)) (M : Model S P)
    (i : Nat) (hi : i < sh.nW) (φ : Formula S) : Prop :=
  SatWCore sh M i hi φ

def SatELocal (sh : Shadow P (Signature.EventType S)) (M : Model S P)
    (i : Nat) (hi : i < sh.nW) (p : P) (φ : Formula S) : Prop :=
  SatELocalCore sh M  i hi p φ

def SatEGlobal (sh : Shadow P (Signature.EventType S)) (M : Model S P)
    (p : P) (φ : Formula S) : Prop :=
  SatEGlobalCore sh M p φ

end Shadow

section Compatibility

variable {S : Signature.{0, 0, 0}} {P : Type} [Nonempty P]
variable {sh : Shadow P (Signature.EventType S)} {M : Model S P}

open Shadow

lemma worldAtNat_mem_history
    (hHist : M.history.val = sh.preHistory)
    {i : Nat} {hi : i < sh.nW} :
    sh.worldAtNat i hi ∈ M.history.val := by
  simpa [hHist] using sh.worldAtNat_mem_preHistory (i := i)

lemma worldAt_mem_history
    (hHist : M.history.val = sh.preHistory)
    {i : Fin sh.nW} :
    sh.worldAt i ∈ M.history.val := by
  simpa [hHist] using sh.worldAt_mem_preHistory i

mutual
  theorem satWCore_equiv
      (hHist : M.history.val = sh.preHistory)
      {i : Nat} {hi : i < sh.nW}
      (φ : Formula S) :
        SatWCore sh M i hi φ ↔
          Sat M (sh.worldAtNat i hi).1
            (sh.worldAtNat i hi).2.1
            (sh.worldAtNat i hi).2.2 φ := by
    classical
    match φ with
    | .bot => simp [SatWCore, Sat]
    | .imp φ ψ =>
        simp only [SatWCore, Sat]
        constructor
        · intro h hφ
          exact (satWCore_equiv hHist ψ).1 (h ((satWCore_equiv hHist φ).2 hφ))
        · intro h hφ
          exact (satWCore_equiv hHist ψ).2 (h ((satWCore_equiv hHist φ).1 hφ))
    | .eq v w => simp [SatWCore, Sat]
    | .forall body =>
        simp only [SatWCore, Sat]
        constructor
        · intro h v
          exact (satWCore_equiv hHist (body v)).1 (h v)
        · intro h v
          exact (satWCore_equiv hHist (body v)).2 (h v)
    | .event a =>
        constructor
        · intro h
          have hmem :=
            worldAtNat_mem_history (sh := sh) (M := M) hHist (i := i) (hi := hi)
          have heq :
              (sh.worldAtNat i hi).2.1 =
                MaybeEvent.some ⟨a.sym, a.args⟩ := by
            simpa [SatWCore, worldAtNat_event] using h
          have hmem' :
              ((sh.worldAtNat i hi).1,
                  MaybeEvent.some ⟨a.sym, a.args⟩,
                  (sh.worldAtNat i hi).2.2) ∈ M.history.val := by
            have :
                ((sh.worldAtNat i hi).1,
                  (sh.worldAtNat i hi).2.1,
                  (sh.worldAtNat i hi).2.2) ∈ M.history.val := by
              simpa using hmem
            simpa [heq] using this
          have hgoal :
              (sh.worldAtNat i hi).2.1 =
                  MaybeEvent.some ⟨a.sym, a.args⟩ ∧
                ((sh.worldAtNat i hi).1,
                    MaybeEvent.some ⟨a.sym, a.args⟩,
                    (sh.worldAtNat i hi).2.2) ∈ M.history.val :=
            ⟨heq, hmem'⟩
          simpa [Sat, worldAtNat_event] using hgoal
        · intro h
          obtain ⟨heq, _⟩ :=
            (by
              simpa [Sat, worldAtNat_event] using h :
                (sh.worldAtNat i hi).2.1 =
                    MaybeEvent.some ⟨a.sym, a.args⟩ ∧
                  ((sh.worldAtNat i hi).1,
                      MaybeEvent.some ⟨a.sym, a.args⟩,
                      (sh.worldAtNat i hi).2.2) ∈ M.history.val)
          simpa [SatWCore, worldAtNat_event] using heq
    | .predicate p => simp [SatWCore, Sat, worldAtNat_place]
    | .past φ =>
        constructor
        · intro h
          have h' :
              ∃ j : Fin i,
                sh.time i (j : Nat) = true ∧
                sh.place (j : Nat) = sh.place i ∧
                SatWCore sh M (j : Nat) (Nat.lt_trans j.is_lt hi) φ := by
            simpa [SatWCore] using h
          rcases h' with ⟨j, hj_time, hj_place, hj_sat⟩
          have hSat :
              ∃ t ∈ (worldAtNat sh i hi).2.2,
                World.place t = sh.place i ∧
                  Sat M (World.place t) (World.event t) (World.time t) φ := by
            refine ⟨sh.worldAtNat j (Nat.lt_trans j.is_lt hi),
              (mem_worldAt_time_nat (sh := sh) (hi := hi)).2 ⟨j, hj_time, rfl⟩,
              ?_, ?_⟩
            · simpa [worldAtNat_place] using hj_place
            · exact (satWCore_equiv hHist φ).1 hj_sat
          simpa [Sat, worldAtNat_place, worldAtNat_time] using hSat
        · intro h
          have h' :
              ∃ t ∈ (worldAtNat sh i hi).2.2,
                World.place t = sh.place i ∧
                  Sat M (World.place t) (World.event t) (World.time t) φ := by
            simpa [Sat, worldAtNat_place, worldAtNat_time] using h
          rcases h' with ⟨t, ht_mem, ht_place, ht_sat⟩
          obtain ⟨j, hj_time, hj_eq⟩ :=
            (mem_worldAt_time_nat (sh := sh) (hi := hi) (t := t)).1 ht_mem
          have hGoal :
              ∃ j : Fin i,
                sh.time i (j : Nat) = true ∧
                sh.place (j : Nat) = sh.place i ∧
                SatWCore sh M (j : Nat) (Nat.lt_trans j.is_lt hi) φ := by
            refine ⟨j, hj_time, ?_, ?_⟩
            · have hplace_j_to_t :
                  sh.place j = t.place := by
                simpa [worldAtNat_place] using
                  congrArg World.place hj_eq.symm
              have hplace_j : sh.place j = sh.place i :=
                hplace_j_to_t.trans ht_place
              simpa [worldAtNat_place] using hplace_j
            · have hSat' :
                Sat M (sh.worldAtNat j (Nat.lt_trans j.is_lt hi)).1
                  (sh.worldAtNat j (Nat.lt_trans j.is_lt hi)).2.1
                  (sh.worldAtNat j (Nat.lt_trans j.is_lt hi)).2.2 φ := by
                simpa [hj_eq] using ht_sat
              exact (satWCore_equiv hHist φ).2 hSat'
          simpa [SatWCore] using hGoal
    | .atEnd φ =>
        have h :=
          satEGlobalCore_equiv hHist (p := sh.place i) φ
        simpa [SatWCore, Sat, worldAtNat_place, worldAtNat_time, hHist] using h
    | .diamond ls φ =>
        classical
        have hLocal :
            ∀ p' : P,
              SatELocalCore sh M i hi p' φ ↔
                Sat M p' † (PreHistory.mk (timeListAt sh i)) φ :=
          fun p' =>
            by
              have :=
                satELocalCore_equiv hHist
                  (i := i) (hi := hi) (p := p') φ
              simpa [worldAtNat_time] using this
        have checkEquiv :
            ∀ (ls : List S.Value) (acc : Set P),
              SatWCore.check sh M i hi φ ls acc ↔
                Sat.check M (PreHistory.mk (timeListAt sh i)) φ ls acc := by
          intro ls
          induction ls with
          | nil =>
              intro acc
              classical
              simp [SatWCore.check, Sat.Sat_check_nil, hLocal]
          | cons ℓ ls ihCheck =>
              intro acc
              classical
              simp [SatWCore.check, Sat.Sat_check_cons, ihCheck]
        have hCheck := checkEquiv ls Set.univ
        simpa [SatWCore, Sat, worldAtNat_place, worldAtNat_time, hLocal]
          using hCheck
    | .seq =>
        have :=
          seq_condition_world (sh := sh) (hi := hi) (p := sh.place i)
        simpa [SatWCore, Sat, worldAtNat_place, worldAtNat_time] using this
  termination_by depth φ
  decreasing_by
    all_goals (try (first
      | apply depth_forall_body
      | apply depth_imp_left
      | apply depth_imp_right
      | apply depth_past_body))

  theorem satELocalCore_equiv
      (hHist : M.history.val = sh.preHistory)
      {i : Nat} {hi : i < sh.nW} {p : P}
      (φ : Formula S) :
        SatELocalCore sh M i hi p φ ↔
          Sat M p † (sh.worldAtNat i hi).2.2 φ := by
    classical
    match φ with
    | .bot => simp [SatELocalCore, Sat]
    | .imp φ ψ =>
        simp only [SatELocalCore, Sat]
        constructor
        · intro h hφ
          exact (satELocalCore_equiv hHist ψ).1 (h ((satELocalCore_equiv hHist φ).2 hφ))
        · intro h hφ
          exact (satELocalCore_equiv hHist ψ).2 (h ((satELocalCore_equiv hHist φ).1 hφ))
    | .eq v w => simp [SatELocalCore, Sat]
    | .forall body =>
        simp only [SatELocalCore, Sat]
        constructor
        · intro h v
          exact (satELocalCore_equiv hHist (body v)).1 (h v)
        · intro h v
          exact (satELocalCore_equiv hHist (body v)).2 (h v)
    | .event _ => simp [SatELocalCore, Sat]
    | .predicate q => simp [SatELocalCore, Sat]
    | .past φ =>
        constructor
        · intro h
          have h' :
              ∃ j : Fin i,
                sh.time i (j : Nat) = true ∧
                sh.place (j : Nat) = p ∧
                SatWCore sh M (j : Nat) (Nat.lt_trans j.is_lt hi) φ := by
            simpa [SatELocalCore] using h
          rcases h' with ⟨j, hj_time, hj_place, hj_sat⟩
          have hSat :
              ∃ t ∈ (worldAtNat sh i hi).2.2,
                World.place t = p ∧
                  Sat M (World.place t) (World.event t) (World.time t) φ := by
            refine ⟨sh.worldAtNat j (Nat.lt_trans j.is_lt hi),
              (mem_worldAt_time_nat (sh := sh) (hi := hi)).2 ⟨j, hj_time, rfl⟩,
              ?_, ?_⟩
            · simpa [worldAtNat_place] using hj_place
            · exact (satWCore_equiv hHist (i := j) (hi := Nat.lt_trans j.is_lt hi) φ).1 hj_sat
          simpa [Sat, worldAtNat_place, worldAtNat_time] using hSat
        · intro h
          have h' :
              ∃ t ∈ (worldAtNat sh i hi).2.2,
                World.place t = p ∧
                  Sat M (World.place t) (World.event t) (World.time t) φ := by
            simpa [Sat, worldAtNat_place, worldAtNat_time] using h
          rcases h' with ⟨t, ht_mem, ht_place, ht_sat⟩
          obtain ⟨j, hj_time, hj_eq⟩ :=
            (mem_worldAt_time_nat (sh := sh) (hi := hi) (t := t)).1 ht_mem
          have hGoal :
              ∃ j : Fin i,
                sh.time i (j : Nat) = true ∧
                sh.place (j : Nat) = p ∧
                SatWCore sh M (j : Nat) (Nat.lt_trans j.is_lt hi) φ := by
            refine ⟨j, hj_time, ?_, ?_⟩
            · have hplace_j_to_t :
                  sh.place j = t.place := by
                simpa [worldAtNat_place] using
                  congrArg World.place hj_eq.symm
              have hplace_j : sh.place j = p :=
                hplace_j_to_t.trans ht_place
              simpa [worldAtNat_place] using hplace_j
            · have hSat' :
                Sat M (sh.worldAtNat j (Nat.lt_trans j.is_lt hi)).1
                  (sh.worldAtNat j (Nat.lt_trans j.is_lt hi)).2.1
                  (sh.worldAtNat j (Nat.lt_trans j.is_lt hi)).2.2 φ := by
                simpa [hj_eq] using ht_sat
              exact (satWCore_equiv hHist (i := j) (hi := Nat.lt_trans j.is_lt hi) φ).2 hSat'
          simpa [SatELocalCore] using hGoal
    | .atEnd φ =>
        have h :=
          satEGlobalCore_equiv hHist (p := p) φ
        simpa [SatELocalCore, Sat, hHist] using h
    | .diamond ls φ =>
        classical
        have checkEquiv :
            ∀ (ls : List S.Value) (acc : Set P),
              SatELocalCore.check sh M i hi φ ls acc ↔
                Sat.check M (sh.worldAtNat i hi).2.2 φ ls acc := by
          intro ls
          induction ls with
          | nil =>
              intro acc
              classical
              constructor
              · intro h
                have h' :
                    ∃ p' ∈ acc, SatELocalCore sh M i hi p' φ := by
                  simpa [SatELocalCore.check] using h
                rcases h' with ⟨p', hp_mem, hp_sat⟩
                have hSat : ∃ p' ∈ acc, Sat M p' † (sh.worldAtNat i hi).2.2 φ :=
                  ⟨p', hp_mem, (satELocalCore_equiv hHist φ).1 hp_sat⟩
                simpa [Sat.Sat_check_nil] using hSat
              · intro h
                have h' :
                    ∃ p' ∈ acc, Sat M p' † (sh.worldAtNat i hi).2.2 φ := by
                  simpa [Sat.Sat_check_nil] using h
                rcases h' with ⟨p', hp_mem, hp_sat⟩
                have hp_sat' := (satELocalCore_equiv hHist φ).2 hp_sat
                have : ∃ p' ∈ acc, SatELocalCore sh M i hi p' φ :=
                  ⟨p', hp_mem, hp_sat'⟩
                simpa [SatELocalCore.check] using this
          | cons ℓ ls ihList =>
              intro acc
              classical
              constructor
              · intro h
                have hCore :
                    ∀ O ∈ (M.learner ℓ).quorums,
                      SatELocalCore.check sh M i hi φ ls (acc ∩ O) := by
                  simpa [SatELocalCore.check] using h
                have hSat :
                    ∀ O ∈ (M.learner ℓ).quorums,
                      Sat.check M (sh.worldAtNat i hi).2.2 φ ls (acc ∩ O) :=
                  fun O hO => (ihList (acc ∩ O)).1 (hCore O hO)
                simpa [Sat.Sat_check_cons] using hSat
              · intro h
                have hSat :
                    ∀ O ∈ (M.learner ℓ).quorums,
                      Sat.check M (sh.worldAtNat i hi).2.2 φ ls (acc ∩ O) := by
                  simpa [Sat.Sat_check_cons] using h
                have hCore :
                    ∀ O ∈ (M.learner ℓ).quorums,
                      SatELocalCore.check sh M i hi φ ls (acc ∩ O) :=
                  fun O hO => (ihList (acc ∩ O)).2 (hSat O hO)
                simpa [SatELocalCore.check] using hCore
        have hCheck := checkEquiv ls Set.univ
        simpa [SatELocalCore, Sat, worldAtNat_place, worldAtNat_time] using hCheck
    | .seq =>
        have :=
          seq_condition_world (sh := sh) (hi := hi) (p := p)
        simpa [SatELocalCore, Sat, worldAtNat_place, worldAtNat_time] using this
  termination_by depth φ
  decreasing_by
    all_goals (try (first
      | apply depth_forall_body
      | apply depth_imp_left
      | apply depth_imp_right
      | apply depth_past_body))

  theorem satEGlobalCore_equiv
      (hHist : M.history.val = sh.preHistory)
      {p : P}
      (φ : Formula S) :
        SatEGlobalCore sh M p φ ↔
          Sat M p † sh.preHistory φ := by
    classical
    match φ with
    | .bot => simp [SatEGlobalCore, Sat]
    | .imp φ ψ =>
        simp only [SatEGlobalCore, Sat]
        constructor
        · intro h hφ
          exact (satEGlobalCore_equiv hHist ψ).1 (h ((satEGlobalCore_equiv hHist φ).2 hφ))
        · intro h hφ
          exact (satEGlobalCore_equiv hHist ψ).2 (h ((satEGlobalCore_equiv hHist φ).1 hφ))
    | .eq v w => simp [SatEGlobalCore, Sat]
    | .forall body =>
        simp only [SatEGlobalCore, Sat]
        constructor
        · intro h v
          exact (satEGlobalCore_equiv hHist (body v)).1 (h v)
        · intro h v
          exact (satEGlobalCore_equiv hHist (body v)).2 (h v)
    | .event _ => simp [SatEGlobalCore, Sat]
    | .predicate q => simp [SatEGlobalCore, Sat]
    | .past φ =>
        constructor
        · intro h
          have h' :
              ∃ (i : Nat) (hi : i < sh.nW),
                sh.place i = p ∧ SatWCore sh M i hi φ := by
            simpa [SatEGlobalCore] using h
          rcases h' with ⟨i, hiIdx, hplace, hSat⟩
          have hSat' :
              ∃ t ∈ sh.preHistory,
                World.place t = p ∧
                  Sat M (World.place t) (World.event t) (World.time t) φ := by
            have hSatW :=
              satWCore_equiv hHist (i := i) (hi := hiIdx) φ
            refine ⟨sh.worldAtNat i hiIdx,
              sh.worldAtNat_mem_preHistory (i := i),
              ?_, ?_⟩
            · simpa [worldAtNat_place] using hplace
            · exact hSatW.1 hSat
          simpa [Sat, hHist] using hSat'
        · intro h
          have h' :
              ∃ t ∈ sh.preHistory,
                World.place t = p ∧
                  Sat M (World.place t) (World.event t) (World.time t) φ := by
            simpa [Sat, hHist] using h
          rcases h' with ⟨t, ht_mem, ht_place, ht_sat⟩
          obtain ⟨iFin, hi_eq⟩ :=
            (mem_preHistory_iff (sh := sh) (t := t)).1
              (by simpa [hHist] using ht_mem)
          have hiProof : (iFin : Nat) < sh.nW := iFin.is_lt
          have hi_eq_nat : sh.worldAtNat (iFin : Nat) hiProof = t := by
            simpa [worldAt_eq_worldAtNat] using hi_eq
          have hSatW :=
            satWCore_equiv hHist (i := (iFin : Nat)) (hi := hiProof) φ
          have hGoal :
              ∃ (i : Nat) (hi : i < sh.nW),
                sh.place i = p ∧ SatWCore sh M i hi φ := by
            refine ⟨(iFin : Nat), hiProof, ?_, ?_⟩
            · have := congrArg World.place hi_eq_nat
              simpa [worldAtNat_place] using this.trans ht_place
            · have hSat' :
                Sat M (sh.worldAtNat (iFin : Nat) hiProof).1
                  (sh.worldAtNat (iFin : Nat) hiProof).2.1
                  (sh.worldAtNat (iFin : Nat) hiProof).2.2 φ := by
                simpa [hi_eq_nat] using ht_sat
              exact hSatW.2 hSat'
          simpa [SatEGlobalCore] using hGoal
    | .atEnd φ =>
        have h := satEGlobalCore_equiv hHist (p := p) φ
        simpa [SatEGlobalCore, Sat, hHist] using h
    | .diamond ls φ =>
        classical
        have checkEquiv :
            ∀ (ls : List S.Value) (acc : Set P),
              SatEGlobalCore.check sh M φ ls acc ↔
                Sat.check M sh.preHistory φ ls acc := by
          intro ls
          induction ls with
          | nil =>
              intro acc
              classical
              constructor
              · intro h
                have h' :
                    ∃ p' ∈ acc, SatEGlobalCore sh M p' φ := by
                  simpa [SatEGlobalCore.check] using h
                rcases h' with ⟨p', hp_mem, hp_sat⟩
                have hSat : ∃ p' ∈ acc, Sat M p' † sh.preHistory φ :=
                  ⟨p', hp_mem, (satEGlobalCore_equiv hHist φ).1 hp_sat⟩
                simpa [Sat.Sat_check_nil] using hSat
              · intro h
                have h' :
                    ∃ p' ∈ acc, Sat M p' † sh.preHistory φ := by
                  simpa [Sat.Sat_check_nil] using h
                rcases h' with ⟨p', hp_mem, hp_sat⟩
                have hp_sat' := (satEGlobalCore_equiv hHist φ).2 hp_sat
                have : ∃ p' ∈ acc, SatEGlobalCore sh M p' φ :=
                  ⟨p', hp_mem, hp_sat'⟩
                simpa [SatEGlobalCore.check] using this
          | cons ℓ ls ihList =>
              intro acc
              classical
              constructor
              · intro h
                have hCore :
                    ∀ O ∈ (M.learner ℓ).quorums,
                      SatEGlobalCore.check sh M φ ls (acc ∩ O) := by
                  simpa [SatEGlobalCore.check] using h
                have hSat :
                    ∀ O ∈ (M.learner ℓ).quorums,
                      Sat.check M sh.preHistory φ ls (acc ∩ O) :=
                  fun O hO => (ihList (acc ∩ O)).1 (hCore O hO)
                simpa [Sat.Sat_check_cons] using hSat
              · intro h
                have hSat :
                    ∀ O ∈ (M.learner ℓ).quorums,
                      Sat.check M sh.preHistory φ ls (acc ∩ O) := by
                  simpa [Sat.Sat_check_cons] using h
                have hCore :
                    ∀ O ∈ (M.learner ℓ).quorums,
                      SatEGlobalCore.check sh M φ ls (acc ∩ O) :=
                  fun O hO => (ihList (acc ∩ O)).2 (hSat O hO)
                simpa [SatEGlobalCore.check] using hCore
        have hCheck := checkEquiv ls Set.univ
        simpa [SatEGlobalCore, Sat, hHist] using hCheck
    | .seq =>
        have := seq_condition_global (sh := sh) (p := p)
        simpa [SatEGlobalCore, Sat, hHist] using this
  termination_by depth φ
  decreasing_by
    all_goals (try (first
      | apply depth_forall_body
      | apply depth_imp_left
      | apply depth_imp_right
      | apply depth_past_body))
end

lemma satW_equiv
    (hHist : M.history.val = sh.preHistory)
    {i : Nat} {hi : i < sh.nW} {φ : Formula S} :
    SatW sh M i hi φ ↔
      Sat M (sh.worldAtNat i hi).1
        (sh.worldAtNat i hi).2.1
        (sh.worldAtNat i hi).2.2 φ := by
  simpa [SatW] using satWCore_equiv hHist (i := i) (hi := hi) φ

lemma satELocal_equiv
    (hHist : M.history.val = sh.preHistory)
    {i : Nat} {hi : i < sh.nW} {p : P} {φ : Formula S} :
    SatELocal sh M i hi p φ ↔
      Sat M p † (sh.worldAtNat i hi).2.2 φ := by
  simpa [SatELocal] using satELocalCore_equiv hHist (i := i) (hi := hi)
    (p := p) φ

lemma satEGlobal_equiv
    (hHist : M.history.val = sh.preHistory)
    {p : P} {φ : Formula S} :
    SatEGlobal sh M p φ ↔
      Sat M p † sh.preHistory φ := by
  simpa [SatEGlobal] using
    satEGlobalCore_equiv hHist (p := p) φ

end Compatibility

end Semantics
end ModalDistribution.ModelCheck
