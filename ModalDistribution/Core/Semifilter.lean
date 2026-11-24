import ModalDistribution.Core.Set
import ModalDistribution.Core.History

open Set
open History

/-!
# Semifilter Structures

This file introduces semifilters as the set-theoretic foundation for quorums.
Semifilters capture nonempty, up-closed families of pairwise intersecting
quorums on a set of participants.

## Main definitions

* `Semifilter.Intersects` (`≬`): quorum-intersection predicate.
* `Semifilter`: structure of nonempty up-closed pairwise-intersecting families of quorums.

## References

* Paper: Definition 3.3.2 (semifilters).
-/

universe u

namespace Semifilter

variable {P : Type u}

/-- Paper: Notation 3.3.1 (≬). Quorum intersection: `O ≬ O'` when two quorums intersect (their
intersection is nonempty). -/
@[simp] def Intersects (O O' : Set P) : Prop := (O ∩ O').Nonempty

scoped infix:50 " ≬ " => Semifilter.Intersects

end Semifilter

open scoped Semifilter

/-- Paper: Definition 3.3.2 (semifilters). A semifilter is a nonempty up-closed
family of pairwise intersecting quorums over a participant set `P`. -/
structure Semifilter (P : Type u) where
  /-- Carrier set of quorums. -/
  quorums : Set (Set P)
  /-- Property 1: the family of quorums is nonempty. -/
  nonempty : quorums.Nonempty
  /-- Property 2: the family is up-closed under supersets inside `P`. -/
  upward_closed : ∀ ⦃O O' : Set P⦄, O ∈ quorums → O ⊆ O' → O' ∈ quorums
  /-- Property 3: quorums pairwise intersect. -/
  pairwise_inter : ∀ ⦃O O' : Set P⦄, O ∈ quorums → O' ∈ quorums → O ≬ O'

namespace Semifilter

variable {P : Type u}

/-- Every quorum of a semifilter is nonempty: it intersects itself. -/
theorem quorum_nonempty {L : Semifilter P} {O : Set P}
    (hO : O ∈ L.quorums) :
    O.Nonempty :=
  let ⟨p, hp, _⟩ := L.pairwise_inter hO hO
  ⟨p, hp⟩

end Semifilter
