import ModalDistribution.Examples.ThyHBB4.Depth
import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyLive

/-!
# Shared capped HBB4 rules and the CM and VM theories

These are the semantic axiom schemata of §3.3 of the revised HBB4 argument.
Natural rounds index event symbols; they are not members of the value sort.
`UncontestedOrDelivered` therefore quantifies over natural numbers in Lean, and `BaseProtocol` is a
model-dependent semantic theory rather than a `Set (Formula S)`. Every modal
subexpression uses the existing satisfaction relation. In particular the full,
restricted `ThyLive` is required, with no additional Knowledge instances.
-/

namespace ModalDistribution.Examples.ThyHBB4

open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

/-- Round numbers are indices of symbols, with target/value arguments. -/
structure ProtocolSignature (S : Signature) where
  liveSymb : S.PredSymb
  correlationSymb : S.PredSymb
  proposeSymb : S.EventSymb
  echoSymb : S.EventSymb
  voteSymb : Nat → S.EventSymb
  deliverSymb : S.EventSymb

namespace ProtocolSignature

def propose (σ : ProtocolSignature S) (v : S.Value) : Formula S :=
  ofEvent ⟨σ.proposeSymb, [v]⟩

def echo (σ : ProtocolSignature S) (v : S.Value) : Formula S :=
  ofEvent ⟨σ.echoSymb, [v]⟩

/-- A vote names its target learner, its value and its round; it no longer
records a source learner. -/
def vote (σ : ProtocolSignature S) (l v : S.Value) (n : Nat) : Formula S :=
  ofEvent ⟨σ.voteSymb n, [l, v]⟩

def deliver (σ : ProtocolSignature S) (l v : S.Value) : Formula S :=
  ofEvent ⟨σ.deliverSymb, [l, v]⟩

def correlation (σ : ProtocolSignature S) (a b : S.Value) : Formula S :=
  ofPredicate ⟨σ.correlationSymb, [a, b]⟩

def live (σ : ProtocolSignature S) : Formula S := predicate0 σ.liveSymb

/-- A quorum of rank-`n` votes for `l` with value `v`. -/
def voteCertificate (σ : ProtocolSignature S) (l v : S.Value) (n : Nat) : Formula S :=
  □ᶠ↓[[l]] (σ.vote l v n)

def echoCertificate (σ : ProtocolSignature S) (l v : S.Value) : Formula S :=
  □ᶠ↓[[l]] (σ.echo v)

end ProtocolSignature

variable {P : Type} [Nonempty P]

/-- Revised HBB4 note §3.3, (1), replaced. The forward-rule side condition on a
value `v` for learner `l`, judged at a world `w` (in the rules, the voter's
final world): either no vote for a value other than `v` has been observed for
any learner correlated with `l`, or a delivery of `v` has been observed for some
learner `c` correlated with `l` whose decision rank `maxDepth c` exceeds the
rank of every such conflicting vote. It occurs only as a premise of the forward
rules, and is exactly what the liveness proofs establish (vacuously under a
unique proposal; from the source delivery, with the rank bound from
`conflicting_rank_lt`, for Liveness 2). The rank bound is what lets a
participant discharge the obligation while respecting `voteNonEquivocation`: the delivery
certificate contains a rank-`maxDepth c` vote for `v`, which outranks any
conflicting same-round vote it may itself have cast. -/
def UncontestedOrDelivered (M : Model S P) (σ : ProtocolSignature S)
    (w : World P S.EventType) (l v : S.Value) : Prop :=
  ∀ b u n, Correlated M σ.correlationSymb w b l → u ≠ v →
    (ObservedAt M w (σ.vote b u n)) →
    ∃ c, n < maxDepth M (Correlated M σ.correlationSymb) c ∧
      Correlated M σ.correlationSymb w c l ∧ (ObservedAt M w (σ.deliver c v))

/-- Exact backward, correlation, non-equivocation and forward schemata. There is
no round cap on the backward side: none of the proofs need one (`voteSuccForward`
carries the only bound, as a restriction on the obligation). The former Vote
source rule, (8), is absorbed into `voteZeroBackward` now that votes carry no
source.
Votes are `vote l v n` (target, value, round) with no source learner.
Each rule is quantified over possible worlds (`w.time ⪯ M.history.val`).
`maxDepth` is a maximum over the completed model; correlation and non-equivocation are
local to their displayed world. The forward side condition
`UncontestedOrDelivered` uses the same participant's final world. Natural ranks in these schemata are Lean quantifiers, outside the
formula value sort. The structure fields are protocol rules, never correctness conclusions. -/
structure BaseProtocol (M : Model S P) (σ : ProtocolSignature S) : Prop where
  thyLive : M ⊨ᵀ ThyLive σ.liveSymb
  /-- Revised HBB4 note §3.3, (2), Echo?. -/
  echoBackward : ∀ {w}, w.time ⪯ M.history.val → ∀ {v},
    (⟪w⟫ ⊨[M] σ.echo v) → (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v))
  /-- Revised HBB4 note §3.3, (3), Vote0?. A round-zero vote is justified either
  by an echo certificate for its target, or by a single observed vote, at *any*
  rank, for some learner `s` correlated with the target at the voting world.
  Votes carry no source, so `s` is existential here. The rank of the observed
  vote is unconstrained: only the forward rule `voteZeroTransferForward` refers
  to the source's decision rank. -/
  voteZeroBackward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l v},
    (⟪w⟫ ⊨[M] σ.vote l v 0) →
    (⟪w⟫ ⊨[M] σ.echoCertificate l v) ∨
      ∃ s m, Correlated M σ.correlationSymb w l s ∧
        (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.vote s v m))
  /-- Revised HBB4 note §3.3, (4), VoteN? (successor indexing). -/
  voteSuccBackward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l v n},
    (⟪w⟫ ⊨[M] σ.vote l v (n + 1)) →
      (⟪w⟫ ⊨[M] σ.voteCertificate l v n)
  /-- Revised HBB4 note §3.3, (5), Deliver?. -/
  deliverBackward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l v},
    (⟪w⟫ ⊨[M] σ.deliver l v) →
      (⟪w⟫ ⊨[M] σ.voteCertificate l v (maxDepth M (Correlated M σ.correlationSymb) l))
  /-- Revised HBB4 note §3.3, (6), EchoNE. -/
  echoNonEquivocation : ∀ {w}, w.time ⪯ M.history.val → ∀ {v u},
    (⟪w⟫ ⊨[M] σ.echo v) → (⟪w⟫ ⊨[M] ↓ᶠ (σ.echo u)) → v = u
  /-- Revised HBB4 note §3.3, (7), replaced by vote non-equivocation: you cannot
  vote for a different value (for a correlated learner, at the same round)
  unless you have seen a deeper vote for the value you are now voting for (for
  a correlated learner). -/
  voteNonEquivocation : ∀ {w}, w.time ⪯ M.history.val → ∀ {l b v u n},
    (⟪w⟫ ⊨[M] σ.vote l v n) → (⟪w⟫ ⊨[M] ↓ᶠ (σ.vote b u n)) →
    Correlated M σ.correlationSymb w l b → u ≠ v →
    ∃ c m, n < m ∧ Correlated M σ.correlationSymb w l c ∧
      (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.vote c v m))
  /-- Revised HBB4 note §3.3, (9), correlation sequentiality. -/
  correlationSeq : ∀ {w}, w.time ⪯ M.history.val → ∀ {a b},
    Correlated M σ.correlationSymb w a b → (⟪w⟫ ⊨[M] ♢ᶠ[[a, b]] Formula.seq)
  /-- Revised HBB4 note §3.3, (10), correlation symmetry. -/
  correlationSymm : ∀ {w}, w.time ⪯ M.history.val → ∀ {a b},
    Correlated M σ.correlationSymb w a b → Correlated M σ.correlationSymb w b a
  /-- Revised HBB4 note §3.3, (11), correlation transitivity. -/
  correlationTrans : ∀ {w}, w.time ⪯ M.history.val → ∀ {a b c},
    Correlated M σ.correlationSymb w a b → Correlated M σ.correlationSymb w b c → Correlated M σ.correlationSymb w a c
  /-- Manuscript Figure 11: correlation persists along the same participant’s past. -/
  correlationPast : ∀ {w}, w.time ⪯ M.history.val → ∀ {a b},
    Correlated M σ.correlationSymb w a b → ∀ {u}, u ≪ w → u.place = w.place → Correlated M σ.correlationSymb u a b
  /-- Revised HBB4 note §3.3, (12), Echo!. -/
  echoForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {v},
    (⟪w⟫ ⊨[M] σ.live) → (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v)) →
    ∃ u, (⟪w⟫ ⊨[M] ↕ᶠ (σ.echo u))
  /-- Revised HBB4 note §3.3, (13), Vote0! from echoes. -/
  voteZeroEchoForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l v},
    (⟪w⟫ ⊨[M] σ.live) → UncontestedOrDelivered M σ (finalWorld M w.place) l v →
    (⟪w⟫ ⊨[M] σ.echoCertificate l v) → (⟪w⟫ ⊨[M] ↕ᶠ (σ.vote l v 0))
  /-- Revised HBB4 note §3.3, (14), Vote0! from transfer. The premise is a
  single observed vote at the source's decision rank, a `KnowledgeBody.known`
  body. -/
  voteZeroTransferForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l s v},
    (⟪w⟫ ⊨[M] σ.live) → UncontestedOrDelivered M σ (finalWorld M w.place) l v →
    Correlated M σ.correlationSymb (finalWorld M w.place) l s →
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.vote s v (maxDepth M (Correlated M σ.correlationSymb) s))) →
    (⟪w⟫ ⊨[M] ↕ᶠ (σ.vote l v 0))
  /-- Revised HBB4 note §3.3, (15), VoteN! (successor indexing). -/
  voteSuccForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l v n},
    n < maxDepth M (Correlated M σ.correlationSymb) l →
    (⟪w⟫ ⊨[M] σ.live) → UncontestedOrDelivered M σ (finalWorld M w.place) l v →
    (⟪w⟫ ⊨[M] σ.voteCertificate l v n) →
    (⟪w⟫ ⊨[M] ↕ᶠ (σ.vote l v (n + 1)))
  /-- Revised HBB4 note §3.3, (16), Deliver!. -/
  deliverForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l v},
    (⟪w⟫ ⊨[M] σ.live) →
    (⟪w⟫ ⊨[M] σ.voteCertificate l v (maxDepth M (Correlated M σ.correlationSymb) l)) →
    (⟪w⟫ ⊨[M] ↕ᶠ (σ.deliver l v))

/-- Correlation at a world holds at every causal predecessor. -/
def CausalMonotonicity (M : Model S P) (σ : ProtocolSignature S) : Prop :=
  ∀ {w}, w.time ⪯ M.history.val → ∀ {a b},
    Correlated M σ.correlationSymb w a b → ∀ {u}, u ≪ w → Correlated M σ.correlationSymb u a b

/-- Vote monotonicity: the target of an observed vote keeps, at the vote event,
every correlation it has at the observer — for every round-zero vote, and for
the later vote of a same-signer, same-round switch between correlated learners.
These are the two instances of causal monotonicity the correctness proofs use
(the second is a switch-coherence condition); each constrains only vote events
and only the
target's row. -/
def VoteMonotonicity (M : Model S P) (σ : ProtocolSignature S) : Prop :=
  ∀ {w}, w.time ⪯ M.history.val → ∀ {g : World P S.EventType} {c v : S.Value} {n : Nat},
    g ≪ w → (⟪g⟫ ⊨[M] σ.vote c v n) →
    (n = 0 ∨ ∃ b u, u ≠ v ∧ Correlated M σ.correlationSymb w b c ∧
      (⟪g⟫ ⊨[M] ↓ᶠ (σ.vote b u n))) →
    ∀ a, Correlated M σ.correlationSymb w c a → Correlated M σ.correlationSymb g c a

/-- HBB4 with causal monotonicity. -/
structure ProtocolCM (M : Model S P) (σ : ProtocolSignature S)
    : Prop extends BaseProtocol M σ where
  causalMonotone : CausalMonotonicity M σ

/-- HBB4 with vote monotonicity. -/
structure ProtocolVM (M : Model S P) (σ : ProtocolSignature S)
    : Prop extends BaseProtocol M σ where
  voteMonotone : VoteMonotonicity M σ

instance {M : Model S P} {σ : ProtocolSignature S} :
    Coe (ProtocolCM M σ) (BaseProtocol M σ) := ⟨ProtocolCM.toBaseProtocol⟩

instance {M : Model S P} {σ : ProtocolSignature S} :
    Coe (ProtocolVM M σ) (BaseProtocol M σ) := ⟨ProtocolVM.toBaseProtocol⟩

end ModalDistribution.Examples.ThyHBB4
