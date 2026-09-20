import ModalDistribution.Examples.ThyHBB4.Depth
import ModalDistribution.Examples.HBB
import ModalDistribution.Examples.ThyLive

/-!
# Shared capped HBB4 rules and the CM, SW, CW theories

These are the semantic axiom schemata of §3.3 of the revised HBB4 argument.
Natural rounds index event symbols; they are not members of the value sort.
`Legal` therefore quantifies over natural numbers in Lean, and `BaseProtocol` is a
model-dependent semantic theory rather than a `Set (Formula S)`. Every modal
subexpression uses the existing satisfaction relation. In particular the full,
restricted `ThyLive` is required, with no additional Knowledge instances.
-/

namespace ModalDistribution.Examples.ThyHBB4

open ModalDistribution.Logic ModalDistribution.Logic.Formula
open scoped Formula PreHistory

set_option autoImplicit false

variable {S : Signature}

/-- Round numbers are indices of symbols, with target/source/value arguments. -/
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

def vote (σ : ProtocolSignature S) (l s v : S.Value) (n : Nat) : Formula S :=
  ofEvent ⟨σ.voteSymb n, [l, s, v]⟩

def deliver (σ : ProtocolSignature S) (l v : S.Value) : Formula S :=
  ofEvent ⟨σ.deliverSymb, [l, v]⟩

def correlation (σ : ProtocolSignature S) (a b : S.Value) : Formula S :=
  ofPredicate ⟨σ.correlationSymb, [a, b]⟩

def live (σ : ProtocolSignature S) : Formula S := predicate0 σ.liveSymb

/-- A vote from an existentially quantified source. -/
def voteFromSomeSource (σ : ProtocolSignature S) (l v : S.Value) (n : Nat) : Formula S :=
  ∃ᶠ fun s => σ.vote l s v n

/-- A quorum of votes whose sources may differ between signers. -/
def voteCertificate (σ : ProtocolSignature S) (l v : S.Value) (n : Nat) : Formula S :=
  □ᶠ↓[[l]] (σ.voteFromSomeSource l v n)

/-- This certificate fixes one source for the entire quorum. -/
def fixedSourceCertificate (σ : ProtocolSignature S) (l s v : S.Value) (n : Nat) : Formula S :=
  □ᶠ↓[[l]] (σ.vote l s v n)

def echoCertificate (σ : ProtocolSignature S) (l v : S.Value) : Formula S :=
  □ᶠ↓[[l]] (σ.echo v)

end ProtocolSignature

variable {P : Type} [Nonempty P]

def Corr (M : Model S P) (σ : ProtocolSignature S)
    (w : World P S.EventType) (a b : S.Value) : Prop :=
  ⟪w⟫ ⊨[M] σ.correlation a b

/-- Legality uses correlation at the observing world, not at the vote event. -/
def Legal (M : Model S P) (σ : ProtocolSignature S)
    (w : World P S.EventType) (l v : S.Value) : Prop :=
  ∀ b u n, Corr M σ w b l → u ≠ v →
    (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.voteFromSomeSource b u n)) →
    ∃ c m, n < m ∧ Corr M σ w c l ∧
      (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.voteFromSomeSource c v m))

/-- The end-of-time world of the same participant. -/
def endWorld (M : Model S P) (w : World P S.EventType) : World P S.EventType :=
  ⟨w.place, †, M.history.val⟩

/-- Exact backward, cap, correlation, legality and forward schemata.
The structure fields are protocol rules, never correctness conclusions. -/
structure BaseProtocol (M : Model S P) (σ : ProtocolSignature S) : Prop where
  thyLive : M ⊨ᵀ ThyLive σ.liveSymb
  echoBackward : ∀ {w}, w.time ⪯ M.history.val → ∀ {v},
    (⟪w⟫ ⊨[M] σ.echo v) → (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v))
  voteZeroBackward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l s v},
    (⟪w⟫ ⊨[M] σ.vote l s v 0) →
    (l = s ∧ (⟪w⟫ ⊨[M] σ.echoCertificate l v)) ∨
      (⟪w⟫ ⊨[M] σ.voteCertificate s v (maxDepth M (Corr M σ) s))
  voteSuccBackward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l s v n},
    (⟪w⟫ ⊨[M] σ.vote l s v (n + 1)) →
      (⟪w⟫ ⊨[M] σ.fixedSourceCertificate l s v n)
  deliverBackward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l v},
    (⟪w⟫ ⊨[M] σ.deliver l v) →
      (⟪w⟫ ⊨[M] σ.voteCertificate l v (maxDepth M (Corr M σ) l + 1))
  echoNonEquivocation : ∀ {w}, w.time ⪯ M.history.val → ∀ {v u},
    (⟪w⟫ ⊨[M] σ.echo v) → (⟪w⟫ ⊨[M] ↓ᶠ (σ.echo u)) → v = u
  voteLegal : ∀ {w}, w.time ⪯ M.history.val → ∀ {l s v n},
    (⟪w⟫ ⊨[M] σ.vote l s v n) → Legal M σ w l v
  voteSource : ∀ {w}, w.time ⪯ M.history.val → ∀ {l s v n},
    (⟪w⟫ ⊨[M] σ.vote l s v n) → l = s ∨ Corr M σ w l s
  voteCap : ∀ {w}, w.time ⪯ M.history.val → ∀ {l s v n},
    (⟪w⟫ ⊨[M] σ.vote l s v n) → n ≤ maxDepth M (Corr M σ) l + 1
  correlationSeq : ∀ {w}, w.time ⪯ M.history.val → ∀ {a b},
    Corr M σ w a b → (⟪w⟫ ⊨[M] ♢ᶠ[[a, b]] Formula.seq)
  correlationSymm : ∀ {w}, w.time ⪯ M.history.val → ∀ {a b},
    Corr M σ w a b → Corr M σ w b a
  correlationTrans : ∀ {w}, w.time ⪯ M.history.val → ∀ {a b c},
    Corr M σ w a b → Corr M σ w b c → Corr M σ w a c
  correlationPast : ∀ {w}, w.time ⪯ M.history.val → ∀ {a b},
    Corr M σ w a b → ∀ {u}, u ∈ w.time → u.place = w.place → Corr M σ u a b
  echoForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {v},
    (⟪w⟫ ⊨[M] σ.live) → (⟪w⟫ ⊨[M] ♢ᶠ↓[[]] (σ.propose v)) →
    ∃ u, (⟪w⟫ ⊨[M] ↕ᶠ (σ.echo u))
  voteZeroEchoForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l v},
    (⟪w⟫ ⊨[M] σ.live) → Legal M σ (endWorld M w) l v →
    (⟪w⟫ ⊨[M] σ.echoCertificate l v) → (⟪w⟫ ⊨[M] ↕ᶠ (σ.vote l l v 0))
  voteZeroTransferForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l s v},
    (⟪w⟫ ⊨[M] σ.live) → Legal M σ (endWorld M w) l v →
    Corr M σ (endWorld M w) l s →
    (⟪w⟫ ⊨[M] σ.voteCertificate s v (maxDepth M (Corr M σ) s)) →
    (⟪w⟫ ⊨[M] ↕ᶠ (σ.vote l s v 0))
  voteSuccForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l s v n},
    n + 1 ≤ maxDepth M (Corr M σ) l + 1 →
    (⟪w⟫ ⊨[M] σ.live) → Legal M σ (endWorld M w) l v →
    (l = s ∨ Corr M σ (endWorld M w) l s) →
    (⟪w⟫ ⊨[M] σ.fixedSourceCertificate l s v n) →
    (⟪w⟫ ⊨[M] ↕ᶠ (σ.vote l s v (n + 1)))
  deliverForward : ∀ {w}, w.time ⪯ M.history.val → ∀ {l v},
    (⟪w⟫ ⊨[M] σ.live) →
    (⟪w⟫ ⊨[M] σ.voteCertificate l v (maxDepth M (Corr M σ) l + 1)) →
    (⟪w⟫ ⊨[M] ↕ᶠ (σ.deliver l v))

/-- Correlation at a world holds at every causal predecessor. -/
def CausalMonotonicity (M : Model S P) (σ : ProtocolSignature S) : Prop :=
  ∀ {w}, w.time ⪯ M.history.val → ∀ {a b},
    Corr M σ w a b → ∀ {u}, u ∈ w.time → Corr M σ u a b

/-- Only the later event of a positive-round, same-signer switch is constrained. -/
def SwitchCoherence (M : Model S P) (σ : ProtocolSignature S) : Prop :=
  ∀ {w}, w.time ⪯ M.history.val → ∀ {f g : World P S.EventType}
    {b s u c t v : S.Value} {n : Nat},
    f ≪ g → g ≪ w → f.place = g.place → 1 ≤ n → u ≠ v →
    Corr M σ w b c →
    (⟪f⟫ ⊨[M] σ.vote b s u n) → (⟪g⟫ ⊨[M] σ.vote c t v n) →
    ∀ a, Corr M σ w c a → Corr M σ g c a

/-- The two predecessor votes need only be strictly comparable; their signers
need not coincide. Each predecessor lies in its own parent's past. -/
def ComparisonWitness (M : Model S P) (σ : ProtocolSignature S) : Prop :=
  ∀ {w}, w.time ⪯ M.history.val → ∀ {E F : World P S.EventType}
    {b s u c t v : S.Value} {k : Nat},
    E ≪ w → F ≪ w → 2 ≤ k → u ≠ v → Corr M σ w b c →
    (⟪E⟫ ⊨[M] σ.vote b s u k) → (⟪F⟫ ⊨[M] σ.vote c t v k) →
    ∃ f g, f ≪ E ∧ g ≪ F ∧
      (⟪f⟫ ⊨[M] σ.vote b s u (k - 1)) ∧
      (⟪g⟫ ⊨[M] σ.vote c t v (k - 1)) ∧
      ((f ≪ g ∧ ∀ a, Corr M σ w b a → Corr M σ g c a) ∨
       (g ≪ f ∧ ∀ a, Corr M σ w b a → Corr M σ f b a))

/-- HBB4 with causal monotonicity. -/
structure ProtocolCM (M : Model S P) (σ : ProtocolSignature S)
    : Prop extends BaseProtocol M σ where
  causalMonotone : CausalMonotonicity M σ

structure ProtocolSW (M : Model S P) (σ : ProtocolSignature S)
    : Prop extends BaseProtocol M σ where
  switchCoherence : SwitchCoherence M σ

structure ProtocolCW (M : Model S P) (σ : ProtocolSignature S)
    : Prop extends BaseProtocol M σ where
  comparisonWitness : ComparisonWitness M σ

instance {M : Model S P} {σ : ProtocolSignature S} :
    Coe (ProtocolCM M σ) (BaseProtocol M σ) := ⟨ProtocolCM.toBaseProtocol⟩

instance {M : Model S P} {σ : ProtocolSignature S} :
    Coe (ProtocolSW M σ) (BaseProtocol M σ) := ⟨ProtocolSW.toBaseProtocol⟩

instance {M : Model S P} {σ : ProtocolSignature S} :
    Coe (ProtocolCW M σ) (BaseProtocol M σ) := ⟨ProtocolCW.toBaseProtocol⟩

end ModalDistribution.Examples.ThyHBB4
