/-!
# Equivalences

An equivalence between two types is a pair of mutually inverse functions.

## Main definitions

* `Equiv α β`, written `α ≃ β`.
-/

universe u v

/-- An equivalence `α ≃ β` is a function `α → β` together with an inverse. -/
structure Equiv (α : Sort u) (β : Sort v) where
  /-- The forward function. -/
  toFun : α → β
  /-- The inverse function. -/
  invFun : β → α
  /-- `invFun` undoes `toFun`. -/
  left_inv : Function.LeftInverse invFun toFun
  /-- `invFun` is undone by `toFun`. -/
  right_inv : Function.RightInverse invFun toFun

@[inherit_doc Equiv]
infixl:25 " ≃ " => Equiv
