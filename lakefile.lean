import Lake
open Lake DSL

package "ModalDistribution" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩, -- Enable mathlib standard linters (conditional)
    ⟨`weak.linter.unnecessarySimpa, true⟩, -- Warn about unnecessary use of simp
    ⟨`weak.linter.unreachableTactic, true⟩, -- Warn about unreachable tactics
  ]

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «ModalDistribution» where
  -- add any library configuration options here

/-- Run the style linter -/
@[lint_driver]
lean_exe «lint-style» where
  srcDir := "scripts"
  supportInterpreter := true
