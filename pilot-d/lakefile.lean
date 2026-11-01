import Lake
open Lake DSL

package pilotD where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.mathlibStandardSet, true⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib PilotD where
  globs := #[.submodules `PilotD]

lean_lib AxiomCheck where
  roots := #[`AxiomCheck]

lean_lib Lint where
  roots := #[`Lint]
