import Lake
open Lake DSL

package pilotA where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib PilotA where
  globs := #[.submodules `PilotA]

lean_lib AxiomCheck where
  roots := #[`AxiomCheck]
