import Lake
open Lake DSL

package pilotF where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

require pilotD from "../pilot-d"

@[default_target]
lean_lib PilotF where
  roots := #[`PilotF]
  globs := #[.andSubmodules `PilotF]

lean_lib AxiomCheck where
  roots := #[`AxiomCheck]
