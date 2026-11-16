import Lake
open Lake DSL

-- Verso Blueprint の Lean v4.35.0-rc4 の系列（v4.35.0 の枝で toolchain が v4.35.0 になる直前のコミット）。
-- proofwidgets・plausible・Cli は SerrePositivity の manifest と同じ版。
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"7bd0c10f0b77d75ab81fe2a2005f6a6428983d27"
require SerrePositivity from "../.."

package KerodonBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]
  packagesDir := "../../.lake/packages"

@[default_target]
lean_lib KerodonBlueprint where
