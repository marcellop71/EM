import Lake
open Lake DSL

package em where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]

  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc1"

require LeanArchitect from git
  "https://github.com/hanwenzhu/LeanArchitect.git" @ "v4.29.0-rc1"

require ca from "../CA"

@[default_target]
lean_lib EM where

lean_exe genRegistry where
  root := `scripts.GenRegistry
