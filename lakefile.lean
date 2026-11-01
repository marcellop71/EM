import Lake
open Lake DSL

package em where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩
  ]

require LeanArchitect from git
  "https://github.com/hanwenzhu/LeanArchitect.git" @ "v4.35.0"

/- CA (content-addressing registry) is pinned to its release tag `v0.4.0`
   (https://github.com/proofinity-it/CA; toolchain and batteries at v4.35.0; type_hash
   scheme 2). The `ca` library is pure Lean and requires only Batteries.
   LeanArchitect is pinned to its `v4.35.0` tag.
   NOTE: EM's mathematics (`lean_lib EM`) depends only on Mathlib; the registry tooling
   (`EM/Meta/{Registry,Blueprint}.lean`) is the separate `lean_lib EMRegistry`. -/
require ca from git
  "https://github.com/proofinity-it/CA" @ "v0.4.0"

-- `require mathlib` LAST: Mathlib's transitive pins (batteries, Cli, …) must take
-- precedence, otherwise `lake exe cache get` computes wrong hashes and the Mathlib
-- olean cache cannot be fetched.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib EM where

/-- Registry / tooling (needs CA and LeanArchitect); `EM` itself needs only Mathlib. -/
@[default_target]
lean_lib EMRegistry where
