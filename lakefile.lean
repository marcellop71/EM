import Lake
open Lake DSL

package em where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩
  ]

require LeanArchitect from git
  "https://github.com/hanwenzhu/LeanArchitect.git" @ "main"

/- CA (content-addressing registry) is pinned to its git tag `v4.33.0`
   (https://github.com/marcellop71/CA; toolchain, batteries and Cli at v4.33.0).
   declbuild-meta is still a sibling-checkout path require:
     ../../proofinity/declbuild-meta  https://github.com/proofinity-it/declbuild-meta
                                      @ 63734c0 + an uncommitted v4.33.0 bump
   LeanArchitect has no v4.33.0 tag, so it is pinned to main; re-pin to a tag when one
   appears.  All three declare lean-toolchain v4.33.0.
   NOTE: EM's mathematics (`lean_lib EM` minus `EM/Meta/{Registry,Strategies,Blueprint}`)
   depends only on Mathlib; those three files carry the registry tooling. -/
require ca from git
  "https://github.com/marcellop71/CA" @ "v4.33.0"

-- CA → redis-lean requires these two over SSH (`git@github.com:…`), which an anonymous
-- clone cannot fetch; requiring them here over https makes the root manifest's entries
-- take precedence.
require zlogLean from git
  "https://github.com/marcellop71/zlog-lean" @ "v4.33.0"
require arrowLean from git
  "https://github.com/marcellop71/arrow-lean" @ "v4.33.0"

require declbuildMeta from "../../proofinity/declbuild-meta"

-- `require mathlib` LAST: Mathlib's transitive pins (batteries, Cli, …) must take
-- precedence, otherwise `lake exe cache get` computes wrong hashes and the Mathlib
-- olean cache cannot be fetched.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

@[default_target]
lean_lib EM where

/-- Registry / tooling (needs CA, declbuild-meta, LeanArchitect); `EM` itself needs only Mathlib. -/
@[default_target]
lean_lib EMRegistry where
