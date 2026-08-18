/- Registry / tooling library: everything in `EM` plus the two files that depend on
non-Mathlib packages (CA content-addressing registry, LeanArchitect blueprint).  Kept out of
`EM` so that the mathematics builds against Mathlib alone.
(`EM/Meta/Strategies.lean`, the DeclbuildMeta strategy/theory catalogue, is parked locally in
`tmp/parked/` since 2026-08-18: its dependency `declbuild-meta` is not public.) -/
import EM
import EM.Meta.Registry
import EM.Meta.Blueprint
