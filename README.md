# Mullin's Conjecture and the Euclid step — a Lean 4 formalization

## The Euclid–Mullin Sequence

Euclid's proposition IX.20 of the Elements shows that for any finite set of primes, each prime
factor of their product plus one is outside the set: to grow your set of primes, you can pick any
of them.
The [Euclid–Mullin sequence](https://oeis.org/A000945) (Mullin, 1963) makes a definite choice: always take the *smallest* prime factor.

```
a(0) = 2,    a(n+1) = smallest prime factor of (a(0) · a(1) · ··· · a(n) + 1)
```

The first terms are 2, 3, 7, 43, 13, 53, 5, 6221671, 38709183810571, 139, 2801, 11, 17, ... — the sequence behaves almost randomly, with small primes appearing out of order and enormous primes appearing early. As of 2025, 51 terms are known; the smallest prime not yet observed is 41.

**Mullin's Conjecture:** Every prime number eventually appears in this sequence.

## Papers

Two documents, both with clickable links to the Lean source for every formally verified result:

- **Short paper** — [download PDF](https://github.com/marcellop71/EM/releases/latest) (10 pages, sources in
  [`paper/short/`](paper/short/)): the mathematics, with proof sketches.  The residue-walk
  reformulations of MC (all equivalent to MC), the composite floor (growth constant, MC ⇒ (C∞),
  Sylvester towers, the invariant ρ), the population laws (head domination, the bag-conditioned
  1/q law, almost-all factor-tree hitting, Karamata and Mertens in progressions), and min versus
  max (Cox–van der Poorten's omission of 5, no congruence invariant under lpf).
- **Technical report** — [download PDF](https://github.com/marcellop71/EM/releases/latest) (sources in [`paper/`](paper/)):
  everything the formalization does — the above plus the variants, the spectral and variance
  routes, the obstruction calculus, the function-field analogue (placeholders marked), the
  complete catalogue of documented dead ends, and the methodology.  Nothing in the short paper
  depends on it.

The compiled PDFs are attached to each [release](https://github.com/marcellop71/EM/releases/latest)
(`EM-short-*.pdf` and `EM-paper-*.pdf`) rather than tracked in the repository, so that clones stay
small.  To build them yourself, run two passes of `lualatex main.tex` in the respective directory;
they share `paper/preamble.tex`.

## Mathlib Candidates

Several general-purpose results developed in this formalization fill genuine gaps in Mathlib. See [`zulip_mathlib_candidates.md`](zulip_mathlib_candidates.md) for a curated list.

## Content-Addressed Registry

The project includes a machine-readable registry of all key results and open hypotheses, using the [CA](https://github.com/marcellop71/CA) (Content Addressing for Lean 4) package.

**How it works:** The CA package provides `@[publish]` and `@[open_point]` attributes that tag declarations for inclusion in a decentralized formal math registry. Each tagged declaration gets a content address — a deterministic hash of its canonicalized type expression (universe-renamed, metadata-stripped). The `#ca_registry` command at the end of [`EM/Meta/Registry.lean`](EM/Meta/Registry.lean) generates the registry files automatically during `lake build`.

- [`EM/Meta/Registry.lean`](EM/Meta/Registry.lean) — `@[open_point]` annotations (unproved hypotheses) and `@[publish]` annotations (proved theorems)
- [`registry/declarations.json`](registry/declarations.json) — entries with name, module, kind, status, content hash, pretty-printed type, and dependency list
- [`registry/meta.json`](registry/meta.json) — project summary (open points, proved, conditional)

The registry is regenerated automatically by `lake build`.

## Building

Requires the pinned Lean toolchain in [`lean-toolchain`](lean-toolchain).  All dependencies are
git requires fetched by `lake`: Mathlib `v4.33.0`, [CA](https://github.com/marcellop71/CA)
`v4.33.0` (the content-addressing registry) and LeanArchitect (pinned to `main`).  Then
`lake build` at the repo root.  Two libraries are built: `EM` (the mathematics; depends only on
Mathlib) and `EMRegistry` (root `EMRegistry.lean`: `EM` plus the registry tooling
`EM/Meta/{Registry,Blueprint}.lean`, which need CA and LeanArchitect).

Verified set: no `sorry`, no user axioms, no `native_decide`; run
`python3 tools/check_axioms.py` after `lake build` to confirm that every published declaration
depends only on `propext`, `Classical.choice`, `Quot.sound`.

## License

Apache 2.0 — see [LICENSE](LICENSE).
