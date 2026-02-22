# A formalized reduction of the Mullin's Conjecture

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

## Paper

The full paper is available at [`paper/main.pdf`](paper/main.pdf) with clickable links to the Lean source code for every formally verified result.

## Mathlib Candidates

Several general-purpose results developed in this formalization fill genuine gaps in Mathlib. See [`zulip_mathlib_candidates.md`](zulip_mathlib_candidates.md) for a curated list.

## Content-Addressed Registry

The project includes a machine-readable registry of all key results and open hypotheses, using the [CA](https://github.com/marcellop71/CA) (Content Addressing for Lean 4) package.

**How it works:** The CA package provides `@[publish]` and `@[open_point]` attributes that tag declarations for inclusion in a decentralized formal math registry. Each tagged declaration gets a content address — a deterministic hash of its canonicalized type expression (universe-renamed, metadata-stripped). The `#ca_registry` command at the end of [`EM/Registry.lean`](EM/Registry.lean) generates the registry files automatically during `lake build`.

- [`EM/Registry.lean`](EM/Registry.lean) — `@[open_point]` annotations (unproved hypotheses) and `@[publish]` annotations (proved theorems)
- [`registry/declarations.json`](registry/declarations.json) — entries with name, module, kind, status, content hash, pretty-printed type, and dependency list
- [`registry/meta.json`](registry/meta.json) — project summary (open points, proved, conditional)

The registry is regenerated automatically by `lake build`.

## License

Apache 2.0 — see [LICENSE](LICENSE).
