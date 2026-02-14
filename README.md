# Formalizing the Mullin's Conjecture

A Lean 4 formalization (Mathlib v4.27.0) with ~22,400 lines of Lean across 32 files.

## The Euclid–Mullin Sequence

Euclid's proof that there are infinitely many primes shows that for any finite set of primes, their product plus one has a prime factor outside the set — but does not specify *which* factor. The [Euclid–Mullin sequence](https://oeis.org/A000945) (Mullin, 1963) makes a definite choice: always take the *smallest* prime factor.

```
a(0) = 2,    a(n+1) = smallest prime factor of (a(0) · a(1) · ··· · a(n) + 1)
```

The first terms are 2, 3, 7, 43, 13, 53, 5, 6221671, 38709183810571, 139, 2801, 11, 17, ... — the sequence behaves almost randomly, with small primes appearing out of order and enormous primes appearing early. As of 2025, 51 terms are known; the smallest prime not yet observed is 41.

**Mullin's Conjecture:** Every prime number eventually appears in this sequence.

## Paper

The full paper is available at [`docs/paper.pdf`](docs/paper.pdf) (source: [`docs/paper.tex`](docs/paper.tex)), with clickable links to the Lean source code for every formally verified result.

## Documentation

| Document | Description |
|----------|-------------|
| [`docs/main-results.md`](docs/main-results.md) | Proved reductions, open hypotheses, key results |
| [`docs/agents.md`](docs/agents.md) | Multi-agent system documentation |
| [`docs/status.md`](docs/status.md) | Detailed project status |

## Building

Requires [Lean 4](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4) v4.27.0.

```bash
curl https://elan.lean-lang.org/install.sh -sSf | sh   # install elan
git clone <repo-url> && cd EM
lake exe cache get   # download prebuilt Mathlib oleans
lake build           # builds all source files — zero errors, zero sorry
```

## License

Apache 2.0 — see [LICENSE](LICENSE).
