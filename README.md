# A formalized reduction of the Mullin's Conjecture

## The Euclid–Mullin Sequence

Euclid’s proposition IX.20 of the Elements shows that for any finite set of primes, each prime
factor of their product plus one is outside the set: to grow your set of primes, you can pick any
of them.
The [Euclid–Mullin sequence](https://oeis.org/A000945) (Mullin, 1963) makes a definite choice: always take the *smallest* prime factor.

```
a(0) = 2,    a(n+1) = smallest prime factor of (a(0) · a(1) · ··· · a(n) + 1)
```

The first terms are 2, 3, 7, 43, 13, 53, 5, 6221671, 38709183810571, 139, 2801, 11, 17, ... — the sequence behaves almost randomly, with small primes appearing out of order and enormous primes appearing early. As of 2025, 51 terms are known; the smallest prime not yet observed is 41.

**Mullin's Conjecture:** Every prime number eventually appears in this sequence.

## Paper

The full paper is available in this repo at [`paper/main.pdf`](paper/main.pdf) with clickable links to the Lean source code for every formally verified result.

## License

Apache 2.0 — see [LICENSE](LICENSE).
