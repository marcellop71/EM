# Goal 02: SieveTransfer via Coprimality Structure

## Status: REVISITABLE (genuine mathematical frontier, underexplored angle)

## What It Is

**SieveTransfer** is the open Prop asserting that generic smallest-prime-factor
equidistribution (which holds for "random" integers by Alladi's theorem) transfers
to the specific EM sequence `prod(n) + 1`.

The chain is:
```
PrimeDensityEquipartition → GenericLPFEquidist → (SieveTransfer) →
SieveEquidistribution → NoLongRuns(L) → PED → CCSB → MC
```

## What's Already Proved

| Theorem | File | Line | Status |
|---------|------|------|--------|
| `SieveTransfer` (def) | EquidistSieveTransfer.lean | 103 | defined |
| `GenericLPFEquidist` (def) | EquidistSieveTransfer.lean | ~70 | defined |
| `SieveEquidistribution` (def) | EquidistSieveTransfer.lean | ~85 | defined |
| `genericLPF_chain_mc` | EquidistSieveTransfer.lean | 321 | PROVED |
| `SieveEquidistImpliesNoLongRuns` | EquidistSieveTransfer.lean | 120 | open Prop |

The full conditional chain from GenericLPFEquidist + SieveTransfer to MC is proved.
Both SieveTransfer and SieveEquidistImpliesNoLongRuns are open.

## The Opportunity — Coprimality Structure

The standard obstacle is stated clearly in the definition (line 103-118):
EM products are super-exponentially growing products of distinct primes, so they
lie in a "very thin and structured subset of integers." Standard sieve methods
apply to ranges, not to specific subsequences.

But this thinness is also a **structural advantage**: `prod(n) + 1` is coprime
to every prime ≤ seq(n) (since `prod(n)` is their product). This means:

1. `prod(n) + 1` avoids small prime factors by construction.
2. The smallest prime factor of `prod(n) + 1` must be > seq(n).
3. This is a **strong coprimality sieve**: the number `prod(n) + 1` has been
   pre-sieved by all primes up to seq(n).

The idea: exploit this coprimality to show that the conditional distribution of
`minFac(prod(n) + 1)` among primes > seq(n) is approximately uniform, which is
a Linnik-type equidistribution result on a pre-sieved set.

## What To Pursue

### For lean-formalizer

1. **Formalize the coprimality lemma.** Prove:
   ```
   theorem prod_plus_one_coprime (n k : ℕ) (hk : k ≤ n) :
       Nat.Coprime (prod n + 1) (seq k)
   ```
   This should follow from `seq k ∣ prod n` and `gcd(m, m+1) = 1`.

2. **Formalize a conditional version of SieveTransfer.** Instead of transferring
   from all integers, transfer from the restricted set
   `{m : ℕ | ∀ p ≤ B, p.Prime → ¬(p ∣ m)}` (B-smooth-free integers).
   This is closer to what sieve theory actually provides.

   Target:
   ```
   def ConditionalSieveTransfer (B : ℕ → ℝ) : Prop :=
     -- GenericLPFEquidist restricted to integers coprime to all primes ≤ B(N)
     -- implies SieveEquidistribution
   ```

3. **Bridge SieveEquidistImpliesNoLongRuns.** The current note (lines 120-131)
   says density on [0,N) doesn't imply gap control. But if the density is
   *monotonically improving* (escape fraction in [0,N) is increasing), then a
   pigeonhole argument should give gap control. Formalize this:
   ```
   theorem monotone_density_implies_noLongRuns
       (hmono : ∀ N₁ ≤ N₂, escapeDensity N₁ ≤ escapeDensity N₂)
       (hpos : ∃ N₀, 0 < escapeDensity N₀) :
       ∃ L, NoLongRuns L
   ```

### For literature-scout

1. **Linnik's theorem on least prime in arithmetic progressions.** The EM
   sequence asks: what is the least prime factor of a specific number coprime
   to all small primes? Linnik's theorem gives equidistribution of primes in
   arithmetic progressions. Search for: "Linnik theorem effective bounds",
   "least prime factor distribution coprime integers", "Iwaniec sieve for
   specific integers".

2. **Alladi's theorem on distribution of largest prime factors.** The dual
   problem (largest vs smallest prime factor) is well-studied. Search for
   analogues for smallest prime factors: "Alladi Erdős smallest prime factor
   equidistribution", "Dickman function smallest factor".

3. **Fouvry-Iwaniec sieve for integers in thin sets.** The EM products form
   a "thin" set (super-exponentially sparse). Search for sieve results that
   apply to specific thin subsequences rather than ranges: "sieve thin
   sequences", "multiplicative structure subsequence equidistribution".

4. **Coprimality sieves (Brun, Selberg) for pre-sieved integers.** When an
   integer is already known to be coprime to all primes ≤ B, what can be said
   about its smallest prime factor? Search: "conditional sieve pre-sieved
   integers", "remainder term Selberg sieve coprime integers".

### For attack agents

1. **Empirical distribution of seq(n+1) / prod(n).** For N up to 10000, compute
   `seq(n+1)` (the smallest prime factor of `prod(n)+1`) and plot its
   distribution relative to the primes > seq(n). Check whether it looks uniform.

2. **Correlations between consecutive seq values.** Compute autocorrelation of
   `seq(n)` for lags 1, 2, 3, .... If correlations decay rapidly, the sieve
   transfer is more plausible.

## Pitfalls to Avoid

- **Do NOT try standard Bombieri-Vinogradov.** Dead end #96 (LargeSieveAnalytic.lean
  line 1601) proves the LoD error term is exponential in N (because prod(N) ≥ 2^N),
  making BV-type bounds useless. Any sieve approach must measure error relative
  to N, not relative to prod(N).

- **Do NOT confuse SieveEquidistribution with CME.** SieveEquidistribution is
  about the distribution of `minFac(prod(n)+1)` among primes, NOT about character
  sums. It's a different (weaker) condition.

- **Do NOT assume the SieveEquidistImpliesNoLongRuns bridge is easy.** The
  density→gap transfer requires careful analysis of the specific structure.

## Success Criteria

- A new `.lean` file with the coprimality lemma and a refined SieveTransfer variant
  that exploits coprimality structure, OR
- A proof of SieveEquidistImpliesNoLongRuns under a monotonicity assumption, OR
- A literature reference to a sieve result that applies to pre-sieved integers
  of the form `∏p_i + 1` with a concrete transfer strategy.
