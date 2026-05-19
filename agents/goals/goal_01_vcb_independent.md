# Goal 01: VCB as an Independent Target

## Status: REVISITABLE (not a dead end — underexplored)

## What It Is

**VanishingConditionalBias (VCB)** weakens CME by allowing fiber character sums
`F(a)` to be approximately proportional to visit counts `V(a)` with a common
ratio `μ`, rather than requiring `F(a) = o(N)` (which forces `μ = 0`).

## What's Already Proved

| Theorem | File | Line | Status |
|---------|------|------|--------|
| `VanishingConditionalBias` (def) | LargeSieveSpectral.lean | 1974 | defined |
| `cme_implies_vcb` | LargeSieveSpectral.lean | 1992 | PROVED (take μ=0) |
| `vcbPedImpliesCcsb` | LargeSieveSpectral.lean | 2036 | PROVED |
| `vcb_ped_implies_mc` | LargeSieveSpectral.lean | 2337 | PROVED |
| `PositiveEscapeDensity` (def) | EquidistSelfCorrecting.lean | ~80 | defined |

The full chain **VCB + PED → CCSB → MC** is formally proved. Both VCB and PED
are strictly weaker than CME.

## The Opportunity

VCB is easier than CME because it allows a non-zero proportionality constant μ.
Instead of proving character sums vanish, you only need to prove they are
*approximately proportional to visit counts*. This is a weaker analytic
requirement that may be accessible through:

1. **Ergodic-type arguments**: If the walk is "approximately stationary" in a
   time-averaged sense, the fiber sums should track visit counts with a common μ.

2. **Spectral gap methods**: A spectral gap for the transition operator on
   `(Z/qZ)×` would give exponential mixing, which implies VCB with explicit
   decay rates.

3. **Correlation decay**: If consecutive multipliers `m(n), m(n+1)` are weakly
   correlated, the fiber sums can't deviate far from proportionality.

## What To Pursue

### For lean-formalizer

1. **Prove VCB for order-2 characters directly.** Since order-2 characters take
   values ±1, the fiber structure is binary: `ker(χ)` vs its complement. Show
   that the ±1 character sum is approximately proportional to the visit imbalance.
   This should be easier than general VCB and would complete the d=2 chain
   without needing PEDImpliesComplexCSB.

   Target theorem:
   ```
   theorem vcb_order2 (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
       (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1)
       (hord : orderOf χ = 2) : VCB_for_chi q hq hne χ hχ
   ```

2. **Characterize when VCB holds with μ = 0 vs μ ≠ 0.** If you can show μ must
   be a root of unity (from the group structure), that constrains the problem.
   Add a lemma showing the set of achievable μ values is related to the character
   group.

3. **Connect VCB to the decorrelation hypothesis.** The `DecorrelationHypothesis`
   in LargeSieveSpectral.lean (~line 1100) says consecutive multipliers are
   uncorrelated. Show `Dec → VCB` directly (bypassing CME), which would give
   a shorter chain.

### For literature-scout

1. Search for results on **equidistribution of multiplicative functions along
   subsequences** that allow proportional bias (not just equidistribution).
   Key terms: "multiplicative function pretentious distance", "Halász theorem
   for subsequences", "mean value theorems with bias".

2. Look for **random walk on finite groups with approximately stationary
   increments**. VCB is essentially a time-averaged stationarity condition.
   Key authors: Diaconis, Saloff-Coste, Hildebrand.

3. Search for **spectral gap estimates for multiplicative walks mod q**. If the
   transition matrix for the walk on `(Z/qZ)×` has a spectral gap bounded away
   from 0 (uniformly in N), VCB follows.

### For attack agents

1. **Numerical check**: For small primes q ∈ {3,5,7,11,13}, compute the actual
   fiber character sums and visit counts for N up to 10000. Fit the ratio
   `F(a)/V(a)` and check whether it converges to a common μ. If μ ≈ 0 always,
   VCB and CME coincide empirically.

2. **Adversarial test**: Construct a modified sequence (not EM, but satisfying
   the same structural constraints) where VCB holds with μ ≠ 0. If no such
   sequence exists, VCB may be equivalent to CME.

## Pitfalls to Avoid

- **Do NOT try to prove VCB by first proving CME.** The whole point is that VCB
  is strictly weaker. If your proof forces μ = 0, you've proved CME, not VCB.
- **Do NOT conflate VCB with simple equidistribution.** VCB allows systematic
  bias (μ ≠ 0). The fiber sums need not vanish.
- **Do NOT import Mathlib directly.** All imports go through existing EM files.
  Check existing API in LargeSieveSpectral.lean and EquidistSelfCorrecting.lean.

## Success Criteria

- A new `.lean` file proving `Dec → VCB` (bypassing CME), OR
- A new `.lean` file proving VCB for order-2 characters, OR
- A literature finding that connects VCB-type conditions to known results about
  multiplicative functions, with a concrete proof strategy.
