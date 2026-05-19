# Goal 03: Level of Distribution with Renormalized Scale

## Status: REVISITABLE (dead end #96 kills the standard formulation, but a walk-adapted variant may work)

## What It Is

The standard Level of Distribution (LoD) formulation measures character sum error
relative to `prod(N)^θ`, which is exponential in N. Dead end #96 proves this is
useless since MMCSB needs `o(N)` bounds.

The idea: reformulate LoD with error terms measured against **N** (the walk step
count) rather than `prod(N)` (the product magnitude). This is a "walk-adapted"
or "renormalized" LoD.

## What's Already Proved

| Theorem | File | Line | Status |
|---------|------|------|--------|
| `EMHasLevelOfDistribution` (def) | LargeSieve.lean | 505 | defined (broken scale) |
| `LoDImpliesMMCSB` (def) | LargeSieve.lean | 530 | open Prop (vacuously unprovable) |
| Dead End #96 | LargeSieveAnalytic.lean | 1601 | PROVED (LoD scale mismatch) |
| `lod_chain_mc` | LargeSieve.lean | 693 | PROVED (conditional) |
| `prod_exponential_lower` | (referenced) | — | PROVED (prod N ≥ 2^N) |

Dead End #96 (LargeSieveAnalytic.lean:1601-1683) formally proves:
- `prod(N)^θ ≥ 2^{θN}` (exponential in N)
- For any ε > 0 and θ > 0, eventually `(prod N)^θ > ε * N`
- Therefore `LoDImpliesMMCSB` is vacuously unprovable

## The Opportunity — Walk-Adapted LoD

Standard LoD: `‖∑ χ(w(n))‖ ≤ (prod N)^θ / (log prod N)^A` for `q ≤ (prod N)^θ`

Walk-adapted LoD: `‖∑ χ(w(n))‖ ≤ N / (log N)^A` for `q ≤ N^θ`

The key differences:
1. The **modulus range** is `q ≤ N^θ` (polynomial in step count), not
   `q ≤ (prod N)^θ` (exponential).
2. The **error bound** is `N / (log N)^A` (sublinear for large A), not
   `(prod N)^θ` (exponential).
3. This is a genuinely different hypothesis because the walk step count N is
   the natural scale for the problem (CCSB and CME both use N).

## What To Pursue

### For lean-formalizer

1. **Define the walk-adapted LoD.** Create a new Prop:
   ```
   def WalkAdaptedLoD (θ : ℝ) : Prop :=
     0 < θ ∧ θ ≤ 1 ∧
     ∀ (A : ℝ) (_ : 0 < A),
     ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
       ∀ (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
       (q : ℝ) ≤ (N : ℝ) ^ θ / (Real.log (N : ℝ)) ^ A →
       ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_ : χ ≠ 1),
       ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤
         (N : ℝ) / (Real.log (N : ℝ)) ^ A
   ```

2. **Prove `WalkAdaptedLoD → CCSB` (or `→ MMCSB`).** The error `N / (log N)^A`
   is `o(N)` for any A > 0, which is exactly what CCSB requires. The modulus
   range `q ≤ N^θ` covers all fixed primes q for large N (since seq grows).
   This should be a short proof:
   ```
   theorem walk_lod_implies_ccsb (θ : ℝ) (hθ : 0 < θ)
       (hlod : WalkAdaptedLoD θ) : ComplexCharSumBound
   ```

3. **Prove the chain to MC.** Connect `WalkAdaptedLoD → CCSB → MC` using the
   existing `complex_csb_mc'` theorem.

4. **Relate to existing hypotheses.** Show:
   - `CME → WalkAdaptedLoD θ` for all θ (CME is stronger)
   - `WalkAdaptedLoD θ → CCSB` (the new chain)
   - Position WalkAdaptedLoD in the existing hierarchy diagram

### For literature-scout

1. **Bombieri-Vinogradov for multiplicative walks.** The standard BV theorem
   gives LoD for Dirichlet characters over intervals. Search for analogues
   where the summation is over a walk/sequence rather than an interval:
   "Bombieri-Vinogradov subsequence", "character sum walk", "level of
   distribution multiplicative sequence".

2. **Elliott-Halberstam conjecture variants.** The EH conjecture extends BV
   to θ = 1. Are there conditional results (on GRH or other hypotheses) that
   give LoD with walk-adapted scales? Search: "Elliott-Halberstam conditional",
   "level of distribution beyond 1/2".

3. **Exponential sums along polynomial sequences.** The EM products satisfy
   `prod(n+1) = prod(n) · seq(n+1)`, a multiplicative recurrence. Search for
   character sum estimates along multiplicatively defined sequences: "exponential
   sum multiplicative recurrence", "Weyl sum recursive sequence".

4. **IK Chapter 17 (Bombieri-Vinogradov theorem).** Check if our IK formalization
   (IKCh1-5, IKCh7Foundations/AdditiveLS/MultiplicativeLS/SieveApplications/Hilbert) has relevant API. The BV theorem is in chapter 17 which
   we haven't formalized yet.

### For attack agents

1. **Empirical modulus range.** For the EM sequence up to N = 10000, what is the
   largest prime q that appears as seq(n) for n ≤ N? Compare to N^{1/2}, N^{2/3},
   N. This determines the effective θ.

2. **Character sum growth rate.** For small primes q ∈ {3,5,7,11}, compute
   `‖∑_{n<N} χ(w(n))‖` for N up to 10000. Plot against N, N/log(N), √N.
   Determine the empirical growth rate.

## Pitfalls to Avoid

- **Do NOT use the existing `EMHasLevelOfDistribution`.** It's defined with the
  wrong scale (prod(N)^θ). Define a new hypothesis from scratch.

- **Do NOT try to derive `WalkAdaptedLoD` from `EMHasLevelOfDistribution`.**
  The scale mismatch is fundamental (dead end #96). The walk-adapted version
  is an independent hypothesis.

- **Do NOT conflate N^θ modulus range with (prod N)^θ.** The whole point is
  that N^θ is polynomial while (prod N)^θ is exponential. They are completely
  different.

- **Be careful with the `q ≤ N^θ` range.** For the EM sequence, primes appearing
  as seq(n) can grow faster than any polynomial of n. The walk-adapted LoD only
  covers primes up to N^θ, which may miss some. This is acceptable since CCSB
  only needs the bound for each fixed q individually (eventually N^θ > q).

## Success Criteria

- A new `.lean` file defining `WalkAdaptedLoD` and proving `WalkAdaptedLoD → CCSB → MC`, OR
- A literature reference showing walk-adapted BV-type results exist with concrete
  applicability to multiplicative sequences, OR
- Numerical evidence characterizing the empirical LoD exponent for the EM walk.
