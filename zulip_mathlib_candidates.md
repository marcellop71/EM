# Mathlib Contribution Candidates from the Euclid-Mullin Formalization

The repository [EM](https://github.com/marcellop71/EM) (~68,500 lines, 125 files, zero sorry)
formalizes reductions of the Mullin Conjecture in Lean 4 / Mathlib v4.29.0-rc1.
Along the way it developed general-purpose mathematics that fills genuine gaps in Mathlib.
Below are the strongest candidates, filtered for non-trivial proofs of well-established
results that are missing from the current library.

---

## 1. Van der Corput Inequality

**File:** `LargeSieveSpectral.lean:591` (~280 lines)

The finite Van der Corput bound for exponential/character sums:
for a bounded sequence `f` with autocorrelation bounds `|R_h| ≤ δN`
for lags `1 ≤ h ≤ H`:

```
‖∑_{n<N} f(n)‖² ≤ 2N²/(H+1) + 2δN²
```

One of the most important techniques in analytic number theory.
Completely missing from Mathlib. Self-contained proof.

| Identifier | Kind | Description |
|---|---|---|
| `VanDerCorputBound` | def | Statement |
| `van_der_corput_bound` | thm | Full proof |

---

## 2. Parseval Identities for Finite Abelian Groups

**Files:** `LargeSieveHarmonic.lean`, `LargeSieveAnalytic.lean`

Mathlib defines `ZMod.dft` but has no Parseval/Plancherel identity for it.
These fill that gap:

| Identifier | File | Description |
|---|---|---|
| `zmod_dft_parseval` | `LargeSieveHarmonic.lean:135` | `∑_k ‖(𝓕Φ)(k)‖² = N · ∑_j ‖Φ(j)‖²` |
| `zmod_dft_plancherel_complex` | `LargeSieveHarmonic.lean:416` | Bilinear Plancherel for `ZMod.dft` |
| `char_parseval_units` | `LargeSieveAnalytic.lean:809` | `∑_χ ‖∑ g(a)·χ(a)‖² = (p−1)·∑ ‖g(a)‖²` for `(ℤ/pℤ)ˣ` |

---

## 3. Gauss Sum API

**Files:** `LargeSieveHarmonic.lean`, `LargeSieveAnalytic.lean`

Mathlib has `gaussSum` and `gaussSum_mul_gaussSum_eq_card` but is missing
several standard results that are needed for any serious application:

| Identifier | File | Description |
|---|---|---|
| `gaussSum_norm_sq_eq_prime` | `LargeSieveHarmonic.lean:388` | `‖τ(χ)‖² = p` for nontrivial χ mod p |
| `gaussSum_stdAddChar_ne_zero` | `LargeSieveAnalytic.lean:255` | `τ(χ) ≠ 0` for nontrivial χ |
| `gauss_sum_inversion` | `LargeSieveAnalytic.lean:268` | `χ(a) = τ(χ⁻¹)⁻¹ · τ(χ⁻¹, ψ_a)` |
| `char_sum_to_exp_sum` | `LargeSieveAnalytic.lean:304` | Gauss conductor transfer: character sums → exponential sums |
| `isPrimitive_of_prime_nontrivial` | `LargeSieveAnalytic.lean:206` | Nontrivial characters at prime level are primitive |

---

## 4. Finite Weyl Criterion

**File:** `LargeSieveSpectral.lean:411`

Quantitative equidistribution criterion for finite abelian groups:
if all nontrivial character sums are small, the sequence is equidistributed.

```
∀ χ ≠ 1, |∑ χ(x_n)| ≤ ε·N  ⟹  |V(a) − N/(p−1)| ≤ ε·N
```

General-purpose, not in Mathlib, and the natural finite-group analogue
of the classical Weyl criterion.

| Identifier | Kind | Description |
|---|---|---|
| `weyl_criterion_finite_group` | thm | Small char sums ⟹ equidistribution |

---

## 5. Liouville Function and Completely Multiplicative Predicate

**File:** `IKCh1.lean`

Mathlib has `ArithmeticFunction.moebius` and `Nat.ArithmeticFunction.IsMultiplicative`
(coprime only) but is missing:

| Identifier | Line | Description |
|---|---|---|
| `IsCompletelyMultiplicative` | 62 | `f(mn) = f(m)f(n)` for ALL m,n (not just coprime) |
| `liouville` | 172 | `λ(n) = (−1)^{Ω(n)}` |
| `liouville_isCompletelyMultiplicative` | 191 | λ is completely multiplicative |
| `liouville_eq_moebius_of_squarefree` | 200 | `λ(n) = μ(n)` for squarefree n |

The Liouville function is as fundamental as Möbius; its absence
from Mathlib is a clear gap.

---

## 6. Rotor-Router on Finite Groups

**File:** `RotorRouter.lean` (455 lines, self-contained)

First formalization of rotor-router (Propp machine) dynamics.
Could form a new `Mathlib.Dynamics.RotorRouter` module.

| Identifier | Line | Description |
|---|---|---|
| `eventually_periodic` | 79 | Every orbit on `[Finite α]` is eventually periodic |
| `rotor_tracks_visits` | 151 | Pointer = (initial + visit count) mod k |
| `visit_count_dvd_of_periodic` | 167 | Over one period, `k ∣ visitCount(x)` |
| `rotor_visits_all` | 328 | Rotor-router on finite group visits every element |
| `scheduled_walk_covers_all` | 395 | Abstract: pointwise-recurrent walk covers all elements |

---

## 7. Jordan's Inequality and Exponential Sum Estimates

**File:** `LargeSieveAnalytic.lean`

| Identifier | Line | Description |
|---|---|---|
| `sin_pi_ge_two_mul` | 102 | `sin(πt) ≥ 2t` for `t ∈ [0, 1/2]` |
| `norm_one_sub_eAN` | 79 | `‖1 − e(β)‖ = 2·|sin(πβ)|` |
| `norm_eAN_geom_sum_le_inv` | 152 | `‖∑ e(kβ)‖ ≤ 1/(2δ)` when β is δ-separated from ℤ |

Jordan's inequality is a classical result missing from Mathlib.
The exponential sum bound is the standard estimate used throughout
analytic number theory.

---

## 8. Mittag-Leffler Expansion of csc

**File:** `IKCh7Hilbert.lean:459` (~100 lines)

The classical partial fraction expansion:
for `θ ∉ ℤ`, the symmetric partial sums
`∑_{m=-K}^{K} (−1)^m/(θ+m)` converge to `π/sin(πθ)` as `K → ∞`.

This is a standard result in complex analysis (Mittag-Leffler theorem applied
to `csc`), used in the proof of the Hilbert inequality (IK Corollary 7.9).
The proof uses Mathlib's `Summable_cotTerm` and `tendsto_logDeriv_euler_cot_sub`
infrastructure.

| Identifier | Kind | Description |
|---|---|---|
| `MittagLefflerCsc` | def | Statement: alternating partial sums → `π/sin(πθ)` |
| `mittag_leffler_csc_proved` | thm | Full proof using Mathlib's cotangent series |

---

## 9. Hilbert Inequality Rescaling

**File:** `IKCh7Hilbert.lean:90` (~50 lines)

Reduction of the general δ-separated Hilbert inequality to the 1-separated case:
given `HilbertInequality1` (for 1-separated points), derive `HilbertInequality`
(for δ-separated points) via the substitution `λ_r ↦ λ_r/δ`.

| Identifier | Kind | Description |
|---|---|---|
| `hilbert_rescale` | thm | `HilbertInequality1 → HilbertInequality` |
| `hilbert1_implies_hilbert` | thm | Same reduction (alternate name) |

---

## 10. Cesaro Convergence of Cross Terms (Product-Index Trick)

**File:** `IKCh7Hilbert.lean:1410` (~490 lines)

Infrastructure for the product-index trick (IK Corollaries 7.9–7.10):
lift R points on `ℝ/ℤ` to `R·(2K+1)` points on `ℝ`, show that cross terms
(involving `1/(α_r − α_s + k)` summed over `k ∈ [-K,K]`) converge in the
Cesaro sense to `π·csc(π(α_r − α_s))` using the Mittag-Leffler expansion.

| Identifier | Kind | Description |
|---|---|---|
| `CrossRCesaroConvergence` | def | Statement of Cesaro convergence of cross terms |
| `cross_r_cesaro_convergence_proved` | thm | Full proof (~490 lines) |
| `same_r_antisymmetry` | thm | Self-interaction terms cancel by antisymmetry |
| `hilbert_lifted_bound` | thm | HilbertInequality applied to lifted point system |

---

## 11. One-Sided Tauberian Lemma

**File:** `OneSidedTauberian.lean:59` (~50 lines)

For nonneg `bₙ ≥ 0`, the partial sum `∑_{n≤N} bₙ` is bounded by
`N^ε · ∑_n bₙ/n^ε` for any `ε > 0`. Elementary proof via `n^ε ≤ N^ε`.

This is the key one-sided bound that, combined with Mathlib's L-function
infrastructure, reduces `WeightedPNTinAP` to a real-variable
Wiener-Ikehara hypothesis. Not in Mathlib.

| Identifier | Kind | Description |
|---|---|---|
| `one_sided_tauberian_upper` | thm | `∑_{n≤N} bₙ ≤ N^ε · ∑_n bₙ/n^ε` for `bₙ ≥ 0` |
| `one_sided_tauberian_dirichlet` | thm | Applied to Dirichlet series: partial sum ≤ N^ε · L(1+ε) |

---

## 12. L-series Upper Bound for Residue Classes

**File:** `OneSidedTauberian.lean:146` (~40 lines)

Mathlib's `PrimesInAP.lean` proves a *lower* bound on `∑ Λ(n)·1_{n≡a}/n^x`
near `x = 1` (via `LSeries_residueClass_lower_bound`), but does not export
the corresponding *upper* bound. This file extracts the identity

    tsum = LFunctionResidueClassAux(a, x).re + (φ(q))⁻¹/(x−1)

from Mathlib's proof and derives both bounds, enabling Tauberian applications.

| Identifier | Kind | Description |
|---|---|---|
| `residueClass_tsum_eq_aux_plus_pole` | thm | Identity: tsum = aux.re + pole |
| `residueClass_tsum_upper_bound` | thm | Upper bound: tsum ≤ (φ(q))⁻¹/(x−1) + C |
| `residueClass_tsum_both_bounds` | thm | Two-sided: pole − C ≤ tsum ≤ pole + C |

---

## 13. Doubly Stochastic Transition on Finite Groups

**File:** `SelfCorrectingDrift.lean:616` (~20 lines)

For a finite group `G` and uniform measure on `G`, the random walk
transition matrix is doubly stochastic: each row and column sums to 1.

| Identifier | Kind | Description |
|---|---|---|
| `group_walk_doubly_stochastic` | thm | Uniform multiplier gives doubly stochastic transitions |

---

## 14. Spectral Gap for Generating Sets on Finite Abelian Groups

**File:** `VanishingNoise.lean:110` (~130 lines)

If a finite subset S of a finite commutative group G generates G, contains the
identity, and has |S| ≥ 2, then for any nontrivial character χ : G →* ℂˣ:

```
‖∑_{s ∈ S} χ(s)‖ < |S|
```

Equivalently, the spectral contraction `‖∑ χ(s)‖ / |S| < 1`.
This is the standard spectral gap that drives mixing on Cayley graphs.
The proof uses `StrictConvexSpace` (for `‖z + w‖ < 2` when z ≠ w on the unit circle)
and `Subgroup.closure_le` to find an element where χ is nontrivial.

A variant without the identity assumption is also proved: if there exist s, t ∈ S
with χ(s) ≠ χ(t), then `‖∑ χ(s)‖ < |S|`.

Completely missing from Mathlib. Self-contained.

| Identifier | Kind | Description |
|---|---|---|
| `char_norm_one_of_hom` | thm | `‖χ(g)‖ = 1` for group hom χ : G →* ℂˣ (G finite) |
| `exists_ne_one_of_nontrivial` | thm | Nontrivial χ on generators: ∃ s ∈ S with χ(s) ≠ 1 |
| `norm_add_lt_two_of_ne` | thm | `‖z + w‖ < 2` for unit-norm z ≠ w (strict convexity) |
| `spectral_gap_with_identity` | thm | `‖∑ χ(s)‖ < |S|` for nontrivial χ, generating S ∋ 1 |
| `spectral_contraction_lt_one` | thm | Ratio form: `‖∑ χ(s)‖ / |S| < 1` |
| `spectral_gap_of_distinct_values` | thm | Without 1 ∈ S: distinct χ-values ⇒ strict bound |

---

## 15. Infinite Product Contraction (Divergent Series ⇒ Vanishing Product)

**Files:** `VanishingNoise.lean:330` (~55 lines), `VanishingNoiseC.lean:363` (~55 lines)

For a sequence `γ_k ∈ (0, 1]` with divergent sum `∑ γ_k = +∞`:

```
∏_{k < N} (1 − γ_k) → 0  as  N → ∞
```

Proved using `1 − x ≤ exp(−x)` and the exponential:
`∏(1 − γ_k) ≤ exp(−∑ γ_k) → 0`.

This is a standard real analysis fact (e.g., Rudin, Principles 15.5) that is
completely missing from Mathlib. Used in probability (Borel–Cantelli),
dynamics (mixing), and number theory (Euler products).

A **sparse variant** relaxes `0 < a_k` to `0 ≤ a_k ≤ 1`, allowing
some factors to equal 1 (no contraction at those steps). The conclusion
is the same: if the gaps `1 − a_k` are non-summable, the partial
products tend to 0. This is the version actually needed for sieve
applications where the indicator function is supported on primes in a
specific residue class (most terms contribute gap 0).

| Identifier | File | Description |
|---|---|---|
| `product_contraction_tendsto` | `VanishingNoise.lean:330` | `γ_k ∈ (0,1], ∑ γ_k = ∞ ⇒ ∏(1 − γ_k) → 0` |
| `sparse_product_contraction` | `VanishingNoiseC.lean:363` | `a_k ∈ [0,1], ¬Summable(1 − a_k) ⇒ ∏ a_k → 0` |

---

## 16. Irrationality of log(p)/log(q) for Distinct Primes

**File:** `LFunction.lean:206` (~130 lines)

For distinct primes p, q: `log(p) / log(q) ∉ ℚ`.

The proof proceeds by contradiction: if `log(p)/log(q) = a/b` with a, b ∈ ℤ,
then `p^b = q^a`, contradicting unique prime factorization.
Handles all sign cases (a, b could be negative) carefully.

| Identifier | Kind | Description |
|---|---|---|
| `prime_pow_ne_prime_pow` | thm | `p^a ≠ q^b` for distinct primes, positive exponents |
| `log_ratio_irrational` | thm | `log(p)/log(q) ∉ ℚ` for distinct primes |

---

## 17. Discrete Abel Summation

**File:** `AbelChain.lean:161` (~40 lines)

The summation-by-parts identity for finite sums:

```
∑_{k=a}^{b-1} f(k)·(g(k+1) − g(k)) = f(b)·g(b) − f(a)·g(a) − ∑_{k=a}^{b-1} g(k+1)·(f(k+1) − f(k))
```

Used throughout analytic number theory (partial summation / Abel's summation formula).
Not in Mathlib as a standalone lemma.

| Identifier | Kind | Description |
|---|---|---|
| `discrete_abel` | thm | Abel summation formula (summation by parts) |

---

## 18. Log-Log Integrals via FTC

**File:** `AbelChain.lean:31` (~80 lines)

Explicit evaluation of two standard integrals via the fundamental theorem of calculus,
plus sandwich inequalities between log-log differences and log ratios:

| Identifier | Kind | Description |
|---|---|---|
| `hasDerivAt_log_log` | thm | `d/dt[log(log t)] = 1/(t·log t)` for t > 1 |
| `hasDerivAt_neg_inv_log` | thm | `d/dt[−(log t)⁻¹] = (t·(log t)²)⁻¹` |
| `integral_inv_mul_log` | thm | `∫_a^b 1/(t·log t) dt = log(log b) − log(log a)` |
| `integral_inv_mul_log_sq` | thm | `∫_a^b 1/(t·(log t)²) dt = 1/log(a) − 1/log(b)` |
| `log_ratio_le` | thm | `(log b − log a)/log b ≤ log(log b) − log(log a)` |
| `loglog_le_ratio` | thm | `log(log b) − log(log a) ≤ (log b − log a)/log a` |

---

## 19. Norm-Squared Partial Sum Telescoping (Inner Product Spaces)

**File:** `DSLInfra.lean:58` (~50 lines)

For a sequence `z_k` in an inner product space:

```
‖∑_{k<N} z_k‖² = ∑_{k<N} ‖z_k‖² + 2 · ∑_{k<N} ⟪∑_{j<k} z_j, z_k⟫
```

This is a pure Hilbert space identity (diagonal + cross-term decomposition of
the squared norm of a partial sum). General-purpose, used in harmonic analysis,
probability (variance decomposition), and signal processing.

| Identifier | Kind | Description |
|---|---|---|
| `norm_sq_partial_sum_telescoping` | thm | ‖∑ z_k‖² = diagonal + 2·cross terms |
