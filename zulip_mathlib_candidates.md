# Mathlib Contribution Candidates from the Euclid-Mullin Formalization

The repository [EM](https://github.com/mparis-est/EM) (~39,600 lines, 62 files, zero sorry)
formalizes reductions of the Mullin Conjecture in Lean 4 / Mathlib v4.27.0.
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
