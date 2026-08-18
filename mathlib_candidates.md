# Mathlib Contribution Candidates from the Euclid–Mullin Formalization

The repository [EM](https://github.com/marcellop71/EM) (208 files, ~107,000 lines, zero
`sorry`) formalizes reductions of Mullin's Conjecture against **Mathlib `v4.33.0`**
(toolchain `leanprover/lean4:v4.33.0`). Along the way it developed general-purpose
mathematics that appears to fill genuine gaps in Mathlib. This file lists the candidates.

**How to read it.** Entries give the *declaration name* and the *file*, never a line
number — line numbers rot on every edit, names do not. Everything below is greppable:

```
grep -rn "necklace_identity_proved" EM/ --include="*.lean"
```

A machine-readable index of all 358 published declarations is in `registry/`.

**Scope.** Only live code is offered.  The repository's `EM/Archive/` (retired, `#exit`-guarded
files) is kept locally and is not part of the public tree; no candidate below lives there
(verified 2026-08-17).

**Status of the "missing from Mathlib" claims.** Re-verified against Mathlib `v4.33.0` on
2026-08-19: every file path and identifier below mechanically re-checked, and the `v4.33.0`
checkout re-grepped. **Three** previously-listed items have since landed in Mathlib and are
recorded as withdrawn rather than silently dropped (§B2, §B7, §B8).

**Prior art outside Mathlib matters too, and two entries have it.** Absence from Mathlib is
necessary but not sufficient for a contribution to be worth a reviewer's time: if a result
already exists in another Lean development, or sits in an open PR, that is the first thing a
reviewer needs to know. Two of the strongest entries are in exactly that position — §A1 (van
der Corput) and §A7 (Mertens) — and each now carries a prior-art note. Priority claims
previously attached to both were audited and **retracted**. Please flag any others.

**Declarations marked `private`** are not exported and would need unsealing before any
port. They are flagged.

---

## Triage

| Tier | What it means | Items |
|---|---|---|
| **A** | Substantial, self-contained, clearly absent, likely wanted | 1–7 |
| **B** | Real gaps, smaller or more specialised | 8–22 |
| **C** | One- or two-line facts; cheap to add, cheap to reprove | 23–29 |

If you only look at three, look at **§A7's Karamata half** (no Tauberian theorem of any
kind is in Mathlib, and none is in the neighbouring Lean developments either),
**§A2 (Parseval/Plancherel for `ZMod.dft`)** and **§A5 (necklace identity)**.

*Changed 2026-08-19.* §A1 (van der Corput) and the Mertens half of §A7 were previously in
this shortlist. Both are still absent from Mathlib `v4.33.0`, but both now have prior art
elsewhere and an open mathlib4 PR — see the notes in those sections. They remain listed;
they are no longer where a reviewer's scarce time is best spent.

---

# Tier A — strongest candidates

## A1. Van der Corput Inequality

**File:** `EM/ForMathlib/VanDerCorput.lean` (Mathlib-only imports; extracted 2026-08-18; un-wrapped statement `vanDerCorput_norm_sq_sum_le`)

The finite van der Corput bound for exponential/character sums: for a bounded sequence `f`
with autocorrelation bounds `|R_h| ≤ δN` for lags `1 ≤ h ≤ H`,

```
‖∑_{n<N} f(n)‖² ≤ 2N²/(H+1) + 2δN²
```

One of the basic techniques of analytic number theory. No occurrence of `van_der_corput`
or `vanDerCorput` anywhere in Mathlib `v4.33.0` (re-grepped 2026-08-19). Self-contained proof.

> **Prior art — read before spending time here.** A theorem named `van_der_Corput` has been
> in the Lean 4 **Carleson** project since its blueprint (arXiv:2405.06423, May 2024) and is
> in the finished formalization: `Carleson/Classical/VanDerCorput.lean`, plus
> `Carleson/HolderVanDerCorput.lean`. There is also an **open mathlib4 PR #39406**. So this
> entry is offered as an *alternative statement shape* (finite, autocorrelation-bounded,
> Mathlib-only imports), not as a first formalization; any earlier priority claim is
> retracted.

| Identifier | Kind | Description |
|---|---|---|
| `VanDerCorputBound` | def | Statement |
| `van_der_corput_bound` | thm | Full proof |

---

## A2. Parseval / Plancherel for `ZMod.dft`

**Files:** `EM/LargeSieve/Harmonic.lean`, `EM/LargeSieve/Analytic.lean`

Mathlib defines `ZMod.dft` in `Mathlib/Analysis/Fourier/ZMod.lean` and gives it a full
algebraic API (`dft_dft`, `dft_comp_neg`, `dft_comp_unitMul`, …) but **no Parseval or
Plancherel identity** — the file has no norm-level result at all. That is the first thing
one reaches for in an application.

| Identifier | File | Description |
|---|---|---|
| `zmod_dft_parseval` (= `ZMod.dft_norm_sq_sum`) | `EM/ForMathlib/ZModDftParseval.lean` | `∑_k ‖(𝓕Φ)(k)‖² = N · ∑_j ‖Φ(j)‖²` |
| `zmod_dft_parseval_complex` (= `ZMod.dft_mul_conj_sum`) | `EM/ForMathlib/ZModDftParseval.lean` | Complex inner-product Parseval |
| `zmod_dft_plancherel_complex` | `EM/LargeSieve/Harmonic.lean` | Bilinear Plancherel for `ZMod.dft` |
| `char_parseval_units` | `EM/LargeSieve/Analytic.lean` | `∑_χ ‖∑ g(a)·χ(a)‖² = (p−1)·∑ ‖g(a)‖²` on `(ℤ/pℤ)ˣ` |

---

## A3. Gauss Sum API

**Files:** `EM/LargeSieve/Harmonic.lean`, `EM/LargeSieve/Analytic.lean`

Mathlib has `gaussSum` and `gaussSum_mul_gaussSum_eq_card`, but not the consequences one
actually uses:

| Identifier | File | Description |
|---|---|---|
| `gaussSum_norm_sq_eq_prime` | `EM/LargeSieve/Harmonic.lean` | `‖τ(χ)‖² = p` for nontrivial `χ` mod `p` |
| `gaussSum_stdAddChar_ne_zero` | `EM/LargeSieve/Analytic.lean` | `τ(χ) ≠ 0` for nontrivial `χ` |
| `gauss_sum_inversion` | `EM/LargeSieve/Analytic.lean` | `χ(a) = τ(χ⁻¹)⁻¹ · τ(χ⁻¹, ψ_a)` |
| `char_sum_to_exp_sum` | `EM/LargeSieve/Analytic.lean` | Conductor transfer: character sums → exponential sums |
| `isPrimitive_of_prime_nontrivial` | `EM/LargeSieve/Analytic.lean` | Nontrivial characters at prime level are primitive |

---

## A4. Rotor-Router Dynamics on Finite Groups

**File:** `EM/Group/RotorRouter.lean` (455 lines, self-contained)

First formalization of rotor-router (Propp machine) dynamics we are aware of. Could form a
new `Mathlib.Dynamics.RotorRouter`.

| Identifier | Description |
|---|---|
| `eventually_periodic` | Every orbit on `[Finite α]` is eventually periodic |
| `rotor_tracks_visits` | Pointer = (initial + visit count) mod `k` |
| `visit_count_dvd_of_periodic` | Over one period, `k ∣ visitCount(x)` |
| `rotor_visits_all` | Rotor-router on a finite group visits every element |
| `scheduled_walk_covers_all` | Abstract: a pointwise-recurrent walk covers all elements |

---

## A5. Necklace Identity for Irreducible Polynomials over Finite Fields

**File:** `EM/FunctionField/NecklaceFormula.lean` (~130 lines)

The classical identity (Gauss; Moreau 1872): for every prime `p` and `n ≥ 1`,

```
∑_{d | n} d · π_p(d) = p^n
```

where `π_p(d)` counts monic irreducibles of degree `d` over `𝔽_p`. Mathlib has the Galois
theory of finite fields but states no irreducible-count result; nothing in
`Mathlib/FieldTheory/Finite/` counts irreducibles. Self-contained proof via minimal
polynomials of elements of `GF(p^n)`.

| Identifier | Kind | Description |
|---|---|---|
| `ffIrredCount` | def | Count of monic irreducibles of degree `d` over `𝔽_p` |
| `ffIrredCount_pos` | thm | `π_p(d) ≥ 1` for `d ≥ 1` |
| `necklace_identity_proved` | thm | `∑_{d∣n} d · π_p(d) = p^n` |
| `necklace_implies_irred_lower_bound` | thm | `d · π_p(d) ≤ p^d` |

Supporting counts, also absent from Mathlib and useful independently:

| Identifier | File | Description |
|---|---|---|
| `monic_natDegree_finite` | `EM/FunctionField/Finiteness.lean` | `{Q : R[X] \| Q.Monic ∧ Q.natDegree = d}` is finite for `[Fintype R]` |
| `card_monic_of_degree` | `EM/FunctionField/NecklaceFormula.lean` | exactly `p^n` monic polynomials of degree `n` over `𝔽_p` |

*(`coeff_injection` in `Finiteness.lean` is `private`.)*

---

## A6. Spectral Gap for Generating Sets on Finite Abelian Groups

**File:** `EM/Stochastic/VanishingNoise.lean` (~130 lines)

If a finite `S ⊆ G` generates the finite commutative group `G`, contains `1`, and
`|S| ≥ 2`, then for every nontrivial character `χ : G →* ℂˣ`,

```
‖∑_{s ∈ S} χ(s)‖ < |S|
```

— the spectral gap driving mixing on Cayley graphs. Proof via `StrictConvexSpace` and
`Subgroup.closure_le`. A variant drops `1 ∈ S` in favour of "some `s, t ∈ S` with
`χ(s) ≠ χ(t)`".

| Identifier | Description |
|---|---|
| `char_norm_one_of_hom` | `‖χ(g)‖ = 1` for `χ : G →* ℂˣ`, `G` finite |
| `exists_ne_one_of_nontrivial` | Nontrivial `χ` on generators: `∃ s ∈ S`, `χ(s) ≠ 1` |
| `norm_add_lt_two_of_ne` | `‖z + w‖ < 2` for unit-norm `z ≠ w` |
| `spectral_gap_with_identity` | `‖∑ χ(s)‖ < \|S\|` |
| `spectral_contraction_lt_one` | Ratio form |
| `spectral_gap_of_distinct_values` | Without `1 ∈ S` |

---

## A7. Karamata's Tauberian Theorem, and Mertens' Theorem in Progressions

**File:** `EM/IK/Karamata.lean` (~670 lines, self-contained over Mathlib)

Mathlib has no Tauberian theorem of any kind (no hit for `Karamata`, `Tauberian`,
`HardyLittlewood` in `v4.33.0`).  This file proves the classical one for Dirichlet series
with nonnegative coefficients: if `c n ≥ 0`, `∑ c n · n^{−s}` converges for every `s > 0`,
and `s · ∑ c n · n^{−s} → C` as `s → 0⁺`, then

```
(∑_{n ≤ x} c n) / log x  →  C     (x → ∞).
```

Proof is the textbook Weierstrass-sandwich argument (monomials first, then polynomials, then
a continuous ramp squeezing the indicator `1_{[e^{−1},1]}`), with all the sandwich estimates
explicit; nothing is borrowed beyond Weierstrass approximation, `intervalIntegral`, and
`Summable` calculus.

| Identifier | Kind | Description |
|---|---|---|
| `IK.Karamata.dser`, `IK.Karamata.psum` | def | Dirichlet series `∑ c n · n^{−s}`; partial sums `∑_{1≤n≤x} c n` |
| `IK.Karamata.tendsto_monomial` | thm | The theorem for the test function `y^k` |
| `IK.Karamata.tendsto_poly` | thm | … for polynomials |
| `IK.Karamata.exists_sandwich` | thm | Polynomials `P_l ≤ 1_{[e^{−1},1]}/y ≤ P_u` with integrals within `η` |
| `IK.Karamata.tendsto_psum_exp` | thm | `s · psum c (e^{1/s}) → C` |
| `IK.Karamata.karamata` | thm | **The theorem**: `psum c x / log x → C` |

Applied in the same file to the coefficients `c n = Λ(n)·1_{n ≡ a (q)}` (Mathlib's
`vonMangoldt.residueClass`), whose L-series pole is exactly what
`Mathlib/NumberTheory/LSeries/PrimesInAP.lean` supplies, this gives **Mertens' theorem in
arithmetic progressions in asymptotic form**, and with prime-power stripping and Abel
summation (`EM/IK/Tauberian.lean`, `EM/IK/AbelChain.lean`) the reciprocal form:

| Identifier | File | Description |
|---|---|---|
| `IK.wcoef_tendsto` | `EM/IK/Karamata.lean` | `(∑_{n≤x, n≡a} Λ(n)/n) / log x → 1/φ(q)` |
| `IK.weightedPNTinAP_asymp_proved` | `EM/IK/Karamata.lean` | `∑_{p≤x, p≡a} log p / p ~ (log x)/φ(q)` |
| `IK.prime_power_stripping_asymp_proved` | `EM/IK/Tauberian.lean` | Prime powers contribute `O(1)` |
| `IK.primesEquidistInAP_asymp_proved` | `EM/IK/Karamata.lean` | `∑_{p≤x, p≡a} 1/p ~ (log log x)/φ(q)` |

Mathlib `v4.33.0` has no Mertens theorem (not even for `q = 1`), so the second table is a
candidate in its own right; the natural home for both is next to `PrimesInAP.lean`.  Nothing
here is `private`.

> **Prior art for the Mertens half — read before spending time here.** Two-sided Mertens I is
> in the **Isabelle/HOL AFP** since 2018 (Eberl–Paulson, *The Prime Number Theorem*,
> `Mertens_Theorems.thy`; `mertens_bound_strong` has strictly better constants than anything
> here), and in Lean 4 outside Mathlib in **PrimeNumberTheoremAnd**
> (`IEANTN/Mertens.lean`, `sum_log_prime_div_eq_log`, no `sorry`). An **open mathlib4 PR
> #41394** ("feat(NumberTheory/Mertens)") supersedes #40656. Any priority claim is retracted.
> **The Karamata half is unaffected**: no Tauberian theorem of any kind appears in Mathlib
> `v4.33.0`, and none of the developments above contains one — that is the part of this entry
> a reviewer should weigh.

---

# Tier B — real gaps, smaller or more specialised

## B1. Finite Weyl Criterion

**File:** `EM/LargeSieve/Spectral.lean`

`∀ χ ≠ 1, |∑ χ(x_n)| ≤ ε·N ⟹ |V(a) − N/(p−1)| ≤ ε·N`: the finite-group analogue of the
classical Weyl criterion.

| Identifier | Description |
|---|---|
| `weyl_criterion_finite_group` | Small character sums ⟹ equidistribution |

---

## B2. Completely-Multiplicative Predicate, and Liouville ↔ Möbius — **partially superseded**

**File:** `EM/IK/Ch1.lean`

> **Correction.** An earlier version claimed the Liouville function was missing. As of
> Mathlib `v4.30`+ it is **not**: `ArithmeticFunction.liouville` lives in
> `Mathlib/NumberTheory/ArithmeticFunction/Liouville.lean`, with `liouville_apply`,
> `liouville_apply_mul` and `isMultiplicative_liouville`. `IK.liouville` in this repo is
> now redundant and should be replaced by Mathlib's.

Two things in that entry are still absent, and both are small but real:

| Identifier | Description | Why still a gap |
|---|---|---|
| `IsCompletelyMultiplicative` | `f(mn) = f(m)f(n)` for **all** `m, n` | Mathlib has `IsMultiplicative` (coprime only) and states complete multiplicativity only as a bare equation per function (`liouville_apply_mul`); there is no predicate. `CompletelyMultiplicative` occurs solely as a section name in `EulerProduct/Basic.lean` |
| `liouville_eq_moebius_of_squarefree` | `λ(n) = μ(n)` for squarefree `n` | Mathlib's Liouville file makes no connection to `moebius` at all |

## B3. Mittag-Leffler Expansion of `csc`

**File:** `EM/IK/Ch7Hilbert.lean` (~100 lines)

For `θ ∉ ℤ`, the symmetric partial sums `∑_{m=−K}^{K} (−1)^m/(θ+m)` converge to
`π/sin(πθ)`. Built on Mathlib's `Summable_cotTerm` and
`tendsto_logDeriv_euler_cot_sub`, so it is a genuine extension of existing infrastructure
rather than a parallel development.

| Identifier | Kind | Description |
|---|---|---|
| `MittagLefflerCsc` | def | Statement |
| `mittag_leffler_csc_proved` | thm | Full proof |

---

## B4. Hilbert Inequality Rescaling

**File:** `EM/IK/Ch7Hilbert.lean` (~50 lines)

Reduction of the `δ`-separated Hilbert inequality to the `1`-separated case by
`λ_r ↦ λ_r/δ`.

| Identifier | Description |
|---|---|
| `hilbert_rescale` | `HilbertInequality1 → HilbertInequality` |
| `hilbert1_implies_hilbert` | Same reduction, alternate name |

---

## B5. Cesàro Convergence of Cross Terms (Product-Index Trick)

**File:** `EM/IK/Ch7CesaroChain.lean` (~490 lines)

Lift `R` points on `ℝ/ℤ` to `R·(2K+1)` points on `ℝ` and show the cross terms converge in
the Cesàro sense to `π·csc(π(α_r − α_s))`. Infrastructure for IK Corollaries 7.9–7.10.

| Identifier | Kind | Description |
|---|---|---|
| `CrossRCesaroConvergence` | def | Statement |
| `cross_r_cesaro_convergence_proved` | thm | Full proof |

*(`same_r_antisymmetry` and `hilbert_lifted_bound` in the same file are `private`.)*

---

## B6. One-Sided Tauberian Lemma and L-series Bounds for Residue Classes

**File:** `EM/IK/Tauberian.lean`

For `bₙ ≥ 0`, `∑_{n≤N} bₙ ≤ N^ε · ∑_n bₙ/n^ε` for every `ε > 0`. Elementary, and the key
one-sided bound reducing `WeightedPNTinAP` to a real-variable Wiener–Ikehara hypothesis.

Separately: Mathlib's `PrimesInAP.lean` proves a *lower* bound on
`∑ Λ(n)·1_{n≡a}/n^x` near `x = 1` (`LSeries_residueClass_lower_bound`) but does not export
the matching *upper* bound. These extract the identity from Mathlib's own proof and derive
both.

| Identifier | Description |
|---|---|
| `one_sided_tauberian_upper` | `∑_{n≤N} bₙ ≤ N^ε · ∑_n bₙ/n^ε` |
| `one_sided_tauberian_dirichlet` | Applied to Dirichlet series |
| `residueClass_tsum_eq_aux_plus_pole` | `tsum = aux.re + pole` |
| `residueClass_tsum_upper_bound` | Upper bound |
| `residueClass_tsum_both_bounds` | Two-sided |

---

## B7. Exponential Sum Estimates — **partially superseded**

**File:** `EM/LargeSieve/Analytic.lean`

> **Correction.** An earlier version of this file claimed Jordan's inequality was missing
> from Mathlib. It is **not**: `Real.mul_le_sin` in
> `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean` gives
> `2/π · x ≤ sin x` on `[0, π/2]`, from which `sin_pi_ge_two_mul` follows by
> `x = πt`. That entry is withdrawn.

What remains genuinely absent is the geometric-sum bound built on it, which is the estimate
actually used throughout analytic number theory:

| Identifier | Description |
|---|---|
| `norm_one_sub_eAN` | `‖1 − e(β)‖ = 2·\|sin(πβ)\|` |
| `norm_eAN_geom_sum_le_inv` | `‖∑_{k<K} e(kβ)‖ ≤ 1/(2δ)` for `β` at distance `≥ δ` from `ℤ` |

---

## B8. Discrete Abel Summation — **superseded, withdrawn**

> **Correction.** An earlier version claimed summation by parts was "not in Mathlib as a
> standalone lemma". It is: `Finset.sum_range_by_parts` (with `sum_Ico_by_parts` and
> `sum_Ioc_by_parts`) in `Mathlib/Algebra/BigOperators/Module.lean`, stated in the general
> module setting. The EM version (`discrete_abel` in `EM/IK/AbelChain.lean`) is a `private`
> real-valued specialisation and should be replaced by Mathlib's, not contributed.

---

## B9. Log-Log Integrals via FTC

**File:** `EM/IK/AbelChain.lean` (~80 lines)

| Identifier | Description |
|---|---|
| `hasDerivAt_log_log` | `d/dt[log(log t)] = 1/(t·log t)` for `t > 1` |
| `hasDerivAt_neg_inv_log` | `d/dt[−(log t)⁻¹] = (t·(log t)²)⁻¹` |
| `integral_inv_mul_log` | `∫_a^b 1/(t·log t) dt = log log b − log log a` |
| `integral_inv_mul_log_sq` | `∫_a^b 1/(t·(log t)²) dt = 1/log a − 1/log b` |
| `log_ratio_le`, `loglog_le_ratio` | Sandwich between log-log differences and log ratios |

---

## B10. Infinite Product Contraction (Divergent Series ⇒ Vanishing Product)

**Files:** `EM/Stochastic/VanishingNoise.lean`, `EM/Stochastic/VanishingNoiseC.lean`

For `γ_k ∈ (0,1]` with `∑ γ_k = ∞`: `∏_{k<N} (1 − γ_k) → 0`. Standard (Rudin,
*Principles* 15.5); used in Borel–Cantelli, mixing, and Euler products. A **sparse
variant** relaxes to `0 ≤ a_k ≤ 1`, which is the form sieve applications need (most terms
contribute gap `0`).

| Identifier | File | Description |
|---|---|---|
| `product_contraction_tendsto` | `VanishingNoise.lean` | `γ_k ∈ (0,1]`, `∑ γ_k = ∞` ⟹ `∏(1 − γ_k) → 0` |
| `sparse_product_contraction` | `VanishingNoiseC.lean` | `a_k ∈ [0,1]`, `¬Summable(1 − a_k)` ⟹ `∏ a_k → 0` |

---

## B11. Divergence of Prime Reciprocals in Arithmetic Progressions

**File:** `EM/IK/DirichletDensity.lean`

For `2 ≤ q` and any unit class `a : ZMod q`, `∑ 1/p` over primes `p ≡ a (mod q)` is not
summable. Mathlib has the `Λ`-weighted analogue
(`ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div`), which does **not**
imply this — the weighting goes the wrong way.

The proof runs the classical Dirichlet-density argument: Euler-log split with a uniform
prime-power tail bound, character orthogonality, principal-character divergence from
`Nat.Primes.not_summable_one_div`, and boundedness of `∑ χ(p) p^{−σ}` as `σ → 1⁺` for
`χ ≠ 1` via `LFunction_ne_zero_of_one_le_re` plus path-lifting through
`Complex.isCoveringMap_exp` (no hand-rolled branch tracking). Self-contained over Mathlib.

Natural home: `Mathlib/NumberTheory/LSeries/PrimesInAP.lean`.

| Identifier | Description |
|---|---|
| `prime_reciprocal_class_divergent` | `∑_{p ≡ a (q)} 1/p` diverges |

---

## B12. Coprimality Counts Along an Affine Progression

**File:** `EM/ForMathlib/CoprimeAffineBlock.lean` (Mathlib-only; extracted 2026-08-18; Mathlib-style name `Nat.card_filter_coprime_Ico_affine`)

Mathlib's `Nat.filter_coprime_Ico_eq_totient` counts `t ∈ [k, k+N)` coprime to `N`.  The form
one needs for sieving an arithmetic progression is the same count for `a·t + b` with
`Coprime a N`:

```
#{t ∈ [k, k+N) : Coprime N (a·t + b)} = φ N,      #{t ∈ [k, k+B·N) : …} = B · φ N.
```

Proof: periodicity (`Nat.filter_Ico_card_eq_of_periodic`) plus `t ↦ (a t + b) mod N` being a
bijection of `range N` (injectivity in `ZMod N`, then cardinality).

| Identifier | Description |
|---|---|
| `BagConditionedLaw.coprime_mod_iff` | `Coprime N (x % N) ↔ Coprime N x` |
| `BagConditionedLaw.card_coprime_affine_block` | One block |
| `BagConditionedLaw.card_coprime_affine_blocks` | `B` blocks |

---

## B13. Density of `{m : minFac m = p}` and Head Domination

**File:** `EM/Population/HeadDomination.lean`

For a prime `p`, the natural density of `{m : Nat.minFac m = p}` is
`w_p = (1/p)∏_{r<p}(1−1/r)`, with two-sided counting bounds and the telescoping
`w_p = c(p) − c(p+1)`, `c(n) = ∏_{r<n}(1−1/r) → 0`, so `∑_p w_p = 1` (`HasSum`).  Nothing in
Mathlib counts integers by least prime factor.

| Identifier | Description |
|---|---|
| `HeadDomination.totient_prod_primes` | `φ(∏_{r∈s} r) = ∏_{r∈s}(r−1)` for a finset of primes |
| `HeadDomination.card_minFac_eq_ge`, `…_le` | `⌊X/(pN)⌋·φ(N) ≤ #{m ≤ X : minFac m = p} ≤ (⌊X/(pN)⌋+1)·φ(N)` |
| `HeadDomination.w_eq_cfun_sub` | `w_p = c(p) − c(p+1)` |
| `HeadDomination.cfun_tendsto_zero` | `∏_{r<n}(1−1/r) → 0` (from `Nat.Primes.not_summable_one_div`) |
| `HeadDomination.hasSum_wq` | `∑_{p>q} w_p = c(q+1)` |
| `HeadDomination.tendsto_classCount_div` | Density of `{minFac ≡ a (q)}` among `q`-rough integers is `∑_{p≡a} w_p` |

Companion, on a progression (`EM/Population/BagConditionedLaw.lean`):
`BagConditionedLaw.tendsto_bagClass_div_ap` — among `m ≡ 1 (mod P)`, `minFac m = p` (for
`p ∤ P`) has relative density `(1/p)∏_{r<p, r∤P}(1−1/r)`.

---

## B14. Periodic Events Have Natural Density Equal to Their Period Fraction

**File:** `EM/ForMathlib/PeriodicDensity.lean` (Mathlib-only imports; added 2026-08-19)

If membership in a set of naturals depends only on the residue mod `M`, its upper natural
density is the fraction of residues in one period. Elementary block counting, but it is the
step every "density of an `M`-periodic condition" argument needs, and Mathlib states it
nowhere.

| Identifier | Description |
|---|---|
| `PeriodicDensity.periodRep` | Representative of `m` in `[1, M]` (`M` in place of `0`) |
| `PeriodicDensity.periodRep_modEq`, `…_mem_Ico`, `…_eq_self` | Its basic API |
| `PeriodicDensity.card_fiber_le` | Fibre count over one block |
| `PeriodicDensity.eventually_density_le` | `#{m ≤ X : P m}/X ≤ #T/M + o(1)` for `M`-periodic `P` |
| `PeriodicDensity.limsup_density_le` | `limsup` form |

---

## B15. Finite-Tree Exponential Supermartingale and Chernoff Lower Tail

**File:** `EM/Population/TreeChernoff.lean` (Mathlib-only imports)

A self-contained Chernoff bound on a finite sample space with a refinement filtration, in
the form one needs when the per-step success probabilities are only bounded *conditionally*
rather than independent: given a refining family `F k`, events `A k` measurable for it, and
a conditional lower bound `hcond` on each step's success weight, the number of successes is
below a quarter of its compensator with exponentially small probability. Proved by backward
induction on the tree; no measure theory and no independence.

Mathlib has Hoeffding/Chernoff material only for genuinely independent families
(`Mathlib/Probability/Moments/`), so the conditional/filtration form is absent. Offered as a
generic engine rather than as number theory.

| Identifier | Description |
|---|---|
| `TreeChernoff.theta`, `exp_neg_eq_one_sub_theta` | The `1 − e^{−λ}` change of variable |
| `TreeChernoff.chernoff_bound` | General bound |
| `TreeChernoff.chernoff_quarter` | The quarter-of-compensator form |
| `TreeChernoff.chernoff_bound_of_dominating`, `chernoff_quarter_of_dominating` | Domination variants |
| `TreeChernoff.chernoff_quarter_local` | Localized variant (bad set intersected with `{v ≤ compensator}`), which avoids a stopped supermartingale |

---

# Tier C — small facts, cheap either way

Listed for completeness; each is a few lines, and a reviewer may reasonably prefer to
reprove rather than port.

| # | Identifier | File | Statement |
|---|---|---|---|
| C1 | `minFac_mul_eq_min` | `EM/Meta/MarkovSieve.lean` | `Nat.minFac (n*m) = min (minFac n) (minFac m)` for `n, m > 1`; no coprimality needed |
| C2 | `minFac_not_multiplicative` | `EM/Meta/MarkovSieve.lean` | Counterexample: `minFac` is not multiplicative (`6 × 35`) |
| C3 | `eq_of_same_primeFactors_squarefree` | `EM/Stochastic/TreeSieveDecay.lean` | Squarefree + same prime factors ⟹ equal |
| C4 | `norm_sq_partial_sum_telescoping` | `EM/Reduction/DSLInfra.lean` | `‖∑_{k<N} z_k‖² = ∑‖z_k‖² + 2∑⟪∑_{j<k} z_j, z_k⟫` in an inner product space |
| C5 | `group_walk_doubly_stochastic` | `EM/Reduction/SelfCorrecting.lean` | Uniform multiplier on a finite group ⟹ doubly stochastic transitions |
| C6 | `prime_pow_ne_prime_pow`, `log_ratio_irrational` | `EM/Meta/LFunction.lean` | `log p / log q ∉ ℚ` for distinct primes |
| C7 | `sieveDensity` + 5 lemmas | `EM/Reduction/ShiftedDensity.lean` | `g(r) = r/(r²−1)`: partial fractions, `1/r < g(r) < 1/(r−1)`, strict antitonicity, exact correction `g(r) − 1/r = 1/(r(r²−1))` |

---

## Not yet extracted

One pattern that recurs in `EM/Population/DefectTelescope.lean` looks Mathlib-worthy but is
currently inlined rather than stated separately:

> A sequence that is **antitone up to a summable error** — `u_{n+1} ≤ u_n + e_n` with
> `∑ e_n < ∞` — and bounded below, converges.

Mathlib has monotone convergence (`tendsto_atTop_ciInf`) but not this perturbed form, which
is what one actually meets when a recursion is monotone only approximately. Offered as a
suggestion rather than a contribution: it would need extracting from the surrounding
argument first.
