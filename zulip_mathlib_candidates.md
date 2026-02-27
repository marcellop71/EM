# Results from the Euclid-Mullin formalization that could be interesting for Mathlib

The repository [EM](https://github.com/mparis-est/EM) (~28,800 lines, 32 files, zero sorry) is a Lean 4 formalization trying to understand the Mullin conjecture.
Along the way it developed some general-purpose mathematics that is not specific to the Euclid-Mullin sequence
and that could be of independent interest.
Below is a curated list of results organized by topic.

---

## Summary table

| # | Name | File | Line | Kind | Description |
|---|------|------|------|------|-------------|
| | **Large sieve infrastructure** | | | | |
| 1 | `complex_cauchy_schwarz` | `IKCh7.lean` | 103 | thm | Cauchy-Schwarz for complex finite sums: `‖∑ f·g‖² ≤ (∑ ‖f‖²)(∑ ‖g‖²)` |
| 2 | `cauchy_schwarz_bilinear` | `IKCh7.lean` | 120 | thm | Cauchy-Schwarz for bilinear forms: `‖Ψ(α,β)‖² ≤ ‖α‖² · ∑ ‖∑ β_n φ(m,n)‖²` |
| 3 | `duality_principle` | `IKCh7.lean` | 143 | thm | Duality principle: forward and dual large sieve have the same constant |
| 4 | `schur_quadratic_form_bound` | `IKCh7.lean` | 452 | thm | Schur test (diag/off-diag): `‖b*Gb‖ ≤ (D+(R−1)B)·‖b‖²` |
| 5 | `off_diag_sum_le` | `IKCh7.lean` | 413 | thm | Off-diagonal inequality: `∑_{i≠j} wᵢwⱼ ≤ (R−1)·∑ wᵢ²` |
| 6 | `row_sum_schur_bound` | `IKCh7.lean` | 541 | thm | Schur test (row-sum version): `‖b*Gb‖ ≤ C·‖b‖²` |
| 7 | `abs_schur_bound` | `LargeSieveHarmonic.lean` | 773 | thm | Schur test with row+column sum bounds |
| 8 | `norm_sq_sum_le_card_mul_sum_norm_sq` | `IKCh7.lean` | 1834 | thm | `‖∑ vᵢ‖² ≤ |s|·∑ ‖vᵢ‖²` for complex sums over `Finset` |
| 9 | `kernel_row_sum_implies_als` | `LargeSieveHarmonic.lean` | 865 | thm | Trigonometric kernel bound implies analytic large sieve |
| 10 | `als_implies_prime_arith_ls` | `LargeSieveAnalytic.lean` | 1358 | thm | Analytic large sieve implies prime arithmetic large sieve |
| | **Van der Corput** | | | | |
| 11 | `VanDerCorputBound` | `LargeSieveSpectral.lean` | 557 | def | Statement of the finite Van der Corput inequality |
| 12 | `van_der_corput_bound` | `LargeSieveSpectral.lean` | 591 | thm | Proof: `‖∑ f(n)‖² ≤ 2N²/(H+1) + 2δN²` (~280 lines) |
| | **Harmonic analysis on finite groups** | | | | |
| 13 | `zmod_dft_parseval` | `LargeSieveHarmonic.lean` | 135 | thm | Parseval for `ZMod.dft`: `∑ ‖𝓕Φ(k)‖² = N·∑ ‖Φ(j)‖²` |
| 14 | `zmod_dft_plancherel_complex` | `LargeSieveHarmonic.lean` | 416 | thm | Plancherel (bilinear Parseval) for `ZMod.dft` |
| 15 | `char_parseval_units` | `LargeSieveAnalytic.lean` | 809 | thm | Parseval for `(ℤ/pℤ)ˣ` characters: `∑_χ ‖∑ g·χ‖² = (p−1)·∑ ‖g‖²` |
| 16 | `nontrivial_char_parseval_le` | `IKCh7.lean` | 1128 | thm | Same, restricted to nontrivial characters (inequality) |
| 17 | `weyl_criterion_finite_group` | `LargeSieveSpectral.lean` | 411 | thm | Finite Weyl criterion: small char sums ⟹ equidistribution |
| 18 | `stdAddChar_sum_eq` | `LargeSieveHarmonic.lean` | 71 | lem | Additive character orthogonality on `ZMod N` |
| 19 | `walk_energy_parseval` | `LargeSieveSpectral.lean` | 89 | thm | Character energy = `(p−1)·∑ V(a)²` for sequences in `(ℤ/pℤ)ˣ` |
| 20 | `visit_energy_lower_bound` | `LargeSieveSpectral.lean` | 104 | thm | Cauchy-Schwarz: `∑ V(a)² ≥ N²/(p−1)` |
| | **Gauss sums** | | | | |
| 21 | `gaussSum_norm_sq_eq_prime` | `LargeSieveHarmonic.lean` | 388 | thm | `‖τ(χ)‖² = p` for nontrivial `χ` mod `p` |
| 22 | `gaussSum_conj_eq` | `LargeSieveHarmonic.lean` | 366 | thm | `conj(τ(χ,ψ)) = τ(χ⁻¹,ψ⁻¹)` |
| 23 | `gaussSum_stdAddChar_ne_zero` | `LargeSieveAnalytic.lean` | 255 | thm | `τ(χ) ≠ 0` for nontrivial `χ` on `ZMod p` |
| 24 | `gauss_sum_inversion` | `LargeSieveAnalytic.lean` | 268 | thm | `χ(a) = τ(χ⁻¹)⁻¹·τ(χ⁻¹,ψ_a)` |
| 25 | `char_sum_to_exp_sum` | `LargeSieveAnalytic.lean` | 304 | thm | Gauss conductor transfer: char sums → exponential sums |
| 26 | `isPrimitive_of_prime_nontrivial` | `LargeSieveAnalytic.lean` | 206 | thm | Nontrivial characters at prime level are primitive |
| 27 | `mulChar_norm_one_of_unit` | `LargeSieveHarmonic.lean` | 333 | lem | Multiplicative character values on units have norm 1 |
| 28 | `mulChar_conj_eq_inv` | `LargeSieveHarmonic.lean` | 349 | lem | `conj(χ(a)) = χ⁻¹(a)` for units |
| | **Number-theoretic exponential `e(α) = exp(2πiα)`** | | | | |
| 29 | `eAN` | `LargeSieveHarmonic.lean` | 528 | def | Definition of `e(α) = exp(2πiα)` |
| 30 | `eAN_zero` | `LargeSieveHarmonic.lean` | 532 | thm | `e(0) = 1` |
| 31 | `eAN_add` | `LargeSieveHarmonic.lean` | 536 | thm | `e(α+β) = e(α)·e(β)` |
| 32 | `eAN_neg` | `LargeSieveHarmonic.lean` | 547 | thm | `e(−α) = conj(e(α))` |
| 33 | `eAN_norm` | `LargeSieveHarmonic.lean` | 557 | thm | `‖e(α)‖ = 1` |
| 34 | `eAN_intCast` | `LargeSieveHarmonic.lean` | 561 | thm | `e(n) = 1` for `n : ℤ` |
| 35 | `eAN_ne_zero` | `LargeSieveHarmonic.lean` | 568 | thm | `e(α) ≠ 0` |
| 36 | `eAN_mul_conj` | `LargeSieveHarmonic.lean` | 572 | thm | `e(α)·conj(e(α)) = 1` |
| 37 | `norm_one_sub_eAN` | `LargeSieveAnalytic.lean` | 79 | thm | `‖1 − e(β)‖ = 2·|sin(πβ)|` |
| 38 | `norm_eAN_sub_one` | `LargeSieveAnalytic.lean` | 94 | thm | `‖e(β) − 1‖ = 2·|sin(πβ)|` |
| 39 | `eAN_geom_sum_mul` | `LargeSieveAnalytic.lean` | 49 | thm | `(∑ e(kβ))·(e(β)−1) = e(Nβ)−1` |
| 40 | `eAN_geom_sum_eq` | `LargeSieveAnalytic.lean` | 62 | thm | Closed form of geometric sum of `e(kβ)` |
| 41 | `norm_eAN_geom_sum_le` | `LargeSieveAnalytic.lean` | 68 | thm | `‖∑ e(kβ)‖ ≤ 2/‖e(β)−1‖` |
| 42 | `sin_pi_ge_two_mul` | `LargeSieveAnalytic.lean` | 102 | thm | Jordan's inequality: `sin(πt) ≥ 2t` for `t ∈ [0,½]` |
| 43 | `abs_sin_pi_ge_two_frac` | `LargeSieveAnalytic.lean` | 122 | thm | `|sin(πβ)| ≥ 2·|β − round(β)|` |
| 44 | `norm_eAN_geom_sum_le_inv` | `LargeSieveAnalytic.lean` | 152 | thm | `‖∑ e(kβ)‖ ≤ 1/(2δ)` when β is δ-separated from ℤ |
| | **Farey spacing** | | | | |
| 45 | `FareySpacing` | `LargeSieve.lean` | 601 | def | Statement: `|a/q − a'/q'| ≥ 1/Q²` for distinct fractions |
| 46 | `farey_spacing_proved` | `LargeSieve.lean` | 613 | thm | Proof of Farey spacing |
| | **Arithmetic functions** | | | | |
| 47 | `IsAdditiveFunction` | `IKCh1.lean` | 52 | def | Additive arithmetic function predicate |
| 48 | `IsCompletelyAdditiveFunction` | `IKCh1.lean` | 57 | def | Completely additive arithmetic function predicate |
| 49 | `IsCompletelyMultiplicative` | `IKCh1.lean` | 62 | def | Completely multiplicative predicate (all m,n, not just coprime) |
| 50 | `liouville` | `IKCh1.lean` | 172 | def | Liouville function `λ(n) = (−1)^{Ω(n)}` |
| 51 | `liouville_apply_prime` | `IKCh1.lean` | 181 | thm | `λ(p) = −1` |
| 52 | `liouville_apply_prime_pow` | `IKCh1.lean` | 184 | thm | `λ(p^k) = (−1)^k` |
| 53 | `liouville_isCompletelyMultiplicative` | `IKCh1.lean` | 191 | thm | Liouville function is completely multiplicative |
| 54 | `liouville_eq_moebius_of_squarefree` | `IKCh1.lean` | 200 | thm | `λ(n) = μ(n)` for squarefree `n` |
| 55 | `EulerPhiOverN` | `IKCh1.lean` | 206 | def | `φ(n)/n = ∑_{d∣n} μ(d)/d` |
| 56 | `eChar` | `IKCh1.lean` | 219 | def | Standard additive character `e(x) = exp(2πix)` |
| 57 | `ramanujanSum` | `IKCh1.lean` | 230 | def | Ramanujan sum `c_q(n) = ∑_{(a,q)=1} e(an/q)` |
| 58 | `RamanujanSumFormula` | `IKCh1.lean` | 241 | def | Möbius expansion of Ramanujan sums |
| 59 | `kloostermanSum` | `IKCh1.lean` | 247 | def | Kloosterman sum `S(a,b;c)` |
| 60 | `KloostermanSymmetric` | `IKCh1.lean` | 254 | def | `S(a,b;c) = S(b,a;c)` |
| 61 | `summatoryFunction` | `IKCh1.lean` | 278 | def | Summatory function `M_f(x) = ∑_{n≤x} f(n)` |
| | **Elementary prime number theory (IK Ch. 2)** | | | | |
| 62 | `mobiusSummatory` | `IKCh2.lean` | 38 | def | Möbius summatory function `M(x) = ∑_{m≤x} μ(m)` |
| 63 | `MobiusFloorIdentity` | `IKCh2.lean` | 154 | def | `∑_{m≤x} μ(m)⌊x/m⌋ = 1` |
| 64 | `MobiusReciprocalBound` | `IKCh2.lean` | 159 | def | `|∑_{m≤x} μ(m)/m| ≤ 1` |
| 65 | `vonMangoldtK` | `IKCh2.lean` | 208 | def | Higher von Mangoldt function `Λ_k = μ ∗ (log)^k` |
| | **Summation and special functions (IK Ch. 4)** | | | | |
| 66 | `sawtooth` | `IKCh4.lean` | 54 | def | Sawtooth `ψ(x) = frac(x) − ½` |
| 67 | `periodicBernoulli` | `IKCh4.lean` | 65 | def | Periodic Bernoulli function `B_k({x})` |
| 68 | `JacobiThetaTransformation` | `IKCh4.lean` | 172 | def | Jacobi theta transformation `θ(1/y) = √y·θ(y)` |
| 69 | `rootNumber` | `IKCh4.lean` | 387 | def | Root number `ε(χ) = i^{−κ}·τ(χ)/√q` |
| 70 | `fejerKernel` | `IKCh4.lean` | 456 | def | Fejér kernel |
| 71 | `dirichletKernel` | `IKCh4.lean` | 462 | def | Dirichlet kernel |
| 72 | `mellinTransform` | `IKCh4.lean` | 501 | def | Mellin transform `M(f)(s) = ∫₀^∞ f(y)y^{s−1} dy` |
| | **L-function framework (IK Ch. 5)** | | | | |
| 73 | `LFunctionData` | `IKCh5.lean` | 58 | struct | Axiomatic L-function structure (Selberg class) |
| 74 | `shimura_vanishing` | `IKCh5.lean` | 141 | thm | Root number `−1` ⟹ `L(f,½) = 0` |
| | **Rotor-router theory** | | | | |
| 75 | `RotorState` | `RotorRouter.lean` | 26 | struct | Rotor state: position + rotor pointers |
| 76 | `rotorStep` | `RotorRouter.lean` | 32 | def | Single rotor-router step |
| 77 | `rotorRun` | `RotorRouter.lean` | 37 | def | n-step rotor-router iteration |
| 78 | `eventually_periodic` | `RotorRouter.lean` | 79 | thm | Every orbit of `f : α → α` on `[Finite α]` is eventually periodic |
| 79 | `periodic_of_eq` | `RotorRouter.lean` | 85 | thm | Period propagation: periodicity at μ extends to all n ≥ μ |
| 80 | `rotor_tracks_visits` | `RotorRouter.lean` | 151 | thm | Rotor pointer = (initial + visit count) mod k |
| 81 | `visit_count_dvd_of_periodic` | `RotorRouter.lean` | 167 | thm | Over one period, `k ∣ visitCount(x)` |
| 82 | `visited_closed_under_gens` | `RotorRouter.lean` | 237 | thm | Visited set in one period is closed under generators |
| 83 | `rotor_visits_all` | `RotorRouter.lean` | 328 | thm | Rotor-router on finite group visits every element |
| 84 | `rotor_visits_all_infinitely` | `RotorRouter.lean` | 338 | thm | …and visits every element infinitely often |
| 85 | `scheduled_walk_covers_all` | `RotorRouter.lean` | 395 | thm | Any pointwise-recurrent walk on a finite group covers all elements |
| | **Discrete dynamics / combinatorics** | | | | |
| 86 | `exists_lt_map_eq` | `RotorRouter.lean` | 69 | thm | Ordered pigeonhole: `∃ m < n, f m = f n` for `[Finite α]` |
| 87 | `exists_visits_inf_often` | `RotorRouter.lean` | 384 | thm | Sequence in finite type visits some value infinitely often |
| 88 | `cofinal_pigeonhole` | `EquidistPreamble.lean` | 152 | thm | Cofinal pigeonhole into finitely many buckets |
| 89 | `submonoid_closure_subset_of_mul_closed` | `RotorRouter.lean` | 211 | thm | Right-induction principle for submonoid closure |
| 90 | `mem_submonoid_closure_of_subgroup_top` | `RotorRouter.lean` | 205 | thm | In finite group: subgroup gen = top ⟹ submonoid gen = top |
| | **Multiplicative walks on groups** | | | | |
| 91 | `subgroup_trapping` | `MullinDepartureGraph.lean` | 55 | thm | Walk in H ⟹ multipliers in H |
| 92 | `generation_escapes_subgroup` | `MullinDepartureGraph.lean` | 79 | thm | Generating multipliers force walk out of proper subgroups |
| 93 | `walk_in_coset_closure` | `MullinDepartureGraph.lean` | 167 | thm | `w(k) ∈ w(0)·closure(range m)` |
| 94 | `walk_hits_target_iff` | `MullinDepartureGraph.lean` | 493 | thm | `w(k+1) = t ↔ m(k) = w(k)⁻¹·t` |
| 95 | `closure_compl_singleton_eq_top` | `MullinDepartureGraph.lean` | 408 | thm | `G \ {g}` generates `G` when `|G| ≥ 3` |
| 96 | `card_subgroup_of_order_two_mul_prime` | `MullinDepartureGraph.lean` | 338 | thm | Subgroup orders in a group of order 2p |
| | **Finite group theory** | | | | |
| 97 | `not_mem_proper_subgroup_of_full_order` | `MullinGroupEscape.lean` | 579 | thm | `orderOf g = |G| ⟹ g ∉ H` for proper `H` |
| 98 | `pow_card_subgroup_eq_one` | `MullinGroupQR.lean` | 540 | thm | `g ∈ H ⟹ g^|H| = 1` (Lagrange for subgroups) |
| 99 | `gordon_sequenceable` | `MullinGroupPumping.lean` | 316 | thm | Gordon's theorem: `ℤ/(2m)ℤ` is sequenceable (first formalization) |
| | **Quadratic residues** | | | | |
| 100 | `neg_one_pow_half_eq_one` | `MullinGroupQR.lean` | 42 | thm | `q ≡ 1 (mod 4) ⟹ (−1)^{q/2} = 1` |
| 101 | `neg_one_pow_half_eq_neg_one'` | `MullinGroupQR.lean` | 49 | thm | `q ≡ 3 (mod 4) ⟹ (−1)^{q/2} = −1` |
| 102 | `neg_one_pow_odd_mul` | `MullinGroupQR.lean` | 56 | thm | `m odd ⟹ (−1)^{mn} = (−1)^n` |
| 103 | `legendreSym_three_eq_neg_one` | `MullinGroupQR.lean` | 96 | thm | `(3∣q) = −1` iff `q ∉ {±1} mod 12` |
| 104 | `legendreSym_five_eq_neg_one` | `MullinGroupQR.lean` | 131 | thm | `(5∣q) = −1` iff `q ∉ {±1} mod 5` |
| 105 | `legendreSym_seven_eq_neg_one` | `MullinGroupQR.lean` | 209 | thm | `(7∣q) = −1` via conditions mod 28 |
| 106 | `legendreSym_thirteen_eq_neg_one` | `MullinGroupQR.lean` | 235 | thm | `(13∣q) = −1` via conditions mod 13 |
| 107 | `legendreSym_fortythree_eq_neg_one_mod4_1` | `MullinGroupQR.lean` | 303 | thm | `(43∣q) = −1` when `q ≡ 1 (mod 4)` |
| 108 | `legendreSym_fortythree_eq_neg_one_mod4_3` | `MullinGroupQR.lean` | 334 | thm | `(43∣q) = −1` when `q ≡ 3 (mod 4)` |
| 109 | `legendreSym_fiftythree_eq_neg_one` | `MullinGroupQR.lean` | 264 | thm | `(53∣q) = −1` via conditions mod 53 |
| | **CRT and ZMod API** | | | | |
| 110 | `crt_pair_surjective` | `CRTFiberIndependence.lean` | 126 | thm | CRT: lift `(a mod p, b mod q)` to `ℤ` for distinct primes |
| 111 | `crt_unit_pair_surjective` | `CRTFiberIndependence.lean` | 200 | thm | CRT for unit pairs |
| 112 | `dvd_independent_of_residue` | `CRTFiberIndependence.lean` | 184 | thm | `∃ x, x ≡ c (mod q) ∧ p ∣ x+1` for distinct primes p, q |
| | **Elementary number theory** | | | | |
| 113 | `not_dvd_consec` | `MullinConjectures.lean` | 91 | thm | `p ≥ 2` cannot divide two consecutive naturals |
| 114 | `dvd_succ_iff_mod_pred` | `MullinResidueWalk.lean` | 30 | thm | `q ∣ a+1 ↔ a % q = q−1` |
| 115 | `dvd_two_mul_prime_iff` | `MullinDepartureGraph.lean` | 313 | thm | Divisors of `2p` (p odd prime) are `{1, 2, p, 2p}` |
| 116 | `prime_residue_escape` | `EquidistBootstrap.lean` | 211 | thm | Small primes generate `(ℤ/pℤ)ˣ` for `p ≥ 5` |
| | **Inequalities** | | | | |
| 117 | `sum_sq_le_bound_mul_sum` | `ExcursionIndependence.lean` | 182 | thm | `∑ xᵢ² ≤ M·∑ xᵢ` when `0 ≤ xᵢ ≤ M` |
| 118 | `finset_markov_inequality` | `LargeSieve.lean` | 551 | thm | Discrete Markov: `|{i : f(i) > T}|·T ≤ B` |
| 119 | `finset_markov_card_bound` | `LargeSieve.lean` | 576 | thm | `|{i : f(i) > T}| ≤ B/T` |
| 120 | `norm_sub_one_sq_eq` | `LargeSieveSpectral.lean` | 2014 | thm | `‖z−1‖² = 2−2·Re(z)` for `‖z‖ = 1` |
| 121 | `unit_norm_re_le_of_dist` | `LargeSieveSpectral.lean` | 2027 | thm | `‖z‖=1, ‖z−1‖≥η₀ ⟹ Re(z) ≤ 1−η₀²/2` |
| | **Open Prop definitions (statements only)** | | | | |
| 122 | `AnalyticLargeSieve` | `LargeSieve.lean` | 51 | def | Montgomery-Vaughan ALS with sharp constant |
| 123 | `ArithmeticLargeSieve` | `LargeSieve.lean` | 75 | def | Arithmetic large sieve for Dirichlet characters |
| 124 | `BombieriVinogradov` | `LargeSieve.lean` | 98 | def | Bombieri-Vinogradov theorem |
| 125 | `JacobiThetaTransformation` | `IKCh4.lean` | 172 | def | `θ(1/y) = √y·θ(y)` |
| 126 | `GrandRiemannHypothesis` | `IKCh5.lean` | 446 | def | GRH for general L-functions |

---

### 1. Analytic Number Theory: Large Sieve Infrastructure

**File: `IKCh7.lean`, `LargeSieveHarmonic.lean`, `LargeSieveAnalytic.lean`, `LargeSieveSpectral.lean`**

These files formalize key parts of Chapter 7 of Iwaniec-Kowalski and develop the large sieve from scratch.

- **Cauchy-Schwarz for complex finite sums** (`complex_cauchy_schwarz`, `IKCh7.lean:103`): `‖∑ m, f m * g m‖ ^ 2 ≤ (∑ m, ‖f m‖ ^ 2) * (∑ m, ‖g m‖ ^ 2)` for `f g : Fin M → ℂ`. Mathlib has the real version via `Finset.inner_mul_le_norm_mul_sq` but this direct complex finite-sum form is missing.

- **Cauchy-Schwarz for bilinear forms** (`cauchy_schwarz_bilinear`, `IKCh7.lean:120`): `‖Ψ(α, β)‖² ≤ ‖α‖² · ∑_m ‖∑_n β_n φ(m,n)‖²`. The key step for deriving operator norm bounds.

- **Duality principle for bilinear forms** (`duality_principle`, `IKCh7.lean:143`): If the "forward" large sieve bound holds with constant Δ, so does the "dual" bound, with the same constant. A structural result about bilinear forms.

- **Schur test (row-sum version)** (`row_sum_schur_bound`, `IKCh7.lean:541`; also `abs_schur_bound`, `LargeSieveHarmonic.lean:773`): For a norm-symmetric matrix with row sums bounded by C, the Hermitian quadratic form satisfies `|b* G b| ≤ C · ‖b‖²`. The classical Schur test for bounding operator norms.

- **Schur test (diagonal/off-diagonal version)** (`schur_quadratic_form_bound`, `IKCh7.lean:452`): `‖b* G b‖ ≤ (D + (R−1)·B) · ‖b‖²` where D bounds diagonal norms and B bounds off-diagonal norms.

- **Off-diagonal sum inequality** (`off_diag_sum_le`, `IKCh7.lean:413`): `∑_{i≠j} w_i w_j ≤ (R−1) · ∑_i w_i²` for nonneg reals.

- **`‖∑ v_i‖² ≤ |s| · ∑ ‖v_i‖²`** (`norm_sq_sum_le_card_mul_sum_norm_sq`, `IKCh7.lean:1834`): Cauchy-Schwarz for norms of sums over arbitrary `Finset`, for complex-valued functions.

- **Kernel row-sum implies ALS** (`kernel_row_sum_implies_als`, `LargeSieveHarmonic.lean:865`): The standard proof strategy: once the trigonometric kernel bound is established, the analytic large sieve follows via the bilinear expansion + Schur test.

- **ALS implies prime arithmetic large sieve** (`als_implies_prime_arith_ls`, `LargeSieveAnalytic.lean:1358`): The reduction from the analytic to the arithmetic large sieve for prime moduli, via Gauss expansion and uniform well-separation.

---

### 2. Van der Corput Inequality

**File: `LargeSieveSpectral.lean:591`**

- **Finite Van der Corput bound** (`van_der_corput_bound`): For a bounded sequence `f` with autocorrelations `|R_h| ≤ δN` for lags `1 ≤ h ≤ H`: `‖∑_{n<N} f(n)‖² ≤ 2N²/(H+1) + 2δN²`. This is a ~280-line fully proved theorem, one of the most important techniques in analytic number theory for bounding exponential/character sums. Not in Mathlib.

---

### 3. Harmonic Analysis on Finite Groups

**File: `LargeSieveHarmonic.lean`, `LargeSieveAnalytic.lean`, `LargeSieveSpectral.lean`**

- **Parseval identity for `ZMod.dft`** (`zmod_dft_parseval`, `LargeSieveHarmonic.lean:135`): `∑_k ‖(𝓕 Φ)(k)‖² = N · ∑_j ‖Φ(j)‖²`. The DFT on `ZMod N` preserves L² norm up to a factor of N. Mathlib has `ZMod.dft` but not this Parseval identity.

- **Plancherel identity for `ZMod.dft`** (`zmod_dft_plancherel_complex`, `LargeSieveHarmonic.lean:416`): The bilinear generalization: `∑_k (𝓕Φ)(k) · conj((𝓕Ψ)(k)) = N · ∑_j Φ(j) · conj(Ψ(j))`.

- **Parseval for multiplicative characters** (`char_parseval_units`, `LargeSieveAnalytic.lean:809`): `∑_χ ‖∑_{a∈(ℤ/pℤ)ˣ} g(a)·χ(a)‖² = (p−1) · ∑_a ‖g(a)‖²`. The Plancherel theorem for the character group of `(ℤ/pℤ)ˣ`.

- **Nontrivial character Parseval** (`nontrivial_char_parseval_le`, `IKCh7.lean:1128`): The sum over nontrivial characters only is `≤ (p−1) · ∑ ‖g(a)‖²` (dropping the nonneg trivial-character term from full Parseval).

- **Finite Weyl criterion** (`weyl_criterion_finite_group`, `LargeSieveSpectral.lean:411`): If all nontrivial character sums are `o(N)`, then the sequence is equidistributed: `|V(a) − N/(p−1)| ≤ ε·N`. The quantitative equidistribution criterion for finite abelian groups.

---

### 4. Gauss Sums

**File: `LargeSieveHarmonic.lean`, `LargeSieveAnalytic.lean`**

- **Gauss sum norm-squared** (`gaussSum_norm_sq_eq_prime`, `LargeSieveHarmonic.lean:388`): `‖τ(χ)‖² = p` for nontrivial `χ : MulChar (ZMod p) ℂ`. Mathlib has `gaussSum_mul_gaussSum_eq_card` but this direct norm-squared form is missing.

- **Gauss sum conjugation** (`gaussSum_conj_eq`, `LargeSieveHarmonic.lean:366`): `conj(τ(χ, ψ)) = τ(χ⁻¹, ψ⁻¹)`.

- **Gauss sum nonvanishing** (`gaussSum_stdAddChar_ne_zero`, `LargeSieveAnalytic.lean:255`): `τ(χ) ≠ 0` for nontrivial χ on `ZMod p`.

- **Gauss sum inversion formula** (`gauss_sum_inversion`, `LargeSieveAnalytic.lean:268`): `χ(a) = τ(χ⁻¹)⁻¹ · τ(χ⁻¹, ψ_a)`, expressing character values via Gauss sums.

- **Character sum to exponential sum (Gauss conductor transfer)** (`char_sum_to_exp_sum`, `LargeSieveAnalytic.lean:304`): `∑ f(n)·χ(n) = τ⁻¹ · ∑_b χ⁻¹(b) · ∑_n f(n)·ψ(bn)`. Converts multiplicative character sums into linear combinations of additive character sums.

- **Nontrivial characters at prime level are primitive** (`isPrimitive_of_prime_nontrivial`, `LargeSieveAnalytic.lean:206`).

- **Multiplicative character values have norm 1** (`mulChar_norm_one_of_unit`, `LargeSieveHarmonic.lean:333`), and **conjugate equals inverse** (`mulChar_conj_eq_inv`, `LargeSieveHarmonic.lean:349`).

---

### 5. Exponential Function Infrastructure

**File: `LargeSieveHarmonic.lean`, `LargeSieveAnalytic.lean`**

The number-theoretic exponential `e(α) = exp(2πiα)` is defined as `eAN` with a full API:

- `eAN_zero`, `eAN_add`, `eAN_neg`, `eAN_norm`, `eAN_intCast`, `eAN_ne_zero`, `eAN_mul_conj` — basic properties.
- **Geometric sum closed form and bound** (`eAN_geom_sum_eq`, `eAN_geom_sum_mul`, `norm_eAN_geom_sum_le`): `|∑_{k<N} e(kβ)| ≤ 2/|e(β)−1|`.
- **Jordan's inequality** (`sin_pi_ge_two_mul`, `LargeSieveAnalytic.lean:102`): `sin(πt) ≥ 2t` for `t ∈ [0, 1/2]`.
- **Sine lower bound by fractional part** (`abs_sin_pi_ge_two_frac`, `LargeSieveAnalytic.lean:122`): `|sin(πβ)| ≥ 2|β − round(β)|`.
- **`|1 − e(β)| = 2|sin(πβ)|`** (`norm_one_sub_eAN`, `LargeSieveAnalytic.lean:79`).
- **Key exponential sum estimate** (`norm_eAN_geom_sum_le_inv`, `LargeSieveAnalytic.lean:152`): When β is δ-far from any integer, `|∑ e(kβ)| ≤ 1/(2δ)`.

While `Complex.exp` exists in Mathlib, this clean `e(·)` wrapper with its standard properties is missing and would be a natural addition for analytic number theory.

---

### 6. Farey Spacing

**File: `LargeSieve.lean:613`**

- **Farey spacing** (`farey_spacing_proved`): Distinct fractions `a/q, a'/q'` with `1 ≤ q, q' ≤ Q` satisfy `|a/q − a'/q'| ≥ 1/Q²`. Fully proved. A classical property of Farey fractions, needed for the large sieve and Diophantine approximation.

---

### 7. Arithmetic Functions

**File: `IKCh1.lean`**

- **`IsCompletelyMultiplicative` predicate** (`IKCh1.lean:62`): `f(1) = 1` and `f(mn) = f(m)f(n)` for *all* positive `m, n` (not just coprime). Mathlib has `IsMultiplicative` (coprime only) but not the stronger "completely multiplicative" predicate. This applies to Dirichlet characters, the Liouville function, etc.

- **`IsAdditiveFunction` / `IsCompletelyAdditiveFunction`** (`IKCh1.lean:52, 57`): The additive analogues. Mathlib has no additive function predicates at all.

- **Liouville function** (`liouville`, `IKCh1.lean:172`): `λ(n) = (−1)^{Ω(n)}`, with proved properties:
  - `liouville_isCompletelyMultiplicative`
  - `liouville_apply_prime`: `λ(p) = −1`
  - `liouville_apply_prime_pow`: `λ(p^k) = (−1)^k`
  - `liouville_eq_moebius_of_squarefree`: `λ(n) = μ(n)` for squarefree n

  Mathlib has `μ` and `Ω` but not `λ`. This is a fundamental arithmetic function.

- **Summatory function** (`summatoryFunction`, `IKCh1.lean:278`): `M_f(x) = ∑_{1≤n≤x} f(n)`. A ubiquitous construction in analytic number theory, missing from Mathlib.

- **Ramanujan sum** (`ramanujanSum`, `IKCh1.lean:230`) and **Kloosterman sum** (`kloostermanSum`, `IKCh1.lean:247`): Definitions of two of the most important exponential sums in number theory. Completely missing from Mathlib.

---

### 8. Summation and Special Functions (IK Chapter 4)

**File: `IKCh4.lean`**

- **Sawtooth function** (`sawtooth`, `IKCh4.lean:54`): `ψ(x) = frac(x) − 1/2`, the first periodic Bernoulli function.

- **Periodic Bernoulli functions** (`periodicBernoulli`, `IKCh4.lean:65`): `B_k({x})`. Central to the Euler-Maclaurin formula. Mathlib has `Polynomial.bernoulli` and `bernoulli` but not the periodic extension.

- **Mellin transform** (`mellinTransform`, `IKCh4.lean:501`): `M(f)(s) = ∫_0^∞ f(y) y^{s−1} dy`. Central to analytic number theory. Missing from Mathlib.

- **Fejer and Dirichlet kernels** (`fejerKernel`, `dirichletKernel`, `IKCh4.lean:456, 462`): Foundational objects in Fourier analysis, missing from Mathlib.

- **Root number** (`rootNumber`, `IKCh4.lean:387`): The normalized Gauss sum `ε(χ) = i^{−κ}·τ(χ)/√q` appearing in L-function functional equations.

---

### 9. L-Function Framework (IK Chapter 5)

**File: `IKCh5.lean`**

- **`LFunctionData` structure** (`IKCh5.lean:58`): An axiomatic framework for L-functions in the Selberg class sense: degree, coefficients, local roots, gamma factor, conductor, root number, pole order. Mathlib has `LSeries` but no axiomatic L-function framework.

- **Shimura vanishing** (`shimura_vanishing`, proved): If the root number is `−1`, then `L(f, 1/2) = 0`. Follows purely algebraically from the functional equation.

---

### 10. Rotor-Router Theory

**File: `RotorRouter.lean`**

A self-contained formalization of rotor-router (Propp machine) dynamics on finite groups:

- **Eventually periodic orbits** (`eventually_periodic`, `RotorRouter.lean:79`): Every orbit of a self-map on a finite type is eventually periodic (∃ μ, T > 0 with `f^[μ+T](x) = f^[μ](x)`). Mathlib has `Dynamics.PeriodicPts` but not this "pre-periodic + periodic tail" decomposition.

- **Period propagation** (`periodic_of_eq`, `RotorRouter.lean:85`): If `f^[μ+T](x) = f^[μ](x)` then `f^[n+T](x) = f^[n](x)` for all `n ≥ μ`.

- **Rotor-router visits every group element** (`rotor_visits_all`, `RotorRouter.lean:328`): A rotor-router walk on a finite group with a generating set visits every group element. The deterministic analogue of random walk irreducibility.

- **Rotor-router visits every element infinitely often** (`rotor_visits_all_infinitely`, `RotorRouter.lean:338`): The full recurrence theorem.

- **Visit count divisibility** (`visit_count_dvd_of_periodic`, `RotorRouter.lean:167`): Over one full period, the visit count to any vertex is divisible by the number of generators k — perfect equidistribution of generator usage.

- **Scheduled walk coverage** (`scheduled_walk_covers_all`, `RotorRouter.lean:395`): Abstracted version: *any* multiplicative walk `w(n+1) = w(n)·σ(n)` on a finite group visits everything infinitely often, provided the steps come from a generating set with "pointwise recurrence."

The whole `RotorState`/`rotorStep`/`rotorRun` framework is the first formalization of rotor-routers in Lean/Mathlib, and could form a new `Mathlib.Dynamics.RotorRouter`.

---

### 11. Discrete Dynamics / Combinatorics

**Files: `RotorRouter.lean`, `EquidistPreamble.lean`, `MullinDepartureGraph.lean`**

- **Ordered pigeonhole** (`exists_lt_map_eq`, `RotorRouter.lean:69`): Any `f : ℕ → α` with `[Finite α]` has `m < n` with `f m = f n`. Mathlib has `not_injective_infinite_finite` but not this ordered-pair form.

- **Infinite sequence hits some value infinitely often** (`exists_visits_inf_often`, `RotorRouter.lean:384`): `∀ [Fintype α], ∀ f : ℕ → α, ∃ x, ∀ N, ∃ n ≥ N, f n = x`. Should be expressible as `∃ a, ∃ᶠ n in atTop, f n = a`.

- **Cofinal pigeonhole** (`cofinal_pigeonhole`, `EquidistPreamble.lean:152`): If a property P holds cofinally and `f : ℕ → α` classifies into finitely many buckets, some bucket is hit cofinally with P.

- **Submonoid closure induction** (`submonoid_closure_subset_of_mul_closed`, `RotorRouter.lean:211`): If V contains 1 and is right-closed under S, then V contains the submonoid closure of S. A right-induction principle.

- **Subgroup closure = submonoid closure for finite groups** (`mem_submonoid_closure_of_subgroup_top`, `RotorRouter.lean:205`): In a finite group, if S generates as a subgroup, it generates as a monoid.

---

### 12. Multiplicative Walks on Groups

**File: `MullinDepartureGraph.lean`**

Despite the name, this file develops an abstract theory of multiplicative walks `w(k+1) = w(k) · m(k)` on finite groups:

- **Subgroup trapping** (`subgroup_trapping`, `MullinDepartureGraph.lean:55`): Walk confined to H implies all multipliers in H.
- **Generation escapes subgroups** (`generation_escapes_subgroup`, `MullinDepartureGraph.lean:79`): If multipliers generate G, the walk exits every proper subgroup.
- **Walk stays in coset** (`walk_in_coset_closure`, `MullinDepartureGraph.lean:167`): `w(k) ∈ w(0) · closure(range m)`.
- **Walk hits target iff** (`walk_hits_target_iff`, `MullinDepartureGraph.lean:493`): `w(k+1) = t ↔ m(k) = w(k)⁻¹ · t`.
- **Complement generation** (`closure_compl_singleton_eq_top`, `MullinDepartureGraph.lean:408`): In a finite group of order ≥ 3, removing any single element still yields a generating set.
- **Subgroup orders in groups of order 2p** (`card_subgroup_of_order_two_mul_prime`, `MullinDepartureGraph.lean:338`): Every subgroup of a group of order 2p (p odd prime) has order 1, 2, p, or 2p.

---

### 13. Finite Group Theory

**File: `MullinGroupEscape.lean`, `MullinGroupQR.lean`, `MullinGroupPumping.lean`**

- **Generator not in proper subgroup** (`not_mem_proper_subgroup_of_full_order`, `MullinGroupEscape.lean:579`): If `orderOf g = |G|`, then `g ∉ H` for any proper `H < G`.

- **`g^|H| = 1` for `g ∈ H`** (`pow_card_subgroup_eq_one`, `MullinGroupQR.lean:540`): Lagrange for subgroups. Mathlib has `pow_card_eq_one` for the full group but not this subgroup refinement.

- **Gordon's sequenceability theorem** (`gordon_sequenceable`, `MullinGroupPumping.lean:316`): `ℤ/(2m)ℤ` is sequenceable for all `m ≥ 1` — there exists a permutation of the nonzero elements whose partial sums are also a permutation. This is a classical result (Gordon, 1961, *Pacific J. Math.* 11) with explicit construction. First formalization.

---

### 14. Quadratic Residues

**File: `MullinGroupQR.lean`**

- **Legendre symbol corollaries for small primes**: Explicit QR characterizations of when `(ℓ|q) = −1` for `ℓ = 3, 5, 7, 13, 43, 53`, proved via quadratic reciprocity. These are standard corollaries of QR that Mathlib does not pre-package.

- **Sign lemmas** (`neg_one_pow_half_eq_one/neg_one`, `neg_one_pow_odd_mul`): `(−1)^{q/2} = 1` iff `q ≡ 1 (mod 4)`, and `(−1)^{mn} = (−1)^n` when m is odd.

---

### 15. CRT and ZMod API

**File: `CRTFiberIndependence.lean`**

- **CRT pair surjectivity** (`crt_pair_surjective`, `CRTFiberIndependence.lean:126`): For distinct primes `p, q` and any `a : ZMod p`, `b : ZMod q`, `∃ x : ℤ` with `x ≡ a (mod p)` and `x ≡ b (mod q)`. Mathlib has `ZMod.chineseRemainder` as a ring iso, but this concrete lift statement requires nontrivial assembly.

- **CRT for units** (`crt_unit_pair_surjective`, `CRTFiberIndependence.lean:200`): Same for `(ZMod p)ˣ × (ZMod q)ˣ`.

- **Divisibility independent of residue class** (`dvd_independent_of_residue`, `CRTFiberIndependence.lean:184`): For distinct primes p, q and any `c : ZMod q`, `∃ x` with `x ≡ c (mod q)` and `p ∣ x+1`.

---

### 16. Number Theory Basics

**Files: `MullinConjectures.lean`, `MullinDWH.lean`, `MullinResidueWalk.lean`, `MullinDepartureGraph.lean`**

- **`p ≥ 2` cannot divide consecutive naturals** (`not_dvd_consec`, `MullinConjectures.lean:91`).
- **`q ∣ a+1 ↔ a % q = q−1`** (`dvd_succ_iff_mod_pred`, `MullinResidueWalk.lean:30`): Clean characterization of `a ≡ −1 (mod q)` for naturals.
- **Divisors of 2p** (`dvd_two_mul_prime_iff`, `MullinDepartureGraph.lean:313`): For p an odd prime, `d ∣ 2p ↔ d ∈ {1, 2, p, 2p}`.
- **Small primes generate `(ℤ/pℤ)ˣ`** (`prime_residue_escape`, `EquidistBootstrap.lean:211`): For `p ≥ 5`, the residues of primes less than p generate the full unit group. Key identity: `2 = (−4)(−2)⁻¹`.
- **`∑ x_i² ≤ M · ∑ x_i`** (`sum_sq_le_bound_mul_sum`, `ExcursionIndependence.lean:182`): When `0 ≤ x_i ≤ M`.

---

### 17. Discrete Markov Inequality

**File: `LargeSieve.lean`**

- **Finset Markov inequality** (`finset_markov_inequality`, `LargeSieve.lean:551`; `finset_markov_card_bound`, `LargeSieve.lean:576`): For nonneg `f` with `∑ f ≤ B`, the number of indices with `f(i) > T` is at most `B/T`. Mathlib has the measure-theoretic Markov inequality but not this clean finset version.

---

### Definitions only (open `Prop`s from IK formalization)

The IK files also formalize the *statements* (as `Prop` definitions, not proved) of many important results. These could seed Mathlib stubs:

- `AnalyticLargeSieve`, `ArithmeticLargeSieve`, `BombieriVinogradov`
- `JacobiThetaTransformation`, `PoissonShiftScale`, `EulerMaclaurinOrderK`
- `DirichletFunctionalEquation`, `RiemannZetaFunctionalEquation`
- `GrandRiemannHypothesis`, `PrimeNumberTheoremForL`, `ChebotarevDensity`
- `WeilBound` (for Kloosterman sums), `HadamardFactorization`, `PerronFormula`

---

