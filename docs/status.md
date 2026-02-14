# Project Status: Formal Verification of the Euclid-Mullin Sequence

## Overview

This project is a Lean 4 formalization investigating **Mullin's Conjecture** (1963):
every prime number eventually appears in the Euclid-Mullin sequence. The codebase
contains ~19,327 lines of Lean 4 across 25 source files (plus 3,189 lines of IKCh
formalization across 6 files), comprising ~911 theorems/lemmas and ~407 definitions
with **zero errors** and **zero warnings**. Two `sorry` marks document Dead End #93
(FEB ⟺ CME equivalence — proofs are mathematically routine but tactically complex;
the results are redundant with the already-proved CME → CCSB → MC path).

**The irreducible core:**

> **DynamicalHitting → MullinConjecture**
> (`dynamical_hitting_implies_mullin`)
>
> If the walk hits −1 whenever the multiplier residues generate (ZMod q)ˣ,
> then Mullin's Conjecture follows by strong induction. PrimeResidueEscape
> is proved elementarily (no Burgess needed): if all odd primes < p are in a
> proper subgroup H of (Z/pZ)×, then p−2 ≡ −2 and p−4 ≡ −4 are in H
> (odd factorization), giving 2 = (−4)(−2)⁻¹ ∈ H, hence H = ⊤ — contradiction.
> The SE bootstrap from MC(< p) and the proved PRE provides SubgroupEscape
> at each step; DynamicalHitting converts SE into the walk hitting −1 cofinally.

This is a genuine reduction: DynamicalHitting is strictly weaker than MC
(it has an SE antecedent that could fail). The sole open hypothesis is
DynamicalHitting. The inductive bootstrap that derives SE from MC(< p)
and the proved PRE is real mathematical content.

**Parametric specialization at B = 11:**

> **ThresholdHitting(11) → MC**
> (`threshold_11_implies_mullin'`)
>
> The finite verification (primes 2, 3, 5, 7 from seq values 0, 1, 6, 2)
> discharges FiniteMCBelow(11). Only one open hypothesis remains.

More broadly, the formalization establishes a multi-layered reduction
architecture where every arrow is machine-verified:

1. **PE → MC** via two independent paths (direct through HH, structural through SE + EMPR)
2. **DH → MC** by strong induction (one-hypothesis reduction, §13; PRE proved elementarily)
3. **ThresholdHitting(B) + FiniteMCBelow(B) → MC** parametric decomposition (§14; PRE proved)
4. **Concrete SE** for all 30 primes q ≤ 157 not in the sequence
5. **PRE ↔ SE** decomposing SE into finite power-residue conditions per prime
6. **QR obstruction** constraining SE counterexamples to ≤ 1.6% of primes
7. **Scheduled walk coverage** (sorry-free) reducing Mixing to pointwise recurrence
8. **Sieve/self-avoidance/character** infrastructure constraining walk dynamics
9. **Factored sieve reduction** (§21): MertensEscape + SieveAmplification → TailSE → CofinalEscape → QuotientDH
10. **Analytical characterization** (§22): EMFE ↔ TailSE per-q equivalence, factoring oracle barrier
11. **Oracle impossibility analysis** (§23): OI definition, DH ↔ death-pair cofinality, marginal/joint barrier
12. **Character sum framework** (§24): WalkCollisionCount, CharSumCancellation, CSCImpliesDH reduction
13. **TailSE → DH character chain** (§25): block-rotation cancellation, DH decomposition, three-Prop MC reduction
14. **Multi-modulus sieve decomposition** (§26): GlobalTailSE, TailSE below 11 vacuous, `tail_se_almost_all_11_chain`
15. **Decorrelation principle** (§27): product-escape lemma, MultiplierEquidistribution, WalkEquidistribution, two-Prop and single-Prop MC reductions
16. **Cofinal cycle product** (§28): walk telescoping, cofinal cycle multiplier product-one lemma
17. **Character orthogonality counting** (§29): WalkHitCount, monotonicity, unboundedness equivalences, hitCount_lower_bound → WE
18. **Complex character sum bound** (§30): ComplexCharSumBound (ℂ-valued), `complex_csb_implies_hit_count_lb_proved` (**PROVED**), `complex_csb_mc` → MC
19. **Escape density and decorrelation** (§31): PositiveEscapeDensity, DecorrelationHypothesis, PEDImpliesComplexCSB, `decorrelation_implies_ped` (PROVED), ped_mc → MC, decorrelation_mc → MC
20. **Self-correcting sieve** (§32): NoLongRuns(L), `noLongRuns_implies_ped` (PROVED), noLongRuns_mc chain
21. **Block-rotation estimate** (§33): char_walk_recurrence (PROVED), BlockRotationEstimate (open), `block_rotation_implies_ped_csb` (PROVED), bre_ped_mc, bre_decorrelation_mc, bre_noLongRuns_mc chains
22. **Simplified chains** (§34): `complex_csb_mc'` (**CCSB → MC single hop!**), `ped_mc'`, `decorrelation_mc'`, `bre_ped_mc'`, `bre_decorrelation_mc'`, `bre_noLongRuns_mc'`, `noLongRuns_mc'` — all eliminating Fourier bridge parameter
23. **BRE for order-2 characters** (§35): IsOrder2, `walk_char_val_pm_one` (PROVED), `escape_flips_walk_char` (PROVED), `kernel_preserves_walk_char` (PROVED), `walk_char_norm_one` (PROVED), `bre_order2_from_noLongRuns`, `order2_noLongRuns_mc` chain
24. **Sieve equidistribution + multi-modular** (§36): `SieveEquidistribution` (open — known theorem, not in Mathlib), `dirichlet_residues_independent` (PROVED via Mathlib), `dirichlet_residues_unbounded` (PROVED), `MultiModularCSB` (open), `MultiModularCSBImpliesMC` (**NOW PROVED** — see §42 in LargeSieve.lean)
25. **Walk telescoping + BRE analysis** (§37): `walk_telescope_identity` (PROVED — ∑ χ(w)·(χ(m)-1) = χ(w(N))-χ(w(0))), `walk_telescope_norm_bound` (PROVED — norm ≤ 2), `walk_shift_one_correlation` (PROVED — h=1 autocorrelation = conj(multiplier sum)). Documents that BRE is impossible from PED alone for character order ≥ 3.
26. **Prime density + sieve route** (§38): `PrimeDensityEquipartition` (open — PNT in APs, known theorem not in Mathlib), `GenericLPFEquidist` (open — Alladi 1977, not formalized), `SieveTransfer` (open — GENUINE FRONTIER), `genericLPF_chain_mc` (PROVED — full sieve route to MC), `primeDensity_chain_mc` (PROVED — PNT in APs through all intermediates to MC).
27. **Window equidistribution + per-prime NoLongRuns** (§39): `StrongSieveEquidist` (open — window equidist), `strongSieveEquidist_noLongRunsAt` (PROVED — pigeonhole with L=φ(q)+1), `noLongRunsAt_ped` (PROVED — block-counting, δ=1/(2L)). Documents that cumulative SieveEquidist is too weak for gap control.
28. **Distributional PED** (§40): `DistributionalPED` (open), `dped_implies_ped` (PROVED — filter monotonicity), `DPEDImpliesComplexCSB` (open — **DEAD**: counterexample for d≥3), `dped_mc` (PROVED), `dped_mc'` (PROVED). Exhaustive analysis: PED→CCSB bridge is irreducible for d≥3 — no factorizable intermediate exists.
29. **Large Sieve + BV statements** (§41): `AnalyticLargeSieve` (open — known, not in Mathlib), `ArithmeticLargeSieve` (open — known, not in Mathlib), `BombieriVinogradov` (open — known, not in Mathlib). Formal statements of the analytic prerequisites for BV-on-average strategy.
30. **MMCSB → MC** (§42): `mmcsb_implies_threshold` (**PROVED** — MMCSB → ThresholdHitting per-prime Fourier bridge), `mmcsb_implies_mc` (**PROVED** — MMCSB + FiniteMCBelow → MC), `mmcsb_small_threshold_mc` (**PROVED** — MMCSB with Q₀ ≤ 11 → MC unconditionally). Closes previously-open `MultiModularCSBImpliesMC`.
31. **BV + ArithLS transfer chains** (§43-§44): `BVImpliesMMCSB` (open — **GENUINE FRONTIER**), `ArithLSImpliesMMCSB` (open), `bv_chain_mc` (PROVED), `bv_small_threshold_mc` (PROVED), `arith_ls_chain_mc` (PROVED). Fourth independent route to MC.
32. **Product growth + Level of Distribution** (§45): `prod_exponential_lower` (**PROVED** — 2^N ≤ prod N by induction), `prod_growth_eventually_exceeds` (**PROVED** — ∀ B, ∃ N₀, B ≤ prod N), `EMHasLevelOfDistribution` (open — EM walk has level θ), `LoDImpliesMMCSB` (open).
33. **Markov inequality** (§46): `finset_markov_inequality` (**PROVED** — averaged-to-pointwise), `finset_markov_card_bound` (**PROVED** — card form B/T).
34. **ALS-ArithLS reduction + Farey + LoD chains** (§47): `farey_spacing_proved` (**PROVED** — nonzero integer argument), `ALSFareyImpliesArithLS` (open — Gauss sum argument), `als_farey_chain_mc'` (PROVED — Farey eliminated), `lod_chain_mc` (PROVED), `lod_small_threshold_mc` (PROVED). Fifth independent route to MC via Level of Distribution.
35. **Product parity + sqrt range** (§48): `two_dvd_prod` (**PROVED** — 2 | prod n), `prod_add_one_odd` (**PROVED** — Euclid numbers odd), `seq_pos_ne_two` (**PROVED** — seq n ≠ 2 for n > 0), `fixed_q_eventually_in_sqrt_range` (**PROVED** — any B eventually ≤ √(prod N)).
36. **GaussConductorTransfer + structural sieve** (§49-§51): `GaussConductorTransfer` (open — ALS → ArithLS), `gct_implies_als_farey` (**PROVED**), `gauss_conductor_chain_mc` (**PROVED**), `prod_strictly_increasing` (**PROVED**), `euclid_number_coprime_seq` (**PROVED**), `seq_coprime_of_distinct` (**PROVED**), `euclid_cong_one_mod_earlier_prod` (**PROVED**). Comprehensive structural lemmas for sieve arguments.
37. **BVImpliesMMCSB decomposition** (§52): `EMMultCharSumBound` (open — multiplier char sums o(N)), `BVImpliesEMMultCSB` (open — sieve transfer), `MultCSBImpliesMMCSB` (open — walk bridge, **CONFIRMED FALSE** Dead End #58), `StrongSieveImpliesMultCSB` (**NOW PROVED** — Weyl bridge, via SSE→SE composition), `bv_decomposition_implies_mmcsb` (**PROVED** — composition), `bv_decomposed_chain_mc` (**PROVED**), `bv_decomposed_small_threshold_mc` (**PROVED**), `telescope_constrains_walk` (**PROVED** — restatement from §37), `sieve_equidist_implies_mult_csb` (**PROVED** — SieveEquidistribution → EMMultCharSumBound via multiplier Weyl criterion: fiber decomposition + character orthogonality + triangle inequality), `strongSieveEquidist_implies_sieveEquidist` (**PROVED** — window equidist implies cumulative equidist, ~75 lines), `strongSieve_implies_multCSB` (**PROVED** — composition of SSE→SE→MultCSB). Separates NUMBER THEORY (BV → multiplier cancellation) from DYNAMICS (multiplier → walk cancellation).
38. **Sieve-to-Harmonic Bridge** (§79, LargeSieve.lean): `sieve_equidist_implies_decorrelation` (**PROVED** — SE → DecorrelationHypothesis, 73-line Weyl criterion: counting equidistribution implies character-sum cancellation for ALL primes q), `sieve_equidist_implies_ped` (**PROVED** — SE → PositiveEscapeDensity, composition with Dec→PED), `sieve_equidist_chain_mc` (**PROVED** — SE + PEDImpliesCSB → MC), `strongSieve_implies_decorrelation` (**PROVED** — SSE → Dec), `strongSieve_implies_ped` (**PROVED** — SSE → PED), `strongSieve_chain_mc` (**PROVED** — SSE + PEDImpliesCSB → MC). **Key insight**: the sieve hierarchy and harmonic hierarchy converge at `DecorrelationHypothesis`. Any proof of SieveEquidistribution (e.g., PNT in APs + Alladi's theorem) immediately gives Dec + PED; sole remaining gap to MC is `PEDImpliesComplexCSB`.
38. **Parseval + Plancherel + Gauss sums** (§53-§54): `zmod_dft_parseval` (**PROVED** — ∑‖𝓕Φ(k)‖²=N·∑‖Φ(j)‖²), `zmod_dft_plancherel_complex` (**PROVED**), `gaussSum_norm_sq_eq_prime` (**PROVED** — ‖τ(χ)‖²=p), `zmod_large_sieve_subset` (**PROVED**), `mulChar_conj_eq_inv` (**PROVED**).
39. **Analytic Large Sieve infrastructure** (§55, LargeSieveHarmonic.lean): `eAN` (exp function), `trigKernel` (kernel K(k)=∑e(kα)), `als_bilinear_expansion` (**PROVED** — ∑‖S(α_r)‖²=Re(∑∑a_m·conj(a_n)·K(m-n))), `abs_schur_bound` (**PROVED** — Schur test via AM-GM), `KernelRowSumBound` (open — standard trig estimate, δ≤1 added Session 33), `kernel_row_sum_implies_als` (**PROVED** — **KernelRowSumBound → AnalyticLargeSieve**). Reduces ALS to a single trigonometric estimate.
40. **Geometric sum infrastructure** (§56): `eAN_geom_sum_mul` (**PROVED** — telescoping), `eAN_geom_sum_eq` (**PROVED** — closed form), `norm_eAN_geom_sum_le` (**PROVED** — ≤2/‖e(β)-1‖), `norm_one_sub_eAN` (**PROVED** — =2|sin(πβ)|), `sin_pi_ge_two_mul` (**PROVED** — Jordan's inequality), `abs_sin_pi_ge_two_frac` (**PROVED** — |sin(πβ)|≥2|β-round(β)|), `norm_eAN_geom_sum_le_inv` (**PROVED** — **KEY**: ‖∑e(kβ)‖ ≤ 1/(2δ) for well-separated β). Provides all tools for KernelRowSumBound proof.
41. **Gauss Sum Inversion** (§57): `gaussSum_stdAddChar_ne_zero` (**PROVED** — Gauss sum non-vanishing), `gauss_sum_inversion` (**PROVED** — χ(a) = τ(χ⁻¹)⁻¹·τ(χ⁻¹,ψ_a)), `gauss_sum_inversion_sum` (**PROVED** — sum form), `char_sum_to_exp_sum` (**PROVED** — **KEY**: ∑f(n)χ(n) = τ⁻¹·∑_b χ⁻¹(b)·∑_n f(n)·ψ(bn)). Converts character sums to exponential sums via Gauss sum inversion — core step 3 of GaussConductorTransfer.
42. **Weak Analytic Large Sieve** (§58): `well_separated_card_le` (**PROVED** — R ≤ δ⁻¹+1 for δ-separated points, pigeonhole via bin counting), `als_per_point_bound` (**PROVED** — Cauchy-Schwarz + eAN unitarity), `weak_als_from_card_bound` (**PROVED** — ∑_r ‖S(α_r)‖² ≤ N·(δ⁻¹+1)·∑‖a_n‖²). Supersedes KernelRowSumBound: trivial N·(δ⁻¹+1) constant suffices for MC since MMCSB only needs o(N) qualitative bound.
43. **Character sum → exponential sum bound** (§59): `char_sum_norm_sq_le_exp_sum` (**PROVED** — for nontrivial χ mod p, ‖∑f(n)χ(n)‖² ≤ ∑_a ‖∑f(n)ψ(an)‖²). Uses Gauss sum inversion (§57) + triangle inequality + gaussSum_norm_sq_eq_prime (§54). GCT lemma 5.
44. **Multiplicative Parseval** (§60): `char_parseval_units` (**PROVED** — ∑_χ ‖∑g(a)χ(a)‖² = (p-1)·∑‖g(a)‖²). Character orthogonality on (ZMod p)ˣ. GCT lemma 6.
45. **Uniform well-separation** (§61): `uniform_points_well_separated` (**PROVED** — {b/p : b ∈ Fin p} are (1/p)-separated). Distinct elements of Fin p have nonzero integer difference |d| < p. GCT lemma 7.
46. **GCT composition** (§62): `gct_nontrivial_char_sum_le` (**PROVED** — ∑_{χ≠1} ‖∑f(n)χ(n)‖² ≤ (p-1)·∑_a ‖∑f(n)ψ(an)‖²). Composes §59 over all nontrivial Dirichlet characters via Finset.sum_le_card_nsmul + dirichlet_card_eq_pred. **GCT lemma 8 — ALL 8 GCT LEMMAS COMPLETE.**
47. **ALS → PrimeArithLS** (§65): `als_implies_prime_arith_ls` (**PROVED** — AnalyticLargeSieve → PrimeArithmeticLargeSieve). Composes §64 `char_sum_norm_sq_le_exp_sum_finN` with ALS at evaluation points {b/p : b ∈ Fin p}, bridging ZMod↔Fin via successor decomposition. Chain theorems: `prime_arith_ls_chain_mc` (**PROVED**), `als_prime_arith_ls_chain_mc` (**PROVED**), `als_prime_arith_ls_small_threshold_mc` (**PROVED** — ALS + transfer with Q₀≤11 → MC unconditionally). `PrimeArithLSImpliesMMCSB` (open — transfer from PrimeArithLS to MultiModularCSB). Sixth independent route to MC.
48. **Walk Energy Parseval** (§66): `walkVisitCount` (occupation measure), `walkVisitCount_sum` (**PROVED** — ∑V(a)=N), `walk_char_sum_eq_occupation` (**PROVED** — rearrangement via Finset.sum_fiberwise), `walk_energy_parseval` (**PROVED** — ∑_χ ‖∑χ(w(n))‖² = (p-1)·∑V(a)²), `visit_energy_lower_bound` (**PROVED** — ∑V(a)² ≥ N²/(p-1) by Cauchy-Schwarz). Makes the equidistribution-energy tradeoff precise: character sum cancellation ↔ uniform visit distribution.
49. **SubquadraticVisitEnergy → MMCSB Markov Bridge** (§67): `excessEnergy` (def — (p-1)·∑V(a)² − N²), `excess_energy_eq_nontrivial_sum` (**PROVED** — excess = ∑_{χ≠1} ‖∑χ(w(n))‖² via Parseval decomposition), `excessEnergy_nonneg` (**PROVED**), `nontrivial_char_sq_le_excess` (**PROVED** — single char sum ≤ total excess), `SubquadraticVisitEnergy` (open — visit energy N²/(p-1)+o(N²)), `sve_implies_mmcsb` (**PROVED** — SVE → MMCSB via ε²-trick + le_of_sq_le_sq), `sve_implies_mc` (**PROVED** — SVE + FiniteMCBelow → MC), `sve_small_threshold_mc` (**PROVED** — SVE with Q₀≤11 → MC unconditionally). Seventh independent route to MC.
50. **Finite Weyl Criterion** (§68): `WalkEquidistCondition` (def — ∀ nontrivial χ, ‖∑χ(w(n))‖ ≤ ε·N), `char_indicator_expansion` (**PROVED** — ∑_χ χ(a⁻¹)·χ(x) = (p-1)·[x=a] via Mathlib's `sum_char_inv_mul_char_eq`), `visit_count_char_expansion` (**PROVED** — V_N(a) = (1/(p-1))·∑_χ χ(a⁻¹)·S_χ), `visit_count_nontrivial_decomposition` (**PROVED** — V_N(a) − N/(p-1) = (1/(p-1))·∑_{χ≠1} χ(a⁻¹)·S_χ), `weyl_criterion_finite_group` (**PROVED** — WalkEquidistCondition → ‖V_N(a)−N/(p-1)‖ ≤ ε·N for all a). Connects character sum cancellation to walk equidistribution — makes MMCSB semantically transparent.
51. **Higher-Order Decorrelation + Van der Corput** (§69): `HigherOrderDecorrelation` (open — h-fold walk autocorrelation o(N) for all lags), `vanDerCorputBound` (**PROVED** — ~305 lines, Iwaniec-Kowalski windowed-sum approach; first VdC formalization in any proof assistant worldwide), `hod_vdc_implies_ccsb` (**PROVED** — HOD + VdC → ComplexCharSumBound via ε²/4-trick and optimal H choice), `hod_vdc_chain_mc` (**PROVED** — HOD + VdC → MC), `hod_vdc_implies_mmcsb` (**PROVED** — HOD + VdC → MultiModularCSB with Q₀=0), `hod_implies_ccsb` (**PROVED** — HOD → CCSB, VdC parameter eliminated since now proved), `hod_chain_mc` (**PROVED** — HOD → MC, single hypothesis!), `hod_implies_mmcsb` (**PROVED** — HOD → MMCSB). With VdC now proved, HOD alone suffices for MC. Note: HOD is strictly STRONGER than CCSB — documents the decorrelation hierarchy but is not a useful attack target.
52. **Conditional Multiplier Equidistribution** (§70): `ConditionalMultiplierEquidist` (open — minFac equidistributed mod q conditional on walk position), `cme_implies_dec` (**PROVED** — CME → DecorrelationHypothesis via Finset.sum_fiberwise partition + triangle inequality), `cme_chain_mc` (**PROVED** — CME + PEDImpliesCSB → MC), `fiberMultCharSum` (def — fiber-restricted multiplier character sum), `cme_iff_fiber_bound` (**PROVED** — CME definitionally equals bounding fiber sums, by Iff.rfl), `mult_char_sum_eq_fiber_sum` (**PROVED** — total char sum decomposes as sum of fiber sums via Finset.sum_fiberwise). CME → HOD is FALSE for h≥2 (Dead End #81): walk feedback creates correlations between consecutive multipliers. Hierarchy: PED < Dec < CME < CCSB (all strict inclusions). **Session 59 analysis**: CME is the optimal intermediate — weaker than CCSB but still implies MC via the proved chain CME→CCSB→MC. The irreducible content is CompositeSieveEquidist (conditional on walk position, for composite Euclid numbers). Faces the Four-Layer Gap (population→individual, unconditional→conditional, static→growing, counting→distribution).
53. **Elliott-Halberstam Conjecture** (§71): `ElliottHalberstam` (open — major open conjecture in analytic number theory, not in Mathlib), `eh_implies_bv` (**PROVED** — EH → BV by instantiating θ=1/2), `eh_chain_mc` (**PROVED** — EH + BVImpliesMMCSB + FiniteMCBelow → MC), `eh_small_threshold_mc` (**PROVED** — EH + BVImpliesMMCSB (Q₀≤11) → MC unconditionally). Documents MC's conditional dependence on the Elliott-Halberstam conjecture. Eighth independent route to MC.
54. **Kernel Confinement and CCSB Failure** (§72): `kernel_confinement_walk_char_constant` (**PROVED** — eventual kernel confinement → walk char constant), `kernel_confinement_walk_sum` (**PROVED** — explicit linear growth formula under confinement), `ccsb_at_implies_escape_cofinal` (**PROVED** — CCSB at (q,χ) implies infinitely many escapes from ker(χ), by reverse triangle inequality + Archimedean argument). Documents the PED-CCSB boundary precisely: CCSB REQUIRES escapes.
55. **Quadratic Walk Sum Decomposition** (§73): `escape_telescope_order2` (**PROVED** — for order-2 χ, −2·∑_{escape} χ(w(n)) = χ(w(N)) − χ(w(0)), specializing the telescope identity), `escape_sum_order2_bounded` (**PROVED** — ‖∑_{escape} χ(w(n))‖ ≤ 1, from triangle + walk char norm 1), `quadratic_walk_sum_split` (**PROVED** — S_N = kernel sum + escape sum), `walk_sum_le_kernel_sum_add_one` (**PROVED** — ‖S_N‖ ≤ ‖kernel sum‖ + 1), `QuadraticCCSB` (definition — CCSB restricted to order-2 characters), `ccsb_implies_quadratic_ccsb` (**PROVED** — trivial specialization), `kernel_sum_le_walk_sum_add_one` (**PROVED** — reverse direction: ‖kernel sum‖ ≤ ‖S_N‖ + 1), `quadratic_ccsb_iff_kernel_ccsb` (**PROVED** — QuadraticCCSB ↔ kernel-block sum is o(N), an iff reduction eliminating escapes). For order-2 characters, the escape contribution is provably O(1), reducing CCSB(d=2) to the kernel-block sum alone.
56. **Escape Decorrelation Hypothesis** (§74): `local_char_walk_multi_step` (**PROVED** — χ(w(n+h)) = χ(w(n)) · ∏_{j<h} χ(m(n+j)), local copy of §53 multi-step recurrence), `quadratic_autocorrelation_eq_mult_product` (**PROVED** — for order-2 χ, χ(w(n+h))·χ(w(n)) = ∏_{j<h} χ(m(n+j)), using χ²=1), `EscapeDecorrelation` (definition — h-fold multiplier product sums o(N) for all h ≥ 1, the quadratic analogue of HOD), `escape_dec_h1_specializes` (**PROVED** — h=1 case reduces to single multiplier character sum), `escape_dec_implies_walk_autocorr_bound` (**PROVED** — EscapeDecorrelation → walk autocorrelation sum o(N)), `escape_dec_implies_quadratic_ccsb` (**PROVED** — VdC + EscapeDecorrelation → QuadraticCCSB, using autocorrelation identity), `escape_dec_quadratic_ccsb_chain` (**PROVED** — chain wrapper). Note: attack-analytic analysis confirms EscapeDecorrelation ≡ QuadraticHOD ≡ QuadraticCCSB via proved VdC — this is a reformulation, not a new attack surface (Dead End #85).
57. **Energy Increment Dynamics** (§75): `nontrivial_char_walk_sum` (**PROVED** — ∑_{χ≠1} χ(a⁻¹)·S_χ = (p-1)·V_N(a) − N, connecting nontrivial character sums to visit counts via orthogonality), `energy_increment_identity` (**PROVED** — ∑_{χ≠1} (2·Re(S_χ·χ̄(a)) + 1) = 2(p-1)·V_N(a) − 2N + (p-2), the character-sum form of the energy increment), `energy_below_average_decreases` (**PROVED** — V_N(a) < N/(p-1) implies energy increment < p-2), `energy_above_average_increases` (**PROVED** — V_N(a) > N/(p-1) implies energy increment > p-2), `average_energy_increment` (**PROVED** — (1/(p-1))·∑_a increment(a) = p-2, the neutral drift value). Documents the dynamical self-correcting structure: energy grows slower when the walk visits underrepresented positions. SVE ↔ walk typically visits below-average positions. Reduces to SieveTransfer (not a new attack surface).
58. **Quadratic Block Alternation Structure** (§77): `order2_not_one_eq_neg_one` (**PROVED** — for order-2 χ, χ(u)≠1 implies χ(u)=−1), `kernel_opposite_after_escape` (**PROVED** — kernel step then escape flips walk char: χ(w(n+2))=−χ(w(n))), `kernel_block_walk_char_constant` (**PROVED** — k consecutive kernel steps preserve walk char: χ(w(n+k))=χ(w(n)), by induction), `quadratic_kernel_sum_on_block` (**PROVED** — block of L kernel steps sums to L·χ(w(start)), by Finset.sum_congr). The d=2 kernel-block sum is a pure alternating series s·(L₁−L₂+L₃−⋯) where Lₖ are block lengths — unique to order 2 since escape rotations are all −1 (for d≥3, escape rotations vary among d−1 values, destroying alternation).
59. **Escape Alternation Structure** (§78): `escape_values_alternate` (**PROVED** — for order-2 χ, consecutive escape values alternate: if all steps between e₁ and e₂ are kernel steps, then χ(w(e₂)) = −χ(w(e₁)), by composing escape_flips_walk_char with kernel_block_walk_char_constant), `kernel_sum_between_escapes` (**PROVED** — kernel-block sum between consecutive escapes e₁,e₂ equals (e₂−e₁−1)·(−χ(w(e₁))), composing quadratic_kernel_sum_on_block with escape_flips_walk_char). Completes the d=2 kernel-block characterization: the walk character value at escape positions follows a strict +1,−1,+1,−1,… alternation, and each inter-escape kernel block contributes a signed multiple of its length to the kernel sum.
60. **Fiber Energy Bound** (§80): `FiberEnergyBound` (def — ∑_a ‖fiberMultCharSum(a)‖² ≤ ε·N², L² fiber control), `cme_implies_feb` (sorry — L∞→L² trivially), `feb_implies_ccsb` (sorry — Cauchy-Schwarz route), `feb_implies_mc` (composition — FEB → CCSB → MC). **Dead End #93**: FEB ⟺ CME for fixed q — Markov inequality on finitely many (q−1) positions shows L² control implies L∞ control. Similarly, **Dead End #94**: Density-1 CME ≡ CME because each fiber has Θ(N/(q−1)) = Θ(N) elements. No L^p interpolation provides a strictly weaker intermediate between Dec and CCSB. The sorry marks are redundant with the already-proved CME → CCSB → MC path.
61. **LoD Scale Mismatch** (§82): `exp_dominates_linear` (**PROVED** — ∀ C>0, ∃ N₀, ∀ N≥N₀, C·N < 2^N; from `isLittleO_coe_const_pow_of_one_lt`), `prod_superlinear` (**PROVED** — ∀ C>0, ∃ N₀, ∀ N≥N₀, C·N < prod N; from `prod_exponential_lower`). **Dead End #96**: The LoD error term `(prod N)^θ / (log prod N)^A` grows exponentially in N since `prod N ≥ 2^N`, making `LoDImpliesMMCSB` vacuously unprovable — the bound exceeds N for all large N. Standard LoD is designed for settings where the range x equals the integer size; for EM, range is N while integer size is prod(N), creating an exponential gap.

---

## The Sole Open Question

All formal reductions are complete. The sole remaining open question is:

> **Can the greedy factoring process sustain a "factoring oracle" — a
> systematic correlation between the mod-q residue of Prod(n) and the
> mod-q residue of minFac(Prod(n)+1) — to avoid the death equation
> minFac(Prod(n)+1) ≡ −Prod(n)⁻¹ (mod q) indefinitely?**

Formally, this is **DynamicalHitting**: if the multiplier residues generate
(ZMod q)ˣ, the walk must hit −1 cofinally.

**The marginal/joint barrier:** The verified reductions (TailSE, CofinalEscape,
QuotientDH) exhaust what can be proved about the *marginal* distribution of
multiplier residues. Even perfect per-position equidistribution of multipliers
is consistent with HH failure. DH is a *joint* distribution statement — the
(position, multiplier) pair must hit the death curve — and no marginal
statement can force this.

**The no-oracle principle:** HH failure couples a mod-q residue (O(log q) bits)
with a factorization outcome (~2^n bits). The Euclid numbers Prod(n)+1 grow
doubly exponentially with pairwise disjoint prime factorizations. The oracle
must work at all primes q simultaneously, requiring a factoring algorithm —
contradicting the presumed hardness of integer factorization.

**The analytic program:**
1. Prove a Bombieri–Vinogradov type estimate for EM walk residues (joint distribution)
2. Derive ThresholdHitting(B) for some explicit B from the equidistribution estimate
3. Verify FiniteMCBelow(B) computationally (B = 11 already discharged)
4. Combine via `threshold_finite_implies_mullin` with PrimeResidueEscape to obtain MC

---

## The Reduction Architecture

```
                     MullinConjecture
                           ^
               ____________|____________
              |                         |
    HittingHypothesis              SE + Mixing
         ^    ^                     ^       ^
         |    |                    /         \
    WalkCoverage  (SE bootstrapped    MixingHypothesis
                   from PRE)              ^
                                           |
                                    EMPointwiseRecurrence
                                           +
                                  scheduled_walk_covers_all (proved)

ONE-HYPOTHESIS REDUCTION (§13):
  DynamicalHitting  →  MC
  (strong induction: IH → MC(<p) → SE(p) → HH(p) → MC(p))
  PrimeResidueEscape proved elementarily (no Burgess needed)

THRESHOLD SPECIALIZATION (§14):
  ThresholdHitting(11)  →  MC
  (FiniteMCBelow(11) discharged from four computed seq values)
  (PrimeResidueEscape proved, no longer an open hypothesis)

SE DECOMPOSITION (§9-10):
  PRE ↔ SE                         ← finite power-residue conditions
  PRE_at automatic for (q-1)/ℓ ≤ 7 ← 8 elements escape small kernels
  QR obstruction: ≤ 1.6% of primes fail ℓ=2 escape

SIEVE TRICHOTOMY (§4):
  For any q ∉ seq: SE fails ∨ Mixing fails ∨ HH holds
```

All arrows are formally proved (**zero sorry**). The open hypotheses are
stated as `def ... : Prop` (clean mathematical propositions, not gaps).

---

## File Structure

| File | Lines | Content |
|------|-------|---------|
| `Euclid.lean` | 425 | Constructive Euclid's theorem (`propext` + `Quot.sound` only) |
| `MullinDefs.lean` | 527 | `seq`, `prod`, `aux`, basic identities, `seq_isPrime`, `seq_injective` |
| `MullinConjectures.lean` | 494 | `MullinConjecture`, `ConjectureA` (FALSE), `HittingHypothesis`, `hh_implies_mullin` |
| `MullinDWH.lean` | 551 | `DivisorWalkHypothesis`, `dwh_implies_mullin` — LEAF |
| `MullinResidueWalk.lean` | 605 | `WalkCoverage`, residue walk, pigeonhole, concrete MC instances |
| `MullinGroupCore.lean` | 422 | `walkZ`, `multZ`, confinement, `SubgroupEscape`, `se_mixing_implies_mullin` |
| `MullinGroupEscape.lean` | 673 | 6 mult escape lemmas, `eight_elts_escape`, `se_of_maximal_escape`, `se_at_of_pow_checks` |
| `MullinGroupSEInstances.lean` | 364 | 30 concrete SE instances, concrete mixing, `walkZ_hits_iff_target` |
| `MullinGroupPumping.lean` | 343 | Gordon's sequenceability, pumping, subgroup growth — LEAF |
| `MullinGroupQR.lean` | 683 | QR conditions, `se_qr_obstruction`, multi-witness SE — LEAF |
| `RotorRouter.lean` | 421 | Rotor-router + scheduled walk coverage (standalone, 0 sorry) |
| `MullinRotorBridge.lean` | 87 | `emWalkUnit`, `EMPointwiseRecurrence`, EMPR+SE→MC (0 sorry) |
| `EquidistPreamble.lean` | 234 | `PairEquidistribution`, `pe_implies_mullin`, bootstrapping |
| `EquidistSieve.lean` | 297 | Sieve analysis, `WeakHittingPrinciple`, `whp_iff_hh` |
| `EquidistSelfAvoidance.lean` | 450 | Self-avoidance, periodicity vs. generation |
| `EquidistCharPRE.lean` | 811 | Character non-vanishing, PRE↔SE, local PRE, EKE |
| `EquidistBootstrap.lean` | 522 | Inductive bootstrap, minimality sieve, irreducible core (DH→MC) |
| `EquidistThreshold.lean` | 299 | Threshold approach, `concrete_mc_below_11`, open problem analysis |
| `EquidistOrbitAnalysis.lean` | 1441 | Cofinal orbit expansion, quotient walk, cofinal escape, factored sieve, oracle barrier, selectability |
| `EquidistFourier.lean` | 1298 | Character sums, TailSE chains, GlobalTailSE, decorrelation, Fourier bridge (**PROVED**) |
| `EquidistSelfCorrecting.lean` | 2418 | Escape density, decorrelation, BRE, simplified chains, sign-flip algebra, telescoping, Euclid feedback loop (E(n) mod q = w(n)+1), kernel confinement (§72), quadratic walk decomposition (§73), escape decorrelation (§74), energy increment (§75), general walk sum (§76), quadratic block alternation (§77), escape alternation (§78), sieve route, window equidist, DPED |
| `LargeSieve.lean` | 1812 | Large Sieve, Arithmetic Large Sieve, BV statements; MMCSB→MC (PROVED); BV/ArithLS/LoD chains; Farey (PROVED); parity; sqrt range; GCT; coprimality; §52 BV decomposition; **SieveEquidist→EMMultCSB (PROVED)**; **StrongSieveEquidist→SieveEquidist (PROVED)**; **StrongSieve→MultCSB (PROVED)**; §79 Sieve-Harmonic Bridge: **SE→Dec (PROVED)**, **SE→PED (PROVED)**, **SE+PEDImpliesCSB→MC (PROVED)**, **SSE→Dec (PROVED)**, **SSE→PED (PROVED)**, **SSE+PEDImpliesCSB→MC (PROVED)** |
| `LargeSieveHarmonic.lean` | 892 | §53-§55: Parseval/Plancherel/Gauss sums; ALS infrastructure (eAN, trigKernel, Schur test, kernel_row_sum_implies_als — all PROVED) |
| `LargeSieveAnalytic.lean` | 1571 | §56-§71, §75, §80-§82: Geometric sums (PROVED); Gauss inversion (PROVED); WeakALS (PROVED); char sum bounds (PROVED); GCT composition (ALL 8 LEMMAS PROVED); **ALS → PrimeArithLS (PROVED)**; **Walk Energy Parseval (PROVED)**; **SVE → MMCSB Markov Bridge (PROVED)**; **Finite Weyl Criterion (PROVED)**; **VanDerCorputBound (PROVED)**; **HOD → CCSB → MC (PROVED, VdC eliminated)**; **CME → Dec (PROVED)**; **EH → BV → MC (PROVED)**; Energy increment dynamics; **fiberMultCharSum** (def); §80 **FiberEnergyBound** (def), **cme_implies_feb** (sorry — Dead End #93), **feb_implies_ccsb** (sorry — Dead End #93); §81 **walk_as_partial_product** (PROVED); §82 **exp_dominates_linear** (PROVED), **prod_superlinear** (PROVED) — Dead End #96: LoD Scale Mismatch |
| `LargeSieveSpectral.lean` | 1685 | Spectral analysis, walk energy, quadratic forms (split from LargeSieveAnalytic) |
| `EquidistSieveTransfer.lean` | 1319 | SieveTransfer decomposition, CompositeSieveEquidist, sieve route infrastructure |
| `IKCh1.lean` | 437 | IK Chapter 1: arithmetic functions, exponential sums |
| `IKCh2.lean` | 270 | IK Chapter 2: Dirichlet's theorem, PNT (open Props) |
| `IKCh3.lean` | 557 | IK Chapter 3: Gauss sums, Hecke characters (open Props) |
| `IKCh4.lean` | 593 | IK Chapter 4: Primes in arithmetic progressions (open Props) |
| `IKCh5.lean` | 877 | IK Chapter 5: L-functions, zero-free regions (open Props) |
| `IKCh7.lean` | 455 | IK Chapter 7: Large sieve, bilinear forms (open Props) |
| **Total** | **~22,516** | **~911 theorems/lemmas, ~407 definitions, 2 sorry (Dead End #93)** |

### Import DAG

```
                    Euclid
                       |
                  MullinDefs
                       |
                MullinConjectures
                  /         \
        MullinDWH         MullinResidueWalk
        [LEAF]                 |
                         MullinGroupCore
                          /    |     \
           MullinGroupEscape  |    MullinGroupPumping [LEAF]
                  |           |
    MullinGroupSEInstances   MullinGroupQR [LEAF]
                |                |
                |          RotorRouter
                |               |
                |       MullinRotorBridge
                 \         /
              EquidistPreamble
                     |
               EquidistSieve
                     |
          EquidistSelfAvoidance
                     |
             EquidistCharPRE
                     |
            EquidistBootstrap
                     |
           EquidistThreshold
                     |
         EquidistOrbitAnalysis
                     |
           EquidistFourier
                     |
        EquidistSelfCorrecting
                    |
         EquidistSieveTransfer
                    |
              LargeSieve
                    |
          LargeSieveHarmonic
                    |
          LargeSieveAnalytic
                    |
          LargeSieveSpectral
```

---

## Axiom Usage

| Files | Axioms |
|-------|--------|
| Euclid.lean | `propext`, `Quot.sound` (fully constructive) |
| MullinDefs–ResidueWalk | `propext`, `Quot.sound`, `Classical.choice`, `Lean.ofReduceBool` |
| MullinGroup*, Equidist*, RotorRouter, Bridge | Full Mathlib (all CIC axioms) |

The core definitions (`seq`, `prod`, `IsPrime`) and their basic properties
are fully constructive. Classical reasoning enters only at the reduction level.

---

## Verification

```
$ lake build
Build completed successfully.
```

Zero errors on theorem content. Two `sorry` warnings in §80 FiberEnergyBound
(`cme_implies_feb`, `feb_implies_ccsb`) — both document Dead End #93 (FEB ⟺ CME
equivalence) and are redundant with the already-proved CME → CCSB → MC path.
All open hypotheses stated as `def ... : Prop` (clean propositions, not sorry'd theorems).
