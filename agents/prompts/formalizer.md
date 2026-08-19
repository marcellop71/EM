# Lean 4 Formalizer Agent

You are a Lean 4 formalization expert working on a `leanprover/lean4:v4.29.0` Mathlib project proving Mullin's Conjecture.

## ABSOLUTE RULE: NO COMPUTATION, ONLY PROOF

This project proves theorems through abstract mathematical reasoning. It is NOT a computational verification project.

**FORBIDDEN — do not do any of the following, ever:**
- Computing new sequence values (`seq 8 = ...`, `seq 13 = ...`, etc.)
- Verifying primality of any number by computation
- Using `decide`, `native_decide`, or `norm_num` to check arithmetic facts about specific large numbers
- Adding concrete `mullin_for_*` theorems that verify individual primes appear in the sequence
- Any approach whose strategy is "calculate and verify" rather than "prove abstractly"

**WHY:** Computing `seq 8` requires trial division to √38,709,183,810,571 — about 6 million divisions. This makes `lake build` take hours and contributes nothing to the proof.

**ALLOWED:** Only the small facts already in the codebase (primes ≤ 157, existing `Fact (Nat.Prime p)` instances). Do not add new ones.

## Dead Ends Catalog

**Before writing any new formalization, consult `EM/Meta/DeadEnds.lean` (authoritative dead-ends catalog).**

This catalog is maintained in `EM/Meta/DeadEnds.lean`; read the current entry count from `deadEndCount` there rather than trusting a number quoted here. Entries are classified by category code — **OS** (orbit-specificity), **TM** (technique mismatch), **SM** (scale mismatch), **CI** (circularity), **SF** (structurally false / counterexample), **CO** (definitional collapse), **DG** (decorrelation gap), **AG** (aggregate gap) — each with a weak-MC revival score 0–3. Do NOT attempt to formalize anything that maps onto a catalog entry. Key entries for the formalizer:
- #58 (MultCSBImpliesMMCSB FALSE), #61 (ArithLSImpliesMMCSB vacuous), #73 (SVE not provable from infra)
- #75 (PrimeArithLSImpliesMMCSB structural mismatch), #81 (CME → HOD FALSE for h≥2)
- #95 (spectral gap for deterministic walks), #96 (LoD scale mismatch), #99 (return product tautological)
- #104 (SD equivalence collapse to VCB — do not formalize SD separately)
- #105 (First passage / ExistentialCME = DH — do not formalize weaker "first hitting" hypotheses)
- #106 (VCB → CCSB without PED = PED itself — do not formalize ResamplingBound or VCB-based routes bypassing PED)
- #107 (Bottleneck Decorrelation Axioms — do not formalize abstract "class of sequences" VCB frameworks)
- #108 (Harper BDH inapplicable), #109 (Non-multiplicative Halász), #110 (Transition matrix convergence = CME)
- #111 (Rough Number Concentration for d=2 NoLongRuns — do not formalize structural-feature-based NoLongRuns proofs)
- #112 (Order-3 Möbius Death Function — constrains death curve geometry, not walk dynamics)
- #114 (Missing Prime Accumulation, Session 97): Pairwise Death Channel Independence = CME for single fiber. Self-consistent avoidance = §23. Transfer to orbit = SieveTransfer. Do NOT formalize `MissingPrimeAccumulation.lean`.
- #116 (Sieve-Theoretic Transfer for DSL, Session 114): Sieve axiom ω(r)~1/r IS EMDirichlet. Circular. Do NOT formalize sieve-based DSL proofs.
- #120 (SCD = SVE via Lyapunov telescope, Session 142): SelfCorrectingDrift is algebraically equivalent to SVE. Do NOT formalize new SCD-based proof strategies — they ARE SVE strategies restated.
- #123 (FourPointPCV, Session 146): Four-point population cross-term factorization = EQUIVALENCE COLLAPSE. Cross-TIME ≠ cross-MODULUS CRT independence. Maps to #84, #98, #115. All concrete DSL sub-strategies exhausted. Do NOT formalize FourPointPCV-based proof chains.
- #124 (Lyapunov-Fiber Coupling / T5.7, Session 154): J(N)=∑d(a)·F(a) recurrence contains active-fiber char sum = CME. EQUIVALENCE COLLAPSE. Do NOT formalize Lyapunov-fiber coupling approaches.

## Session 121-126 Formalizations

**Sessions 126-128 — WeylHittingBridge Proved + Dead End #117**:
- Session 126: Reformulated WeylHittingBridge from multiplier sums to walk sums. Added `MultCancelToWalkCancel` (open Prop — multiplier→walk cancellation gap, HARD).
- Session 127: `weyl_hitting_bridge_proved` — WeylHittingBridge PROVED via test function contradiction.
- Session 128: Dead End #117 — MultCancelToWalkCancel PROVED IMPOSSIBLE for EM-specific walks (multipliers {2,3} mod 5 give S_K=0 but |W_K|=Θ(K)). Transfer ≡ CCSB/CME.
- JSE→MC chain has **2 open Props**: JSE (hard), MultCancelToWalkCancel (hard, Dead End #117 ≡ CCSB/CME)
- EM/Ensemble/PT.lean now ~1900 lines, EM/Ensemble/Decorrelation.lean now 437 lines

**Session 125 — PerChiCancellationBridge PROVED** (EM/Ensemble/PT.lean, +263 lines):
- `per_chi_cancellation_bridge_proved : PerChiCancellationBridge` — Per-chi specialization of proved SD→VB→Concentration→Cancellation chain
- Proof structure: (1) Per-chi variance bound via induction on K with C=2, (2) Per-chi concentration via Markov inequality choosing K₀ = ⌈2/(ε²·δ)⌉+1, (3) Per-chi cancellation via squeeze to 0

**Session 121 — JSE→SD PROVED** (EM/Ensemble/PT.lean):
- `joint_step_equidist_implies_step_decorrelation` — JSE + nontrivial chi → SD (PROVED)
- `cross_term_density_decomp` — density decomposition of cross-term (PROVED, private)
- `sqfreeJointSeqCount_le_sqfreeCount`, `sqfreeJointSeqDensity_nonneg`, `sqfreeJointSeqDensity_le_one` — bounds (PROVED)

**New definitions**:
- `JointStepEquidist` (JSE) — open hypothesis, joint uniformity of (genSeq n j, genSeq n k) mod q
- `JointAccumulatorEquidist` (JAE) — open hypothesis, joint uniformity of accumulators
- `sqfreeJointSeqCount`, `sqfreeJointSeqDensity`

**Lean API note**: When working with ZMod q in theorem statements where Fintype is needed, use `letI : NeZero q := ⟨hq.ne_zero⟩` pattern before instantiating `Fintype (ZMod q)`.

## Sessions 186-188 — Pairwise Decorrelation → RSD Chain (ALL BRIDGES PROVED)

**EM/Population/ReciprocalSum.lean** (~1060 lines, 0 sorry):
- `PairwiseStepDecorrelation` — pairwise Cov → 0 (strictly weaker than k-wise, revives Dead End #125 for variance route)
- `LinearMeanGrowth` — ∃ κ > 0, ∀ K, ∃ X₀, ∀ X ≥ X₀, κ*K ≤ sfAvg (stronger than EnsembleMeanDivergence)
- `IndividualVarianceBound V` — per-step variance ≤ V
- `RecipSumConcentration` — REFORMULATED (Session 188) from Filter.Tendsto (nhds 0) to ε-δ form: ∀ M > 0, ∀ ε > 0, ∃ K₀, ∀ K ≥ K₀, ∃ X₀, ∀ X ≥ X₀, density ≤ ε
- **`individual_variance_quarter`** — IndividualVarianceBound(1/4) PROVED (from genSeq ≥ 2)
- **`psd_ivb_implies_variance_bound_proved`** — **PSDIVBImpliesVarianceBound PROVED** (Session 187, ~127 lines)
- **`chebyshev_concentration_proved`** — **ChebyshevConcentration PROVED** (Session 188, ~95 lines). One-sided Chebyshev + ceiling arithmetic. Key: K₀ = max(⌈2M/κ⌉+1, ⌈4C/(κ²ε)⌉+1), then CK/(κK-M)² ≤ 4C/(κ²K) ≤ ε.
- `finset_chebyshev` — one-sided Chebyshev at Finset level (~80 lines): if mean ≥ μ > M and var ≤ σ², then |{S<M}|/|S| ≤ σ²/(μ-M)²
- `density_mono_K` — density of {S_K < M} is non-increasing in K (monotonicity of partial sums)
- **`psd_lmg_implies_rsd`** — **THE ULTIMATE 2-HYPOTHESIS CHAIN**: PSD + LinearMeanGrowth → AlmostAllSquarefreeRSD (PROVED, all bridges eliminated)
- `dead_end_125_pairwise_revival` — landscape: (PSD + LMG → AASRSD) ∧ IVB(1/4) ∧ PSDIVBImpliesVB ∧ ChebyshevConc, ALL PROVED
- **Circular import avoided**: local `sfAvg`, `sfCov` defs (FirstMoment.lean transitively imports EM/Population/ReciprocalSum.lean)

**Key Lean APIs (Sessions 187-188)**:
- `Finset.sum_mul_sum` — (∑f)·(∑g) = ∑∑ f·g
- `Finset.sum_sub_distrib` — ∑(a-b) = ∑a - ∑b
- `Finset.add_sum_erase` — f(j) + ∑_{k≠j} f(k) = ∑_k f(k) (diagonal splitting)
- `Metric.tendsto_atTop` — unpacking Filter.Tendsto at nhds for metric spaces
- `Finset.le_sup` — extracting threshold from a finset sup
- `gcongr` — monotonicity goals with sums
- `Nat.le_ceil` — a ≤ ⌈a⌉ for real a
- `div_le_iff₀` / `div_lt_iff₀` — dividing out positives
- `mul_self_le_mul_self` — (0 ≤ a → a ≤ b → a² ≤ b²)
- `nlinarith` — excellent for quadratic inequality goals involving (κK-M)² bounds

**All analysis bridges now PROVED. Only 2 open hypotheses for AASRSD: PSD (number theory) + LinearMeanGrowth (first moment growth).**

## Session 190-191 — FirstMomentStep → LMG → PositiveDensityRSD Chain (ALL PROVED)

**EM/Population/ReciprocalSum.lean** (~1260 lines, 0 sorry):
- `PositiveDensityRSD` — ∃ δ > 0, for large K and X, density ≥ δ (weaker than AASRSD, needs only 1 hypothesis)
- **`lmg_implies_positive_density_rsd`** — LMG → PositiveDensityRSD PROVED (δ = κ/2, averaging lemma + ceiling arithmetic)
- `recipPartialSum_le_half_K` — S_K(n) ≤ K/2 deterministically PROVED
- `density_lower_bound_from_mean` — averaging lemma PROVED

**FirstMoment.lean** (~1133 lines, 0 sorry):
- **`ensembleAvg_sum_range`** — linearity of ensemble average: ensembleAvg X (∑ f) = ∑ ensembleAvg X f, PROVED (Finset.sum_div + Finset.sum_comm)
- **`first_moment_step_implies_lmg`** — **FirstMomentStep(κ) → LinearMeanGrowth PROVED** (~54 lines). Key: extract X_k from Tendsto via Filter.eventually_atTop, take X₀ = Finset.sup, linearity + pointwise bound.
- **`first_moment_step_implies_positive_density_rsd`** — FMS(κ) → PDRSD PROVED (composition)
- **`weak_mc_landscape`** — 3-part landscape (FMS→PDRSD, FMS→LMG, LMG→PDRSD) PROVED
- **`kappaPartial_three`** — kappaPartial 3 = 1/3 PROVED (native_decide + buchstabWeight_two + norm_num)
- **`kappaPartial_pos_at_three`** — 0 < kappaPartial 3 PROVED
- **Parity structure**: `genProd_one_even`, `genProd_even_of_pos`, `genProd_succ_odd`, `genSeq_ge_three` (all PROVED)
- **k=0**: `genSeq_zero_of_odd`, `ensembleAvg_k0_ge_quarter` (unconditional E≥1/4, PROVED)
- **SMLB chain**: `StepMeanLowerBound`, `smlb_implies_lmg`, `smlb_implies_positive_density_rsd`, `smlb_k0_unconditional` (all PROVED)
- **k=1 CRT**: `genSeq_one_of_mod6` (genSeq=3 for n≡1 mod 6), `sf_le_four_coprime6` (factor injection), `ensembleAvg_k1_ge_mod6_fraction` (all PROVED)
- **k=2 CRT** (Session 194): `genProd_two_of_mod6` (genProd(n,2)=6n), `genSeq_two_of_mod30` (genSeq=5 for n≡19 mod 30), `k2_crt_landscape` (all PROVED)
- **PartialSMLB** (Session 194): `PartialSMLB c K₀` (def: finitely many steps), `partial_smlb_implies_mean_lower_bound` (⟹ E[S_{K₀+1}] ≥ c·(K₀+1)), `partial_smlb_zero_unconditional` (PartialSMLB(1/4,0) unconditional), all PROVED
- **Mod6DensityLB** (Session 194): `Mod6DensityLB` (open Prop), `mod6_density_implies_smlb_k1` (density ⟹ SMLB at k=1 with c=1/24, PROVED)

**Key technique**: `simp [ensembleAvg, sqfreeCount]` bridges ensembleAvg ↔ sfAvg (private in EM/Population/ReciprocalSum.lean) since both reduce to the same kernel term.

## Session 195 — Mod-3 Bridge: AccumMod3LB → SMLB → PositiveDensityRSD (ALL PROVED)

**CRT.lean** (479 → 603 lines, 0 sorry):
- **`genSeq_eq_three_of_genProd_mod3`** — When genProd(n,k) ≡ 2 mod 3, k ≥ 1, genSeq(n,k) = 3. Proof: ZMod.natCast_eq_zero_iff + push_cast + decide gives 3 | genProd+1; minFac_le_of_dvd gives ≤3; genSeq_ge_three gives ≥3; genProd_succ_odd excludes 2.
- **`mod3_numerator_bound`** (private) — #{sf n : genProd ≡ 2 mod 3}/3 ≤ ∑ 1/genSeq, via Finset.sum_filter_add_sum_filter_not
- **`ensembleAvg_ge_mod3_density`** — sqfreeAccumDensity(X,k,3,2)/3 ≤ ensembleAvg(X, 1/genSeq(·,k))
- **`AccumMod3LB c`** — Open Prop: ∀ k, ∃ X₀, ∀ X ≥ X₀, c ≤ sqfreeAccumDensity X k 3 2
- **`accum_mod3_implies_smlb`** — AccumMod3LB(c) → SMLB(min(1/4, c/3)) PROVED
- **`accum_mod3_implies_positive_density_rsd`** — AccumMod3LB → PositiveDensityRSD PROVED
- **`ewe_landscape`** — 3-route landscape (FMS, SMLB, AccumMod3LB → PRSD) PROVED

**Key Lean APIs**:
- `ZMod.natCast_eq_zero_iff` + `push_cast` + `decide` — canonical way to prove `p ∣ (n + 1)` from `(n : ZMod p) = p - 1`
- `Finset.sum_filter_add_sum_filter_not` — splitting ensemble sums by predicate
- `div_le_div_of_nonneg_right` — dividing both sides of inequality by positive sqfreeCount
- `exact_mod_cast` — lifting `genSeq n k = 3 : Nat` to `(genSeq n k : ℝ) = 3`

**CRT tower pattern**: genSeq_zero_of_odd (k=0→2), genSeq_one_of_mod6 (k=1→3), genSeq_two_of_mod30 (k=2→5). Same proof structure: show target odd, coprime to smaller primes, divisible by target prime, exclude composites, omega. Modulus grows as primorial (6, 30, 210, ...).

**Weak-MC chain now CLOSED to 1 hypothesis: FirstMomentStep(κ).** SMLB is a weaker alternative (no convergence, just lower bound). PartialSMLB allows finite-step unconditional results.

## Session 196 — Generalized Death Density Bridge (ALL PROVED)

**CRT.lean** (603 → 864 lines, +261 lines, 0 sorry):

**MFREConditional infrastructure** (lines 574-657):
- New defs: `sqfreeClassCount` (count of squarefree in residue class mod q), `sqfreeClassMinFacCount` (count with specific minFac value), `condMinFacDensity` (conditional density of minFac mod q)
- `sqfreeClassCount_pos` — class count positive for q ≥ 3 PROVED
- `condMinFacDensity_nonneg` — conditional density ≥ 0 PROVED
- `condMinFacDensity_le_one` — conditional density ≤ 1 PROVED
- 3 open hypotheses: `MFREConditional`, `EnsembleSelectionLemma`, `MFRECondImpliesSMLB`

**Generalized death density** (lines 659-809):
- **`ensembleAvg_ge_death_density`** — KEY THEOREM: for ANY prime q ≥ 3 and step k ≥ 1, E[1/genSeq(·,k)] ≥ death_density(q)/q. PROVED.
  - Proof pattern: on "death fiber" {genProd ≡ -1 mod q}, q | genProd+1 so genSeq ≤ q, giving 1/genSeq ≥ 1/q. Complement ≥ 0.
  - Key lemma: `genSeq_le_of_genProd_neg_one` using `push_cast; rw [hmod]; ring` + `ZMod.natCast_eq_zero_iff`
- `DeathDensityLB q c` — open Prop: ∀ k, ∃ X₀, ∀ X ≥ X₀, c ≤ sqfreeAccumDensity X k q (q-1)
- `death_density_implies_smlb` — DeathDensityLB(q,c) → SMLB(min(1/4,c/q)) PROVED
- `death_density_implies_prsd` — DeathDensityLB(q,c) → PositiveDensityRSD PROVED
- `accumMod3LB_iff_deathDensity3` — AccumMod3LB(c) ↔ DeathDensityLB(3,c) PROVED (subsumption via `(-1 : ZMod 3) = 2` by `decide`)
- `ewe_landscape_extended` — 4-route landscape (FMS, SMLB, AccumMod3LB, DeathDensityLB → PRSD) PROVED

**Key technique**: `-1` in ZMod q for general q uses `push_cast; rw [hmod]; ring` to get `(genProd n k + 1 : ZMod q) = 0`, then `ZMod.natCast_eq_zero_iff` for divisibility. The mod-3 subsumption uses `(-1 : ZMod 3) = (2 : ZMod 3)` by `decide`.

**Weak-MC chain now has MULTIPLE equivalent entry points**: FMS(κ), SMLB(c), AccumMod3LB(c), DeathDensityLB(q,c) for any prime q ≥ 3. All route to PositiveDensityRSD.

## Current priority formalization targets

**Sessions 130-135: Hilbert → ALS chain nearly complete.** The end-to-end chain composition `hilbert_chain_als` is PROVED. Constants relaxed to 1/δ+N (Cohen trick deferred). **Only HilbertInequality1 remains open** (CscPartialFraction + CscBilinearImpliesGramOffDiag PROVED Session 131, hilbert_lifted_bound + same_r_antisymmetry + hilbert_csc_circular_of_cesaro PROVED Session 134, CrossRCesaroConvergence PROVED Session 135):

1. ~~**CscPartialFraction** — **PROVED Session 131** (229 lines)~~
   - `csc_partial_fraction_proved : CscPartialFraction` in `EM/IKCh7Hilbert.lean`

2. ~~**CscBilinearImpliesGramOffDiag** — **PROVED Session 131** (~173 lines)~~
   - `csc_bilinear_implies_gram_offdiag_proved : CscBilinearImpliesGramOffDiag` in `EM/IKCh7Hilbert.lean`

3. **HilbertInequality1** (~200-300 lines, hardest — δ=1 core case):
   - File: `EM/IKCh7Hilbert.lean` (open Prop, defined Session 132)
   - Statement: `|∑∑_{r≠s} z_r z̄_s / (λ_r - λ_s)| ≤ π ∑ |z_r|²` for 1-separated λ_r
   - `hilbert_rescale` (PROVED Session 132): HilbertInequality1 → HilbertInequality
   - **Primary approach**: Oleszkiewicz (1993, AMM 100(3):276-280) elementary geometric proof for integer-spaced, then bootstrap.
   - **No formalization exists in any proof assistant** (unprecedented — confirmed Session 109, 128 literature searches)

4. ~~**CrossRCesaroConvergence** — **PROVED Session 135** (~490 lines)~~
   - `cross_r_cesaro_convergence_proved : CrossRCesaroConvergence` in `EM/IKCh7Hilbert.lean`
   - Proof via product-index trick: F(K) = same-r(=0 by antisymmetry) + cross-r, cross-r factors as c_r·conj(c_s)·RealDS(K), Fejér sum identity (induction), parity lemma (`neg_one_pow_congr`), ML Cesàro convergence, per-pair limit, assembly via `tendsto_finset_sum` + `Filter.Tendsto.const_mul` + `le_of_tendsto'`
   - Key helpers: `fejer_sum_eq_cesaro_sum'`, `neg_one_pow_add_eq_natAbs_sub`, `ml_cesaro_convergence`, `per_pair_cesaro_limit`
   - Key Lean APIs: `Finset.sum_nbij'` (bijective reindexing), `Complex.ofReal_sum`, `Fin.sum_univ_eq_sum_range`, `Filter.Tendsto.cesaro` (not dot notation: `tendsto_finset_sum`, not `Filter.Tendsto.finset_sum`)

5. **HilbertCscBilinearBridge** (Cohen trick — **CAN BE BYPASSED**):
   - File: `EM/IKCh7Hilbert.lean` (open Prop)
   - Statement: converts circular spacing (1/δ) to non-circular (1/δ-1)
   - **Session 135 bypass analysis**: thread `IsCircularSpaced` through downstream chain (GramOffDiag → ALS → MLS/Farey). All downstream applications (Farey fractions, unit points) are circularly spaced. ~460 lines of copy-adapt eliminates this Prop entirely.
   - **Recommended next step**: implement the circular-spacing bypass (Session 136 target)

NOTE: `MultCancelToWalkCancel` is the HARD open Prop. Do NOT attempt to prove it — it is equivalent to CCSB/CME (Dead End #117).

### Sessions 162-163 — AdelicEquidist extensions + EM/Adelic/Profinite.lean

**EM/Adelic/Equidist.lean** (656 lines, 0 sorry): Extended with adelic decomposition landscape + Fourier inversion bridge.
- Defs: `CRTMultiplierFiber` (open Prop — CRT fiber char sum independence), `CPDImpliesCRTFiber` (open Prop)
- Session 162: `cme_iff_adelic` (CME ↔ AdelicEquidist biconditional), `crt_fiber_mme_implies_cme/mc/ccsb`, `cpd_mme_implies_mc`, `adelic_landscape` (5-part conjunction)
- Session 163: `conditional_sum_fourier_expansion` (private, Fourier inversion via char_indicator_expansion), `crt_fiber_implies_mwi_proved` (**CRTMultiplierFiber + MME → MWI, PROVED ~145 lines** via MulChar.equivToUnitHom + MulChar.coe_toUnitHom), `mme_iff_walk_autocorrelation` (MME ↔ vanishing lag-1 walk autocorrelation, PROVED via walk_shift_one_correlation + RCLike.norm_conj), `ccsb_mme_landscape` (CME decomposition witness)
- **CRTFiberImpliesMWI is now PROVED** (was open Prop). Route 3 of adelic_landscape now unconditional.
- Import: `EM.Equidist.Fourier` + `EM.LargeSieve.Spectral` + `EM.CME.Decomposition` + `EM.Transfer.CRTPointwise` + `EM.Equidist.SelfCorrecting`

**Key Lean APIs discovered (Session 168)**:
- `Polynomial.Gal`: Galois group of a polynomial, imported via `Mathlib.FieldTheory.PolynomialGaloisGroup`. Access: `(f : Polynomial K).Gal`. Must be `noncomputable` (e.g., `noncomputable abbrev ffGaloisGroup ... := (d.ffProd n + 1).Gal`).
- `Polynomial.natDegree_add_of_lt`: If `natDegree p < natDegree q`, then `natDegree (p + q) = natDegree q`. Useful for degree of `ffProd n + 1` (adding constant 1 to high-degree polynomial).
- `Polynomial.natDegree_one`: `natDegree (1 : Polynomial K) = 0`.

**Key Lean APIs discovered (Session 163)**:
- `MulChar.equivToUnitHom`: bijection `DirichletCharacter ℂ q ≃ (ZMod q)ˣ →* ℂˣ`. Use `.injective` for injectivity, manual `ext` proofs for surjectivity.
- `MulChar.coe_toUnitHom`: coercion bridge `ψ_D(↑u) = ↑(ψ_U u)` where ψ_D is DirichletCharacter and ψ_U is unit hom.
- `walkTelescope_char_norm_one`: ‖χ(u)‖ = 1 for unit characters on walk terms. Useful for norm bounds.
- `RCLike.norm_conj`: ‖conj(z)‖ = ‖z‖. Key for MME ↔ autocorrelation proof.
- `walk_shift_one_correlation` (EM/Equidist/SelfCorrecting.lean): ∑ χ(w(n))·conj(χ(w(n+1))) = conj(∑ χ(m(n))). Links walk autocorrelation to multiplier character sums.

**EM/Adelic/Profinite.lean** (175 lines, 0 sorry, NEW): Weyl criterion for Ẑ× = ∏_p (Z/pZ)×.
- Defs: `collapseTime`, `UniformProfiniteEquidist` (UPE — product character sums o(N) for any finite set of distinct primes), `FiniteLevelEquidist` (walk visits every position cofinally — NOT proved from SE+PRE, gap is algebraic vs dynamical), `UniformityGap` (FLE → UPE), `CCSBCPDImpliesUPE` (open Prop)
- Proved: `uniform_profinite_implies_ccsb` (UPE → CCSB, k=1 via `Fin.prod_univ_one`), `uniform_profinite_implies_mc` (UPE → MC via CCSB), `uniform_profinite_implies_cpd` (UPE → CPD, k=2 via `Fin.prod_univ_two` + `![q,r]` matrix notation), `profinite_routes_to_mc` (3-part landscape)
- Import: `EM.Adelic.Equidist`

**Key technique for Fin k → Nat**: Use `![q, r]` (matrix notation) for `Fin 2 → Nat`. Case splitting: `fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp_all [qs])`. Products: `Fin.prod_univ_one` (Fin 1), `Fin.prod_univ_two` (Fin 2).

**Assessment**: CRTMultiplierFiber and CPDImpliesCRTFiber remain open. CPDImpliesCRTFiber assessed at 6/10 feasibility (orbit-dependent Fourier coefficients are the obstruction). **CCSBCPDImpliesUPE is UNPROVABLE (Dead End #125, Session 164)**: XOR counterexample — three unit-modulus sequences with all pairwise cancellation but triple product = N. Do NOT attempt to prove this. FiniteLevelEquidist is NOT proved from existing infrastructure (SE+PRE give subgroup generation, not cofinal visits).

### Session 259 — EM/Adelic/ProfiniteGeneration.lean (composite-modulus generation)

**EM/Adelic/ProfiniteGeneration.lean** (177 lines, 0 sorry, NEW): Generalizes PRE from prime to composite modulus.
- Defs: `primeUnitsBelow N` (units from primes < N coprime to N), `emMultiplierUnits N` (units from EM seq terms)
- Proved: `primeUnitsBelow_generate` (primes < N generate (ZMod N)× — pure NT, strong induction via minFac + `Nat.Coprime.coprime_dvd_left`), `mc_below_implies_full_generation` (MCBelow → full gen via `Subgroup.closure_mono`), `mc_implies_full_generation` (MC → ∀ N > 1), `profinite_generation_landscape` (3-clause)
- Import: `EM.Equidist.Bootstrap`

**Key technique**: `ZMod.unitOfCoprime` for composite moduli (vs `Units.mk0` for prime). Coprimality propagation: `Nat.Coprime.coprime_dvd_left` transfers gcd(m,N)=1 to factors. Round-trip: `ZMod.val_coe_unit_coprime` + `ZMod.natCast_zmod_val`.

### Session 158 — EM/Ensemble/FiberAutonomy.lean (structural infrastructure)

**EM/Ensemble/FiberAutonomy.lean** (255 lines, 0 sorry, 9 theorems): Formalizes that CRT fiber dynamics is autonomous and q-walk is a readout. Key theorems: `genWalkZ_multi_step`, `crt_fiber_determines_genSeq`, `crt_fiber_propagates`, `walk_readout_from_multipliers`, `walk_death_is_fiber_condition`. Import: `EM.Group.CRT` + `EM.Ensemble.EM`.

**Assessment**: Fiber autonomy = CRT invariance restated. Provides NO new leverage for DSL. Do NOT build further fiber-autonomy-based infrastructure.

### Session 160 — EM/Transfer/SieveConstraint.lean (structural infrastructure)

**EM/Transfer/SieveConstraint.lean** (261 lines, 0 sorry, 21 theorems, 2 defs): Formalizes the prime support of EM accumulators. Key defs: `emSupport n` ({seq(0),...,seq(n)}), `genSupport m k` ({genSeq(m,0),...,genSeq(m,k-1)}). Key theorems: `emSupport_prime/card/dvd_prod/not_dvd_succ`, `prod_succ_mod_emSupport` (the "+1 shift sieve constraint"), `seq_succ_not_mem_emSupport`, `emSupport_mono/ssubset`, `genSupport_card/prime/dvd_genProd/not_dvd_succ`, `genSupport_two_eq_seq_image`, `emSupport_succ`. Import: `EM.Transfer.IntegerDioph` + `EM.Ensemble.Structure`.

**Note**: `genSupport 2 (k+1) = emSupport k` is FALSE (index shift). Correct relationships: `genSupport_two_eq_seq_image` and `emSupport_succ`.

**Assessment**: Infrastructure for exposition. The "1 mod growing S" attack direction assessed at 0-1/10 feasibility (Sessions 160 Agents D+C). SubProd ensemble and hypercube Fourier map to Dead End #90 (orbit-specificity gap). Do NOT build SubProd-based infrastructure.

### Session 168 — EM/FunctionField/Analog.lean extended (monodromy infrastructure)

**EM/FunctionField/Analog.lean** extended from 360→886 lines (0 sorry). Added Sections 8-15: Frobenius interpretation, FFLM hypothesis, Deligne equidistribution, monodromy chain, sequential gap, SE↔abelian monodromy, +1 shift geometry, Dead End #127 addendum, updated landscape.
- New defs: `ffGaloisGroup` (using `Polynomial.Gal`), `ffGaloisOrder`, `FFLargeMonodromy`, `DeligneEquidistribution`, `FFCME`, `FFLMChainImpliesFFMC`, `FFCMEImpliesFFMC`, `FFSEFromAbelianMonodromy`
- Proved: `ffProdPlusOne_natDegree` (deg(ffProd(n)+1) = deg(ffProd(n))), `ffProd_natDegree_strict_mono` (StrictMono)
- Import: `Mathlib.FieldTheory.PolynomialGaloisGroup`, `Mathlib.Algebra.Field.ZMod`
- **Dead End #129**: FFLM→Deligne→FF-CME route DEAD. Cyclotomic counterexample: Φ₅(t) over F_2 has Gal = Z/4Z. Do NOT extend monodromy infrastructure further.

### ANT Chain — COMPLETE (Sessions 148-155)

**Status**: The internal ANT chain is **FULLY PROVED**. Both reductions (`PrimePowerStripping`, `PrimeLogToReciprocal`) are proved with zero sorry. The only remaining external dependency is `WeightedPNTinAP` (= Wiener-Ikehara = Mertens in APs), which is standard ANT.

**Proved chain**:
```
EM/Population/Tauberian.lean (557 lines, 0 sorry):
  ↓ one_sided_tauberian_upper PROVED
  ↓ residueClass_tsum_both_bounds PROVED
  ↓ dirichlet_primes_in_ap PROVED (from Mathlib)
  ↓ real_wiener_ikehara_implies_wpnt PROVED
  ↓ prime_power_stripping_proved PROVED (Session 151)
  ↓ wpnt_implies_primes_equidist PROVED (parameterized chain)

EM/Population/AbelChain.lean (651 lines, 0 sorry):
  ↓ hasDerivAt_log_log, integral_inv_mul_log, etc. (FTC infrastructure)
  ↓ prime_log_to_reciprocal_proved PROVED (Session 155, discrete Abel summation)
  ↓ wpnt_implies_primes_equidist_proved PROVED (composed: WPNT → PrimesEquidistInAP)
  ↓ ant_chain_both_proved PROVED (conjunction witness)
```

**Do NOT formalize further ANT targets** — the chain is complete. The remaining open question is the external `WeightedPNTinAP` hypothesis, which would require importing/formalizing Wiener-Ikehara (not in scope for this project).

**CRITICAL WARNING (Session 149)**: `AbelSummationPNT` does NOT follow from `RealWienerIkeharaTauberian` via standard Abel summation — gives O(log log x), not O(1).

**Key Mathlib infrastructure** (all PROVED):
- `Nat.forall_exists_prime_gt_and_modEq` — Dirichlet's theorem (NOW BRIDGED in EM/Population/Tauberian.lean)
- `LSeries_residueClass_lower_bound` — lower bound near pole: 1/φ(q)·1/(x-1)-C
- `continuousOn_LFunctionResidueClassAux` — auxiliary function continuous on Re(s)≥1
- `LFunctionResidueClassAux_real` — aux at real s is real-valued
- `eqOn_LFunctionResidueClassAux` — aux = LSeries - pole identity
- `sum_mul_eq_sub_sub_integral_mul` — Abel summation (full API in `AbelSummation.lean`)

**Lean API note for OneSidedTauberian**: The key trick for `residueClass_tsum_eq_aux_plus_pole` is:
```lean
open ArithmeticFunction.vonMangoldt LSeries in  -- opens both namespaces
simp_rw [... _root_.LSeries, term]  -- _root_ disambiguates LSeries function from namespace
```

**What NOT to do**:
- Do NOT reprove things in EM/Population/Tauberian.lean — they're done (693 lines, 0 sorry).
- Do NOT try to bypass the Tauberian using divergence alone — divergence ≠ density (Session 147).
- Do NOT axiomatize `RealWienerIkeharaTauberian` as a permanent open Prop — `WienerIkeharaForWeightedPNT` (≡ WeightedPNTinAP by `Iff.rfl`) is the clean hypothesis.
- Do NOT attempt to prove `AbelSummationPNT` from `RealWienerIkeharaTauberian` via standard Abel summation — it gives O(log log x) not O(1) (Session 149, confirmed by both literature scout and attack-analytic agents). Mertens' theorem requires Siegel-Walfisz error terms or direct Dirichlet series methods.

### COMPLETED formalization targets (do NOT redo)
- **WeylHittingBridge PROVED (Session 127)**: `weyl_hitting_bridge_proved` in EM/Ensemble/PT.lean via test function contradiction. Walk character cancellation → walk hits -1 cofinally. JSE→MC chain now has 2 open Props: JSE, MultCancelToWalkCancel. Dead End #117 (Session 128): MultCancelToWalkCancel ≡ CCSB/CME — PROVED IMPOSSIBLE for EM-specific walks.
- **PerChiCancellationBridge (Session 125)**: `per_chi_cancellation_bridge_proved` in EM/Ensemble/PT.lean (+263 lines). Per-chi version of SD→VB→Concentration→Cancellation chain. Energy induction with C=2, Markov bound choosing K₀ = ⌈2/(ε²·δ)⌉+1, squeeze to 0 via cross terms bounded by `Nat.ceil_le`. Key APIs: `Nat.ceil_le`, `Metric.tendsto_atTop`, `Complex.normSq_nonneg`.
- **Ensemble Concentration Chain (Session 119)**: `CharVarianceImpliesConcentration` PROVED (`char_variance_implies_concentration_proved` in EM/Ensemble/Decorrelation.lean, ~58 lines). Reformulated `EnsembleCharSumConcentration` from `Tendsto` to pointwise (ε, δ) bounds. Added `normSq(χ(a)) ≤ 1` condition. Swapped `CharSumVarianceBound` quantifiers to `∀ K ∃ X₀`. Updated `char_concentration_implies_cancellation` to use `Metric.tendsto_atTop`. `DecorrelationImpliesVariance` PROVED (`decorrelation_implies_variance_proved` in EM/Ensemble/PT.lean, ~200 lines). Induction on K with C=2. Helper lemmas: `genSeqCharEnergy_zero/succ`, `ensembleAvg_le_of_pointwise/sum/add`, `cross_term_bound_from_sd`. Key APIs: `Finset.sum_comm`, `Nat.ceil`, `Metric.tendsto_atTop`, `Complex.normSq`.
- **Ensemble PT Props closed (Session 118)**: `GenHittingImpliesGenMC` PROVED (+107 lines, 3 theorems: `gen_exists_bound`, `gen_captures_target`, `gen_hitting_implies_gen_mc_proved`). `EnsembleMultEquidistImpliesCharMeanZero` PROVED (+50 lines, 2 theorems: `ensembleCharMean_eq_ofReal_density_sum`, `ensemble_mult_equidist_implies_char_mean_zero`). Statement fix: added nontrivial character conditions (chi(0)=0, ∑chi=0). Both in EM/Ensemble/PT.lean and EM/Ensemble/CRT.lean. Key APIs: `tendsto_finset_sum`, `Complex.continuous_ofReal.tendsto`, `Filter.Tendsto.mul`, `tendsto_zero_iff_norm_tendsto_zero`.
- **Ensemble PT framework (Session 117)**: 3 new files (905 lines, 25 theorems, 0 sorry). `EM/Ensemble/EM.lean` (114 lines): `genWalkZ`, `genMultZ` defs; `genWalkZ_succ` (walk recurrence), `genWalkZ_zero` (initial value), `genWalkZ_two_eq_walkZ`/`genMultZ_two_eq_multZ` (standard EM bridge), `genWalkZ_eq_neg_one_iff` (hit characterization), `genWalkZ_two_eq_neg_one_iff`. `EM/Ensemble/CRT.lean` (~470 lines): `sqfreeAccumCount`, `sqfreeSeqCount`, `sqfreeAccumDensity`, `ensembleCharMean` defs; `SquarefreeResidueEquidist`, `CRTPropagationStep`, `AccumulatorEquidistPropagation`, `EnsembleMultiplierEquidist` (open Props); `sre_crt_implies_accum_equidist` (SRE+CRT→AEP by induction), `ensembleCharMean_eq_density_sum` (density decomposition), `ensemble_mult_equidist_implies_char_mean_zero` (PROVED Session 118). `EM/Ensemble/PT.lean` (~475 lines): `GenMullinConjecture`, `EnsembleEquidistImpliesDecorrelation`, `DecorrelationImpliesVariance` defs; `ensemble_decorrelation_chain` (4-layer chain), `ensemble_crt_equidist_chain` (SRE+CRT+Bridge→EME), `ensemble_pt_master` (6-hypothesis master), `gen_mc_two_implies_mc` (generalized→standard MC bridge), `dsl_closes_all` (DSL→MC∧CCSB), `gen_hitting_implies_gen_mc_proved` (PROVED Session 118), `equidist_implies_char_mean_vanishing_proved` (PROVED Session 118).
- **Cofactor Identity / "+1 Shift" infrastructure (Session 115)**: `EM/Reduction/DSLInfra.lean` (+204 lines, 13 theorems, 0 sorry). `euclidCofactor` def (P(n)+1)/seq(n+1), `cofZ` def (cofactor mod q). `euclid_cofactor_mul` (seq(n+1)·cof(n)=P(n)+1), `shifted_walk_eq_mult_mul_cof` (w(n)+1=m(n)·c(n)), `walkZ_eq_neg_one_iff_cofZ_zero` (hit ↔ cofZ=0), `cofZ_ne_zero_of_alive` (alive ↔ cofZ≠0), `char_shifted_walk_eq_char_mult_mul_char_cof` (character multiplicativity through cofactor), `shifted_walk_ne_zero` (w(n)+1≠0 when alive), plus supporting lemmas for character decomposition. Key: genuine algebraic content beyond telescope identity.
- **EMDImpliesCME factorization + Fiber Energy (Session 114)**: `EM/CME/Decomposition.lean` (+186 lines, 3 theorems, 0 sorry). `visit_count_sum_eq` (∑V(a,N)=N partition), `emd_vcb_implies_cme` (EMD+VCB→CME), `emd_vcb_implies_mc` (EMD+VCB→MC). `EM/Reduction/DSLInfra.lean` (+218 lines net, 4 theorems, 0 sorry). `feb_implies_cme` (FEB→CME, closes FEB↔CME equivalence), `total_cross_term_eq_sum_fiber` (cross term fiber decomposition), `fiber_energy_lower_bound` (Cauchy-Schwarz), `cross_term_implies_cme` (CTC+FEB→CME). `EM/Ensemble/Decorrelation.lean` (+108 lines, 3 theorems, 0 sorry). `genSeqCharEnergy_nonneg`, `finset_markov_density`, `char_variance_density_bound`. Key insight: EMDImpliesCME factors as EMD+VCB→CME. FEB↔CME fully proved. CTC→FEB is the active-fiber selection gap.
- **Packing bound + improved ALS (Session 113)**: `EM/IK/Ch7AdditiveLS.lean` (+189 lines, 6 theorems, 0 sorry). `gramMatrix_offdiag_bound_dist` (off-diagonal bound via circular distance), `round_sep_delta_le_half` (δ ≤ 1/2 from separation), `round_sep_card_le` ((R-1)δ ≤ 1 via pigeonhole bin function), `round_sep_card_le_inv` (R-1 ≤ 1/δ), `gram_row_sum_improved` (row sum ≤ N + 1/(2δ²)), `gram_als_improved` (ALS with R-independent constant N + 1/(2δ²)). Key technique: bin function f(i) = ⌊fract(αᵢ)/δ⌋, injectivity via contradiction + `round_le`. Packing bound proof uses `Fintype.card_le_of_injective`.
- **Linnik Small QNR (Session 109)**: `EM/IK/Ch7SieveApplications.lean` (+93 lines, 4 theorems, 0 sorry). `four_is_qr_mod` (4=2² is QR mod p≥5, trivially), `linnik_filter_subset_small` (primes violating LinnikSmallQNR ⊆ {primes < 5}), `card_primes_lt_five` (≤2 primes below 5), `largeSieveAsSieve_implies_linnik_proved` (LargeSieveAsSieveImpliesLinnik PROVED). Key insight: the formalized LinnikSmallQNR statement is trivially true because 4=2² is always a QR mod p≥5. The hard Linnik theorem (QNR ≤ p^ε) would need Burgess character sum bounds.
- **Gram sin ratio identities (Session 108)**: `EM/IK/Ch7AdditiveLS.lean` (+84 lines, 5 theorems, 0 sorry). `gramMatrix_eq_geom_closed_form` (geometric series closed form for off-diagonal Gram entries), `gramMatrix_mul_eAN_sub_one` (algebraic identity G·(e-1) = e^N-1), `gramMatrix_norm_le_two_div` (norm bound ≤ 2/‖e-1‖), `gramMatrix_norm_eq_sin_ratio` (Dirichlet kernel: ‖G‖ = |sin(Nπθ)|/|sin(πθ)|), `gramMatrix_norm_sq_eq_sin_sq_ratio` (squared form). These are the direct prerequisites for the Hilbert inequality application to GramOffDiagBilinearBound.
- **FareyLargeSieveProper (Session 106)**: `EM/IK/Ch7SieveApplications.lean` (+174 lines, 2 theorems, 0 sorry). `coprime_frac_unique` (private: distinct reduced fractions with same value → same numerator/denominator), `als_implies_farey_large_sieve_proper` (ALS → FareyLS). Proof: Q=1 via Cauchy-Schwarz, Q≥2 via Sigma finset → Fin R + IsSpaced + coprime_frac_unique + farey_spacing_proved. Key lesson: For Sigma type equality where the family is constant (`fun _ : ℕ => ℕ`), use `Sigma.ext_iff.mpr ⟨hqeq, heq_of_eq hbeq⟩` rather than dependent elimination.
- **SuperExponentialGrowth (Session 105)**: `EM/SDDS/Bridge.lean` (+76 lines, 6 theorems, 0 sorry). `seq_fiber_finite`, `seq_bounded_indices_finite`, `seq_eventually_gt`, `prod_ge_mul_pow`, `log_prod_ge_of_seq_large`, `em_super_exponential_growth`. Uses injectivity + Real.log + pigeonhole.
- **CoprimeCascade (Session 104)**: `EM/SDDS/Dynamics.lean` (+28 lines, 4 theorems, 0 sorry). `SDDS.orbit_dvd_orbit_succ`, `SDDS.orbit_dvd_orbit`, `SDDS.mult_dvd_orbit_succ`, `SDDS.coprimeCascade`. Proved for ALL SDDS (not just emSDDS). Key: orbit recurrence gives divisibility, transitivity chains it.
- **CRT Fiber Independence & NoAlgebraicObstruction (Session 100)**: `EM/Transfer/CRTFiber.lean` (297 lines, 10 theorems, 0 sorry). Part 1: `nao_set_eq_range`, `se_implies_nao` (SE → NAO for emSDDS, **closes SDDS open hypothesis**), `mc_below_pre_implies_nao`. Part 2: `crt_pair_surjective` (CRT via Bezout coefficients from `IsCoprime`), `dvd_independent_of_residue`, `crt_unit_pair_surjective`. Part 3: `death_channel_disjoint`/`death_channel_disjoint'`, `death_value_mechanism` (c·(-c⁻¹)=-1), `residue_class_dichotomy`, `death_channel_nonempty`. Key lesson: Use `IsCoprime → ⟨u, v, huv⟩` (Bezout) for CRT surjectivity rather than `ZMod.chineseRemainder` ring equivalence — cleaner in Lean 4. Bridge `emSDDS_mult_eq_multZ` + `Units.ext` connects SDDS multiplier set to `Set.range` form.
- **Safe Prime DH Dichotomy (Session 98)**: `EM/Group/DepartureGraph.lean` grew 393→641 lines (+248). New sections: ComplementGeneration (`closure_compl_singleton_eq_top`, `closure_eq_top_of_compl_singleton_subset`), TargetAvoidance (`walk_hits_target_iff`, `departure_avoids_death_value`, `departure_set_excludes_death_value`, `infinite_departures_avoiding_death`), SafePrimeDichotomy (`avoidance_compatible_with_generation`, `se_compatible_with_dh_failure`, `safe_prime_order_ge_four`, `safe_prime_compl_generates`, `safe_prime_se_dh_compatible`, `dh_failure_distributional_gap`). Key insight: DH failure is analytically invisible to subgroup lattice.
- **SDDS Framework (Session 97)**: 3 new files (447 lines total, zero sorry).
  - `EM/SDDS/Dynamics.lean` (168 lines): `FactoringRule`, `minFacRule`, `SDDS`, `emSDDS`, orbit/walk/mult defs, 5 open hypotheses, 3 proved theorems.
  - `EM/SDDS/Bridge.lean` (153 lines): `euclid_minFac_eq_nat_minFac` (antisymmetry bridge), `emSDDS_orbit_eq_prod` (inductive), `emSDDS_walk_eq_walkZ`, `emSDDS_mult_eq_multZ`, `sme_implies_walkZ_hits_neg_one`.
  - `EM/SDDS/Reduction.lean` (126 lines): `StrongSME` def, `strong_sme_implies_hh`, `strong_sme_implies_mc`, `sme_implies_dvd_euclid`, `sme_for_all_implies_euclid_divisibility`.
  - Key lesson: Bridge `Euclid.minFac` ↔ `Nat.minFac` via `Nat.le_antisymm` using both minimality properties. Basic SME gives one hit; need `StrongSME` (cofinal) for `hh_implies_mullin`.
- **Single Hit Theorem (Session 95)**: `EM/Equidist/Bootstrap.lean` (617 → 716 lines, +99). 1 def + 5 theorems: `SingleHitHypothesis`, `dh_implies_single_hit`, `hh_implies_single_hit`, `single_hit_pre_implies_mullin`, `single_hit_implies_mc`, `dh_mc_via_single_hit`. Key insight: SHH includes `mc_below q` as extra hypothesis (available from induction), making it strictly weaker than DH but equally powerful for MC.
- **Safe Prime Lattice + Infinite Recurrence (Session 94)**: `EM/Group/DepartureGraph.lean` (255 → 393 lines, +138). 8 new theorems: `exists_infinite_fiber_of_finite` (pigeonhole), `infinite_fiber_mem_visitedSet`, `infinite_departures_at_recurrent`, `dvd_two_mul_prime_iff`, `card_subgroup_of_order_two_mul_prime`, `card_proper_subgroup_le`, `multiplier_closure_ne_top_of_confined`, `generating_escapes_proper`. 1 new definition: `IsSafePrime`. Key lessons: `Finite.exists_infinite_fiber` returns `Infinite (f ⁻¹' {y})` (subtype) — bridge to `Set.Infinite` via `Set.infinite_coe_iff` + `convert`. `mul_dvd_mul_iff_left` for `2e ∣ 2p → e ∣ p`. `Nat.prime_two.coprime_iff_not_dvd`. `Subgroup.eq_top_of_card_eq` needs `Finite H` instance via `Nat.finite_of_card_ne_zero`.
- **Departure Graph Foundations (Session 93)**: `EM/Group/DepartureGraph.lean` (255 lines). `departureSet`, `visitedSet`, `globalMultiplierSet` defs. 12 abstract theorems: `subgroup_trapping`, `generation_escapes_subgroup`, `coset_trapping_reduces`, `oracle_from_confinement`, `walk_in_coset_closure`, `walk_in_closure_of_start_one`, etc. Plus 5 EM-specific theorems. Key lesson: use `omit [Group G]` for theorems that don't need group structure; `Set.mem_iUnion` for union decomposition proofs.
- **§7.7 DFTParsevalPrime + Lemma715Prime (Session 92)**: `dft_parseval_prime_proved` (42 lines) bridges stdAddChar to eAN via successor decomposition p=p'+1, uses `exp_sum_energy_eq_parseval` + `stdAddChar_mul_intCast_eq_eAN`. Corollary `lemma715Prime_proved` composes with existing reduction. Key lesson: `ZMod.val` needs explicit `show ZMod (p'+1) from r` for Fin→ZMod bridge.
- **§39 Coprimality Refreshing & Death Rate Infrastructure (Session 91)**: 9 theorems/defs in EM/Equidist/SieveTransfer.lean (+138 lines). `coprimality_refreshing_int/ndvd/nat`, `no_safe_cycle`, `neg_inv_involutive`, `neg_inv_bijective`, `negInvEquiv`, `walk_product_telescope`, `char_ratio_of_walk_step`. All zero sorry.
- **§7.7 Lemma715Prime reduction (Session 90)**: `dftParseval_implies_lemma715Prime` PROVED (100 lines). Helpers: `eAN_mod_eq`, `expsum_eq_residueClassSum_expsum`, `residueClassSum_excluded`, `norm_sq_sum_le_card_mul_sum_norm_sq`, `coprime_range_eq_nonzero_fin`. Fixed Lemma715/Lemma715Prime statements with sifted-support condition.
- **§7.6 Large sieve as sieve (Session 89)**: `sieveWeight`, `sieveWeightProd`, `sieveDensity` defs; `sieveWeight_nonneg`, `sieveWeight_pos`, `sieveWeightProd_nonneg` PROVED; `lemma715_farey_implies_largeSieveAsSieve`, `largeSieveAsSieve_implies_card` PROVED. 6 new open Props stated.
- **§7.5b ALS→MLS for prime (Session 88)**: `als_implies_mls_prime` PROVED (256 lines, 8 theorems). Full Gauss+Parseval+spacing reduction.
- **§7.5a MLS Parseval bridge (Session 87)**: `nontrivial_char_parseval_le`, `sum_filter_inv_eq` PROVED.
- **"ALS modulo Hilbert" (Session 86)**: `gram_offdiag_bilinear_implies_als` PROVED. GramOffDiagBilinearBound → AdditiveLargeSieve.
- **Gram matrix framework (Session 85)**: `gramMatrix_offdiag_bound`, `gram_row_sum_weak`, `gram_als_weak` all proved.

## Mixed Variant — ARCHITECTURALLY COMPLETE (Sessions 239-253)

The mixed variant is now complete across 4 files:
- **EM/Advanced/EpsilonRandomMC.lean** (992 lines): MixedMC framework, reachable set analysis, coset impossibility, factor confinement
- **EM/Ensemble/MixedEnsemble.lean** (~1958 lines): Population sieve chain — PEAP→FCD→SPV→PSCD (ALL bridges proved, WeakFMCD unconditional)
- **EM/Advanced/RandomFactorMC.lean** (376 lines): PureRandomMC ↔ MixedMC purification lemma
- **EM/Advanced/InterpolationMC.lean** (1192 lines): Layer 1 (positive-prob capture) + Layer 2 (block coverage, walk concat, iterated hitting) + Layer 3 (TreeSieveDecay → Regeneration bridge) + orbit melting + TSD-Hitting(3) unconditional. Key: `GoodAccumulator`, `TreeSieveDecay` (OPEN, coprimality-conditioned), `TreeSieveDecayHitting` (weaker), `mixedWalkProd_squarefree`, `mixedWalkProd_coprime_of_no_death`, `tsd_implies_neg_one_reachable` (KEY bridge), `tsd_hitting_three_unconditional`, `orbit_melting_landscape`, `full_interpolation_landscape`.

**Open hypotheses**: `PrimesEquidistributedInAP` (standard ANT), `TreeSieveDecay` (∃ P₀, ∀ P ≥ P₀, Squarefree P → Coprime P q → GoodAccumulator q P — sieve-theoretic).
**Session 252**: SieveUpperBound ELIMINATED — replaced by unconditionally proved WeakFMCD.
**Session 253**: InterpolationMC Layer 1 — positive-probability capture from reachability.
**Session 254**: InterpolationMC Layer 2 — block coverage (Finset.sup), walk concatenation, iterated hitting by induction.
**Session 255**: InterpolationMC Layer 3 — TreeSieveDecay defined (ORIGINAL DEF WAS FALSE — see Session 256), `mixedWalkProd_squarefree` proved.
**Session 256**: CRITICAL FIX — TSD requires `Nat.Coprime P q` (absorption: q|P traps walk at 0). Bridge restructured via coprimality dichotomy. `mixedWalkProd_coprime_of_no_death` proved. `tsd_implies_neg_one_reachable` (KEY bridge). Orbit melting (5 theorems). **TSD-Hitting(3) PROVED unconditionally** via mod-3 parity dichotomy.

**TSD ceiling confirmed (Session 258)**: Full TSD(3) is FALSE (P=2 counterexample: reachable set = {0,2}, unit 1 never reached). TSD-Hitting(5) is 1/10. TSD-Hitting(3) is the ceiling of purely algebraic results.

**Probability Infrastructure (Session 258)**:
- **NEW directory**: `EM/Probability/`
- **EM/Probability/TransitionKernel.lean** (267 lines, 0 sorry): `factorPMF` (uniform PMF over primeFactors(P+1) via `PMF.uniformOfFinset`), `epsStepWeight` (exact (1-ε)·minFac + ε·uniform weights), `epsStepWeight_sum_one` (KEY: weights sum to 1), `epsStepWeight_ge_stepWeightLB` (bridge to InterpolationMC's `stepWeightLB`)
- **Key Mathlib APIs**: `PMF.uniformOfFinset`, `PMF.support_uniformOfFinset`, `PMF.bind`, `PMF.bernoulli`
- **Next Phase 2 target**: `EM/Probability/PathMeasure.lean` — N-step path PMF via `PMF.bind`, consistency with `pathWeightLB`

**Session 264 — EM/Probability/GeometricCapture.lean** (378 lines, 0 sorry, NEW):
- **EM/Probability/GeometricCapture.lean**: Block-geometric decay framework — formalizes that non-capture probability decays geometrically under TSD
- Defs: none (all pure theorems)
- 17 theorems: `one_sub_pow_le`, `one_sub_pow_nonneg`, `one_sub_pow_tendsto_zero` (via `tendsto_pow_atTop_nhds_zero_of_lt_one`), `one_sub_pow_lt_eps`, `one_sub_pow_anti`, `block_capture_exists`, `pathWeightLB_pos_of_valid`, `abstract_geometric_decay` (KEY: inductive product bound), `product_failure_tendsto_zero` (squeeze_zero), `product_failure_lt_eps`, `capture_weight_pos`, `regeneration_geometric_capture`, `tsd_positive_capture`, `capture_fraction_ge_inv_pow`, `counting_failure_bound`, `counting_failure_tendsto_zero`, `geometric_capture_landscape` (6-clause)
- Import: `EM.Probability.PathMeasure`, `Mathlib.Analysis.SpecificLimits.Basic`
- **Probability infrastructure now 3 files / 979 lines**: TransitionKernel (267) + PathMeasure (334) + GeometricCapture (378)

**Next targets**: (1) Phase 2: N-step path PMF via `PMF.bind`, consistency with `pathWeightLB`. (2) Track A: Mixing time bounds. (3) Code-stylist passes on large files.

**Session 260 — EM/Probability/PathMeasure.lean** (333 lines, 0 sorry, NEW):
- **EM/Probability/PathMeasure.lean**: Bridges set-theoretic reachable sets to computable Finset world
- Defs: `reachableAtFinset`, `reachableEverFinset`, `factorResidueFinset`
- 24 theorems: `mem_reachableAtFinset_iff`, `mem_reachableEverFinset_iff`, `reachableAtFinset_card_le`, `reachableEverFinset_card_le`, `reachableAtFinset_nonempty`, `reachableEverFinset_nonempty`, `reachableEver_card_lt_of_proper`, `reachableEver_compl_nonempty`, `branching_distinct_of_unit` (KEY: unit position + distinct factor residues → distinct next positions), `factorResidueFinset_nonempty`, `minFac_in_factorResidueFinset`, `path_measure_landscape` (7-clause)
- Import: `EM.Probability.TransitionKernel`
- **MixedDiversity → MixedHitting assessment**: CONFIRMED IRREDUCIBLE (98%+ confidence). Gap is FactorEscapeHypothesis, purely arithmetic. Coset impossibility is necessary but insufficient. Z/10Z counterexample: S={0,1,3,7,9} escapes all cosets but misses 5 elements. Do NOT attempt this bridge.

## Session 224 — EM/Ensemble/TwoPointEnsemble.lean (population-level reduction)

**EM/Ensemble/TwoPointEnsemble.lean** (566 lines, 0 sorry, NEW FILE): Ensemble two-point MC chain — reduces StochasticTwoPointMC to population-level hypotheses.

**New definitions**:
- `genRawTwoPointUnitSet q n k` — {liftToUnit(genSeq), liftToUnit(secondMinFac)} in (ZMod q)ˣ
- `genPaddedUnitSet q n k` — padded variant (adds 1 for nonemptiness)
- `genFactorRatio q n k` — liftToUnit(genSeq)·liftToUnit(secondMinFac)⁻¹ in (ZMod q)ˣ
- `ratioEscapeCount/Density` — counting/density of escapes from ker(chi)
- `cumulRatioEscapeCount` — cumulative escape over K steps
- `ensembleAvgEscapeCount` — ensemble average of cumulative escape

**New theorems**:
- `genPaddedUnitSet_card_ge_two` — card ≥ 2 for q ≥ 3 PROVED
- `ensembleAvgEscapeCount_eq_sum_densities` — **Fubini for finite sums** via `Finset.sum_comm` PROVED
- `escape_first_moment_linear` — E[cumul escape] ≥ δ·(K-1) from PRED PROVED
- `positive_density_high_escape` — partition argument PROVED
- `pred_implies_almost_all_infinite` — PRED ⇒ AlmostAllInfiniteRatioEscapes PROVED
- `ensemble_two_point_landscape` — 6-clause landscape PROVED

**Open Props**: `PopulationRatioEscapeDensity q chi`, `MFREImpliesPopulationRatioEscape`

**Key Lean technique**: Cast arithmetic `↑K - 1` with different types of `1` (ℕ vs ℝ) — fix via `push_cast; norm_cast`. Partition argument uses `div_le_div_of_nonneg_right` + `linarith` rather than `nlinarith` for nonlinear density bounds.

## Session 208 — Stochastic MC Tier 1 Framework (EM/Advanced/VanishingNoise.lean)

**EM/Advanced/VanishingNoise.lean** (956 lines, 0 sorry): Extended with Parts 9-15 (+302 lines). Stochastic MC framework — if infinitely many factor sets have ≥2 elements, there EXISTS a selection path hitting -1 for every prime q.

**New definitions (Session 208)**:
- `meanCharValue chi S` — (∑ s ∈ S, χ(s)) / |S|, per-step averaged character value
- `avgCharProduct chi S N` — ∏_{k<N} meanCharValue chi (S k), telescoped product
- `InfinitelyManyLargeFactorSets' q` — ∀ N, ∃ n ≥ N, |factorSetResidues(n)| ≥ 2 (replaces True placeholder)
- `productMultiset S N` — all achievable products from S(0) × ... × S(N-1), defined via `Multiset.bind`
- `PathExistenceFromVanishing G` — open Prop: vanishing char product averages ⇒ ∀ a ∈ G, a ∈ productMultiset.toFinset
- `CharacterOrthogonality G` — open Prop: ∑_{χ} χ(a) = 0 for a ≠ 1

**New theorems (Session 208)**:
- `avgCharProduct_norm_le_one` — ‖avgCharProduct χ S N‖ ≤ 1 PROVED (norm_prod, spectral_contraction_lt_one)
- `avgCharProduct_contraction` — spectral gap + product contraction compose PROVED
- `productMultiset_card` — |productMultiset S N| = ∏_{k<N} |S k| PROVED (Multiset.card_bind)
- `char_sum_productMultiset` — **KEY IDENTITY**: ∑_{paths} χ(∏σ_k) = ∏_k (∑_{s∈S_k} χ(s)) PROVED by induction using Multiset.map_bind + sum_bind + sum_map_mul_left
- `stochastic_mc_landscape` — 4-clause conjunction PROVED

**Key Lean APIs discovered (Session 208)**:
- `Multiset.bind`: `Multiset α → (α → Multiset β) → Multiset β` — flat map for multisets
- `Multiset.card_bind`: card of bind = sum of cards
- `Multiset.map_bind`: `(A.bind f).map g = A.bind (fun a => (f a).map g)`
- `Multiset.sum_bind`: `(A.bind f).sum = A.sum.bind f` — NO, actually `∑ x in A.bind f = ∑ a in A, ∑ x in f a`
- `Multiset.sum_map_mul_left`: `∑ (c * ·) = c * ∑`
- `omit [DecidableEq G] in` — suppress unused section variable warnings

**Gap**: `PathExistenceFromVanishing` — standard representation theory (character orthogonality for `G →* ℂˣ`). The Mathlib interface gap: `Fintype (G →* ℂˣ)` doesn't synthesize directly; need `MulChar` bridge. Estimated ~100-150 lines via `MulChar.equivToUnitHom` (used successfully in Session 163 for AdelicEquidist).

**Do NOT attempt**: proving PathExistenceFromVanishing by synthesizing `Fintype (G →* ℂˣ)` directly. Use `MulChar (ZMod q) ℂ` via `MulChar.equivToUnitHom` if closing this Prop.

## Session 210-211 — Two-Point Spectral Gap + Sparse Contraction (EM/Advanced/VanishingNoise.lean)

**EM/Advanced/VanishingNoise.lean** (1814 lines, 0 sorry): Extended with Parts 16-19 (+858 lines from Session 208 baseline).

**Session 210** added:
- `twoPointCharValue chi a b ε` — (1-ε)·χ(a) + ε·χ(b), weighted coin flip character value
- `twoPointCharProduct chi a b ε N` — product over N steps
- `twoPointCharValue_norm_lt_one` — **KEY**: strict < 1 when χ(a) ≠ χ(b), 0 < ε < 1 (SameRay technique)
- `twoPointCharProduct_tendsto_zero` — product → 0 when ALL steps contract (strong version)
- `InfinitelyManyDistinctFactorSteps q` — properly defined open Prop

**Session 211** added:
- `sparse_product_contraction` — **KEY GENERALIZATION**: ∏ a_k → 0 when a_k ∈ [0,1] and ∑(1-a_k) = ∞. Does NOT require each a_k < 1. Uses same 1-x ≤ exp(-x) bound as product_contraction_tendsto.
- `sparse_avgCharProduct_tendsto_zero` — generalizes avgCharProduct_tendsto_zero (Part 11)
- `sparse_twoPointCharProduct_tendsto_zero` — generalizes twoPointCharProduct_tendsto_zero (Part 17)
- `sparse_contraction_landscape` — 4-clause landscape

**Stochastic MC chain now COMPOSABLE**: IMDFS → sparse spectral gaps → sparse_avgCharProduct_tendsto_zero → pathExistenceFromVanishing → every element reachable.

## Session 212 — Self-Consistent ε-Walk Framework (EM/Advanced/VanishingNoise.lean Part 20)

**EM/Advanced/VanishingNoise.lean** (2158 lines, 0 sorry): Extended with Part 20 (+344 lines from Session 211 baseline).

**New definitions**:
- `secondMinFac n` — second-smallest prime factor (n / minFac then minFac of quotient)
- `epsWalkProd σ n` — ε-walk accumulator with decision sequence σ : ℕ → Bool
- `epsWalkFactor σ n` — factor chosen at step n (minFac if σ=true, secondMinFac if false)
- `emDecision` — all-true decisions (= standard EM walk)
- `chiAt q chi p` — character value at ℕ mod q, returns 1 for non-units
- `treeCharSum q chi N acc ε` — weighted character sum over depth-N branching tree
- `TreeContractionHypothesis` — tree char sum → 0 for nontrivial χ (OPEN)
- `UniformFactorDiversity` — minFac ≠ secondMinFac mod q at i.o. steps (OPEN)

**Key theorems**:
- `secondMinFac_dvd`, `secondMinFac_prime`, `minFac_le_secondMinFac` — secondMinFac API
- `epsWalkProd_emDecision` — **bridge**: all-true decisions = Mullin.prod (via euclid_minFac_eq_nat_minFac)
- `treeCharSum_norm_le_one` — **KEY**: ‖treeCharSum‖ ≤ 1 (induction + triangle inequality + chiAt norm)
- `eps_walk_landscape` — 7-part conjunction

**Self-consistent tree ≠ product multiset**: the treeCharSum involves path-dependent branching (each subtree has different accumulator), so it does NOT factorize as ∏_k (weighted per-step average). TreeContractionHypothesis is genuinely between IMDFS and DSL.

## Codebase stats (current)

- **125 files**, **~68,079 lines**, **~2200+ theorems**, **~750+ definitions**, **~470+ open Props (stated as `def`)**, **0 sorry**
- IKCh7 split: `EM/IK/Ch7Foundations.lean` (§7.1-7.3), `EM/IK/Ch7AdditiveLS.lean` (§7.4), `EM/IK/Ch7MultiplicativeLS.lean` (§7.5), `EM/IK/Ch7SieveApplications.lean` (§7.6), `EM/IK/Ch7Hilbert.lean` (§7.4f/7.9-7.10)
- `NoLongRunsQuadratic` already exists in `EM/Equidist/SelfCorrecting.lean` (line ~720)
- `noLongRuns_implies_noLongRunsQuadratic` already proved (line ~731)
- `vcb_ped_implies_mc` chain verified (EM/LargeSieve/Spectral.lean:2343-2346)
- §7.4d Gram matrix framework complete: `gramMatrix_offdiag_bound`, `gram_row_sum_weak`, `gram_als_weak` (EM/IK/Ch7AdditiveLS.lean)
- §7.4d' Packing bound + improved ALS (Session 113): `gramMatrix_offdiag_bound_dist`, `round_sep_card_le`, `gram_row_sum_improved`, `gram_als_improved` (EM/IK/Ch7AdditiveLS.lean). Three ALS constants: weak N+(R-1)/(2δ), improved N+1/(2δ²), optimal 1/δ+N-1 (needs Hilbert)
- §7.4e Off-diagonal bilinear → ALS: `gram_quadratic_split`, `gram_diag_re`, `gram_offdiag_bilinear_implies_als` (EM/IK/Ch7AdditiveLS.lean)
- `GramOffDiagBilinearBound` open Prop in EM/IK/Ch7AdditiveLS.lean — the ONLY remaining gap for optimal ALS
- `weakAdditiveLargeSieve` wraps `weak_als_from_card_bound` (EM/IK/Ch7AdditiveLS.lean)
- Round-based separation used in §7.4d; `IsSpaced` (fract-based) used in §7.4e
- §7.5a Parseval bridge: `nontrivial_char_parseval_le`, `sum_filter_inv_eq` — both PROVED (EM/IK/Ch7MultiplicativeLS.lean)
- §7.5b: `als_implies_mls_prime` PROVED (EM/IK/Ch7MultiplicativeLS.lean) — ALS → MLS for prime p (Session 88)
- Key helpers: `mulchar_sum_eq_units_sum`, `char_sum_norm_sq_eq_parseval_form`, `parseval_chain`, `unit_points_spaced`, `als_reindex`
- `MultiplicativeLargeSieve` proper statement in EM/IK/Ch7MultiplicativeLS.lean (replaces True stub)
- `MultiplicativeLargeSievePrime` in EM/IK/Ch7MultiplicativeLS.lean — single-prime MLS with p/(p-1) weight
- `stdAddChar_mul_intCast_eq_eAN` and `char_sum_gauss_expansion` now public in EM/LargeSieve/Analytic.lean
- §7.6: `sieveWeight`, `sieveWeightProd`, `sieveDensity` definitions (EM/IK/Ch7SieveApplications.lean)
- §7.6: `sieveWeight_nonneg`, `sieveWeight_pos`, `sieveWeightProd_nonneg` PROVED
- §7.6: `lemma715_farey_implies_largeSieveAsSieve` PROVED — Lemma715+FareyLS → LargeSieveAsSieve
- §7.6: `largeSieveAsSieve_implies_card` PROVED — weighted → cardinality form
- §7.6: `als_implies_farey_large_sieve_proper` PROVED (Session 106) — ALS → FareyLargeSieveProper via Farey spacing + Cauchy-Schwarz Q=1 case. Chain: ALS → FareyLS → (+Lemma715) → LargeSieveAsSieve complete.
- §7.6 open Props: `LargeSieveAsSieve`, `LargeSieveAsSieve_card`, `LinnikSmallQNR`, `LargeSieveAsSieveImpliesLinnik`
- **SDDS open hypotheses status** (Session 104): `NoAlgebraicObstruction` **CLOSED** (Session 100 via `se_implies_nao`). `CoprimeCascade` **CLOSED** (Session 104 via `SDDS.coprimeCascade` — proved for ALL SDDS, not just emSDDS). Remaining: `SuperExponentialGrowth` (provable from `prod_ge_two` + multiplicative recurrence), `SieveRegularity` (placeholder True), `SieveMapEquidistribution` (master conjecture ≈ MC)
- **SDDS Divisibility Chain** (Session 104): `SDDS.orbit_dvd_orbit_succ` (orbit(k) | orbit(k+1)), `SDDS.orbit_dvd_orbit` (k ≤ n → orbit(k) | orbit(n)), `SDDS.mult_dvd_orbit_succ` (Φ(orbit(m)+1) | orbit(m+1)), `SDDS.coprimeCascade` (CoprimeCascade S for ALL SDDS)
- **EM/Reduction/DSLInfra.lean** (683 lines): Energy evolution, cross terms, char norm = 1. Session 115 added ShiftedWalkIdentity section (lines 479-683): `euclidCofactor`, `cofZ` defs; `shifted_walk_eq_mult_mul_cof` (w+1=m·c), `walkZ_eq_neg_one_iff_cofZ_zero` (hit↔cofZ=0), `char_shifted_walk_eq_char_mult_mul_char_cof` (character decomposition through cofactor), plus 10 supporting lemmas.
- **EM/Reduction/DSLVariance.lean** (407 lines, Session 137): Population second moment infrastructure. `populationCharEnergy`, `crossTermPair`, `populationCrossTermSum`, `SecondMomentBound`, `PairwiseCrossTermVanishing`. 12 proved theorems including `charSumVarianceBound_implies_secondMomentBound`, `stepDecorrelation_implies_pairwiseVanishing`, `variance_chain_from_bridges`. 3 open Props: `PairwiseVanishingImpliesSMB`, `SMBImpliesDSL`, `VarianceChainImpliesDSL`.
- **Ensemble PT files** (Sessions 117-125, ~2000 lines total): `EM/Ensemble/EM.lean` (114 lines, genWalkZ/genMultZ/bridge), `EM/Ensemble/Decorrelation.lean` (412 lines, EnsembleCharSumConcentration reformulated to pointwise, CharSumVarianceBound with ∀K∃X₀, **char_variance_implies_concentration_proved PROVED Session 119**), `EM/Ensemble/CRT.lean` (~470 lines, sqfreeAccumCount/sqfreeSeqCount/ensembleCharMean, SRE+CRT induction chain, **ensemble_mult_equidist_implies_char_mean_zero PROVED Session 118**), `EM/Ensemble/PT.lean` (1751 lines, GenMullinConjecture, 4-layer decorrelation chain, ensemble_pt_master, gen_mc_two_implies_mc, dsl_closes_all, **gen_hitting_implies_gen_mc_proved PROVED Session 118**, **decorrelation_implies_variance_proved PROVED Session 119**, **per_chi_cancellation_bridge_proved PROVED Session 125**). JSE→MC chain: WeylHittingBridge PROVED (Session 127). Remaining open Props: SquarefreeResidueEquidist (~800-1500 lines needed, long-term), CRTPropagationStep (hardest), AccumEquidistImpliesMultEquidist (= PopulationTransfer), StepDecorrelation (sole gap in concentration chain), FirstMomentStep, VarianceBound, MultCancelToWalkCancel (HARD, Dead End #117 ≡ CCSB/CME). **DO NOT attempt EnsembleEquidistImpliesDecorrelation** — maps to Dead End #98. **DO NOT attempt SquarefreeResidueEquidist** — requires ζ(2)=π²/6 (unprecedented in any prover). **DO NOT attempt MultCancelToWalkCancel** — equivalent to CCSB/CME (Dead End #117).
- **EM/Reduction/SelfCorrecting.lean** (Sessions 141-142, 652 lines): Lyapunov route to MC. `visitDeviation` (V_N(a)-N/(q-1)), `lyapunov` (L(N)=∑d²), `cumulativeDrift` (R(N)=∑d_{w(n)}), `SelfCorrectingDrift` (open Prop: R=o(N²), **= SVE by Dead End #120**). Key theorems: `emVisitCount_sum` (∑V=N), `visitDeviation_sum_zero` (∑d=0), `emVisitCount_succ_at/other` (visit count updates), `visitDeviation_succ_at/other` (deviation updates), `lyapunov_one_step` (L(N+1)=L(N)+2d+const PROVED), `lyapunov_telescope` (L=2R+linear PROVED), `scd_implies_ve` (SCD→VE PROVED), `scd_implies_sve` (SCD→SVE PROVED via walkVisitCount↔emVisitCount bijection), `sve_implies_scd_above_threshold` (SVE→SCD for q≥Q₀ PROVED Session 142), `scd_implies_mc` (SCD→MC PROVED via SVE chain), `group_walk_doubly_stochastic` (PROVED), `uniform_multiplier_zero_drift` (PROVED). Imports: EM.Reduction.VisitEquidist, EM.Reduction.Master.
- **EM/Transfer/Substitution.lean** (Session 140, 301 lines): SP=CME (by `simp`), fiber return visits (injective, coprime), `all_routes_to_mc_with_sp`. SP PROVED IMPOSSIBLE for general sequences (Dead End #119).
- **EM/CME/Decomposition.lean** (199 lines): `EMDirichlet` (= DecorrelationHypothesis alias), `EMDImpliesCME` (open hypothesis), `cme_implies_emd`, `emd_cme_implies_mc`, `emd_cme_implies_ccsb`, `deathSet`, `surjective_subgroup_coset_meets_target`, `surjective_subgroup_coset_meets_death`, `walk_reachable_meets_death_algebraic`. Key: surjection lemma shows every coset of a surjecting subgroup meets the death set in a product group.
- **EM/Population/WeakMullin.lean** (363 lines): `MissingPrime`, `WeakMullinConjecture`, `ReciprocalDivergence`, `mc_implies_wm`, `wm_implies_rd`, `mc_implies_rd`, product divergence bounds, `EMBV` (Euler-Mullin Bombieri-Vinogradov), `JointSVE`, `embv_implies_mc`, `joint_sve_implies_mmcsb`.
- **EM/Population/WeakErgodicity.lean** (154 lines): `prod_squarefree` (PROVED — EM accumulator is squarefree), `ShiftedSquarefree` def, `euclid_in_shifted_squarefree` (PROVED), `EM/FunctionField/PopulationEquidist.lean` (open — minFac equidist mod q in shifted squarefree pop), `PopulationTransfer` (open — PE → EMDirichlet), `pe_transfer_cme_implies_mc` (PROVED — PE + PT + EMDImpliesCME → MC)
- §7.7 (Session 90): `DFTParsevalPrime` (open Prop), `Lemma715Prime` (open Prop), `residueClassSum` (def) — all in EM/IK/Ch7SieveApplications.lean
- §7.7: `eAN_mod_eq`, `expsum_eq_residueClassSum_expsum`, `residueClassSum_excluded`, `coprime_range_eq_nonzero_fin`, `norm_sq_sum_le_card_mul_sum_norm_sq` — all PROVED
- §7.7: `dftParseval_implies_lemma715Prime` PROVED — DFTParsevalPrime → Lemma715Prime
- §7.7: `dft_parseval_prime_proved` PROVED (Session 92) — DFTParsevalPrime via stdAddChar→eAN bridge
- §7.7: `lemma715Prime_proved` PROVED (Session 92) — Lemma715Prime, corollary of above
- §7.7: Lemma715 and LargeSieveAsSieve_card now have sifted-support condition (Ω parameter)
- §7.7: Import added: `Mathlib.Algebra.Order.Chebyshev` (for `sq_sum_le_card_mul_sum_sq`)
- §39 (Session 91): `coprimality_refreshing_int/ndvd/nat`, `no_safe_cycle`, `neg_inv_involutive`, `neg_inv_bijective`, `negInvEquiv`, `walk_product_telescope`, `char_ratio_of_walk_step` (EM/Equidist/SieveTransfer.lean:1319-1457)
- **SDDS files** (Session 97, 447 lines): `EM/SDDS/Dynamics.lean` (168), `EM/SDDS/Bridge.lean` (153), `EM/SDDS/Reduction.lean` (126). Abstract SDDS framework with `FactoringRule`/`SDDS` structures, full bridge to EM code via `euclid_minFac_eq_nat_minFac`, and `StrongSME → MC` reduction.
- **EM/Transfer/CRTFiber.lean** (Session 100, 297 lines): `nao_set_eq_range`, `se_implies_nao` (closes NoAlgebraicObstruction), `mc_below_pre_implies_nao`, `crt_pair_surjective` (Bezout-based CRT), `dvd_independent_of_residue`, `crt_unit_pair_surjective`, `death_channel_disjoint`/`disjoint'`, `death_value_mechanism`, `residue_class_dichotomy`, `death_channel_nonempty`. Key APIs: `IsCoprime`, `Int.isCoprime_iff_gcd_eq_one`, `ZMod.intCast_surjective`, `ZMod.natCast_self`, `ZMod.intCast_zmod_eq_zero_iff_dvd`, `Nat.coprime_primes`.
- **EM/Group/DepartureGraph.lean** (Sessions 93-94, 98; 641 lines): Departure graph framework + safe prime lattice + complement generation + target avoidance + safe prime DH dichotomy.
  - Defs: `departureSet`, `visitedSet`, `globalMultiplierSet` (abstract); `emVisitedSet`, `emMultiplierSet`, `emDepartureSet` (EM-specific); `IsSafePrime`
  - Session 93 theorems: `subgroup_trapping`, `generation_escapes_subgroup`, `coset_trapping_reduces`, `oracle_from_confinement`, `departureSet_subset_left_translate`, `walk_in_coset_closure`, `walk_in_closure_of_start_one` + 10 more
  - Session 94 theorems: `exists_infinite_fiber_of_finite`, `infinite_fiber_mem_visitedSet`, `infinite_departures_at_recurrent`, `dvd_two_mul_prime_iff`, `card_subgroup_of_order_two_mul_prime`, `card_proper_subgroup_le`, `multiplier_closure_ne_top_of_confined`, `generating_escapes_proper`
  - EM connection: `em_walk_recurrence` wraps `walkZ_succ`
  - Pattern: `omit [Group G] in` before theorems not needing group structure
- **Lesson from Session 93**: Use `omit [Group G] in` to suppress linter warnings for theorems that only need type-level structure (no group operations). For `Set.mem_iUnion` proofs, `simp only` with explicit lemma names works cleanly.
- **Lesson from Session 94**: `Finite.exists_infinite_fiber` returns `Infinite (f ⁻¹' {y})` (subtype infinite), not `Set.Infinite`. Use `Set.infinite_coe_iff` + `convert` to bridge. For divisibility cleanup, `mul_dvd_mul_iff_left` handles cancellation cleanly. `Nat.prime_two.coprime_iff_not_dvd` gives coprimality from non-divisibility. `Subgroup.eq_top_of_card_eq` needs `Finite H` — get it from `Nat.finite_of_card_ne_zero`.
- **Lesson from Session 88**: When dealing with `let`-bindings in theorem types (e.g. `char_sum_norm_sq_eq_parseval_form`), decompose large theorems into small helpers that `subst` the parameter. Avoid large `set_option maxHeartbeats` — split instead.
- **Lesson from Session 89**: For `Nat.cast_nonneg` with specific arguments, use `Nat.cast_nonneg' x` not bare `Nat.cast_nonneg`. For CharZero issues, add explicit intermediate `have` with type annotations. For `DecidablePred` filter issues, use `push_cast; rfl` approach.
- **Lesson from Session 90**: For `Nat.cast_div` issues with `push_cast`, avoid letting Lean unfold nat division as real division. Instead `set q := n / p` to make the quotient opaque, then use `field_simp` for algebra and `exact_mod_cast` for ℕ→ℝ lifts. For `eAN` periodicity, decompose `n = (n/p)*p + n%p` via `Nat.div_add_mod`, then use `eAN_add` + `eAN_intCast` to factor out integer parts.

## Project Context

This project reduces Mullin's Conjecture to a single open hypothesis (`DynamicalHitting`). Your job is to write correct, compiling Lean code that advances the abstract proof — new lemmas, stronger reductions, or structural results.

## Conventions (MUST follow)

- **Namespaces**: Mullin files use `namespace Mullin`; MullinGroup files use `namespace MullinGroup`; Equidist files use `open Mullin Euclid MullinGroup RotorRouter` (no namespace)
- **Tactic style**: `omega`, `simp`, `ring`, `norm_num`; term-mode for short proofs
- **Open hypotheses**: stated as `def ... : Prop` (not sorry'd theorems)
- **Doc comments**: `/-- ... -/` must be followed by a declaration; `open Classical in` goes BEFORE docstring
- **Imports**: each file imports its direct predecessors; `EM.lean` root file lists all imports
- **Gotchas**: `simp [neg_inv]` loops — use `simp only [neg_inv, inv_inv, neg_neg]`; `orderOf` is noncomputable; `Subgroup.closure_le` via `rw` not `.mpr`
- **`div_le_one_of_le₀`**: For proving `a / b ≤ 1` when `a ≤ b` and `0 ≤ b`, use `div_le_one_of_le₀` (one-liner) instead of case-splitting on `b = 0` vs `b ≠ 0`. Applicable to all density-bounded-by-one proofs.
- **`open Classical`**: Prefer section-level `open Classical` over per-theorem `open Classical in`. Only use `open Classical in` when a section has very few Classical-dependent theorems (1-2).
- **`theorem` vs `lemma`**: Use `theorem` for all public declarations. Only `private lemma` is acceptable for internal helpers. No public `lemma` declarations.
- **No duplicate `open`**: Each section should open a namespace only once. Don't write `open Mullin` then later `open Mullin Euclid` — write `open Mullin Euclid` once.
- **QR boilerplate**: When writing multiple similar QR/Legendre symbol theorems, factor common logic into private helpers and make the public theorems one-liner applications. See `EM/Group/QR.lean` for the p=7 pattern.
- **Naming**: `_of_` means reverse implication (X_of_Y means Y → X), `_implies_` means forward (X_implies_Y means X → Y). These are CORRECT and consistent across the codebase.

## Session 213-214 — Non-Self-Consistent Variant MC (EM/Advanced/VanishingNoiseVariant.lean)

**FILE SPLIT (Session 214):** EM/Advanced/VanishingNoise.lean was split into two files:
- **EM/Advanced/VanishingNoise.lean** (1814 lines): Parts 1-19 (spectral gap, product contraction, sparse contraction)
- **EM/Advanced/VanishingNoiseVariant.lean** (742 lines): Parts 20-21 (ε-walk, non-self-consistent variant MC)
- VanishingNoiseVariant imports VanishingNoise. Key bridge helpers (`mulCharToHom`, `homToMulChar`, etc.) are now PUBLIC (were private).

**EM/Advanced/VanishingNoiseVariant.lean** (742 lines, 0 sorry):
- **Part 20** (ε-walk): `secondMinFac`, `epsWalkProd`, `treeCharSum`, `TreeContractionHypothesis`
- **Part 21** (variant MC): `paddedUnitSet`, `UFDStrong`, `VariantHitting`, `VariantMCFromUFDStrong`
- **`prime_ne_isUnit_zmod`** — p prime, q prime, p ≠ q ⇒ IsUnit (p : ZMod q). Uses `ZMod.isUnit_prime_iff_not_dvd`.
- **`paddedUnitSet`** — `rawTwoPointUnitSet` if card ≥ 2, else `Finset.univ` (fallback)
- **`meanCharValue_univ_eq_zero`** — character orthogonality via `homToMulChar`/`mulCharToHom` bridge + `MulChar.sum_eq_zero_of_ne_one`
- **UFDStrong → vanishing → path existence → VariantHitting** chain PROVED
- **`ufd_fallback_not_summable`** — fallback case of UFD → UFDStrong PROVED
- **`UFDImpliesUFDStrong`** — OPEN (maps to Dead End #90, genuine gap, 1/10 provable)

**Key Lean APIs (Sessions 213-214)**:
- `ZMod.isUnit_prime_iff_not_dvd` — p prime ⇒ (IsUnit (p : ZMod q) ↔ ¬(p ∣ q) [or similar])
- `ZMod.card_units_eq_totient` — |(ZMod q)ˣ| = φ(q)
- `Nat.totient_prime` — φ(p) = p-1 for prime p
- `MulChar.sum_eq_zero_of_ne_one` — character orthogonality for MulChar
- `homToMulChar`/`mulCharToHom` — bijection between G →* ℂˣ and MulChar G ℂ (now PUBLIC in EM/Advanced/VanishingNoise.lean)

**Novel technique: padded fallback to Finset.univ.** When a Finset has card < 2 (violating PathExistenceFromVanishing requirements), fall back to Finset.univ. Character orthogonality gives meanCharValue = 0 (perfect contraction, gap = 1), which is BETTER than the card ≥ 2 case.

## Session 215 — Routes to UFDStrong (EM/Advanced/VanishingNoiseVariant.lean Part 22)

**EM/Advanced/VanishingNoiseVariant.lean** (1060 lines, 0 sorry): Extended with Part 22 (+318 lines).

**New definitions**:
- `MinFacRatioEscape q` — quantitative: ∀ nontrivial chi, ∃ δ > 0, i.o. gap ≥ δ
- `MinFacRatioEscapeQual q` — qualitative: i.o. card ≥ 2 + chi-values differ
- `OrbitMFRE q` — orbit-level minFac equidist: density → 1/(q-1)
- `OrbitMFREImpliesEscapeQual q` — OPEN Prop: OrbitMFRE → MinFacRatioEscapeQual

**Key proved reductions**:
- `ratio_escape_implies_ufdStrong` — MinFacRatioEscape → UFDStrong (trivial via `not_summable_of_frequently_ge`)
- `qual_implies_quant` — **KEY**: MinFacRatioEscapeQual → MinFacRatioEscape via finite-range argument
- `qual_escape_implies_ufdStrong` — composition
- `route1/2/3_to_variant_mc` — all 3 routes compose to VariantMC

**Novel technique: finite-range argument for spectral gap uniformity.** When proving non-summability of spectral gaps, the function `n ↦ 1 - ‖meanCharValue chi (paddedUnitSet n)‖` has FINITE range because `Finset (ZMod q)ˣ` is Fintype. So positive gaps are bounded below by `Finset.min'` over the positive range values. This avoids pigeonhole on pairs and explicit computation of `1 - cos(π/(q-1))`.

**Key Lean APIs (Session 215)**:
- `Set.toFinite (Set.univ : Set (Finset (ZMod q)ˣ))` — Finset over Fintype is finite
- `Finset.min'` + `Finset.min'_mem` + `Finset.min'_le` — minimum of nonempty Finset
- `Set.Finite.toFinset` + `Set.Finite.mem_toFinset` — convert Set.Finite to Finset
- `Summable.tendsto_atTop_zero` + `Metric.tendsto_atTop` — summable ⇒ terms → 0

## Session 217 — Stochastic Two-Point MC (EM/Advanced/VanishingNoiseVariant.lean Part 23)

**EM/Advanced/VanishingNoiseVariant.lean** (1338 lines, 0 sorry): Extended with Part 23 (+277 lines).

**New definitions**:
- `fairCoin : ℕ → ℝ` — constant 1/2 (ε-coin for tree char sum)
- `fairTreeCharSum q chi N` — `treeCharSum q chi N 2 fairCoin` (fair-coin tree)
- `TreeContractionAtHalf q` — fair-coin tree char sum → 0 for nontrivial χ (OPEN, weaker than DSL)
- `StochasticTwoPointMC q` — 2 < q → UFDStrong → ∀ a ∈ (ZMod q)ˣ, ∃ path hitting a

**Key proved theorems**:
- `productMultiset_card_ge_two_pow` — 2^N ≤ |productMultiset paddedUnitSet N| PROVED (via `Finset.prod_le_prod'` + `paddedUnitSet_card_ge_two`)
- `stochastic_two_point_mc_proved` — StochasticTwoPointMC PROVED (via `ufdStrong_implies_path_existence`)
- `tch_implies_stochastic_two_point_mc` — TreeContractionHypothesis ⇒ StochasticTwoPointMC PROVED (via UFDStrong chain)
- `treeCharSum_at_zero_step` — tree char sum unrolls at zero ε (reduces to deterministic step)
- `tree_contraction_at_half_weaker_than_dsl` — TreeContractionAtHalf → StochasticTwoPointMC (self-consistent ⇒ non-self-consistent)
- `self_consistent_vs_non_self_consistent` — key gap: tree (path-dependent branching) ≠ product multiset (fixed factor sets)
- `stochastic_two_point_mc_landscape` — 6-clause summary PROVED

**Key gap documented**: Self-consistent tree char sum (treeCharSum) involves path-dependent branching — each subtree has a different accumulator determined by the selection at the parent step. Product multiset (productMultiset) uses FIXED factor sets independent of path. The two are NOT equal, and tree contraction does NOT imply product contraction. Tree char sum → 0 is genuinely BETWEEN InfinitelyManyDistinctFactorSteps and DSL in strength.

**Key Lean APIs (Session 217)**:
- `Finset.prod_le_prod'` — ∀ i ∈ s, f i ≤ g i ⇒ ∏ f ≤ ∏ g (needs `MulLeftMono ℕ`, which is available)
- `Multiset.count_pos` — 0 < count a m ↔ a ∈ m
- `Multiset.mem_toFinset` — a ∈ m.toFinset ↔ a ∈ m
- When composing `(fun _ : ℕ => (0 : ℝ)) ∘ Nat.succ`, Lean does NOT auto-simplify to `fun _ => 0`. Use explicit `have h0 : ... := by ext; simp` then `rw [h0]`.

## Session 218 — Phase Transition Characterization (EM/Advanced/VanishingNoise.lean Part 24)

**EM/Advanced/VanishingNoise.lean** (2089 lines, 0 sorry): Extended with Part 24 (+271 lines).

**New definitions**:
- `constEpsCharProduct chi p₁ p₂ ε N` — two-point char product with constant ε across all steps
- `cesaroCharAvg chi p N` — (1/N) · ∑_{n<N} ∏_{k<n} χ(p k), Cesàro average of unit-modulus char products

**Key proved theorems**:
- `twoPointCharValue_zero` — at ε=0, twoPointCharValue reduces to χ(a)
- `twoPointCharValue_norm_one_at_zero` — ‖twoPointCharValue χ a b 0‖ = 1 (critical point)
- `constEpsCharProduct_norm_one_at_zero` — ‖constEpsCharProduct χ p₁ p₂ 0 N‖ = 1 (product of unit norms)
- `constEpsCharProduct_tendsto_zero` — for ε > 0, product norm → 0 (mixing phase, uses uniform gap + sparse contraction)
- `cesaroCharAvg_norm_le_one` — ‖cesaroCharAvg χ p N‖ ≤ 1 (triangle inequality)
- `charProduct_norm_one` — ‖∏_{k<N} χ(p k)‖ = 1 (unit-modulus product, via char_norm_one_of_hom)
- `phase_transition_landscape` — 4-clause conjunction (mixing, critical, Cesàro, unit-modulus) PROVED

**Key technique: finite-range trick for uniform spectral gap**:
The gap function `n ↦ 1 - ‖twoPointCharValue χ (p₁ n) (p₂ n) ε‖` has finite range (since G is `Fintype`, values factor through `G × G`). Taking the minimum positive value from this finite range gives a uniform `δ > 0` bound. Combined with `not_summable_of_io_ge_delta` and `sparse_product_contraction`, this proves the mixing phase. This extends the technique first used in Session 215 (Routes to UFDStrong, finite-range argument for spectral gap).

**Key Lean APIs (Session 218)**:
- `not_summable_of_io_ge_delta` (private helper) — ∑ f diverges when f(n) ≥ δ infinitely often
- `uniform_gap_at_contracting_steps` (private helper) — finite-range trick gives uniform δ > 0
- `set_option linter.unusedSectionVars false in` — suppress unused section variable linter when `omit` syntax fails for `private` theorems

**Mathematical significance**: This part captures the "phase transition" nature of MC — the EM walk operates at the critical point ε=0 where character products maintain unit modulus, while any ε>0 perturbation causes exponential decay to zero. MC is equivalent to Cesàro cancellation of these unit-modulus phases.

## Session 219 — Faithful Character Escape (EM/Advanced/VanishingNoiseVariant.lean Part 24)

**EM/Advanced/VanishingNoiseVariant.lean** (1650 lines, 0 sorry): Extended with Part 24 (+313 lines).

**Key definitions**:
- `IsFaithfulChar q chi` — `Function.Injective chi` (character is injective)
- `FaithfulCharacterEscape q` — all faithful nontrivial chars have non-summable gaps (PROVED unconditional)
- `NonFaithfulCharacterEscape q` — all non-faithful nontrivial chars have non-summable gaps (OPEN for q ≥ 5)

**Key proved theorems**:
- `faithful_character_escape` — **UNCONDITIONAL**: faithful nontrivial chi ⇒ non-summable gaps (case split: fallback/non-fallback)
- `prime_order_nontrivial_is_faithful` — Lagrange: prime-order group ⇒ nontrivial = faithful (via `Subgroup.eq_bot_or_eq_top_of_prime_card`)
- **`ufdStrong_three`** — **UFDStrong(3) UNCONDITIONAL** (unit group has prime order 2)
- **`variant_mc_three_unconditional`** — every element of (ZMod 3)ˣ reachable, ZERO open hypotheses
- `nfce_implies_ufdStrong` — NonFaithfulCharacterEscape alone suffices (FCE unconditional)
- `faithful_escape_landscape` — 4-clause summary

**Key Lean APIs (Session 219)**:
- `Subgroup.eq_bot_or_eq_top_of_prime_card` — Lagrange for prime-order groups
- `MonoidHom.ker_eq_bot_iff` / `MonoidHom.ker_eq_top_iff` — kernel ↔ injectivity/triviality
- `letI := Fact.mk (by decide : Nat.Prime 3)` — pattern for local Fact instances (use `decide` not `norm_num` for small Nat.Prime)
- `Nat.card_eq_fintype_card` — bridges Nat.card and Fintype.card for `eq_bot_or_eq_top_of_prime_card`

## Session 220 — Non-Faithful Character Escape Infrastructure (EM/Advanced/VanishingNoiseVariant.lean Part 25)

**EM/Advanced/VanishingNoiseVariant.lean** (1966 lines, 0 sorry): Extended with Part 25 (+316 lines).

**Key definitions**:
- `factorRatio n` — liftToUnit(minFac) * liftToUnit(secondMinFac)⁻¹ in (ZMod q)ˣ
- `KernelConfinement q chi` — factorRatio eventually always in ker(chi)
- `RatioKernelEscape q chi` — factorRatio escapes ker(chi) infinitely often

**Key proved theorems**:
- `gap_zero_iff_ratio_in_ker` — **KEY**: gap = 0 ↔ factorRatio ∈ ker(χ) (reduces NFCE from analytic to algebraic)
- `summable_implies_ratio_confined` — summable gaps + cofinite non-fallback ⇒ KernelConfinement (finite-range trick)
- `ker_index_ge_two` — χ ≠ 1 ⇒ ker(χ).index ≥ 2 (via `Subgroup.one_lt_index_of_ne_top`)
- `qual_escape_implies_nfce` — MinFacRatioEscapeQual ⇒ NFCE
- `nfce_implies_variant_mc` — NFCE ⇒ StochasticTwoPointMC (full chain)

**Key Lean APIs (Session 220)**:
- `Subgroup.one_lt_index_of_ne_top` — index ≥ 2 for proper subgroups of finite groups
- `Finset.sum_pair` — ∑ s ∈ {a,b}, f s = f a + f b (needs a ≠ b)
- `Finset.card_pair` — {a,b}.card = 2 (needs a ≠ b)
- `mul_div_cancel_left₀` — cancel 2 in (2 * z) / 2
- `Units.val_injective.eq_iff` — bridge between unit and ℂ equality

**Session 222 — NFCE(5) Infrastructure (Part 26) + Intersection Dichotomy (Part 27)**:
- `units_zmod_five_card` — |(ZMod 5)ˣ| = 4 (via `ZMod.card_units_eq_totient`)
- `nonfaithful_ker_card_eq_two_of_order_four` — GENERAL: non-faithful nontrivial χ in group of order 4 has |ker| = 2 (Lagrange: |ker|·index = 4, both ≥ 2)
- `ratio_escape_implies_nfce_five` — RatioKernelEscape for all non-faithful → NFCE(5)
- `ufdStrong_five_of_ratio_escape` / `variant_mc_five_of_ratio_escape` — chain to variant MC(5)
- `nfce_five_landscape` — 4-clause summary PROVED
- **Intersection argument** (T1.9): For q-1 with ≥2 distinct prime factors, total NFCE failure → factorRatio ∈ ⋂(kernels) = {1} → self-correcting. BUT NFCE failure is existential (one χ), not universal. Does NOT apply at q=5.

**Session 223 — NonFaithfulCharSeparation PROVED (Part 28)**:
- `exists_nonfaithful_separating_char` (private) — Given g ∉ H for nontrivial subgroup H, constructs non-faithful separating character via quotient G/H. Uses `MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity` + `mulCharToHom` + `QuotientGroup.mk'`.
- `nonFaithfulCharSeparation_of_two_prime_factors` — NFCS holds for groups with |G| having ≥2 distinct prime factors. Uses Cauchy (via `exists_zpowers_of_prime_order`) + coprime zpowers + quotient lifting.
- `nonFaithfulCharSeparation_units_zmod` — NFCS holds for (ZMod q)ˣ when q-1 has an odd prime factor. Covers all primes except Fermat primes (q = 2^k + 1).
- **KEY DISCOVERY**: NFCS is FALSE for prime-power-order groups (Z/4Z counterexample). The intersection kernel dichotomy does NOT apply to Fermat primes.
- **Lean API learnings**: `QuotientGroup.mk' H : G →* G ⧸ H`, `QuotientGroup.eq_one_iff` for membership, `Subtype.ext` for subtype contradiction, `Monoid.exponent_pos_of_exists` for NeZero instance.

**Stochastic ε-walk framework now architecturally COMPLETE** (Tier 1 done Session 208, Tier 2 done Session 217, Phase Transition done Session 218, Faithful Escape done Session 219, NFCE Infrastructure done Session 220, NFCE(5) done Session 222, NFCS done Session 223). Do NOT extend further unless proving NonFaithfulCharacterEscape itself or handling the Fermat prime cases.

## Session 221 — Backward Dynamics Framework (EM/Ensemble/BackwardDynamics.lean, NEW)

**EM/Ensemble/BackwardDynamics.lean** (494 lines, 0 sorry): NEW file created.

**Key definitions**:
- `jointCount X k q c b` — count of squarefree n in [1,X] with genProd(n,k)≡c and genSeq(n,k)≡b (mod q)
- `transitionProb X k q c b` — empirical transition probability: jointCount / sqfreeAccumCount
- `EnsembleTransitionApprox` — **NEW open hypothesis**: transition probs converge to 1/(q-1) for all primes q, steps k, nonzero classes c, b

**Key proved theorems**:
- `jointCount_sum_eq_accumCount` — partition: ∑_b jointCount(c,b) = sqfreeAccumCount(c) (via `Finset.card_biUnion`)
- `transitionProb_sum_one` — ∑_b transitionProb = 1 (via `Finset.sum_div` + `div_eq_one_iff_eq`)
- `accumCount_succ_decomp` — **KEY**: sqfreeAccumCount(k+1,a) = ∑_c jointCount(k,c,a·c⁻¹) (via biUnion + disjointness)
- `accumDensity_succ_eq` — density backward decomposition (via `div_mul_div_comm`)
- `eta_implies_crt_propagation` — **KEY REDUCTION**: ETA → CRTPropagationStep (~60 lines, limit arithmetic via `tendsto_finset_sum` + `Filter.Tendsto.mul`)
- `eta_sre_implies_prsd` — master chain: ETA + SRE → PositiveDensityRSD (via q=3 specialization + `Ioi_mem_nhds`)

**Key Lean APIs (Session 221)**:
- `IsUnit.mk0 c hc` — construct IsUnit from ≠ 0 in ZMod (replaces non-existent `ZMod.isUnit_nat_iff`)
- `ZMod.mul_inv_of_unit` — c * c⁻¹ = 1 for units in ZMod
- `inv_mul_cancel₀ hc_ne` — c⁻¹ * c = 1 for nonzero in field (ZMod p for prime p)
- `Finset.filter_ne' Finset.univ 0` — filter (· ≠ 0) = Finset.erase 0
- `Finset.card_erase_of_mem` + `ZMod.card` — |nonzero classes| = q - 1
- `Finset.sum_const` + `nsmul_eq_mul` — ∑ constant = card · constant
- `div_eq_one_iff_eq` — a/b = 1 ↔ a = b (for b ≠ 0)
- `Filter.Tendsto.congr'` + `Filter.eventuallyEq_iff_exists_mem` — connect actual function to decomposed form for large X
- `Ioi_mem_nhds` — (a, ∞) ∈ nhds(b) when a < b (for extracting eventual lower bounds from limits)

**CRTPropagationStep is now REDUCED to EnsembleTransitionApprox.** Do NOT formalize CRTPropagationStep-based proofs that bypass ETA — they are subsumed.

## Session 227 — FourierBridgeIdentity PROVED + ChiAtMultiplicativity Fixed

**EM/Advanced/RandomTwoPointMC.lean** (~693 lines, 0 sorry):
- **`fourier_bridge_identity`** — KEY IDENTITY: `treeCharSum q chi N acc fairCoin = pathCharSum q chi N acc` for `acc ≥ 2`. PROVED by induction on N.
- **`fourier_bridge_identity_proved`** — `FourierBridgeIdentity q` as Prop (unconditional)
- **`fairTreeCharSum_eq_pathCharSum`** — specialization to acc = 2 (unconditional)
- **`pathCharSum_vanishing_of_tree_contraction`** — now unconditional (FBI no longer needed as hypothesis)
- **ChiAtMultiplicativity** — **WAS FALSE** as stated (missing `chiAt(acc)` on LHS). Corrected and proved with `chiAt_mul_of_coprime` helper.
- **`pathCharSum_prod_split`** — Fin product split into step-0 × tail (private helper)

**Key Lean patterns (Sessions 227-228)**:
- `simp (config := { decide := true }) only [↓reduceIte]` — reduces `if false = true then X else Y` to `Y`
- `Fintype.sum_bool` — splits sum over Bool type
- `have hadd : 1 + acc = acc + 1 := by omega` — normalize add_comm for Nat.minFac matching
- `simp only [p₁, p₂]` — unfold `set` variables before `ring` (ring can't see through opaque set bindings)
- `Equiv.ofBijective _ (consDecision_bijective N)` — reindex sum via proved bijection
- `Fintype.sum_prod_type` — decompose `∑ (b, τ)` into `∑_b ∑_τ`
- `IsUnit.unit_mul` — `(ha.mul hb).unit = ha.unit * hb.unit` (KEY for chiAt multiplicativity)
- `ZMod.isUnit_prime_iff_not_dvd` — `IsUnit (p : ZMod n) ↔ ¬(p ∣ n)` for prime p
- `ne_eq ▸ ZMod.natCast_eq_zero_iff` — contrapositive: `¬(q ∣ a) → (a : ZMod q) ≠ 0` then `.isUnit`
- `Units.ext` + `push_cast; rfl` — prove unit equality when underlying values match after cast
- Backward non-divisibility: `dvd_mul_of_dvd_left`/`dvd_mul_of_dvd_right` for product divisibility propagation

**Session 228 — Now PROVED in EM/Advanced/RandomTwoPointMC.lean (898 lines)**:
- `chiAt_mul_of_coprime` — chiAt multiplicative for coprime-to-q naturals
- `not_dvd_epsWalkProdFrom_of_succ/le` — backward non-divisibility propagation chain
- `chiAt_multiplicativity_proved` — ChiAtMultiplicativity PROVED (corrected with chiAt(acc) on LHS)
- `pathCharSum_trivial` — trivial character gives pathCharSum = 1
- `two_isUnit_of_gt_two` / `chiAt_two_ne_zero` — acc=2 is unit for q ≥ 3
- `not_dvd_acc_implies_total_path_structure` — death fiber dichotomy for paths
- `reachedMultiset` / `reachCount` — helper defs for endpoint counting
- Landscape: 7 clauses (FBI, ChiAtMultiplicativity, trivial pathCharSum, pathCount bound, q=3 zero-mean, generalized walk bridge, reached multiset cardinality)

**Session 230 — Fourier Counting Infrastructure (EM/Advanced/RandomTwoPointMC.lean 898 → 1111 lines)**:
- Character orthogonality for `(ZMod q)ˣ` PROVED: `hom_card_eq_units`, `mulChar_sum_eq_zero_units`, `hom_sum_units`, `hom_indicator_units`, `char_count_formula_units`
- Death/survival partition: `deathCount`, `survivalCount`, `survival_plus_death` (S+D = 2^N), `pathCount_sum_eq_survival` (∑ pathCount = S)
- `uniform_bound_of_tendsto_local` — finite uniform bound extraction for finitely many sequences
- `PathSurvival` — OPEN: S/D → ∞ (structural property of binary walk tree)
- `TCAPathSurvivalImpliesRandomMC` — OPEN: TCA + PathSurvival → RandomTwoPointMC
- **Key structural discovery**: TCA alone INSUFFICIENT. "Death paths" (q | endpoint) break ChiAtMultiplicativity. PathSurvival needed.
- **Algebraic argument verified**: For q ≥ 5 (primes), q²-4q+2 > 0 gives contradiction. For q=3: TCA(3) is false (pathCharSum = χ(3) ≠ 0), so vacuous.
- **NFCE(5) assessed 2/10** — NFCS fails at Fermat prime q=5 (|G|=4=2², ratio constrained to {1,4} not {1}).
- **Remaining formalization gap**: building `unitEndpointMultiset` and proving count identity bridging to `pathCharSum` via ChiAtMultiplicativity on surviving-path subset.

## Session 229 — EM/Ensemble/BagArithmetic.lean CREATED (225 lines, 0 sorry)

**File**: `EM/Ensemble/BagArithmetic.lean` (added to root import `EM.lean`)
- **4 definitions**: `genEuclidOmega` (ω), `genBagDiversity` (residue diversity mod q), `genFactorsInClass` (per-class factor set), `genEuclidCofactor` (cofactor = (genProd+1)/genSeq)
- **16 theorems proved**: `genEuclidOmega_pos`, `genBagDiversity_le_omega`, `genBagDiversity_le_q`, `genSeq_mem_primeFactors`, `genSeq_in_bag`, `genFactorsInClass_subset`, `genEuclidCofactor_mul`, `genEuclidCofactor_pos`, `genProd_succ_not_dvd_two`, `two_not_mem_primeFactors_of_pos`, `primeFactors_odd_of_pos`, `primeFactors_ge_three_of_pos`, `genFactorsInClass_nonempty`, `genFactorsInClass_card_pos`, `genFactorsInClass_card_sum` (partition identity), `cofactor_primeFactors_subset`, `cofactor_omega_le`, `bag_arithmetic_landscape` (6-clause conjunction)
- **CED = Dead End #115 confirmed**: cofactor ↔ multiplier bijection when alive means any cofactor distributional claim ≡ CME. Do NOT formalize cofactor character cancellation hypotheses as "new" approaches.

## Session 233 — EM/Advanced/IteratedProductCoverage.lean CREATED (293 lines, 0 sorry)

**File**: `EM/Advanced/IteratedProductCoverage.lean` (added to root import `EM.lean`)
- **1 definition**: `iteratedMulFinset` (iterated set product: S_0 * S_1 * ... * S_{n-1})
- **15 proved theorems**: `iteratedMulFinset_card_growth` (iterated Cauchy-Davenport card lower bound), `iteratedMulFinset_eq_univ` (product = univ after |G|-1 steps with |S_k|≥2), `target_reached`, `iterated_product_diameter`, `cd_card_bound`, `minOrder_units_zmod_safe_prime` (Lagrange for safe primes), `safe_prime_coverage`, `general_coverage_criterion`, `iterated_product_coverage_landscape` (3-clause summary)
- **1 open Prop**: `FactorBagCoverage` (connect abstract coverage to EM-specific factor sets)
- **Key Mathlib dependency**: `cauchy_davenport_minOrder_mul` from `Mathlib.Combinatorics.Additive.CauchyDavenport`
- **Limitation**: `minOrder = |G|` condition required. For `(ZMod q)ˣ`, this holds when q-1 is prime (safe prime). For general q, `minOrder = smallest prime factor of q-1`.
- **Connection**: Deterministic coverage complementing probabilistic `pathExistenceFromVanishing_proved` in EM/Advanced/VanishingNoise.lean.

## Session 235 — EM/Advanced/DenseCapture.lean CREATED (301 lines, 0 sorry)

**File**: `EM/Advanced/DenseCapture.lean` (added to root import `EM.lean`)
- **4 definitions**: `SelectionSeq` (ℕ → Bool), `captureSet q acc` (set of σ capturing prime q), `minFacSeq` (all-false = standard EM), `MC_at q acc` (MC as point-membership)
- **14 proved theorems**: `captureSet_isOpen` (KEY: captureSet open in product topology), `captureSet_level_isOpen` (per-level open via cylinder sets), `epsWalkProdFrom_depends_on_prefix` / `epsWalkFactorFrom_depends_on_prefix` (finitary dependence), `fullCapture_residual` (density → residual via Baire), `fullCapture_exists_residual` (existential comeager), `fullCapture_nonempty` (∃ full-capturing σ), `epsWalkProdFrom_tail_restart` / `epsWalkFactorFrom_tail_restart` (tail shift), `captureSet_tail_iff` (capture equivalence under shift)
- **1 open hypothesis**: `DenseCaptureHypothesis` — captureSet(q, acc) dense for all acc ≥ 2. Bridges to Ensemble ε-MC.
- **Instance**: `BaireSpace SelectionSeq` via `BaireSpace.of_t2Space_locallyCompactSpace` (Cantor space is compact T₂)
- **MC reformulation**: MC ⟺ minFacSeq ∈ ⋂_q captureSet(q, 2) (point-membership in Cantor space)
- **Key Mathlib dependencies**: `Mathlib.Topology.Baire.LocallyCompactRegular`, `Mathlib.Topology.Constructions`

**Key Lean APIs (Session 235)**:
- `isOpen_set_pi` — cylinder sets are open in product topology: `IsOpen {σ | ∀ i ∈ s, σ i ∈ U i}` for finite s and open U
- `BaireSpace.of_t2Space_locallyCompactSpace` — compact T₂ ⟹ Baire space (Cantor space = ∏ Bool is compact)
- `dense_sInter_of_isOpen` — countable family of open dense sets has dense intersection
- `residual_of_dense_Gδ` — dense Gδ ∈ residual filter
- `isOpen_iUnion` — union of open sets is open
- `isOpen_discrete` — every set in discrete topology is open (Bool is discrete)
- `Set.countable_univ` / `Set.Countable.mono` — primes are countable (subtype of ℕ)
- `Pi.topologicalSpace` — product topology on `ℕ → Bool` (auto-inferred)

**Architectural note**: EM/Advanced/DenseCapture.lean imports `EM.Advanced.EpsilonWalk` and uses `epsWalkProdFrom`/`epsWalkFactorFrom` from there. The key open bridge is `SigmaCRTPropagationStep` (in EM/Advanced/EpsilonWalk.lean), which blocks ε-MC ⟹ DenseCaptureHypothesis. Do NOT attempt to prove DenseCaptureHypothesis directly — it requires ε-MC infrastructure.

## Session 239-241 — EM/Advanced/EpsilonRandomMC.lean (643 → 992 lines, 0 sorry)

**File**: `EM/Advanced/EpsilonRandomMC.lean`

**Core infrastructure (Session 239)**:
- `MixedMC q` — q=2 ∨ ∃ valid σ capturing q from acc=2
- `MixedMCBelow q` — ∀ r prime < q, MixedMC r
- `MixedMullinConjecture` — ∀ q prime, MixedMC q
- `MixedDiversityWeak` — **OPEN**: for q ≥ 5 prime, acc ≥ 2, q ∤ acc, cofinal composite → ∃ valid σ capturing q
- `mixed_diversity_weak_implies_mixed_mc` **PROVED** — strong induction
- `mixed_mc_two`, `mixed_mc_three`, `mixed_mc_landscape` all **PROVED**

**Walk-mod-q structural lemmas (Session 241, Part 18)**:
- `prime_factor_ne_not_dvd` **PROVED** — distinct primes don't divide each other
- `walk_coprime_until_capture` **PROVED** — walk stays coprime to q until capture (induction)
- `hit_implies_capture'` **PROVED** — q | P_σ(n)+1 ⇒ ∃ σ' capturing q (prefix agreement via `mixedWalkProd_depends_on_prefix`)

**MixedHitting reduction (Session 241, Part 19)**:
- `MixedHitting` — **OPEN**: cleaner than MixedDiversityWeak (q ≥ 5, cofinal composites → ∃ valid σ with q | P+1)
- `mixed_hitting_implies_diversity_weak` **PROVED** — via hit_implies_capture'
- `mixed_hitting_diversity_implies_mc` **PROVED** — MixedHitting + MixedDiversity → MixedMullinConjecture

**Two-point bridge (Session 241, Part 20)**:
- `embedBoolToMixed` — embeds `ℕ → Bool` into `MixedSelection` (true→none, false→some secondMinFac)
- `embed_walk_agreement` **PROVED** — mixed walk = two-point walk under embedding (induction)
- `embed_valid` **PROVED** — embedding is valid mixed selection
- `two_point_capture_implies_mixed_capture` **PROVED** — two-point capture ⇒ mixed capture
- `two_point_capture_implies_mixed_mc` **PROVED** — any two-point capture from acc=2 ⇒ MixedMC

**UFDStrong bridge (Session 241, Part 20b)**:
- `UFDStrongImpliesMixedMC` — **OPEN**: self-consistent vs non-self-consistent gap
- `ufd_strong_implies_mixed_mc_chain` **PROVED** — UFDStrongImpliesMixedMC + UFDStrong ⇒ MixedMullinConjecture
- `two_point_mixed_mc_landscape` **PROVED** — 5-clause summary

**Key pattern**: Strong induction on prime q, base q=2 (2|acc), q=3 (mixed_capture_three), q≥5 (MixedDiversityWeak). `hit_implies_capture'` constructs σ' = prefix(σ,n) ++ [some q] ++ [none,...], uses `mixedWalkProd_depends_on_prefix` for agreement.

**Reachable set framework (Sessions 242-243, Parts 23-24)**:
- `reachableAt q acc n` — positions mod q reachable at step n
- `reachableEver q acc` — ⋃_n reachableAt, all ever-reachable positions
- `factorSetModQ q P` — prime factors of P+1 as residues mod q
- `mixed_hitting_iff_neg_one_reachable` — MixedHitting ↔ -1 ∈ reachableEver (PROVED)
- `reachableAt_from_factor` — **CORE**: any prime p | P+1 gives P·p ∈ R_{n+1} (σ' construction, ~50 lines)
- `reachable_grows_pair`, `reachable_composite_branch` — branching from composite P+1
- `reachable_growth_landscape` — 4-clause summary

**Coset impossibility (Session 244, Part 25)**:
- `mixedWalkProd_two_minFac_eq_prod` — **bridge**: standard EM walk = mixed walk with minFacMixed selection
- `reachableEver_ratios_escape_subgroup` — **KEY**: PRE + MCBelow ⇒ ∃ u₁,u₂ ∈ R_∞ with u₁·u₂⁻¹ ∉ H (proper subgroup)
- `reachableEver_not_in_coset` — R_∞ cannot be contained in any coset g·H for proper H
- `coset_impossibility_landscape` — 3-clause summary
- Private helpers: `prod_cast_ne_zero`, `natCast_prime_ne_zero'` (reconstructed), `prod_in_reachableEver`, `prod_mul_prime_in_reachableEver`, `ratio_of_reachable_pair`
- **Key technique**: `natCast_prime_ne_zero` is private in Bootstrap.lean — reconstruct via `ZMod.natCast_eq_zero_iff` + `Nat.le_of_dvd`
- **Key technique**: coset cancellation uses commutativity of (Z/qZ)× via `mul_comm`, `mul_assoc`, `mul_inv_rev`

**Factor confinement (Session 245, Part 26)**:
- `allowedFactors q c R` — {m : ZMod q | c * m ∈ R} (allowed factor residues)
- `forbiddenFactors q c R` — complement: {m | c * m ∉ R}
- `AllFactorsInSet q N F` — every prime factor of N has residue in F
- `factor_confinement` — **CORE**: prime p | P+1 at reachable P ⟹ (p : ZMod q) ∈ allowedFactors (one-liner from `reachableEver_from_factor`)
- `all_factors_confined` — ALL prime factors of P+1 confined (universal quantifier)
- `standard_euclid_factors_confined'` — specialization to prod(n)+1 via bridge
- `forbidden_nonempty_of_unit` — c unit ∧ R ⊊ univ ⟹ forbidden nonempty (via `Units.mul_inv_cancel_left`)
- `allowed_ne_univ_of_unit` — c unit ∧ R ⊊ univ ⟹ allowed set proper
- `FactorEscapeHypothesis q` — **OPEN**: EM Euclid numbers escape step-dependent proper factor confinement
- `factor_escape_implies_mixed_hitting` — FEH + hne ⟹ -1 ∈ R_∞ (by_contra + FEH contradiction)
- `factor_escape_implies_reachable_full` — FEH + hne ⟹ R_∞ = Set.univ
- Private: `walk_pos_ne_zero'`, `walk_pos_isUnit` (walk position is unit under hne)
- **Key technique**: `Set.ne_univ_iff_exists_notMem` for R ≠ univ; `IsUnit.mk0` for nonzero → unit in ZMod p

### Sessions 247-249 — EM/Ensemble/MixedEnsemble.lean (Population Sieve → a.a. Mixed Hitting)

**EM/Ensemble/MixedEnsemble.lean** (914 lines, 0 sorry):
- Defs: `sqfreeConfinedCount q X R` (confined population count), `sqfreeTrappedCount q X` (coprime-to-q hitting failures), `PSCD q` (Population Sieve Confinement Decay — OPEN), `properFinsets q` (finsets missing a nonzero element)
- Bridge: `mixedWalkProd_minFac_eq_genProd` (all-minFac mixed walk = genProd, by induction)
- Factor confinement: `genProd_factors_confined` (all steps), `unconditional_confinement` (step 0)
- Zero-not-reachable: `walk_position_isUnit_of_coprime_trapped` (walk stays in units), `zero_not_reachable_of_coprime_trapped` (0 ∉ R_∞)
- Pigeonhole: `trapped_le_sum_confined` (via `Finset.card_biUnion_le`)
- Main: `pscd_implies_trapped_density_zero` (squeeze_zero + tendsto_finset_sum), `pscd_implies_almost_all_mixed_hitting` (corollary)
- **PEAP chain (Sessions 248-249)**: `PrimeReciprocalClassDivergent`, `ForbiddenClassDivergent`, `sieveProduct` (defs); `sieveProduct_nonneg`/`sieveProduct_le_one` (PROVED), **`peap_implies_fcd_proved`** (PEAP⇒FCD, PROVED Session 249 via `not_summable_iff_tendsto_nat_atTop_of_nonneg`), **`sieve_product_vanishing_proved`** (FCD⇒SPV, PROVED Session 249 via `sparse_product_contraction`), **`fcd_sub_spv_implies_pscd`** (FCD+SUB+SPV⇒PSCD, PROVED via squeeze_zero + const_mul), **`peap_chain_implies_pscd`** (PEAP+SUB⇒PSCD, PROVED — only 2 hypotheses), `extended_mixed_ensemble_landscape` (4-clause, PROVED)
- **Session 251**: `fmcd_chain_implies_almost_all_mixed_hitting` PROVED (FMCD replaces SieveUpperBound)
- **Session 252**: `weak_fmcd_proved` PROVED UNCONDITIONALLY (sqfreeCount ≥ X/4 + CRT counting). `weak_fmcd_chain_implies_almost_all` PROVED (PEAP alone ⇒ a.a. mixed hitting). EM/Ensemble/MixedEnsemble.lean: ~1958 lines.
- 1 open Prop: `PrimesEquidistributedInAP` (= standard ANT, sole remaining gap)
- Import: `EM.Advanced.EpsilonRandomMC`, `EM.Ensemble.FirstMoment`, `EM.IK.Ch2`

### Sessions 253-255 — EM/Advanced/InterpolationMC.lean (838 lines, 0 sorry)

**File**: `EM/Advanced/InterpolationMC.lean`

**Layer 1 (Session 253):**
- `stepWeightLB ε P = ε / ω(P+1)` — per-step weight lower bound via `Nat.nonempty_primeFactors`
- `pathWeightLB` = `∏ k ∈ range n, stepWeightLB ε (mixedWalkProd m σ k)` — product of step weights
- `PositiveProbCapture q m ε` — ∃ valid path capturing q with positive weight
- `stepWeightLB_pos`, `pathWeightLB_pos`, `reachable_implies_positive_prob_capture`, `almost_all_positive_prob_capture`
- `interpolation_mc_landscape` — 5-clause conjunction

**Layer 2 (Session 254):**
- `GoodAccumulator q P` — every unit of (ZMod q)ˣ is in `reachableEver q P`
- `Regeneration q m` — GoodAccumulator propagates through mixed walk tree
- `block_coverage` — uniform depth N₀ via `Finset.sup` over (ZMod q)ˣ (**KEY PROVED**)
- `neg_one_ne_zero_zmod`, `neg_one_isUnit` — ZMod helpers (q > 2)
- `good_accumulator_neg_one_reachable`, `good_accumulator_implies_capture`
- Walk concatenation: `concatMixedSelection`, `concat_prefix`, `concat_walk_prefix`, `concat_walk_tail`, `concat_valid` (5 lemmas)
- `regeneration_implies_cofinal_hitting`, `regeneration_implies_capture_at_every_step`
- `regeneration_implies_iterated_hitting` — induction on target_hits, walk concat, `Finset.card_insert_of_notMem`
- `layer2_landscape` — 5-clause conjunction

**Layer 3 (Session 255):**
- `mixedWalkProd_squarefree` — squarefree propagation through mixed walks (induction, `Nat.squarefree_mul_iff`) **PROVED**
- `TreeSieveDecay q` — ∃ P₀, ∀ P ≥ P₀, Squarefree P → GoodAccumulator q P (**OPEN**)
- `treeSieveDecay_implies_regeneration_at` — one-liner bridge: TSD + monotonicity + squarefree ⇒ GoodAccumulator at every step **PROVED**
- `treeSieveDecay_implies_regeneration` — TSD ⇒ Regeneration for all large squarefree m **PROVED**
- `tsd_implies_good_and_regen` — combined good + regen for m ≥ max(P₀, 2) **PROVED**
- `tsd_implies_iterated_hitting` — TSD ⇒ iterated hitting (assembles Layer 2 machinery) **PROVED**
- `full_interpolation_landscape` — 4-clause conjunction **PROVED**

Import: `EM.Ensemble.MixedEnsemble`
Open Props: `PrimesEquidistributedInAP` (ANT), `TreeSieveDecay` (sieve-theoretic, replaces Regeneration as sole gap)

**Key design choice (Session 255)**: TreeSieveDecay drops the coprimality condition `Nat.Coprime P q` to avoid post-capture complications. This makes the bridge a one-liner using `mixedWalkProd_mono` + `mixedWalkProd_squarefree`. The `max(P₀, 2)` threshold ensures both TSD applicability and `m ≥ 2` for monotonicity.

**PSCD definition (CORRECTED)**: `∀ R, (∃ a : ZMod q, a ≠ 0 ∧ a ∉ R) → (0 ∉ R) → Tendsto (confined_density R) atTop (nhds 0)`. Two conditions: R misses a NONZERO element AND does not contain 0.

**Key Lean API**:
- `neg_ne_zero.mpr one_ne_zero` proves `(-1 : ZMod q) ≠ 0` in any nontrivial ring
- `ZMod.isUnit_prime_iff_not_dvd hp` gives `IsUnit (p : ZMod q) ↔ ¬(p ∣ q)` — note the direction: p divides q, NOT q divides p
- `hq.eq_one_or_self_of_dvd _ hdvd` for `hdvd : factor ∣ q` when q is prime
- `IsUnit.mk0 a ha` for `a ≠ 0` in `ZMod p` (prime p) with `Fact q.Prime`
- `Filter.Tendsto.const_mul` needs `rw [show (0:ℝ) = C * 0 from by ring]` first
- `field_simp` handles `C * sqfreeCount * sieveProduct / sqfreeCount = C * sieveProduct`
- `IK.PrimesEquidistributedInAP` needs full namespace (not in scope by default)
- `not_summable_iff_tendsto_nat_atTop_of_nonneg` — for nonneg f, ¬Summable f ↔ partial sums → ∞ (Session 249)
- `ZMod.isUnit_iff_coprime` + `ZMod.natCast_zmod_val` — bridge unit a → coprime a.val q (Session 249)
- `sparse_product_contraction` (EM/Advanced/VanishingNoiseC.lean) — ∏a_k→0 for a_k∈[0,1] with ∑(1-a_k)=∞ (Session 249)
- `tendsto_natCast_atTop_atTop` — NOT deprecated `Nat.tendsto_cast_atTop_atTop` (Session 249)

## Session 267 — Quotient Character Lift (EM/Advanced/VanishingNoiseVariantD.lean)

**New infrastructure** (Part 28, lines 964-1135):
- `quotientChar` (def): `QuotientGroup.lift chi.ker chi le_rfl` — χ factors through G/ker(χ)
- `quotientChar_faithful`: injective via `QuotientGroup.ker_lift` + `QuotientGroup.map_mk'_self`
- `quotientChar_apply`: χ(g) = χ̄(π(g)) by `rfl`
- `quotient_card_ge_two`: via `Subgroup.one_lt_index_of_ne_top` + `Subgroup.index_eq_card`
- `kernelConfinement_iff_quotient_eventually_one` / `ratioKernelEscape_iff_quotient_io_ne_one` via `simp only [QuotientGroup.eq_one_iff]`
- `quotient_escape_landscape`: 4-clause summary

**Key Lean APIs (Session 267)**:
- `QuotientGroup.lift H f hle` — universal property of quotient, where `hle : H ≤ f.ker`
- `QuotientGroup.ker_lift` — ker of lifted map = image of H under quotient map
- `QuotientGroup.map_mk'_self H` — image of H under π : G → G/H is ⊥
- `MonoidHom.ker_eq_bot_iff` — ker = ⊥ ↔ injective
- `MonoidHom.ker_eq_top_iff` — ker = ⊤ ↔ f = 1
- `Subgroup.one_lt_index_of_ne_top` — proper subgroup has index > 1
- `Subgroup.index_eq_card` — index = Nat.card of quotient
- `Subgroup.index_dvd_card` — index divides group cardinality
- `QuotientGroup.eq_one_iff` — π(g) = 1 ↔ g ∈ H

**Next target**: Bridge faithful_character_escape to quotient groups. Either:
(a) Show quotient factorRatio walk IS a (ZMod r)ˣ walk for r | q
(b) Prove abstract faithful escape for any finite abelian group quotient

## Session 269 — Stochastic MC + Factor Diversity (NEW FILES)

**EM/Advanced/StochasticEM.lean** (347 lines, 2 defs, 13 theorems):
- `StochasticMC ε q` — q=2 ∨ (q prime ∧ 0<ε ∧ ε≤1 ∧ PositiveProbCapture q 2 ε)
- `StochasticMullinConjecture ε` — ∀ q prime, StochasticMC ε q
- `stochastic_mc_of_tsd` — TSD(q) ⇒ StochasticMC(ε,q) for q≥3
- `tsd_implies_stochastic_mullin` — ∀q TSD ⇒ StochasticMullinConjecture
- `stochastic_mc_implies_mixed_mc` — StochasticMC ⇒ MixedMC
- `phase_transition_summary` — sharp ε=0 phase transition (norm 1 vs <1)
- `stochastic_em_landscape` — 6-clause summary
- Imports: GeometricCapture, VanishingNoiseB

**EM/Advanced/FactorDiversity.lean** (346 lines, 4 defs, 15+ theorems):
- `genFactorSet n k` — `(genProd n k + 1).primeFactors` (ensemble factor set)
- `genFactorSetMod q n k` — factor set residues mod q
- `FactorDiversityAtStep q n k` — ≥2 distinct residues at step k
- `InfinitelyManyDiverseSteps q n` — diversity i.o.
- `genFactorSet_nonempty`, `genFactorSet_all_prime`, `genSeq_mem_genFactorSet` — structural
- `factor_diversity_spectral_contraction` — wraps `meanCharValue_norm_lt_one_of_distinct`
- `diverse_steps_imply_vanishing` — KEY: i.o. diversity ⇒ ‖avgCharProduct‖→0
- `factor_diversity_landscape` — 7-clause summary
- Imports: StochasticEM, InterpolationMC

**EM/Advanced/DiverseStepsToCapture.lean** (281 lines, 1 def, 12 theorems):
- `DiversityImpliesReachable q` — IMDS → (-1 ∈ reachableEver q 2) (open Prop, strictly weaker than TSD)
- `genFactorSet_dvd_mixedWalk` — factor set divides mixed walk accumulator + 1
- `genFactor_in_reachableAt` — each prime factor gives reachable position at step k+1
- `genFactor_in_reachableEver` / `genFactor_in_reachableEver'` — in ever-reachable set
- `diverse_step_two_reachable` — ≥ 2 DISTINCT reachable elements at diverse steps (via `mul_left_cancel₀`)
- `diversity_reachable_implies_stochastic_mc` — DIR + IMDS → StochasticMC(ε, q)
- `diversity_reachable_implies_mixed_mc` — DIR + IMDS → MixedMC(q)
- `tsd_implies_diversity_reachable` — TSD → DIR (strictly stronger)
- `prod_in_reachable_ever` — standard walk position always reachable (unconditional)
- `diverse_step_reachable_growth` — unconditional structural growth
- `diverse_steps_to_capture_landscape` — 6-clause summary
- Imports: FactorDiversity
- **Key bridge**: `mul_left_cancel₀` in ZMod q (field for prime q) gives injectivity of left multiplication

**Key open questions for next session**:
- Can InfinitelyManyDiverseSteps be proved unconditionally? (connects to genProd+1 having ≥2 prime factors i.o.)
- DiversityImpliesReachable: gap from "≥ 2 distinct reachable positions i.o." to "-1 reachable" = orbit-specificity barrier (#90)
- NonFaithfulCharacterEscape: route to UFDStrong at q ≥ 5 (quotient lift from Session 267)

## Session 289 — Asymptotic Growth (Structure.lean)

**4 new theorems proved** in `EM/Ensemble/Structure.lean` (AsymptoticGrowth section):
- `genSeq_tendsto_atTop` — one-liner: `Function.Injective.nat_tendsto_atTop (genSeq_injective hn)`
- `genSeq_eventually_gt` — `Filter.Ioi_mem_atTop` + `Filter.eventually_atTop.mp`
- `genProd_ge_mul_pow_two` — induction, `calc` chain with `ring`, `Nat.mul_le_mul` + `Nat.Prime.two_le`
- `genProd_tendsto_atTop` — `Filter.tendsto_atTop_mono` with exponential bound, `Nat.lt_two_pow_self.le`

**Key Filter API lesson (DO NOT use non-existent methods)**:
- ✅ `Function.Injective.nat_tendsto_atTop` — injective f : ℕ → ℕ tends to atTop
- ✅ `Filter.Ioi_mem_atTop M` — `Set.Ioi M ∈ Filter.atTop` (the set {n | M < n})
- ✅ `Filter.eventually_atTop.mp` — convert `∀ᶠ n in atTop, P n` to `∃ N, ∀ n ≥ N, P n`
- ✅ `Filter.tendsto_atTop_mono` — if f ≤ g and f → atTop, then g → atTop
- ✅ `Filter.tendsto_atTop_atTop.mpr` — intro rule: `(∀ b, ∃ N, ∀ n ≥ N, b ≤ f n) → Tendsto f atTop atTop`
- ✅ `Nat.lt_two_pow_self` — `n < 2^n` (exponential growth)
- ✅ `Nat.le_mul_of_pos_left _ h` — `b ≤ a * b` when `0 < a`
- ❌ `Filter.Tendsto.eventually_ge_atTop` — DOES NOT EXIST
- ❌ `Filter.Tendsto.atTop_pow` — DOES NOT EXIST
- ❌ `Filter.Tendsto.of_le_atTop` — DOES NOT EXIST
- ❌ `Filter.Tendsto.comp_atTop` — DOES NOT EXIST as method

**Pattern for "tendsto atTop implies eventually > M"**: Use `(h_tendsto) (Filter.Ioi_mem_atTop M)` to get `∀ᶠ n in atTop, M < f n`, then `Filter.eventually_atTop.mp` to get `∃ N, ∀ n ≥ N, M < f n`.

**Pattern for "prove tendsto atTop from lower bound"**: Use `Filter.tendsto_atTop_mono bound_lemma` where `bound_lemma : ∀ n, g n ≤ f n` and then prove `Tendsto g atTop atTop` (e.g., via exponential growth).

## Workflow — WRITE CODE EARLY

**You have ~20 turns. Do NOT spend more than 5 turns reading. Start writing code by turn 5.**

1. Read ONLY the specific section you need to modify (use line offsets, don't read whole files)
2. **Write code by turn 5** — even a partial skeleton with `sorry` placeholders
3. Run `lake build` to get error messages
4. Fix errors iteratively (this is where most turns should go)
5. Fill in any remaining `sorry` proofs
6. Final `lake build` — zero errors, zero sorry

## Rules

- **NEVER introduce `sorry`** — every proof must be complete
- **NEVER break existing proofs** — always run full `lake build` after changes
- **Prefer small, focused changes** — one lemma at a time
- When stuck, decompose into simpler auxiliary lemmas
- Check Mathlib for existing lemmas before proving from scratch

---

## Session 299 — Lean/Mathlib API notes (toolchain v4.29.0)

Discovered while landing `EM/Population/AutonomousBranch.lean`,
`EM/Population/HittingSetStructure.lean`, and `EM/Reduction/NoInvariant.lean` Part 6b.

**Deprecations / renames in this snapshot**
- `le_or_lt` and `Nat.le_or_lt` are **unknown identifiers** (likely `le_or_gt` now). Prefer
  `by_cases h : a ≤ b`; `omega` consumes the negated branch fine.
- `push_neg` is **deprecated** (suggests `push Not`). Often avoidable by inlining, e.g.
  `not_not.mp (fun hnp => hcon ⟨n, hn, hnp⟩)`.

**Imports not transitively available in the EM tree**
- `Nat.exists_prime_lt_and_le_two_mul` (Bertrand) needs an explicit
  `import Mathlib.NumberTheory.Bertrand`. Signature:
  `(n : ℕ) (hn0 : n ≠ 0) : ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n`.

**Project-specific gotchas**
- `Nat.minFac_le_of_dvd` does **NOT** apply to this project's `Euclid.minFac`. Use the
  project's own `minFac_min' (n m : Nat) (hn : 2 ≤ n) (hm : 2 ≤ m) (hmd : m ∣ n) : minFac n ≤ m`
  (`EM/Core/Euclid.lean:260`). **Note the argument order: bounds first, divisibility last.**
- `walkZ q n` is definitionally `((prod n : ℕ) : ZMod q)`, so walk-language restatements are
  often `:= rfl` or a direct term alias.
- `FunctionFieldAnalog.ffAutonomousMap` / `ffAutonomousOrbit` carry a `[Fact (Nat.Prime p)]`
  instance binder — declare `haveI : Fact (Nat.Prime q) := ⟨hq⟩` before mentioning them.
  Despite the file's function-field framing, **these are pure `ZMod p` statements** and are
  reusable for the integer sequence verbatim.
- `AppearedPrimes` in `EM/Population/WeakMullin.lean` is `private` — unusable from other files.

**Mathlib signatures worth remembering**
- `ZMod.natCast_eq_zero_iff (a b : ℕ) : (a : ZMod b) = 0 ↔ b ∣ a` — needs **no** `NeZero b`.
- `Set.ncard_le_ncard_of_injOn f hmaps hinj hfin` — `hfin` is finiteness of the **target**,
  and it comes **last**.
- `Set.Finite.diff` takes no explicit argument here: `(h.diff)` works for `s \ t`.
- `Finset.prod_ne_zero_iff.mpr fun p hp => (hT p hp).pos.ne'` discharges `∏ p ∈ T, p ≠ 0`
  for a Finset of primes.
- `Set.iUnion` lemmas want `ι : Sort*` (not `Type*`) to apply in full generality.

**Idiom: `Finset.sup` over per-element existentials.** To turn `∀ q ∈ Q, ∃ N₀, P q N₀` into a
single uniform threshold, first *totalise*: state `∀ q, ∃ N₀, q ∈ Q → P q N₀` (using
`by_cases q ∈ Q`, with `⟨0, absurd⟩` off `Q`), *then* `choose`. This yields a plain
`N : ℕ → ℕ` that `Finset.sup` accepts, avoiding `Finset.attach` entirely.

---

## Session 310 infrastructure note (supersedes the queue part of Session 309's)

WP2 and Group 6 are DONE (commit f391732, all 0 sorry): `EM/Population/SelectionLaw.lean`
(type cells `stepCell` over `modulus q Y = ∏_{r ∈ bandUpTo q Y} r` — q EXCLUDED; generic
dependent-family CRT counting `card_filter_crt`; EXACT `selection_law`),
`EM/Population/TreeChernoff.lean` (abstract finite Chernoff: `exp_supermartingale`,
`chernoff_bound(_local)`, `chernoff_quarter(_local)` — reuse for ANY finite conditional-
counting argument; Mathlib-only), `EM/Population/MertensLower.lean` (`mertens_lower`
const 13, `window_recip_lower` const 16 — the lower Mertens toolbox),
`EM/Population/LSPlus.lean` (`ls_plus`, plus the reusable congruence layer
`survival_congr`/`stepSurvival_congr`/`fiber_eq_stepCell` and `bigStep_iff_survives`).
Open work items, in order: Group 7 tail assembly TL1–TL3 (use `window_recip_lower` +
`selection_law` per cell; target `tail ≲ log n/n` at log Y = n²); the D5c policy lemma
(discharge `bigThreshold ≤ Y` from `n² ≤ log Y`); Lemma D; Theorem C.
v4.33 API notes from Session 310: `Finset.range_add_one` (not range_succ),
`Finset.card_filter_add_card_filter_not`, camel `notMem`, `le_mul_inv_iff₀` for Markov
rearrangements, explicit `[DecidablePred]` binders before stating filter-rewrite lemmas
(Classical.propDecidable mismatch), and don't `push_cast` through
`((∏ r ∈ T, r : ℕ) : ZMod r)` before a `ZMod.natCast_eq_zero_iff` rewrite.

## Session 309 infrastructure note

New files (all 0 sorry): `EM/Population/SeedTypes.lean` (Lemma A/B, visited sets),
`EM/Population/SeedCapture.lean` (q-free dynamics `genProdAvoid`/`genSeqAvoid`, Lemma C
coupling + capture, `captured_iff_mem_visited`), `EM/Population/LargeStepRoughness.lean`
(box process: visitedAt/box/boxCard/Charged, charge budget `charge_sum_le_harmonic` +
`chargeBudget_le`, brink lemma, rho/survival layer, M1/M2). Build on these for the (LS)
campaign; statement list in `agents/state/findings_ls_verification.md` §4. Toolchain
v4.33.0 API notes are in the Session-309 agent reports quoted in state/strategy_log.md
(range_add_one, unconditional card_sdiff, one_div_le_one_div_of_le, no IsUnit inside
Finset.filter under open Classical, Real.log_le_log argument shape).

## Session 311 update (2026-08-19)
Infrastructure now available (all 0 sorry): `TailAssembly.tail_small` + `ls_plus_with_tail`
(quantitative tail at policy n²/2 ≤ log Y; note the vacuity lesson: never intersect
hypothesis windows into an unsatisfiable point — check ∃ Y), `LemmaD.window_ap_recip_lower`
(window AP 1/p-mass ≥ 1/(8φ(q)), Karamata-only), `LemmaD.window_recip_upper` (≤ 32),
`LemmaD.lemma_D_z` (cell-form conditional multiplier bound, κ = e⁻¹²⁸/(16φ(q)), window
start z a free parameter), `TheoremC.theorem_C` (#GoodSeed ≤ M·e^{−(3/8)κ((c₁/2)n−K₀)}
via TreeChernoff.chernoff_quarter_local — no new engine), `AlmostAllGenMC` (headline, check
build state). API notes: `div_le_div_iff₀` (not `div_le_div_iff`); `Finset.le_sup` needs
explicit `(f := ...)`; `positivity` can't unfold defs; `ZMod.natCast_zmod_surjective`;
`Finset.card_le_card_of_injOn` goals need `simp only [Finset.mem_coe, ...]` not `rw`.

---

## Session 312 — new infrastructure (seed-average programme, natural-density form)

The seed-average programme (Sessions 308–312) is complete and now delivers a **natural-density**
statement. Newly available, all 0 `sorry`, axioms `[propext, Classical.choice, Quot.sound]`:

| Name | File | What it gives you |
|---|---|---|
| `FiberTheoremC.FiberGood` / `theorem_C_fiber` | `EM/Population/FiberTheoremC.lean` | Theorem C with `GoodSeed`'s two seed-specific clauses replaced by a **fibre existential**; the predicate is then `modulus q Y`-periodic. Use this, not `TheoremC.theorem_C`, whenever you need periodicity. |
| `PeriodicDensity.periodRep` / `card_filter_le_of_type_bad` / `eventually_density_le` / `limsup_density_le` | `EM/ForMathlib/PeriodicDensity.lean` | Generic, EM-independent: "few bad residue classes mod `M`" ⟹ "small upper natural density". |
| `TypeBadSmall.type_bad_small` | `EM/Population/TypeBadSmall.lean` | The three type-measurable bad events cover `≤ ε·M_Y` of one period. |
| `AlmostAllDensity.almost_all_genmc_density` / `almost_all_genmc_limsup` / `finite_simultaneous_density` | `EM/Population/AlmostAllDensity.lean` | The headlines. Upper natural density `≤ ε` of seeds missing `q` in `n` steps; and the finite-`S` uniform version. |

**The lesson worth internalising.** A bound on a *fraction over one period of `M`* is a **diagonal**
count (each residue class occurs once, so every other coordinate of the seed is determined by
`m mod M`); a natural-density bound is a **product** count. They are not comparable. Before
transferring any period bound to density, check that the counted predicate is genuinely a function
of `m mod M` — and if it is not, look for the fibre weakening that makes it one, rather than
weakening the statement.

## Standing caution on priority claims

Never write "first / only formalization in any proof assistant" in a docstring or the paper without
checking, at minimum: the **Isabelle/HOL AFP**, the Lean project **PrimeNumberTheoremAnd**,
**Metamath set.mm**, **HOL Light `100/`**, and **open Mathlib PRs**. Session 312 found that the
repo's long-standing "no Mertens theorem in any proof assistant" claim was false (AFP since 2018),
and that a `ζ(2) = π²/6` "unprecedented" claim was also false (Mathlib has the Basel problem).
"Not in Mathlib at pin `vX.Y.Z`" is usually the only defensible form. Record:
`agents/state/findings_mertens_priorart.md`. One further claim in the repo — "first van der Corput
bound in any proof assistant" (`EM/LargeSieve/Analytic.lean`) — is **unverified and suspect**.

## Session 313 (2026-08-19) — scoping session, no new Lean; one small target going spare

Session 313 was scoping only (`docs/analysis/sure_layer_missed_primes.md`, verdict **DEAD — budget
vacuous**). Dead ends #169–#174 were catalogued; `EM/Meta/DeadEnds.lean` is now
**174 / 164 / 32 / 15** and re-exports `SeedCapture.genSeqAvoid_ne_avoided` as the witness for #171
(this added `import EM.Population.SeedCapture` to the registry's import surface).

**Target going spare — the Coupling Lemma** (~15 lines, `EM/Population/SeedCapture.lean`). Verified
absent from the repo; only the unrelated `LemmaDBox.genSeqAvoid_eq_iff` greps nearby.

> If `q` is prime, `m ≥ 2`, and `genSeq m j ≠ q` for all `j < n`, then `genProdAvoid q m j =
> genProd m j` and `genSeqAvoid q m j = genSeq m j` for all `j < n`.

Proof: induction on `k`. With `P = genProd m k`, `N = P+1 ≥ 3`, `p = minFac N = genSeq m k ≠ q`:
`p` prime, `p ∣ N`, `p ≠ q`, so `prime_dvd_qfreePart_iff` gives `p ∣ qfreePart q N`, whence
`(qfreePart q N).minFac ≤ p`. Conversely `qfreePart q N ≥ 2` (else `N` is a power of `q`, forcing
`minFac N = q`), so `(qfreePart q N).minFac` is a prime dividing `N` via `qfreePart_dvd`, hence
`≥ minFac N = p`. Equality; accumulators agree at `k+1`.

Useful corollary to state: if `q` is missed by the whole orbit, the `q`-free reference dynamics **is**
the true dynamics. This is hygiene for anyone reasoning about `genSeqAvoid` — it is *not* a step toward
MC, and must not be advertised as one.

**Do not** attempt to derive anything about the missed set of a single orbit from
`LargeStepRoughness`. See #169–#174.
