import CA
import EM.Reduction.Master
import EM.CME.Equivalences
import EM.Population.HeadDomination
import EM.Population.SeededGrowth
import EM.Population.BagConditionedLaw
import EM.Population.GrowthDensity
import EM.Population.SizeResidueDecoupling
import EM.Population.RelativeSize
import EM.Ensemble.UncenteredRefutations
import EM.Transfer.SieveConstraint
import EM.Transfer.IntegerDioph
import EM.Ensemble.FiberAutonomy
import EM.Transfer.Substitution
import EM.Reduction.SelfCorrecting
import EM.Reduction.TailWindow
import EM.Reduction.TailIdentity
import EM.Transfer.CRTPointwise
import EM.IK.Ch7Hilbert
import EM.IK.Ch7CesaroChain
import EM.Ensemble.PT
import EM.Ensemble.WeylChain
import EM.Adelic.Equidist
import EM.Adelic.UniformConductor
-- New imports for complete registry coverage
import EM.LargeSieve.WalkAnalysis
import EM.CME.FiberAnalysis
import EM.Group.Core
import EM.Equidist.FourierB
import EM.Equidist.SelfCorrecting
import EM.Reduction.DSLInfra
import EM.Population.ReciprocalSum
import EM.Ensemble.FirstMoment
import EM.Ensemble.MinFacShifted
import EM.Meta.OrbitBarrier
import EM.Meta.BagInformation
import EM.Obstruction.Fragment
import EM.Reciprocity.NoReciprocityInvariant
import EM.Equidist.OneHorizon
import EM.Equidist.WeakHitting
import EM.Ensemble.CRT
import EM.LargeSieve.Spectral
import EM.LargeSieve.Analytic
import EM.LargeSieve.PrimeArithLS
import EM.Adelic.Profinite
import EM.Adelic.ProfiniteGeneration
import EM.Stochastic.VanishingNoiseVariantB
import EM.Stochastic.VanishingNoiseVariantC
import EM.Stochastic.NonFaithfulCharacterEscape
import EM.Stochastic.RandomTwoPointMCB
import EM.Stochastic.MixedWalk
import EM.Stochastic.MixedMC
import EM.Stochastic.PerpetualPrimality
import EM.Population.ArborealTower
import EM.Population.BackwardLevels
import EM.Population.BackwardOrbit
import EM.Population.CompositeFloor
import EM.Population.DefectTelescope
import EM.Population.SylvesterTower
import EM.Obstruction.RuleTransition
import EM.Obstruction.Anatomy
import EM.Stochastic.ReachableSets
import EM.Stochastic.RandomFactorMC
import EM.Ensemble.MixedEnsemble
import EM.Ensemble.UnconditionalPSCD
import EM.Stochastic.PositiveProbCapture
import EM.Stochastic.TreeSieveDecay
import EM.Stochastic.GeometricCapture
import EM.FunctionField.Bootstrap
import EM.FunctionField.SubgroupEscape
import EM.Group.CyclicWalkCoverage
import EM.FunctionField.Analog
import EM.FunctionField.DegreeTelescope
import EM.FunctionField.FactorTree
import EM.FunctionField.PopulationEquidist
import EM.FunctionField.Finiteness
import EM.FunctionField.StochasticMC
import EM.Stochastic.FactorDiversity
import EM.Stochastic.StochasticEM
import EM.FunctionField.AutonomousMap
import EM.FunctionField.NecklaceFormula
import EM.FunctionField.FFSieve
import EM.FunctionField.DensityMC
import EM.FunctionField.StableTower
import EM.Stochastic.MissedPrimes
import EM.Population.AvoidanceTube
import EM.Population.InfiniteM
import EM.Population.SpectralConspiracy
import EM.LargeSieve.Basic
import EM.Equidist.SieveTransfer

/-!
# EM Registry: Content-Addressed Publication Annotations

Retroactive `@[publish]` and `@[open_point]` annotations for the EM project's
key results and open hypotheses, using the CA content-addressing framework.

The registry covers the declarations tagged here with `@[publish]` or
`@[open_point]` — a curated selection of headline results and live
hypotheses — not every result proved in the repository.

## Organization

- **Open points**: Mathematical statements published without proof (the live targets)
- **Published results**: Proved theorems of independent mathematical interest
-/

-- ============================================================================
-- Open points: unproved mathematical hypotheses
-- ============================================================================

/-! ### The master gap -/

-- DeterministicStabilityLemma (PE → CME) RETIRED 2026-08-17: PE is false (Dead End #160), so
-- DSL is vacuous; archived in EM/Archive/Population/PopulationEquidistArchive.lean.  The
-- master gap is `ConditionalMultiplierEquidist` below.
attribute [open_point] Mullin.MullinConjecture

/-! ### Core dynamical hypotheses -/

attribute [open_point] DynamicalHitting
attribute [open_point] SingleHitHypothesis
-- DSLHitting RETIRED (vacuous, Dead End #160; archived)
attribute [open_point] Mullin.HittingHypothesis

/-! ### Character sum hypotheses -/

attribute [open_point] ConditionalMultiplierEquidist
-- 2026-08-18 review: every missing-prime hypothesis is EQUIVALENT to MC (MC ⇒ it vacuously).
-- CME/CCSB/DH/SHH/HH/WFG are reformulations of MC in the language of the walk, not strictly
-- weaker sufficient conditions.  On record in EM/CME/Equivalences.lean.
attribute [publish] cme_iff_mc
attribute [publish] ccsb_iff_mc
attribute [publish] dh_iff_mc
attribute [publish] shh_iff_mc
attribute [publish] hh_iff_mc
attribute [publish] walkEquidist_iff_mc
attribute [publish] wfg_iff_mc
attribute [publish] walk_layer_equivalences
attribute [open_point] ComplexCharSumBound
attribute [open_point] DecorrelationHypothesis
attribute [open_point] MultiModularCSB
-- SubstitutionPrinciple RETIRED as a separate open point 2026-08-17 (collapse audit): it is CME
-- by definition (`sp_eq_cme`).

/-! ### Equidistribution hypotheses -/

-- PopulationEquidist / PopulationTransfer RETIRED (PE is FALSE, Dead End #160; archived)
attribute [open_point] VisitEquidistribution

/-! ### Drift and self-correcting hypotheses -/

attribute [open_point] SelfCorrectingDrift
-- TailWindowDecorrelation RETIRED 2026-08-17: FALSE at χ ≡ 1 (`not_tailWindowDecorrelation`, #156)

/-! ### Ensemble and variance hypotheses -/

-- StepDecorrelation RETIRED 2026-08-17: FALSE at χ ≡ 1 (`not_stepDecorrelation`, #156)
attribute [open_point] EnsembleConcentration

/-! ### Four-point hypotheses -/

-- FourPointPCV RETIRED 2026-08-17: FALSE at χ ≡ 1 (`not_fourPointPCV`, #156)

/-! ### Bridge hypotheses -/

-- CRTPointwiseTransferBridge RETIRED 2026-08-17 (collapse audit): its input PCE is a `True`
-- placeholder, so the bridge IS CME (`crtPointwiseTransferBridge_iff_cme`).
-- TWDImpliesCCSB RETIRED 2026-08-17: vacuous (`twdImpliesCCSB_vacuous`)

/-! ### ANT hypotheses -/

-- IK.WeightedPNTinAP RETIRED as an open point 2026-08-18 (review): it is a KNOWN THEOREM (IK
-- 2.30 / Mertens in APs), not an open problem of this project; its asymptotic form is proved
-- (`IK.weightedPNTinAP_asymp_proved`).  "Open point" means "hypothesis of the reduction network
-- whose truth is unknown", which this is not.
-- PrimesEquidistImpliesRoughLPF / RoughLPFImpliesMFRE RETIRED (Dead End #160: endpoints
-- RoughLPFEquidist / MFRE are false; archived in EM/Archive/Population/AlladiDensityArchive.lean)
-- Asymptotic (rate-free) entry point: the `O(1)` error of IK (2.30) is not load-bearing
-- (`asymptotic_entry_point_status`).  `IK.WeightedPNTinAPAsymp` is now a THEOREM
-- (`IK.weightedPNTinAP_asymp_proved`, Karamata + `L(1,χ) ≠ 0`, EM/IK/Karamata.lean).
-- Dead End #160 (EM/Population/HeadDomination.lean): the endpoints RoughLPFEquidist / MFRE /
-- PE are FALSE (head domination), so `PrimesEquidistAsympImpliesRoughLPF` is equivalent to a
-- false family of series identities (`primesEquidistAsympImpliesRoughLPF_iff`) and
-- `RoughLPFImpliesMFRE` is vacuous.  Both stay registered only so the equivalence can be
-- referenced; neither is a target.  Likewise `PopulationEquidist`, `PopulationTransfer`,
-- `DeterministicStabilityLemma`, `DSLHitting` are false / vacuous.
-- PrimesEquidistAsympImpliesRoughLPF RETIRED as an open point 2026-08-18 (review): it is
-- documented as a false family of identities; the equivalence is published instead.

/-! ### Conductor equidistribution hypotheses -/

-- UniformConductorEquidist / UCEImpliesCME RETIRED 2026-08-17 (Dead End #160): UCE at
-- conductor M = 1 is RoughLPFEquidist, which is false (`uce_implies_roughLPFEquidist`), so
-- UCE is false and UCEImpliesCME vacuous.  Kept as definitions, no longer targets.

/-! ### Variant open hypotheses -/

-- BVImpliesMMCSB RETIRED as an open point 2026-08-18 (review): the previous body of
-- `BombieriVinogradov` was trivially true (∃ E ≤ x/(log x)^A ∧ 0 ≤ E), so this "frontier" was
-- literally `MultiModularCSB`; BV/EH are now stated faithfully (ψ-form) but the BV route is a
-- dead end (#54, #96, #61, #75) and is not a live target.
-- SieveTransfer RETIRED 2026-08-17 (Dead End #160): its hypothesis GenericLPFEquidist is FALSE
-- (small-prime domination, `not_genericLPFEquidist`), so it holds vacuously
-- (`sieveTransfer_vacuous`).
-- LinearMeanGrowth open_point deleted (RED #8)
-- EnsembleTransitionApprox open_point deleted (RED #10)
-- NonFaithfulCharacterEscape : (q : ℕ) → [Fact (Nat.Prime q)] → Prop (not bare Prop, skip)
attribute [open_point] MixedDiversity
attribute [open_point] MixedDiversityWeak
attribute [open_point] MixedHitting
attribute [open_point] UFDStrongImpliesMixedMC
-- FactorEscapeHypothesis : ℕ → Prop (not bare Prop, skip)

-- ============================================================================
-- Published results: proved theorems
-- ============================================================================

/-! ### Master reduction chains -/

attribute [publish] cme_implies_mc
attribute [publish] complex_csb_mc'
attribute [publish] dynamical_hitting_implies_mullin
attribute [publish] Mullin.hh_implies_mullin
attribute [publish] single_hit_implies_mc
attribute [publish] walk_equidist_mc
attribute [publish] MullinGroup.se_mixing_implies_mullin
attribute [publish] mmcsb_implies_mc
attribute [publish] sve_implies_mc
attribute [publish] scd_implies_mc
attribute [publish] cancel_weyl_implies_mc
attribute [publish] vcb_ped_implies_mc

/-! ### Character sum chain -/

attribute [publish] cme_implies_ccsb
attribute [publish] cme_implies_vcb
attribute [publish] decorrelation_implies_ped
attribute [publish] feb_implies_cme
attribute [publish] char_sum_energy_eq_N_plus_cross
attribute [publish] shifted_walk_eq_mult_mul_cof

/-! ### Sequence foundations -/

attribute [publish] Mullin.seq_isPrime
attribute [publish] Mullin.seq_injective
attribute [publish] prod_squarefree

/-! ### Walk-divisibility bridge and dynamics -/

attribute [publish] MullinGroup.walkZ_eq_neg_one_iff
attribute [publish] MullinGroup.confinement_forward
attribute [publish] walk_hit_count_fourier_step
attribute [publish] walk_telescope_identity
attribute [publish] walk_shift_one_correlation

/-! ### CRT structural decorrelation -/

attribute [publish] MullinCRT.crt_multiplier_invariance
-- Finite-set form (Session 307): the multiplier is blind not to one coordinate but to
-- ANY finite death-free set of coordinates.  The strongest proved form of "the new
-- multiplier forgets the accumulator".
attribute [publish] MullinCRT.crt_multiplier_invariance_finset

/-! ### Algebraic framework -/

attribute [publish] prime_residue_escape

/-! ### Ensemble generalization -/

attribute [publish] genSeq_injective
attribute [publish] genProd_two_eq_prod
attribute [publish] genProd_restart
attribute [publish] start_dvd_genProd

/-! ### Integer-level T-iteration -/

attribute [publish] emIterationT_iterate_eq

/-! ### Sieve constraint infrastructure -/

attribute [publish] emSupport_card
attribute [publish] prod_succ_mod_emSupport
attribute [publish] emSupport_ssubset

/-! ### Fiber autonomy -/

attribute [publish] crt_fiber_determines_genSeq
attribute [publish] crt_fiber_propagates

/-! ### ANT chain -/

attribute [publish] IK.wpnt_implies_primes_equidist_proved
attribute [publish] IK.prime_power_stripping_proved
-- Shared, error-shape-agnostic content of the two chain steps
attribute [publish] IK.prime_sum_sub_vonMangoldt_sum_le
-- The asymptotic chain: both steps survive the weakening from `O(1)` to `o(main term)`
attribute [publish] IK.prime_power_stripping_asymp_proved
attribute [publish] IK.prime_log_to_reciprocal_asymp_proved
attribute [publish] IK.wpnt_asymp_implies_primes_equidist_asymp
attribute [publish] IK.weightedPNTinAP_asymp_of_weightedPNTinAP
attribute [publish] IK.primesEquidistInAP_asymp_of_primesEquidistInAP
-- (primesEquidistImpliesRoughLPF_of_asymp, wpnt_asymp_to_mfre, asymptotic_entry_point_status
--  archived with AlladiDensity.lean, Dead End #160)
-- Karamata's Tauberian theorem and the unconditional ANT entry point (EM/IK/Karamata.lean)
attribute [publish] IK.Karamata.karamata
attribute [publish] IK.Karamata.tendsto_psum_exp
attribute [publish] IK.Karamata.tendsto_poly
attribute [publish] IK.Karamata.exists_sandwich
attribute [publish] IK.wcoef_tendsto
attribute [publish] IK.weightedPNTinAP_asymp_proved
attribute [publish] IK.primesEquidistInAP_asymp_proved
-- (mfre_of_alladi_links, alladi_dsl_implies_mc, alladi_dsl_hitting_implies_mc,
--  ant_entry_point_unconditional archived with AlladiDensity.lean, Dead End #160)
attribute [publish] uce_implies_roughLPFEquidist
attribute [publish] not_genericLPFEquidist
-- Dead Ends #156/#157 witnessed (EM/Ensemble/UncenteredRefutations.lean)
attribute [publish] UncenteredRefutations.not_stepDecorrelation
attribute [publish] UncenteredRefutations.not_fourPointPCV
attribute [publish] UncenteredRefutations.not_tailWindowDecorrelation
attribute [publish] UncenteredRefutations.not_charSumVarianceBound
attribute [publish] UncenteredRefutations.not_ensembleCharSumConcentration
attribute [publish] UncenteredRefutations.not_secondMomentSquaredBound
attribute [publish] UncenteredRefutations.not_ensembleMultiplierEquidist
attribute [publish] UncenteredRefutations.twdImpliesCCSB_vacuous
attribute [publish] crtPointwiseTransferBridge_iff_cme
attribute [publish] sieveTransfer_vacuous
-- Dead End #160: head domination (EM/Population/HeadDomination.lean)
attribute [publish] HeadDomination.card_minFac_eq_ge
attribute [publish] HeadDomination.card_minFac_eq_le
attribute [publish] HeadDomination.w_eq_cfun_sub
attribute [publish] HeadDomination.cfun_tendsto_zero
attribute [publish] HeadDomination.hasSum_wq
attribute [publish] HeadDomination.tendsto_roughCount_div
attribute [publish] HeadDomination.tendsto_classCount_div
attribute [publish] HeadDomination.roughLPFEquidist_iff
attribute [publish] HeadDomination.primesEquidistAsympImpliesRoughLPF_iff
attribute [publish] HeadDomination.not_roughLPFEquidist_of_head
attribute [publish] HeadDomination.sum_tsum_wcls
-- Pass 4 (2026-08-17): the seeded growth constant (EM/Population/SeededGrowth.lean)
attribute [publish] SeededGrowth.sgrowth_T
attribute [publish] SeededGrowth.sgrowth_iterate
attribute [publish] SeededGrowth.seedInfinitelyManyComposite_iff_sgrowth_eq_zero
attribute [publish] SeededGrowth.sgrowth_two
attribute [publish] SeededGrowth.mixedDiversity_iff_sgrowth_zero
-- unpublished 2026-08-18 (review): `SeededGrowth.seeded_growth_landscape` is a conjunction of already-published facts (documentation, not content)
-- Pass 4 (2026-08-17): the bag-conditioned multiplier law (EM/Population/BagConditionedLaw.lean)
attribute [publish] BagConditionedLaw.card_coprime_affine_block
attribute [publish] BagConditionedLaw.minFac_eq_iff_on_ap
attribute [publish] BagConditionedLaw.tendsto_bagClass_div_ap
attribute [publish] BagConditionedLaw.bagWeight_least_missing
attribute [publish] BagConditionedLaw.tendsto_least_missing_div_ap
-- 2026-08-18: the growth projection, measured (EM/Population/GrowthDensity.lean)
attribute [publish] GrowthDensity.hasDensityZero_prime
attribute [publish] GrowthDensity.hasDensityZero_comp_T
attribute [publish] GrowthDensity.hasDensityZero_genProd_prime
attribute [publish] GrowthDensity.hasDensityZero_perpetual
-- unpublished 2026-08-18 (review): `GrowthDensity.growth_density_landscape` is a conjunction of already-published facts (documentation, not content)
-- 2026-08-18: the joint object (EM/Population/SizeResidueDecoupling.lean)
attribute [publish] SizeResidueDecoupling.multiplier_residue_of_prime_stage
attribute [publish] SizeResidueDecoupling.exists_seed_composite_residue_size
-- unpublished 2026-08-18 (review): `SizeResidueDecoupling.size_residue_landscape` is a conjunction of already-published facts (documentation, not content)
-- 2026-08-18: the relative-size invariant (EM/Population/RelativeSize.lean)
attribute [publish] RelativeSize.rho_T
attribute [publish] RelativeSize.rho_dichotomy
attribute [publish] RelativeSize.sgrowth_pos_iff_rho_eq_one
attribute [publish] RelativeSize.sgrowth_eq_zero_iff_rho_le_half
attribute [publish] RelativeSize.rho_eq_zero_of_seedRD
attribute [publish] RelativeSize.rho_two_eq_zero_of_rd
attribute [publish] RelativeSize.rho_two_le_half_iff
-- unpublished 2026-08-18 (review): `RelativeSize.relative_size_landscape` is a conjunction of already-published facts (documentation, not content)
/-! ### Large sieve chain -/

attribute [publish] IK.mittag_leffler_csc_proved
attribute [publish] IK.cross_r_cesaro_convergence_proved

/-! ### Lyapunov and visit dynamics -/

attribute [publish] lyapunov_one_step
attribute [publish] lyapunov_telescope
attribute [publish] excessEnergy_eq_visit_deviation

/-! ### Adelic decomposition -/

attribute [publish] mwi_mme_implies_cme
attribute [publish] adelic_implies_mc
attribute [publish] cme_implies_mwi
attribute [publish] all_routes_to_mc_adelic
attribute [publish] cme_iff_adelic
attribute [publish] crt_fiber_mme_implies_cme
attribute [publish] uniform_profinite_implies_mc
attribute [publish] primeUnitsBelow_generate
attribute [publish] mc_implies_full_generation

/-! ### Conductor equidistribution -/

attribute [publish] uce_cme_implies_mc
attribute [publish] prod_coprime_of_not_in_seq
-- unpublished 2026-08-18 (review): `uce_landscape` is a conjunction of already-published facts (documentation, not content)
/-! ### Ensemble / DSL framework -/

attribute [publish] sd_implies_cancellation
attribute [publish] weyl_hitting_bridge_proved
-- lmg_implies_positive_density_rsd archived to EM/Archive/Meta/RegistryArchive.lean (RED #8)
attribute [publish] genSeq_ge_three
attribute [publish] ensembleAvg_k0_ge_quarter
attribute [publish] ensembleAvg_ge_death_density
attribute [publish] death_then_never_death_again
-- eta_sre_implies_prsd archived to EM/Archive/Meta/RegistryArchive.lean (RED #10)

/-! ### Spectral and large sieve routes -/

attribute [publish] van_der_corput_bound
attribute [publish] hod_implies_ccsb
attribute [publish] weak_als_from_card_bound
attribute [publish] als_implies_prime_arith_ls

/-! ### Variant frameworks -/

attribute [publish] variant_mc_from_ufd_strong_proved
attribute [publish] faithful_character_escape
attribute [publish] variant_mc_three_unconditional
attribute [publish] nonFaithfulCharSeparation_of_two_prime_factors
attribute [publish] quotientChar_faithful
attribute [publish] tca_path_survival_implies_random_mc_proved
attribute [publish] mixed_diversity_weak_implies_mixed_mc
attribute [publish] mixed_capture_three
attribute [publish] mixed_hitting_diversity_implies_mc
attribute [publish] embed_walk_agreement
attribute [publish] hit_implies_capture'
attribute [publish] mixed_hitting_iff_neg_one_reachable
attribute [publish] perpetual_prime_excludes_mod3_one
attribute [publish] reachableAt_from_factor
attribute [publish] reachable_composite_branch
attribute [publish] reachableEver_not_in_coset
attribute [publish] factor_confinement
attribute [publish] factor_escape_implies_mixed_mc_at
attribute [publish] pure_random_mc_iff_mixed_mc
attribute [publish] standard_mc_implies_pure_random
attribute [publish] pscd_implies_almost_all_mixed_hitting
attribute [publish] trapped_le_sum_confined
attribute [publish] zero_not_reachable_of_coprime_trapped
-- peap_chain_implies_almost_all_mixed_hitting archived to
-- EM/Archive/Ensemble/MixedEnsembleArchive.lean (superseded by weak-FMCD chain;
-- see weak_fmcd_chain_implies_pscd below)
attribute [publish] tsd_all_implies_mixed_mc
-- unpublished 2026-08-18 (review): `coset_ambiguity_landscape` is a conjunction of already-published facts (documentation, not content)
attribute [publish] product_failure_tendsto_zero
attribute [publish] tsd_positive_capture
attribute [publish] perpetual_prime_eventually_periodic
attribute [publish] perpetual_prime_mod5_orbit
attribute [publish] reachableEver_mono_along_walk
attribute [publish] perpetual_primality_multi_exclusion

/-! ### Function field analog -/

attribute [publish] FunctionFieldAnalog.ff_dh_implies_ffmc
attribute [publish] FunctionFieldAnalog.weil_implies_ff_se
attribute [publish] alternating_walk_misses_two
attribute [publish] FunctionFieldAnalog.ff_cyclotomic_dead_end
attribute [publish] FunctionFieldAnalog.ffMixedSel_injective
attribute [publish] FunctionFieldAnalog.ffMixedWalkProd_coprime_succ
attribute [publish] FunctionFieldAnalog.start_not_capturable
attribute [publish] FunctionFieldAnalog.ff_factor_pool_degree_grows
attribute [publish] FunctionFieldAnalog.ffFiniteIrreduciblesPerDegree_proved
attribute [publish] FunctionFieldAnalog.ff_dh_implies_ffmc_unconditional
attribute [publish] FunctionFieldAnalog.stochastic_mc_unconditional
attribute [publish] FunctionFieldAnalog.ff_phase_transition_unconditional
attribute [publish] factor_diversity_spectral_contraction
attribute [publish] diverse_steps_imply_vanishing
attribute [publish] stochastic_mc_of_tsd
-- unpublished 2026-08-18 (review): `phase_transition_summary` is a conjunction of already-published facts (documentation, not content)
attribute [publish] FunctionFieldAnalog.ff_neg_one_unreachable
attribute [publish] FunctionFieldAnalog.necklace_identity_proved
attribute [publish] FunctionFieldAnalog.ff_almost_all_unconditional
-- 2026-09-02: the function-field conjecture is FALSE over 𝔽_5[t] (stable Sylvester tower)
attribute [publish] FunctionFieldAnalog.StableTower.g_irreducible
attribute [publish] FunctionFieldAnalog.StableTower.tower_euclid_irreducible
attribute [publish] FunctionFieldAnalog.not_ffMullinConjecture_five

/-! ### Avoidance tube and spectral conspiracy -/

attribute [publish] tube_collapse
attribute [publish] shielding_lemma
attribute [publish] rogue_character_exists
attribute [publish] sve_contradicts_avoidance
attribute [publish] not_wm_implies_missing_infinite
-- unpublished 2026-08-18 (review): `spectral_conspiracy_landscape` is a conjunction of already-published facts (documentation, not content)
/-! ### Superseded hypotheses -/

-- SieveUpperBound : ℕ → Prop (not bare Prop, skip)

/-! ### Sieve chain (proved) -/

attribute [publish] weak_fmcd_chain_implies_pscd
attribute [publish] peap_implies_fcd_proved
-- sieve_product_vanishing_proved archived to
-- EM/Archive/Ensemble/MixedEnsembleArchive.lean (superseded by weak-FMCD chain)
attribute [publish] sqfreeCount_ge_quarter_real

/-! ### Unconditional Dirichlet density chain (proved; supersedes the PEAP hypothesis
for the PSCD chain) -/

attribute [publish] IK.DirichletDensity.prime_reciprocal_class_divergent
-- Density form (Session 307): the ratio, not just the divergence.  `1/φ(q)` per
-- invertible class, `|A|/φ(q)` for a Finset of them.  Dirichlet density, NOT natural
-- density (that needs PNT in APs = the open `IK.WeightedPNTinAP`).
attribute [publish] IK.DirichletDensity.tendsto_classPrimeSum_div_unitPrimeSum
attribute [publish] IK.DirichletDensity.tendsto_setPrimeSum_div_unitPrimeSum
-- Modulus-free denominator (Part 10): needed to compare densities across moduli.
attribute [publish] IK.DirichletDensity.tendsto_classPrimeSum_div_primeZetaSum
attribute [publish] IK.DirichletDensity.tendsto_setPrimeSum_div_primeZetaSum
-- First multiplier of the correct-parity ω = 2 ensemble (Session 307): the density of
-- `minFac (2p+1) = 3` is exactly 1/2, so equidistribution fails at the correct parity
-- too — not by the parity artifact of Dead End #157 but by small-prime domination.
attribute [publish] MinFacShifted.minFac_two_mul_add_one_eq_three_iff
attribute [publish] MinFacShifted.tendsto_minFacThree_density
attribute [publish] MinFacShifted.first_multiplier_not_equidistributed
-- The orbit-specificity barrier, witnessed (Session 307): Dead Ends #90 and #117 —
-- the two entries carrying the "why MC is hard" thesis — plus the integer analogue of
-- the function-field `orbit_barrier_thesis`.
attribute [publish] OrbitBarrier.population_does_not_determine_hitting
attribute [publish] OrbitBarrier.mult_cancel_not_walk_cancel
attribute [publish] OrbitBarrier.integer_orbit_barrier_thesis
-- The proof-theoretic dichotomy (Session 298) and its Session-307 widening.  These are
-- unconditional theorems *about* MC: within the congruence-invariant proof genre,
-- provability of avoidance decides membership — and that survives letting the invariant
-- depend on the step index and letting the proof assume the candidate is as large as the
-- Euclid number itself.
attribute [publish] Obstruction.proof_theoretic_dichotomy
attribute [publish] Obstruction.no_graded_induction_proof
attribute [publish] Obstruction.graded_provability_iff
-- The omega guard is free too: a proof may assume the candidate has as many prime
-- factors as the Euclid number actually has, and the fragment is still empty.  So the
-- surviving axis of anatomy is smoothness / largest prime factor, not omega.
attribute [publish] Obstruction.no_omega_graded_induction_proof
attribute [publish] Obstruction.omega_graded_provability_iff
-- The smoothness axis, closed from the other side: the Euclid numbers are eventually
-- y-rough for every y, so a smoothness guard excludes the orbit's own candidates.
attribute [publish] CvdP.eventually_rough
attribute [publish] CvdP.smooth_guard_inadmissible
attribute [publish] Obstruction.fragment_analysis_complete
-- The smoothness axis closes outright (Session 307): even a GROWING guard leaves the
-- fragment empty.  Candidates are chosen at a recurrent residue before the stage is
-- chosen, and eventually_rough then forces the guard above their largest prime factor.
attribute [publish] Obstruction.no_smooth_graded_induction_proof
attribute [publish] Obstruction.guard_analysis_complete
-- What the bag determines about the next prime (Session 307): three senses in which it
-- determines nothing, two in which it does (exclusion, roughness at a missing prime), and
-- the non-uniformity clause that blocks reading the first three as "uniformly random".
-- unpublished 2026-08-18 (review): `BagInformation.bag_information_landscape` is a conjunction of already-published facts (documentation, not content)
-- The reciprocity frontier (Session 307): the EXTENDS verdict of
-- docs/analysis/reciprocity_invariants.md, proved.  By (R1) a reciprocity invariant is a
-- congruence invariant at the growing symbol modulus, and the fragment is still empty.
attribute [publish] Reciprocity.no_reciprocity_induction_proof
attribute [publish] Reciprocity.reciprocity_provability_iff
-- The one-horizon Fourier criterion (Session 307): a single finite horizon per prime
-- suffices, giving the quantitative "cover within O(q^2) steps" reading of CCSB.
attribute [publish] OneHorizon.covers_of_charSum_lt
attribute [publish] OneHorizon.windowFourierGain_implies_mc
attribute [open_point] OneHorizon.WindowFourierGain
-- The weakest orbit target (Session 307): every odd prime divides SOME Euclid number.
-- Keeps the minFac accumulator (slow growth, many trials) but drops the selection
-- requirement.  HH => MC => (V) => reachable in the factor tree.
attribute [open_point] WeakHitting.EveryPrimeDividesEuclid
attribute [open_point] WeakHitting.OneWindowGain
attribute [publish] WeakHitting.mullin_implies_everyPrimeDividesEuclid
attribute [publish] WeakHitting.oneWindowGain_implies_V
attribute [publish] WeakHitting.weak_hitting_ladder
attribute [publish] fcd_unconditional
attribute [publish] pscd_unconditional
attribute [publish] almost_all_mixed_hitting_unconditional

/-! ### FF genuine density chain (conditional on the Kornblum divergence
hypothesis `FFDirichletDensity`, which replaces the counting proxies of
`FFSieve.lean`) -/

-- FFDirichletDensity : (p : ℕ) → [Fact p.Prime] → Prop (not bare Prop, skip open_point)
attribute [publish] FunctionFieldAnalog.ffMonicDeg_residue_card
attribute [publish] FunctionFieldAnalog.ffSqfreeDegCount_quarter
attribute [publish] FunctionFieldAnalog.ff_density_pscd
attribute [publish] FunctionFieldAnalog.ff_almost_all_genmixed_density

/-! ### Stochastic variant: unconditional almost-all capture (Session 304) -/

attribute [publish] almost_all_positive_prob_capture_unconditional

/-! ### Diagonal strengthening: all small primes simultaneously (Session 305) -/

attribute [publish] almost_all_mixed_hitting_diagonal
attribute [publish] almost_all_positive_prob_capture_diagonal

/-! ### Missed-prime structure and q=3 cofinal opportunities (Session 306) -/

attribute [publish] missed_primes_forward_invariant
attribute [publish] good_child_exists
attribute [publish] three_notMem_missedPrimes
attribute [publish] three_cofinal_capture_opportunities
attribute [publish] three_positive_prob_capture_pointwise
attribute [publish] expected_missed_smallprimes_diagonal

/-! ### The composite floor under the smallness statements (Session 307)

Every weakening of MC that asserts the missing set is *small* — finiteness, convergence
of `∑ 1/q` over it, and MC itself — implies that infinitely many Euclid candidates are
composite.  That statement is open, so it is the floor of the whole family. -/

attribute [open_point] WeakMullin
attribute [open_point] ReciprocalDivergence
attribute [open_point] AutonomousBranch.InfinitelyManyComposite

attribute [publish] CompositeFloor.two_pow_le_prod
attribute [publish] CompositeFloor.summable_one_div_seq_of_perpetual
attribute [publish] CompositeFloor.infinitelyManyComposite_of_reciprocalDivergence
attribute [publish] CompositeFloor.infinitelyManyComposite_of_weakMullin
attribute [publish] CompositeFloor.sum_inv_primes_below_le_tsum
-- unpublished 2026-08-18 (review): `CompositeFloor.composite_floor_landscape` is a conjunction of already-published facts (documentation, not content)
/-! ### (C∞) identified as Sylvester-tower primality (Session 307) -/

attribute [publish] SylvesterTower.perpetualPrimality_iff_tower_prime
attribute [publish] SylvesterTower.infinitelyManyComposite_iff_tower_composite
attribute [publish] SylvesterTower.infinitelyManyComposite_of_everyPrimeDividesEuclid
-- unpublished 2026-08-18 (review): `SylvesterTower.sylvester_tower_landscape` is a conjunction of already-published facts (documentation, not content)
/-! ### The Cox--van der Poorten obstruction class, unified (Session 307)

One rule-parameterised transition system; the class is inhabited for `maxFac` at
`(5, 12)` and empty for `minFac` at every missing prime and every modulus. -/

attribute [publish] RuleTransition.exists_large_odd_of_representable
attribute [publish] RuleTransition.no_congruence_induction_proof_of_ne_zero
attribute [publish] RuleTransition.no_min_rule_obstruction
attribute [publish] RuleTransition.cvdp_dichotomy
-- unpublished 2026-08-18 (review): `RuleTransition.rule_transition_landscape` is a conjunction of already-published facts (documentation, not content)
/-! ### The anatomy axis (Session 307)

The min rule's selection condition is pure congruence data; the max rule's is decided by
no modulus; anatomy carried as invariant state is inert. -/

attribute [publish] Anatomy.minFac_eq_iff
attribute [publish] Anatomy.minFac_eq_congruence_determined
attribute [publish] Anatomy.maxFac_not_congruence_determined
attribute [publish] Anatomy.no_anatomy_induction_proof
-- unpublished 2026-08-18 (review): `Anatomy.anatomy_axis_landscape` is a conjunction of already-published facts (documentation, not content)
/-! ### The autonomous branch, refuted where the data reaches (Session 307) -/

attribute [publish] SylvesterTower.euclid_prime_at_six
attribute [publish] SylvesterTower.autonomous_step_at_six
attribute [publish] SylvesterTower.not_perpetualPrimality_of_le_seven
attribute [publish] SylvesterTower.exists_composite_beyond_seven

/-! ### Primality of a Euclid number is self-limiting (Session 307) -/

attribute [publish] CompositeFloor.sq_lt_prod_succ_of_prime
attribute [publish] CompositeFloor.two_pow_two_pow_primeEuclidCount_le_prod
attribute [publish] CompositeFloor.primeEuclidCount_le_log_log

/-! ### (C∞) as a growth statement (Session 307) -/

attribute [publish] CompositeFloor.le_compositeEuclidCount_add_log_log
attribute [publish] CompositeFloor.prod_add_one_le_three_pow
attribute [publish] CompositeFloor.infinitelyManyComposite_of_subtower_growth

/-! ### The floor sharpened to a growth statement (S) (Session 308) -/

attribute [publish] CompositeFloor.summable_one_div_seq_of_lower_bound
attribute [publish] CompositeFloor.exists_lt_of_reciprocalDivergence
attribute [publish] CompositeFloor.summable_one_div_seq_of_geometric
attribute [publish] CompositeFloor.exists_small_minFac_of_reciprocalDivergence
attribute [publish] CompositeFloor.exists_small_minFac_of_mullin
attribute [publish] CompositeFloor.infinitelyManyComposite_of_small_minFac
attribute [publish] CompositeFloor.infinitelyManyComposite_of_reciprocalDivergence_via_growth
-- unpublished 2026-08-18 (review): `CompositeFloor.growth_floor_landscape` is a conjunction of already-published facts (documentation, not content)
/-! ### The defect telescope: (C∞) as a growth constant (Session 308) -/

attribute [publish] DefectTelescope.logProd_succ_eq_two_mul_sub_defect
attribute [publish] DefectTelescope.neg_two_pow_le_defect
attribute [publish] DefectTelescope.normLog_eq_sub_sum
attribute [publish] DefectTelescope.tendsto_normLog
attribute [publish] DefectTelescope.growthConstant_nonneg
attribute [publish] DefectTelescope.subtower_growth_iff_growthConstant_eq_zero
attribute [publish] DefectTelescope.infinitelyManyComposite_of_growthConstant_eq_zero
attribute [publish] DefectTelescope.growthConstant_eq_zero_of_reciprocalDivergence
attribute [publish] DefectTelescope.tendsto_log_seq_div_logProd_of_pos
attribute [publish] DefectTelescope.defect_dichotomy
-- unpublished 2026-08-18 (review): `DefectTelescope.defect_landscape` is a conjunction of already-published facts (documentation, not content)
/-! ### The degree telescope over `𝔽_p[t]` (Session 308) -/

attribute [publish] FFDegreeTelescope.ffDeg_succ_add_ffDefect
attribute [publish] FFDegreeTelescope.ffDefect_eq_zero_iff
attribute [publish] FFDegreeTelescope.ffNormDeg_eq_sub_sum
attribute [publish] FFDegreeTelescope.ffNormDeg_antitone
attribute [publish] FFDegreeTelescope.tendsto_ffNormDeg
attribute [publish] FFDegreeTelescope.ffInfinitelyManyReducible_of_ffGrowthConstant_eq_zero
attribute [publish] FFDegreeTelescope.tendsto_ffDeg'_div_ffDeg_of_pos
attribute [publish] FFDegreeTelescope.ffDefect_dichotomy
-- unpublished 2026-08-18 (review): `FFDegreeTelescope.ff_degree_telescope_landscape` is a conjunction of already-published facts (documentation, not content)
/-! ### Trial division closes the growth reformulation (Session 309)

The growth constant turns out to be a *complete* invariant for (C∞): the branch on which
`log (seq (n+1)) / log (prod n) → 1` is not wider than perpetual primality, because a
least prime factor above the square root is the number itself. -/

attribute [publish] CompositeFloor.exists_le_compositeEuclidCount
attribute [publish] DefectTelescope.defect_gap
attribute [publish] DefectTelescope.normLogCorr_succ_le_of_not_prime
attribute [publish] DefectTelescope.logProd_le_pow_mul
attribute [publish] DefectTelescope.growthConstant_eq_zero_of_infinitelyManyComposite
attribute [publish] DefectTelescope.infinitelyManyComposite_iff_growthConstant_eq_zero
attribute [publish] DefectTelescope.growthConstant_pos_iff_perpetualPrimality
attribute [publish] FFDegreeTelescope.two_mul_ffDeg'_le_of_not_irreducible
attribute [publish] FFDegreeTelescope.ffDeg_le_pow_mul
attribute [publish] FFDegreeTelescope.ffInfinitelyManyReducible_iff_ffGrowthConstant_eq_zero
attribute [publish] FFDegreeTelescope.ffGrowthConstant_pos_iff_perpetual

/-! ### (C∞) as a hitting statement: the backward orbit of zero (Session 310)

`Φ₆(x) = x² - x + 1` reduces the Sylvester tower modulo `ℓ`, so (C∞) becomes a hitting
statement for `walkZ` against `PreZero ℓ`, the backward orbit of `0`.  Level 1 of that
target is exactly the classical death equation `Φ₃(w) = w² + w + 1 = 0`. -/

attribute [publish] BackwardOrbit.cast_tower
attribute [publish] BackwardOrbit.dvd_tower_iff
attribute [publish] BackwardOrbit.mem_preZero_of_phi6_mem
attribute [publish] BackwardOrbit.six_dvd_sub_one_of_phi6_root
attribute [publish] BackwardOrbit.walkZ_notMem_preZero_of_perpetual
attribute [publish] BackwardOrbit.backwardOrbitHitting_iff_infinitelyManyComposite
attribute [publish] BackwardOrbit.infinitelyManyComposite_of_small_backward_hit
attribute [publish] BackwardOrbit.phi6_add_one
attribute [publish] BackwardOrbit.phi3_ne_zero_of_perpetual
-- unpublished 2026-08-18 (review): `BackwardOrbit.backward_orbit_landscape` is a conjunction of already-published facts (documentation, not content)
/-! ### Raising the hit level past `Φ₃` (Session 311)

Translation by `1` conjugates the take-all walk `y ↦ y² + y` to `Φ₆`, so the preimage
levels of `0` are exactly the take-all death times.  Level one is the classical `Φ₃`
condition; level two exists whenever `13` is a quadratic non-residue, which quadratic
reciprocity turns into a congruence on `ℓ` of density `1/2`. -/

attribute [publish] BackwardLevels.phi6_add_one_eq
attribute [publish] BackwardLevels.iterate_phi6_add_one
attribute [publish] BackwardLevels.mem_preZero_iff_sylvWalk_reaches_neg_one
attribute [publish] BackwardLevels.death_level_unique
attribute [publish] BackwardLevels.six_dvd_sub_one_of_death
attribute [publish] BackwardLevels.sylvWalk_step_of_isSquare
attribute [publish] BackwardLevels.cube_root_pair_product_eq_thirteen
attribute [publish] BackwardLevels.exists_death_level_two
attribute [publish] BackwardLevels.isSquare_thirteen_iff
attribute [publish] BackwardLevels.psi_two_ne_zero_of_perpetual
attribute [publish] BackwardLevels.infinitelyManyComposite_of_sylvWalk_death
-- unpublished 2026-08-18 (review): `BackwardLevels.backward_levels_landscape` is a conjunction of already-published facts (documentation, not content)
/-! ### Level three, and the engine behind every level (Session 312)

The two `q`-preimages of a point have discriminants multiplying to `Δ(z) = -3 - 16z` — a
ring identity of which the level-two constant `13 = Δ(-1)` is the first instance.  Level
three follows by the same lift, with constant `Δ(ω)Δ(ω²) = 217`.  The tower is finite. -/

attribute [publish] BackwardLevels.sylvWalk_neg_one_sub
attribute [publish] BackwardLevels.preimage_pair_discriminant
attribute [publish] BackwardLevels.exists_death_level_add_two
attribute [publish] BackwardLevels.exists_death_level_three
attribute [publish] BackwardLevels.delta_pair_product_eq_217
attribute [publish] BackwardLevels.exists_death_level_three_of_split
attribute [publish] BackwardLevels.realizedLevels_finite
attribute [publish] BackwardLevels.not_isSquare_iff_jacobiSym
attribute [publish] BackwardLevels.not_isSquare_217_iff
attribute [publish] BackwardLevels.psi_three_ne_zero_of_perpetual

/-! ### The arboreal tower: witnesses are free, smallness is everything (Session 313)

The qualitative half of what Chebotarev would give — every level of the backward-orbit tree
is occupied at infinitely many primes — is *unconditional*, by the Euclid argument, because
every level polynomial has constant term `1`.  What remains is a size condition on one
specific integer's factorisation, which no density theorem supplies. -/

attribute [publish] ArborealTower.cast_sylvNat_iterate
attribute [publish] ArborealTower.dvd_sylvNat_iterate
attribute [publish] ArborealTower.sylvWalk_iterate_succ_eq_prod
attribute [publish] ArborealTower.coprime_level_values
attribute [publish] ArborealTower.exists_large_prime_level_occupied
attribute [publish] ArborealTower.levelPrimes_infinite
attribute [publish] ArborealTower.tower_eq_sylvNat
attribute [publish] ArborealTower.level_witness_iff
attribute [publish] ArborealTower.infinitelyManyComposite_iff_witness_proper
attribute [publish] ArborealTower.witness_eq_self_of_perpetual
attribute [publish] ArborealTower.minFac_level_injective
-- unpublished 2026-08-18 (review): `ArborealTower.arboreal_tower_landscape` is a conjunction of already-published facts (documentation, not content)
-- ============================================================================
-- Registry generation (runs during `lake build`)
-- ============================================================================

#ca_registry "registry/"
