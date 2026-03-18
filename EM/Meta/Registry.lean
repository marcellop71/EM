import CA
import EM.Reduction.Master
import EM.Population.AlladiDensity
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
import EM.Group.Core
import EM.Equidist.FourierB
import EM.Equidist.SelfCorrecting
import EM.Reduction.DSLInfra
import EM.Population.ReciprocalSum
import EM.Ensemble.FirstMoment
import EM.Ensemble.CRT
import EM.Ensemble.BackwardDynamics
import EM.LargeSieve.Spectral
import EM.LargeSieve.Analytic
import EM.LargeSieve.PrimeArithLS
import EM.Adelic.Profinite
import EM.Adelic.ProfiniteGeneration
import EM.Advanced.VanishingNoiseVariantB
import EM.Advanced.VanishingNoiseVariantC
import EM.Advanced.VanishingNoiseVariantD
import EM.Advanced.RandomTwoPointMCB
import EM.Advanced.EpsilonRandomMC
import EM.Advanced.RandomFactorMC
import EM.Ensemble.MixedEnsemble
import EM.Advanced.InterpolationMC
import EM.Probability.GeometricCapture
import EM.FunctionField.Bootstrap
import EM.FunctionField.SubgroupEscape
import EM.FunctionField.CyclicWalkCoverage
import EM.FunctionField.Analog
import EM.FunctionField.FactorTree
import EM.FunctionField.PopulationEquidist
import EM.FunctionField.Finiteness
import EM.FunctionField.StochasticMC
import EM.Advanced.FactorDiversity
import EM.Advanced.StochasticEM
import EM.FunctionField.AutonomousMap
import EM.FunctionField.NecklaceFormula
import EM.FunctionField.FFSieve
import EM.Population.AvoidanceTube
import EM.Population.InfiniteM
import EM.Population.SpectralConspiracy
import EM.LargeSieve.Basic
import EM.Equidist.SieveTransfer

/-!
# EM Registry: Content-Addressed Publication Annotations

Retroactive `@[publish]` and `@[open_point]` annotations for the EM project's
key results and open hypotheses, using the CA content-addressing framework.

Every declaration appearing in the paper's "Summary of Formally Verified Results"
table is registered here, ensuring each row receives an L1 type hash.

## Organization

- **Open points**: Mathematical statements published without proof (the live targets)
- **Published results**: Proved theorems of independent mathematical interest
-/

-- ============================================================================
-- Open points: unproved mathematical hypotheses
-- ============================================================================

/-! ### The master gap -/

attribute [open_point] DeterministicStabilityLemma
attribute [open_point] Mullin.MullinConjecture

/-! ### Core dynamical hypotheses -/

attribute [open_point] DynamicalHitting
attribute [open_point] SingleHitHypothesis
attribute [open_point] DSLHitting
attribute [open_point] Mullin.HittingHypothesis

/-! ### Character sum hypotheses -/

attribute [open_point] ConditionalMultiplierEquidist
attribute [open_point] ComplexCharSumBound
attribute [open_point] DecorrelationHypothesis
attribute [open_point] MultiModularCSB
attribute [open_point] SubstitutionPrinciple

/-! ### Equidistribution hypotheses -/

attribute [open_point] PopulationEquidist
attribute [open_point] PopulationTransfer
attribute [open_point] VisitEquidistribution

/-! ### Drift and self-correcting hypotheses -/

attribute [open_point] SelfCorrectingDrift
attribute [open_point] TailWindowDecorrelation

/-! ### Ensemble and variance hypotheses -/

attribute [open_point] StepDecorrelation
attribute [open_point] EnsembleConcentration

/-! ### Four-point hypotheses -/

attribute [open_point] FourPointPCV

/-! ### Bridge hypotheses -/

attribute [open_point] CRTPointwiseTransferBridge
attribute [open_point] TWDImpliesCCSB

/-! ### ANT hypotheses -/

attribute [open_point] IK.WeightedPNTinAP
attribute [open_point] PrimesEquidistImpliesRoughLPF
attribute [open_point] RoughLPFImpliesMFRE

/-! ### Conductor equidistribution hypotheses -/

attribute [open_point] UniformConductorEquidist
attribute [open_point] UCEImpliesCME

/-! ### Variant open hypotheses -/

attribute [open_point] BVImpliesMMCSB
attribute [open_point] SieveTransfer
attribute [open_point] LinearMeanGrowth
attribute [open_point] EnsembleTransitionApprox
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

attribute [publish] full_chain_dsl
attribute [publish] cme_implies_mc
attribute [publish] complex_csb_mc'
attribute [publish] dynamical_hitting_implies_mullin
attribute [publish] Mullin.hh_implies_mullin
attribute [publish] pe_dsl_implies_mc
attribute [publish] wpnt_dsl_implies_mc
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
attribute [publish] uce_landscape

/-! ### Ensemble / DSL framework -/

attribute [publish] sd_implies_cancellation
attribute [publish] weyl_hitting_bridge_proved
attribute [publish] lmg_implies_positive_density_rsd
attribute [publish] genSeq_ge_three
attribute [publish] ensembleAvg_k0_ge_quarter
attribute [publish] ensembleAvg_ge_death_density
attribute [publish] death_then_never_death_again
attribute [publish] eta_sre_implies_prsd

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
attribute [publish] peap_chain_implies_almost_all_mixed_hitting
attribute [publish] tsd_all_implies_mixed_mc
attribute [publish] coset_ambiguity_landscape
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
attribute [publish] phase_transition_summary
attribute [publish] FunctionFieldAnalog.ff_neg_one_unreachable
attribute [publish] FunctionFieldAnalog.necklace_identity_proved
attribute [publish] FunctionFieldAnalog.ff_almost_all_unconditional

/-! ### Avoidance tube and spectral conspiracy -/

attribute [publish] tube_collapse
attribute [publish] shielding_lemma
attribute [publish] rogue_character_exists
attribute [publish] sve_contradicts_avoidance
attribute [publish] not_wm_implies_missing_infinite
attribute [publish] spectral_conspiracy_landscape

/-! ### Superseded hypotheses -/

-- SieveUpperBound : ℕ → Prop (not bare Prop, skip)

/-! ### Sieve chain (proved) -/

attribute [publish] weak_fmcd_chain_implies_pscd
attribute [publish] peap_implies_fcd_proved
attribute [publish] sieve_product_vanishing_proved
attribute [publish] sqfreeCount_ge_quarter_real

-- ============================================================================
-- Registry generation (runs during `lake build`)
-- ============================================================================

#ca_registry "registry/"
