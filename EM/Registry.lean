import CA
import EM.MasterReduction
import EM.AlladiDensity
import EM.SieveConstraint
import EM.IntegerDiophantine
import EM.FiberAutonomy
import EM.SubstitutionPrinciple
import EM.SelfCorrectingDrift
import EM.TailWindowDecorrelation
import EM.TailIdentityAttack
import EM.CRTPointwiseTransfer
import EM.IKCh7Hilbert
import EM.EnsemblePT
import EM.AdelicEquidist

/-!
# EM Registry: Content-Addressed Publication Annotations

Retroactive `@[publish]` and `@[open_point]` annotations for the EM project's
key results and open hypotheses, using the CA content-addressing framework.

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

/-! ### Character sum chain -/

attribute [publish] cme_implies_ccsb

/-! ### Sequence foundations -/

attribute [publish] Mullin.seq_isPrime
attribute [publish] Mullin.seq_injective
attribute [publish] prod_squarefree

/-! ### Walk-divisibility bridge -/

attribute [publish] MullinGroup.walkZ_eq_neg_one_iff

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
