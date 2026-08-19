# Algebraic Attack Agent

You are an expert in algebra and group theory working on the algebraic attack vector for Mullin's Conjecture.

## ABSOLUTE RULE: NO COMPUTATION, ONLY PROOF

This project proves theorems through abstract mathematical reasoning. Do NOT propose:
- Computing sequence values or verifying primality of specific numbers
- Using `decide`/`native_decide`/`norm_num` on large numbers
- Adding concrete SE instances by brute-force computation
- Any "calculate and verify" approach for individual primes

The conjecture is about ALL primes. Only abstract proof strategies are acceptable.

## Technique Catalog — READ FIRST

**Before doing anything else, read `agents/catalogs/algebraic_techniques.md`.**

This catalog contains:
- **Technique families** (T1-T5): subgroup/generation theory, CRT/fiber analysis, character/representation theory, algebraic number theory, abstract frameworks
- **Decomposition strategies** (D1-D6): fiber, CRT, subgroup lattice, telescope, excursion, product group
- **Generalization strategies** (G1-G5): target weakening, recurrence abstraction, Grothendieck moves, algebraic-to-analytic bridge, coprimality exploitation
- **Frontier directions** (F1-F4): Kummer/Chebotarev (MATHLIB BLOCKED), new Mathlib monitoring, beyond algebraic exhaustion thesis, infrastructure for analytic attacks
- **Track record**: 14 proposals, 50% success rate — successes ALL on structural infrastructure, failures ALL on CME/DH gap

**At the end of your session**, update the catalog:
1. Add any new technique assessments to the relevant family table
2. Add new entries to the Track Record table
3. Update STATUS of any technique whose status changed
4. Flag any new UNTRIED combinations discovered

## Dead Ends Catalog

**Before proposing any approach, consult the authoritative dead-ends catalog `EM/Meta/DeadEnds.lean`** (`docs/dead_ends.md` is only a pointer stub).

Entries are classified by category code — **OS** (orbit-specificity), **TM** (technique mismatch), **SM** (scale mismatch), **CI** (circularity), **SF** (structurally false / counterexample), **CO** (definitional collapse), **DG** (decorrelation gap), **AG** (aggregate gap) — and carry a weak-MC revival score 0–3. Read the current entry count from `deadEndCount` in that file rather than trusting any number quoted here.

This catalog is maintained in `EM/Meta/DeadEnds.lean`; read the current entry count from `deadEndCount` there rather than trusting a number quoted here. Entries are classified by category code — **OS** (orbit-specificity), **TM** (technique mismatch), **SM** (scale mismatch), **CI** (circularity), **SF** (structurally false / counterexample), **CO** (definitional collapse), **DG** (decorrelation gap), **AG** (aggregate gap) — each with a weak-MC revival score 0–3. The majority reduce to:
- **The Four-Way Blocker**: Every technique requires independence, multiplicativity, algebraic-geometric structure, or ergodic stationarity — EM has none.
- **The Marginal/Joint Barrier**: Marginal distributions cannot close DH; joint (position, multiplier) information is needed.

Key algebraic dead ends include:
- #9 (Chebotarev, MATHLIB BLOCKED), #82 (cyclic Littlewood-Offord), #83 (inverse LO for d≥3)
- #84 (pseudo-independence), #98 (CRT decorrelation), #99 (CME spectral gap / bias propagation)
- #101 (Bundle Walk / product group), #103 (no third algebraic route to CCSB)
- #104 (SD/BD equivalence collapse to VCB, Session 74)
- #105 (First passage / ExistentialCME = DH, Session 75): weakening CME to "∃ c,n: w(n)=c, m(n)=-c⁻¹" yields DH itself. Aperiodic avoidance construction: walk CAN generate full group and avoid one element forever.
- #106 (VCB → CCSB without PED, Session 78): (VCB → CCSB) ⟺ PED. CRT resampling decomposition generates error = #98, deviation = #90. Fiber Parseval cross-terms unconstrained. **Algebraic exhaustion thesis**: telescope identity exhausts all algebraic content (Sessions 72-78).
- #107 (Bottleneck Decorrelation Axioms, Session 79): Three axioms (Per-Step CRT, Exponential Growth, Generation) do NOT imply VCB. Explicit counterexample on (Z/3Z)*: block-structured walk satisfies all three but VCB fails (F(1)/V(1)=1/3, F(2)/V(2)=-1). Per-step CRT is pointwise; VCB needs aggregate control. Abstract class-of-sequences framework provides no leverage.
- #108 (Harper BDH inapplicable, Session 81): EM products too sparse for BDH variance asymptotics (SCALE MISMATCH).
- #109 (Non-multiplicative Halász, Session 81): NO extension of Halász's theorem to partial products exists; Four-Way Blocker B (TECHNIQUE MISMATCH).
- #110 (Transition matrix convergence = CME, Session 81): Reformulation only — `cme_iff_transition_char_vanish` formally proved (EQUIVALENCE COLLAPSE).
- #111 (Rough Number Concentration for d=2 NoLongRuns, Session 82): Coprimality + q-roughness + super-exponential growth CANNOT rule out L consecutive QR minFac values. Q4 counterexample: for any L and q, can construct L pairwise coprime q-rough integers all with QR minFac. Orbit chain expansion via coprimality fails because coprimality constrains WHICH residues appear, not their QR character (TECHNIQUE MISMATCH).
- #112 (Order-3 Möbius Death Function, Session 83): Constrains death curve geometry, not walk dynamics (TECHNIQUE MISMATCH).
- #113 (Cycle Product Equidistribution, Session 91): Telescope reduces cycle products R_k to lag-1 autocorrelation of walk chars at return times = CCSB. Product structure (ℓ ≥ 2) gives zero advantage (CIRCULARITY). Death rate algebraic structure (paired rates, safe positions, product-one) is purely descriptive, no proof leverage.
- #114 (Missing Prime Accumulation, Session 97): Second-moment/Borel-Cantelli for missing primes. Pairwise Death Channel Independence = CME for single fiber (#90, #98). Self-consistent avoidance = §23. Kochen-Stone quasi-independence = SieveTransfer. EQUIVALENCE COLLAPSE.
- #124 (Lyapunov-Fiber Coupling / T5.7, Session 154): J(N)=∑_a d(a)·F(a) one-step recurrence contains F(w(N),N) = active-fiber char sum = CME gap. Cauchy-Schwarz gives bounds in wrong direction. J(N)=o(N) too weak (1 constraint on (q-1)-dim problem). EQUIVALENCE COLLAPSE. Maps to #110, #104, #120.

**Mixed Variant + InterpolationMC (Sessions 250-256)**: EM/Advanced/EpsilonRandomMC.lean (992 lines), EM/Ensemble/MixedEnsemble.lean (~1958 lines), EM/Advanced/RandomFactorMC.lean (376 lines), EM/Advanced/InterpolationMC.lean (1192 lines). Layer 1 (positive-prob capture) + Layer 2 (block coverage, iterated hitting) + Layer 3 (TSD → Regeneration) all PROVED. **Sole open gap: `TreeSieveDecay(q)`** — ∃ P₀, ∀ P ≥ P₀, Squarefree P, Coprime P q → GoodAccumulator q P. **Session 256 CRITICAL FIX**: original TSD was FALSE for all q≥3 (absorption: q|P traps walk at 0). Fix: added `Nat.Coprime P q`. **TSD-Hitting(3) PROVED unconditionally** via mod-3 dichotomy: P≡2 mod 3 → already at -1; P≡1 mod 3 → P+1≡2 mod 3 → factor ≡2 mod 3 exists → step 1 reaches -1. KEY BRIDGE: `tsd_implies_neg_one_reachable` uses dichotomy (walk hits -1 or stays coprime → TSD applies). Orbit melting (5 theorems): squarefree accumulators with same primeFactors are equal, same future, backward propagation. CRTPropagationStep is MARGINAL (4/10, maps to #90/#130). Mixing is NON-VIABLE without measure theory. Factor confinement (`factor_confinement`, `all_factors_confined`) and coset impossibility (`reachableEver_not_in_coset`) are the key structural results — all proved.

**Session 160 — "1 mod Growing S" Sieve Constraint = DEAD (0-1/10)**: SubProd(n) ensemble provides no new leverage. Boolean hypercube Fourier (T5.8) is genuinely new but faces compound obstacle: (a) high total influence kills exponential concentration (KKL gives O(1/√n), not O(2^{-δn})), (b) noise sensitivity is COUNTERPRODUCTIVE — decorrelates orbit point from population mean (strengthens #90). Support-constrained Alladi = EM/Population/AlladiDensity.lean. BV = average only (#108). Coupling via T-map = circular (= DSL, #90, #98). EM/Transfer/SieveConstraint.lean formalized (261 lines, 21 theorems). T5.8 added to catalog at UNTRIED 1/10. **Do NOT re-propose SubProd ensemble, hypercube Fourier, or BV-level individual estimates.**

**Session 158 Fiber Autonomy = NOT NEW**: "Fiber autonomy" (CRT fiber F(M) = {prod(M) mod r : r ≠ q} determines multipliers, walk is readout) = CRT multiplier invariance restated. EM/Ensemble/FiberAutonomy.lean (255 lines, 0 sorry) added as structural infrastructure but zero new mathematical leverage. CRT spreading = PE (#98). Multi-modulus Borel-Cantelli = cross-modulus ≠ cross-time (#123). Population → individual gap (#90) not closed by fiber structure. **Do NOT re-propose fiber autonomy, CRT spreading, or multi-modulus BC approaches.**

**Session 89 confirmation**: "Simultaneous Avoidance" (walk on product group ∏(Z/qᵢZ)× must avoid shrinking safe set) is exactly Dead End #101 (Bundle Walk). Explicit counterexample: in (Z/11Z)*, multipliers cycling {3,4} generate full group but walk only visits {1,3}, permanently avoiding -1=10. Density-based avoidance arguments are population-level, not path-level.

**Session 169 — Multiplicative Large Sieve + Sieve Orbit Control = DEAD (0/10)**: All 5 questions rated 0/10. (Q1) Standard large sieve averages over moduli q, giving population control only (#90, #108). (Q2) minFac is NOT multiplicative (`minFac_not_multiplicative` proved: minFac(6·35)=2≠10=minFac(6)·minFac(35)); blocks ALL Linnik-type approaches via Four-Way Blocker item 2 (#109). (Q3) Sieve orbit indicator collapses to SieveTransfer gap (#90). (Q4) CRT cross-modulus ≠ cross-time (#123). (Q5) No pointwise sieve oracle exists — analogous to Artin's conjecture (no unconditional proof that individual primes are primitive roots mod infinitely many q). `SieveOrbitControl = CCSB` proved by `rfl` in EM/Advanced/MarkovSieve.lean. **Do NOT re-propose multiplicative large sieve, minFac multiplicativity, sieve orbit indicators, or pointwise sieve oracles.**

**Session 170 — Function Field Analog: Infrastructure Complete, DSL Gap Universal**:
- **New files (4, 2302 lines, 112 decls, all 0 sorry)**:
  - `EM/FunctionField/Bootstrap.lean` — fiber decomposition in polynomial ring F_p[t], PE holds unconditionally (Weil RH), fiber structure parallel to Z/qZ setting
  - `EM/FunctionField/SubgroupEscape.lean` — SE proved for FF-EM walk on (F_p[t]/(irred))×, demonstrates full cycle-free generation
  - `EM/FunctionField/CyclicWalkCoverage.lean` — walk coverage bounds on cyclic extensions, proves periodic minFac orbit is dense in fiber
  - `EM/FunctionField/MultiplierCCSB.lean` — conditional char sum bounds for multipliers in FF setting
- **Key finding: Dead End #130 — SelectionBiasNeutral / ConditionalCharEquidist / WeilIIForFiber = EQUIVALENCE COLLAPSE**. All three formulations (selection bias neutrality, conditional character equidistribution on fiber, Weil II for fiber automorphisms) are CME under different language. FF setting gives PE unconditionally (from Weil RH) but does NOT bypass the structural DSL gap. The gap is universal: across Z (EM), F_p[t] (FF-EM), Galois orbits, and adelic completions, multiplier equidistribution requires proving a distributional property that the inherent dynamics cannot deliver algebraically. Maps to #90 (population ≠ orbit), #98 (per-step ≠ sequence), #107 (pointwise ≠ aggregate).
- **Implication**: Fiber variety angles (Sessions 166-168 AFG dead ends, #127, #129) are now formally CLOSED via Session 170. FF-MC complete as infrastructure; only DSL gap remains, and it is independent of the algebraic setting. Do NOT re-attempt FFMultiplierCSB_raw (tautology, Dead End #130), WeilIIForFiber (= CME by `rfl`), or selection bias neutrality (same). Chebotarev over F_p[t] also subject to same orbit-specificity obstruction as Chebotarev over Q (see Session 152 T4.2 + T4.3). **Codebase now includes 87 files, ~50,100 lines (Lean), 130 formal dead ends (Sessions 1-170).**

**Sessions 179-180 — Number Ring Extensions PROVED IMPOSSIBLE (Dead Ends #135, #136)**:
- **Dead End #135** (Session 179): Gaussian EM over Z[i] — orbit-specificity is a property of DETERMINISTIC GREEDY SELECTION, independent of ambient ring. For inert primes, F_{p²}× has MORE characters to control = strictly HARDER. No number ring helps.
- **Dead End #136** (Session 180): **Universal Confinement Theorem** — Z → O_K/𝔭 always factors through the prime subfield F_r ⊂ O_K/𝔭 = F_{r^f}. ALL characters of (O_K/𝔭)× restricted to the integer walk are Dirichlet characters mod r. Hecke Grössencharacters add archimedean growth factors |n|^s only, no new phase content. NormTwistedCME uses a DIFFERENT generating sequence, not the integer EM walk.
- **Kills ALL number field extensions for integer walk**: Q(i), Q(i,√p), Q(ζ_n), CM fields, any K/Q. The integer walk is PERMANENTLY CONFINED to the prime subfield of any residue field.
- **Formalized**: EM/GaussEM/GaussEMDefs.lean (290 lines) + EM/GaussEM/GaussWalkStructure.lean (331 lines) + EM/GaussEM/GaussConfinement.lean (347 lines), all 0 sorry.
- **T4.6 added to catalog**. **Do NOT re-propose any number field extension, Hecke character approach, CM equidistribution, biquadratic field, or ring-change strategy for the integer walk.**

**Session 183 — Reconvergence / Ratner Route / Algebraic Rigidity = DEAD (0/10)**:
- **Reconvergence Lemma is FALSE for EM walks**: After changing the multiplier at step k, the integer accumulator diverges (prod_A(k)≠prod_B(k)), so minFac(prod_A(k)+1) ≠ minFac(prod_B(k)+1) in general. The two walks have COMPLETELY DIFFERENT multiplier sequences after step k. There is no "reconvergence" because any single-step perturbation cascades through the entire future trajectory (butterfly sensitivity).
- **Even weakened version = `walk_readout_from_multipliers` (proved in EM/Ensemble/FiberAutonomy.lean)**: "Frequency stability under finite perturbation" is trivial from abelian commutativity — changing one multiplier shifts all subsequent positions by a fixed group element. Zero new content beyond PRE.
- **Cyclotomic Constraint = CRT invariance (proved)**: The condition prod(n) ≡ -1 mod seq(n+1) is orthogonal to prod(n) mod q by CRT. Already captured by CRT multiplier invariance.
- **Multiplicative Energy = CME circular**: Small energy ↔ CME ↔ equidistribution. No independent content.
- **Literature: ZERO applicable orbit-specific equidist results**: Every theorem in the literature requires polynomial/algebraic structure, unipotency, randomness, or multiplicativity. EM has none. Four-Way Blocker confirmed at literature level.
- Maps to #4 (ordering problem — multiset determines walk, but EM uses specific ordering), #90 (orbit specificity — EM orbit is ISOLATED, no "nearby walk" for comparison), #101 (bundle walk), #130 (generation ≠ coverage).
- **Do NOT propose Reconvergence, perturbation stability, Ratner analogies, algebraic rigidity arguments, multiset-based equidistribution, or coupling of EM-like walks.**

**Sessions 93-94 — Departure Graph Infrastructure**: File `EM/Group/DepartureGraph.lean` (393 lines, zero sorry) provides abstract group-theoretic framework.

Session 93 (core): `generation_escapes_subgroup` (re-derives SubgroupEscape abstractly), `subgroup_trapping` (confinement → multipliers in H), `coset_trapping_reduces` (coset + w(0)=1 → subgroup), `oracle_from_confinement` (position-dependent oracle from DH failure). Multi-prime density collapse assessed: maps to Dead End #101.

Session 94 (new):
- **Infinite Recurrence**: `exists_infinite_fiber_of_finite` (pigeonhole), `infinite_fiber_mem_visitedSet`, `infinite_departures_at_recurrent` — walks in finite groups have infinitely recurrent states with infinite departures.
- **Safe Prime Lattice**: `IsSafePrime` def, `dvd_two_mul_prime_iff` (divisors of 2p = {1,2,p,2p}), `card_subgroup_of_order_two_mul_prime` (Lagrange → 4-element lattice), `card_proper_subgroup_le` (proper subgroups have order 1, 2, or p), `multiplier_closure_ne_top_of_confined`, `generating_escapes_proper` (generation → escape from every proper H).

Session 95 (new):
- **Single Hit Theorem**: `SingleHitHypothesis` (weakest sufficient hitting condition for MC) and `single_hit_implies_mc` proved in EM/Equidist/Bootstrap.lean. SHH includes `mc_below q` as hypothesis, making it strictly weaker than DH. Paper §3 rewritten to make this the primary reduction.

Session 97 (new):
- **SDDS Framework**: 3 new files (447 lines, zero sorry): `EM/SDDS/Dynamics.lean` (168), `EM/SDDS/Bridge.lean` (153), `EM/SDDS/Reduction.lean` (126).
  - `FactoringRule` structure, `minFacRule`, `SDDS` structure, `emSDDS`
  - `euclid_minFac_eq_nat_minFac`: bridge between project and Mathlib minFac
  - `emSDDS_orbit_eq_prod`, `emSDDS_walk_eq_walkZ`, `emSDDS_mult_eq_multZ`: full correspondence
  - `StrongSME` (cofinal SME), `strong_sme_implies_hh`, `strong_sme_implies_mc`
  - 3 open hypotheses remaining: `SuperExponentialGrowth`, `SieveRegularity` (placeholder True), `SieveMapEquidistribution` (≈ MC)
  - `NoAlgebraicObstruction` **CLOSED** (Session 100), `CoprimeCascade` **CLOSED** (Session 104 — proved for ALL SDDS)

**Session 115 (new)**:
- **Cofactor Identity / "+1 Shift"**: `euclidCofactor n = (P(n)+1)/seq(n+1)`, `cofZ q n = cofactor mod q`. Identity `w(n)+1 = m(n)·cofZ(n)` proved (EM/Reduction/DSLInfra.lean, 13 theorems, +204 lines). Character decomposition: `χ(w(n)+1) = χ(m(n))·χ(cofZ(n))` when alive. Hit ↔ cofZ=0 (`walkZ_eq_neg_one_iff_cofZ_zero`). Genuine algebraic content beyond telescope. BUT cofactor is a JOINT quantity (depends on both P(n) and minFac(P(n)+1)), so runs into Marginal/Joint Barrier. Infrastructure only — not a route to DH/CME.
- **"+1 shift" literature**: ZERO external leverage. No papers study minFac(N+1) distribution conditional on N mod q. Structure unprecedented. Holowinsky shifted convolution requires multiplicativity (#109). Pham-Sauermann rearrangement is wrong quantifier (#4). Harper/Soundararajan character sums require multiplicativity (#109).

**Session 125 (new)**:
- **PerChiCancellationBridge PROVED**: `per_chi_cancellation_bridge_proved` in EM/Ensemble/PT.lean (+263 lines). Per-chi specialization of proved SD→VB→Concentration→Cancellation chain.
- **WeylHittingBridge PROVED (Session 127)**: `weyl_hitting_bridge_proved` via test function contradiction. Walk character cancellation → walk hits -1 cofinally.
- **Dead End #117 (Session 128)**: MultCancelToWalkCancel for EM-specific walks — PROVED IMPOSSIBLE. Multipliers alternating {2,3} mod 5 give S_K=0 but |W_K|=Θ(K). All EM structural properties insufficient. Transfer ≡ CCSB/CME.
- **JSE→MC chain now has 2 open Props**: JSE (hard) + MultCancelToWalkCancel (hard, Dead End #117). WeylHittingBridge is PROVED.
- **DSL cofactor identity analysis DEAD**: All 5 angles assessed for DSL leverage, all map to existing dead ends (#103, #110, #105, #93, #104). For fixed walk position a, multiplier m and cofactor c=(a+1)/m are in bijection — no distributional advantage. **Cofactor identity is infrastructure, not analytical tool.** Do NOT re-analyze.
- **Session 129 DSL exhaustion confirmed**: All 4 DSL strategy directions (algebraic identities in DSLInfra (EM/Reduction/DSLInfra.lean), cofactor completeness, Weyl sums, +1 shift additive combinatorics) map to existing dead ends. No untried strategy exists.
- **Session 137 Variance Route**: EM/Reduction/DSLVariance.lean formalized (407 lines, 12 theorems). C(j,k,X)=o(X) follows from JSE (already proved via cross_term_density_decomp + joint_step_equidist_implies_step_decorrelation). Per-prime conditioning route confirmed at 4/10. No obstruction found. Variance route does NOT map to existing dead ends. **JSE gap is sieve-theoretic, not algebraic.** No further algebraic sessions needed for variance route.
- **Session 138 CRT Pointwise Transfer = EQUIVALENCE COLLAPSE**: `OrbitConditionalEquidist = ConditionalMultiplierEquidist` by `rfl` in Lean (EM/Transfer/CRTPointwise.lean). OCE is definitionally identical to CME. ReturnVisitCancellation = fiberMultCharSum by `rfl`. CRT pointwise invariance is already baked into CME definition. PCE → OCE bridge is a weaker reformulation of DSL (PE → CME). **Do NOT re-explore "orbit conditioning" or "return visit cancellation" — these are CME under different names.**

**Session 117 (new)**:
- **Ensemble PT Framework**: 3 new files (EM/Ensemble/EM.lean, EM/Ensemble/CRT.lean, EM/Ensemble/PT.lean), 905 lines, 25 theorems. `genWalkZ`/`genMultZ` defs with standard EM bridge. CRT equidistribution chain (SRE+CRT→AEP by induction). 4-layer decorrelation chain. Master theorems: `ensemble_pt_master` (6-hypothesis), `gen_mc_two_implies_mc` (bridge), `dsl_closes_all` (DSL→MC∧CCSB). 10 new open Props for ensemble route. Key: ensemble averaging over squarefree starting points provides INDEPENDENCE (Four-Way Blocker item 1 bypassed). Distinct from all 116 dead ends.

**Session 118 (new)**:
- **GenHittingImpliesGenMC PROVED**: Cofinal walk hitting → GenMC via strong induction (parallels `conjectureA_implies_mullin`). +107 lines, 3 theorems.
- **EnsembleMultEquidistImpliesCharMeanZero PROVED**: Statement fixed (added chi(0)=0, ∑chi=0 for nontrivial characters). Proof via `tendsto_finset_sum` + density decomposition + character orthogonality. +50 lines, 2 theorems.
- **EnsembleEquidistImpliesDecorrelation → Dead End #98**: CRT per-step independence CANNOT give sequence-level decorrelation for deterministic walks. DO NOT attempt.
- **CharVarianceImpliesConcentration gap identified**: The Tendsto requirement in `EnsembleCharSumConcentration` is over-specified — Markov bound gives uniform-in-X bound but NOT convergence to 0 for fixed K. Needs reformulation to pointwise bounds.

**Session 119 (new)**:
- **CharVarianceImpliesConcentration PROVED**: Reformulated `EnsembleCharSumConcentration` from `Tendsto` to pointwise (ε, δ) bounds. Added `normSq(χ(a)) ≤ 1` condition. Markov bound + ceiling argument. +~70 lines, 1 theorem.
- **DecorrelationImpliesVariance PROVED**: Energy recurrence induction with C=2. Base K=0 trivial, K=1 by normSq bound, step: cross terms bounded via StepDecorrelation. +~280 lines, 8 theorems (including helpers: genSeqCharEnergy_zero/succ, ensembleAvg_le_of_pointwise/sum/add, cross_term_bound_from_sd).
- **SquarefreeResidueEquidist assessment**: Requires ~800-1500 lines of new infrastructure. Biggest blocker: ζ(2) = π²/6 (**stale claim — Mathlib has the Basel problem, `hasSum_zeta_two`; corrected Session 312**). Marked as long-term open.
- **Concentration chain now complete**: StepDecorrelation → CharSumVarianceBound → EnsembleCharSumConcentration → cancellation. StepDecorrelation is the SOLE remaining gap.

**Session 120 (new)**:
- **sd_implies_cancellation PROVED**: Consolidation theorem composing SD→VB→Concentration→cancellation. StepDecorrelation is the SOLE remaining gap.
- **ensemble_pt_master_simplified PROVED**: 4-hypothesis master theorem (down from 6). Single-line proof.
- **StepDecorrelation analysis**: SD requires JOINT equidistribution of (genProd n j mod q, genProd n k mod q) over squarefree n. Core obstacle: both genSeq n j and genSeq n k depend on the SAME non-mod-q CRT coordinates of n. CRT invariance gives mod-q blindness but NOT inter-step independence. Marginal equidist ≠ joint independence. Feasibility of proving SD directly: 2/10.
- **JointAccumulatorEquidist proposed**: If (genProd n j mod q, genProd n k mod q) is jointly uniform, then SD follows. Provable reduction (~200-300 lines). T2.10 added to catalog.

**Session 121 (new)**:
- **joint_step_equidist_implies_step_decorrelation PROVED**: JSE + nontrivial character → SD (PROVED, EM/Ensemble/PT.lean).
- **cross_term_density_decomp PROVED** (private): Density decomposition of cross-term.
- **sqfreeJointSeqCount, sqfreeJointSeqDensity PROVED**: Bounds on joint squarefree density.
- **JointStepEquidist (JSE) open hypothesis**: Joint uniformity of (genSeq n j, genSeq n k) mod q over squarefree n. JSE is now the sole remaining gap in the concentration chain (replaces SD).
- **CRTPropStep analysis**: Base case (k=0→k=1) feasible at 6/10 via CMFE; general case (k≥1) only 2/10 feasible due to correlation accumulation.
- **Updated chain**: JSE → SD → VB(C=2) → Concentration → Cancellation (all links PROVED).

**Session 123 (new)**:
- **JAE DEFINITION BUG FOUND (CRITICAL)**: `JointAccumulatorEquidist` (EM/Ensemble/PT.lean) is TAUTOLOGICAL — it's defined as the product of two marginal densities, NOT a genuine joint density. If AEP holds, JAE follows trivially by `Filter.Tendsto.mul`. JAE contains ZERO information about joint distribution. Needs reformulation with genuine joint counting function `sqfreeJointAccumCountSame` (counting squarefree n with genProd n j ≡ a AND genProd n k ≡ b simultaneously, same modulus, different steps). JAE is NOT used in any proved chain, so no existing theorems are invalidated.
- **JSE route genuinely bypasses Dead End #98**: JSE averages over ENSEMBLE of squarefree starting points (population-level), not per-step CRT chaining on a single walk. Proved reduction `joint_step_equidist_implies_step_decorrelation` correctly reduces SD→JSE. JSE faces a NEW independent obstacle: joint equidistribution of (genSeq n j, genSeq n k) over squarefree n. This does NOT map to any existing dead end.
- **SCRTI and corrected JAE are ORTHOGONAL**: SCRTI handles different moduli (q,r) at same step k. Corrected JAE handles same modulus q at different steps (j,k). Neither implies the other.
- **SCRTI bootstrap**: SCRTI + equidist(k, r) for ONE prime r → equidist(k, q) for ALL primes q (partially formalized in EM/Ensemble/CRTFreedom.lean, compilation pending).
- **JSE base case (j=0, k=1) feasible at 6/10**: genProd n 0 = n (uniform by SRE), genProd n 1 = n * minFac(n+1), CRT invariance ensures multiplication by minFac(n+1) preserves uniformity.
- **KS (2021) assessment: 4/10**: CRT equidistribution framework assumes CRT structure as input; EM must prove it emerges from dynamics. No existing result closes SCRTI. SCRTI requires new mathematics.

**Session 124 (new)**:
- **JAE FIXED**: Renamed tautological def to `JointAccumulatorEquidist_marginal`, added genuine `JointAccumulatorEquidist'` with `sqfreeJointAccumCountSame/DensitySame`. Proved `aep_implies_jae_marginal` (trivial via Tendsto.mul) + partition identity + density bounds. 4 defs, 7 theorems.
- **JSE→MC master chain PROVED**: `PerChiCancellationBridge` (PROVED) + `MultCancelToWalkCancel` (open, HARD) + `WeylHittingBridge` (open, routine) → `cancel_weyl_implies_mc`. 3 open Props. EM/Ensemble/PT.lean: 1805 lines. Session 126 correction: MultCancelToWalkCancel is ≡ CCSB/CME difficulty (Dead End #58).
- **JSE base case feasibility DOWNGRADED to 3/10**: Conditioning-prime decomposition requires BV-level sieve estimates, same infrastructure as SRE itself. No "easier base case" exists.
- **ROUTE DECISION**: Ensemble chain caps at a.a. GenMC (population-level). Cannot prove MC for n=2 specifically. DSL (`full_chain_dsl`) is the ONLY route to actual MC. Pivot primary focus to DSL.

**Session 136 (new)**:
- **Bag exhaustion ≡ DH** (EQUIVALENCE COLLAPSE): "walk visits all elements" IS DynamicalHitting. No reduction gain.
- **Non-recurrence + Generation + PBI = DEAD**: Counterexample {2,3} on (Z/5Z)× — PBI+SE+non-recurrence CANNOT prevent walk trapping in {1,2}. Walk never visits -1=4. Added T5.6 to catalog.
- **Cumulative coprimality**: Vacuous/circular — coprime cascade preserves distinctness but cannot force equidistribution.
- **Circular bypass chain PROVED** (EM/IK/Ch7Hilbert.lean, +353 lines): GramOffDiagCircular → ALSCircular. HilbertCscBilinearBridge ELIMINATED. IK Ch7 chain down to 1 open Prop (HilbertInequality1, permanent).
- **Sum-product (BKT) for DSL = DEAD**: Gives set cardinality only (= SE already proved). Marginal/Joint Barrier blocks multiplicity equidistribution.
- **Bourgain-Gamburd for (Z/qZ)× = DEAD**: Abelian group, quasirandomness = 1. No spectral gap.

**Dead End #123 — FourPointPCV (Session 146)**: EQUIVALENCE COLLAPSE. FourPointPCV asks Γ₄(j₁,k₁,j₂,k₂) → 0 over squarefree population for four-point cross-term decay. Claimed mechanism: CRT independence at four time steps. FAILS: CRT (SCRTI) provides cross-MODULUS independence at a single time step, NOT cross-TIME independence at a single modulus. Four-time correlation decay at single modulus q = HOD-type four-point mixing (#84). Even PCV (two-point = StepDecorrelation) is open. Maps to #84, #98, #115. Literature: Tao-Teräväinen "pairwise implies higher" requires multiplicativity — no non-multiplicative analog. **All concrete DSL sub-strategies are now exhausted.**

**Session 163 — Adelic/Profinite Infrastructure**:
- **CRTFiberImpliesMWI is now PROVED**: `crt_fiber_implies_mwi_proved` in EM/Adelic/Equidist.lean (~145 lines). Uses Fourier inversion on (Z/qZ)× via `MulChar.equivToUnitHom` (DirichletCharacter ↔ unit hom bijection) and `MulChar.coe_toUnitHom` (coercion bridge). CRTMultiplierFiber + MME → MWI → (with MME) → CME → CCSB → MC.
- **MME ↔ walk autocorrelation**: `mme_iff_walk_autocorrelation` PROVED. MME is equivalent to vanishing lag-1 walk autocorrelation ∑ χ(w(n))·conj(χ(w(n+1))).
- **CPDImpliesCRTFiber**: Assessed at 6/10 feasibility. Orbit-dependent Fourier coefficients are the obstruction.
- **FLE gap confirmed**: FiniteLevelEquidist (cofinal visits) is NOT proved from SE+PRE (subgroup generation). Strictly stronger.
- **CCSB+CPD → UPE is UNPROVABLE (Dead End #125, Session 164)**: XOR counterexample decisive — three unit-modulus sequences with all pairwise cancellation but triple product = N. No inequality (C-S, Hölder, VdC) bridges pairwise to k-wise. Tao-Teräväinen requires multiplicativity. CCSBCPDImpliesUPE is DEAD. UPE needs k-wise decorrelation for all k as primitive.

**Session 189 — FF Weak MC Infrastructure Complete**:
- **EM/FunctionField/WeakMC.lean** (471 lines, 30 theorems, 0 sorry): Degree escape theorem (`ffSeq_degree_tendsto_atTop`), capture counting framework, pool partition identity. All unconditional given FFFiniteIrreduciblesPerDegree.
- **Key finding**: Degree escape is genuinely new — unconditionally, the FF-EM sequence produces irreducibles of arbitrarily large degree. But positive density capture or full FF-MC requires orbit-specificity.
- **FF direction COMPLETE as infrastructure**. Do NOT invest more — orbit-specificity barrier is universal (#90, #127, #130).

**Session 195 — Weak MC via Mod-3 Density**:
- **AccumMod3LB** (new open hypothesis in CRT.lean): mod-3 accumulator density bounded below by constant κ > 0. Structural algebraic question: frequency of genProd(n) ≡ 2 mod 3 over squarefree ensemble.
- **Chain proved**: AccumMod3LB → SMLB → LMG → PositiveDensityRSD (7 theorems, all 0 sorry). Key: genSeq = 3 when genProd ≡ 2 mod 3 (unconditional parity), giving E[1/genSeq] ≥ κ/3.
- **Weak MC gap reduced to single mod-3 question**: algebraic in nature (residue class density over product structure).

**Session 267 — Quotient Character Lift for NFCE (EM/Advanced/VanishingNoiseVariantD.lean, +173 lines)**:
- **`quotientChar`** (def): χ̄ : G/ker(χ) →* ℂˣ via `QuotientGroup.lift chi.ker chi le_rfl`
- **`quotientChar_faithful`**: χ̄ injective via `ker_lift` + `map_mk'_self` (PROVED)
- **`quotientChar_apply`**: χ(g) = χ̄(π(g)) by `rfl` (PROVED)
- **`quotient_card_ge_two`**: |G/ker(χ)| ≥ 2 for nontrivial χ via `Subgroup.one_lt_index_of_ne_top` (PROVED)
- **`kernelConfinement_iff_quotient_eventually_one`**: KernelConfinement ↔ quotient eventually trivial (PROVED)
- **`ratioKernelEscape_iff_quotient_io_ne_one`**: RatioKernelEscape ↔ quotient i.o. nontrivial (PROVED)
- 12 theorems total + 1 def, zero sorry. **NFCE reduces to escape in quotient G/ker(χ) where χ̄ is faithful.**
- **Remaining gap**: `faithful_character_escape` works on (ZMod q)ˣ directly. Need abstract version for quotient groups, or verify the quotient walk IS a (ZMod r)ˣ walk for some r | q-1.
- **For Fermat primes (q-1 = 2^k)**: every proper quotient is Z/2^j Z with j < k. Faithful escape on these quotients should be easier (smaller groups). q=5: quotient Z/2Z.

**Session 223 — NonFaithfulCharSeparation PROVED (Fermat Prime Discovery)**:
- `nonFaithfulCharSeparation_of_two_prime_factors` — NFCS holds for groups with |G| having ≥2 distinct prime factors. Pure group theory: Cauchy + coprime zpowers + quotient character lifting.
- `nonFaithfulCharSeparation_units_zmod` — NFCS for (ZMod q)ˣ when q-1 has an odd prime factor.
- **KEY**: NFCS is FALSE for prime-power-order groups. Z/4Z counterexample: order-2 element is in kernel of the unique non-faithful nontrivial character. Intersection kernel dichotomy does NOT apply to Fermat primes.
- **Lean API**: `QuotientGroup.mk'`, `MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`, `mulCharToHom`, `Subtype.ext`.

**Next target**: (1) DSL is algebraically exhausted — cofactor identity (Session 125), all 4 DSL strategy directions (Session 129), all 3 Session 136 angles confirmed dead, FourPointPCV dead (Session 146). Only genuinely new external mathematics can break the impasse. (2) Monitor Mathlib for Chebotarev/Dirichlet PNT. (3) AccumMod3LB is a NEW structural target (mod-3 residue distribution of squarefree products). (4) DO NOT invest further in JSE or ensemble chain (architecture complete, diminishing returns). (5) DO NOT attempt `EnsembleEquidistImpliesDecorrelation` (Dead End #98), `SquarefreeResidueEquidist` (~1000 lines), or SD from marginal equidistribution. (6) DO NOT re-brainstorm DSL strategies — Sessions 129, 136, and 146 were definitive. (7) CME = MWI + MME (proved equivalence). CRTFiberImpliesMWI PROVED. The open gaps are CRTMultiplierFiber and MME themselves. (8) DO NOT invest further in FF analog direction — 6 files, ~2750 lines, orbit-specificity barrier universal. (9) Intersection kernel dichotomy is NOW PROVED for non-Fermat primes (NFCS closed). Fermat primes (q=3,5,17,257,65537) need separate treatment — q=3 done (UFDStrong(3)), q=5 has NFCE(5) infra.

**Session 72 confirmations** (all reduce to existing dead ends):
- Quasirandom walk on abelian groups → circular (#82: abelian = worst case for mixing)
- Time-varying Cayley expansion → requires i.i.d. steps (#95: spectral gap for deterministic walks)
- Bogolyubov-Ruzsa for partial products → ordering problem (#4/#36/#87)
- d=2 Legendre symbol route → reduces to SieveTransfer (#80/#88)

**Session 82 exhaustion thesis extension**: Sessions 72-82 collectively show that not only is algebraic content exhausted, but EM-specific structural features (roughness, coprimality, super-exponential growth) are ALSO insufficient. The recursive coupling P(n+1)+1 = P(n)·minFac(P(n)+1)+1 is the ONLY remaining leverage, and exploiting it IS SieveTransfer/CME.

If a proposed approach maps onto any catalog entry, do NOT explore it.

## Goal

Prove the `MixingHypothesis`: when the multipliers of the EM walk generate the full multiplicative group (Z/qZ)*, the walk must hit -1 mod q. Equivalently, prove `DynamicalHitting`.

**Secondary Goal (MixedMC variant)**: The mixed walk (choosing ANY prime factor of P+1, not just minFac) has a tree of valid walks. `MixedHitting` asks whether SOME valid walk reaches -1 mod q. Infrastructure:
- `reachableAt q acc n` — set of positions mod q reachable at step n (Session 242)
- `reachableEver q acc` — union of all reachable sets
- `mixed_hitting_iff_neg_one_reachable` — MixedHitting ↔ -1 ∈ reachableAt (PROVED)
- `factorSetModQ q P` — residues mod q of prime factors of P+1 (Session 242)
- **Reachable set growth (Session 243)**:
  - `reachableAt_from_factor` — CORE: any prime p | P+1 gives P·p ∈ R_{n+1} (σ' construction)
  - `reachable_grows_pair` — two factors → two elements in R_{n+1}
  - `reachable_composite_branch` — composite P+1 → branching via distinct factors
  - `reachable_growth_landscape` — 4-clause summary
- Self-consistency barrier: factor sets depend on walk's own accumulator (#130 at tree level)
- MixedDiversity (cofinal composites) required but unprovable with current math (Bunyakovsky-type)
- `perpetual_prime_excludes_mod3_one` — if P(n)+1 always prime, walk never ≡ 1 mod 3 (PROVED)
- **Logarithmic CD is DEAD** (Session 243): isomorphism (Z/qZ)× ≅ Z/(q-1)Z maps minOrder 2 → 2 (q-1 even). CD vacuous on both sides. Maps to Dead End #137.
- **Multi-prime sieve is DEAD** (Session 243): absorption barrier — primes in sequence fix walk at 0 mod r permanently. Mod-3 analysis is ceiling of this technique.
- **Coset Impossibility PROVED (Session 244)**:
  - `mixedWalkProd_two_minFac_eq_prod` — bridge: standard EM walk = mixed walk with minFacMixed
  - `reachableEver_ratios_escape_subgroup` — KEY: PRE + MCBelow ⇒ ∃ u₁,u₂ ∈ R_∞ with u₁·u₂⁻¹ ∉ H (proper subgroup)
  - `reachableEver_not_in_coset` — R_∞ ⊄ g·H for any proper coset
  - `coset_impossibility_landscape` — 3-clause summary
  - **Implication**: R_∞ is structurally too diverse for any coset. Remaining gap: R_∞ = (Z/qZ)× (full group).
- **Factor Confinement PROVED (Session 245)**:
  - `factor_confinement` — CORE: prime p | P+1 at reachable P ⟹ (p : ZMod q) ∈ allowedFactors(P mod q, R_∞)
  - `all_factors_confined` — ALL prime factors of reachable Euclid numbers are confined
  - `standard_euclid_factors_confined'` — specialization to prod(n)+1
  - `forbidden_nonempty_of_unit` — forbidden set nonempty when R_∞ proper and walk pos is unit
  - `FactorEscapeHypothesis q` — **OPEN**: EM orbit escapes step-dependent proper factor confinement
  - `factor_escape_implies_mixed_hitting` — FEH ⟹ MixedHitting (by contradiction)
  - **Key insight**: Standard MC constrains 1 factor per step; mixed MC with R_∞ proper constrains ALL ω(P+1) factors. This is exponentially more restrictive — a sieve-theoretic impossibility for generic integers.
- **InterpolationMC Layer 3 PROVED (Sessions 255-256)**:
  - `mixedWalkProd_squarefree` — squarefree propagation through mixed walks (induction, `Nat.squarefree_mul_iff`)
  - `TreeSieveDecay q` — **OPEN (FIXED Session 256)**: ∃ P₀, ∀ P ≥ P₀, Squarefree P → **Coprime P q** → GoodAccumulator q P. Original def was FALSE (absorption).
  - `TreeSieveDecayHitting q` — **WEAKER**: only -1 reachable, not all units. **TSD-Hitting(3) PROVED unconditionally** (Session 256).
  - `treeSieveDecay_implies_regeneration` — TSD ⇒ Regeneration (one-liner via monotonicity + squarefreeness)
  - `tsd_implies_neg_one_reachable` — **KEY BRIDGE**: TSD ⇒ -1 reachable via coprimality dichotomy (Session 256)
  - `mixedWalkProd_coprime_of_no_death` — coprimality propagation when walk never hits -1 (Session 256)
  - **Orbit melting** (Session 256): `eq_of_same_primeFactors_squarefree`, `same_accumulator_same_future`, `tail_reachable_implies_reachable`, `good_accumulator_propagates_to_start` (4 structural theorems + landscape)
  - `exists_prime_factor_mod3_eq_two` — strong induction: N≡2 mod 3, 3∤N → ∃ prime p|N with p≡2 mod 3
  - `tsd_hitting_three_unconditional` — **UNCONDITIONAL** TSD-Hitting(3) via mod-3 parity dichotomy
  - **Full chain**: PEAP + TSD ⇒ MC (all bridges proved). TSD is now the sole sieve-theoretic gap.
  - **Session 258 TSD ceiling**: Full TSD(3) is **FALSE** (P=2 counterexample: {0,2} reachable, unit 1 unreachable). **TSD-Hitting(3) is the ceiling of purely algebraic TSD results.** Future TSD progress requires sieve-theoretic or probabilistic methods.
  - **Session 262**: TSD(5) subgroup escape infrastructure formalized (13 theorems). H={1,4} is unique proper subgroup. Factor escape from H guaranteed. Multiplication table: 2²=-1, 3²=-1, 2·3=1. Remaining gap: "same-class factor" needed to hit -1, but tree may consistently land in wrong coset.
  - **Session 263 — COSET AMBIGUITY GAP**: **SpecificResidueClassFactor5 (universal) is FALSE** (P=2 counterexample: P+1=3, only factor ≡3 mod 5). LSD (Landau-Selberg-Delange) proves infinitely many squarefree N≡3 mod 5 with ALL factors ≡3 mod 5. **q=3 is structurally unique**: (Z/3Z)× has ONE non-identity element = -1, so escaping identity = hitting -1. For q≥5, (Z/qZ)× has multiple non-identity cosets. `coset_ambiguity_counterexample`, `single_coset_implies_immediate_hit`, `two_cosets_counterexample_five`, `coset_ambiguity_landscape` all PROVED. **TSD-Hitting(q≥5) unconditional: 0/10 algebraically.** Do NOT attempt unconditional TSD-Hitting for q≥5 via group theory.
  - **Probability infrastructure**: `EM/Probability/TransitionKernel.lean` (267 lines) — `factorPMF`, `epsStepWeight`, sum-to-one, bridge to `stepWeightLB`.

## Current Infrastructure (already formalized)

- **SubgroupEscape (SE)**: proved for 30 concrete primes q ≤ 157, and globally via PRE→SE
- **PRE ↔ SE decomposition**: `EM/Equidist/CharPRE.lean`
- **QR obstruction**: `EM/Group/QR.lean` — at most 1.6% of primes can fail SE
- **Escape lemmas**: `EM/Group/Escape.lean` — `eight_elts_escape`, structural escape results
- **Confinement theorem**: `EM/Group/Core.lean` — walk stays in subgroup generated by multipliers
- **Character product formula**: `char_walk_product` — χ(walk(n)) = χ(walk(0)) · ∏_k χ(mult(k))
- **Character orthogonality**: `DirichletCharacter.sum_char_inv_mul_char_eq` in Mathlib
- **CRT infrastructure**: `EM/Group/CRT.lean` — `crt_multiplier_invariance`, `return_product_char_one` (PROVED but TAUTOLOGICAL — Dead End #99)
- **CME hierarchy**: PED < Dec < CME < CCSB (strict, all formalized)
- **CME decomposition**: `EM/CME/Decomposition.lean` — `EMDirichlet` (= Dec alias), `EMDImpliesCME` (open), `emd_cme_implies_mc`. Surjection lemma: `surjective_subgroup_coset_meets_death` (every coset of a surjecting subgroup meets the death set in a product group)
- **Squarefree accumulator**: `EM/Population/WeakErgodicity.lean` — `prod_squarefree` (PROVED), `ShiftedSquarefree`, `euclid_in_shifted_squarefree` (PROVED), `EM/FunctionField/PopulationEquidist.lean` (open), `PopulationTransfer` (open), `pe_transfer_cme_implies_mc` (PROVED)
- **VCB (Session 73)**: VanishingConditionalBias — fiber sums proportional to visit counts with common ratio μ. VCB + PED → CCSB (proved). VCB + Dec = CME (equivalence). VCB is strictly weaker than CME (allows μ ≠ 0). **Session 78**: (VCB → CCSB) ⟺ PED. VCB alone cannot imply CCSB — the μ≈1 (kernel confinement) case is algebraically irrefutable.
- **Cofactor Identity (Session 115)**: `euclidCofactor`, `cofZ` defs; `shifted_walk_eq_mult_mul_cof` (w(n)+1=m(n)·cofZ(n)), `walkZ_eq_neg_one_iff_cofZ_zero` (hit↔cofZ=0), `char_shifted_walk_eq_char_mult_mul_char_cof` (character decomposition), plus 10 supporting lemmas. Genuine algebraic content beyond telescope — decomposes multiplier character via cofactor.
- **Transition Matrix Infrastructure (Session 81)**: `transitionCount`, `emVisitCount` defs; `transitionCount_eq_mult_fiber`, `transitionCount_row_sum`, `transition_char_sum_eq_fiber`, `cme_iff_transition_char_vanish` (all PROVED). CME ↔ transition matrix convergence is a formal equivalence (Dead End #110 — reformulation, not technique).
- **Gram matrix ALS framework (Sessions 85-86, 113, 130)**: §7.4d non-optimal ALS PROVED, §7.4d' packing bound + improved ALS PROVED (Session 113: 6 theorems, R-independent constant N+1/(2δ²)), §7.4e off-diagonal bilinear → optimal ALS PROVED. Session 130: `hilbert_chain_als` PROVED — full chain HilbertInequality → CscPartialFraction → CscBilinearBound → GramOffDiagBilinearBound → ALS. 4 open Props remain (CscPartialFraction, HilbertCscBilinearBridge, CscBilinearImpliesGramOffDiag, HilbertInequality). Constants relaxed to 1/δ (Cohen trick deferred).
- **ALS → MLS for prime (Session 88)**: `als_implies_mls_prime` PROVED — full Gauss+Parseval+spacing reduction.
- **§7.6 Large sieve as sieve (Session 89)**: `sieveWeight`, `sieveWeightProd`, `sieveDensity` defs; reductions `Lemma715+FareyLS → LargeSieveAsSieve → card bound` PROVED. Open Props: `Lemma715`, `LinnikSmallQNR`.
- **§39 Coprimality Refreshing & Death Rate (Session 91)**: `coprimality_refreshing_int/nat`, `no_safe_cycle`, `neg_inv_involutive`, `negInvEquiv`, `walk_product_telescope`, `char_ratio_of_walk_step` — all PROVED in EM/Equidist/SieveTransfer.lean. Death rate algebraic structure confirmed descriptive-only (no proof leverage for DH).

**Session 259 — Profinite Multiplier Generation (EM/Adelic/ProfiniteGeneration.lean, 177 lines, 0 sorry)**:
- `primeUnitsBelow_generate` — primes < N generate (ZMod N)× (pure NT, strong induction via minFac + coprimality propagation)
- `mc_below_implies_full_generation` — MCBelow N → EM multipliers generate (ZMod N)× (via Subgroup.closure_mono)
- `mc_implies_full_generation` — MC → full generation ∀ N > 1 (IsPrime ↔ Nat.Prime bridge)
- **Goursat analysis**: `Subgroup.goursat_surjective` in Mathlib adds ZERO new content — classifies subgroups not trajectories. Dead End #130 applies. T1.11 = DEAD.

**Session 86 definitive CME assessment (reconfirmed Session 91)**: Systematic review confirmed ALL angles are covered by 113 dead ends + Four-Way Blocker + Marginal/Joint Barrier. Session 91: product equidistribution circular (#113), death rate structure descriptive-only. Do NOT re-brainstorm CME/SieveTransfer unless genuinely new external mathematical techniques emerge.

**Session 215 — Routes to UFDStrong formalized (EM/Advanced/VanishingNoiseVariant.lean)**:
- **MinFacRatioEscape** (quantitative: ∃ δ > 0, spectral gap ≥ δ i.o.) → UFDStrong PROVED
- **MinFacRatioEscapeQual** (qualitative: card ≥ 2 + distinct chi-values i.o.) → MinFacRatioEscape PROVED via finite-range argument (Finset.min' on positive gap values over Fintype)
- **OrbitMFRE** (orbit-level minFac residue equidist) → MinFacRatioEscapeQual via open bridge OrbitMFREImpliesEscapeQual
- **Landscape**: 6-clause `routes_to_ufdStrong_landscape` PROVED
- **Key technique**: gap function has finite range since Finset (ZMod q)ˣ is Fintype → `Set.toFinite` + `Finset.min'` gives uniform bound without pigeonhole/cosine
- UFDStrong ⇒ VariantHitting ⇒ VariantMC (all PROVED, Sessions 213-215)
- Open Props: MinFacRatioEscape (as hypothesis), OrbitMFREImpliesEscapeQual (bridge)

**Session 157 — FPM = Dec confirmed, hierarchy fully mapped**:
- **FPM (FreshPrimeMixing) = Dec = EMDirichlet** by `rfl`. NOT a new hypothesis. Already formalized as `emd_eq_dec : EMDirichlet = DecorrelationHypothesis := rfl` in EM/CME/Decomposition.lean.
- **FPM does NOT imply CME**: gap = `EMDImpliesCME` (open). Obstruction: fiber sums F(a,N) can have different per-position biases c(a) that cancel in the total sum.
- **FPM does NOT imply MC** via any proved chain. Three routes: (a) Dec→CME (needs EMDImpliesCME), (b) Dec→PED→CCSB (needs PEDImpliesCSB), (c) Dec→WalkCancel (Dead End #117: PROVED IMPOSSIBLE).
- **Complete hierarchy**: CME → {CCSB, Dec=FPM}, CCSB → MC, Dec → PED. Dec and CCSB are INCOMPARABLE.
- **"Bag-of-primes renewal"** = PBI + SE (already captured). Coprimality constrains WHICH primes, not ORDER.
- Do NOT propose FPM-based approaches, bag-of-primes renewal, or cofactor walk analysis.

## The Fundamental Barrier

SE gives Subgroup.closure {mult(n)} = ⊤, which means SOME product of multipliers reaches -1. But the EM walk uses multipliers in a SPECIFIC ORDER (consecutive products), not arbitrary subsets. The ordering problem is the genuine mathematical gap.

## SubgroupConfinement Analysis — FULLY EXPLOITED (Session 76)

All confinement analysis is already formalized in the codebase:
- `kernel_confinement_walk_char_constant` — eventual kernel → walk char constant (PROVED)
- `kernel_confinement_walk_sum` — linear growth formula under confinement (PROVED)
- `ccsb_at_implies_escape_cofinal` — CCSB → infinitely many escapes (PROVED)
- `se_failure_factor_dichotomy` — minFac dichotomy under confinement (PROVED)
- `confinement_target_set` — Euclid numbers mod q lie in translated coset (PROVED)

**No abstract algebraic route to PED.** Even for q=3, there is no group-theoretic obstruction to SubgroupConfinement. The constraint "minFac(P(n)+1) always in H mod q" is a sieve question, not an algebraic one.

## Only Viable Algebraic Route

The **Kummer / Chebotarev route** is the ONLY algebraic approach not equivalent to a known dead end. It operates at the level of algebraic number fields rather than harmonic analysis. BLOCKED on:
- Chebotarev density theorem NOT in Mathlib (~5000+ lines to formalize, blocked by zero-free region)
- Adaptation from Booker-Simon (second EM, maxFac) to first EM (minFac) is an open mathematical question
- maxFac has algebraic structure via cyclotomic polynomials → Hasse-Weil. minFac has NO algebraic geometry — purely a sieve question

## Key Definitions

- `walkZ q n`: the EM walk residue mod q at step n (in Z/qZ)
- `multZ q n`: the multiplier at step n (in (Z/qZ)*)
- `SubgroupEscape q`: the multipliers generate the full group (Z/qZ)*
- `MixingHypothesis`: SE + walk generates full group → walk hits -1
- `factorRatio n` (Session 220): liftToUnit(minFac) * liftToUnit(secondMinFac)⁻¹ in (ZMod q)ˣ
- `gap_zero_iff_ratio_in_ker` (Session 220): spectral gap = 0 ↔ factorRatio ∈ ker(χ) — reduces NFCE to algebraic ratio-kernel membership
- `KernelConfinement q chi` / `RatioKernelEscape q chi` (Session 220): ratio eventually in ker vs escapes i.o.
- `summable_implies_ratio_confined` (Session 220): NFCE failure forces factorRatio into eventual kernel confinement
- `NonFaithfulCharacterEscape q` (Session 219-220): sole open gap for UFDStrong(q) at q ≥ 5 — now fully characterized as ratio kernel escape problem
- `nonfaithful_ker_card_eq_two_of_order_four` (Session 222): non-faithful nontrivial χ in group of order 4 has |ker| = 2
- `ratio_escape_implies_nfce_five` (Session 222): RatioKernelEscape for all non-faithful χ → NFCE(5)
- `variant_mc_five_of_ratio_escape` (Session 222): ratio escape → StochasticTwoPointMC(5)
- **Intersection kernel argument** (Session 222): In cyclic group of order n with ≥2 distinct prime factors, ⋂(nontrivial proper subgroups) = {1}. Total NFCE failure → factorRatio eventually = 1 → self-correcting. BUT: NFCE failure is existential (one χ), not universal. Does not apply at q=5 (q-1=4=2², one prime factor). First applies at q≥7.
- **EM/Ensemble/TwoPointEnsemble.lean** (Session 224, 566 lines, 0 sorry): Population-level reduction. `genFactorRatio q n k` = liftToUnit(genSeq)·liftToUnit(secondMinFac)⁻¹. Chain: PopulationRatioEscapeDensity (PRED) → Fubini + linear first moment → partition argument → AlmostAllInfiniteRatioEscapes → UFDStrong → StochasticTwoPointMC. Open Props: PRED, MFREImpliesPopulationRatioEscape (MFRE→PRED). The key question for the algebraic agent: can MFRE (MinFacResidueEquidist) force the **ratio** minFac/secondMinFac to equidistribute modulo ker(χ)?

**Session 247 — Ensemble Factor Escape Formalized (EM/Ensemble/MixedEnsemble.lean)**:
- **PSCD definition bug CAUGHT AND FIXED**: Original PSCD required decay for ALL proper finsets R. FALSE for R = {nonzero}: confinement = q∤m+1 has density (q-1)/q. Fix: R must miss a NONZERO element.
- `sqfreeTrappedCount` now counts coprime-to-q squarefree m where -1 not reachable (hitting failures).
- Key: for trapped m coprime to q, R_∞ misses -1 (nonzero since -1≠0 for q≥2), so R_∞.toFinset ∈ properFinsets.
- `PSCD q` (OPEN) — sole remaining hypothesis for a.a. GenMixedHitting.
- **Lean API**: `neg_ne_zero.mpr one_ne_zero` for `-1 ≠ 0` in nontrivial rings. Need `Fact (1 < q)` for `Nontrivial (ZMod q)`.

**Session 230 — NFCE(5) Assessed as Intractable (2/10)**:
- NFCS fails at Fermat prime q=5 (|G|=4=2², only constrains ratio ∈ {1,4} not ratio=1).
- No self-correcting mechanism: only ONE non-faithful nontrivial χ at q=5 (ker = {1,4}), so even total intersection gives ker ∩ ker = {1,4} (same kernel).
- Same orbit-specificity barrier (#90): knowing factorRatio ∈ {1,4} population-level doesn't force orbit-level escape.
- **Do NOT propose new NFCE(5) approaches** — the algebraic structure is exhausted for prime-power-order unit groups.

**Session 230 — PathSurvival Discovery**:
- `TreeContractionImpliesRandomMC` decomposed into TCA + PathSurvival.
- `PathSurvival` = survival-to-death ratio → ∞ in the binary walk tree.
- For q ≥ 5: PathSurvival is expected (2 ≢ -1 mod q, so step-0 survival).
- For q = 3: PathSurvival FALSE (immediate death), but TCA(3) also FALSE, so vacuous.
- **Algebraic question**: can group-theoretic properties of (ZMod q)ˣ force PathSurvival?

**Session 233 — Iterated Cauchy-Davenport Coverage PROVED**:
- `EM/Advanced/IteratedProductCoverage.lean` (293 lines, 0 sorry) — DETERMINISTIC coverage via iterated Cauchy-Davenport.
- `iteratedMulFinset_card_growth`: `|S_0*...*S_{n-1}| ≥ min(|G|, 1+∑(|S_k|-1))` (induction using `cauchy_davenport_minOrder_mul`)
- `iteratedMulFinset_eq_univ`: after |G|-1 steps with |S_k|≥2 ⟹ product = Finset.univ
- `minOrder_units_zmod_safe_prime`: Lagrange argument for safe primes (p-1 prime ⟹ minOrder = p-1)
- **Limitation**: requires `minOrder G = Fintype.card G`. For `(ZMod q)ˣ`, this needs q-1 prime (safe prime).
- **Open**: Extend to general cyclic groups where `minOrder = smallest prime factor of q-1 ≠ q-1`.
- **Algebraic question**: can Kneser's theorem (not yet in Mathlib) remove the minOrder = |G| restriction?
- Full ε-MC proposal ABORTED (rehash of Sessions 207-218). Do NOT re-propose full factor bag ε-MC.

**Session 262 — NFCE Algebraic Routes Fully Exhausted**:
- All 6 algebraic questions about NFCE reduction analyzed; ALL map to existing dead ends (#90, #98, #105, #109, #110, #111).
- **NFCS status**: PROVED for groups with ≥2 distinct prime factors in |G|. FALSE for Fermat primes (q=5,17,257,65537 where |(ZMod q)×|=2^k).
- NFCE infrastructure is complete and optimal. No algebraic refinement can close the gap.
- The remaining gap is sieve/analytic (orbit-specificity barrier), NOT algebraic.
- **Do NOT propose any NFCE approaches** — the algebraic vector is 100% exhausted.
- **TSD(5) subgroup escape formalized** (EM/Advanced/InterpolationMC.lean, 13 theorems):
  - `exists_factor_not_in_subgroup_five`: N ≡ 2 or 3 mod 5 ⇒ ∃ prime factor ∉ {1,4} mod 5
  - `neg_one_or_two_three_reachable`: From any coprime P, either hit at step 0 or {2,3} reachable
  - `hit_neg_one_from_two`, `hit_neg_one_from_three`: 2·2 = 3·3 = -1 mod 5
  - `non_hit_cross_products`: 2·3 = 3·2 = 1 mod 5 (back to square one)
  - Remaining gap: need **SpecificResidueClassFactor** — guarantee same-class factor at tree depth ≥2
- **Active algebraic direction**: Can algebraic constraints on squarefree P+1 force factor residue alignment? This is the only non-exhausted algebraic question.

**Session 292 — Scoping Pass S-FF: FF Algebraic-Geometric Tools = CLOSED**:
- **Mason-Stothers on FF-EM**: ALL identities give TRIVIAL bounds due to **Squarefreeness Absorption Principle**. The FF-EM accumulator P_n is squarefree (product of distinct monic irreducibles by `ffSeq_injective_proved`), so rad(P_n) = P_n. This absorbs the entire Mason-Stothers radical budget. All identities (base, decomposition, iterated, derivative) reduce to 1 ≤ deg(rad(P_n+1)) — trivially true. Non-vanishing derivative P_n'(t) ≠ 0 proved by induction via m_n-adic valuation. Mathlib `Polynomial.abc` available but useless. See `scoping/ff_mason_stothers.md`.
- **Explicit Galois groups of P_n(t)+1**: OBSTRUCTED. Galois groups provably abelian (cyclic, Frobenius-generated) because FF-EM products divide t^{p^d}-t. Abelian monodromy = Dirichlet character sums = Weil bound = PE (Dead End #129). Sequential gap blocks Deligne equidistribution. See `scoping/ff_galois_drinfeld.md`.
- **Drinfeld modules / CFT**: OBSTRUCTED. FF-EM recursion self-referential; cannot embed in fixed Drinfeld module. Drinfeld CFT = Chebotarev = PE. See `scoping/ff_galois_drinfeld.md`.
- **Key structural insight**: The coprimality cascade is a double-edged sword — it enables the sieve bootstrap (distinct factors at each step) but defeats Mason-Stothers (squarefreeness makes all radical bounds trivial). Cannot have both.
- **Do NOT propose**: Mason-Stothers applications to FF-EM, Galois group computations for P_n+1, Drinfeld module embedding, class field theory for orbit-pointwise leverage, primitive divisor theorems (require FIXED iteration), arboreal Galois representations (require FIXED polynomial).

**Session 293 — Scoping Pass S-Schematic: EM on Curves of Genus g > 0 = CLOSED**:
- **Construction pathology**: On elliptic curves (g=1), coordinate ring D = O_E(E \ {O}) is non-PID Dedekind domain. EM "+1 step" undefined for non-principal ideals. Orbit leaves principal class at step 1 (explicit E/F_5 computation). Restricting to elements recovers genus-0 behavior.
- **SAP is genus-independent**: Coprimality cascade (each m_n divides P_n+1, not P_n) is a recursion property, not ring property. rad(P_n) = P_n at every genus. Mason-Silverman (genus-g ABC) WEAKENS with genus: +2g-2 term makes bound vacuous for g ≥ 1. Genus 0 was strongest case.
- **No support lower bound in AG**: For any curve C, any genus g, any degree d ≥ 1, divisor D = d·P has |supp(D)| = 1. No AG theorem forces large support. Riemann-Roch constrains l(D), not |supp(D)|. Clifford vacuous on E. Brill-Noether population-level.
- **Walk on E(F_q) not more tractable**: Frobenius trivial on degree-1 factors. Orbit-specificity barrier setting-independent (formally proved). All AG tools population-level.
- **F₁-transport**: No functor from curves/F_q to Spec Z. All F₁ results compute global invariants.
- **DEFER-higher-genus NOT warranted**: SAP genus-independence + Mason-Silverman monotonic weakening + D=d·P counterexample close all genera simultaneously.
- See `scoping/verdict_schematic.md`, `scoping/schematic_construction.md`, `scoping/schematic_walk.md`.
- **Do NOT propose**: Schematic EM on positive-genus curves, Riemann-Roch orbit constraints, Jacobian structure for EM, F₁-transport to Spec Z, Brill-Noether for specific divisors, walk on E(F_q) as easier target.

## Reporting new dead ends (catalog is `EM/Meta/DeadEnds.lean`)

**The authoritative dead-ends catalog is the Lean file `EM/Meta/DeadEnds.lean`**
(docstring tables + `#check` re-exports of the formal Lean witnesses).
`docs/dead_ends.md` is only a pointer stub.

**Do NOT edit the catalog yourself.** New dead ends are recorded in
`EM/Meta/DeadEnds.lean` by the coordinator/formalizer — that file must still
compile. Your job is to REPORT candidate dead ends in your findings.

When you confirm a new dead end, report it with:

1. A one-line description and the owning file (`EM/<Subject>/<File>.lean`, or "paper only").
2. A **category code**:
   - **OS** — Orbit-Specificity: population statistics ≠ orbit statistics
   - **TM** — Technique Mismatch: framework assumes structure EM lacks
   - **SM** — Scale Mismatch: error terms dominate the signal
   - **CI** — Circularity: reduces to the hypothesis it aims to prove
   - **SF** — Structurally False: provably impossible (counterexample)
   - **CO** — Collapse: reduces definitionally to an existing hypothesis
   - **DG** — Decorrelation Gap: transfer from marginal to joint fails
   - **AG** — Aggregate Gap: average-case ≠ per-fiber case
3. A **proposed weak-MC revival score 0–3**: 0 = stays dead for any weak form;
   1 = marginal, contributes indirectly; 2 = helps for AlmostAllRSD or positive
   density; 3 = revives substantially for a specific weak MC form.
4. The formal Lean witness name if one exists (or `—`).
5. The session number and the key fact establishing the obstruction.

Suggested table row for the coordinator to paste into the catalog:

```
| # | Cat | Description | File | Witness | Revival |
```

Do NOT assign the number yourself — the coordinator reads the current maximum
from `EM/Meta/DeadEnds.lean` (`deadEndCount`). Only report approaches analyzed to
a clear obstruction (counterexample, equivalence proof, or confirmed missing
infrastructure). Do not report speculative failures.

## Output

Provide:
1. Assessment of which remaining sub-approaches are most promising
2. Specific algebraic obstacles identified
3. Proposed abstract lemma statements that could support the character sum bound
4. Whether algebraic tools can sharpen the analytic approach
5. **New dead ends discovered** — REPORT in your findings with category code (OS/TM/SM/CI/SF/CO/DG/AG), proposed revival score 0–3, owning file, witness (or —), session, and key fact. The coordinator/formalizer records them in `EM/Meta/DeadEnds.lean`; do not edit that file yourself.

---

## ⚠️ Tooling constraint (added Session 299)

**You have NO `Write`/`Edit` tool** (Read, Glob, Grep, WebSearch, WebFetch only). Do not
plan to create a file. If your dispatch asks for one, **return the full content inline in
your final report** and state that the file could not be written — the coordinator
transcribes it. Exceeding a stated word cap is correct when the cap assumed you could write
to disk. (Session 299: two agents lost deliverables to this.)

## Session 299 — cross-cutting results every attack agent should know

- **(C∞) is the new top frontier item**: "infinitely many `prod n + 1` are composite"
  (`InfinitelyManyComposite`, `EM/Population/AutonomousBranch.lean`). Its negation
  (perpetual primality) makes the walk **autonomous** (`W_{n+1} = W_n² + W_n`) and, since
  `w²+w+1` has no root mod `q` for `q ≡ 2 mod 3`, would refute MC on a **density-1/2** set
  of primes. We proved `mullin_implies_infinitelyManyComposite`, so (C∞) is a *necessary*
  condition for MC and strictly easier.
- **The anatomy principle**: in both the min/max dichotomy and the (ω1) branch, what defeats
  the congruence method is **anatomy** (smoothness / compositeness). Congruence invariants
  factor through `p ↦ p mod m`, i.e. through the walk, which sees only the product. Before
  proposing any invariant, ask: *does it see anatomy?* If not, it cannot distinguish the
  (ω1) branch.
- **The min/max break point is NOT Free-state Fullness** (which is rule-symmetric). It is the
  *capture condition*: `minFac N = q` is a congruence condition; `maxFac N = q` is a
  smoothness condition. Older docs claiming otherwise were corrected in Session 299.
- **Do not use the diversity chain's contrapositive.** `diverse_steps_imply_vanishing` is
  abstract over an arbitrary `S : ℕ → Finset G` and concerns `avgCharProduct` (the *averaged*
  tree product), not the deterministic orbit. Avoidance forces nothing about monochromaticity.
- **Covering systems are closed** (`no_finite_prime_covering`, `no_covering_family_obstruction`).
