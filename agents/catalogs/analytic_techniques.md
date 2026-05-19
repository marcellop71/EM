# Analytic Technique Catalog

**Domain**: Analytic number theory / harmonic analysis on finite groups
**Attack agent**: `attack_analytic`
**Last updated**: Session 276

---

## How to use this catalog

1. **Before proposing anything**: scan the STATUS column. If DEAD, don't revisit.
2. **Check preconditions**: each technique lists what it needs. If EM fails a precondition, the technique is blocked.
3. **Check the Four-Way Blocker**: does the technique require independence, multiplicativity, algebraic-geometric structure, or ergodic stationarity? If so, it's dead on arrival for EM.
4. **Look for UNTRIED combinations**: the most promising moves are combining two PARTIAL techniques to cover each other's gaps.
5. **Consider generalization**: if a technique almost applies, what generalization would make it apply? Check whether that generalization has been tried (dead-end catalog).

---

## Technique Families

### T1: Character Sum Methods

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T1.1 | Pólya-Vinogradov | Dirichlet character χ, sum over consecutive integers | \|∑χ(n)\| ≤ √q log q | INAPPLICABLE | — | EM sums are over walk positions w(n), not consecutive integers. Walk positions are a deterministic orbit, not a range |
| T1.2 | Burgess bound | Character χ, sum over short interval [M, M+N] | Sublinear character sums for N > q^{1/4+ε} | INAPPLICABLE | — | Same obstruction as T1.1: walk positions are not an interval |
| T1.3 | Large sieve inequality (additive) | Well-separated frequencies α_r, arbitrary coefficients a_n | ∑_r \|∑ a_n e(α_r n)\|² ≤ (N+R)·∑\|a_n\|² | PROVED (weak), OPEN (optimal) | #102 | Weak ALS proved. Optimal ALS blocked by GramOffDiagBilinearBound (Hilbert inequality). Single-frequency extraction gives nothing (#102) |
| T1.4 | Large sieve (multiplicative, prime modulus) | ALS + Parseval bridge | ∑_χ \|∑ a_n χ(n)\|² ≤ ... | PROVED | — | `als_implies_mls_prime` fully proved via Gauss sums + Parseval |
| T1.5 | Large sieve as sieve (IK §7.6) | Farey large sieve + Lemma 7.15 | Upper bound on sifted sets | CHAIN PROVED modulo ALS | — | Full chain: ALS → FareyLS → (+Lemma715) → LargeSieveAsSieve. Gap: GramOffDiagBilinearBound (relaxed to 1/δ in Session 130). Session 130 architectured full Hilbert → ALS chain with `hilbert_chain_als` PROVED |
| T1.6 | Halász theorem | MULTIPLICATIVE f: ℕ → ℂ with \|f\|≤1 | Mean value bound via pretentious distance | DEAD | #109 | EM walk character χ(w(n)) is NOT multiplicative in n. Pretentious distance is intrinsically Euler-product-based. No non-multiplicative extension exists |
| T1.7 | Van der Corput inequality | Sequence of unit vectors in Hilbert space | \|∑ u_n\|² ≤ ... via lag-h correlations | PROVED (h=1) | #38, #77 | VdC with h=1 gives O(N/√2), a constant fraction — SCALE MISMATCH. h≥2 requires joint distribution of consecutive multipliers = HOD |
| T1.8 | Weyl differencing | Exponential sums over polynomials | Sublinear bounds via repeated squaring | INAPPLICABLE | — | Walk positions w(n) are not polynomial in n. Differencing produces terms involving ratios of consecutive multipliers, which are uncontrolled |
| T1.9 | Vinogradov method | Exponential sums, mean value theorem | Bounds via major/minor arc decomposition | INAPPLICABLE | — | Requires sum over integers in an interval, not a deterministic orbit |
| T1.10 | Sum-product set growth (BKT) | Set A ⊂ F_p with p^δ < |A| < p^{1-δ} | max(|A+A|, |A·A|) ≥ |A|^{1+ε} | INAPPLICABLE (for DSL) | — | Bypasses Four-Way Blocker for SET CARDINALITY, but DSL needs visit MULTIPLICITY (character sums). BKT gives |V_K| → q-1 = SE (proved). Gap: Marginal/Joint Barrier. Session 136 |
| T1.11 | KBSZ criterion (Katai-Bourgain-Sarnak-Ziegler) | Bounded sequence a(n), dilate decorrelation a(pn)·conj(a(qn))→0 for distinct primes p,q | ∑ a(n)·ν(n) = o(N) for all bounded multiplicative ν | WRONG DIRECTION | #122, #123 | KBSZ proves orthogonality TO multiplicative functions. EM needs equidist OF a sequence (different problem). "Temporal KBSZ" = additive VdC (Bergelson-Moreira 2015). minFac not multiplicative (PROVED). COD = TWD relabeled. Session 197. **Extractor/LHL framework** (Session 199): NT-LHL = PE at population level. All extractors require H_∞ > 0; EM orbit H_∞ = 0 (CG impossibility). CRT-blind extractor = `crt_multiplier_invariance` (PROVED). Block source = TWD. Mauduit-Sarkozy closest analogue (requires multiplicativity). Category error |

### T2: Sieve Methods

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T2.1 | Selberg sieve | Sifting set A ⊂ [1,N], sifting primes P | Upper bound on S(A,P,z) = #{a∈A: p\|a ⟹ p≥z} | APPLICABLE (population) | — | Applies to population of squarefree integers. Gives Population Equidistribution (PE). Does NOT transfer to specific EM orbit |
| T2.2 | Bombieri-Vinogradov | Primes in arithmetic progressions, averaged over moduli | ∑_{q≤Q} max_a \|π(x;q,a) - x/φ(q)\| ≪ x/log²x | MATHLIB BLOCKED | #55, #56 | Not in Mathlib. Even if proved, gives SieveEquidistribution (population), NOT SieveTransfer (orbit). PNT+ project may eventually provide this |
| T2.3 | Elliott-Halberstam | Strengthening of BV: Q up to x^{1-ε} | Better range for equidistribution in APs | OPEN (major conjecture) | — | `ElliottHalberstam` stated as open Prop. `eh_chain_mc` PROVED. Would give MC if proved, but EH is a famous open problem |
| T2.4 | Linnik's theorem | Small least quadratic non-residue | n(p) ≪ p^L for some L | PROVED (trivially) | #39 | 4 = 2² is always a QR mod p≥5, so all odd primes have QNR ≤ 4. Sieve application proved but irrelevant to walk dynamics |
| T2.5 | Brun-Titchmarsh | Upper bound on primes in short APs | π(x;q,a) ≤ 2x/φ(q)log(x/q) | INAPPLICABLE | — | Bounds count of primes, not walk behavior. Population-level |

### T3: Equidistribution Theory

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T3.1 | Weyl criterion (finite groups) | Sequence in finite group G, all nontrivial characters | Equidistribution iff ∑χ(g_n) = o(N) for all χ≠1 | PROVED | — | `finiteWeylCriterion` proved. This IS CCSB when applied to EM walk. The question is proving the character sum bound |
| T3.2 | Erdős-Turán inequality | Sequence in [0,1), trigonometric sums | Discrepancy bound from exponential sums | INAPPLICABLE | — | Continuous version. Finite group version is T3.1 |
| T3.3 | Diaconis-Shahshahani | Random walk on group, convolution of conjugacy-invariant measures | Convergence to uniform in L² after O(log\|G\|) steps | DEAD | #86, #95 | Requires RANDOM walk (iid steps). EM walk is deterministic with different multiplier at each step. Spectral gap applies to distributions, not deterministic paths |
| T3.4 | Mixing time theory | Markov chain on group, transition matrix | Convergence to stationary distribution | DEAD | #110 | EM walk is not a Markov chain (multiplier depends on entire history). Transition matrix convergence IS CME (#110) |
| T3.5 | Population equidistribution | Density of squarefree n with minFac(n+1) ≡ a mod q | For most n, minFac is equidistributed mod q | PROVED (PE provable from standard ANT) | — | Population-level result. The gap from population to specific EM orbit is SieveTransfer / PopulationTransfer |
| T3.6 | Arithmetic dynamics equidistribution | Algebraic self-map f: V → V, orbit {f^n(x)} | Orbit equidistribution wrt canonical measure | INAPPLICABLE | #26, #89 | EM map involves minFac (not algebraic, not well-defined mod q). Four-Way Blocker leg 3. Silverman/Baker-Rumely require algebraic maps. Session 136 |

### T4: Fourier / Harmonic Analysis

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T4.1 | Parseval identity (finite groups) | Function on finite group G | ∑\|f̂(χ)\|² = \|G\| · ∑\|f(g)\|² | PROVED | — | `parseval_identity` proved. Used in ALS→MLS bridge |
| T4.2 | Plancherel theorem | Function on finite group G | Pointwise inversion from Fourier coefficients | PROVED | — | `plancherel_identity` proved |
| T4.3 | Gauss sum bounds | Primitive character mod q, exponential sum | \|τ(χ)\| = √q | PROVED | — | `gauss_sum_norm_sq` proved |
| T4.4 | Walk energy Parseval | Walk on (Z/qZ)×, character decomposition | ∑\|V(a) - N/(q-1)\|² = ∑_{χ≠1}\|S_N(χ)\|²/(q-1) | PROVED | — | Links visit discrepancy to character sums. Proved in LargeSieveAnalytic |
| T4.5 | Fourier identity for V(-1) | Walk hitting -1, character decomposition | V(-1)·(q-1) = N + ∑_{χ≠1} χ(-1)⁻¹·S_N(χ) | PROVED | #105 | This IS the CCSB-to-DH bridge. Using it to prove V(-1)>0 requires controlling all S_N(χ), which IS CCSB |
| T4.6 | Gram matrix / Dirichlet kernel | Exponential sums at separated frequencies | G_{r,s} = sin(Nπ(α_r-α_s))/sin(π(α_r-α_s)) | PROVED | — | `gramMatrix_norm_eq_sin_ratio` proved (Session 108). Packing bound (R-1)δ≤1 + improved ALS N+1/(2δ²) proved (Session 113). Session 113 analysis: Schur test on |G(r,s)| gives O(log R)/δ — inherent limitation (absolute values discard signed cancellation) |
| T4.7 | Hilbert inequality | Bilinear form ∑∑ a_r ā_s / (r-s) | \|∑∑\| ≤ π · ∑\|a_r\|² | OPEN (chain PROVED) | — | `HilbertInequality` stated as open Prop. **Session 130**: Full chain HilbertInequality → ALS architectured (`hilbert_chain_als` PROVED). Constants relaxed to 1/δ+N. **Session 131**: CscPartialFraction PROVED, CscBilinearImpliesGramOffDiag PROVED. **Session 134**: `hilbert_lifted_bound` PROVED (product-index trick application via `finProdFinEquiv`), `same_r_antisymmetry` PROVED (same-r terms vanish by swap), `hilbert_csc_circular_of_cesaro` PROVED (HI+CrossRCesaro→CscCircular). **3 sub-Props remaining**: HilbertInequality1 (hard, Oleszkiewicz), CrossRCesaroConvergence (Fejér+Cesàro), HilbertCscBilinearBridge (Cohen trick) |

### T5: Ergodic / Dynamical Methods

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T5.1 | Birkhoff ergodic theorem | Measure-preserving transformation, integrable function | Time average = space average a.e. | DEAD | #74 | EM walk is non-autonomous (different map at each step). Mathlib `BirkhoffSum` assumes orbit under SINGLE map |
| T5.2 | Furstenberg correspondence | Combinatorial structure in integers | Transfer to dynamical system, recurrence | DEAD | early | EM sequence is too structured. Correspondence gives no information beyond what group theory provides |
| T5.3 | Nonstationary ergodic theorems | Time-inhomogeneous random walk | Convergence under mixing conditions | DEAD | #86 | Monakov/Ito-Kawada require strictly aperiodic PROBABILITY measures AND independent steps. EM has Dirac mass steps |
| T5.4 | Spectral gap methods | Markov chain, reversible or expanding | Geometric convergence to equilibrium | DEAD | #95 | Spectral gap is for DISTRIBUTIONS converging. EM is a single deterministic path |
| T5.5 | Exponential mixing | Hyperbolic dynamics, SRB measures | Correlation decay at exponential rate | DEAD | #86 | EM has no hyperbolicity, no smooth structure, no measure |
| T5.6 | Bourgain-Gamburd expansion | Non-abelian quasirandom group, symmetric generating set, iid random steps | Spectral gap → equidistribution in O(log|G|) steps | DEAD | #86, #95 | (Z/qZ)× is ABELIAN: quasirandomness = 1 (worst case). Requires random iid steps. Breuillard (arXiv:2512.15364, Dec 2025) extends but requires semisimple groups. Session 136 |
| T5.7 | Dobrushin coefficient / non-homogeneous convergence | Non-homogeneous Markov chain with transition kernels K_n | ∏(1-α(K_n))→0 ⟹ forgetting of initial condition | DEAD | #90, #95, #110, #131 | Dobrushin coefficient α(K_n)=0 for ALL n (deterministic kernels are Dirac masses, TV distance=1 between distinct rows). MUB (weaker than CME, ∑(1-δ_n)=∞) is vacuous: achieving any δ_N<1 requires CME-strength equidist. Batching preserves Dirac (products of deterministic steps remain deterministic). Windowing=empirical CME. **Markov chain theory FULLY EXHAUSTED** (Sessions 145, 169, 172) |
| T5.8 | Furstenberg group extension / Schmidt essential range (cocycle non-coboundary) | Ergodic base system (Ẑ, +1), measurable cocycle Φ: Ẑ → Ẑˣ, compact abelian fiber | If Φ not coboundary: skew product ergodic ⟹ a.e. orbit equidistributes | DEAD | #74, #90, #95, #101 | Φ = minFac(·+1) is wildly discontinuous on Ẑ → no unique ergodicity (every orbit). EM orbit lives on Haar-measure-zero set → ergodic conclusions vacuous. Step-to-walk gap (#20, #117): cocycle = STEP property, DSL = WALK property. PhiNotCoboundary strictly WEAKER than CME (two gaps: orbit specificity + conditional transfer). MartingaleCME ill-defined for deterministic sequences. Tao-Collatz breaks at 3 points. **Session 291 (Scoping S-Φ)**: All 5 Schmidt hypotheses satisfied for System (A) but give PE only; System (B) cocycle circular; coboundary test = CCSB equivalence collapse; μ(L_p) = (1/p)∏_{q<p}(1-1/q); E[log Φ] = +∞ irrelevant for compact G. NO-GO-foundations (stronger than NO-GO-DSL). See `scoping/verdict_phi.md`. Sessions 181, 291 |

### T6: Probabilistic Methods

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T6.1 | Littlewood-Offord problem | Sum of random ±1 variables | Anti-concentration of sums | DEAD | #82, #83 | Reduces to Dec/HOD for cyclic groups. Inverse LO FALSE for d≥3 |
| T6.2 | Borel-Cantelli lemma | Sequence of events, independence or quasi-independence | Almost sure occurrence/non-occurrence | DEAD | #114 | Quasi-independence of death channels IS CME for single fiber |
| T6.3 | Second moment method | Random variable with known mean and variance | Concentration via Chebyshev/Markov | PARTIAL | #121, #122, #123 | Works at population level (PE, concentration hypotheses). Cannot constrain specific deterministic orbit. Per-class extension (SMSB+SE) dead: per-class density = CME (Dead End #121, Session 143). Temporal window extension (TWD) dead: multiplier-sum cross terms give Dec not CCSB (Dead End #122, Session 144). **FourPointPCV dead**: four-point cross-term factorization for K² fourth moment bound = HOD (#84). CRT provides cross-modulus independence, not cross-time independence (#98, #115). Strictly harder than CCSB. (Dead End #123, Session 146). Pigeonhole gives ∃ SOME class with small bad set, not ALL classes |
| T6.4 | Harper's BDH for general sequences | Non-multiplicative f with AP equidistribution | Variance asymptotics for partial sums | DEAD | #108 | EM products super-exponentially sparse, AP condition circular, gives variance not pointwise |
| T6.5 | Stochastic perturbation (ε-walk) | Noise schedule ε(n) with Σε=∞; |F_q|≥2 infinitely often | ε-walk captures every prime a.s. | PARTIALLY PROVED | #90, #95, #117 | Genuinely escapes #90 for stochastic variant only. Does NOT prove MC for deterministic walk. Spectral gap PROVED. Product contraction PROVED. Isometry PROVED. Selection counterexample PROVED (Session 207): fixed selection gives ‖χ(s)‖=1, no contraction. factorSetResidues defined + membership PROVED. Chain for det. walk has TWO gaps: (1) MinFacUnbiased = SelectionBiasNeutral = #90 (orbit specificity), (2) step-to-walk = #117 (|P_n|=1 always for deterministic path, no decay of cumulative products; product contraction applies to DISTRIBUTIONS not individual trajectories). ~654 lines. Sessions 205, 207 |

### T7: Algebraic Number Theory

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T7.1 | Chebotarev density theorem | Number field extension, Frobenius elements | Density of primes with given splitting type | **PARTIAL — abelian case AVAILABLE** | #9 | Session 298 (R-Inverse/C): for multiquadratic/cyclotomic (abelian) targets, Chebotarev DEGENERATES to Dirichlet mod `lcm(4\|d_j\|)` via quadratic reciprocity — a multiquadratic field is abelian and sits inside `Q(ζ_D)`. Mathlib's `Nat.forall_exists_prime_gt_and_eq_mod` suffices; verified in use by `CvdP.free_transition`. Only Kummer extensions `Q(ζ_k, ᵏ√a)`, `k ≥ 3` (Booker Lemmas 3–4), still need general Chebotarev (~5000+ lines) |
| T7.2 | Kummer theory | Cyclotomic extensions, p-th power residues | Splitting of primes by residue class | MATHLIB BLOCKED | #9 | Requires Chebotarev |
| T7.3 | Class field theory | Abelian extensions, Artin map | Reciprocity law for splitting | MATHLIB BLOCKED | — | Far beyond current Mathlib |
| T7.4 | Dirichlet's theorem on primes in APs | Characters mod q, L-functions | Infinitely many primes in each unit class (qualitative) | **AVAILABLE (qualitative)** | #55 | **CATALOG CORRECTION, Session 298.** IS in Mathlib: `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` — `Nat.infinite_setOf_prime_and_eq_mod` and `Nat.forall_exists_prime_gt_and_eq_mod (ha : IsUnit a) (n : ℕ) : ∃ p > n, p.Prime ∧ (p : ZMod q) = a`. The `∃ p > n` form is ideal: gives "prime in the class, larger than any bound" in one shot. **Verified twice independently**: used in a compiled proof by `CvdP.free_transition` (Task A), and located by source search (Task C). Quantitative/uniform (π(x;q,a) asymptotic, and BV-style uniformity) still ABSENT — do not conflate |
| T7.5 | Fargues-Fontaine / perfectoid / diamonds | p-adic Galois representations, local Langlands | Geometric framework for p-adic phenomena | DEAD | #128 | FF curve at single prime p, not adelic. No algebraic avatar for minFac. Slope analogy is category error (slopes = Newton polygon of phi-module, not prime valuations). Session 167 |
| T7.6 | Hecke orbit equidist (Clozel-Ullmo, Eskin-Mozes-Shah) | Fixed algebraic Hecke correspondence T_p on Shimura variety S; orbit {T_p^k(x)} | Equidist of Hecke orbit wrt Haar on S | DEAD | #128 | Requires FIXED correspondence (stationarity), algebraic variety (Shimura), Lie group structure (Ratner). EM fails all three: state-dependent multiplier, no algebraic variety, finite abelian group. Session 167 |
| T7.7 | Deligne equidistribution / monodromy (Weil II) | Family of varieties V_t → base B, l-adic sheaf F, geometric monodromy group G^geom | Frobenius conjugacy classes equidistributed in G^geom# | DEAD | #129 | Three independent kills: (1) FFLM (Gal(ffProd(n)+1) ⊇ A_d) likely FALSE — cyclotomic counterexample Φ₅(t) over F_2 has Gal=Z/4Z, not A₄. (2) Deligne = FAMILY statement — equidistributes Frobenius ACROSS fibers of family, not along single orbit. (3) Cycle type of Frobenius does NOT determine residue class of minFac. Maps to #90, #127. Session 168 |
| T7.8 | Number field extensions for integer walk | O_K for K/Q, prime ideal 𝔭 above r, character χ of (O_K/𝔭)× | χ restricted to integer walk = Dirichlet character mod r | PROVED IMPOSSIBLE | #135, #136 | **Universal Confinement** (Session 180): Z → O_K/𝔭 always factors through prime subfield F_r. ALL characters restrict to Dirichlet. Hecke Grössencharacters add growth factors |n|^s only. Kills: Gaussian (Z[i]), biquadratic (Q(i,√p)), cyclotomic, CM, Hecke, ALL K/Q |
| T7.9 | FF autonomous map / Φ₃ exclusion criterion | Perpetual irreducibility of ffProd(n)+1, degree-1 target Q over F_p | Walk for degree-1 targets follows f(w)=w(w+1) autonomously on F_p. Preimage of -1 = roots of Φ₃ | PROVED (structural negative) | #127, #129 | **Session 276**: For p≡2 mod 3, p≥5: Φ₃ has no roots in F_p (Lagrange: 3∤(p-1)), so -1 unreachable from any a≠-1. Excludes p-2 degree-1 targets simultaneously. EM/FunctionField/AutonomousMap.lean (225 lines, 14 theorems). Positive direction: p≡1 mod 3 may allow hitting -1 (cube roots exist). Extension to F_{p^d} for higher-degree targets UNTRIED |
| T7.10 | Reciprocity invariants (Kronecker/Jacobi symbols BETWEEN sequence data) | Real characters `χ_d`, `d` a fundamental discriminant built from ORBIT primes; Jacobi multiplicativity in the denominator | Max side: blocks primes (Cox–vdP 1968, Booker 2012, Pollack–Treviño 2014). Min side: nothing | **DEAD for min** (obstruction-killed, assessment-grade) | new TM entry, Session 298 | **Session 298 (R-Inverse/C).** The enrichment is NOT a new kind of invariant: by `jacobiSym.mod_right` + quadratic reciprocity it IS the congruence system at the growing modulus `Π_n = 8m·p_2⋯p_n`. **Character Non-Constancy Lemma**: a nontrivial real character is never constant on the primes above any bound (Dirichlet), but IS constant on suitable finite sets. maxFac confines the Euclid number's factor support to a FINITE set (characters can be constant ⟹ contradiction available); minFac confines it to a COFINITE set (never constant ⟹ no contradiction, ever). Euclid unit + parity laws are IMPLIED by forcing, not in tension with it. Escalation branch run explicitly and NEGATIVE (unconstrained cofactor `C` composed of primes > X). Blocking needs anatomy/smoothness, not symbols. Formalization plan ≈1100–1760 lines, `EM/Reciprocity/NoInvariant.lean`; first slice items 1–3+10 ≈330–500 lines |

---

## Decomposition Strategies

When facing a hard target H, try these decomposition patterns:

### D1: Fiber decomposition
Split ∑_{n=1}^{N} f(n) into ∑_{a ∈ G} ∑_{n: w(n)=a} f(n). This gives CME when applied to character sums. **Status**: explored, IS the CME approach.

### D2: Excursion decomposition
Split the walk into excursions (maximal segments between returns to a basepoint). Character sum over excursion k has modulus ≤ length of excursion. **Status**: explored, formalized in EM/Transfer/Excursion.lean. Blocked by EIP (excursion independence).

### D3: Block decomposition
Split [1,N] into blocks of length L. Apply VdC or Cauchy-Schwarz to each block. **Status**: explored. Block-level cancellation requires HOD or independence between blocks. **Session 144**: TWD (non-overlapping temporal windows + tail identity) confirmed as special case. TWD controls multiplier sums only (Dead End #122). Walk-sum version = HOD at block scale (#84). No new leverage from tail identity connection.

### D4: Dyadic decomposition
Split sum at scales N, N/2, N/4, .... Standard technique for converting pointwise to averaged bounds. **Status**: not deeply explored for EM. Could combine with T1.3 (large sieve) at each scale.

### D5: CRT decomposition
Factor q = q₁ · q₂ (coprime), work mod q₁ and mod q₂ separately. **Status**: explored. CRT surjectivity proved. Per-step independence does NOT give sequence-level independence (#98, #115). **Session 122**: CRT conditional independence (conditioning on genSeq n j = p) assessed at 4/10 — reduces to CRTPropagationStep, no bypass. `SquarefreeCRTIndependence` defined as the clean formulation of what's needed: mod-r and mod-q coordinates of genProd approximately independent over squarefree n. Infrastructure formalized in EM/Ensemble/CRTFreedom.lean (496 lines, 21 theorems).

### D6: Population → Individual transfer
Prove a statement for "most" starting points, then transfer to the specific EM orbit. **Status**: the PE → PT → CME chain. PE is provable; PT (PopulationTransfer) is open.

---

## Generalization Strategies

### G1: Weaken the target
Instead of CCSB (o(N) for ALL χ), try:
- o(N) for a DENSITY-1 set of χ → this IS CCSB (#93, equivalence collapse)
- O(N/log N) instead of o(N) → **EQUIVALENCE COLLAPSE (Session 116)**: O(N/f(N)) for any growing f(N) IS o(N). For fixed q, the Fourier identity needs (q-2)·max|S_N| < N, so any growing f(N) eventually overwhelms the constant (q-2). The weakest sufficient rate IS o(N) itself. Specifying a rate gives zero new leverage because the barrier is achieving ANY growing f(N), not a fast-enough one. The only non-trivial quantitative question is uniformity in q, which is MMCSB (already formulated, strictly stronger than CCSB, not needed for MC)
- CCSB for a cofinal set of primes q → already sufficient via Single Hit Theorem
- |S_N(χ)| ≤ (1-δ)·N for fixed δ → requires δ > (q-3)/(q-2), collapses to o(N) for large q. **ASSESSED Session 116**

### G2: Strengthen the hypothesis
Instead of trying to prove CME from nothing, assume:
- PE (Population Equidistribution) — provable by standard sieve → partial progress
- SE (Subgroup Escape) — proved (PRE) → used, not sufficient alone
- Growth conditions — SuperExponentialGrowth proved → used in SDDS framework

### G3: Change the setting (Grothendieck move)
Instead of (Z/qZ)×:
- Work in the profinite completion ∏_q (Z/qZ)× → explored, doesn't simplify (#101)
- Work in a function field analogue → **DEAD (Session 166)**: Weil bound provides population statistics only; orbit-specificity barrier (#90) applies identically. PE becomes unconditional (Weil is a theorem), but DSL gap is structurally identical. Dead End #127
- Work in p-adic geometry (perfectoid spaces, diamonds, FF curve, Hecke orbits) → **DEAD (Session 167)**: Every geometric equidist theorem requires FIXED algebraic correspondence or FIXED group action; EM has neither. FF curve is single-prime, not adelic. Slope analogy is category error. Dead End #128
- Use monodromy / Deligne equidistribution (Weil II) for FF-EM → **DEAD (Session 168)**: FFLM likely false (Φ₅(t) over F_2 counterexample). Deligne = family statement. Cycle type ≠ residue class. Dead End #129
- Work with a random model where EM-like sequences satisfy independence, prove the result there, then transfer → **PARTIALLY EXPLORED** (population equidistribution is this; the transfer step is the open gap)
- **ALL G3 sub-items are now CLOSED**: profinite (#101), function field (#127), p-adic geometry (#128), monodromy/Deligne (#129), random model (= PE→DSL gap)

### G4: Abstract the recurrence
Instead of a(n+1) = minFac(a(0)·...·a(n) + 1):
- Study SDDS (Sieve-Defined Dynamical Systems) abstractly → explored, formalized
- Study "any sequence where consecutive products grow super-exponentially and are pairwise coprime" → **PARTIALLY EXPLORED** (CoprimeCascade proved for ALL SDDS)
- Study "any orbit of a map on a finite group with the generation property" → **EXPLORED** (departure graph framework)

### G5: Interpolate between known and target
Find an intermediate condition X such that:
- Known results ⟹ X is easier to verify than CCSB
- X ⟹ MC is provable
**Status**: this IS the project's methodology. The current sharpest X is CME. Finding a weaker X that still implies MC and is more accessible is the live frontier.

---

## The Frontier (what might actually work)

Based on 115 dead ends and the Four-Way Blocker analysis, the only genuinely open directions are:

### F1: External infrastructure
- **Hilbert inequality** (T4.7): ~200-300 lines, elementary proof exists (Oleszkiewicz 1993). **Sessions 130-131**: Full chain architecture formalized + 2 of 4 open Props closed. Chain composition `hilbert_chain_als` PROVED. Constants relaxed to 1/δ+N (Cohen trick deferred). **2 open Props remain** (~280-420 lines total): HilbertInequality (~200-300 lines), HilbertCscBilinearBridge (~80-120 lines). CscPartialFraction PROVED (229 lines, Session 131), CscBilinearImpliesGramOffDiag PROVED (~173 lines, Session 131). Mathlib has: Jordan's inequality (`mul_le_sin`), cotangent Mittag-Leffler (`cot_series_rep`), operator norms. Not formalized in any proof assistant as of Mar 2026.
- **Bombieri-Vinogradov** (T2.2): would give SieveEquidistribution. Awaiting PNT+ project (v4.28.0, Feb 2026 — no BV yet). Mathlib-blocked.
- **Packing bound + improved ALS**: **PROVED (Session 113)**. 6 theorems, 189 lines. R-independent constant N + 1/(2δ²). Supersedes harmonic Schur row-sum approach.
- ~~Harmonic Schur row-sum~~: **Superseded by Session 113 packing bound**. Schur test gives O(log R)/δ at best — inherent limitation because absolute values discard signed cancellation. Packing bound gives 1/(2δ²) which is R-independent and stronger for typical parameters.

### F2: A "fifth way" past the Four-Way Blocker
Something that does not require independence, multiplicativity, algebraic-geometry, or ergodic stationarity. Must use the SPECIFIC structure of EM:
- The recurrence P(n+1) = P(n) · minFac(P(n)+1)
- The coprimality cascade (consecutive products pairwise coprime)
- Super-exponential growth
- The generation property (multipliers generate the full group)

No such technique is currently known in the literature. Monitoring for new developments.

### F3: Quantitative refinement of existing bounds
- Can the O(N/√2) from VdC h=1 be improved to O(N/f(N)) for some growing f(N) by exploiting EM structure? The standard VdC gives a constant fraction; any improvement requires EM-specific input.
- Can the population-level second moment be sharpened to give pointwise control? Standard Markov gives density-1, which is not enough for a single deterministic orbit.

### F4: New external mathematics
- Any theorem about minFac distribution conditional on modular structure
- Any equidistribution result for deterministic sequences on finite groups that does not require the Four-Way Blocker properties
- Any advance in the theory of non-stationary, non-random walks on finite groups

---

## Track Record

| Session | Proposal | Outcome | Advancement |
|---------|----------|---------|-------------|
| 298 (R-Inverse/C) | Reciprocity-class No-Invariant assessment | **EXTENDS**. Extracted the true max-side invariant from Booker §3 + Pollack–Treviño Prop. 5 (Jacobi symbol `(d/N_n)` evaluated top-down by reciprocity, bottom-up by denominator multiplicativity). Defined the min-side ind-system and proved the collapse *reciprocity ≡ congruence at growing modulus `Π_n`*. All three moves extend: EVICTION automatic (`N_n ≡ 1 mod R_n`), FULLNESS via two-prime construction needing only qualitative Dirichlet, CRT-REACH via Parity Correction. Escalation branch checked, NEGATIVE. **Mathlib correction: Dirichlet in APs IS available (T7.4 was stale)** | 0.6 |
| 298 (R-Inverse/D) | Simultaneous avoidance (Heath-Brown move) | **NO-MECHANISM**, as priced (prior 12%). But produced Finite Hitting as a by-product and showed `ShieldedHitting` is UNSATISFIABLE — an existing codebase dichotomy is degenerate. Decoupling identity: k-fold avoidance = conjunction of independent monotone conditions, no interaction term. Large-sieve budget (the real HB engine) mispriced by `2^N/N`. Key deflation: the tail confinement avoidance appears to force is UNCONDITIONAL, holding for present primes too | 0.5 |
| 81 | Harper BDH for EM | Dead end #108 (sparsity, AP condition circular) | 0 |
| 82 | Rough number concentration for d=2 NLR | Dead end #111 (coprimality insufficient) | 0 |
| 83 | Möbius death function leverage | Dead end #112 (geometry ≠ dynamics) | 0 |
| 85 | Hilbert inequality assessment | Assessed: feasible, ~200-300 lines, deferred | 0.3 |
| 86 | Systematic CME/ST review | Confirmed: all angles covered by 113 dead ends | 0 (but valuable: closure) |
| 86 | Gram bilinear → ALS | PROVED (`gram_offdiag_bilinear_implies_als`) | 1.0 |
| 87 | Parseval bridge for MLS | PROVED (`nontrivial_char_parseval_le`) | 1.0 |
| 88 | ALS → MLS prime | PROVED (`als_implies_mls_prime`) | 1.0 |
| 89 | Large sieve as sieve chain | PROVED (Lemma715 + LSAS chain) | 1.0 |
| 91 | Cycle product equidistribution | Dead end #113 (telescope absorbs products) | 0 |
| 97 | Missing prime accumulation | Dead end #114 (Borel-Cantelli = CME) | 0 |
| 108 | Gram sin ratio identities | PROVED (5 theorems) | 1.0 |
| 109 | Accumulating CRT independence | Dead end #115 (dimensional explosion illusory) | 0 |
| 110 | Visit energy variance check | Already proved (`excessEnergy_eq_visit_deviation`) — no new work | 0 |
| 111 | External literature scan + harmonic row-sum assessment | No new external input. Harmonic row-sum: 4/10, ~60-90 lines | 0.1 |
| 113 | Packing bound + improved ALS (formalizer) | PROVED: 6 theorems, 189 lines. R-independent ALS constant N+1/(2δ²) | 1.0 |
| 113 | GramOffDiagBilinearBound bypass assessment | Confirmed: Hilbert inequality inescapable for optimal ALS. Schur test has inherent log R factor | 0.2 |
| 116 | G1 quantitative CCSB O(N/log N) assessment | Equivalence collapse: O(N/f(N)) IS o(N) for any growing f. No new leverage | 0 (closes G1 UNTRIED) |
| 121 | JSE → SD reduction | Lean formalization of joint step equidistribution → step decorrelation. 5 theorems proved, JSE sole remaining gap | 1.0 |
| 122 | CRT conditional independence → SD strategy | ConditionalCRTPropagation ≡ CRTPropagationStep (same difficulty). Rated 4/10 for bypassing barriers. Infrastructure value: SCRTI conceptual clarity | 0.3 |
| 125 | DSL from cofactor identity (5 angles) | All 5 angles map to existing dead ends (#103, #110, #105, #93, #104). Cofactor/multiplier bijection means no distributional advantage. DSL algebraically exhausted from this angle | 0 |
| 129 | Comprehensive DSL strategy assessment (4 directions) | All 4 map to existing dead ends. (1) DSLInfra (EM/Reduction/DSLInfra.lean) identities: active-fiber selection gap = Marginal/Joint Barrier. (2) Cofactor completeness: bijection exhausted. (3) Weyl/exponential sums: require polynomial/interval structure (Four-Way Blocker). (4) +1 shift additive combinatorics: sum-product gives population mixing = PE, transfer requires independence. External lit scan (March 2026): nothing new. PNT+ still pre-BV | 0 (confirms exhaustion) |
| 130 | Hilbert → ALS chain architecture + GramOffDiag relaxation | PROVED: `hilbert_chain_als` (chain composition). 4 new defs, 5 definitions relaxed (1/δ+N-1 → 1/δ+N). Cohen trick deferred. Mathlib assessment: `cot_series_rep` + `mul_le_sin` available. +103 net lines, 0 sorry | 1.0 (architecture + proved composition) |
| 131a | CscPartialFraction (formalizer) | PROVED: `csc_partial_fraction_proved` (229 lines). Even/odd splitting of cot series + ℂ→ℝ bridge + ℕ→ℕ⁺ conversion. 8 helper lemmas. Key APIs: `cot_series_rep'`, `Complex.hasSum_ofReal`, `HasSum.even_add_odd`, `Equiv.pnatEquivNat` | 1.0 |
| 131b | CscBilinearImpliesGramOffDiag (formalizer) | PROVED: `csc_bilinear_implies_gram_offdiag_proved` (~173 lines). Dirichlet kernel factorization + phase absorption + triangle inequality. 5 helper lemmas: `eAN_sub_one_factor`, `eAN_half_sub`, `gramMatrix_mul_two_I_sin`, `l2NormSq_mul_eAN`, `hsin_ne`. Key technique: d_r = b_r·eAN(phase_r), Gram form = (Sd-Sd')/(2I), triangle ineq | 1.0 |
| 132 | hilbert_rescale + product-index infrastructure | PROVED: `hilbert_rescale` (HI1→HI by δ-rescaling). Product-index lifting: liftedPts, liftedCoeffs, separation lemmas. IsCircularSpaced predicate. +867 lines, 8 new definitions | 1.0 |
| 133a | MittagLefflerCsc (formalizer) | PROVED: `mittag_leffler_csc_proved` (~284 lines). ℂ→ℝ bridge via isometry embedding, even/odd splitting via HasSum.even_add_odd, half-angle relation, cot(a)-cot(2a)=1/sin(2a). Key APIs: tendsto_logDeriv_euler_cot_sub, Summable.alternating, tsum_congr, tendsto_nhds_unique | 1.0 |
| 133b | HilbertInequality1 literature scout | Assessed: ALL approaches ≥500 lines (toeplitz 2π≠π, Fourier L² missing, Beurling-Selberg 1500+, Schur divergent rows). Recommend leave as open Prop | 0 (but valuable: confirms infeasibility) |

| 134 | Product-index trick (formalizer) | PROVED: `hilbert_lifted_bound` (HI→lifted bound via `finProdFinEquiv`), `same_r_antisymmetry` (same-r vanish by j↔l swap), `hilbert_csc_circular_of_cesaro` (HI+CrossRCesaro→CscCircular). NEW open Prop: `CrossRCesaroConvergence`. +174 lines, 0 sorry | 0.7 (algebraic parts proved, analytical gap remains) |
| 135a | CrossRCesaroConvergence (formalizer) | **PROVED**: `cross_r_cesaro_convergence_proved` (~490 lines). Fejér sum identity by induction, parity via `neg_one_pow_congr`, ML Cesàro convergence, per-pair limit, F(K) decomposition (same-r=0, cross-r factors), assembly via `tendsto_finset_sum` + `le_of_tendsto'`. **Closes CrossRCesaroConvergence open Prop**. | 1.0 |
| 135b | Circular-spacing bypass assessment (analytic) | Feasible: ~460 lines of copy-adapt. Thread `IsCircularSpaced` through GramOffDiag → ALS → MLS/Farey. All downstream apps (Farey fractions, unit points) are circularly spaced. Eliminates `HilbertCscBilinearBridge` entirely. Constant weakening absorbed. | 0.8 (assessment complete, implementation pending) |
| 136 | Sum-product approach to DSL (4 questions) | All 4 angles map to existing barriers. (Q1) BKT set growth = SE (proved), gap = Marginal/Joint Barrier. (Q2) Arithmetic dynamics: Four-Way Blocker leg 3. (Q3) BG expansion: non-abelian + random required (#86, #95). (Q4) Coset equidist = equivalence collapse to DSL. Breuillard (Dec 2025) non-abelian only. T1.10, T3.6, T5.6 added | 0 (confirms: set-theoretic methods cannot reach DSL) |
| 137 | Population second moment E_2(K,X) via sieve methods (5 questions) | E_2 = CharSumVarianceBound (existing open hyp). ALS/MLS: wrong averaging variable (#102 analogue). Selberg sieve: genMult not separable. BV: marginal only (PE), cross-terms blocked by nonlinear minFac. Even if proved, 2 gaps to MC (#90, #58). Feasibility 3/10 | 0 (confirms: sieve methods insufficient for EM-specific cross-terms) |

| 143 | SMSB + SE per-class escape (BSE collapse analysis) | Dead end #121 (EQUIVALENCE COLLAPSE — BSE requires orbit-specificity = CME, Marginal/Joint Barrier) | 0 (confirms: per-class density control from marginal bounds impossible without CME) |
| 144 | Tail Window Decorrelation (TWD) assessment | Dead end #122 (EQUIVALENCE COLLAPSE — TWD gives Dec at best via multiplier sums; block decorrelation for walk sums = HOD/CME at coarser scale) | 0 (confirms: temporal block averaging cannot bypass Marginal/Joint Barrier) |
| 146 | FourPointPCV feasibility (tail identity attack) | Dead end #123 (EQUIVALENCE COLLAPSE — four-point population mixing = HOD (#84). CRT cross-modulus ≠ cross-time (#98, #115)). Attack plan conflated cross-modulus SCRTI with cross-time independence. FourPointPCV strictly harder than CCSB. Literature: Tao-Teräväinen "pairwise implies higher" requires multiplicativity, no non-multiplicative analog exists | 0 (confirms: higher-moment approaches cannot bypass Marginal/Joint Barrier) |

| 148 | ANT chain architecture (WeightedPNTinAP → PE) | Architecture document: 4 steps identified, compressed route saves 500-900 lines. EM/Population/Tauberian.lean CREATED by formalizer (281 lines, 0 sorry). DirichletPrimesInAP PROVED. Tsum identity + upper bound companion PROVED. SieveDensityAxiom mitigation for sieve step. Total remaining: ~700-1300 lines | 0.7 (architecture + formalizer delivery in same session) |
| 151 | PrimePowerStripping PROVED | `prime_power_stripping_proved` in EM/Population/Tauberian.lean (~275 lines). Fiber decomposition by minFac + geometric series + summability. WPNT → PrimeLogSumEquidist. Literature scout: Tao-Teräväinen Dec 2025 blocked by multiplicativity. Four-Way Blocker unchanged. | 0.8 (formalizer proved PPS, literature confirmed no new openings) |
| 152 | DSL brainstorm: 3 proposals (Multiset BSG+SE, Entropy/MI, Non-abelian lift) + literature scan | All 3 map to existing barriers. Multiset BSG closest to novel (2/10) but blocked by set-vs-multiset gap = Marginal/Joint Barrier. Entropy = DSL repackaging (1/10). Non-abelian lift = BG requires randomness (1/10). Lit scan: Tao-Teräväinen Dec 2025 (multiplicativity blocked), Gowers inverse all abelian groups (HOD blocked), no new deterministic walk results. Four-Way Blocker unchanged | 0 (confirms exhaustion; literature scan negative) |

| 157 | DSL deep dive: 5 questions (FPM=Dec, intermediate H, cofactor, external, fresh primes) | All 5 resolved negatively. FPM = Dec (not CME). No intermediate H exists. Cofactor dead (Session 125). No new external math. Fresh-prime = PBI+SE. All map to existing dead ends (#20, #58, #90, #93, #98, #103, #104, #105, #107, #110, #115, #117, #120, #122, #123) | 0 (confirms exhaustion; valuable for closure) |

| 158 | Fiber autonomy + CRT spreading + multi-modulus Borel-Cantelli | All 5 questions resolved negatively. Fiber autonomy = CRT invariance restated (zero new content). Multi-modulus ≠ cross-time (#123). CRT spreading = PE (#98). Borel-Cantelli gap = #90. FiberOrbitEscape strictly stronger than DSL. EM/Ensemble/FiberAutonomy.lean created (structural only) | 0 (confirms: fiber decomposition provides no new leverage for DSL) |
| 246 | FEH viability assessment (Q1-Q5): pop vs orbit, sieve theory, dead end mapping, structural levers, retreat | **5/10 overall**. FEH genuinely weaker than DSL (existential + omega growth amplification). Partially maps to #90 but ALL-factors gives ~2^n/n escape chances per step (NEW). LSD+BC heuristic strong. Ensemble FEH (6/10) best retreat. Odoni negative signal (Sylvester density-zero). No new dead end. | 0.3 (assessment clarifies FEH's unique position; no proved theorems) |
| 248 | PSCD sieve chain: PEAP → FCD → sieveProduct vanishing → PSCD → a.a. mixed hitting | Decomposed PSCD into 3 standard ANT open Props: PEAPImpliesFCD (partial sums→series bridge), SieveUpperBound (fundamental lemma), SieveProductVanishing (product_contraction_tendsto + reindexing). Composition theorem `fcd_sub_spv_implies_pscd` fully PROVED. +251 lines, 0 sorry. SieveProductVanishing closest to provable (product_contraction_tendsto already proved). | 0.8 (composition PROVED, 3 clean open Props, all standard ANT) |
| 160 | "1 mod growing S" sieve constraint + SubProd(n) + BV-level analysis | All 6 components assessed: 5 map to existing dead ends (#90, #98, #108). SubProdDecorrelation = SD for different population (incomparable, same difficulty). BV = average estimates = PE only. Coupling circular (= DSL). Hypercube Fourier (T5.8 in algebraic catalog): genuinely new but high total influence kills exponential concentration, noise sensitivity COUNTERPRODUCTIVE for orbit specificity. EM/Transfer/SieveConstraint.lean formalized as infrastructure (261 lines, 21 theorems, 0 sorry) | 0.3 (infrastructure only; attack direction confirmed dead) |
| 161 | CrossModulusDecorrelation (CMD) — adelic picture, joint character sum across two moduli | DEAD (0/10). CMD = Dec at composite modulus qr (not new). CMD→CCSB(qr) blocked by multiplier→walk gap (#20, #58, #117). DSLCMD = DSL at larger modulus (#90). Two-modulus structure adds zero content (#98, #123). All 3 proposed legs independently killed. No Lean code warranted | 0 (confirms: cross-modulus product characters provide no new route to MC) |
| 163a | CRTFiberImpliesMWI Fourier inversion proof (formalizer) | PROVED: `crt_fiber_implies_mwi_proved` (~145 lines). Key: MulChar.equivToUnitHom bijection, MulChar.coe_toUnitHom coercion bridge, Fourier expansion via char_indicator_expansion. EM/Adelic/Equidist.lean 417→656 lines | 1.0 |
| 163b | Walk autocorrelation ↔ MME (formalizer) | PROVED: `mme_iff_walk_autocorrelation`. Uses walk_shift_one_correlation + RCLike.norm_conj. Clean 22-line proof | 1.0 |
| 163c | CPD → CRTFiber feasibility (analytic agent) | Assessed 6/10. Obstruction: orbit-dependent Fourier coefficients c_ψ(r) = ∑ χ(mult_q)·conj(ψ(walk_r))/N are non-universal. CPD gives pairwise decorrelation but Fourier coefficients need product-over-primes factorization | 0.3 (assessment only) |
| 163d | CCSB+CPD → UPE pairwise-vs-kwise analysis (analytic agent) | Confirmed HARD. Pairwise ⊬ mutual independence in general. Counter: pairwise uniform random variables that are jointly non-uniform (XOR construction). No generic induction works | 0 (confirms: known hard, no route identified) |
| 163e | FLE vs SE+PRE exploration | Gap confirmed: FLE (cofinal visits to every element) is strictly stronger than SE (subgroup generation) and EMPR (single-element recurrence). SE+PRE are algebraic, FLE is dynamical. No proof from existing infrastructure | 0.2 (closes open question about docstring) |
| 164 | CCSB+CPD → UPE via CompositeCSB / Hölder induction | **Dead End #125**: XOR counterexample decisive — three unit-modulus sequences with all pairwise cancellation but triple product = N. No inequality (C-S, Hölder, VdC) bridges pairwise to k-wise. Tao-Teräväinen requires multiplicativity. Session 163's 8/10 estimate was INCORRECT (actual: 2/10). CCSBCPDImpliesUPE is UNPROVABLE from stated hypotheses | 0 (closes CCSBCPDImpliesUPE) |
| 166 | Function field analog of EM over F_p[t] + Weil bound | **Dead End #127**: Weil bound provides POPULATION control only (irreducibles equidistributed mod Q). Walk sum S_N is sum of PRODUCTS of χ-values — not a standard character sum. Orbit-specificity (#90) identical. PE becomes unconditional but DSL gap unchanged. Four-Way Blocker applies with same force. Conceptual clarity: hard part is orbit specificity, not ANT. G3 function field UNTRIED → DEAD | 0 (closes G3 function field; valuable conceptual insight) |
| 167 | p-adic geometry (Hecke orbits, FF curve, perfectoids, diamonds) for DSL | **Dead End #128** (TECHNIQUE MISMATCH — every geometric equidist theorem requires fixed algebraic correspondence; EM walk has state-dependent non-algebraic multiplier). All 5 questions resolved negatively. Maps to #86, #90, #95, #101, #127, Four-Way Blocker legs 3+4. EM/Advanced/Diamonds.lean created (340 lines, 7 theorems, 0 sorry). G3 p-adic geometry → DEAD | 0 (closes G3 p-adic geometry; infrastructure value for expert consultation) |
| 168 | FF-EM Monodromy / Deligne equidistribution (FFLM → FF-CME) | **Dead End #129** (TECHNIQUE MISMATCH — Deligne is family/population, FFLM likely false). Cyclotomic counterexample: Φ₅(t) over F_2 has Gal=Z/4Z, not A₄. Three independent failure modes. EM/FunctionField/Analog.lean extended 360→886 lines (4 proved theorems, 8 new defs). T7.7 added. G3 monodromy → DEAD | 0.3 (infrastructure: Polynomial.Gal integration, degree lemmas proved; dead end confirmation closes monodromy direction) |
| 169a | Doeblin/Dobrushin convergence for EM walk (5 questions) | ALL 0/10. DoeblinConvergenceForEM = CME by `rfl` (#110). QuantitativeDSL strictly STRONGER than DSL. MultiplierApproxUniform = DSL (Dirac mass). Spectral gap = stronger CME. Quantitative Markov bound = DSL in any coherent formulation | 0 (confirms: Markov chain convergence theory reformulates CME, no new leverage) |
| 169b | Multiplicative large sieve for EM orbits (5 questions) | ALL 0/10. Standard large sieve gives average-over-q only (#90, #108). minFac not multiplicative (#109, Four-Way Blocker item 2). Sieve orbit indicator = SieveTransfer gap (#90). CRT cross-modulus ≠ cross-time (#123). No pointwise sieve oracle exists (Artin's conjecture analogy) | 0 (confirms: multiplicative sieve methods inapplicable due to non-multiplicativity + orbit specificity) |
| 169c | EM/Advanced/MarkovSieve.lean (formalizer) | PROVED: 16 theorems, 520 lines. `doeblin_eq_cme` (rfl), `sieve_orbit_eq_ccsb` (rfl), `qdsl_implies_dsl`, `spectral_gap_implies_doeblin`, `minFac_not_multiplicative`, `markov_sieve_landscape` (7-route conjunction). Key collapses: Doeblin=CME, SieveOrbit=CCSB, QDSL⊃DSL | 0.5 (formalization of dead end landscape — documentary value + 2 definitional collapses) |

| 170 | FF-MC infrastructure (4 files, 2302 lines); SelectionBias dead (#130) | PROVED: EM/FunctionField/Bootstrap.lean (438 lines, FFDH+finiteness⇒FF-MC), EM/FunctionField/SubgroupEscape.lean (552 lines, Weil SE for p>(d-1)²), EM/FunctionField/CyclicWalkCoverage.lean (549 lines, abstract walk coverage), EM/FunctionField/MultiplierCCSB.lean (763 lines, 4-route FF-MC landscape). Dead End #130: SelectionBiasNeutral=ConditionalCharEquidist=FF-CME=CME by rfl. Equivalence collapse + fiber variety not algebraic. 0 new content. | 1.0 (infrastructure delivery) + 0 (dead end confirmation) |
| 172 | Dobrushin coefficient / MUB + stopping-time perspective (3 questions) | **Dead End #131** (TECHNIQUE MISMATCH — α_n=0 for deterministic walks, MUB vacuous, stopping-time=repackaging). EM/Advanced/Dobrushin.lean CREATED (704 lines, 0 sorry): `cme_implies_mub` PROVED, `dead_end_131_witness`, landscape theorem. T5.7 added. Markov chain theory now FULLY EXHAUSTED | 0.5 (formalization of dead end landscape + 1 proved reduction cme_implies_mub) |

| 173 | L-function perspective on DSL (EM-specific Dirichlet series) | **Dead Ends #132-134** (3 dead ends in one session). #132: L-function factorization circular (L_{non-EM} zero-free requires MC). #133: Self-similar FE mismatch (Lapidus inapplicable — tail orbit ≠ scalar multiple). #134: No Tauberian lever (L_{EM} entire for Re(s)>0 — no pole). EM/Advanced/LFunction.lean CREATED (447 lines): `accum_reciprocal_summable`, `log_ratio_irrational`, `em_self_similar_decomposition` all PROVED | 0.5 (3 dead end confirmations + 3 proved theorems) |
| 180 | Universal Confinement Theorem (number field extensions for integer walk) | **Dead End #136** (PROVED IMPOSSIBLE). Z → O_K/𝔭 always factors through prime subfield F_r. ALL characters of (O_K/𝔭)× restrict to Dirichlet characters mod r on integer walk. Hecke Grössencharacters add archimedean growth factors |n|^s only. Kills ALL K/Q simultaneously: Q(i), Q(i,√p), cyclotomic, CM, arbitrary. T7.8 added. EM/GaussEM/GaussConfinement.lean CREATED (347 lines, 31 theorems, 0 sorry) | 0.3 (formalization of universal negative result + dead end closes all number ring approaches) |
| 181 | Φ = minFac(·+1) classification (cocycle, carry function, martingale, Collatz) | All 5 angles map to existing dead ends (#74, #90, #95, #101). PhiNotCoboundary = population only (two gaps below CME). MartingaleCME ill-defined for deterministic sequences. Tao-Collatz breaks at 3 independent points. Step-to-walk gap (#20, #117) kills cocycle approach. No new dead end warranted. T5.8 added. No Lean code | 0 (confirms: ergodic/dynamical reformulations cannot bypass orbit-specificity barrier) |
| 182 | Furstenberg q-adic strategy (HigherPRE + additive walk via q-adic log) | **Pre-flight ABORT**. HigherPRE provable (70%) but 0% MC utility — all reductions factor through (Z/qZ)× level. Additive walk via log_q: 1+qZ_q → qZ_q is ISOMORPHISM — preserves all barriers. Increments v_j = log_q(seq(j+1)) are minFac-derived, no polynomial structure → Four-Way Blocker leg 3. Session 182 = Session 181 repackaged at Z_q× level. Maps to #90, #101, #128. No Lean code | 0 (pre-flight assessment confirms: q-adic reformulation is isomorphism of difficulty) |
| 183 | Ratner route: Reconvergence / algebraic rigidity / orbit-specific equidist literature | **Pre-flight ABORT**. Reconvergence Lemma FALSE (butterfly sensitivity — changing one multiplier cascades through all future steps via minFac). Even weakened version = `walk_readout_from_multipliers` (proved). Literature search: ZERO applicable orbit-specific equidist results (all require polynomial/unipotent/random/multiplicative structure). Four-Way Blocker confirmed at literature level. Cyclotomic = CRT invariance. Energy = CME circular. Maps to #4, #90, #101, #130. No Lean code | 0 (Reconvergence Lemma falsified; literature confirms Four-Way Blocker is universal) |
| 184 | Basin of Attraction / Confluence / Orbit Thickness / "EM as generic point" | **Pre-flight ABORT**. Confluence basin = `genProd_restart` (proved). BCPDensity = CME (user's own calculation). Orbit thickness = MC restated (walks from seq(k) collecting earlier primes IS MC). "Tail Theorem" = `genProd_restart` + `genSeq_restart` (already proved, no new theorem). All non-circular versions vacuous. Maps to #4, #90, #101, #130. No Lean code | 0 (confirms: "EM orbit as attractor" perspective provides zero new leverage — all content already captured by existing infrastructure) |

| 187 | PSDIVBImpliesVarianceBound (formalizer) | **PROVED**: `psd_ivb_implies_variance_bound_proved` (~127 lines). Variance decomposition identity + finite threshold assembly via Finset.sup. Key: ε=1/(K²+1), nlinarith on (K-1)²≥0. Supporting lemmas: sfAvg_const_mul, sq_sum_eq_double_sum, sfAvg_double_sum, variance_eq_double_sum_cov. Simplified chains psd_chain_implies_concentration' and psd_implies_rsd' (3 hypotheses instead of 5). ChebyshevConcentration: achievable but not completed (quantifier nesting analysis) | 1.0 (main bridge proved) |

| 197 | KBSZ / CrossOrbitDecorrelation (COD) / temporal KBSZ for DSL | **Pre-flight ABORT**. COD = TWD (#122) relabeled. KBSZ is wrong-direction tool (proves orthogonality TO mult functions, EM needs equidist OF a sequence). Temporal KBSZ = additive VdC (Bergelson-Moreira 2015). Fiber refinement = #90. Borel-Cantelli = FourPointPCV (#123). Literature: KBSZ (Katai 1986, BSZ 2013), Sarnak conjecture — all require multiplicativity of target. No new dead end — all components map to #20, #84, #90, #117, #122, #123 | 0 (confirms: VdC/KBSZ framework already exhausted; new label on TWD + FourPointPCV) |

| 199 | MinFac as Number-Theoretic Extractor (LHL / block source / CRT affine source) | **Pre-flight ABORT**. Category error: all extractors require min-entropy > 0; EM orbit has H_∞ = 0 (deterministic). CG impossibility theorem decisive. NT-LHL = PE (population level). CRT-blind extractor = `crt_multiplier_invariance` (proved). Block source sequential = TWD (#122). Mauduit-Sarkozy closest analogue but requires multiplicativity (Weil bounds). Literature: Gabizon-Raz, Dvir, Kamp-Zuckerman — all require entropy. Mathlib extractor infra = 0/5. Maps to #90, #109, #117, #122, #130 | 0 (confirms: extractor/LHL framework is category error — random-source tools inapplicable to deterministic sequence) |
| 200 | Number-Theoretic Blum-Micali (NTBM) — 7-axiom ADS framework, fixed-point bootstrap, CRT-blindness compounding | **SUBSUMPTION**: Axioms 1-5 = existing proved/open infrastructure. Axiom 6 = CrossPrimeDecorrelation (already defined). Axiom 7 = population-level correlation decay (#90). Fixed-point = CPD+MME→CME (already proved in EM/Adelic/Equidist.lean). "Compounding" = population-to-orbit transfer = DSL = #90. BM analogy structurally inapplicable (computational vs arithmetic, no reduction theorem). Literature: Tao Collatz parallel (5/10 for AccumMod3LB only — backward dynamics for population density, not orbit). Lacunary theory wrong variable direction. PRG/GL/hardcore all need entropy/computational hardness. Zero new mathematical content for MC | 0 (complete subsumption by existing infrastructure; Tao Collatz noted as marginal lead for AccumMod3LB ensemble question only) |

| 201 | Death density absorption mechanism → weak MC landscape collapse | PROVED: 13 theorems (CRT.lean +107, FirstMoment.lean +141). `genProd_mod_zero_absorbing`, `death_then_never_death_again`, `DecayingSMLB`, `decaying_smlb_implies_fmd`. AccumMod3LB/FMS/SMLB/LMG likely FALSE (absorption drains death density at every prime). FMD true but insufficient for PRSD | 0.8 (infrastructure: absorption mechanism + divergence hierarchy proved; strong negative finding: weak-MC chain collapsed) |
| 202 | Spectral Genericity (ensemble Fourier + Artin's conjecture for n=2) | **Pre-flight ABORT**. H1 (spectral decay) strictly STRONGER than CME. H2 (ord_M(2) large, Artin) UNUSED by argument. Cauchy-Schwarz discards phases ψ(2) → trivial bound. Fourier expansion = fiber decomposition in EM/Adelic/Equidist.lean. Konyagin-Shparlinski/BGK closest literature (χ(g^n) cancellation) but EM walk ≠ g^n. Arithmetic of 2 noted as genuinely untried direction but no mechanism found | 0 (H1 wrong direction; H2 unused; Fourier = existing fiber decomposition) |
| 203 | PSD from CRT ensemble (representation-theoretic orthogonality, hypercontractivity, influence decay) | **ABORT**. Maps to #123 (cross-time ≠ cross-modulus CRT). Rep theory fails (A, B nonlinear on all CRT coords). Hypercontractivity: KLLM 2024 requires 3 extensions (varying alphabets, deterministic map, Cov bound). Influence gives O(log(k-j)) NON-DECAYING. Literature: 0 applicable results; "influence decay under iterated self-maps on product spaces" is an OPEN PROBLEM. Four-Way Blocker applies (legs 2,3 untouched by ensemble) | 0 (confirms: PSD faces same barrier as CME; influence calculation O(log(k-j)) is only new quantitative content — heuristic, not proved) |
| 204 | Mutual exclusivity at same prime for PSD (winning-prime exclusion, Alladi race model, lag decay, negative correlation) | **ABORT**. THREE fatal flaws: (1) Conditional independence failure — conditioning on m_j=p constrains ALL CRT coordinates, not just n mod p; conditional dist of m_k ≠ Alladi-minus-p. (2) Calculation circular — uses unconditional χ(m_k) cancellation as input. (3) Case 1 = `death_then_never_death_again` (PROVED in CRT.lean); Case 2 = Dead End #123. "Fresh chance" lag decay false (permanent absorption). Literature: Negative Association framework (Joag-Dev-Proschan 1983) is right language but proving NA = proving PSD. Only new content: negative correlation sign (qualitative, not a bound) | 0 (maps to proved absorption + Dead End #123; no new mathematical leverage) |
| 207 | VanishingNoise bridge: factor set definitions + selection counterexample + MinFacUnbiased assessment | EM/Advanced/VanishingNoise.lean extended 437→654 lines (+217). `factorSetResidues` defined (prime factors of P(n)+1 as ZMod q residues). `multZ_in_factorSetResidues` PROVED. `factorSetResidues_nonempty_at_death` PROVED. **Selection counterexample PROVED**: `selection_no_contraction` (‖χ(s)‖=1 for any single s∈S), `selection_vs_average_gap` (averaging contracts < 1, but selection = 1). **MinFacUnbiased = SelectionBiasNeutral** (#90, confirmed). TWO gaps in det. chain: (1) MFU=#90, (2) step-to-walk=#117 (|P_n|=1 always, product contraction applies to distributions not paths). `vanishing_noise_landscape_v2` (5-clause conjunction, PROVED). Stochastic variant (5% genuinely new) only works for random walk, not det. EM | 0.5 (infrastructure: 7 new theorems, 217 lines; negative finding: 2-gap analysis clarifies VanishingNoise chain cannot close for det. walk) |

| 216 | Tao backward dynamics transfer for EM (MSI(p^k) + backward counting + mixing + diagonal argument → a.a. GenMC) | **SUBSUMPTION**: MSI = `MinFacSelectionIndependence` (CRT.lean:832). Backward counting = `CRTPropagationStep` (CRT.lean:216). Mixing = Dead End #95 (random walk, not deterministic). Error non-accumulation = Dead End #123 (cross-time ≠ cross-modulus CRT). R_K(c,a) depends on joint CRT distribution of EM accumulators, not just residue class c. Tao's Collatz works because Syracuse has 4 essential properties: (E1) CRT-independent kernel, (E2) entropy surplus, (E3) affine structure, (E4) universal kernel. EM has E1 (partial), E2 (yes), but LACKS E3 (multiplicative, not affine — no Syracuse random variable analog) and E4 (kernel orbit-dependent — accumulators structured, not generic). Siegel (2020, 2024) only generalization: Hydra maps, ALL require affine structure. Even if successful: gives a.a. GenMC ≠ MC | 0 (complete subsumption by CRT.lean; closes Tao-Collatz adaptation permanently) |
| 218 | Phase Transition Characterization of MC (EM/Advanced/VanishingNoise.lean Part 24) | PROVED: 8 theorems, 2 defs, +271 lines. `constEpsCharProduct` (constant-ε char product), `cesaroCharAvg` (Cesàro average). Part B: `constEpsCharProduct_norm_one_at_zero` (critical point ε=0, product norm ≡ 1). Part A: `constEpsCharProduct_tendsto_zero` (mixing ε>0, norm → 0 via finite-range trick + sparse contraction). `charProduct_norm_one` (unit-modulus product). `phase_transition_landscape` (4-clause). MC = Cesàro cancellation of unit-modulus phases at critical point. **Stochastic ε-walk framework now architecturally COMPLETE** (Tiers 1-3 all done). Do NOT extend further | 0.7 (infrastructure: 8 new theorems, 271 lines; structural insight: phase transition characterizes MC as critical ε=0 behavior; no new attack vector opened) |

| 225 | Tower contraction bound for TreeContractionAtHalf (Biggins martingale, iterated conditional expectation, MFRE transfer) | **ABORT (2/10)**. Tower bound NOT provable: triangle inequality gives convex combination (1/2)‖T_L‖+(1/2)‖T_R‖, not product of spectral factors. Tower bound IS Biggins additive martingale → converges to NON-DEGENERATE limit (wrong direction). TreeContractionAtHalf requires PHASE CANCELLATION, not modulus decay. Iterated conditional contraction (3/10): uniform gap bound orbit-specific (#90). MFRE transfer (4/10): tree nodes are structured integers (#90 at node level). Complex cascade degeneracy (Barral-Jin-Mandelbrot) and complex spine decomposition identified as speculative alternatives (3-4/10). No Lean code | 0 (confirms: modulus-product approaches fundamentally unsuitable for tree char sums; phase cancellation is the correct framework) |
| 229 | CofactorEnsembleDecorrelation (CED) assessment + EM/Ensemble/BagArithmetic.lean | CED = Dead End #115 (confirmed): cofactor ↔ multiplier bijection when alive means CED ≡ ensemble CME. Literature search: joint independence of minFac(n+1) and cofactor(n+1) mod q is OPEN PROBLEM in ANT (Alladi, McNew-Pollack-Roy give marginals only). EM/Ensemble/BagArithmetic.lean CREATED (225 lines, 0 sorry): 4 defs, 16 theorems (genEuclidOmega, genBagDiversity, genFactorsInClass, genEuclidCofactor + partition identity, oddness, cofactor subset) | 0.5 (infrastructure: 16 proved theorems; negative finding: CED = #115 confirmed, literature gap identified) |

| 233 | Random-Factor ε-MC with full factor bags + Cauchy-Davenport iterated product coverage | Full ε-MC **ABORTED** (4/10): rehash of Sessions 207-218 with quantitative refinement only (full bag vs two-point). Does NOT prove MC. Literature: `cauchy_davenport_minOrder_mul` in Mathlib4 → iterated product coverage PROVED. `EM/Advanced/IteratedProductCoverage.lean` (293 lines, 0 sorry): `iteratedMulFinset_card_growth` (iterated CD bound by induction), `iteratedMulFinset_eq_univ` (D≥|G|-1 steps with |S_k|≥2 ⇒ univ), `minOrder_units_zmod_safe_prime` (Lagrange for safe primes). Limitation: minOrder=|G| needed, holds only for safe primes. Open: `FactorBagCoverage` (connect to EM). Non-homogeneous Markov/Borel-Cantelli: all require probability (Four-Way Blocker). Kneser's theorem not in Mathlib | 0.6 (infrastructure: 15 proved theorems, 293 lines; strong negative on full ε-MC; deterministic coverage result genuinely new) |

| 262 | TSD(5) subgroup escape analysis + formalization | TSD(5) structural analysis: (Z/5Z)× ≅ Z/4Z, unique proper subgroup H={1,4}. Subgroup escape from acc≡2,3 PROVED (13 theorems, +328 lines EM/Advanced/InterpolationMC.lean). Hit cases: 2·2=3·3=-1. Non-hit cross: 2·3=3·2=1. Remaining gap: SpecificResidueClassFactor (same-class factor at depth ≥2). Viability: 6/10 for TSD-Hitting(5), 4/10 for full TSD(5). Literature: Booker (2016) subset-splitting freedom insufficient for standard product+1. | 0.8 (13 proved theorems + structural analysis; TSD(5) gap clearly characterized) |
| 263 | Coset ambiguity gap analysis + InterpolationMC cleanup | SpecificResidueClassFactor5 FALSE (counterexample P=2; LSD gives infinitely many). q=3 structurally unique: single non-identity coset = -1. q≥5: multiple cosets allow "bouncing." 4 theorems proved, -325 lines cleanup | 0.5 (structural finding + cleanup) |
| 264 | EM/Probability/GeometricCapture.lean: block-geometric decay framework + FMCD resolution confirmed | EM/Probability/GeometricCapture.lean CREATED (378 lines, 0 sorry): abstract geometric decay (5 thms), block capture weight (2 thms), block-geometric induction (3 thms), mixed walk bridge (3 thms), counting argument (3 thms), landscape (1 thm). FMCD confirmed already resolved (weak_fmcd_proved). Probability infrastructure now 3 files / 979 lines | 1.0 (17 proved theorems, complete geometric decay framework) |
| 265 | ETA provability analysis + HilbertInequality1 assessment | ETA FALSE for c=-1 (death class absorption: q\|genProd+1 ⇒ Pr[genSeq=q]~C₁/log q>0). Chain `eta_implies_crt_propagation` UNSOUND as stated (uses ETA at c=-1). Fix: exclude death class, handle via absorption decay. ETA-corrected viability 4-5/10: k=0 is 6/10 (standard ANT), k≥1 is 4/10 (requires ESL=ensemble orbit-specificity). HilbertInequality1: NOT formalized anywhere; Oleszkiewicz elementary proof recommended (1300-2000 lines). No new dead end (formulation bug, not conceptual) | 0.3 (critical formulation error found; no proved theorems; assessment clarifies ETA status) |
| 266 | AEP validity at q=3 + SRE formulation audit | **CRITICAL**: AEP FALSE at q=3 for k≥1 (Dead End #137, absorption drains nonzero classes exponentially: F_k(a) ~ C·2^{-k} → 0). SRE wrong limit (Dead End #138: correct = r/(r²-1), not 1/(r-1)). CRTPropagationStep FALSE (absorption prevents equidist propagation). Entire backward dynamics chain ETA→AEP→DeathDensityLB→SMLB→LMG→PRSD is vacuously true. SMLB(c) likely false for any fixed c > 0 (sieve effect). ETA backward dynamics vector downgraded from 4/10 to 1/10. Formalizer dispatched to fix SRE/AEP limit values in code | 0.3 (2 new dead ends; critical chain collapse; SRE limit corrected; no new proved theorems) |
| 276 | FF autonomous map Φ₃ exclusion criterion (EM/FunctionField/AutonomousMap.lean) | **PROVED**: `ffAutonomousMap_eq_neg_one_iff` (preimage of -1 = roots of Φ₃), `phi3_no_roots` (Lagrange: p≡2 mod 3 ⇒ no cube roots of unity in F_p), `ff_neg_one_unreachable` (death unreachable from any a≠-1 for p≡2 mod 3). EM/FunctionField/AutonomousMap.lean CREATED (225 lines, 14 theorems, 0 sorry). Excludes p-2 degree-1 targets simultaneously. Structural: under perpetual irreducibility, FF walk for degree-1 targets follows f(w)=w(w+1) autonomously on F_p. All 6 FF-specific reasoning lines assessed: all map to existing dead ends (#90, #127, #129, #130). FF setting gives 3 population-level advantages (free PE, exact counts, explicit Galois) but none bypass orbit-specificity barrier | 0.8 (14 proved theorems, 225 lines; strong structural negative result for p≡2 mod 3; 6 FF-specific questions definitively assessed) |
| 289 | Analytic attack vector saturation analysis | **ARCHITECTURAL SATURATION**: All major analytic fronts exhausted. **Critical formulation errors**: Dead End #136 (ETA FALSE for c=-1), #137 (AEP FALSE at q=3, absorption drains nonzero classes: F_k(a) ~ C·2^{-k} → 0), #138 (SRE wrong limit: correct = r/(r²-1), not 1/(r-1)), #139 (backward dynamics chain ETA→AEP→...→PRSD broken at every level). **Feasibility assessment**: `PrimeLogToReciprocal` (300-500 lines, 7/10), `HilbertInequality1` (1300-2000 lines, 4/10), `WeightedPNTinAP` (2000+ lines, 0/10, Mathlib-blocked). **Recommendation**: Dispatch for `PrimeLogToReciprocal` formalization — only high-value, low-effort target remaining. | 0.5 (critical error discovery + feasibility assessment; no proved theorems) |
| 291 | Scoping S-Φ: Φ-cocycle foundational rigor + POP/ORB gating (Task B) | System (A): all 5 Schmidt hypotheses satisfied, μ(L_p) = (1/p)∏_{q<p}(1-1/q) sum=1, E[log Φ] = +∞ irrelevant for compact G. System (B): cocycle over F(x)=x·minFac(x+1) circular — base dynamics IS EM problem. Coboundary test = CCSB (equivalence collapse). Verdict: NO-GO-foundations. T5.8 updated. No Lean code | 0 (definitive closure of Schmidt/cocycle approach; confirms Session 181) |
| 294 | Scoping S-Height: confinement height Ĥ_q as Lyapunov function (Tasks B+C) | **NO-GO-no-capacity**. Sub-thesis 1: γ_q = log((q-1)/(q-2)) CONSTANT under all 3 population nulls (Dirichlet+CRT). Renormalized height ≡ 0. Sub-thesis 2: Δ_q ≥ 0 trivially true (constant positive cost). Sub-thesis 3: capacity = lower bound (MATCHED-LINEAR). All existing infrastructure gives LOWER bounds on energy, not UPPER bounds on height. Sublinear capacity directly implies MC (circularity). L(N) strictly dominates Ĥ_q (state-dependent increments, quadratic/linear gap vs zero gap). No Lean code | 0 (7th scoping pass confirms orbit-specificity; confinement height CLOSED) |

**Success rate on novel proposals**: 28/81 (34.6%) led to proved theorems. All successes were on large sieve or ANT infrastructure (pure analysis). All failures on CME/SieveTransfer/DSL (EM-specific barriers).

**Pattern**: The agent is effective at formalizing standard analytic number theory and FF structural results. It is ineffective at finding new approaches to the EM-specific barriers. Future dispatches should focus on external infrastructure (F1), FF structural exploration (proved Φ₃ criterion Session 276), or monitoring for genuinely new mathematics (F4), not re-attacking the Four-Way Blocker.

**Saturation indicator**: Sessions 130-135 completed the Hilbert → ALS chain (except HI1). Sessions 148-152 built the ANT chain (EM/Population/Tauberian.lean, 557 lines after cleanup). Sessions 166-168 explored FF-EM (G3 Grothendieck moves) — all three attempts (FF analog #127, p-adic geometry #128, monodromy/Deligne #129) confirmed dead. G3 is CLOSED for orbit-specificity approaches. Session 276 found new structural content in FF autonomous map (Φ₃ exclusion, EM/FunctionField/AutonomousMap.lean). Session 169 closed Doeblin/Dobrushin + multiplicative large sieve approaches (both = reformulations of CME/CCSB). Session 170 built FF-MC infrastructure (4 files, 2302 lines, 0 sorry) and confirmed Dead End #130 (SelectionBias = CME, equivalence collapse). Session 172 closed Dobrushin coefficient / MUB approach (Dead End #131) — **Markov chain theory now FULLY EXHAUSTED** for EM walks (Sessions 145, 169, 172: non-homogeneous Markov, Doeblin=CME, Dobrushin α=0). Session 182: q-adic / Furstenberg q-adic strategy ABORTED at pre-flight (isomorphism of difficulty, HigherPRE useless for MC). **Sessions 287-289: Analytic attack vector saturation confirmed** — all major fronts exhausted, critical formulation errors discovered (#136-139). **Priority targets**:
1. **PrimeLogToReciprocal** — Abel summation (log p)/p → 1/p, ~300-500 lines, **7/10 feasibility** — **HIGHEST PRIORITY**
2. **HilbertInequality1** — 1300-2000 lines via Oleszkiewicz elementary proof (Session 265/289 assessment). NOT formalized in any proof assistant. Sharp constant π essential. Recommended method avoids Fourier analysis, uses convexity/AM-GM. **4/10 feasibility**
3. **WeightedPNTinAP → MFRE (compressed)** — ~500-900 lines using SieveDensityAxiom. **0/10 feasibility** (Mathlib-blocked, requires Wiener-Ikehara)
4. External infrastructure monitoring (F1, F4) — next check June 2026

---

## Session 299 (Run S-Receptacle) — STATUS changes and new frontier item

### New frontier item — supersedes the priority list above

**F5: (C∞) — "infinitely many `prod n + 1` are composite."**
`InfinitelyManyComposite`, `EM/Population/AutonomousBranch.lean`. **OPEN, top priority.**

Its negation is a live failure mode: under perpetual primality the walk mod `q` is
**autonomous** (`W_{n+1} = W_n² + W_n`), and `w²+w+1` has no root in `𝔽_q` for `q ≡ 2 mod 3`,
so MC would fail on a **density-1/2** set of primes
(`perpetual_primality_excludes_two_mod_three`; cleaner, via Bertrand,
`eventually_prime_implies_not_mullin`). We PROVED the contrapositive
`mullin_implies_infinitelyManyComposite`, so (C∞) is **necessary for MC and strictly
easier**. Expect it to be hard (cf. the open problem for Euclid numbers), but it is the
crisp gate that the diversity, monochromaticity, and factor-contraction families all
silently need.

### STATUS changes

| Technique | Old | New (Session 299) |
|---|---|---|
| T6.5 diversity chain / factor-set contraction | OPEN | **DEAD for the orbit.** `diverse_steps_imply_vanishing` is abstract over arbitrary `S : ℕ → Finset G` and concerns `avgCharProduct` (averaged tree product), not the deterministic orbit. Three failures: (F1) averaging vs selection (`‖χ(s)‖ = 1` pointwise); (F2) *some* branch vs *the min* branch; (F3) factor sets fixed in advance vs path-dependent. **Avoidance forces nothing about monochromaticity.** |
| T7.9 Φ₃ / autonomous map | FF-only | **Transfers to ℤ** under (ω1). Excludes ~π(x)/2 primes, not finitely many. Now `EM/Population/AutonomousBranch.lean`. |
| Consumption / shield-ledger receptacle | UNTRIED | **DEAD (false Gap).** Detection strength is ZERO (tail class is 0 unconditionally via `exists_tail_coprime`); the Gap conjecture is inhabited by the zero ledger (the (ω1) branch). Sharpenings landed anyway: `hittingSet_ncard_le_appearing`, `finite_missing_confinement`, `hitting_ledger_sum/bound`. |
| Covering systems / multi-modulus congruence | UNTRIED (wildcard) | **DEAD.** Covering systems are finite by definition; `no_finite_prime_covering` kills the class in one line. `no_cvdp_obstruction` is set-generic, so lcm-composition is already covered. |
| LSD / Wirsing density along the orbit | UNTRIED | **DEAD.** No exponentially-sparse LSD exists; `O(log x)` orbit terms below `x` sit under every LSD error term. (Fine for genuine population statements.) |
| Iwasawa / Euler system | UNTRIED | **DEAD.** Kolyvagin needs the full squarefree *lattice*; the orbit gives a single maximal *flag*. No ℤ_p-tower, no motive, no period formula. |
| Nonstandard / ultraproduct | UNTRIED | **DEAD.** Detection honest (Łoś), Gap vacuous (Loeb measure 0 for *every* sequence). |
| Confinement cohomology | UNTRIED | **DEAD (false Gap).** `free_transition` + `exists_tail_coprime` make the box forward-mobile; `H⁰ ≠ 0`. |

### New cross-cutting principles

- **The anatomy principle.** In both the min/max dichotomy and the (ω1) branch, what defeats
  the congruence method is **anatomy** (smoothness / compositeness). Congruence invariants
  factor through `p ↦ p mod m`, i.e. through the walk, which sees only the product. Filter
  every proposed invariant by: *does it see anatomy?*
- **Correction**: the min/max break point is **not** Free-state Fullness (rule-symmetric —
  for maxFac pick `π ≡ (r+1)s⁻¹` first, then `M ≡ s > π`). It is the *capture condition*:
  `minFac N = q` is a congruence condition; `maxFac N = q` is a smoothness condition.
- **Receptacle conservation law** (observed regularity, not a theorem): Detection-difficulty +
  Gap-difficulty ≥ the orbit-specificity barrier. Session 299 sharpened it — pushing
  difficulty onto Gap yields not a *hard* Gap but a **false** one. Mechanisms:
  **Zero-Configuration** (consumption gives only upper bounds; the zero ledger is always
  feasible) and **Support-Invisibility** (missingness is a support condition on `Σ_p e_p`).
- **Arboreal diagnostic**: a *clean* Detection arrow is a symptom of being a factor map onto
  a classical system, hence of a false or vacuous Gap. Stop hunting clean Detection arrows.

### New UNTRIED combinations

- (C∞) via the function-field analogue (the algebra is in `EM/FunctionField/AutonomousMap.lean`).
- (C∞) conditional on standard conjectures — is there a Schinzel/Bateman–Horn-flavoured
  statement that forces compositeness infinitely often for this recursion?
- Weaker gates that kill the autonomous branch without full (C∞).

### Track record

| Session | Proposal | Outcome | Advancement |
|---|---|---|---|
| 299 | Run S-Receptacle: receptacle design (Task A), monochromaticity Gap (Task B), graded map (Task C) | **Escalation fired.** Tasks A and B independently converged on the eventually-prime (ω1) failure branch; formalized as `EM/Population/AutonomousBranch.lean` (321 lines, 0 sorry) with a new *unconditional* consequence of MC (`mullin_implies_infinitelyManyComposite`). Covering-system wildcard: **NO HOLE** (two independent arguments). Found and fixed a factual error in our own `NoInvariant.lean` docstrings. 8 new dead ends. Consumption sharpenings landed in `HittingSetStructure.lean` (287→540 lines). | **0.8** (new named frontier item (C∞); first concrete failure mechanism; new unconditional theorem; own-work correction) |

**Success-rate note**: Session 299's value came from *disconfirmation done precisely* —
grading receptacles until one's Gap was decided FALSE, which exposed the mechanism. Record
this as evidence that "decide the Gap, don't hunt Detection" is the productive posture.
