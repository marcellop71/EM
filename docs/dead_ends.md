# Dead Ends Catalog

**Canonical reference for the Mullin's Conjecture formalization project.**
**114 dead ends documented across 97 sessions.**

Agents MUST check this file before exploring any new direction. If a proposed approach maps onto any entry here, it is a dead end and must not be re-explored.

Last updated: Session 97 (2026-02-26). One new dead end (#114) from Session 97.

---

## Taxonomy

Dead ends fall into six categories:

- **PROVED IMPOSSIBLE**: A formal counterexample or impossibility proof exists. The approach is mathematically ruled out.
- **EQUIVALENCE COLLAPSE**: The proposed "new" hypothesis or technique is formally equivalent to an existing one, providing zero new leverage.
- **TECHNIQUE MISMATCH**: A known mathematical technique exists but its prerequisites fail for the EM walk (e.g., requires independence, stationarity, multiplicativity).
- **SCALE MISMATCH**: The technique applies but at the wrong scale or in the wrong direction (e.g., bounds too weak, inequality points the wrong way).
- **CIRCULARITY**: The approach reduces to the very thing it was trying to prove.
- **MATHLIB BLOCKED**: The approach is mathematically viable but requires Lean infrastructure not currently in Mathlib.

---

## Category A: Walk Bridge & Character Sum Barriers

These dead ends concern the gap between MARGINAL information about multipliers and JOINT information about (position, multiplier) pairs. This is the core barrier of the project.

| # | Description | Category | Session | Key fact |
|---|-------------|----------|---------|----------|
| 4 | Consecutive vs arbitrary subsequence barrier | TECHNIQUE MISMATCH | 1-4 | Cauchy-Davenport / EGZ apply to arbitrary subsequences, not consecutive partial products |
| 20 | Dec does NOT imply CCSB | PROVED IMPOSSIBLE | 12+ | Decorrelation (multiplier char sums o(N)) is strictly weaker than CCSB (walk char sums o(N)). Counterexample: multipliers cancel but walk accumulates bias |
| 36 | BRE impossible from PED for d≥3 | PROVED IMPOSSIBLE | 18 | Counterexample: alternating ω, ω² multipliers satisfy PED but walk sum is Θ(N). Block rotation estimate CANNOT be derived from positive escape density for character order ≥ 3 |
| 38 | VdC with h=1 gives O(N) not o(N) | SCALE MISMATCH | 18 | Van der Corput with single-lag (h=1) decorrelation gives ‖S‖ ≤ N/√2, a constant fraction, not o(N). Higher lags (h≥2) require joint distribution of consecutive multipliers |
| 58 | MultCSBImpliesMMCSB is FALSE | PROVED IMPOSSIBLE | 28 | Definitive counterexample: multipliers cycling {−1,−1,+1,+1} give S_M = O(1) but S_W = Θ(N). Multiplier character sum cancellation does NOT imply walk character sum cancellation. Root cause: walk sums involve partial products (order-sensitive) |
| 73 | SVE not provable from existing infrastructure | CIRCULARITY | 39 | Subquadratic visit energy faces the same VdC h=1 barrier as CCSB. L²-averaged CCSB is no easier than pointwise CCSB |
| 76 | CCSB does NOT imply HOD | PROVED IMPOSSIBLE | 42 | Higher-Order Decorrelation is strictly stronger than CCSB for abstract walks |
| 77 | Dec + VdC insufficient for CCSB | EQUIVALENCE COLLAPSE | 42 | Reconfirms #38 at the VdC framework level |
| 78 | Partial HOD (h=2) not provable | TECHNIQUE MISMATCH | 42 | Requires joint distribution of consecutive EM least prime factors — an open problem in analytic number theory |
| 79 | HOD is not a useful attack target | SCALE MISMATCH | 42 | HOD → MC is proved, but HOD is strictly HARDER than CCSB. Proving HOD is harder than proving MC directly |
| 80 | Order-2 CCSB from PED+NoLongRuns | PROVED IMPOSSIBLE | 41 | Alternating sum analysis: even with Ω(N) blocks, adversarial block lengths give O(N) not o(N) |
| 85 | Route C (VdC + EscapeDecorrelation) | EQUIVALENCE COLLAPSE | 49 | EscapeDecorrelation ≡ QuadraticHOD ≡ QuadraticCCSB via proved VdC. Not a new attack — just assuming the conclusion |
| 87 | General escape sum bound for d≥3 | PROVED IMPOSSIBLE | 54 | Unweighted escape sum ∑_{esc} χ(w(n)) is NOT O(1) for d≥3. Adversarial phase alignment among d−1 rotations gives Θ(N). Kernel-block reduction is specific to order-2 |
| 88 | d=2 block-length balance from PED | PROVED IMPOSSIBLE | 56 | PED controls total kernel density but not distribution across blocks. Adversarial block lengths defeat alternating series argument |

## Category B: Sieve Transfer & Equidistribution Barriers

These concern transferring generic equidistribution results to the specific EM orbit.

| # | Description | Category | Session | Key fact |
|---|-------------|----------|---------|----------|
| 26 | Residue class vs prime identity | TECHNIQUE MISMATCH | early | minFac being "small" (a SIZE property) is invisible to character sums (a RESIDUE property). Multiple primes share residue classes |
| 40 | SieveEquidist does NOT imply NoLongRuns | PROVED IMPOSSIBLE | 19-20 | Cumulative equidistribution allows arbitrarily long gaps. Window equidistribution (StrongSieveEquidist) is needed |
| 48 | Orthogonality tautology | CIRCULARITY | early | Character orthogonality gives ∑χ(a)V(a) identities, but V(a) = N/(q−1) IS equidistribution. Using orthogonality to prove equidistribution is circular |
| 61 | ArithLSImpliesMMCSB is vacuous | SCALE MISMATCH | 27 | ArithLS with dense coefficients (a(n)=1) gives trivial bounds. PrimeArithLS bound N²(p+1) is worse than triangle inequality |
| 75 | PrimeArithLSImpliesMMCSB structural mismatch | PROVED IMPOSSIBLE | 38 | PrimeArithLS bounds character sums at integer arguments; MMCSB needs sums at walk positions. Walk function w: Fin N → (ZMod p)ˣ is many-to-one, not captured by large sieve |
| 90 | CME derivable from existing results | TECHNIQUE MISMATCH | 59 | CME faces Four-Layer Gap: population→individual, unconditional→conditional, static→growing, counting→distribution. No technique spans even one layer |
| 91 | Prime Euclid density argument | SCALE MISMATCH | 59 | Prime Euclid numbers are finitely many (~2.89 heuristically). Contribute o(N) trivially. Zero information for composites |
| 92 | Self-correction forcing equidistribution | CIRCULARITY | 59 | Feedback from growing excluded set is summable (∑1/seq(n) < ∞). Stabilizes walk but cannot force bias to zero |
| 96 | LoD scale mismatch | SCALE MISMATCH | 63 | (prod N)^θ ≥ 2^{θN} grows exponentially in N, making LoDImpliesMMCSB vacuously unprovable. Standard LoD assumes range ≈ integer size; for EM, range is N while integer size is prod(N) |
| 108 | Harper BDH for general sequences inapplicable to EM | SCALE MISMATCH | 81 | Harper (arxiv:2412.19644, Dec 2024) proves BDH variance asymptotics for general non-multiplicative sequences, but requires well-distribution in APs to small moduli and non-concentration on multiples. EM products are super-exponentially sparse (N terms in [1, 2^{2^N}]) and structured (pairwise coprime). Sparsity makes BDH vacuous; AP-distribution condition IS an equidistribution hypothesis (circular). Even if applicable, gives variance (most q good) not pointwise (all q good) |
| 111 | Rough Number Concentration for d=2 NoLongRuns | TECHNIQUE MISMATCH | 82 | Coprimality + q-roughness + super-exponential growth CANNOT rule out L consecutive QR minFac values. Counterexample: for any L, pick L distinct QR primes ≥ q, construct coprime q-rough integers with those minFac. Pollack-Roy (2023) gives marginal equidistribution only; "coprimality ⇒ minFac independence" does NOT exist in literature. Recursive coupling P(n+1)=P(n)·minFac+1 is the only leverage but exploiting it IS SieveTransfer |

## Category C: Algebraic & Group-Theoretic Barriers

| # | Description | Category | Session | Key fact |
|---|-------------|----------|---------|----------|
| 9 | Chebotarev density theorem | MATHLIB BLOCKED | early | Kummer theory route requires Chebotarev, which is ~5000+ lines and not in Mathlib |
| 22 | Quadratic character large sieve for d=2 | TECHNIQUE MISMATCH | early | Large sieve bounds are over ALL characters simultaneously; restricting to d=2 loses the averaging |
| 39 | Linnik small QNR | TECHNIQUE MISMATCH | early | Smallest quadratic non-residue results don't apply to walk dynamics |
| 81 | CME → HOD FALSE for h≥2 | PROVED IMPOSSIBLE | 43 | Walk feedback creates correlations between consecutive multipliers. CME controls single-step conditional distribution but NOT multi-step joint distribution |
| 82 | Cyclic Littlewood-Offord | EQUIVALENCE COLLAPSE | 46 | Reduces entirely to Dec/HOD framework. When specialized to (Z/qZ)× ≅ Z/(q−1)Z, Tiep-Vu mechanism IS character-sum CCSB |
| 83 | Inverse Littlewood-Offord | PROVED IMPOSSIBLE | 46 | FALSE for d≥3. Counterexample: alternating ω, ω² multipliers give |S_N|=N/2 with zero ker(χ)-concentration. Large walk sums do NOT force multiplier concentration |
| 84 | Pseudo-independence notions | EQUIVALENCE COLLAPSE | 46 | Pair mixing = Dec (too weak). Exponential decay = Dec. k-point decay = HOD (unverifiable). Block independence = HOD at coarser scale. All reduce to known hierarchy |

## Category D: Analytic Technique Barriers

| # | Description | Category | Session | Key fact |
|---|-------------|----------|---------|----------|
| 55 | Dirichlet PNT for MC | MATHLIB BLOCKED | early | IK Thm 5.27 not in Mathlib. Even if formalized, only gives asymptotic π(x;q,a) ~ x/φ(q)log(x), which is SieveEquidistribution not SieveTransfer |
| 56 | Siegel-Walfisz for MC | MATHLIB BLOCKED | early | IK Cor 5.29 not in Mathlib. Same issue as #55 |
| 63 | KernelRowSumBound (sharp ALS) | SCALE MISMATCH | 31+ | Needs Selberg-MV extremal functions (~300-500 lines). WeakALS (PROVED) already supersedes it for all MC applications |
| 74 | BirkhoffSum API inapplicable | TECHNIQUE MISMATCH | 39 | Mathlib BirkhoffSum assumes orbit under SINGLE map. EM walk has different multiplier at each step — non-autonomous dynamics |
| 86 | Nonstationary ergodic theorems | TECHNIQUE MISMATCH | 51 | Monakov / Ito-Kawada type results require strictly aperiodic probability measures AND independent steps. EM walk has Dirac mass steps (deterministic) and dependent steps |
| 89 | Anti-concentration / PGF zero-free | TECHNIQUE MISMATCH | 57 | Four-Way Blocker: (A) Independence-based — no PGF factorization, (B) Multiplicativity-based — EM not multiplicative, (C) Algebraic-geometric — no parameter family, (D) Ergodic — no independence/stationarity. EM satisfies NONE |
| 95 | Spectral gap for deterministic walks | TECHNIQUE MISMATCH | 62 | Spectral gap theory applies to DISTRIBUTIONS (convergence of random sampling). EM walk is a single deterministic path. Frequency of visiting a state ≠ probability of visiting it |
| 102 | Large sieve single-frequency extraction | SCALE MISMATCH | 72 | Large sieve is an averaging tool over R well-separated frequencies. With R=1 (single α=0), separation is vacuous and bound collapses to trivial ‖S_N‖≤N. Embedding α=0 in larger set gives ‖S(0)‖²≤N²(R+1), WORSE than trivial. Gram off-diagonal structure has no effect with one point |
| 103 | Third algebraic route to CCSB | PROVED IMPOSSIBLE | 72 | Telescope χ(w(n+1))=χ(w(n))·χ(m(n)) is the COMPLETE algebraic content. Only two decomposition strategies for S_N: by value (fiber→CME) and by lag (autocorrelation→HOD). Abel summation wrong direction (O(N²) remainder). Differentiation=unit steps. Möbius/Dirichlet need multiplicativity (Four-Way Blocker). No third route exists |
| 109 | Non-multiplicative Halász | TECHNIQUE MISMATCH | 81 | No extension of Halász to non-multiplicative functions exists (searched 2024-2026). Pretentious distance is intrinsically Euler-product-based. Tao-Teräväinen (Dec 2025) confirms pairwise correlations remain within multiplicative world. EM walk χ(w(n)) satisfies first-order recurrence not multiplicativity; telescope identity exhausts algebraic content (#103). Four-Way Blocker item B |

## Category E: LP, CRT, and Structural Reformulation Barriers

These are approaches that reformulate the problem elegantly but provide zero new mathematical leverage.

| # | Description | Category | Session | Key fact |
|---|-------------|----------|---------|----------|
| 93 | Density-1 CME / FEB / CC_χ=o(N²) | EQUIVALENCE COLLAPSE | 61 | All three formulations equivalent to full CME for fixed q. Markov inequality on q−1 positions: L² control ⟹ L∞ control. No weakening available |
| 94 | Fiber uniformity from SE alone | PROVED IMPOSSIBLE | 61 | SE guarantees multipliers generate full group but says nothing about conditional distribution per walk position |
| 97 | LP avoidance framework | EQUIVALENCE COLLAPSE | 64 | LP infeasibility for all T with uniform FPE is EQUIVALENT to DH. Feasible for many T at all tested q. Not a reduction — a reformulation |
| 98 | CRT decorrelation approach | EQUIVALENCE COLLAPSE | 65 | CMI + FPE = CME (already in hierarchy). CRT exogeneity ≠ statistical independence for deterministic sequences. Per-step ≠ sequence-level. Three-Way Blocker in algebraic guise |
| 99 | CME spectral gap / bias propagation | EQUIVALENCE COLLAPSE | 66 | Bias propagation identity: 1 equation, p−2 unknowns (underdetermined). CRT state-independence: per-step, not sequence-level. Return product constraints: tautological (group law). Spectral gap: distributions, not deterministic paths |
| 100 | Walk periodicity dichotomy | EQUIVALENCE COLLAPSE | 69 | Periodic walks do NOT automatically give o(N) char sums. One-period sum S_p ≠ 0 for short/non-uniform cycles. Trichotomy (aperiodic/periodic-good/periodic-bad) reduces to existing barriers (#42, #80, #88, #95). Ruling out periodicity requires SieveTransfer. Codebase already has walk_periodic_hh_iff_in_cycle |
| 101 | Bundle Walk / Weak MC | EQUIVALENCE COLLAPSE | 70 | Bundle walk on ∏(Z/qZ)× does not simplify MC. Avoidance set T_S is not a subgroup/coset. Character sums don't factor (shared minFac index). All three routes (equidist, Borel-Cantelli, sieve) require SieveTransfer. Avoidance density δ(M)→0 is population-level, cannot constrain deterministic walk |
| 104 | Summable Decorrelation (SD) / Bottleneck Decorrelation | EQUIVALENCE COLLAPSE | 74 | SD (fiber sums F(a) = μ·V(a) + O(1)) is strictly stronger than VCB (F(a) = μ·V(a) + o(N)) but provides zero additional leverage: VCB + PED → CCSB is provable with the same argument. The o(N) error in VCB summed over φ(q) fibers remains o(N). EM-specific verification of SD faces Dead Ends #90 (Four-Layer Gap) and #98 (CRT decorrelation) |
| 105 | First passage / ExistentialCME weakening | EQUIVALENCE COLLAPSE | 75 | MC only needs one hit of -1 (not equidistribution), but this is a TAUTOLOGICAL weakening: the Fourier identity V_N(-1)·(q-1) = N + ∑_{χ≠1} χ(-1)⁻¹·S_N(χ) carries zero new information (it restates V_N(-1)=0 ↔ phased sum = -N). ExistentialCME (∃ c,n: w(n)=c, m(n)=-c⁻¹) IS DH. Inter-character cancellation requires HOD-type correlations (#79). Borel-Cantelli on conditional subsequence = Marginal/Joint Barrier (#94). Binary structure (at-most-once hitting) formalized but provides no proof leverage |
| 106 | VCB → CCSB without PED | EQUIVALENCE COLLAPSE | 78 | Telescope forces (μ-1)·S_N = O(1). If μ≠1: S_N = O(1), CCSB trivial. If μ≈1: kernel confinement, CCSB fails. So (VCB → CCSB) ⟺ PED. "VCB implies CCSB without PED" is equivalent to PED itself. Cannot bypass PED via algebraic analysis of VCB alone. Shift equivariance constrains dynamics, not statistics (#94). ResamplingBound either tautological or requires open conditional distribution (#90, #98). Fiber deviation Parseval: ∑‖F(a)-V(a)‖² = ‖M_N-N‖²/(q-1) + cross-char terms — cross terms unconstrained by existing infrastructure |
| 107 | Bottleneck Decorrelation Axioms insufficient for VCB | PROVED IMPOSSIBLE | 79 | Explicit counterexample on (Z/3Z)*: block-structured walk with N=4K steps (alternating escape/kernel blocks) satisfies all three axioms (Per-Step CRT, Exponential Growth, Generation) but VCB fails — F(1)/V(1)=1/3, F(2)/V(2)=-1, no common μ exists. Root cause: per-step CRT cannot detect temporal correlations between visit patterns and multiplier blocks. Abstract class-of-sequences framework provides no leverage beyond individual-sequence analysis |
| 110 | Empirical transition matrix convergence = CME | EQUIVALENCE COLLAPSE | 81 | K_N(a,b) = #{n: w(n)=a, w(n+1)=b}/V_N(a) converging to uniform IS CME (fiber char sums o(N) for all positions a). Weyl criterion on K_N rows = CME definition. All techniques for transition matrix convergence (spectral gap #95, mixing #86, ergodic #74) require randomness/stationarity. Reformulation provides zero new proof leverage. Formally verified: cme_iff_transition_char_vanish PROVED in Session 81 |
| 112 | Order-3 Möbius death function as proof leverage | EQUIVALENCE COLLAPSE | 83 | The Möbius death function b(a)=(1-a)⁻¹ has order 3 with clean identity m₁·m₂·m₃ = -1 for forbidden multiplier triples. But this constrains the DEATH CURVE geometry, not the WALK DYNAMICS. The dynamically relevant map is the order-2 involution f(c) = -c⁻¹ (already formalized). Avoidance graph is a perfect matching (maximally simple). Maps to Marginal/Joint Barrier: structure of constraint surface ≠ dynamics of walk through it. Formalized as infrastructure (§2C/§2D in EquidistSieve.lean) but provides zero proof leverage |
| 113 | Cycle Product Equidistribution | CIRCULARITY | 91 | Cycle products R_k = ∏_{j in cycle k} m(j) equidistributing mod auxiliary primes p is EQUIVALENT to CCSB for p, not a new approach. Telescoping identity χ(R_k) = χ(w(end_k))/χ(w(start_k)) = a_{k+1}/a_k reduces product of ℓ ≥ 2 terms to lag-1 autocorrelation of walk characters at return times. This IS a character sum bound on the walk (CCSB). For ℓ ≥ 2 product structure gives ZERO advantage: internal structure absorbed by telescope. Decorrelation across cycles maps to Dead Ends #92 (self-correction circularity) and #98 (CRT per-step not sequence-level). Product equidistribution from Alladi distribution is population-level, not path-level |
| 114 | Missing Prime Accumulation argument | EQUIVALENCE COLLAPSE | 97 | Second-moment/Borel-Cantelli argument that primes missing from EM would accumulate contradictorily. "Pairwise Death Channel Independence" (events {q divides P(n)+1} quasi-independent across n) is CME restricted to a single fiber (#90, #98). Self-consistent avoidance model restates §23 analysis (EquidistOrbitAnalysis). Transfer from population-level sieve estimates to specific EM orbit IS SieveTransfer (#107). Kochen-Stone variant requires same quasi-independence. No new leverage beyond CME/SieveTransfer |

## Category F: Early Dead Ends (Sessions 1-25)

These were documented in early sessions. Reconstructed from cross-references in later sessions. Numbers without explicit descriptions are from sessions not currently in the uploaded transcript; the description is inferred from context.

| # | Description | Category | Session | Key fact |
|---|-------------|----------|---------|----------|
| 1-3 | Computational approaches (sequence values, threshold raising, brute force SE) | SCALE MISMATCH | 1-4 | Computing seq values or raising ThresholdHitting by brute force doesn't prove the conjecture for ALL primes |
| 5-8 | Early algebraic attempts | Various | early | Various algebraic approaches to SE → DH that hit the marginal/joint barrier |
| 10-19 | Various character sum and Fourier approaches | Various | 6-12 | Multiple attempts at character sum bounds that reduce to Dec (too weak) or CCSB (what we're trying to prove) |
| 21 | DPED → CCSB for d≥3 | PROVED IMPOSSIBLE | 21 | Alternating ω, ω² satisfies DPED but walk sum Θ(N) |
| 23-25 | Hooley-type sieve, entropy, variance | CIRCULARITY | 22 | Hooley gives PED at best. Entropy/variance circular (walk equidist = CCSB) |
| 27-35 | Self-avoidance, periodicity, generation | Various | 14-17 | Self-avoidance invisible to characters. Periodicity arguments can't handle aperiodic walks. Generation ≠ coverage (counterexample: step 2 in Z/6Z) |
| 37 | Walk bridge attempts | PROVED IMPOSSIBLE | early | Various attempts to convert multiplier cancellation to walk cancellation (precursor to #58) |
| 41-47 | Expander mixing, DWH variants, profinite | Various | 22-23 | Expander mixing requires random steps. DWH variants don't improve on DWH itself. Profinite = SieveTransfer |
| 49-54 | IK formalization attempts | MATHLIB BLOCKED | 24-27 | Multiple IK theorems that require Mathlib infrastructure not available |
| 57 | Second EM sequence | N/A | early | Cox-van der Poorten "largest factor" variant misses primes — documented but doesn't advance MC for "smallest factor" |
| 59-60 | Kneser's theorem, sumset arguments | TECHNIQUE MISMATCH | early | Kneser gives weaker bounds than direct arguments. Sumset results apply to arbitrary subsequences, not consecutive |
| 62 | Vaughan identity for MC | MATHLIB BLOCKED | early | Vaughan's identity not in Mathlib; even if formalized, produces the SieveTransfer gap |
| 64-72 | Various hybrid approaches | Various | 30-48 | Multiple attempts combining proved infrastructure in new ways that don't escape known barriers |

---

## The Three-Way Blocker

The majority of dead ends reduce to one meta-obstacle identified in Session 57 and extended in later sessions:

**The Four-Way Blocker**: Every known technique for proving equidistribution of sequences on finite groups requires at least ONE of:
1. **Independence** of steps (random walk theory, LO, PGF factorization)
2. **Multiplicativity** of the generating function (Halász, pretentiousness)
3. **Algebraic-geometric structure** (Katz monodromy, algebraic parameter families)
4. **Ergodic stationarity** (mixing theorems, invariant measures)

The EM walk satisfies NONE of these. It is:
- **Deterministic** (each step is fixed, not random)
- **Non-multiplicative** (minFac is not a multiplicative function; the sequence is recursively defined)
- **Non-algebraic** (no parameter family; the walk is a single orbit)
- **Non-stationary** (different multiplier at each step; no invariant measure)

Any proposed approach must be checked against this blocker. If it requires any of (1)-(4), it is dead on arrival.

---

## The Marginal/Joint Barrier

The second meta-obstacle, identified in §22-23 of the formalization:

All proved reductions extract MARGINAL information about the walk (TailSE, PED, Dec, SE). DH requires JOINT information: the (position, multiplier) pair must hit the death curve. The project proves:

> There is no useful intermediate between TailSE (marginal) and DH (joint).

Any proposed approach that works with marginal distributions (of positions alone, or multipliers alone) cannot close DH. The approach must somehow constrain the JOINT distribution — which requires knowing how minFac(P(n)+1) depends on P(n) mod q, the core open question.

---

## Usage Instructions for Agents

1. **Before proposing any approach**: Check whether it maps onto ANY entry in this catalog.
2. **Check the taxonomy**: Does the approach require independence? → Four-Way Blocker. Does it work with marginals? → Marginal/Joint Barrier.
3. **If uncertain**: State the approach precisely and check whether it implies something already proved (equivalence collapse) or contradicts a counterexample (proved impossible).
4. **New dead ends**: If a new approach fails, add it to this catalog with number, description, category, session, and key fact. Maintain the numbering sequence.
