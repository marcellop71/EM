# Algebraic Technique Catalog

**Domain**: Algebra, group theory, CRT, algebraic number theory
**Attack agent**: `attack_algebraic`
**Last updated**: Session 293 (post-session lemma-target addendum, 2026-05-23)

---

## How to use this catalog

1. **Before proposing anything**: scan the STATUS column. If DEAD, don't revisit.
2. **Check preconditions**: each technique lists what it needs. If EM fails a precondition, the technique is blocked.
3. **Check the Marginal/Joint Barrier**: does the technique work with marginal information only (positions alone, or multipliers alone)? If so, it cannot close DH.
4. **Check the Algebraic Exhaustion Thesis** (Sessions 72-82): the telescope identity χ(w(n+1))=χ(w(n))·χ(m(n)) exhausts ALL algebraic content of the walk. Only two decomposition strategies exist: by value (fiber → CME) and by lag (autocorrelation → HOD). No third algebraic route exists (#103).
5. **Look for UNTRIED combinations**: the most promising moves are combining structural results with new external mathematics.

---

## Technique Families

### T1: Subgroup & Generation Theory

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T1.1 | Cauchy-Davenport / EGZ | Arbitrary subsequence of elements in Z/pZ | Every subsequence of length ≥ p has zero-sum subsequence | DEAD | #4 | EM needs PREFIX products (consecutive), not arbitrary subsequences. Ordering problem |
| T1.2 | Subgroup Escape (SE) | Multipliers m(0),...,m(N) in finite group G | ⟨m(0),...,m(N)⟩ = G (full generation) | PROVED | — | `SubgroupEscape` proved via PRE→SE for all primes. 29 concrete instances. SE is necessary but far from sufficient |
| T1.3 | Subgroup Confinement analysis | Walk confined to proper subgroup H | Multipliers ∈ H, walk char constant on cosets | PROVED (fully exploited) | #94 | `kernel_confinement_walk_char_constant`, `ccsb_at_implies_escape_cofinal`, `confinement_target_set`. Session 76: no abstract algebraic route to PED from confinement |
| T1.4 | Departure Graph framework | Walk in finite group, position-dependent departures | Structural constraints on DH failure | PROVED | — | `EM/Group/DepartureGraph.lean` (393 lines). `oracle_from_confinement`, `generation_escapes_subgroup`, infinite recurrence, safe prime lattice. Infrastructure only — no proof leverage for DH |
| T1.5 | Safe Prime structural dichotomy | G of order 2p (safe prime), multipliers generate G | 4-element subgroup lattice: {1}, C₂, C_p, G | PROVED | — | `card_subgroup_of_order_two_mul_prime`, `generating_escapes_proper`. DH failure is "analytically invisible" to the subgroup lattice (`dh_failure_distributional_gap`). Structural analysis exhausted |
| T1.6 | Sequenceability / pumping | Finite abelian group G, ordering of elements | Every element reachable by SOME ordering of generators | PROVED (irrelevant) | #4, #101 | Gordon's conjecture, `EM/Group/Pumping.lean`. Proves EXISTENCE of good orderings; EM needs result about its SPECIFIC ordering. Confirms Marginal/Joint Barrier |
| T1.7 | Complement generation | Finite group G with |G|≥3 | G \ {g} generates G for any g | PROVED | — | `closure_compl_singleton_eq_top`. Structural fact, no dynamical content |
| T1.8 | Davenport constants | Zero-sum theory in finite abelian groups | D(G) = length guaranteeing zero-sum subsequence | DEAD | #4, #59-60 | DH needs PREFIX products, not arbitrary subsets. Kneser gives weaker bounds than direct arguments |
| T1.9 | Character kernel intersection / NFCE dichotomy | Cyclic group G, |G| with ≥2 distinct prime factors | Total NFCE failure ⇒ factorRatio = 1 (self-correction) | **PROVED** (for non-Fermat primes) | — | Sessions 222-223. ⋂(non-faithful char kernels) = {1} when |G| has ≥2 distinct prime factors. **NFCS PROVED** (Session 223): `nonFaithfulCharSeparation_of_two_prime_factors` via quotient character lifting. NFCS is FALSE for prime-power-order groups (Z/4Z counterexample). Covers all primes except Fermat primes (q = 2^k+1). q=3 handled (UFDStrong(3)), q=5 has NFCE(5) infra. |
| T1.10 | Iterated Cauchy-Davenport via minOrder | Sets S_k with |S_k| ≥ 2 in finite abelian G, minOrder G = |G| | After |G|-1 steps, S₀·...·S_{D-1} = G | **DEAD (#137)** | #4, #130, #137 | Session 233-234. `iteratedMulFinset_eq_univ` PROVED but `minOrder (ZMod q)× = 2` for ALL primes q ≥ 3 (`minOrder_units_zmod_eq_two`). CD bound gives only |A*B| ≥ 2 (vacuous). Safe prime ⇒ q = 3 only (`prime_sub_one_prime_implies_eq_three`). Kneser (not in Mathlib) would fix minOrder issue but faces ordering (#4) + generation ≠ coverage (#130). |
| T1.11 | Goursat's lemma for product groups | I ≤ G₁ × G₂ subdirect, projections surjective | Normal M, N with G₁/M ≅ G₂/N | **DEAD (#130, #101)** | #90, #101, #130 | Session 259. Goursat classifies SUBGROUPS, not trajectories. For cyclic groups of coprime orders, every subdirect product = full product (trivial). For non-coprime, FTA+CRT already give full generation via `primeUnitsBelow_generate`. Zero content beyond existing infrastructure. Mathlib: `Subgroup.goursat_surjective`. |

### T2: CRT & Fiber Analysis

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T2.1 | CRT surjectivity | Coprime moduli q₁, q₂ | (Z/q₁q₂Z)× ≅ (Z/q₁Z)× × (Z/q₂Z)× | PROVED | — | `crt_pair_surjective` proved via Bezout |
| T2.2 | CRT multiplier invariance (PBI) | minFac and modular reduction | minFac(P(n)+1) mod q independent of P(n) mod q | PROVED | #98 | `crt_multiplier_invariance`. Per-step structural decorrelation. Does NOT give sequence-level independence (per-step ≠ aggregate) |
| T2.3 | CRT decorrelation | Per-step CRT independence → sequence independence | Equidistribution from CRT | DEAD | #98, #107, #115 | Per-step CRT ≠ sequence-level decorrelation. Explicit counterexample (#107): block-structured walk satisfies CRT + growth + generation but VCB fails. ACI (#115): dimensional explosion illusory for deterministic sequences. Session 138: OCE (orbit-conditional equidist) = CME by `rfl` — orbit conditioning adds zero new content |
| T2.4 | Fiber decomposition | Walk visits V(a) to each position a | S_N = ∑_a ∑_{n:w(n)=a} χ(m(n)) | PROVED | #90, #93, #94 | This IS the CME approach. Density-1 CME ≡ full CME (#93). Fiber uniformity from SE alone impossible (#94). Four-Layer Gap (#90) |
| T2.5 | CRT fiber independence | CRT + coprimality + death channel structure | Death channels nonempty, disjoint, mechanism proved | PROVED | — | `EM/Transfer/CRTFiber.lean` (10 theorems). `death_channel_nonempty`, `dvd_independent_of_residue`. Infrastructure, not proof leverage for CME |
| T2.6 | CME ↔ transition matrix | Empirical transition matrix K_N(a,b) | CME ↔ K_N rows converge to uniform | PROVED (equivalence) | #110 | `cme_iff_transition_char_vanish`. Reformulation only — all convergence techniques require randomness/stationarity |
| T2.7 | VCB (Vanishing Conditional Bias) | Fiber sums F(a) proportional to V(a) | F(a) = μ·V(a) + o(N) for common μ | OPEN | #104, #106, #107 | VCB + PED → CCSB (proved). VCB alone → CCSB ⟺ PED (#106). μ≈1 (kernel confinement) irrefutable. BDA counterexample on (Z/3Z)* (#107) |
| T2.8 | Surjection lemma | Surjective subgroup Λ ↦ ∏ Cᵢ | Every coset of Λ meets the death set | PROVED | — | `surjective_subgroup_coset_meets_death`. Walk never ALGEBRAICALLY trapped. But dynamical trapping is still possible |
| T2.9 | Cofactor Identity / "+1 Shift" | Walk w(n), multiplier m(n), cofactor c(n) | w(n)+1 = m(n)·c(n), χ(w(n)+1) = χ(m(n))·χ(c(n)) | PROVED (infrastructure) | — | `shifted_walk_eq_mult_mul_cof`, `char_shifted_walk_eq_char_mult_mul_char_cof` (EM/Reduction/DSLInfra.lean, Session 115). Cofactor c(n)=(P(n)+1)/seq(n+1). Identity genuine beyond telescope. Hit ⟺ cofZ=0 (`walkZ_eq_neg_one_iff_cofZ_zero`). BUT cofactor is a JOINT quantity (harder than multiplier alone), runs into Marginal/Joint Barrier. Infrastructure for future use, not a route to DH/CME |
| T2.10 | Ensemble StepDecorrelation analysis | CRT invariance + ensemble averaging | SD requires JOINT equidist of (genProd n j, genProd n k) mod q | OPEN | #98 (variant) | Session 120 analysis. Core obstacle: both genSeq n j and genSeq n k depend on SAME non-mod-q CRT coordinates of n. CRT invariance gives mod-q blindness but NOT inter-step independence. Marginal equidist of each genSeq ≠ joint independence. **Session 123 update**: JAE as defined is TAUTOLOGICAL (product of marginals, not joint density). JSE route genuinely bypasses #98 (ensemble-level, not per-step). SCRTI and corrected-JAE are ORTHOGONAL independence assertions (different moduli vs different steps). **Session 124 update**: JAE bug FIXED (genuine joint density `sqfreeJointAccumDensitySame` added, old renamed with WARNING, `aep_implies_jae_marginal` proved trivial). JSE base case **downgraded to 3/10** (conditioning-prime decomposition requires BV-level sieve estimates). Ensemble chain caps at a.a. GenMC, NOT MC for n=2. Route decision: DSL is sole path to actual MC |
| T2.11 | SCRTI bootstrap (all primes) | SquarefreeCRTIndependence + equidist(k,r) for one prime r | equidist(k,q) for ALL primes q ≠ r | PARTIAL (compilation pending) | — | Session 123. Decompose sqfreeAccumCount by r-fiber. Nonzero b terms: joint → 1/(q-1)·1/(r-1), sum over (r-1) b's → 1/(q-1). Zero-class → 0 by partition. `scrti_bootstrap_all_primes` partially formalized in EM/Ensemble/CRTFreedom.lean |
| T2.12 | JSE→GenMC master chain | JSE + PerChiCancellationBridge + WeylHittingBridge | GenMC (density-1 starting points) and MC (via n=2 specialization) | PROVED (infrastructure) | — | Session 124. `jse_implies_nontrivial_cancellation` (JSE+PerChiBridge → char cancellation). `cancel_weyl_implies_gen_mc` (WeylBridge + cancellation → GenMC). `cancel_weyl_implies_mc` (n=2 specialization → MC via `Nat.squarefree_two`). Two open Props: PerChiCancellationBridge (concentration→cancellation per chi) and WeylHittingBridge (cancellation→cofinal hitting via Weyl). Full chain: JSE → nontrivial SD → (PerChiBridge) → concentration → (WeylBridge) → hitting → MC |
| T2.13 | Return-Time Coprime Cross-Term Control | Fiber return visits with pairwise coprime multiplier primes + CRT invariance | Cross-term sign control at return visits | UNTRIED | — | Session 152. At return visits to fiber a, multiplier primes are pairwise coprime (`return_visit_mult_coprime`). Each new character value is "fresh" via CRT. Cross-term sign might behave like martingale difference. Obstructed by fiber-specific QR concentration: nothing prevents all return-visit multipliers at one fiber from being QR. Feasibility 2/10 |

### T3: Character & Representation Theory

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T3.1 | Character product formula | Walk on finite abelian group, character χ | χ(w(n)) = χ(w(0)) · ∏_{k<n} χ(m(k)) | PROVED | — | `char_walk_product`. The fundamental algebraic identity for the walk |
| T3.2 | Telescope identity | Consecutive walk values | χ(w(n+1)) = χ(w(n)) · χ(m(n)) | PROVED | #103 | The COMPLETE algebraic content of the walk. Only two decompositions: by value (CME) or by lag (HOD). No third route |
| T3.3 | Character orthogonality | Characters of finite abelian group | ∑_χ χ(a)χ̄(b) = |G|·δ_{ab} | PROVED | #48 | Using orthogonality to prove equidistribution is circular: V(a)=N/(q-1) IS equidistribution |
| T3.4 | Littlewood-Offord (cyclic) | Random ±1 variables, anti-concentration | Bounds on P(∑ ε_i x_i = s) | DEAD | #82, #83 | Reduces to Dec/HOD for cyclic groups (#82). Inverse LO FALSE for d≥3 (#83): alternating ω,ω² has large walk sum with zero concentration |
| T3.5 | Pseudo-independence notions | Pair mixing, exponential decay, k-point decay | Substitute for full independence | DEAD | #84 | Pair mixing = Dec (too weak). k-point decay = HOD (unverifiable). Block independence = HOD at coarser scale. All reduce to known hierarchy |

### T4: Algebraic Number Theory

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T4.1 | Chebotarev density theorem | Number field extension K/Q, Frobenius | Density of primes with given splitting type | MATHLIB BLOCKED | #9 | ~5000+ lines not in Mathlib. Would give SieveEquidistribution but NOT SieveTransfer (population ≠ orbit) |
| T4.2 | Kummer theory | Cyclotomic extensions, p-th power residues | Splitting of primes by residue class | MATHLIB BLOCKED | #9 | Requires Chebotarev. ONLY algebraic route not equivalent to a dead end |
| T4.3 | Class field theory | Abelian extensions, Artin map | Reciprocity law for splitting | MATHLIB BLOCKED | — | Far beyond current Mathlib. Even if available, gives population-level (SieveEquidist), not orbit-level |
| T4.4 | Booker-Simon results | Second EM sequence (maxFac variant) | Generalized EM can miss primes | N/A | #57 | maxFac has algebraic structure via cyclotomic polynomials. minFac has NO algebraic geometry — purely sieve. Confirms EM hardness |
| T4.5 | Tao-Teräväinen Correlation Transfer | Pilatte-type correlation estimates + Buchstab decomposition | JSE base case via partial multiplicative structure | UNTRIED (likely BLOCKED) | #109 | Session 152. Apply arXiv:2512.01739 correlation framework to chi(minFac(n+1)) via Buchstab identity. Non-multiplicativity barrier applies but Buchstab provides partial multiplicative structure. Requires genuinely new ANT, not formal methods. Feasibility 2/10 |
| T4.6 | Number field extensions (O_K for K/Q) | Prime ideal 𝔭 of O_K above r; character χ of (O_K/𝔭)× | χ restricted to integer walk = Dirichlet character mod r | PROVED IMPOSSIBLE | #135, #136 | **Universal Confinement Theorem** (Session 180): Z → O_K/𝔭 factors through prime subfield F_r. Applies to ALL K/Q simultaneously: Q(i), Q(i,√p), cyclotomic, arbitrary. Hecke Grössencharacters add archimedean growth factors only, no new phase content. `EM/GaussEM/GaussConfinement.lean` (347 lines, 0 sorry). Do NOT re-propose any number ring extension |

### T5: Abstract Algebraic Frameworks

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T5.10 | **Schematic/AG no-go formalization** | Basic commutative algebra + multiset/divisor combinatorics | Formalize durable S-Schematic insights without AG: (i) principality needed for “+1” on ideals, (ii) squarefree/coprime cascade in Dedekind-like setting, (iii) no lower bound on support size from degree alone, (iv) Mason–Silverman weakens with genus parameter | **RECOMMENDED (infrastructure)** | — | Session 293 follow-up: these lemmas are *negative/structural* and avoid orbit-specificity loops; they prevent future re-proposals of positive-genus/RR/Brill–Noether routes by making the obstructions explicit in Lean. Feasibility 6–9/10 depending on target.

### T5: Abstract Algebraic Frameworks

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T5.1 | SDDS framework | Factoring rule Φ, orbit sequence | Abstract sieve-defined dynamical system | PROVED | — | `EM/SDDS/Dynamics.lean`, `EM/SDDS/Bridge.lean`, `EM/SDDS/Reduction.lean`. Full bridge to EM. `CoprimeCascade` proved for ALL SDDS. `SuperExponentialGrowth` proved for EM |
| T5.2 | Bundle Walk / product group | Walk on ∏(Z/qZ)× | Simultaneous analysis across primes | DEAD | #101 | Avoidance density → 0 is population-level. Character sums don't factor (shared index). Counterexample: {3,4} in (Z/11Z)* avoid -1=10 |
| T5.3 | Walk periodicity dichotomy | Walk eventually periodic or aperiodic | Periodic → finite check; aperiodic → equidist? | DEAD | #100 | Periodic walks do NOT automatically give o(N) char sums. Trichotomy reduces to existing barriers. Ruling out periodicity = SieveTransfer |
| T5.4 | Bottleneck Decorrelation Axioms | Per-Step CRT + Exponential Growth + Generation | Abstract class-of-sequences framework → VCB? | DEAD | #107 | Explicit counterexample on (Z/3Z)*: all three axioms satisfied but VCB fails. Per-step CRT pointwise; VCB needs aggregate control |
| T5.5 | ExistentialCME weakening | ∃ c,n: w(n)=c, m(n)=-c⁻¹ | Single hit at death curve | DEAD | #105 | ExistentialCME IS DH. Tautological weakening — Fourier identity carries zero new information. Aperiodic avoidance construction exists |
| T5.6 | Non-recurrence + Generation + PBI | Bounded consecutive visits + multipliers generate G + position-blind | Equidistribution? | DEAD | #4, #107, #115 | Session 136. Counterexample: {2,3} cycling on (Z/5Z)* satisfies all three (f(q)=1, generation, PBI) but walk confined to {2,4}. Non-recurrence bounds stalling, not cycling. Ordering problem is fundamental |
| T5.7 | Lyapunov-Fiber Coupling | Walk Lyapunov function L(N) + fiber char sums F(a,N) | Coupled identity J(N) relating visit equidist to fiber cancellation | DEAD | #124 | Session 154. EQUIVALENCE COLLAPSE (feasibility 1/10). J(N) is marginal (bilinear contraction loses joint info). One-step recurrence J(N+1)-J(N) contains F(w(N),N) = active-fiber char sum = CME gap. Telescoping reveals ∑F(w(k),k) = full CME problem in disguise. Cauchy-Schwarz gives bounds in wrong direction (lower bound on FiberEnergy). J(N)=o(N) is 1 constraint on (q-1)-dimensional problem. Maps to #110, #104, #120 |
| T5.8 | Hypercube Fourier on SubProd(n) | SubProd(n) = {prod of subsets of S_n} identified with {0,1}^{n+1}, noise sensitivity of chi(genSeq(prod, k) mod q) | Population equidistribution of minFac mod q over SubProd(n) | UNTRIED (1/10) | #90 (strengthened) | Session 160. Genuinely new angle (not in any prior session). Boolean hypercube identification is natural. KKL/BKS/hypercontractivity tools require extension from Boolean to S^1-valued (unproved). Noise sensitivity COUNTERPRODUCTIVE: decorrelates orbit point from population mean. High total influence Inf_j(f) >= c > 0 for j <= k (linear total influence). KKL/hypercontractivity give O(1/√n) at best, not O(2^{-δn}). Exponential concentration impossible. Support-constrained Alladi = existing PE. BV = #108. Coupling requires CME (#90, #98, #107). |
| T5.9 | PathSurvival / Supercritical Branching | Binary tree from acc=2 with minFac/secondMinFac branching | survival/death ratio unbounded | OPEN (2/10) | -- | Session 231. FALSE for q in {3, 7, 43} (pre-branching universal death: first 3 P+1 values are prime, so all paths share same accumulator through step 2). Supercritical branching heuristic applies after step 3 (expected branching factor 2 - 1/(q-1) > 1). Self-consistent tree structure prevents direct Galton-Watson application. TCA + PathSurvival => RandomTwoPointMC (proved conditional). TCA and PathSurvival are formally independent. Orbit-specific (anchored at acc=2) but involves 2^N-path population. |

---

## Decomposition Strategies

### D1: Fiber decomposition (by walk position)
Split S_N = ∑_a ∑_{n:w(n)=a} χ(m(n)). Character sum over fiber at position a is the CME condition. **Status**: explored, IS the CME approach. Density-1 CME ≡ full CME (#93).

### D2: CRT decomposition
Factor q = q₁·q₂ coprime, work in each coordinate separately. **Status**: explored. CRT surjectivity proved. Per-step independence DOES NOT give sequence-level independence (#98, #107, #115).

### D3: Subgroup lattice decomposition
Analyze DH failure by which proper subgroups could trap the walk. For safe primes (order 2p), the lattice has exactly 3 proper subgroups. Generation forces escape from all three simultaneously. **Status**: explored. `dh_failure_distributional_gap` proves DH failure is analytically invisible to lattice structure.

### D4: Telescope / Abel decomposition
Use χ(w(n+1)) = χ(w(n))·χ(m(n)) to relate walk sums to multiplier sums. **Status**: EXHAUSTED (#103). Only two outcomes: by-value = CME, by-lag = HOD. Abel summation gives O(N²) remainder (wrong direction).

### D5: Excursion decomposition
Split walk into maximal return-to-basepoint segments. Each excursion contributes a bounded character sum. **Status**: explored. Formalized in `EM/Transfer/Excursion.lean`. Blocked by EIP (excursion independence — requires inter-excursion decorrelation).

### D6: Product group decomposition
Embed the single-prime walk into ∏_q (Z/qZ)×. **Status**: DEAD (#101). Character sums don't factor across components (shared minFac index).

---

## Generalization Strategies

### G1: Weaken the algebraic target
Instead of proving DH for all primes:
- SHH: weaken to "MC(<q) + SE → hit past sieve gap" — already the primary reduction. **PROVED**
- Safe prime special case: simpler lattice, but DH failure equally possible (#98 via distributional gap). **EXPLORED, no leverage**
- Small primes only (q ≤ B): SE instances proved for q ≤ 157, but MC needs ALL primes. **DEAD**

### G2: Abstract the recurrence
Instead of P(n+1) = P(n) · minFac(P(n)+1):
- SDDS framework: abstract factoring rule. **EXPLORED** — full bridge, coprime cascade for all SDDS, but `SieveMapEquidistribution ≈ MC`
- "Any walk where generators satisfy CRT + growth + generation" — **DEAD** (#107, explicit counterexample)
- "Any walk where the multiplier map is position-blind" — **DEAD** (#98, counterexample: {2,3} in (Z/5Z)*)

### G3: Grothendieck move — change the group
- Work in ∏_q (Z/qZ)× (profinite completion) → **DEAD** (#101, doesn't simplify)
- Work in function field analogue → **DEAD** (Sessions 166-168, Dead Ends #127, #129): Weil RH gives PE unconditionally but orbit-specificity identical. FFLM/Deligne/monodromy also dead (cyclotomic counterexample). All G3 sub-items CLOSED.
- Work in a Lie group with the same generation property → **UNTRIED** but EM is intrinsically discrete

### G4: From algebraic to analytic
Instead of proving DH algebraically, prove it analytically:
- CME as analytic target (fiber character sums) → this IS the project strategy
- CCSB as analytic target (walk character sums) → proved equivalent to MC
- Kummer/Chebotarev as algebraic input to analytic reduction → **MATHLIB BLOCKED**

### G5: Exploit the coprimality cascade
Consecutive orbit terms P(n), P(n)+1 are coprime; P(n) is squarefree. Can this be leveraged?
- `CoprimeCascade` proved for all SDDS — but gives no equidistribution information
- Coprimality + roughness CANNOT rule out long QR runs (#111)
- Coprimality constrains WHICH residues appear, not their QR character
**Status**: structural property fully formalized, no dynamical content extractable.

---

## The Frontier (what might actually work)

### F1: Kummer/Chebotarev route
The ONLY algebraic approach not equivalent to a known dead end. Operates via algebraic number fields rather than harmonic analysis. **Blocked on**:
- Chebotarev density theorem NOT in Mathlib (~5000+ lines)
- Adaptation from maxFac (Booker-Simon) to minFac is open
- minFac has NO algebraic geometry — purely a sieve question

### F2: New Mathlib infrastructure
If Mathlib adds Chebotarev, class field theory, or Dirichlet PNT, blocked approaches become viable. Monitor Mathlib development.

### F3: Beyond the Algebraic Exhaustion Thesis
Sessions 72-82 showed the telescope identity exhausts all algebraic content. A genuinely new approach would need to:
- Bypass the telescope entirely (not decompose S_N algebraically)
- Use non-algebraic properties of minFac (sieve/analytic)
- Find a "fifth way" past the Four-Way Blocker

No such approach is currently known.

### F4: Structural lemmas supporting analytic approaches
The algebraic agent's most productive role is providing INFRASTRUCTURE for analytic attacks:
- Group-theoretic lemmas about (Z/qZ)×
- CRT identities and surjectivity results
- Character sum identities and transformations
- Departure graph structural constraints

---

## Track Record

| Session | Proposal | Outcome | Advancement |
|---------|----------|---------|-------------|
| 72 | Quasirandom walk / Bogolyubov-Ruzsa | Dead ends (reduce to #82, #95, #4, #80) | 0 |
| 74 | Summable Decorrelation (SD) axioms | Dead end #104 (≡ VCB, no new leverage) | 0 |
| 75 | First passage / ExistentialCME | Dead end #105 (≡ DH) | 0 |
| 78 | VCB → CCSB without PED | Dead end #106 (≡ PED itself) | 0 |
| 79 | Bottleneck Decorrelation Axioms | Dead end #107 (counterexample on Z/3Z*) | 0 |
| 82 | Rough number concentration for NLR | Dead end #111 (counterexample: coprimality insufficient) | 0 |
| 93 | Departure Graph core infrastructure | PROVED (12 theorems: generation→escape, trapping, oracle) | 1.0 |
| 94 | Infinite recurrence + safe prime lattice | PROVED (8 theorems: pigeonhole, lattice analysis) | 1.0 |
| 95 | Single Hit Theorem | PROVED (`single_hit_implies_mc`) | 1.0 |
| 97 | SDDS framework | PROVED (3 files, 447 lines, full bridge) | 1.0 |
| 98 | Safe Prime DH Dichotomy + Target Avoidance | PROVED (6+4 theorems) + Dead end confirmed | 0.8 |
| 100 | CRT Fiber Independence | PROVED (10 theorems, NAO closed) | 1.0 |
| 104 | CoprimeCascade for all SDDS | PROVED (`SDDS.coprimeCascade`) | 1.0 |
| 109 | Accumulating CRT Independence | Dead end #115 (dimensional explosion illusory) | 0 |
| 115 | Cofactor Identity / "+1 Shift" analysis | PROVED (13 theorems, +204 lines EM/Reduction/DSLInfra.lean). T2.9 infrastructure added. Not a route to DH/CME (cofactor is joint quantity). Literature: zero external leverage | 0.5 |
| 118 | Closeable ensemble Props analysis | Ranked 5 open Props by feasibility. Identified EnsembleEquidistImpliesDecorrelation → Dead End #98 (avoid). Identified CharVarianceImpliesConcentration Tendsto gap (needs reformulation). Led to successful formalization of EnsembleMultEquidistImpliesCharMeanZero. | 0.8 |
| 120 | StepDecorrelation provability analysis | SD requires JOINT equidistribution (not marginal). Core obstacle: shared non-mod-q CRT coordinates. Proposed JointAccumulatorEquidist reformulation (provable reduction). Feasibility 2/10 for direct proof. T2.10 added | 0.5 (structural characterization of the gap) |
| 121 | JSE → SD reduction + CRTPropStep base case analysis | 5 theorems proved (JSE→SD, cross_term_density_decomp, 3 sqfreeJointSeqDensity bounds). JSE now sole remaining gap. CRTPropStep base case feasible (6/10) via CMFE; general step 2/10. T2.10 updated | 1.0 |
| 123 | JAE→JSE and EME→SD bypass analysis | JAE definition bug found (TAUTOLOGICAL — product of marginals). JSE route confirmed to genuinely bypass Dead End #98. SCRTI and corrected-JAE orthogonal. Route B (JSE bypass) strictly better than Route A. JSE base case (j=0,k=1) feasible at 6/10. Critical gap: ensemble gives a.a. GenMC, not MC for n=2. T2.10 updated, T2.11 added | 0.8 (critical definitional bug found + route analysis) |
| 124 | JSE base case + route decision + JSE→MC chain | JAE fixed (7 theorems: genuine joint density, partition identity, bounds, `aep_implies_jae_marginal`). JSE(0,1) feasibility **downgraded to 3/10** (same infra as SRE). JSE→MC chain PROVED (3 theorems: `jse_implies_nontrivial_cancellation`, `cancel_weyl_implies_gen_mc`, `cancel_weyl_implies_mc`). Route decision: ensemble caps at a.a. GenMC; DSL is sole path to MC. T2.10 updated, T2.12 added | 0.8 (route clarification + 10 theorems) |
| 136 | Bag exhaustion + non-recurrence + cumulative coprimality | All three reduce to existing dead ends. Bag exhaustion = MC (equivalence with DH via captures_target). Non-recurrence + Generation + PBI: counterexample on (Z/5Z)* with {2,3} cycling (maps to #4, #107, #115). Cumulative coprimality: vacuous for c!=0, circular for c=0 (maps to #92, #105, #115). T5.6 added. | 0 |
| 137 | CRT decorrelation of cross-term C(j,k) | Structural analysis: C(j,k,X)=o(X) follows from JSE (already formalized via cross_term_density_decomp + joint_step_equidist_implies_step_decorrelation). Per-prime conditioning route confirmed at 4/10. No obstruction (no new dead end). Variance route does NOT map to existing dead ends. JSE remains sole gap, sieve-theoretic in nature | 0.5 (structural confirmation + route assessment) |
| 138 | OCE (orbit-conditional equidist) vs CME analysis | EQUIVALENCE COLLAPSE: OCE = CME by `rfl`. EM/Transfer/CRTPointwise.lean formalized (263 lines, 8 theorems, 0 sorry). `oce_eq_cme`, `returnVisitCharSum_eq_fiberMultCharSum`, `oce_implies_mc`, `dsl_implies_crt_bridge`, `all_routes_to_mc`. Maps to #90, #98, #107, #115. Valuable closure: prevents re-exploration of orbit-conditioning angle | 0.5 (formalized closure + 8 theorems) |
| 152 | Genuinely new algebraic strategies for DSL | 5 proposed directions map to existing dead ends (#105, #101, #9, #4, #136). 3 genuinely new UNTRIED techniques identified: T5.7 Lyapunov-Fiber Coupling (3/10), T4.5 Tao-Teräväinen Correlation Transfer (2/10), T2.13 Return-Time Coprime Cross-Term Control (2/10). No proposal closes DSL. Algebraic Exhaustion Thesis reconfirmed. Chebotarev still MATHLIB BLOCKED (March 2026). T5.7, T4.5, T2.13 added | 0.3 (landscape analysis + 3 UNTRIED techniques identified) |
| 154 | T5.7 Lyapunov-Fiber Coupling assessment | DEAD END #124, EQUIVALENCE COLLAPSE. J(N) one-step recurrence contains F(w(N),N) = active-fiber char sum = CME gap. Cauchy-Schwarz gives bounds in wrong direction. J(N)=o(N) too weak (1 constraint on (q-1)-dim problem). Maps to #110, #104, #120. T5.7 updated to DEAD. No remaining algebraic techniques above 2/10 feasibility | 0.2 (dead end confirmation, catalog update) |
| 157 | FPM ↔ CME equivalence analysis | FPM = Dec = EMDirichlet by `rfl` (NOT new). Does NOT imply CME (gap = EMDImpliesCME), CCSB (Dead End #117), or MC. Hierarchy: CME → {CCSB, Dec=FPM}, CCSB → MC, Dec → PED. Dec and CCSB INCOMPARABLE. "Bag-of-primes" = PBI + SE. No new formalization needed | 0.1 (confirms existing hierarchy, closure) |

| 158 | CRT spreading + multi-modulus Borel-Cantelli | CRT spreading = PE (#98). Multi-modulus = cross-modulus ≠ cross-time (#123). Borel-Cantelli gap = #90. FiberOrbitEscape strictly stronger than DSL. Finite-fiber trapping non-closure. No new dead ends — all map to existing entries | 0 (confirms: fiber decomposition provides no new algebraic leverage) |
| 160 | Support-constrained Alladi + SubProd(n) hypercube ensemble | 5 of 6 components map to existing infrastructure/dead ends. Hypercube Fourier (T5.8) genuinely new but 1/10 feasibility: noise sensitivity counterproductive for orbit specificity (decorrelates orbit point from population mean), high total influence kills exponential concentration, KKL gives O(1/√n) not O(2^{-δn}). Support-constrained Alladi = EM/Population/AlladiDensity.lean. BV = #108. Coupling = #90/#98/#107. EM/Transfer/SieveConstraint.lean formalized (261 lines, 21 theorems, 0 sorry). T5.8 added | 0.3 (landscape analysis + infrastructure + 1 new UNTRIED technique at 1/10) |
| 163 | Adelic Fourier inversion + profinite pairwise-vs-kwise | **CRTFiberImpliesMWI PROVED** (formalizer, ~145 lines). `mme_iff_walk_autocorrelation` PROVED. CPDImpliesCRTFiber assessed 6/10 (orbit-dependent Fourier coefficients). **Key finding**: CCSB+CPD→UPE assessed 8/10 via SquarefreeCompositeCSB induction (product chars factor through CRT into composite Q = ∏qᵢ, CCSB extends to squarefree Q by induction). This does NOT map to pairwise ⊬ mutual independence because CRT structure constrains the coordinates. Potential formalization target: ~400-600 lines. FLE gap confirmed (SE+PRE ⊬ FLE) | 1.0 (2 proved theorems + 1 high-value target identified) |
| 169 | Multiplicative large sieve for EM orbits (5 questions) | ALL 0/10. Standard large sieve = average-over-q (#90, #108). minFac NOT multiplicative (proved). Sieve orbit indicator = SieveTransfer gap. CRT cross-modulus ≠ cross-time (#123). No pointwise sieve exists (Artin's conjecture analogy). **New framing**: orbit-specificity ↔ pointwise sieve impossibility ↔ Artin's conjecture analogy | 0 (confirms: sieve orbit approaches = CCSB by `rfl`, minFac non-multiplicativity blocks all Linnik-type approaches) |
| 170 | FF-MC infrastructure built (EM/FunctionField/Bootstrap.lean, EM/FunctionField/SubgroupEscape.lean, EM/FunctionField/CyclicWalkCoverage.lean, EM/FunctionField/MultiplierCCSB.lean) + Dead End #130 | +2302 lines, 112 decls; SelectionBias = CME confirmed; FF-MC complete except universal DSL gap | Dead End #130: SelectionBiasNeutral / ConditionalCharEquidist / WeilIIForFiber EQUIVALENCE COLLAPSE (maps to #90). FF setting provides PE for free (Weil RH) but DSL gap is universal across all algebraic settings. Fiber variety techniques already exhausted via AFG dead ends. Do NOT re-attempt FFMultiplierCSB_raw or WeilIIForFiber after comprehensive formal proof that all three are CME under disguise |

| 179 | Gaussian EM sequence: norm-1 subgroup advantage? | **Dead End #135** (TECHNIQUE MISMATCH). Orbit-specificity is property of DETERMINISTIC GREEDY SELECTION, not ambient ring. For inert primes, F_{p²}× has MORE characters = HARDER. No number ring helps. EM/GaussEM/GaussEMDefs.lean + EM/GaussEM/GaussWalkStructure.lean created (621 lines, 0 sorry). T4.6 added | 0.3 (infrastructure + dead end confirmation) |
| 180 | Universal Confinement (biquadratic Q(i,√p), Hecke chars, NormTwistedCME) | **Dead End #136** (PROVED IMPOSSIBLE). Z → O_K/𝔭 factors through F_r (prime subfield). Hecke chars = Dirichlet × growth factor. NormTwistedCME = different walk. Kills ALL number field extensions for integer walk. EM/GaussEM/GaussConfinement.lean created (347 lines, 31 theorems, 0 sorry). T4.6 added | 0.3 (formalization of universal negative result) |
| 183 | Reconvergence / Ratner route / algebraic rigidity | Pre-flight ABORT. Reconvergence Lemma FALSE (butterfly sensitivity: changing one multiplier cascades through all future steps). Even weakened version = `walk_readout_from_multipliers` (proved). Cyclotomic = CRT invariance. Multiplicative energy = CME circular. Literature: zero orbit-specific equidist results applicable. Maps to #4 (ordering), #90 (orbit specificity), #101 (bundle walk), #130 (generation ≠ coverage) | 0 |

| 189 | FF Weak MC: degree escape + capture counting | EM/FunctionField/WeakMC.lean created (471 lines, 30 theorems, 0 sorry). `ffSeq_degree_tendsto_atTop` PROVED (degree escape). `captureCount_plus_missing` PROVED (pool partition). `captureExhaustive_iff_ffmc` PROVED. Literature: FF-EM novel, no prior work. Bank-Bary-Soroker-Rosenzweig (2015) for PNT in APs over F_q[t]. No Mathlib counting lemma for irred polys per degree | 0.8 (unconditional structural result + complete infrastructure, but orbit-specificity barrier still applies) |
| 214 | UFDImpliesUFDStrong gap assessment | Genuine gap confirmed. Maps to #90 (orbit specificity of ratio minFac/secondMinFac). Counterexample scenario: q=7, chi order 3, ratio in ker(chi). Three approaches at 1-3/10. RSE (RatioSubgroupEscape) cleanest reformulation but faces same barrier as SE for arbitrary sequences. Not provable (1/10). 8/10 as well-posed intermediate target. No new dead end. No technique catalog change. | 0.3 (structural analysis + landscape clarification) |
| 215 | Routes to UFDStrong formalization | MinFacRatioEscape (quantitative) → UFDStrong PROVED. MinFacRatioEscapeQual (qualitative) → quantitative PROVED (finite-range argument via Fintype + Finset.min'). OrbitMFRE → Qual via open bridge. 6-clause landscape PROVED. +318 lines EM/Advanced/VanishingNoiseVariant.lean, 17 theorems, 0 sorry. Key technique: gap function finite range (Finset (ZMod q)ˣ is Fintype). | 1.0 (3 independent routes formalized, key finite-range technique) |
| 222 | NFCE(5) infra + kernel confinement assessment | NFCE(5) Part 26 PROVED (11 theorems, +231 lines). Kernel confinement assessment: Q1-Q3,Q5 map to existing dead ends (#90, #108). **Q4 intersection argument genuinely new** (6/10 structural, 2/10 proof): total NFCE failure is self-correcting for q with q-1 having ≥2 distinct prime factors (⋂ kernels = {1}). T1.9 added. Part 27 formalization in progress. | 0.8 (11 proved theorems + new structural insight) |
| 223 | NonFaithfulCharSeparation proof | **NFCS PROVED** for groups with ≥2 distinct prime factors (3 theorems, +143 lines). Key discovery: NFCS FALSE for prime-power-order groups (Z/4Z counterexample). Intersection kernel dichotomy now fully operational for non-Fermat primes. Lean API: QuotientGroup.mk', MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity, mulCharToHom, Subtype.ext. T1.9 status → PROVED. | 1.0 (open Prop closed, important negative result about Fermat primes) |

| 234 | Iterated Cauchy-Davenport extension to general primes | **Dead End #137**: minOrder (ZMod q)× = 2 for ALL primes q ≥ 3. CD bound vacuous. Safe prime ⇒ q=3 only. Kneser not in Mathlib. +128 lines EM/Advanced/IteratedProductCoverage.lean (6 theorems, 0 sorry). T1.10 added | 0.3 (clear negative result + landscape closure) |
| 243 | Logarithmic CD strategy for MixedHitting | DEAD (reconfirms #137): isomorphism (Z/qZ)× ≅ Z/(q-1)Z maps minOrder 2 to minOrder 2 (q-1 always even). CD equally vacuous on additive side. Pivoted to reachable set growth (8 theorems, +184 lines EM/Advanced/EpsilonRandomMC.lean). `reachableAt_from_factor` = core growth lemma (σ' construction). | 0.5 (dead end reconfirmed + infrastructure) |

| 254 | Regeneration gap assessment (3 angles) | CRTPropagationStep MARGINAL (4/10, maps to #90/#130), Sieve Bounds VIABLE (7/10, new target), Mixing NON-VIABLE (2/10, needs measure theory). PointwiseSieveDecay proposed as new unconditional sieve-theoretic target. Regeneration IS easier than DSL/CME (ensemble averaging available). | 0.7 (new viable target identified, clear landscape analysis) |

| 258 | TSD-Hitting(5) and full TSD(3) assessment | Full TSD(3) **FALSE** (P=2 counterex: {0,2} reachable, unit 1 never). TSD-Hitting(5) 1/10 ((Z/5Z)× order 4, QR/QNR insufficient). **TSD-Hitting(3) is ceiling of purely algebraic TSD results.** Future TSD needs sieve/probability tools. Probability infrastructure Phase 1 created (EM/Probability/TransitionKernel.lean, 267 lines) | 0.5 (confirms algebraic ceiling + Phase 1 infrastructure) |

| 259 | Profinite Multiplier Generation + Goursat analysis | **EM/Adelic/ProfiniteGeneration.lean** (177 lines, 7 theorems, 0 sorry): `primeUnitsBelow_generate` (primes < N generate (ZMod N)×, pure NT), `mc_below_implies_full_generation` (MCBelow → full gen), `mc_implies_full_generation` (MC → full gen ∀N). Goursat analysis: Mathlib has `Subgroup.goursat_surjective` but adds ZERO content beyond FTA argument — classifies subgroups, not trajectories. T1.11 added (DEAD, #130). | 0.8 (7 proved theorems + clean closure of Goursat angle) |

**Success rate on novel proposals**: 24/43 (56%) led to proved theorems or actionable analysis. All successes were INFRASTRUCTURE (departure graph, SDDS, CRT fiber analysis, single hit, cofactor identity, ensemble bridge analysis, SD gap characterization, JSE→MC chain, sieve constraint infrastructure, FF-MC infrastructure, Gaussian EM foundations). All failures were attempts at CME/DH itself or reductions to existing dead ends.

| 262 | NFCE algebraic routes fully exhausted | ALL 6 questions → existing dead ends (#90, #98, #105, #109, #110, #111). NFCS PROVED for non-Fermat, FALSE for Fermat primes. NFCE infrastructure complete and optimal. Remaining gap sieve/analytic. TSD(5) subgroup escape formalized (13 theorems). T1.9 status confirmed | 0 (confirms algebraic exhaustion of NFCE) |
| 291 | Scoping S-Φ: POP vs ORB gating for essential range R(c̃) (Task C) | System (A) R(c̃) is POP: uniquely ergodic base, character criterion Haar-computable, CRT joint independence gives R(c̃) = ∏_q R(c̃)_q. System (B): ORB (framework inapplicable). Transfer A→B: ORB (Dead End #90). Coboundary test = CCSB reformulation (equivalence collapse). No new algebraic technique or dead end | 0 (definitive gating: POP for population, ORB for orbit; confirms CCSB = coboundary) |
| 292 | Scoping S-FF: Mason-Stothers + Galois + Drinfeld for FF-EM | ALL THREE TOOLS NON-VIABLE. C1 (Galois): OBSTRUCTED — Galois groups abelian (#129), collapse to PE. C2 (Mason-Stothers): TRIVIAL — Squarefreeness Absorption Principle (rad(P_n)=P_n absorbs radical budget; all identities give 1≤deg(rad(P_n+1)), trivially true). Non-vanishing derivative P_n'≠0 proved. C3 (Drinfeld): OBSTRUCTED — self-referential recursion blocks embedding, CFT=Chebotarev=PE. Double-edged sword: coprimality cascade enables sieve but defeats M-S. Option 3 (FF-AG route) CLOSED. 5 scoping documents created | 0.3 (structural insight: Squarefreeness Absorption Principle; confirms FF-AG closure) |
| 293 | Scoping S-Schematic: EM on elliptic curves/positive-genus curves | ALL SIX QUESTIONS NEGATIVE. Construction pathological (non-PID: "+1" undefined for non-principal ideals). SAP genus-independent (coprimality cascade = recursion property). Mason-Silverman WEAKENS with genus (+2g-2 term). No support lower bound in AG (D=d·P counterex). Walk on E(F_q) not more tractable (Frobenius trivial on degree-1, orbit-specificity setting-independent). F₁-transport: no functor. DEFER-higher-genus NOT warranted. Schematic EM direction CLOSED. Scoping program COMPLETE (6 passes, all NO-GO) | 0.2 (three structural insights: SAP genus-independence, Mason-Silverman monotonic weakening, no support lower bound in AG) |

**Pattern**: The algebraic agent excels at building structural infrastructure (departure graph, SDDS, CRT, safe prime analysis, ensemble analysis, equivalence closure). It consistently fails when attempting to close the CME/DH gap algebraically — the gap is NOT algebraic (#103 algebraic exhaustion thesis). Session 138 confirmed OCE = CME (equivalence collapse), providing formal closure on orbit-conditioning approaches. Session 152 added 3 UNTRIED techniques at 2-3/10 feasibility; Session 154 killed T5.7 (the highest at 3/10), leaving only T4.5 (2/10) and T2.13 (2/10). Session 160 added T5.8 (Hypercube Fourier on SubProd) at 1/10 — noise sensitivity is COUNTERPRODUCTIVE for orbit specificity. Session 169 confirmed minFac non-multiplicativity formally (proved) and Artin's conjecture analogy for pointwise sieve impossibility. Sessions 179-180 confirmed number ring extensions PROVED IMPOSSIBLE (Universal Confinement Theorem). T4.6 closes ALL number field approaches. Session 254: Regeneration gap assessment identified **PointwiseSieveDecay** as new viable (7/10) sieve-theoretic target that doesn't map to any existing dead end. The DSL gap remains fundamentally sieve-theoretic, but Regeneration (variant MC) is structurally easier — ensemble averaging + branching diversity available. Session 262: NFCE algebraic routes 100% exhausted — all 6 questions map to existing dead ends. Do NOT dispatch for NFCE. Session 293 closes the schematic EM direction (positive-genus curves) — SAP genus-independent, Mason-Silverman weakens monotonically, no support lower bound in AG. Scoping program now COMPLETE (6 passes, all NO-GO). Future dispatches should focus on PointwiseSieveDecay formalization, SpecificResidueClassFactor hypothesis analysis, Mathlib monitoring for Chebotarev, and monitoring Tao-Teräväinen/Pilatte for non-multiplicative extensions. Do NOT propose schematic EM on positive-genus curves, Riemann-Roch orbit constraints, Jacobian structure, F₁-transport, or Brill-Noether for specific divisors.
