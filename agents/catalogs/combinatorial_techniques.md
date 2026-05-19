# Combinatorial Technique Catalog

**Domain**: Combinatorial number theory, graph theory, extremal combinatorics
**Attack agent**: `attack_combinatorial`
**Last updated**: Session 260

**STATUS: COMBINATORIAL VECTOR EXHAUSTED (Session 37, reconfirmed Sessions 82, 86-87, 89)**

No remaining purely combinatorial path to MC exists. This catalog documents what was tried, why it failed, and what (if anything) the combinatorial agent should monitor for.

---

## How to use this catalog

1. **The combinatorial vector is exhausted.** Do NOT propose new combinatorial attacks unless genuinely new external mathematics emerges.
2. **Check the Marginal/Joint Barrier**: every combinatorial technique works with marginal properties (counts, densities, subsequences). DH requires joint (position, multiplier) information.
3. **Check the ordering problem**: combinatorial tools handle SETS or ARBITRARY orderings. EM needs results about its SPECIFIC ordering of multipliers as consecutive prefix products.
4. **Only viable role**: monitoring for new external mathematics and providing combinatorial infrastructure supporting analytic attacks.

---

## Technique Families

### T1: Hitting & Coverage

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T1.1 | DWH (Deterministic Walk Hitting) | Walk covers all elements of finite group | Every element is hit | PROVED (reduction) | — | `dwh_implies_mullin` proved. But DWH itself is equivalent to MC — not a technique, a reformulation |
| T1.2 | Single Hit Hypothesis | MC(<q) + SE → hit past sieve gap | MC for prime q | PROVED | — | `single_hit_implies_mc`. Weakest sufficient hitting condition. The primary reduction |
| T1.3 | Rotor-router coverage | Deterministic routing on graph, Euler tour guarantee | Every edge traversed in Eulerian multigraph | PROVED | — | `EM/Group/RotorRouter.lean`. Standalone result. Does NOT apply to EM walk: the walk is multiplicative on a group, not a rotor-router on a graph |
| T1.4 | Threshold hitting | Walk hits -1 within first T steps for specific T | ThresholdHitting(T) → MC | PROVED (T=11) | #1-3 | `threshold_11_implies_mullin'`. Cannot raise T by computation — need abstract proof for all primes |
| T1.5 | Walk periodicity → hitting | If walk eventually periodic, period analysis gives hits | Periodic → finite check | DEAD | #100 | Periodic walks don't automatically give o(N) char sums. Trichotomy reduces to existing barriers. Ruling out periodicity = SieveTransfer |

### T2: Subsequence & Product Methods

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T2.1 | Cauchy-Davenport | Elements in Z/pZ, sumsets | |A+B| ≥ min(p, |A|+|B|−1) | DEAD | #4 | Applies to ARBITRARY subsets, not consecutive prefix products |
| T2.2 | Erdős-Ginzburg-Ziv (EGZ) | 2p−1 elements of Z/pZ | Zero-sum subsequence of length p exists | DEAD | #4 | Same obstruction: ARBITRARY subsequences vs CONSECUTIVE prefix products |
| T2.3 | Davenport constant | Finite abelian group G | D(G) = min length guaranteeing zero-sum subsequence | DEAD | #4, #59-60 | DH needs PREFIX products reaching -1, not existence of zero-sum subsequences |
| T2.4 | Kneser's theorem | Sumsets in abelian groups | |A+B| ≥ |A|+|B|−|H| where H = stabilizer | DEAD | #59-60, #137 | Gives weaker bounds than direct arguments. Same ordering obstruction. Session 234: even iterated CD/Kneser with growing sets is vacuous via minOrder for (ZMod q)× (minOrder = 2). Kneser not in Mathlib (LeanCamCombi only) |
| T2.5 | Sequenceability / Gordon's conjecture | Abelian group G, ordering of elements | Some ordering of G\{0} gives all prefix sums distinct | PROVED (irrelevant) | #101 | `EM/Group/Pumping.lean`. Proves EXISTENCE of good orderings. EM needs its SPECIFIC ordering. Marginal/Joint Barrier |
| T2.6 | Subset products vs prefix products | Arbitrary subsequences of m(0),...,m(N) | Some product reaches target | N/A | #4 | The fundamental combinatorial obstruction: prefix products are a SPECIFIC ordering, not an arbitrary selection |

### T3: Quadratic Residue Methods

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T3.1 | QR obstruction | Legendre symbol analysis | At most 1.6% of primes fail ℓ=2 escape | PROVED | — | `EM/Group/QR.lean`. Useful structural bound but doesn't give DH |
| T3.2 | NoLongRuns → PED | No L consecutive QR multipliers | PED with δ=1/(2L) | PROVED | #80, #88, #111 | `NoLongRuns_implies_PED`. But NoLongRuns itself is unprovable: counterexample (#111) shows coprimality+roughness cannot rule out long QR runs |
| T3.3 | d=2 block analysis | Order-2 characters, kernel-escape blocks | Alternating sum structure | PROVED (infrastructure) | #80, #87, #88 | Complete d=2 infrastructure (~1400 lines). But PED controls total density, not block distribution. Adversarial block lengths defeat alternating argument (#88) |
| T3.4 | DPED → CCSB for d≥3 | Positive escape density for higher-order characters | CCSB via accumulation of escapes | DEAD | #21, #36, #87 | Counterexample: alternating ω,ω² satisfies DPED but walk sum Θ(N). Phase-aligned escapes for d≥3 |

### T4: Self-Avoidance & Graph Methods

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T4.1 | Self-avoidance constraints | Multipliers are distinct primes (past sieve gap) | Walk cannot return via same multiplier | PROVED | #27-35 | Self-avoidance is invisible to characters. Does not constrain visit distribution |
| T4.2 | Coprimality refreshing | Consecutive P(n)+1 values coprime | Death rate algebraic structure | PROVED | #113 | `coprimality_refreshing_int/nat`, `no_safe_cycle`. Algebraic structure is descriptive only — no proof leverage |
| T4.3 | Simultaneous Avoidance | Walk on ∏(Z/qᵢZ)× avoids shrinking safe set | Eventually must hit death set | DEAD | #101 | Counterexample: in (Z/11Z)*, {3,4} generate full group but walk visits only {1,3}, avoiding -1=10. Population-level density arguments cannot constrain deterministic walk |
| T4.4 | Information-theoretic arguments | Entropy, mutual information, compression | DH from information constraints | DEAD | session 68 | EM is DETERMINISTIC — zero Shannon entropy. Category error. Information theory requires probabilistic model |

### T5: Orbit & Cycle Analysis

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T5.1 | Orbit analysis | Walk in finite group, cofinal orbits | Quotient walks, return structure | PROVED | — | `EM/Equidist/OrbitAnalysis.lean`. Cofinal cycle product-one. Infrastructure, not proof technique |
| T5.2 | Cycle product equidistribution | Return products R_k = ∏ m(j) over return cycles | Equidist of R_k mod auxiliary primes? | DEAD | #113 | Telescope reduces R_k to lag-1 autocorrelation = CCSB. Product structure (ℓ≥2) gives ZERO advantage. Circularity |
| T5.3 | Missing prime accumulation | Primes missing from EM would accumulate | Borel-Cantelli contradiction? | DEAD | #114 | Pairwise quasi-independence = CME for single fiber. Kochen-Stone = SieveTransfer. Equivalence collapse |
| T5.4 | Multi-modular coupling | Force character sum cancellation via CRT | Joint equidistribution across moduli | DEAD | #98, #101 | CRT per-step ≠ sequence-level. Bundle walk dead end |

---

## Decomposition Strategies

### D1: Block decomposition
Split [1,N] into blocks. For d=2, kernel/escape alternation structure is fully understood (~1400 lines). **Status**: EXHAUSTED for d=2 (#80, #88). Inapplicable for d≥3 (#87 phase alignment).

### D2: Self-avoidance decomposition
Group walk steps by whether the multiplier was seen before. Past sieve gap, all multipliers are distinct. **Status**: explored. Distinctness is invisible to characters (#27-35).

### D3: Return decomposition
Group walk steps by returns to basepoint (excursions). **Status**: explored (`EM/Transfer/Excursion.lean`). Blocked by inter-excursion decorrelation (= CME).

### D4: QR/QNR decomposition
For d=2, split steps by Legendre symbol. **Status**: EXHAUSTED. Full d=2 infrastructure proved but adversarial blocks defeat the argument.

### D5: Multi-modular decomposition
Analyze walk simultaneously across multiple moduli. **Status**: DEAD (#101, #98). CRT product doesn't simplify.

---

## Generalization Strategies

### G1: Weaken the combinatorial target
- From DH to SHH — **PROVED** (single hit theorem)
- From "all primes" to "density 1 of primes" — still DH (density 1 is NOT a weakening for a conjecture about ALL primes)
- From CCSB to "positive fraction of characters" — ≡ full CCSB (#93, equivalence collapse)

### G2: Extend the combinatorial framework
- Combine SE + confinement analysis exhaustively — **EXHAUSTED** (Session 76)
- Add QR conditions to SE — **EXPLORED** (EM/Group/QR.lean, no DH leverage)
- Add departure graph structure — **EXPLORED** (infrastructure only)

### G3: Hybrid combinatorial-analytic
- NoLongRuns as input to analytic argument — NLR → PED → (gap) → MC. The gap IS CME
- Self-avoidance as input — invisible to characters
- Block structure as input — only helps for d=2, and even there adversarial blocks are fatal

### G4: Grothendieck move — different combinatorial objects
- Sumsets instead of products → wrong operation for multiplicative walk
- Hypergraph coloring instead of group walk → **UNTRIED** but no clear connection to EM
- Extremal graph theory (Szemerédi regularity) → **UNTRIED** but requires density/randomness

---

## The Frontier (what might work for the combinatorial agent)

### F1: Monitor for new external combinatorics
The combinatorial vector is exhausted with CURRENT techniques. New mathematics could change this:
- Advances in deterministic walk coverage on groups
- New zero-sum/subsequence results for PREFIX products
- Results about specific orderings (not existence of good orderings)

### F2: Combinatorial infrastructure for analytic attacks
The most productive role is building lemmas that support the analytic or algebraic agents:
- Counting arguments (pigeonhole, inclusion-exclusion)
- Graph-theoretic structural lemmas
- Extremal estimates on visit distributions

### F3: New Mathlib infrastructure
Monitor Mathlib for additions to:
- Combinatorial number theory (additive combinatorics, sumset theory)
- Graph theory (expander, mixing)
- Finite group combinatorics

---

## Track Record

| Session | Proposal | Outcome | Advancement |
|---------|----------|---------|-------------|
| 1-4 | Computational approaches, Cauchy-Davenport | Dead ends #1-4 | 0 |
| 14-17 | Self-avoidance, periodicity, generation | Dead ends #27-35 | 0 |
| 18 | BRE from PED for d≥3 | Dead end #36 (phase alignment counterexample) | 0 |
| 37 | Comprehensive combinatorial review | **COMBINATORIAL VECTOR EXHAUSTED** | 0 (closure) |
| 41 | DPEDImpliesCSB for d≥3 | Dead end (alternating ω,ω² counterexample) | 0 |
| 46 | Littlewood-Offord variants | Dead ends #82-84 | 0 |
| 56 | d=2 block-length balance from PED | Dead end #88 | 0 |
| 61 | Density-1 CME / fiber energy | Dead ends #93-94 | 0 |
| 68 | Information-theoretic angles | Dead end (category error — EM is deterministic) | 0 |
| 82 | Rough Number Concentration for d=2 NLR | Dead end #111 | 0 |
| 86-87 | Systematic review / Coupled Walk | CONFIRMED: all angles covered | 0 (closure) |
| 89 | Simultaneous Avoidance | Dead end (≡ #101) | 0 |
| 97 | Missing prime accumulation | Dead end #114 | 0 |

| 246 | FEH combinatorial assessment (Q6-Q8): moving target, omega growth, UFDStrong→FEH | **3/10 overall**. Every route maps to #90. Q6 (moving target density) requires walk equidist = conjecture. Q7 (omega growth) ≈ MixedDiversity (Bunyakovsky-hard). Q8 (UFDStrong→FEH) blocked by character ≠ set-theoretic gap (#130). Maps to #90, #101, #117, #130. | 0 (assessment only; confirms exhaustion) |
| 260 | MixedDiversity→MixedHitting bridge analysis | **0-2% provable**. R_∞ is fixed point of factor-confinement closure. Coset impossibility (proved) eliminates algebraically structured proper fixed points. But Z/10Z counterexample (S={0,1,3,7,9}) shows set can escape all cosets while proper. Gap IS FactorEscapeHypothesis (arithmetic, not group-theoretic). All 5 proposed routes (branching+distinctness, coset, pumping, starting point, pigeonhole) map to #130. | 0 (assessment only; confirms exhaustion) |

**Success rate on novel proposals**: 0/15+ (0%) led to proved theorems. All purely combinatorial attacks on MC/DH/CCSB have failed.

**Pattern**: The combinatorial vector produces ZERO proofs. Every purely combinatorial approach hits either the ordering problem (#4: prefix products ≠ arbitrary subsets) or the Marginal/Joint Barrier (combinatorial tools capture counts/densities, not joint distributions). The exhaustion thesis (Session 37) has been confirmed repeatedly (Sessions 82, 86-87, 89, 246). **Do not dispatch this agent for novel attack proposals.** Use only for infrastructure, Mathlib monitoring, or evaluating genuinely new external results.
