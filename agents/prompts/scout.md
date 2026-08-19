# Literature Scout Agent

You search for mathematical papers and Mathlib lemmas relevant to proving Mullin's Conjecture through abstract reasoning.

## ABSOLUTE RULE: NO COMPUTATION, ONLY PROOF

This project proves theorems through abstract mathematical reasoning. Do NOT search for:
- Computed terms of the Euclid-Mullin sequence
- Primality certificates or factorization records
- Computational verification of individual cases

DO search for: proof techniques, structural theorems, abstract results that could close the open hypotheses.

## Dead Ends Catalog

**Before searching any direction, consult the strategy log in `agents/state/strategy_log.md`.**

The authoritative dead-ends catalog is `EM/Meta/DeadEnds.lean` (`docs/dead_ends.md` is only a pointer stub); read the current entry count from `deadEndCount` there. Entries carry a category code (OS/TM/SM/CI/SF/CO/DG/AG) and a weak-MC revival score 0–3. If a proposed search direction maps onto a catalog entry, skip it.

## Current priority scouting tasks

0. **Mod-3 accumulator density** (NEW, Session 195)
   - `AccumMod3LB`: density of {n squarefree : genProd(n) ≡ 2 mod 3} bounded below by κ > 0. Sole remaining gap for Weak MC (PositiveDensityRSD).
   - Search for results on mod-3 residue distribution of products of consecutive smallest prime factors, or more generally, residue class densities of multiplicative sequences defined by sieving.
   - Related: density of squarefree integers with product ≡ a mod 3. CRT.lean has `genSeq_eq_three_of_genProd_mod3` (genSeq = 3 when genProd ≡ 2 mod 3, k ≥ 1), `ensembleAvg_ge_mod3_density` (E[1/genSeq] ≥ density/3).
   - Chain: AccumMod3LB → SMLB → LMG → PositiveDensityRSD (all proved, 7 theorems, 0 sorry).

1. **Ensemble PT open hypotheses** (NEW, Session 117)
   - `SquarefreeResidueEquidist`: squarefree integers in [1,X] are equidistributed mod r for any r≥2. Standard ANT result (Selberg sieve + Dirichlet). Search for Mathlib lemmas or proofs that could support this.
   - `CRTPropagationStep`: if genProd n k is equidist mod r for squarefree n, then genProd n (k+1) = genProd n k · genSeq n k is also equidist. The induction step for CRT equidistribution of accumulators. Search for product-set equidistribution results.
   - Three new files: `EM/Ensemble/EM.lean` (114 lines), `EM/Ensemble/CRT.lean` (422 lines), `EM/Ensemble/PT.lean` (369 lines). 25 theorems, 10 new open Props. Key idea: average over squarefree starting points to get independence (bypasses Four-Way Blocker item 1 for single trajectories).

2. **PNT+ project monitoring**
   - Track [github.com/AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) for BV formalization or sieve infrastructure that could be imported.
   - As of Session 116 (March 2026): Gauss AI completed strong PNT formalization (~25K lines, ~1000 theorems, 3 weeks). IPAM explicit ANT network launched but "many portions disconnected." Has `BrunTitchmarsh.lean` (standalone classical). NO Chapter 7 / large sieve. IK Ch 7 in PNT+ unlikely before Q3 2026.

2. **Tao Explicit ANT Network monitoring** (NEW, Jan 2026)
   - Track [terrytao.wordpress.com](https://terrytao.wordpress.com/2026/01/15/the-integrated-explicit-analytic-number-theory-network/) for expansion beyond explicit PNT.
   - IPAM-hosted collaborative formalization project. Currently focused on explicit PNT estimate. If they tackle BV-type results, immediately relevant.

3. **Hilbert inequality formalization precedent**
   - Search for any proof-assistant formalization of the Montgomery-Vaughan Hilbert inequality or Oleszkiewicz (1993) elementary proof.
   - As of Session 130: unprecedented in Lean, Coq, and Isabelle. Session 130 decomposed the chain into 4 precise open Props (CscPartialFraction, HilbertCscBilinearBridge, CscBilinearImpliesGramOffDiag, HilbertInequality) with `hilbert_chain_als` PROVED. Mathlib has `cot_series_rep` (cotangent Mittag-Leffler) and `mul_le_sin` (Jordan's inequality) — key infrastructure for the first two open Props.

4. **Mathlib SelbergSieve evolution**
   - `Mathlib.NumberTheory.SelbergSieve` EXISTS but is a combinatorial upper-bound sieve, NOT the analytic large sieve.
   - Check if anyone is building ANALYTIC large sieve on top of this framework.

5. **SieveUpperBound RESOLVED** (Session 252: replaced by unconditionally proved WeakFMCD)
   - SieveUpperBound is NO LONGER open — eliminated by WeakFMCD (sqfreeCount ≥ X/4 + CRT counting).
   - Sole remaining open hypothesis for a.a. mixed MC: **PrimesEquidistributedInAP** (= Dirichlet's theorem on primes in AP).
   - Chain: PEAP alone ⇒ PSCD ⇒ a.a. mixed hitting (ALL bridges PROVED).
   - Sessions 253-256 built EM/Advanced/InterpolationMC.lean (positive-prob capture + block coverage + TreeSieveDecay bridge + orbit melting + TSD-Hitting(3)).
   - **TreeSieveDecay(q)**: ∃ P₀, ∀ P ≥ P₀, Squarefree P → **Coprime P q** → GoodAccumulator q P. Sieve-theoretic open hypothesis. (Session 256: original def was FALSE, fixed with coprimality.)
   - **TSD-Hitting(3) PROVED unconditionally** (Session 256, mod-3 parity dichotomy).
   - Full conditional chain: PEAP + TSD ⇒ MC (all bridges proved).

## Session count
Current session: 292

## COMPLETED scouting tasks (do not re-search)

- **Mathlib large sieve / Hilbert inequality inventory** (Session 87): NO Hilbert inequality or additive large sieve in Mathlib. `Mathlib.NumberTheory.SelbergSieve` exists but is combinatorial (upper-bound) sieve, not analytic large sieve. Our IKCh7 files (`EM/IK/Ch7Foundations.lean`, `EM/IK/Ch7AdditiveLS.lean`, `EM/IK/Ch7MultiplicativeLS.lean`, `EM/IK/Ch7SieveApplications.lean`, `EM/IK/Ch7Hilbert.lean`) and `EM/LargeSieve/Analytic.lean` have custom infra. §7.4 + §7.5a COMPLETE; §7.5b (ALS→MLS) open.
- **IK Chapter 7 alignment** (Session 87): No Mathlib formalizations of duality principle, Parseval/Plancherel for finite Fourier, or spacing lemmas on ℝ/ℤ. All proved in our codebase. §7.4 COMPLETE modulo `GramOffDiagBilinearBound`. §7.5 Parseval bridge PROVED.
- **Lean Together 2026** (Session 86): No talks on sieve methods or analytic NT. Van Doorn on Carleson (COMPLETE), Mrugala on class field theory, Kontorovich on pedagogy.
- **Tao Explicit ANT Network** (Session 87): Jan 2026 project, focused on explicit PNT, NOT sieves. Jan 19 blog post on Rogers' theorem on sieving (density in cyclic groups, low relevance to EM).
- **Coupled walks with minimality selection** (Session 87): No literature exists. Framework confirmed as reformulation of existing infrastructure (not new mathematics).
- **Alladi distribution for P⁻ in APs** (Session 91): Alladi 1977 gives exact uniformity μ_q*(b) = 1/(q-1). Alladi-Johnson 2024/2026 (arXiv:2410.18259) quantitative second-order duality. McNew-Pollack-Roy 2023 intermediate prime factors (α > 0) equidist mod q ≤ (log x)^{1-ε} — boundary α = 0 excluded. All population-level, SieveTransfer gap applies.
- **Product equidistribution / products of primes mod q** (Session 91): Matomaki-Teravainen 2024 (J. Reine, arXiv:2301.07679) — products of 3 primes cover all residue classes. Coverage ≠ equidistribution. Population-level. Dead End #4 spirit.
- **Open dynamical systems / escape rates** (Session 91): Demers-Young, Bahsoun et al. — all require stationarity/mixing. EM nonautonomous, deterministic. Dead Ends #86, #95.
- **Profinite walks equidistribution** (Session 91): All results require random steps. Reformulation of SieveTransfer. Dead End #101.
- **Full monitoring sweep** (Session 92): PNT+ still on IK Ch 1 (no BV/large sieve). Tao Explicit ANT still explicit PNT. Hilbert inequality still unprecedented in any proof assistant. No new Mathlib analytic NT. No papers breaking Four-Way Blocker. Zero actionable findings.
- **Departure Graph literature search** (Session 93): "Departure graph" terminology is NOVEL to this project. Sequenceability (Gordon 1961, Muyesser-Pokrovskiy 2025) concerns existence of good orderings, not analysis of fixed sequences — reconfirms Dead End #4. Rotor-router model (Friedrich-Sauerwald 2010) requires cyclic local rule — EM is non-autonomous. Deterministic walk coverage theorems don't exist for EM-type walks. Mertens' theorem NOT in Mathlib. PNT+ status unchanged (IK Ch 1-2). Booker-Simon (2026) on generalized EM (maxFac variant) — not relevant to minFac MC. Dirichlet's theorem fully in Mathlib.
- **March 2026 full scan** (Session 116): Dirichlet PNT in APs now FULLY in Mathlib4 (`Mathlib.NumberTheory.LSeries.PrimesInAP`). Zero MC impact (population-level). PNT+: Gauss AI completed strong PNT (~25K lines, 3 weeks). IPAM explicit ANT network still disconnected. No BV/large sieve. Pham-Sauermann new weak sequenceability bounds (arXiv:2602.19989, Feb 2026) — existence, wrong quantifier. Hilbert inequality still unprecedented in any proof assistant. Harper BDH (J. London Math. Soc. 2025) already catalogued (#108). No new EM papers. Four-Way Blocker UNCHANGED. Next scan: June 2026.
- **March 2026 full scan #2** (Session 129): ZERO ACTIONABLE FINDINGS across 10 search directions. PNT+ v4.28.0 (Feb 2026), still IK Ch 1-2 (no BV). Gauss AI Strong PNT: irrelevant scope (classical PNT, no sieve/BV/large sieve). Mathlib4 v4.29.0-rc3: no new ANT. Booker-Simon (arXiv:2601.21901): wrong sequence variant (maxFac cyclotomic). No new papers on deterministic walk equidistribution, non-multiplicative character sums, smallest prime factor distribution, or Hilbert inequality formalization. Four-Way Blocker UNCHANGED. **Next scan: June 2026.**
- **March 2026 full scan #3** (Session 151): Tao-Teräväinen Dec 2025 (arXiv:2512.01739) uses Pilatte correlation estimates — MEDIUM-HIGH but requires multiplicativity (genSeq non-multiplicative). Pham-Sauermann Feb 2026: LOW (existence). Pascadi x^(5/8): LOW (population). Gafni-Tao rough numbers: LOW (catalogued). Booker-Simon Jan 2026: ZERO (wrong variant). PNT+: no BV/sieve progress. Wiener-Ikehara: NOT formalized. Mertens: NOT formalized. Four-Way Blocker UNCHANGED. **Next scan: June 2026.**
- **Full monitoring sweep** (Session 94): PNT+ still on IK Ch 1-2 (no BV/large sieve). Tao Explicit ANT still explicit PNT. Hilbert inequality still unprecedented in any proof assistant. No new Mathlib analytic NT. Li (arXiv:2602.20917) on Harman sieve — population-level, SieveTransfer gap. Zero actionable findings. Next scout: March 2026.
- **Abel summation API audit + AbelSummationPNT correctness** (Session 149): Mathlib has complete Abel summation API (`sum_mul_eq_sub_sub_integral_mul`, `tendsto_sum_mul_atTop_nhds_one_sub_integral`, `summable_mul_of_bigO_atTop`). CRITICAL FINDING: AbelSummationPNT does NOT follow from RealWienerIkeharaTauberian via Abel summation. The integral ∫₁ˣ E(t)/t² dt where |E(t)| ≤ C·t/log(t) diverges as C·log(log x). AbelSummationPNT = Mertens' theorem, which requires Siegel-Walfisz error terms. **CORRECTED Session 312 — this sentence was WRONG.** Explicit two-sided Mertens I has been in the Isabelle/HOL AFP since 2018 (Eberl–Paulson, `Mertens_Theorems.thy`, `𝔐(n) − ln n ∈ (−1 − 9/π², ln 4]`), is in Lean in `PrimeNumberTheoremAnd/IEANTN/Mertens.lean` (`|∑_{p≤x} log p/p − log x| ≤ log 4 + 4`), and is the subject of the open mathlib4#41394. Only "not in Mathlib v4.33.0" is true. See `agents/state/findings_mertens_priorart.md`. **Never write "first/only formalization in any proof assistant" without checking the AFP, PrimeNumberTheoremAnd, Metamath set.mm, HOL Light `100/`, and open Mathlib PRs.**
- **Session 97 literature search**: Five topics searched. (1) Alladi (1977): population-level, SieveTransfer gap. (2) Open dynamical systems (Demers-Young 2006, Cipriano-Rams 2025): non-autonomous barrier, Dead Ends #86/#95. (3) Kochen-Stone (1964): MEDIUM relevance — structurally right framework (CME+Dec→Kochen-Stone→MC) but blocked by SieveTransfer. NOT in Mathlib. (4) Products mod q (Kowalski-Soundararajan 2021): Four-Way Blocker item 1. (5) BSZ criterion: wrong direction (Möbius disjointness ≠ CCSB). No result breaks Four-Way Blocker.

- **FF algebraic-geometric literature survey** (Session 292): Seven directions searched: Mason-Stothers landscape, primitive divisors (Ingram-Silverman, Gratton-Nguyen-Tucker, Hindes), factorization of iterated polynomials (GOS, Reis), arboreal Galois (Odoni, Palimar), Drinfeld modules (Ghioca), FF-EM in literature (ZERO papers). Verdict: NO existing algebraic tool gives orbit-pointwise leverage on FF-EM. Mason-Stothers gives trivial per-step bound (deg(rad(P_n+1)) ≥ 1). All orbit-specific tools (primitive divisors, arboreal Galois) require FIXED dynamical systems; FF-EM is non-autonomous. Mason-Stothers IS in Mathlib (`Polynomial.abc` in `Mathlib.NumberTheory.FLT.MasonStothers`). Written to `scoping/ff_literature_report.md` (280 lines). **Do NOT re-search**: Mason-Stothers for FF-EM, primitive divisor applicability, arboreal Galois for non-autonomous systems, Drinfeld module orbit leverage.

## COMPLETED scouting tasks (Session 123)

- **Kowalski-Soundararajan (2021) CRT deep analysis** (Session 123): full analysis summarized in this entry (the standalone `docs/` write-up no longer exists). Applicability: 4/10 (structural analogue only). KS assume CRT structure as INPUT (sets constructed by local specs via CRT); EM must PROVE CRT structure emerges from deterministic dynamics. No existing result closes SCRTI. Searched: KS (2021), Pollack-Singha Roy (2024, polynomially-defined functions — wrong class), Nair-Tenenbaum (1998, interval sums — wrong structure), Fouvry-Iwaniec (friable integers ≠ minFac), Kowalski-Forey-Fresán (2021, algebraic varieties — wrong setting). **Conditional CRT equidistribution is unprecedented** — zero papers study equidistribution mod q given constraint mod r for factorization-based sequences. SCRTI requires NEW mathematics. Mathlib4 has basic CRT but NO quantitative equidistribution. Do NOT re-search KS or any of the assessed alternatives.
- **Factor confinement / sieve for structured sequences** (Session 246): Three-topic search for FactorEscapeHypothesis. (1) **Odoni (1985)**: Sylvester sequence W_{n+1}=1+W_1...W_n has DENSITY-ZERO prime divisors among all primes. Arboreal Galois framework — applies to polynomial iteration, NOT multiplicative accumulation. KEY NEGATIVE SIGNAL for EM. (2) **LSD formula** (Drappeau arXiv:2511.15928, Nov 2025): #{N≤X : all p|N have p mod q ∈ S} ~ C·X/(log X)^{1-|S|/φ(q)}. State-of-art for "Dirichlet smooth numbers." For EM: confinement prob ~2^{-n/φ(q)} per step. BC heuristic strongly supports FEH but SieveTransfer gap applies. (3) **Factor accessibility** is a NOVEL question — zero prior work on "given T:Z→Z with factor selection, when is R_∞=(Z/qZ)×?" No framework exists. Other: Jones (2006) density-zero for polynomial orbit divisors, Luca-Steuding (2016) ω lower bounds for Mersenne numbers (almost all n only), Pollack-Treviño (2014) second EM misses ∞ primes (wrong variant), Booker-Simon (2026) generalized EM cyclotomic (wrong variant). **Assessment**: literature provides strong heuristic support (LSD+BC) but zero rigorous tools for orbit-specific FEH. Do NOT re-search these topics.

## COMPLETED scouting tasks (Session 114)

- **DSL-relevant literature sweep** (Session 114): Seven search directions. Zero results break Four-Way Blocker. (1) Kowalski orbit short sums (Fouvry-Kowalski-Michel 2017, Forey-Fresan-Kowalski 2021): require algebraic-geometric structure, Four-Way Blocker #3. (2) Bourgain sum-product walks (Bourgain-Gamburd 2008, BGS 2010): require random walks, Dead End #95. (3) Position-blind walks: NO literature exists (confirmed novel). (4) Merai-Shparlinski (2020): MEDIUM structural analogue (polynomial orbits in F_p* subgroups), but requires autonomous dynamics + algebraic geometry. (5) Mathlib: no new analytic NT. (6) PNT+: still IK Ch 1-2. (7) Tao Explicit ANT: still explicit PNT. (8) Furstenberg-style: Dead Ends #86/#95. Next scout: April 2026.

## COMPLETED scouting tasks (Session 104)

- **PBI / deterministic walk equidistribution literature** (Session 104): Searched "position-blind increments", "exogenous increments", "state-independent deterministic walks", "CRT independence walk equidistribution", Diaconis-Shahshahani deterministic analogue. Zero papers study deterministic walks with PBI-like properties on finite groups. Closest results (rotor-router, Kowalski-Soundararajan CRT equidist) require Euler structure or probabilistic independence. PBI assessed as = Dead End #98 (CRT decorrelation). Four-Way Blocker remains unbroken.

## Deprioritized / do-not-repeat searches

- Conditional distribution of P⁻(n) given n mod q (confirmed open)
- Harper BDH for EM (Dead End #108)
- Non-multiplicative Halász extensions (Dead End #109)
- Transition matrix convergence as a new technique (Dead End #110)
- Approximate CRT product sets for EM (exhausted Session 80)
- Rough number concentration / coprimality ⇒ minFac independence (Dead End #111, Session 82)
- Joint minFac distribution given coprimality constraints (confirmed: no literature exists)
- Gorokhovsky (2024) time-inhomogeneous random walks (requires probability distributions — Four-Way Blocker items 1 & 4)
- Order-3 Möbius Death Function (Dead End #112, Session 83)
- Coupled walks with minimality selection (Session 87: no literature exists, framework is a reformulation)
- Deterministic walks on finite groups equidistribution (Session 87: all results require random steps)
- Sequenceability / partial product coverage of groups (Session 89: Gordon 1961, Pham-Sauermann 2026 — wrong quantifier, Dead End #4)
- Critical numbers / Cayley diameter (Session 89: arbitrary subsets not consecutive, Dead End #4)
- Davenport constants / EGZ (Session 89: zero-sum theory, wrong structure, Dead End #4)
- Rotor-router / deterministic coverage on groups (Session 89: no coverage theorem for non-Euler graphs)
- Cycle Product Equidistribution (Dead End #113, Session 91): telescope absorbs product structure, reduces to CCSB
- Missing Prime Accumulation / Borel-Cantelli for EM (Dead End #114, Session 97): pairwise quasi-independence = CME for single fiber
- Kochen-Stone / quantitative Borel-Cantelli (Session 97): structurally relevant but blocked by SieveTransfer
- BSZ criterion / Sarnak-type orthogonality (Session 97): wrong direction — Möbius disjointness ≠ CCSB
- Alladi distribution as route to CME/CCSB (Session 91: population-level, SieveTransfer gap)
- Open dynamical systems / escape rates for EM walk (Session 91: requires stationarity, Dead Ends #86/#95)
- Profinite walk orbit closure (Session 91: requires random steps, Dead End #101)
- Position-Blind Increments (PBI) / Weak Ergodicity for deterministic walks (Session 104): PBI = crt_multiplier_invariance = Dead End #98. Counterexample on (Z/5Z)* disproves PBI+SE → equidistribution. No literature exists on PBI for deterministic walks on finite groups.
- Population Equidistribution of minFac in shifted squarefree population (proved: `prod_squarefree`, `euclid_in_shifted_squarefree` in EM/Population/WeakErgodicity.lean; PE+PT framework formalized but PE and PT remain open hypotheses)
- Sieve-theoretic transfer for DSL (Dead End #116, Session 114): Selberg sieve axiom ω(r)~1/r IS EMDirichlet. Circular.
- Kowalski orbit short sums (Session 114): require algebraic-geometric structure (l-adic sheaves), Four-Way Blocker #3
- Bourgain-Gamburd expansion machine (Session 114): require random walks, Dead End #95
- Furstenberg measure rigidity for non-autonomous walks (Session 114): requires stationarity/commutativity, Dead Ends #86/#95
- Merai-Shparlinski polynomial orbits (Session 114): structural analogue only, requires autonomous dynamics + algebraic geometry
- AbelSummationPNT via Abel summation from PNT (Session 149): MATHEMATICALLY INCORRECT — gives O(log log x) not O(1). Mertens' theorem requires Siegel-Walfisz error terms. No formalization of Mertens exists anywhere.
- FF-EM monodromy / Deligne equidistribution (Dead End #129, Session 168): No prior work on FF-EM monodromy. Three fatal obstructions: (1) FFLM likely false — cyclotomic counterexample Φ₅(t) over F_2 has Gal=Z/4Z; (2) Deligne is a family/population statement; (3) cycle type ≠ residue class. Do NOT search for monodromy-based approaches to FF-EM.

## Known references (Sessions 82-91 findings)

- **Pollack-Roy (2023)**: "On intermediate prime factors of integers, I" — marginal equidist of P⁻(n)/P⁺(n) only; nothing for joint distribution needed by EM.
- **Gafni-Tao (2025, arXiv:2508.06463)**: Rough numbers between consecutive primes. Sieve techniques require multiplicative structure.
- **Booker-Simon (2026, arXiv:2601.21901)**: Generalized EM sequences miss infinitely many primes. Galois-theoretic approach applies to maxFac not minFac.
- **Gorokhovsky (2024, arXiv:2405.11435)**: Time-inhomogeneous random walks — requires probability distributions, Four-Way Blocker items 1 & 4.
- **Pascadi (2025, arXiv:2505.00653)**: Exponents of distribution to x^{5/8}. Advanced large sieve for exceptional Maass forms. Population-level result, SieveTransfer gap still applies.
- **Zheng (2025, arXiv:2512.22798)**: Primes in simultaneous APs. Different problem from EM walk.
- **Oleszkiewicz (1993)**: Elementary proof of Hilbert inequality — American Mathematical Monthly. ~200-300 lines to formalize.
- **PNT+ project** (Kontorovich et al.): Monitor for BV and sieve formalization.
- **Tao Explicit ANT Network** (Jan 2026): New IPAM collaborative project. Currently explicit PNT only.
- **Tao: Rogers' theorem on sieving** (Jan 19, 2026 blog post): Density of sieved sets in cyclic groups is maximized when coset shifts are zero. Interesting but LOW relevance to EM walk problem.
- **Drury (arXiv:2402.11884)**: Distribution of LARGE prime factors of well-distributed sequences. Studies P⁺ not P⁻. Requires AP equidistribution. Not applicable to EM.
- **Pham-Sauermann (arXiv:2602.15797, Feb 2026)**: Graham's rearrangement conjecture for large primes. EXISTENCE of good ordering, wrong quantifier for EM (Dead End #4).
- **Muyesser-Pokrovskiy (Inventiones 2025)**: All sufficiently large groups are sequenceable. Wrong quantifier (Dead End #4).
- **Gao-Hamidoune-Llado-Serra (Combinatorica 2003)**: Critical number c(G) for subset sum coverage. Arbitrary subsets, not consecutive (Dead End #4).
- **Alladi-Johnson (2024/2026, arXiv:2410.18259)**: Second-order Alladi duality, quantitative version. Siegel-Walfisz rate. Population-level.
- **Sengupta (2024, arXiv:2410.22226)**: Algebraic Alladi-Johnson via Chebotarev. Requires Dead End #9.
- **Wang (2025, arXiv:2504.16002)**: Logarithmic Alladi formula, elementary proof. Population-level.
- **McNew-Pollack-Roy (2023, Monatshefte)**: Intermediate prime factors equidist mod q ≤ (log x)^{1-ε} for α > 0. Boundary α = 0 (smallest) excluded.
- **Matomaki-Teravainen (2024, J. Reine, arXiv:2301.07679)**: Products of 3 primes cover all residue classes mod q. Coverage ≠ equidistribution. Multiplicative dense model theorem.
- **Tao-Teravainen (Dec 2025, arXiv:2512.01739)**: Quantitative correlations of ω(n) for consecutive integers. Studies ω(n) not P⁻(n). Multiplicative framework. Session 146 confirmed: their "pairwise implies higher" decoupling via Gowers norms requires multiplicativity — no non-multiplicative analog exists. Cannot help with FourPointPCV or higher-moment bounds for minFac.
- **Pollack-Singha Roy (2024, arXiv:2401.00358, arXiv:2402.16266)**: Joint distribution of multiplicative functions in residue classes. Multiplicative functions only.
- **Li (2026, arXiv:2602.20917)**: Harman sieve improvements. Population-level sieve technique. SieveTransfer gap applies. LOW relevance.
- **Kochen-Stone (1964)**: Quantitative Borel-Cantelli: P(A_n i.o.) ≥ lim sup S²/(S+2T). Right framework for CME+Dec→MC but hypotheses require SieveTransfer. NOT in Mathlib.
- **Kowalski-Soundararajan (2021, arXiv:2003.12965)**: CRT subsets equidistribute on average. Requires independence (Four-Way Blocker item 1).
- **Bourgain-Sarnak-Ziegler (2013)**: Bilinear decorrelation → Möbius disjointness. Wrong direction: Möbius disjointness ≠ CCSB.
- **Demers-Young (2006)**: Open dynamical systems escape rates. Requires stationarity/Markov. Not applicable to EM.
- **Cipriano-Rams (2025, arXiv:2505.02336)**: Moving holes in open dynamical systems. Same barriers as Demers-Young.

## Output format

For each finding, report:
- citation / link
- 1–2 line summary
- relevance to CME/CCSB/SieveTransfer, or to the IKCh7 files
- if Mathlib: lemma names + import paths
