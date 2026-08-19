# Dynamical Systems Technique Catalog

**Domain**: Dynamical systems, ergodic theory, non-autonomous walks on finite groups
**Attack agent**: `attack_dynamicalsystem`
**Last updated**: Session 308 (new family **T7: Population Box Process** — the first
technique family in this catalog where classical probabilistic dynamics legitimately applies)

---

## How to use this catalog

1. **Before proposing anything**: scan the STATUS column. If DEAD, don't revisit.
2. **Check the fundamental dynamical obstacle**: classical ergodic theory requires INVARIANT MEASURES. The EM walk is non-autonomous (different map at each step), deterministic (Dirac mass steps), and non-stationary. Standard tools (mixing time, spectral gap, Birkhoff averages) assume randomness or stationarity.
3. **Check the Four-Way Blocker**: does the technique require independence (1), multiplicativity (2), algebraic-geometric structure (3), or ergodic stationarity (4)? EM has none.
4. **The three viable approaches** are PT, EMDImpliesCME, and genuinely new non-autonomous walk theory. Focus effort here.
5. **PBI (Position-Blind Increments) is proved but insufficient**: counterexample shows PBI+SE does not imply equidistribution.

---

## Technique Families

### T1: Classical Ergodic Theory (ALL DEAD)

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T1.1 | Birkhoff ergodic theorem | Measure-preserving transformation T, integrable f | Time average = space average a.e. | DEAD | #74 | EM walk is non-autonomous — different multiplier at each step. Mathlib `BirkhoffSum` assumes orbit under SINGLE map |
| T1.2 | Mixing time theory | Markov chain on group, transition matrix | Convergence to stationary in O(log|G|) steps | DEAD | #110 | EM walk is NOT Markov (multiplier depends on entire history via P(n)). Transition matrix convergence IS CME — reformulation, not technique |
| T1.3 | Spectral gap methods | Reversible Markov chain or expander | Geometric convergence to equilibrium | DEAD | #95 | Spectral gap applies to DISTRIBUTIONS (random sampling). EM walk is a single deterministic PATH. Frequency ≠ probability |
| T1.4 | Exponential mixing / decay of correlations | Hyperbolic dynamics, SRB measures | Correlation decay at exponential rate | DEAD | #86 | EM has no hyperbolicity, no smooth structure, no invariant measure |
| T1.5 | Diaconis-Shahshahani theory | Random walk on group, i.i.d. conjugacy-invariant steps | Convergence after O(log|G|) steps | DEAD | #86, #95 | Requires RANDOM walk with i.i.d. steps. EM is deterministic with different multiplier at each step |
| T1.6 | Nonstationary ergodic theorems | Time-inhomogeneous random walk | Convergence under mixing conditions | DEAD | #86 | Monakov/Ito-Kawada require strictly aperiodic PROBABILITY measures AND independent steps. EM has Dirac mass steps (deterministic) and dependent steps |
| T1.7 | Furstenberg correspondence | Combinatorial structure ↔ dynamical system | Recurrence from dynamical properties | DEAD | early | EM too structured. Correspondence gives no information beyond group theory |

### T2: Position-Blind Increment (PBI) Framework

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T2.1 | CRT multiplier invariance | minFac and modular arithmetic | minFac(P(n)+1) mod q does not depend on P(n) mod q | PROVED | — | `crt_multiplier_invariance`. The STRUCTURAL decorrelation theorem. Per-step, not aggregate |
| T2.2 | PBI + SE → equidistribution? | Position-blind increments + full generation | Equidist of walk? | DEAD | #98 | Counterexample on (Z/5Z)*: multipliers alternating {2,3} have PBI+SE but walk trapped in {1,3}, avoiding -1=4. PBI + distinctness also fails |
| T2.3 | PBI + growth + generation → VCB? | PBI + super-exponential growth + generation | Vanishing conditional bias? | DEAD | #107 | Explicit counterexample on (Z/3Z)*: all three axioms satisfied but VCB fails. Per-step CRT pointwise; VCB needs aggregate control |
| T2.4 | PBI → EMDImpliesCME | PBI as ingredient for unconditional→conditional | Equidist conditional on position? | OPEN (2/10) | #98, #107, #115 | PBI is per-step, EMDImpliesCME needs aggregate. CRT freshness idea (new prime factors refreshing CRT decomposition) maps to #115 (CRT dimensional explosion) and #118 (growth-based decorrelation). Refreshing CONSTRAINS rather than frees CRT coordinates. Marginal/Joint Barrier applies fully. Any quantitative non-concentration of visits IS visit equidistribution (circular). Session 155 assessment: OPEN but no concrete proof path |

### T3: Population Transfer Framework

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T3.1 | Population Equidistribution (PE) | Selberg sieve + Dirichlet | minFac equidist mod q in shifted squarefree population | OPEN (provable from standard ANT) | — | `EM/FunctionField/PopulationEquidist.lean` stated. The population-level result. Provable by standard sieve methods but requires Dirichlet PNT (MATHLIB BLOCKED) |
| T3.2 | Population Transfer (PT) | PE + trajectory sampling property | PE → EMDirichlet | OPEN | — | `PopulationTransfer` stated. The cleanest dynamical question: does P(0)+1, P(1)+1, ... sample shifted squarefree without bias mod q? |
| T3.3 | PE + PT + EMDImpliesCME → MC | Full chain | Mullin's Conjecture | PROVED | — | `pe_transfer_cme_implies_mc`. The chain works; the open links are PT and EMDImpliesCME |
| T3.4 | Squarefree accumulator | Orbit structure | P(n) is squarefree; P(n)+1 ∈ ShiftedSquarefree | PROVED | — | `prod_squarefree`, `euclid_in_shifted_squarefree`. Structural property that makes PT well-posed |
| T3.5 | Population → individual transfer (general) | Density argument for population, transfer to orbit | Equidist for specific orbit from "most orbits" | DEAD (general) | #101 | Avoidance density → 0 is population-level, cannot constrain specific deterministic orbit. PT for EM specifically remains OPEN |

### T4: Non-Autonomous Walk Theory

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T4.1 | Time-varying Cayley expansion | Distinct generators at each step | Walk coverage after enough steps | DEAD | #95 | Requires i.i.d. steps for spectral gap. Deterministic expansion at each step ≠ random walk expansion |
| T4.2 | Quasirandom walk on abelian groups | Walk on Z/nZ with "random-like" multipliers | Equidistribution from quasirandomness | DEAD | #82 | Abelian is worst case for mixing. Quasirandomness requires specific spectral properties that EM multipliers don't satisfy |
| T4.3 | Non-autonomous multiplicative walk theory | w(n+1) = w(n)·m(n), distinct m(n), PBI, SE, growth | Equidist of {w(n)}? | OPEN (2/10) | #74, #86, #95, #98, #107, #110 | **No such theory exists** (confirmed Sessions 104, 155). Counterexample lower bound (#98, #107) shows axioms (A)-(D) insufficient. Session 157: +1 shift / cofactor walk FULLY ASSESSED — cofactor walk is a coordinate change (not new dynamics), cofactor recurrence is harder (second-order, mixes additive+multiplicative), cofactor mod q is position-DEPENDENT (unlike PBI multiplier). All +1 shift leverage is arithmetic/sieve-theoretic, not dynamical. Building new theory would be genuine new math but faces Four-Way Blocker legs 1+4 |
| T4.4 | Open dynamical systems / escape rates | Escape from target set, invariant measure | Escape rate = Lyapunov exponent | DEAD | — | Demers-Young (2006), Cipriano-Rams (2025): require stationarity/Markov/invariant measure |
| T4.5 | Deterministic walk coverage results | Walk on finite group, generation property | All elements hit after f(|G|) steps | OPEN (1/10) | — | Pham-Sauermann Feb 2026 proved Graham's conjecture for large primes via probabilistic anticoncentration+Fourier. Proof inherently existential (random ordering + local adjustments). No info about specific orderings. Additive-to-multiplicative mismatch for EM. Alspach conjecture (general abelian) planned as future work but no characterization of good orderings expected. Session 155: confirmed fundamental mismatch (∃ vs ∀, additive vs multiplicative) |

### T5: Dynamical Structural Properties

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T5.1 | Super-exponential growth | Orbit growth rate | P(n) grows super-exponentially: log P(n) ≥ c·2^n | PROVED | — | `em_super_exponential_growth` via injectivity + log analysis. Structural property, used in SDDS framework |
| T5.2 | Coprimality cascade | gcd(P(n)+1, P(m)+1) for n≠m | Consecutive orbit terms coprime | PROVED | — | `SDDS.coprimeCascade` for ALL SDDS. Structural property, no equidist content |
| T5.3 | Walk product telescope | χ(w(n)) = χ(w(0))·∏χ(m(k)) | Walk char = running product of mult chars | PROVED | #103 | The complete algebraic content. Only two decompositions: fiber (CME) or lag (HOD). This is ALGEBRAIC, not dynamical |
| T5.4 | Coprimality refreshing | P(n+1)+1 coprime to P(n) | Death rate cycle structure | PROVED | #113 | `coprimality_refreshing_int/nat`, `no_safe_cycle`. Descriptive only — constrains death curve geometry, not walk dynamics |
| T5.5 | Infinite recurrence | Walk in finite group | Some position visited infinitely often, with infinite departures | PROVED | — | `exists_infinite_fiber_of_finite`, `infinite_departures_at_recurrent`. Pigeonhole. No dynamical content beyond finiteness |
| T5.6 | Cofactor walk / +1 shift identity | w(n)+1 = m(n)·cofZ(n) in ZMod q | Decomposition of shifted walk; death ↔ cofZ=0 | PROVED (identity), DEAD (for dynamical leverage) | #103, #118 | `shifted_walk_eq_mult_mul_cof`, `walkZ_eq_neg_one_iff_cofZ_zero`, `char_shifted_walk_eq_char_mult_mul_char_cof`. Cofactor walk c(n) is a bijective coordinate change of (w(n), m(n)). Recurrence is second-order: c(n+1) = (m(n)²·c(n) - m(n) + 1)/m(n+1). Mixes additive + multiplicative, HARDER. cofZ mod q is position-dependent (encodes w(n)), so LESS decorrelated than multiplier. Session 157: all angles dead — no leverage for DH, no independent dynamics, no CRT advantage beyond PBI |

### T6: Profinite & Product Group Methods

| ID | Technique | Preconditions | What it gives | EM status | Dead ends | Notes |
|----|-----------|---------------|---------------|-----------|-----------|-------|
| T6.1 | Profinite orbit closure | Walk in ∏(Z/qZ)× | Orbit closure is a group ⟹ equidist | DEAD | #101 | Orbit closure arguments require random steps. Deterministic walk in product group doesn't simplify |
| T6.2 | Accumulating CRT independence | As P(n) gains prime factors, CRT dimension grows | Correlations "diluted" in high dimensions | DEAD | #115 | CRT representation of a single integer is degenerate — all coordinates locked. Walk mod q has dimension 1 regardless. Illusory dimensional explosion |
| T6.3 | Kowalski-Soundararajan equidist | CRT subsets equidistribute on average | Average equidist of orbit mod q | DEAD | — | Requires independence (confirmed by K-S 2021). Population-level |

### T7: Population Box Process (type-measure martingale methods) — **NEW, Session 308, LIVE**

**This is the first technique family in this catalog for which classical probabilistic
dynamics is legitimately applicable.** The object is NOT the deterministic orbit of `2`; it is
the *box process* of the seed-average law (`tmp/strategy_seed_average_2026-08-18.md`):

- **State**: `(Bag_k, (V_k(r))_{r ≤ Y})` where `V_k(r)` = residues `c_j mod r` at `r`-exposed
  steps `j < k`, `Bag_k` = primes dividing `P_k`, `B_k(r)` = units `∖ (−V_k(r))^{-1}`,
  `|B_k(r)| = r−1−|V_k(r)|`.
- **Driving measure**: the *type measure* — natural densities of unions of residue classes mod
  `M_Y = ∏_{r≤Y} r` with `Y` an **absolute constant**. This is an honest finite probability
  space, so martingales / compensators / Borel–Cantelli / Freedman are legitimate.
- **Transition law (exact, proved-in-principle)**: `P(p_{k+1}=p ∣ τ) = ρ_p ∏_{r<p}(1−ρ_r)`,
  `ρ_r = [c_k new mod r]/|B_k(r)|`, `ρ_r = 0` on `Bag` and at old positions.
  `S_k(y) = P(p_{k+1} > y ∣ τ) = ∏_{r≤y}(1−ρ_r)`.

| ID | Technique | Preconditions | What it gives | EM status | Notes |
|----|-----------|---------------|---------------|-----------|-------|
| T7.1 | Type/CRT product density (Lemma B + CRT) | multipliers `≤ y`, `M_y` squarefree | exact product formula for `dens(τ)` | CONFIRMED (Session 308 WP0(a)) | local factor at `r = p_{i+1}` is exactly one class; consistency = "`c_i` new mod `p_{i+1}`"; no hidden dependence since `c_0..c_n` are functions of `τ` alone |
| T7.2 | Revisit-freeness (Lemma A) | none | `r ∤ P_k+1` at old positions; `\|V_∞(r)\| ≤ r−2` for uncaptured `r` | PROVED | `SeedTypes.not_dvd_succ_of_revisit`, `card_visitedSet_le_sub_two` |
| T7.3 | `q`-free coupling (Lemma C) | `m' ≡ m mod M_y/q`, `q ∤ m'` | capture ⟺ `m' mod q ∈ −V_n(q)^{-1}`; **capture is a COVERAGE statement** | CONFIRMED (WP0(b)) | shielding handled by using `q`-**exposed** steps; `q`-power case ⊆ tail |
| T7.4 | Large-multiplier randomisation (Lemma D) | type-determined threshold `y_k = C k log₂ c_k`; light-bag types | `P(p_{k+1} ≡ a ∣ τ, large) ≥ κ_q > 0` | OPEN, 7/10 | needs ONLY `weightedPNTinAP_asymp_proved` + Chebyshev `θ ≤ (log 4)x`. **Not** Mertens `O(1)`. `A = 2` suffices |
| T7.5 | **Roughness charge budget** | none (deterministic) | `Σ_{r<2n} H_{r−1} ≤ θ(2n)+π(2n) = O(n)` against `n` steps ⟹ `S_k(y_k) ≥ c₁` on `≥ n/2` steps, pathwise | **VERIFIED Session 309 (CONFIRMED-WITH-CORRECTIONS); core IN LEAN** (`EM/Population/LargeStepRoughness.lean`: F1a–F1e `charge_sum_le_harmonic`, F1f–F1h `chargeBudget_le`, F2, F3 brink, B1–B3, B7, B8, M1, M2 — Session 309 slices 1–2) | The engine of (LS). Six corrections C1–C6 (see `agents/state/findings_ls_verification.md`): exclude `r = q` everywhere; near band `r ≤ 2k+1`; Y tied to n (`log Y ≍ n²`, cutoff `k ≥ n/log n`); tail estimate is new work; tree supermartingale replaces block chaining; stop at σ. Constants: `T = 6`, `c₁ := e^{−36}` (exp-route B7) |
| T7.6 | Brink dichotomy | `\|B_k(r)\| = 1` and position new | `ρ_r = 1` ⟹ `p_{k+1} ≤ r` (the multiplier is forced small) | PROVED (argument) | describes `{S_k = 0}` exactly; also gives `ρ_r ≤ 1/2` at all steps with a huge multiplier |
| T7.7 | Exponential supermartingale on the finite type tree | compensator `Σ S_k ≥ v` surely | `P(N_n < K) ≤ exp(λK − (1−e^{−λ})v)`; at `λ=1, K=(c₁/4)n`: rate `exp(−0.066·c₁·n)` | LEGITIMATE (Session 309) | first time a martingale tool applies. **WARNING (C5): the "elementary block substitute" is INVALID** — the charge budget is global (no per-block version) and goodness is not block-past-measurable; a middle block can be all high-exponent steps. Use the backward-induction supermartingale `E[e^{−λN+θV}] ≤ 1` (per-node factor `e^{θS}(1−θS) ≤ 1`), stopped at σ on `{σ > k} ∈ F_k` |
| T7.8 | Theorem C chaining | Lemma D + `q`-free `V`-growth | geometric decay of the uncaptured density | OPEN, 6/10 | must be written by stopping times (`largeness` is `F_{k+1}`-measurable); `K₀ = π(q−1) + k₀ + k₁` |

**Dead / corrected within T7** (do not re-introduce):
- Seed-magnitude threshold `y_k = C k log₂ P_k` (**SM**): non-measurable for the type
  σ-algebra; and the large-step event then has probability `≍ 1/log log X`, making Theorem C
  vacuous and **(LS) false**. Use `y_k = C k log₂ c_k`.
- The §1.7 heuristic "only primes `r ≳ k/log k` are still active" (**CI**): assumes the small
  primes are captured, i.e. the population form of the conclusion. Use T7.5 instead.
- Worst-case `ω(m) ≤ log₂ m` bag bound (**AG**): unbounded on a type; replace by the first
  moment `E[Σ_{r∣m, r≥z}1/r] ≤ 2/(z log z)` and a density-`2/log C` exclusion.
- "each `r < q` is new at most `r−1` times" (the original `K₀` justification): **false** —
  `V(r)` grows only at `r`-exposed steps. Use distinctness of multipliers (`π(q−1)`).

**Scope**: T7 caps at **a.a. GenMC(q) for each fixed `q`**. `κ_q ≍ c(A)/φ(q) → 0` and
`K₀(q) → ∞`, so there is no `q`-uniformity, and natural density is not countably additive; the
simultaneous statement is open. T7 is **not** a route to MC (#90 stands).

---

## Decomposition Strategies

### D1: PE + PT + EMDImpliesCME decomposition
The primary dynamical decomposition. Separates the problem into:
- PE (sieve-theoretic, provable) — the population has the right distribution
- PT (dynamical) — the orbit samples without bias
- EMDImpliesCME (statistical) — unconditional → conditional
**Status**: the live strategy. PE likely provable. PT and EMDImpliesCME are the open gaps.

### D2: Structural → Statistical bridge
Proved structural properties (PBI, SE, growth, coprimality) → statistical conclusion (equidist). **Status**: DEAD as stated (#107 counterexample). No known bridge from pointwise structural properties to aggregate statistical properties for deterministic sequences.

### D3: Excursion decomposition
Group walk by return excursions. Each excursion contributes bounded character sum. Total walk sum = ∑ excursion sums. **Status**: formalized (`EM/Transfer/Excursion.lean`). Blocked by inter-excursion independence (= CME).

### D4: Scale decomposition
Analyze walk at different scales: short-range (few steps), medium-range (blocks), long-range (Cesàro averages). **Status**: short-range gives PBI; medium-range gives nothing new; long-range IS equidistribution. No scale separation helps.

---

## Generalization Strategies

### G1: Weaken the dynamical target
- From CME to EMDirichlet (= Dec): weaker, but EMDirichlet + EMDImpliesCME → MC. **The live strategy**
- From EMDirichlet to PE + PT: further decomposition. **The live decomposition**
- From "all q" to "density 1 of q": sufficient via SHH + cofinal hitting. **ALREADY EXPLOITED**

### G2: Strengthen structural assumptions
- Assume not just PBI but explicit rate of decorrelation: **UNTRIED** but no natural rate arises from CRT
- Assume not just SE but "rapid generation" (generators span G within O(1) steps): **UNTRIED** but EM has sieve gap, so rapid generation only after gap
- Assume both PBI and distinctness of multipliers: still DEAD (#98 — distinctness doesn't help)

### G3: Grothendieck move — change the dynamical framework
- Instead of (Z/qZ)×, work in the p-adic integers Z_p → **UNTRIED** but EM walk is in a finite group, profinite structure doesn't add information
- Instead of single walk, study ensemble of walks with different initial conditions → **PARTIALLY EXPLORED** (PE is exactly this at the population level). Transfer back to single orbit is PT
- Instead of multiplicative walk, study the additive walk a(n) = ∑ m(k) → **UNTRIED** but EM walk is multiplicative; additive version loses the group structure
- Model as a RANDOM walk where m(n) is chosen from ShiftedSquarefree with the correct distribution → **PARTIALLY EXPLORED** (this is the PE model; the gap is transferring from random to deterministic)

### G4: Build new theory
The most ambitious strategy: develop a theory of equidistribution for non-autonomous multiplicative walks on finite abelian groups satisfying:
- PBI (position-blind increments)
- Full generation (multipliers generate the group)
- Super-exponential growth (in the lifted space)
- Coprimality cascade (consecutive orbit terms coprime)
- Distinctness (multipliers are distinct primes past sieve gap)

No such theory exists. Creating one would be a genuine mathematical contribution, potentially publishable independently. The key question: which ADDITIONAL property (beyond PBI+SE+growth+coprimality+distinctness) is needed to force equidistribution? The counterexample in #107 shows these five are NOT sufficient.

---

## The Frontier (what might actually work)

### F0: The box process / seed-average law (T7) — **now the top item (Session 308)**
Target: **a.a. GenMC(q)** — "for a.a. squarefree seeds `m`, the greedy orbit of `m` captures
`q`" — the cap the paper flags as unattained. Route: T7.1–T7.4 (exact conditional selection
law + Lemma D) ⟹ Theorem C, plus T7.5–T7.7 ⟹ (LS). Uses **no character sums, no
equidistribution hypothesis, no orbit claim**, so it is immune to #90/#117/#136–#139/#157/#160.
Analytic input: `weightedPNTinAP_asymp_proved` (in repo) and Chebyshev `θ ≤ (log 4)x` (Mathlib).
Scope cap: per `q` (see T7 "Scope"). Feasibility 6/10 (was 2/10 before the charge budget).

### F1: Population Transfer (PT) — most promising
**Why**: cleanest separation between sieve-theoretic (PE) and dynamical (PT) content. PT asks only: does the EM trajectory sample ShiftedSquarefree without mod-q bias?

**Structural basis**: CRT independence (PBI) says P(n) mod q doesn't influence WHICH shifted squarefree number P(n)+1 is, beyond the q-coordinate.

**What's needed**: a way to show that the EM trajectory's sampling of ShiftedSquarefree is "typical" — that the trajectory doesn't systematically avoid shifted squarefree numbers with particular minFac residues. This requires controlling the joint distribution of (P(n) mod q, minFac(P(n)+1) mod q), which IS the core open question.

**Possible approaches**:
- Effective equidistribution of P(n)+1 in residue classes of ShiftedSquarefree (requires sieve estimates for specific orbit)
- Mixing argument for the map P ↦ P·minFac(P+1) restricted to squarefree integers (requires invariant measure — circular)
- Ergodic decomposition of ShiftedSquarefree into "good" and "bad" subsets, show bad has density 0 (requires density analysis of orbit intersection)

### F2: EMDImpliesCME — second most promising
**Why**: if EMDirichlet holds (multipliers equidistributed mod q unconditionally), does it follow that they're equidistributed CONDITIONAL on walk position?

**Structural basis**: PBI says the minFac mechanism is position-blind. This is a STRUCTURAL form of conditional independence. The question is whether structural position-blindness implies STATISTICAL conditional independence for a deterministic sequence.

**What's needed**: an argument that PBI prevents the trajectory from creating spurious correlations between walk position and multiplier residue. The gap: PBI holds at each step, but the TRAJECTORY is a single realization that could concentrate in specific (position, multiplier) pairs.

### F3: Non-autonomous walk theory (high-risk, high-reward)
No existing theory covers the EM setting. Building one requires identifying the minimal axioms that force equidistribution for deterministic, non-autonomous, multiplicative walks.

**Known lower bound on axioms** (#107): PBI + growth + generation is NOT sufficient. Something more is needed.

**Candidates for additional axiom**:
- "Sieve regularity": minFac(n+1) for n in a specific residue class mod q is equidistributed mod other primes — this IS SieveTransfer
- "Weak mixing in CRT space": the map (P mod q, P mod q') eventually decorrelates — requires independence
- "Trajectory non-concentration": the orbit avoids structured subsets of ShiftedSquarefree — requires density estimates

All candidates reduce to known open hypotheses. The "fifth way" remains undiscovered.

### F4: New external mathematics
Monitor for:
- Advances in theory of deterministic walks on groups
- Results about minFac distribution conditional on modular constraints
- Non-ergodic equidistribution theorems for specific dynamical systems
- Results from the Booker-Simon line of work on generalized EM sequences
- Any result about non-stationary, non-random walks on finite abelian groups
- **Pham-Sauermann / Alspach conjecture line** (Session 112): If Alspach's conjecture (Graham for arbitrary abelian groups) is addressed with techniques applicable to FIXED orderings, this could be relevant. Authors plan to return to Alspach's conjecture in future work.
- **Pollack-Roy line** (2023+): Distribution of multiplicative functions in coprime residue classes. Relevant to PE, not to orbit-specific questions. Watch for extensions to conditional distributions.

---

## Track Record

| Session | Proposal | Outcome | Advancement |
|---------|----------|---------|-------------|
| early | Furstenberg correspondence | Dead end (too structured) | 0 |
| 39 | Birkhoff API for EM | Dead end #74 (non-autonomous) | 0 |
| 51 | Nonstationary ergodic theorems | Dead end #86 (requires probability measures) | 0 |
| 62 | Spectral gap for deterministic walks | Dead end #95 (distributions ≠ paths) | 0 |
| 65 | CRT decorrelation → equidist | Dead end #98 (per-step ≠ sequence-level) | 0 |
| 69 | Walk periodicity dichotomy | Dead end #100 (periodic walks can avoid -1) | 0 |
| 70 | Bundle Walk / product group | Dead end #101 (population-level only) | 0 |
| 79 | Bottleneck Decorrelation Axioms | Dead end #107 (explicit counterexample) | 0 |
| 81 | Transition matrix convergence | Dead end #110 (≡ CME) | 0 |
| 91 | Cycle product equidistribution | Dead end #113 (≡ CCSB via telescope) | 0 |
| 97 | SDDS framework (with algebraic agent) | PROVED (joint work: structural framework) | 0.5 |
| 104 | Non-autonomous walk theory assessment | No existing theory found. Frontier identified | 0.2 (closure) |
| 105 | Super-exponential growth | PROVED (`em_super_exponential_growth`) | 1.0 |
| 109 | Accumulating CRT Independence | Dead end #115 (dimensional explosion illusory) | 0 |
| 112 | Cross-term feedback analysis | Confirmed irreducible obstacle (feedback loop between S(k) and m(k)) | 0.1 (closure/clarification) |
| 114 | Sieve-theoretic transfer (Approach D) for DSL | Dead end #116 (circular: sieve axiom = EMDirichlet for auxiliaries). All 4 DSL sub-approaches (A-D) confirmed dead | 0 |
| 120 | Ensemble decorrelation via averaging analysis | Ensemble partially breaks Four-Way Blocker leg A (independence via random starting points). Mixing-time analysis collapses under conditioning on non-q coords. The +1 shift is underexploited. Ensemble gives density-1 not n=2. Real content is sieve-theoretic | 0.3 (clarification + structural limitation identified) |
| 137 | Super-exponential growth → population cross-term decorrelation | Dead end #118. Growth provides ZERO quantitative decorrelation: mod-q residues periodic regardless of magnitude, +1 shift arithmetically entangled, CRT invariance structural not statistical. All 5 questions reduce to sieve content (JSE via CRTPropagationStep). Feasibility: 2/10 dynamical, 5/10 sieve+ensemble | 0 |
| 138 | Return-visit decorrelation analysis | Dead — maps to #90, #98, #113, #118. Coprime cascade: zero residue-class info. Same-position returns: product=1 constraint HURTS decorrelation. Growth invisible mod q. Return-visit char sum = fiberMultCharSum by rfl (no new content) | 0 |
| 142 | SelfCorrectingDrift (SCD) assessment | Dead end #120 (SCD = SVE via Lyapunov telescope). Equivalence collapse: R(N)=o(N²) iff L(N)=o(N²) iff excessEnergy=o(N²). Zero new proof leverage. Zero-drift under uniform ≠ sublinear drift for deterministic EM | 0 |
| 155 | T2.4/T4.3/T4.5 assessment | No new dead ends. T2.4: PBI per-step, EMDImpliesCME aggregate (Marginal/Joint Barrier). CRT freshness → #115, #118. T4.3: no literature exists, counterexamples show axioms insufficient. T4.5: Pham-Sauermann existential/probabilistic, additive vs multiplicative mismatch. All OPEN but ≤2/10 feasibility | 0.1 (closure) |
| 157 | +1 shift / cofactor walk dynamics (Q1-Q3) | No new dead ends (all map to #103, #118, #98, #107, #115). Cofactor walk is coordinate change (bijective, second-order, harder). cofZ is position-dependent (less decorrelated than multiplier). +1 shift CRT leverage = PBI (already proved and exhausted). +1 shift exploitation CLOSED as dynamical direction | 0.1 (definitive closure) |
| 181 | Φ = minFac(·+1) classification: cocycle/carry/martingale/Tao-Collatz | All 5 angles map to existing dead ends (#74, #90, #95, #101). PhiNotCoboundary = population result (Furstenberg group extension gives a.e. equidistribution, EM orbit on Haar-measure-zero set). Φ discontinuous on Ẑ → no unique ergodicity. Step-to-walk gap (Z/4Z counterexample PROVED) kills cocycle approach. MartingaleCME ill-defined for deterministic. Tao-Collatz breaks at 3 points (population-only, non-autonomous, no factoring oracle). T5.8 added to analytic catalog. No Lean code | 0 (confirms: cocycle/ergodic reformulations cannot bypass orbit-specificity barrier) |
| 183 | Reconvergence / Ratner route / unique ergodicity for EM | Pre-flight ABORT. Reconvergence Lemma FALSE (butterfly sensitivity — perturbation at step k cascades through all future multipliers). No "nearby walk" exists. Frequency stability = `walk_readout_from_multipliers` (proved). Unique ergodicity blocked by non-autonomy (EM dynamics on (Z/qZ)× is not an autonomous system). Literature: zero orbit-specific equidist for non-algebraic non-autonomous systems. Maps to #4 (ordering), #90 (orbit specificity), #101 (bundle walk), #130 (generation ≠ coverage). No Lean code | 0 (confirms: no dynamical rigidity argument bypasses orbit-specificity) |

| 266 | Backward dynamics chain viability: AEP + SMLB assessment | AEP FALSE at q=3 (absorption drains nonzero classes exponentially, Dead End #137). SMLB(c) FALSE for fixed c (sieve effect: genSeq grows). Entire ETA→AEP→PRSD chain vacuously true. Only salvageable: live-state conditional equidist → DecayingSMLB → FMD (weaker than PRSD). No Lean code (formalizer handles definition fixes) | 0 (chain collapse confirmation; 2 new dead ends) |
| 276 | FF-specific dynamical reasoning lines assessment (6 questions) | ALL 6 FF-specific questions map to existing dead ends: (1) FF-DSL orbit-specificity = #127 (FF walk sum ≠ standard char sum), (2) perpetual irreducibility = new structural finding (autonomous map f(w)=w(w+1) on F_p) but orbit-specific, (3) monodromy/Deligne = #129 (FFLM false, Deligne = family), (4) SelectionBiasNeutral = #130 (= FF-CME by rfl), (5) pool depletion → capture = counting argument only, (6) Artin-Schreier tower = protects irreducibility, doesn't help coverage. FF setting gives 3 population-level advantages (free PE from Weil, exact π_p(d), explicit Galois) but NONE bypass orbit-specificity barrier. One genuinely new finding: Φ₃ exclusion criterion (formalized in EM/FunctionField/AutonomousMap.lean, 225 lines) proves -1 unreachable for p≡2 mod 3 under autonomous map. Assessment dispatched to analytic agent (which proved the theorems) | 0 (6 questions definitively closed; analytic agent handled the one positive finding) |
| 291 | Scoping Pass S-Φ: Schmidt's theorem applicability to Φ-cocycle on Ẑ | Confirmed Session 181 independently with 4 parallel agents. System (A) (odometer+Φ): all 5 Schmidt hypotheses satisfied, R(c̃) POP-computable, gives a.e.-equidist for consecutive integers (= PE). System (B) (EM iteration): framework inapplicable — cocycle over F(x)=x·minFac(x+1) is tautological. Transfer A→B = Dead End #90. Unique ergodicity fails (Φ discontinuous). New elements: Haar μ(L_p) computation with sum-to-1, E[log Φ] = +∞ (irrelevant for compact G), explicit System A/B taxonomy. Coboundary test = CCSB reformulation (equivalence collapse). Verdict: NO-GO-foundations. No Lean code | 0 (definitive closure: Schmidt/cocycle approach fully explored and dead) |
| 292 | Option 1 consolidation: synthesize evidence from S-LDP, S-Φ, S-Profinite, S-FF | Classification: META-OBSERVATION (not theorem, not conjecture). Cannot be formalized without tautology: defining "dynamically irreducible" circularly. Closest formalizable version: `orbit_barrier_thesis` (conjunction of dead-end witnesses). Four scoping passes converge on same diagnosis: orbit-specificity barrier is intrinsic. Two fundamental barriers: Four-Way Blocker + Marginal/Joint. Publishable as AI-assisted mathematical exploration case study. Falsifiable by: new equidist theorem for non-autonomous deterministic multiplicative walks. Option 3 (FF-AG) CLOSED. Option 1 is main deliverable track | 0.3 (clean consolidation + publication assessment) |
| 308 | WP0 adversarial scoping of the seed-average law + WP5 frontier (LS) | (a)(b)(c) CONFIRMED; (d)(e) CORRECTED (2 bugs found independently: SM seed-magnitude threshold — which makes Theorem C vacuous AND (LS) false — and AG worst-case `ω(m)`); (d)(iii) CONFIRMED, **WP4 deleted** (and two further weakenings: no Mertens of any kind, `A=2`, one crude Abel bound). **Main deliverable: candidate PROOF of (LS)** via the deterministic roughness charge budget `Σ_{r<2n}H_{r−1} ≤ θ(2n)+π(2n) = O(n)` + distinctness of multipliers + brink dichotomy + Freedman — analytic input only Chebyshev. New technique family T7 (population box process). Flagged the per-`q` vs simultaneous scope gap. 2 candidate dead ends (SM, CI) | **2.5** (first genuinely applicable probabilistic-dynamics technique; frontier item moved 2/10 → 6/10) |
| 294 | S-Height scoping: confinement height Ĥ_q as Lyapunov function | NO-GO-capacity-gap. Novel formulation (not equivalence collapse). Avoids 4/5 specific prior failure modes. But capacity-bound gap = MC-mod-q (orbit-specificity #90). N2 (capacity = lower bound, MATCHED-LINEAR) is FATAL. POP/ORB dilemma: POP null → vacuous, ORB null → circular. Existing L(N) strictly dominates Ĥ_q | 0.2 (structural closure; 7th scoping pass confirms barrier from new angle) |

**Session 308 changes the pattern.** For the first time the home domain applies, because the
object changed: the *box process* under the *type measure* is an honest finite probability
space, so martingales and Borel–Cantelli are legitimate. The lesson for future dispatches:
**do not ask "can ergodic theory see the orbit of 2" (answer: no, 29 times). Ask "is there a
population-level process with an honest measure whose coverage forces capture".** The
box process is one; the frontier item (LS) went from 2/10 to 6/10 in a single session because
of a purely deterministic accounting identity (T7.5), not because of any ergodic theorem.

**UNTRIED combinations flagged (Session 308)**:
- T7.5 (charge budget) × T7.6 (brink dichotomy) at **fixed small `q`**: for `q = 3` the
  endgame band is `r < 2k` with `r ≠ 3`; can the budget be made explicit enough to give a
  numerical `κ_3` and a clean `q = 3` theorem first (as §1.7 recommends)?
- T7.5 × the **simultaneous** statement (§G): the budget gives an exponential rate
  `e^{−c₁n/16}` with `c₁` **absolute** (not `q`-dependent!) for (LS); the `q`-dependence sits
  only in `κ_q` and `K₀(q)`. If `κ_q ≳ 1/q^{O(1)}` and `K₀(q) ≲ q`, a diagonal `n(q)` might
  give simultaneous a.a. GenMC. **This is the most promising untried combination.**
- T7 × the mixed/ε-walk framework (`EM/Advanced/EpsilonRandomMC.lean`): the box process is a
  second, independent probabilistic model of the same recursion; do the two coverage
  statements imply each other? (`DenseCaptureHypothesis` vs. `V_∞(q) = all units`.)

**Success rate on novel proposals**: 1/29 (3.4%) led to a proved theorem (super-exponential growth, Session 105). Most proposals hit the fundamental dynamical obstacle: classical ergodic theory requires invariant measures, and no substitute exists for deterministic, non-stationary walks.

**Pattern**: The dynamical agent consistently fails because its home domain (ergodic theory, mixing, spectral gap) requires exactly what EM lacks: randomness and stationarity. The one success (super-exponential growth) was a STRUCTURAL result, not a dynamical-theoretic one. Session 120 confirmed: ensemble averaging provides genuine independence (bypasses Four-Way Blocker leg A) but the propagation of randomness through steps is a sieve problem, not a dynamical one. Session 137 confirmed: super-exponential growth provides zero quantitative decorrelation for population cross-terms (Dead End #118). Session 138 confirmed: return-visit decorrelation is a dead end (coprime cascade gives zero residue info, return product constraint hurts, growth invisible mod q). Future dispatches should focus on:
1. **Ensemble PT**: the viable dynamical-adjacent approach (but content is ANT/sieve)
2. **External monitoring**: genuinely new results about deterministic walks on groups
3. **Infrastructure**: structural lemmas supporting the ensemble chain

**+1 shift exploitation CLOSED as dynamical direction** (Session 157): The cofactor identity is algebraically complete (6 theorems in EM/Reduction/DSLInfra.lean). The cofactor walk is a coordinate change, not new dynamics. cofZ is position-dependent (less decorrelated than multiplier). Any remaining +1 shift leverage is arithmetic/sieve-theoretic. Do NOT re-propose cofactor-based dynamical arguments.

**Do NOT re-propose**: classical ergodic theory (#74, #86, #95), random walk theory (#86, #95), transition matrix arguments (#110), CRT-based "independence" (#98, #107, #115), sieve-theoretic transfer (#116), ensemble mixing-time analysis (collapses under conditioning, Session 120), growth-based decorrelation for population cross-terms (#118, Session 137), SelfCorrectingDrift/Lyapunov reformulations (#120, Session 142 — SCD = SVE via telescope identity), cofactor walk / +1 shift dynamical arguments (Session 157 — coordinate change, no independent dynamics, position-dependent, all leverage arithmetic not dynamical), **Furstenberg group extension / cocycle / skew product / coboundary / Schmidt essential range approaches** (Sessions 181, 291 — PhiNotCoboundary = population, Φ discontinuous on Ẑ, EM orbit Haar-measure-zero, step-to-walk gap unbridgeable, MartingaleCME ill-defined, Tao-Collatz non-transferable, System A ≠ System B decisive, coboundary test = CCSB equivalence collapse, NO-GO-foundations), or **Reconvergence / Ratner analogies / unique ergodicity / perturbation coupling** (Session 183 — Reconvergence Lemma FALSE via butterfly sensitivity, unique ergodicity blocked by non-autonomy, no orbit-specific equidist for non-algebraic systems in literature), or **confinement height / avoidance-cost Lyapunov arguments** (Session 294 — γ_q constant under all population nulls, capacity = lower bound MATCHED-LINEAR, POP/ORB dilemma, L(N) strictly dominates Ĥ_q).

---

## Session 309 addendum (2026-08-18) — §F verified and largely formalized

The T7.5 candidate proof was adversarially verified (attack-analytic): **CONFIRMED-WITH-
CORRECTIONS** (C1–C6, full report `agents/state/findings_ls_verification.md`). Highlights:
- **Sound**: charge bookkeeping exact (`Σ 1/|B| ≤ H_{r−1}`, no hidden log; budget tight up
  to ≈1.6×); no circularity; the random-good-step-set worry dissolves because only the SUM
  `Σ S_k` is used and its lower bound is sure. Four-Way-Blocker leg 4 genuinely not needed.
- **Corrected**: r = q must be excluded everywhere (brink FALSE at r = q); near band is
  `r ≤ 2k+1`; the truncation quantifier `∃Y₀ ∀Y ≥ Y₀` kills the far-band constant — Y must
  be a POLICY `log Y(n) ≍ n²` with cutoff `k ≥ n/log n` (this also changes the Theorem C
  (e-3) statement shape); the tail estimate along Y(n) is new work (~200 lines, `≲ log n/n`);
  **the block substitute is invalid** (see T7.7) — tree supermartingale instead.
- **Bonus**: `#{k < n : S_k = 0} ≤ π(2n)` pathwise — the (e-2) non-null event is exactly the
  spoiled-step set, density o(1). For the paper.
- **Lean status after Session 309** (`EM/Population/`): `SeedCapture.lean` (548 lines —
  q-free dynamics, Lemma C coupling+capture, capture identity `captured_iff_mem_visited`);
  `LargeStepRoughness.lean` (992+ lines — Groups 1–3 complete incl.
  `charge_sum_le_harmonic`, `brink_forces_small_multiplier`; Group 4 B1–B3/B7/B8;
  F1f–F1h `chargeBudget_le`; M1/M2). Remaining: B4/B5 (slice 3, dispatched), M3/M4 +
  ★`pathwise_compensator` assembly, Group 6 tree Chernoff, Group 7 tail, then Lemma D +
  Theorem C. All statements per the §4 list in the verification report.

## Session 310 addendum (2026-08-19) — (LS+) IN LEAN; T7.5/T7.6/T7.7 all landed

Commit f391732, four new files, 0 sorry:
- **T7.5 → FULLY IN LEAN** including ★`pathwise_compensator` (Session 309 slice 4) and now
  its probabilistic consumption. Lean constant `c₁ = exp(−250)` (absolute, crude; do NOT
  quote the report's exp(−35/−36) as the Lean value).
- **T7.6 (type measure / selection law) → PROVED** (`SelectionLaw.lean`): type cells over
  `modulus q Y = ∏_{r ∈ bandUpTo q Y} r` (q excluded — the q-coordinate stays CRT-free for
  Lemma C), dependent-family CRT counting `card_filter_crt`, EXACT
  `selection_law : #(cell ∩ Survives) = survival·#cell`.
- **T7.7 → PROVED** (`TreeChernoff.lean`, abstract, Mathlib-only): `exp_supermartingale`,
  `chernoff_quarter` rate `exp(−(3/8)v)`. C6 handled by LOCALIZATION (`chernoff_*_local`
  — bad set ∩ {v ≤ compensator}; no stopped process needed). The stopped-supermartingale
  construction in the verification report is thereby unnecessary in Lean.
- **(LS+) PROVED** (`LSPlus.ls_plus`): `#{m : < (c₁/8)n big steps} ≤ M_Y·e^{−(3/16)c₁n} +
  #{degenerate-prefix seeds}` over one period, under the Y-policy `log Y ≤ n²` and the
  threshold hypothesis `y_k ≤ Y` (D5c discharge lemma pending).
- **Lower Mertens toolbox landed** (`MertensLower.lean`): `mertens_lower` (const 13),
  `window_recip_lower` (const 16) — TL2/TL3's analytic input is DONE.
Remaining for a.a. GenMC(q): Group 7 tail ASSEMBLY (bookkeeping + one Markov exclusion),
D5c, Lemma D, Theorem C. Then §G (q-uniformity) is the genuinely open frontier.

## Track record — Session 311 (2026-08-19)
| Technique | Outcome |
|---|---|
| TreeChernoff reuse with prescribed-class successes (no new engine) | PROVED — theorem_C; supersedes the (e-2) block-chaining/Freedman plan |
| Deterministic success cap via strict-growth + multiplier distinctness | PROVED — success_count_le ≤ 2q |
| "V full ⟹ all residues captured" (kills the q-coordinate CRT issue) | PROVED — captured_of_visited_full; the theorem lives on the M_Y period |
| Guard-failure-at-exposed-step forces capture (compensator bookkeeping) | PROVED — guard_of_exposed |
This is the vector's second and third genuine successes (after S309 pathwise_compensator);
the catalog's 7% historical success rate applies to CLASSICAL ergodic proposals, which
remain dead — the live pattern is finite-tree martingale arguments on the type filtration.

## Session 313 (2026-08-19) — T7's orbit direction is CLOSED

**T7 scope — strengthened.** T7 was already capped at a.a. GenMC(q) and not a route to MC (#90,
non-uniformity in `q`). Session 313 found the stronger and more precise reason: **the sure sub-layer
of T7 cannot by itself constrain any single orbit at all**, because (a) it is proved about a dynamics
that misses `q` by construction (`SeedCapture.genSeqAvoid_ne_avoided`, dead end #171), (b) per prime
it is an identity equivalent to `boxCard_pos` (#169), and (c) its two inequalities point *away* from
capture (#172). The per-`q` scope cap is **not** a quantitative limitation to be improved — it marks
where the population statement is doing all the work.

**T7.5 (charge budget) — append.** Per-`r` content is an identity, `= H_{r−1} − H_{r−1−C}`, equivalent
to `boxCard_pos`, hence to the `minFac` tautology "a declined prime does not divide". Symmetric between
captured and missed primes. Only the *aggregate* over `r < 2n` (via Chebyshev) is non-tautological,
and it is saturated to within an absolute constant by generic behaviour. An upper bound on charge
cannot exclude the zero-charge (capture-free) regime.

**T7.7 (compensator) — append.** `S_k ≡ 1` is the capture-free *extreme*, not evidence of progress.
The compensator is consumed only through the type measure. Also: its type bound `log Y ≤ n²` is a
seed-population **policy**; the true orbit permits `log Y ≈ 2^n`, so it cannot be instantiated at
`m = 2` (#173).

### T7 — what the sure layer cannot do

Dead ends #169 (CO, identity), #170 (CI, `¬DH` circularity, mirror of #166), #171 (SF, model
obstruction — *witnessed*), #172 (OS, wrong sign), #173 (AG, policy hypothesis), #174 (TM, (C∞) gate).

Plus one **principle**, to sit beside the Session-299 anatomy principle:

> **Sign asymmetry of `minFac`.** `p_k = minFac(N_k)` yields infinitely many *negative* facts
> (`r ∤ N_k` for `r < p_k`) and exactly **one** positive fact (`p_k ∣ N_k`, about a prime captured by
> definition). Hence the sure layer produces only *upper* bounds on hit counts — `#{k : q ∣ P(k)+1} ≤
> π(q)` for **every** `q`, captured or missed — and never the lower bound of 1 that capture requires.
> **Before proposing any per-path route, ask: does it produce a positive divisibility fact about a
> prescribed prime? If not, it is inert.**

**The `(ℤ/5)^×` witness of #90/#117 is literally a box-process witness.** With `q=5`, `m=2` and every
multiplier `≡ 4 (mod 5)`: `box = {2,3}` forever, exactly **two** charges in the whole history
(`Σ 1/|box| = 1/4+1/3 ≪ H₄`, enormous slack), the brink never reached, `S_k ≡ 1` (compensator
maximally satisfied) — and `5` missed forever. Distinctness does not rescue it: it constrains the
*primes*, not their *residues*, and infinitely many distinct primes lie in `4 mod 5`.

### Do NOT re-propose

Per-orbit consequences of the charge budget / brink lemma / pathwise compensator; any attempt to bound
the missed set of a single Euclid–Mullin orbit from the sure layer; any argument that reads `1/|box|`
as a per-path quantity.

### Track record

| 313 | Sure layer (charge budget / brink / compensator) applied to a single orbit's missed set | **DEAD — budget vacuous.** Budget is an identity ⟺ `boxCard_pos` ⟺ `minFac` tautology, symmetric in captured/missed; the `q`-free model (`genSeqAvoid_ne_avoided`) satisfies the whole layer while missing `q`; the `r=q` specialisation is `¬DH(q)` (circular, mirror of #166); the `(ℤ/5)^×` #90/#117 witness is literally a box-process witness with maximal slack and `S_k ≡ 1`. Minimal ingredient (NPLB) ⟺ MC-mod-`q`. Six new dead ends (#169–#174), one new principle. | **0.4** |

**F0 frontier item** — keep at 6/10 for its actual target, but annotate: the §G simultaneous-in-`q`
question is *the last place the box process can go*; the orbit direction is closed by this session.
