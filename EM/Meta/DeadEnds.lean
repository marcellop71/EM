import EM.Reduction.SelfCorrecting
import EM.Reduction.SMSB
import EM.Reduction.WeakRecurrence
import EM.Meta.Diamonds
import EM.Meta.Dobrushin
import EM.Meta.LFunction
import EM.Meta.MarkovSieve
import EM.Adelic.UniformConductor
import EM.Adelic.Profinite
import EM.CME.Reduction
import EM.Ensemble.Decorrelation
import EM.LargeSieve.PrimeArithLS
import EM.FunctionField.Analog
import EM.FunctionField.MultiplierCCSB
import EM.Group.CyclicWalkCoverage
import EM.GaussEM.GaussConfinement
import EM.GaussEM.GaussWalkStructure
import EM.Population.ReciprocalSum
import EM.Population.AutonomousBranch
import EM.Stochastic.FactorDiversity
import EM.Stochastic.EpsilonDegeneration
import EM.Obstruction.NoInvariant
import EM.Meta.OrbitBarrier
import EM.Population.HeadDomination
import EM.Equidist.SieveTransfer
import EM.Ensemble.UncenteredRefutations
import EM.Reciprocity.NoReciprocityInvariant

/-!
# Dead End Registry

Central catalog of all documented dead ends in the EM formalization.
Each entry records the dead end number, category, one-line description,
the file where it is documented, and whether a formal Lean witness exists.

## Categories
- **OS** — Orbit-Specificity: population statistics ≠ orbit statistics
- **TM** — Technique Mismatch: framework assumes structure EM lacks
- **SM** — Scale Mismatch: error terms dominate the signal
- **CI** — Circularity: reduces to the hypothesis it aims to prove
- **SF** — Structurally False: provably impossible (counterexample)
- **CO** — Collapse: reduces definitionally to an existing hypothesis
- **DG** — Decorrelation Gap: transfer from marginal to joint fails
- **AG** — Aggregate Gap: average-case ≠ per-fiber case

## Weak-MC Revival Scores (0–3)
- **0** — stays dead for any weak form
- **1** — marginal help, contributes indirectly
- **2** — medium: helps for AlmostAllRSD or positive density
- **3** — high: revives substantially for a specific weak MC form

## Catalog

**Single source of truth: `tools/dead_ends.tsv`** (one row per number 1–160: category, name,
approach, rationale, session, witness, revival score, status).  `python3 tools/gen_dead_ends.py`
regenerates the block below, `paper/dead_ends_table.tex` (the complete catalogue in the paper's
appendix), `paper/dead_ends_stats.tex` and `docs/dead_ends_catalog.md`, and prints the counts that
`deadEndCount` / `deadEndEntryCount` / `witnessedDeadEndCount` / `revivableDeadEndCount` below must
match.  The 2026-08-18 reconstruction recovered every numbered entry from the session logs (the
tables that used to live here covered only ~70 numbers); ten numbers (#25, #64–#72) were never
assigned in any log and are listed as unassigned rather than back-filled.  A "witness" is a
genuine, non-placeholder Lean theorem; the `True`-bodied markers of #129, #131–#135 are not
witnesses (audit 2026-08-17).  A ninth code **MR** (methodological rule) covers #1–#3.

Unnumbered: the Gaussian-EM orbit-specificity barrier (`GaussEM.gauss_orbit_specificity_barrier`,
`GaussEM/GaussWalkStructure`, category OS, revival 1) is recorded here without a number.

<!-- BEGIN GENERATED CATALOGUE -->

160 numbers; 150 catalogued entries; 29 with a genuine Lean witness; 10 with revival score ≥ 2; unassigned numbers: #25, #64, #65, #66, #67, #68, #69, #70, #71, #72.

### Orbit specificity (OS, 8) — population or ensemble statistics do not determine what one orbit does
| # | Dead end | S | Why it fails | Witness | Rev |
|---|---|---|---|---|---|
| 9 | Chebotarev / Kummer route | 10 | Chebotarev not in Mathlib ($\sim$5000 lines); even if available it gives population density (SieveEquidistribution), not orbit-specific SieveTransfer. Abelian case degenerates to Dirichlet in APs (Session 298) | — | - |
| 18 | Target-diversity heuristic (SieveTransfer) | 13 | Heuristic only: needs an Alladi-type theorem for the specific EM products; reduces to proving $\mathrm{prod}(n)+1$ generic w.r.t. small factors = SieveTransfer. Superseded: GenericLPFEquidist false, SieveTransfer vacuous (#160) | — | - |
| 30 | Information-theoretic argument for BRE | 16 | BRE failure has ensemble probability $(s/d)^N$ but EM is one deterministic sequence (zero entropy); ensemble-to-specific gap; restates decorrelation without content | — | - |
| 32 | Bombieri–Vinogradov for EM subsequence | 17 | BV applies to all primes in APs, not to the greedy EM subsequence; also Mathlib-blocked (#55–57); EM bridge `BVImpliesMMCSB` open, MultCSB $\not\Rightarrow$ MMCSB (#58) | — | - |
| 90 | Population statistics do not determine orbit | 59 | Four-Layer Gap: no technique spans population $\to$ individual, unconditional $\to$ conditional, static $\to$ growing, counting $\to$ distribution. Witness: periods $(2,2,3,3)$ and $(2,3,2,3)$ in $(\mathbb Z/5)^\times$ have identical statistics; only the first hits $-1$. Superseded in part: PE/UCE false (#160), bridges vacuous. | `OrbitBarrier.population_does_not_determine_hitting` | 3 |
| 127 | Weil bound does not close FF-DSL | 166 | Weil gives population equidistribution of irreducibles only; $\mathrm{ffProd}(n)+1$ is one specific polynomial, the walk sum is a sum of products of character values (not a Weil sum), and the relevant population is $O(1)$; orbit specificity (#90) and the Four-Way Blocker are unchanged. | — | 2 |
| 148 | Consumption ledger is one-sided | 299 | The ledger only yields caps (`hittingSet_ncard_le_appearing`, starvation); a contradiction needs a lower bound on spending, which requires orbit control, exactly what the consumption discipline forbids. Detection strength is zero (tail class $0$ unconditionally via `exists_tail_coprime`); the Gap is false, not hard. | `hittingSet_ncard_le` | 1 |
| 158 | Tail-identity Borel–Cantelli is #90 again | 307 | `standard_tail_not_bad` needs the bad set to have $\mathrm{card}=0$, not density $\to 0$; a density-zero bad set may contain the sparse sequence $\{\prod M\}$ at no cost. The identity turns an orbit statement into an ensemble-member statement, but specificity reappears as which members are good (#58/#117). | — | 0 |

### Decorrelation gap (DG, 7) — multiplier-level cancellation or independence does not transfer to the walk
| # | Dead end | S | Why it fails | Witness | Rev |
|---|---|---|---|---|---|
| 5 | Cofinal-cycle arguments plus SE | 5 | Cofinal orbit captures only marginal properties, all consistent with HH failure (§23 counterexamples); pumping gives $\ell \ge \Omega(q-1)+1$, logarithmic not linear. Marginal/Joint Barrier | — | - |
| 58 | MultCSB does not imply MMCSB | 28 | False: multipliers $(-1,-1,+1,+1)$ repeating give $S_M=O(1)$ but walk sum $N/2$; $(\omega,\omega^2,1)$ gives $\Theta(N)$. Order of multipliers matters for products, not sums; PED, NoLongRuns, DPED, Abel summation do not repair it. | `OrbitBarrier.mult_cancel_not_walk_cancel` | 0 |
| 81 | CME does not imply HOD ($h\ge2$) | 43 | CME gives Dec ($h=1$) by fiber decomposition, but $h$-fold products couple consecutive multipliers through $w(n+1)=w(n)m(n)$; conditioning on a single position does not control these correlations. Hierarchy PED $<$ Dec $<$ CME $\le$ CCSB. | — | 0 |
| 98 | CRT decorrelation gives no leverage | 65 | Per-step exogeneity is not statistical independence: conditioning on $w(n)=c$ selects a biased time subsequence. CMI+FPE is CME. Counterexample: multipliers $\{2,3\}$ alternating in $(\mathbb Z/5)^\times$ generate the group but the walk cycles $\{1,2\}$, never hitting $-1$. `dh_iff_partial_product_surjective` false. | — | - |
| 115 | Cofactor / accumulating-CRT joint barrier | 109 | $P(n)$ is one locked point, not a generic one; the walk mod $q$ has dimension 1 (same $\{2,3\}$ in $(\mathbb Z/5)^\times$ counterexample). The cofactor is a joint quantity in bijection with the multiplier when alive, so CED is ensemble CME in other notation. | — | 0 |
| 117 | MultCancel does not force WalkCancel | 128 | Multipliers alternating $\{2,3\}$ mod 5 with $\chi(2)=i$: multiplier sums vanish for even $K$, but $W_K=(K/2)(1+i)$, $\|W_K\|=\Theta(K)$. Compatible with every EM structural property; the transfer is equivalent to CCSB/CME. Sharpens #58. | `OrbitBarrier.mult_cancel_not_walk_cancel` | 0 |
| 123 | FourPointPCV: cross-time is not cross-modulus | 146 | SCRTI gives cross-modulus independence at one time; FourPointPCV needs cross-time independence at one modulus. Four-time decay is HOD-type mixing (#84), harder than CCSB; the four values are deterministic functions of one seed (#115); pairwise PCV itself open. Superseded: false (#156), DSL vacuous (#160). | — | - |

### Aggregate gap (AG, 5) — an average-case or aggregate bound does not give the per-fibre or per-class bound needed
| # | Dead end | S | Why it fails | Witness | Rev |
|---|---|---|---|---|---|
| 101 | Bundle Walk / Weak MC / profinite | 70 | BundleGap is weaker than SieveTransfer as a statement but no technique proves it otherwise; product-group characters do not factor (shared minFac index couples moduli), reducing to MMCSB; $\delta(M)\to0$ is population-level. In $(\mathbb Z/11)^\times$ cycling $\{3,4\}$ generates yet visits only $\{1,3\}$. | — | 0 |
| 106 | VCB implies CCSB iff PED | 78 | Telescope forces $(\mu-1)S_N=O(1)$: if $\mu\ne1$ CCSB is trivial, if $\mu\approx1$ kernel confinement kills CCSB, so (VCB$\Rightarrow$CCSB)$\iff$PED. Resampling error is #98, deviation is #90; fiber Parseval cross-character terms are unconstrained. Aggregate does not give per-fiber control. | — | 2 |
| 121 | SMSB plus SE per-class escape | 143 | $\|B\|\le\delta N$ gives by pigeonhole some class with small bad density, not all and not $-1$; per-class uniformity needs $P(\mathrm{bad}\mid w=c)\approx P(\mathrm{bad})$, i.e. CME. SE gives generation, not statistics. Superseded: SMSB false at $\chi\equiv1$ (#156). | `marginal_joint_barrier_witness` | 2 |
| 139 | Backward-dynamics chain broken everywhere | 266 | ETA false at $c=-1$ (#136), DCTA false at $q=3$, SRE mis-stated (#138), CRTPropagationStep false (absorption drains nonzero-class mass each step even with the corrected limit), AEP false (#137), SMLB$(c)$ likely false since absorption forces $\mathrm{genSeq}$ to grow; chain zero-sorry but vacuous. | — | 0 |
| 153 | Iwasawa / Euler-system receptacle | 299 | Kolyvagin derivatives need classes over the full squarefree lattice; the orbit supplies a single maximal flag $P_0 \mid P_1 \mid \cdots$. No $\mathbb{Z}_p$-tower (layer degrees are not $p$-powers), no motive, no period formula. | — | 0 |

### Collapse (CO, 27) — the proposed hypothesis is definitionally (or by a short argument) equivalent to an existing one, usually CME, CCSB or MC itself
| # | Dead end | S | Why it fails | Witness | Rev |
|---|---|---|---|---|---|
| 10 | WeakDecorrelation equals TailSE | 11 | Equivalent to TailSE, already known insufficient: gives escapes $R(N)\to\infty$ but not positive escape density, so no $o(N)$ walk sum | — | - |
| 19 | BRE intermediate equals CCSB | 14 | BRE for $\chi$ of order $d$ is equivalent to CCSB for $\chi,\chi^2,\dots,\chi^{d-1}$ (time-equidistribution among $d$-th roots of unity), so BRE is CCSB, not a simplification | — | - |
| 35 | BV plus threshold | 17 | All multi-modular variants collapse to single-modulus CCSB; BV exceptional set is density-zero, not finite; the EM-specific transfer is SieveTransfer | — | - |
| 73 | SVE not provable from existing infrastructure | 38 | SE gives existence not density; coprimality invisible to the residue walk; PED constrains multipliers not walk phases; VdC at $h=1$ gives $\\|S\\|^2\le N^2/2$, a constant factor; growth is heuristic. Later proved SVE $\Leftrightarrow$ CCSB, so this collapses onto CCSB. | — | - |
| 79 | HOD is not a useful attack target | 40 | HOD is strictly stronger than CCSB (#76) with the same consequence, so proving HOD is the wrong direction; the reduction only documents the hierarchy and offers no simplification. | — | - |
| 82 | Cyclic Littlewood–Offord / Tiep–Vu adaptation | 46 | Reduces entirely to Dec/HOD: for a cyclic group the mechanism is $E[\prod\chi(X_k)]=\prod E[\chi(X_k)]$, independence used only to factor; MultiplierAntiConcentration $=$ PED; anti-concentration bounds the endpoint law, not the walk sum. No result exists for dependent products. | — | - |
| 84 | Pseudo-independence notions reduce to Dec/HOD | 46 | Pair mixing and exponential pair decay $=$ Dec (VdC $h=1$ gives $N/\sqrt2$); $k$-point decay $=$ HOD (unverifiable); block independence $=$ HOD at coarser scale; CME $=$ Dec only (#81). EM feedback gives zero anti-concentration leverage. | — | - |
| 85 | VdC plus EscapeDecorrelation equals QuadraticCCSB | 49 | For $\chi^2=1$, $\chi(w(n+h))\chi(w(n))=\prod\chi(m(n+j))$, so EDH is literally ``walk autocorrelations are $o(N)$'', which is QuadraticCCSB by VdC; $h=1$ alone gives $O(N)$; BV supplies only $h=1$; PED does not imply EDH. | — | - |
| 92 | Self-correction forcing equidistribution | 59 | Feedback is summable ($\sum 1/\mathrm{seq}(n)<\infty$): it stabilises the walk but cannot force bias to zero. Necessary, not sufficient; extracting rates needs minFac conditioned on residue class, which is SieveTransfer/CME itself. Reformulation, not reduction. | — | - |
| 93 | Density-1 CME / FEB equivalent to CME | 61 | On the finite set of $q-1$ positions $L^2$ and $L^\infty$ coincide (Markov: $#\{a:\|F(a)\|>\varepsilon N\}\le CC_\chi/(\varepsilon N)^2\to0$); removing a $\delta N$ fiber bias needs $\ge(\delta-\varepsilon)N$ deletions, exceeding the $o(N)$ budget. No $L^p$ interpolation; strictly stronger than CCSB. | `cme_implies_feb` | 0 |
| 97 | LP avoidance framework equals DH | 64 | LP is feasible for many proper $T$ and always for $T=G\setminus\{-1\}$ (cannot detect single-element avoidance). Infeasibility for all $T$ with uniform FPE is equivalent to DynamicalHitting; only the FPE marginal is nontrivial and that is the open content. Fourier side reduces to CCSB. | — | - |
| 99 | CME spectral gap / bias propagation | 66 | Flow-balance is one equation in $p-2$ unknowns (underdetermined); equal rows fail by biased subsequence selection; spectral gap is #95 again; return products hold tautologically for any returning walk (group law), carrying no EM information. | — | - |
| 100 | Walk periodicity dichotomy | 69 | Periodic walks need not give $o(N)$ sums: period $p<q-1$ with nonzero one-period sum gives $\Theta(N)$. The trichotomy is a reformulation; ruling out periodicity removes the easy case and proving aperiodicity needs the same tools as CCSB. | — | - |
| 103 | No third algebraic route to CCSB | 72 | The telescope $\chi(w(n+1))=\chi(w(n))\chi(m(n))$ is the complete algebraic content. Abel gives $O(N^2)$ remainder; differencing yields norm-1 terms; Moebius needs multiplicativity in $n$; Dirichlet series needs structure. Blocks reduce to HOD (#78), CRT to #75/#98/#101. CME and HOD exhaust the routes. | — | - |
| 104 | Summable Decorrelation collapses to VCB | 74 | VCB+PED$\Rightarrow$CCSB was proved outright (`vcbPedImpliesCcsb`), so SD is strictly stronger than VCB yet adds zero leverage; verifying SD for EM meets #90/#98. Not a published concept. | — | - |
| 105 | First passage / ExistentialCME equals DH | 75 | The phased identity is character orthogonality restating $V_N(-1)=0$; ExistentialCME ($\exists c,n$: $w(n)=c$, $m(n)=-c^{-1}$) is literally DH; inter-character cancellation needs HOD (#79). A walk can generate the group, use every step cofinally, and avoid one element forever. | — | - |
| 110 | Transition matrix / Doeblin equals CME | 81 | $K_N(a,b)/V(a)\to$ uniform is CME (`cme_iff_transition_char_vanish`); DoeblinConvergenceForEM $=$ CME by `rfl`. Transition counts are joint counts, so the convolution-kernel identity itself needs CME. All convergence techniques need randomness or stationarity. | `doeblin_eq_cme` | 0 |
| 112 | Order-3 Moebius death function | 83 | It constrains the death-curve geometry, not the walk dynamics; the dynamically relevant map is the order-2 involution $f(c)=-c^{-1}$, already formalized. Avoidance graph is a perfect matching with no combinatorial leverage; Marginal/Joint Barrier untouched. | — | - |
| 114 | Missing-prime accumulation / Borel–Cantelli | 97 | Pairwise death-channel independence is CME restricted to one fiber; the self-consistent avoidance model restates the earlier orbit analysis; Kochen–Stone needs pairwise quasi-independence of $\{q\mid P(n)+1\}$, the joint-distribution barrier. Population-to-orbit transfer is SieveTransfer (#90/#98/#107). | — | - |
| 120 | SelfCorrectingDrift equivalent to SVE | 142 | `lyapunov_telescope`: $L(N)=2R(N)+N(q-2)/(q-1)$, so $R=o(N^2)\iff L=o(N^2)$ and SCD is SVE restated in drift language (above threshold $Q_0$); maps to #73/#92/#95. No new leverage. | `lyapunov_telescope` | 2 |
| 122 | Tail Window Decorrelation | 144 | TWD controls multiplier sums, giving Dec at best, and Dec does not imply CCSB (#20/#58/#117); the walk-sum version is block HOD at scale $K$ (#84) $=$ CME. Cycling $\{g,g^{-1}\}$ has bounded cross terms but walk sum $\Theta(N)$. Superseded: TWD false (#156). | — | - |
| 124 | T5.7 Lyapunov–fiber coupling | 154 | $J$ is marginal (bilinear contraction loses joint information); the one-step recurrence contains the active-fiber sum $F(w(N),N)$, the CME gap; Cauchy–Schwarz bounds go the wrong way; $J=o(N)$ is one scalar constraint on a $(q-1)$-dimensional problem. Maps to #110/#104/#120. | — | - |
| 143 | Congruence certificate collapses to MC | 298 | The No-Invariant Theorem `no_cvdp_obstruction` (eviction, free-state fullness via Dirichlet, CRT-reach) shows no propagating congruence set blocks a missing prime, so `IC_min` $\leftrightarrow$ `MullinConjecture`; `SingleHitHypothesis`/`DynamicalHitting` make it vacuous. Any disproof of MC must be non-congruential. | `CvdP.ic_min_network` | 0 |
| 145 | Simultaneous avoidance decouples | 298 | $k$-fold missingness is the monotone condition $S\cap\mathrm{Im}(\minFac)=\emptyset$ with no interaction term; the apparent tail confinement is unconditional (holds for present primes too); the only shared budget (rogue characters + large sieve) is mispriced by $2^N/N$ (#108); embeddings give almost-all statements (#90). | `CvdP.hittingSet_finite` | 1 |
| 149 | Ledger small-prime output weaker than injectivity | 299 | The ledger gives $\sum_{p\le y} h_\infty(p) \le \pi(y)^2$, strictly weaker than the injectivity bound $\pi(y)$ (`seq_injective`), because ``$\exists p\le y$ with $p\mid N_n$'' is ``$\minFac N_n \le y$'': the roughness trap, quantified. | `seq_injective` | 0 |
| 150 | Covering-system congruence obstructions | 299 | Covering systems are finite by definition, so `exists_tail_coprime` at $m=\prod T$ kills fixed-finite-prime-set covering (`no_finite_prime_covering`); assembling at the lcm gives one set at one modulus and `no_cvdp_obstruction` is set-generic. Residual escapes: unbounded/profinite families and anatomy invariants. | `CvdP.no_covering_family_obstruction` | 0 |
| 159 | $\varepsilon$-interpolation family reformulates MC | 307 | `mullin_iff_exists_failWeight_bound`: for $q\neq 2$, MC at $q$ iff some $(\varepsilon,N,c)$ with $N\varepsilon<c$ has $\mathrm{failWeight}\le 1-c$; outside $N<c/\varepsilon$ no bound exists unless MC holds; if $q$ never occurs, $\mathrm{failWeight}\ge(1-\varepsilon)^N$, compatible with a.s. capture at every fixed $\varepsilon$. MC relocated into a finite window, not weakened. | `mullin_iff_exists_failWeight_bound` | 0 |

### Circularity (CI, 11) — the argument presupposes the conclusion or an equivalent
| # | Dead end | S | Why it fails | Witness | Rev |
|---|---|---|---|---|---|
| 12 | PairDecorrelation is circular | 11 | $h=1$ correlation is just the multiplier sum (`walk_shift_one_correlation`); $h \ge 2$ requires PairDecorrelation, which is equivalent to walk equidistribution / DH itself — circular | — | - |
| 14 | Expander graphs for PED | 11 | Circular: PED is needed as input to get expansion; $(\mathbb{Z}/q)^\times$ abelian, quasirandomness 1, Bourgain–Gamburd inapplicable | — | - |
| 16 | Selberg sieve on EM products | 13 | Density approximation $\mathrm{multSum}(d) \approx \nu(d)\cdot\mathrm{mass} + \mathrm{rem}(d)$ needs $#\{n : d \mid \mathrm{prod}(n)+1\}$, i.e. walk equidistribution mod $d$ — the very thing to be proved. Population use later itself false (#160) | — | - |
| 21 | Weyl-criterion shortcut for partial products | 15 | Needs $s_n$ equidistributed mod $d$; van der Corput / ergodic tools reduce to PairDecorrelation or stronger; the finite Weyl criterion (later proved) is CCSB itself | — | - |
| 52 | Five direct CCSB approaches via product structure | 22 | Q1: divisibility invisible to characters. Q2: reduces to SieveTransfer/CME. Q3, Q5: reach only PED, insufficient for $d\ge3$. Q4: walk equidistribution is CCSB by orthogonality (circular). All single-modulus routes reach PED at best. | — | - |
| 54 | BV decomposition obstacles, CrossPrime, direct LoD | 25 | BVImpliesMMCSB faces the same generic-to-EM gap as SieveTransfer; CrossPrimeAmplification has no published technique; a direct LoD proof is equivalent to SieveTransfer, and `EMHasLevelOfDistribution` as stated has an exponentially large bound (later #96). | — | - |
| 61 | ArithLS to MMCSB via occupation measure | 35 | Circular: $\sum\|a_n\|^2$ is the $L^2$ norm of the visit distribution, large exactly when the walk is not equidistributed; dense coefficients give the trivial bound $N^2(p+1)$, worse than the triangle inequality. | — | - |
| 113 | Cycle product equidistribution circular | 91 | By the telescope $\chi(R_k)=a_{k+1}/a_k$, equidistribution of $R_k$ is a walk character-sum bound at return times, i.e. CCSB for $p$; lag-1 autocorrelation is #92/#98, cross-cycle decorrelation #98/#58, $\ell\ge2$ reduces to HOD (#79). | — | - |
| 116 | Sieve-theoretic transfer for DSL circular | 114 | The sieve axiom $\omega(r)\sim1/r$ is EMDirichlet mod $r$, so the argument assumes EMDirichlet for all auxiliaries: circular for $q\le L$, reduces to BVImpliesMMCSB for $q>L$. CRT independence is a scope error (for fixed $r$, $r\equiv a$ mod $q$ is deterministic). Superseded: DSL vacuous (#160). | — | 0 |
| 132 | L-function factorization is circular | 173 | Controlling $L_{\mathrm{non\text{-}EM}}$ requires knowing which primes are non-EM, i.e. MC itself; the reformulation reduces to the hypothesis it aims to prove (maps to #90). | — | 1 |
| 134 | No Tauberian lever for $L_{\mathrm{EM}}$ | 173 | $\prod n \ge 2^{n+1}$ makes the series converge for all $s>0$ (`accum_reciprocal_summable`); $L_{\mathrm{EM}}$ is entire on $\Re s>0$ with no pole at $s=1$. The standard PNT route uses $L(s,\chi)$ over all primes, already formalized. | — | 1 |

### Structurally false (SF, 26) — the proposed statement is false: an explicit counterexample or a proved refutation
| # | Dead end | S | Why it fails | Witness | Rev |
|---|---|---|---|---|---|
| 6 | Direct SE implies DH (generation not coverage) | 5 | Counterexample: in $\mathbb{Z}/6$ steps $2,2,2,\dots$ generate but partial sums cycle $0,2,4$ and miss all odd elements; generation does not imply coverage. Later $\mathbb{Z}/4$ witness | — | - |
| 20 | Decorrelation does not imply CCSB | 15 | Counterexample: increments equidistributed in $\mathbb{Z}/3$ (bunched by type) but walk stalls; alternating steps in $\mathbb{Z}/4$ generate yet the walk misses 2. Step cancellation is not walk cancellation | `alternating_walk_misses_two` | 1 |
| 36 | PED to BRE fails for $d\ge3$ | 18 | Counterexample on $\mathbb{Z}/3$: block values $1,\omega,1,\omega,\dots$ with lengths $M,1,M,1,\dots$; escape density $2/(M+1) > 0$ but walk sum $\approx N$. Escape density fixes frequency, not distribution among $d-1$ rotations | — | - |
| 37 | NoLongRuns plus PED implies BRE fails | 18 | Variable block lengths still align adversarially with character phases for $d \ge 3$; Abel gives total variation $\le 2N$, bound $O(N)$ = trivial. Order-2 case provable (`bre_order2_from_noLongRuns`) | — | - |
| 42 | Cumulative SieveEquidist implies NoLongRuns | 20 | Cumulative density on $[0,N)$ does not exclude a late run of $L$ kernel steps at $n \gg L$; fixed by window version `StrongSieveEquidist` (`strongSieveEquidist_noLongRunsAt` proved). #160 later voided the sieve-route endpoint | — | - |
| 45 | DPED to CCSB fails for $d\ge3$ | 21 | Counterexample: rotations alternate $\omega,\omega^2$ (DPED holds), cumulative products cycle $\omega,1$, walk sum $(N/2)(1+\omega)$ of norm $N/2 = \Theta(N)$; DPED controls pointwise not sequential correlations; PED $<$ DPED $<$ RI $\approx$ CCSB | — | - |
| 46 | Escape-value distribution intermediates below CCSB | 21 | Sequential correlations matter, not pointwise statistics: rotations alternating $\omega,\omega^2$ have perfect pointwise balance yet cumulative products cycle $1,\omega$, giving walk sum $(N/2)(1+\omega)=\Theta(N)$. Only controlling cumulative products works, which is CCSB itself. | — | - |
| 76 | CCSB does not imply HOD | 40 | CCSB bounds $\sum\chi(w(n))$, HOD bounds $\sum\prod_{j<h}\chi(m(n+j))$; an equidistributed walk with anti-correlated consecutive increments satisfies CCSB and violates HOD at $h=2$. Hierarchy Dec $<$ HOD $\to$ CCSB $\Leftrightarrow$ SVE. | — | - |
| 83 | Inverse Littlewood–Offord for products false | 46 | False for $d\ge3$: $\chi$ of order 3, multipliers alternating $\omega,\omega^2$: walk visits $\{1,\omega\}$, $\|S_N\|=N/2$ yet no multiplier lies in $\ker\chi$. The inverse direction is just the contrapositive of CCSB. | — | - |
| 87 | General escape-sum bound fails, $d\ge3$ | 54 | For $d=2$ every escape rotation is $-2$, so the telescoped weighted sum factors; for $d\ge3$ rotations $\chi(m)-1$ take $d-1$ values and $\\|\sum z_nr_n\\|\le2$ does not bound $\\|\sum z_n\\|$: adversarial phase alignment gives $\Theta(N)$. Confirms #36. | — | - |
| 88 | d=2 block-length balance from PED alone | 55 | PED controls total kernel density, not the distribution of kernel steps across blocks; alternating long/short blocks $L_k=\alpha N/K$, $(2-\alpha)N/K$ give alternating sum $\Theta(N)$ with $\Omega(N)$ blocks. Balance $\Leftrightarrow$ translated QR/QNR symmetry $\Leftrightarrow$ localized SieveTransfer. | — | - |
| 107 | Bottleneck Decorrelation axioms insufficient | 79 | Counterexample on $(\mathbb Z/3)^\times$: block-structured multipliers ($N=4K$, escape blocks $m=2$, kernel blocks $m=1$) satisfy all axioms but $F(1)/V(1)=1/3$, $F(2)/V(2)=-1$, no common $\mu$. Per-step CRT is pointwise; VCB needs aggregate joint (position, multiplier) control. | — | - |
| 119 | Substitution Principle false | 140 | Counterexample $q=5$: $N_i=p_ir_i$ with distinct primes $p_i\equiv2$, $r_i\equiv3$ mod 5, $r_i>p_i>2^{2^i}$; minFac distinct, $N_i\equiv1$, coprime, yet the sum is $I\chi(2)=\Theta(I)$; generalizes to all $q\ge3$. SP-for-EM equals CME. | `sp_eq_cme` | - |
| 125 | Pairwise is not $k$-wise (XOR) | 164 | XOR counterexample: unit-modulus $X_1,X_2$ with pairwise cancellation and $X_3=X_1X_2$ give $\sum X_1X_2X_3=N$. Cauchy–Schwarz/Hoelder are trivial, VdC reduces to multiplier CPD, Tao–Teravainen needs multiplicativity; UPE needs $k$-wise for all $k$ as a primitive. | — | 3 |
| 129 | FFLM false: cyclotomic counterexample | 168 | Over $\mathbb{F}_2$, $\mathrm{ffProd}(2)+1 = \Phi_5(t)$ with $\mathrm{Gal} = \mathbb{Z}/4$ (abelian; FF-EM products divide $t^{p^d}-t$, so Galois groups are abelian). Deligne is a family statement (sequential gap = #90), and Frobenius cycle type does not determine $\minFac \bmod Q$. | — | 3 |
| 130 | Generation does not imply coverage | 170 | `ConditionalCharEquidist` $=$ FF-CME $=$ CME definitionally (collapse to #90); and generation is not coverage: steps $\{1,3\}$ generate $\mathbb{Z}/4$ but the alternating walk visits only $\{0,1\}$, so subgroup escape never forces the walk to hit $-1$. | `alternating_walk_misses_two` | 1 |
| 136 | ETA false for death class $c=-1$ | 265 | When $\mathrm{genProd} \equiv -1 \pmod q$, a positive fraction ($\sim C_1/\log q$, Mertens) have $\minFac(\mathrm{genProd}+1) = q$, i.e. $b=0$; mass leaks so $T(-1,b) < 1/(q-1)$ for $b\neq 0$. At $q=3$ the split-off DCTA is provably false (`genSeq_eq_three_of_genProd_mod3`). | — | 2 |
| 137 | AEP false at $q=3$ (absorption) | 266 | At $q=3$ death ($\mathrm{genProd} \equiv 2$) forces $\mathrm{genSeq}=3$, hence $\mathrm{genProd}\equiv 0 \pmod 3$ forever; $F_k(1),F_k(2) \sim C 2^{-k} \to 0$ while $F_k(0)\to 1$. Heuristically false at every fixed $q$ (absorption rate $\sim 1/\log q$ per step); `DeathDensityLB`$(3,c)$ false for all $c>0$. | `death_then_permanent_absorption` | 1 |
| 138 | SRE limit wrong: $r/(r^2-1)$ | 266 | For $\gcd(a,r)=1$ the density is $(1/r)\prod_{p\neq r}(1-p^{-2})/\prod_p(1-p^{-2}) = r/(r^2-1)$; class $0$ has density $1/(r+1) \neq 0$; discrepancy factor $r/(r+1)$ (for $r=3$: $3/8$ vs $1/2$). The stated Prop was a false open hypothesis; limit corrected in code. | — | 1 |
| 140 | Cauchy–Davenport coverage vacuous ($\mathrm{minOrder}=2$) | 234 | For every prime $q\ge 3$, $-1$ has order $2$, so $\mathrm{minOrder}(\mathbb{Z}/q)^\times = 2$ and CD gives only $\|AB\|\ge 2$; the safe-prime hypothesis forces $q=3$; Kneser (not in Mathlib) would still face ordering (#4) and generation$\neq$coverage (#130). | `iterated_product_dead_end_landscape` | 1 |
| 142 | Mod-4 CvdP argument closes only $q=5$ | 298 | For $q=11,13$ the forced smooth sets $5^a7^b11^c(13^d)$ meet the class $3 \bmod 4$ since $7\equiv 11\equiv 3$; on the min side $\minFac N=q$ is an open congruence condition: $N=35$ satisfies all max-side congruence hypotheses, has $\minFac 35=5$, is not a $5$-power. | `min_side_no_smoothness_forcing` | 0 |
| 146 | Zero-configuration (eventually-prime) branch | 299 | Under perpetual primality $P_{n+1}=P_n(P_n+1)$ and the walk mod $q$ is autonomous, $w\mapsto w^2+w$; $w^2+w+1$ has no root in $\mathbb{F}_q$ for $q\equiv 2\pmod 3$, so MC would fail on a density-$1/2$ set. Consumption receptacles are vacuous there ($\omega(P_n+1)-1\equiv 0$); ledgers must be gated on (C$\infty$). | `AutonomousBranch.eventually_prime_implies_not_mullin` | 2 |
| 151 | Confinement cohomology Gap is false | 299 | `free_transition` with `exists_tail_coprime` makes every tail state free, so the box is forward-mobile under the over-approximated `Transition`; $H^0\neq 0$. Restricting to orbit-realizable edges is DSL. Side-finding: `free_transition` is rule-symmetric; the min/max break point is capture (`forcingState_captures`), not fullness. | `CvdP.free_transition` | 0 |
| 156 | Uncentered ensemble character layer false | 307 | Take $\chi\equiv 1$: `ensembleAvg` of $1$ is $1$, so the SD limit is $1$ not $0$; energy $K^2 \not\le CK$; bad density $1$; four-point average $\equiv 1$; $E[E^2]=K^4$. The side conditions ($\chi(0)=0$, $\sum\chi=0$) of `MultCancelToWalkCancel` were never back-ported. Repair: centered per-$\chi$ covariance plus Cesàro drift. | `UncenteredRefutations.not_stepDecorrelation` | 0 |
| 157 | Fixed-step multiplier equidistribution false | 307 | $\mathrm{genSeq} n 0=2$ for every odd $n$ (`genSeq_zero_of_odd`) and at least half the squarefree $n$ are odd, so mass $\ge 1/2$ sits on $2\bmod q$: false for $q\ge 5$. Not a parity artifact: on the family $2p$ the Dirichlet density of $\{\minFac(2p+1)=3\}$ is $1/2$. Independent of absorption. | `UncenteredRefutations.not_ensembleMultiplierEquidist` | 0 |
| 160 | PE/MFRE/RoughLPFEquidist false: head domination | - | The density of $\{\minFac m=p\}$ is $w_p=p^{-1}\prod_{r<p}(1-1/r)$; weights telescope, so the class density is the convergent series $\sum_{p\equiv a}w_p$ (`tendsto_classCount_div`) and RoughLPFEquidist is the identity $\sum_{p\equiv a}w_p=c_q/(q-1)$, on which Dirichlet is silent: the class of the least prime above $q$ receives more than its share (about twice for large $q$; the excess at any fixed $q$ is a finite positive-term computation, deliberately not run in Lean). Same for MFRE/PE, UCE. | `HeadDomination.roughLPFEquidist_iff` | 0 |

### Technique mismatch (TM, 51) — the tool needs structure (independence, multiplicativity, stationarity, algebraic families) that the walk provably lacks
| # | Dead end | S | Why it fails | Witness | Rev |
|---|---|---|---|---|---|
| 4 | Consecutive vs arbitrary subsequences (ordering problem) | 5 | Those theorems concern arbitrary subsequences/subset products or existence of some good ordering; DH needs prefix products of one fixed ordering (the EM walk). Generation/coverage of subsets says nothing about the specific order | — | - |
| 7 | Self-avoidance implies character cancellation | 6 | Distinct primes all $\equiv 1 \pmod q$ give $\chi(m_k)=1$ and $\|\sum P_n\| = N$; self-avoidance is a prime-level property, characters see only residues; no literature exploits step distinctness | — | - |
| 8 | Booker/Burgess techniques for first EM sequence | 9 | Booker's variant allows a choice at each step and sums over all of $\mathbb{F}_q$, not the walk; Burgess needs rapidly growing primes (largest factors); Booker–Simon proves omission for the second EM sequence only | — | - |
| 13 | Additive combinatorics for EM residues | 11 | No additive structure in EM residues; sums not products — wrong structure; Bogolyubov–Ruzsa etc. reduce to the ordering problem | — | - |
| 15 | Cross-prime coupling via minimality | 13 | CRT independence: PED failure at $q_0$ does not constrain residues at $q_1$; minimality constrains size not residue class; multi-modulus sieve gives density-zero not finite exceptional set; all primes $\equiv 1$ mod $q$ is not self-contradictory | — | - |
| 17 | Kernel-run position shift | 13 | Within a run the walk visits at most $(q-1)/d$ positions of one coset and revisits give no contradiction: products of subgroup elements stay in the subgroup | — | - |
| 22 | Order-2 cancellation insufficient for MC | 15 | Order-2 cancellation only separates QR from QNR; hitting $-1$ needs all non-trivial characters in the Fourier inversion, so a proper character subgroup cannot isolate the target | — | - |
| 23 | Furstenberg theorem for circle rotations | 15 | Lyapunov exponent of unimodular scalar products is 0, so Furstenberg-type expansion gives nothing; steps are deterministic and correlated | — | - |
| 24 | CCSB for bounded-order characters | 15 | Not sufficient: hit-count Fourier inversion needs every non-trivial character; low-order cancellation cannot isolate $-1$ | — | - |
| 26 | PED plus self-avoidance (residue vs prime) | 16 | Self-avoidance constrains primes, not residue classes: $p_1 \ne p_2$, $p_1 \equiv p_2$ give identical $\chi$-values, and Dirichlet supplies infinitely many primes per class, so any character-value sequence is compatible with self-avoidance | `dirichlet_residues_independent` | - |
| 27 | StructuredBRE with self-avoidance | 16 | Prime-to-character map is many-to-one; injectivity in the domain says nothing about the image; no version incorporating self-avoidance helps | — | - |
| 29 | Counting/dispersion from self-avoidance | 16 | Same obstruction: Dirichlet provides unlimited primes in every residue class, so counting fresh primes never forces dispersion | — | - |
| 31 | Large sieve for partial products | 17 | Large sieve handles linear sums; the EM sum is a sum of partial products, a structure no large-sieve inequality bounds. Later: `ArithLSImpliesMMCSB` circular (#61), PrimeArithLS mismatch (#75) | — | - |
| 34 | Death-set coupling across moduli | 17 | Death sets vary per step and reset (non-cumulative); no uniform coupling bound exists across moduli | — | - |
| 39 | Linnik's theorem for MC | 19 | Constrains prime existence, not EM factorizations; trivially $4$ is a QR mod $p \ge 5$ so QNR $\le 4$ — proved but irrelevant to walk dynamics | — | - |
| 40 | Qualitative Dirichlet implies NoLongRuns | 19 | Needs density (equal divergence of $\sum 1/p$ per class), not mere infinitude; NoLongRuns requires SieveTransfer. Superseded: sieve-route endpoint GenericLPFEquidist false, SieveTransfer vacuous (#160) | — | - |
| 41 | Elementary route avoiding PNT | 19 | Impossible: NoLongRuns inherently requires quantitative prime distribution; qualitative Dirichlet gives infinitely many primes per class, not proportions; SubgroupEscape does not help kernel runs. #160 later voided the population endpoint | — | - |
| 43 | DWH to sieve-route connection | 20 | DWH is about general walks / subset products, sieve route is EM-specific (minFac); independent paths; consecutive-vs-arbitrary barrier (#4) prevents connection | — | - |
| 44 | Walk telescoping for DWH | 20 | Telescoping identities are EM-specific and only confirm PED alone does not give BRE for $d \ge 3$; nothing transfers to general DWH | — | - |
| 47 | Diaconis–Shahshahani UBL for deterministic walk | 22 | UBL bounds convolutions of probability measures with i.i.d.\ steps; the EM walk is one deterministic path with history-dependent steps. Also $(\mathbb Z/q)^\times$ is abelian, so the non-abelian machinery adds nothing. | — | - |
| 48 | Furstenberg systems of multiplicative functions | 22 | The framework needs a multiplicative function defined on all of $\mathbb Z$; the EM multiplier sequence is recursively defined and not multiplicative, so no Furstenberg system exists for it. | — | - |
| 49 | Non-abelian amplification / representation theory | 22 | $(\mathbb Z/q)^\times$ is cyclic: all irreducible representations are one-dimensional characters, quasirandomness is $1$ (worst case), so there is no $SL_2$-type structure to exploit. | — | - |
| 50 | CRT simultaneous equidistribution across moduli | 22 | Requires independence across moduli; the single integer $\minFac(P(n)+1)$ drives every residue walk simultaneously, so the EM walk couples all moduli and the CRT-independence hypothesis fails. | — | - |
| 51 | Polynomially-defined multiplicative function theory | 22 | $\minFac$ is not multiplicative ($\minFac(210)\ne\minFac(6)\minFac(35)$), and those results only reach moduli up to $(\log x)^K$; wrong function class. | — | - |
| 53 | LSD method for recursive minFac sequences | 22 | LSD handles multiplicative functions through Dirichlet series; the recursive $\minFac(P(n)+1)$ sequence is neither multiplicative nor an $L$-function coefficient sequence, so no analytic continuation input exists. | — | - |
| 55 | PNT in APs formalization blocked | 27 | Zero-free region $\sigma\ge 1-c/\log(q\|t\|)$ absent from the entire Lean 4 ecosystem; needs $\sim$5000+ lines including Hadamard factorization for $L$-functions. Even if available it is a population statement (#90). | — | - |
| 56 | Siegel–Walfisz formalization blocked | 27 | Same blocker as #55 (zero-free region and Siegel's theorem absent from Lean 4); and it yields SieveEquidistribution (population), never orbit-level SieveTransfer. | — | - |
| 57 | Direct Bombieri–Vinogradov formalization | 27 | Estimated 5000–10000 lines (multi-year, Vaughan identity and large sieve absent), and even a formal BV leaves the generic-to-EM transfer `BVImpliesMMCSB` (SieveTransfer) unsolved. | — | - |
| 59 | Davenport-constant zero-sum subset products | 37 | DynamicalHitting needs PREFIX (consecutive) products reaching $-1$, not existence of some zero-sum subsequence; same ordering obstruction as #4. Only marginal information, DH needs joint (position, multiplier) data. | — | - |
| 60 | Kneser sumset growth for prefix products | 37 | Gives weaker bounds than direct arguments and faces the same ordering obstruction (#4) and generation-vs-coverage (#130); Kneser is not in Mathlib (LeanCamCombi only). | — | - |
| 62 | Full ALS by refining WeakALS | 36 | WeakALS treats evaluation points independently; the optimal constant exploits interference (Selberg–Beurling majorants, duality + Hilbert). No smooth interpolation exists between the two arguments. | — | - |
| 63 | KernelRowSumBound from geometric-sum tools | 36 | Insufficient: needs Selberg–Montgomery–Vaughan extremal functions ($\sim$300–500 lines, not in Mathlib); S60 notes sharp KRSB is harder than ALS itself. WeakALS already suffices downstream. | — | - |
| 74 | Mathlib BirkhoffSum / Birkhoff ergodic theorem | 38 | The API assumes an orbit under a single map $T$; the EM walk applies a different multiplier at each step (non-autonomous), so no single transformation, invariant measure or Birkhoff average applies. | — | - |
| 75 | PrimeArithLS to MMCSB structural mismatch | 39 | PrimeArithLS sums over integer indices $\sum_{n\le N}a(n)\chi(n)$; MMCSB needs sums at walk positions $\sum\chi(w(n))$, and $w$ is many-to-one, not invertible in $(\mathbb Z/p)^\times$. Every coefficient choice returns the trivial $N$ bound. | — | - |
| 78 | Partial HOD (even h=2) unprovable | 40 | Requires the joint distribution of consecutive least prime factors $(P^-(n),P^-(n+h))$, an open problem; Tao–Ter\"av\"ainen, Pilatte, Charamaras–Richter cover additive or completely multiplicative functions only, and $P^-$ is neither. | — | - |
| 86 | Nonstationary ergodic theorems (Monakov, Ito–Kawada) | 51 | Requires strictly aperiodic probability measures AND independent steps: for a Dirac mass $\delta_a$, $\|E\chi(X_n)\|=\|\chi(a)\|=1$, so strict aperiodicity fails; and $m(n)$ depends on the whole history. Both conditions fail independently. | — | 2 |
| 89 | Michelen–Sahasrabudhe anti-concentration / PGF zeros | 57 | Anti-concentration is a lower bound on variance, the wrong direction for equidistribution; the PGF $f(z)=N^{-1}\sum z^{L(n)}$ has zeros encoding the trajectory (circular); no factorization without independent steps. Introduces the Four-Way Blocker. | — | - |
| 94 | Fiber uniformity from SE alone | 61 | SE gives eventual coverage, not visit statistics; uniformity needs mixing-time estimates (unavailable for deterministic walks) or joint $(w(n),m(n))$ equidistribution, which is CME. Multipliers $\{2,3\}$ alternating in $(\mathbb Z/5)^\times$ generate yet avoid $-1$ forever. | — | - |
| 95 | Spectral gap for deterministic walks | 62 | Spectral gap constrains frequency of step types, not their ordering: clumped kernel-then-escape steps give walk sum $\Theta(N)$. Spectral theory applies to distributions (random sampling), not a single deterministic path; each EM transition operator is a permutation matrix with unimodular spectrum. | — | 0 |
| 109 | Non-multiplicative Halasz | 81 | No extension exists (2024–2026 searches); pretentious distance is intrinsically Euler-product based and minFac is provably not multiplicative (Four-Way Blocker item 2). Tao–Teravainen correlations stay within the multiplicative world. | — | 0 |
| 111 | Rough-number concentration for $d=2$ | 82 | For any $L$ one builds $L$ pairwise coprime $q$-rough integers of arbitrary size all with QR minFac (distinct QR primes times large coprime cofactors). Only the recursion is EM-specific and using it to control minFac residues is SieveTransfer; coprimality does not imply minFac independence. | — | - |
| 118 | Growth gives no decorrelation | 137 | Residues mod $q$ are periodic regardless of magnitude, so growth is invisible mod $q$; the $+1$ shift is arithmetically entangled; CRT invariance is structural, not statistical. Every dynamical mechanism reduces to sieve content (JSE via CRTPropagationStep). Superseded: variance hypotheses false (#156), DSL vacuous (#160). | — | - |
| 126 | UCE is PE restated in progression language | 165 | At $X \approx M_n$ the counting set is the singleton $\{P(n)+1\}$; density over a singleton is the pointwise MC problem, so `UCEImpliesCME` is the population-to-orbit gap (#90) and $X/M = O(1)$ is outside every sieve asymptotic (#108). Superseded: UCE is false (#160). | — | - |
| 128 | p-adic geometry, diamonds, Hecke orbits inapplicable | 167 | Every geometric equidistribution theorem needs a fixed algebraic correspondence or group action; the EM multiplier is state-dependent, history-dependent and non-algebraic. The FF curve lives at a single prime while the walk is adelic; the slope analogy is a category error. | — | 1 |
| 131 | Dobrushin coefficient equals one | 172 | Each EM transition kernel is a point mass, so $\alpha(K_n)=1$ and $\sum(1-\alpha_n)=0$: Dobrushin's theorem never applies. Batching stays deterministic, windowing is CME again, conditioning reintroduces selection bias; MUB is weaker than CME but vacuous; stopping times repackage DH. | — | 0 |
| 133 | Self-similar functional equation mismatch | 173 | The identity gives $L_{\mathrm{EM}} = \text{head} + L_{\text{from }\prod M}$, but the tail orbit starts at $\prod M \neq 2$ and is a different series, not a scalar multiple of $L_{\mathrm{EM}}$; there are no scaling ratios, so the framework does not apply. | — | 0 |
| 135 | Number field extensions invisible to walk | 179 | Universal Confinement: $\mathbb{Z} \to \mathcal{O}_K/\mathfrak{p}$ factors through the prime subfield $\mathbb{F}_r$, so every character of $(\mathcal{O}_K/\mathfrak{p})^\times$ restricts to a Dirichlet character mod $r$ on the integer walk; Hecke characters add only archimedean growth; inert primes give more characters, not fewer. | — | 1 |
| 141 | Rogue character contradicts no known bound | 283 | No standard bound applies to $\sum_{n<N}\chi(\prod n \bmod q)$: Pólya–Vinogradov (not consecutive integers), Burgess (no interval), Halász (not multiplicative in $n$), large sieve (averages over $\chi$), Shiu (consecutive primes in one class exist), CRT (moduli independent); a walk-specific bound is CCSB itself. | `perpetual_avoidance_rogue` | 0 |
| 144 | Reciprocity transfer to min sequence fails | 298 | Max proofs make a real character constant on the finite factor support of the Euclid number; $\minFac$ confines it to a cofinite set, where no nontrivial character is constant (`char_non_constancy`). The invariant is congruential at $\Pi_n=8mP_n$: eviction automatic, fullness at $\Pi_n$, fragment empty. | `Reciprocity.no_reciprocity_induction_proof` | 0 |
| 147 | Avoidance does not force factor-set diversity | 299 | (F1) `meanCharValue` contracts by averaging over a factor set while the walk selects one factor with $\\|\chi(s)\\|=1$; (F2) the chain concludes some branch reaches $-1$, avoidance constrains one branch; (F3) `productMultiset` fixes factor sets in advance, real ones are path-dependent. | `diverse_steps_imply_vanishing` | 1 |
| 152 | Support-invisibility of algebraic invariants | 299 | Missingness is a support condition on $\sum_p e_p$, but every computable algebraic invariant factors through $p\mapsto p \bmod m$, hence through the walk, which sees only the product. | — | 0 |

### Scale mismatch (SM, 12) — the error term of the tool exceeds the signal on an $O(\log x)$-term or exponentially sparse orbit
| # | Dead end | S | Why it fails | Witness | Rev |
|---|---|---|---|---|---|
| 11 | BlockDecorrelation for high-order characters | 11 | Works for low-order characters but fails for order $d \sim q-1$: block bound does not scale with the character order | — | - |
| 28 | Abel summation for walk sums | 16 | Linear weights amplify contributions: yields $O(N^2)$ not $o(N)$, strictly worse than trivial | — | - |
| 33 | CRT product-group reformulation | 17 | Makes the problem harder: the product group is exponentially large; no gain over single modulus. Later #101 (profinite adds nothing) | — | - |
| 38 | Dec to CCSB via Abel/VdC $h=1$ | 18 | Product-to-sum conversion fails; VdC with $H=1$ gives $\|S_N\|^2 \le N^2/2 + o(N^2)$, i.e. $\|S_N\| \le N/\sqrt2$, a constant fraction not $o(N)$; $h \ge 2$ needs HOD | — | - |
| 77 | Dec plus VdC insufficient for CCSB | 40 | VdC at $H=1$ gives $\\|S_{\mathrm{walk}}\\|\le N/\sqrt2$, a constant fraction of the trivial bound, not $o(N)$; $o(N)$ needs autocorrelation control for all lags $h\le H$ with $H\to\infty$. | — | - |
| 80 | Order-2 CCSB from PED plus NoLongRuns | 41 | $\|S\|\le(\text{number of pairs})\times L=O(N)$, not $o(N)$; adversarial block lengths $L_1=2,L_2=0,L_3=2,\dots$ give alternating sum $N$ with $\Omega(N)$ blocks. Alternation alone forces no cancellation below $O(N)$. | — | - |
| 91 | Prime Euclid density argument | 59 | Under doubly-exponential growth ($\log P_n \asymp 2^n$, the perpetual-primality branch) $\sum 1/\log P_n$ converges and prime Euclid numbers are heuristically finitely many; on the branch MC predicts ($\log P_n \asymp p_n$) the heuristic count diverges (paper \S4.1). Either way they contribute $o(N)$ and say nothing about the composite population, which is the irreducible content. | — | - |
| 96 | Level-of-distribution scale mismatch | 63 | LoD error $(\mathrm{prod} N)^\theta/(\log\mathrm{prod} N)^A\ge 2^{\theta N}$ grows exponentially while MMCSB needs $\varepsilon N$; `LoDImpliesMMCSB` is false. Any walk-adapted LoD reduces to CCSB (walk sums) or Dec (multiplier sums); no intermediate. | `prod_superlinear` | 0 |
| 102 | Large sieve single-frequency extraction | 72 | With one evaluation point the separation condition is vacuous, giving the trivial $\|S_N\|\le N$; embedding $\alpha=0$ in $R+1$ points gives $\|S(0)\|^2\le N^2(R+1)$, worse than trivial. Large sieve averages over frequencies; it cannot extract pointwise information on one walk. | — | - |
| 108 | Harper BDH / Weil scale mismatch | 81 | BDH needs well-distribution in APs (circular for EM) and non-concentration; EM products are super-exponentially sparse, and it yields variance over most $q$, not pointwise. Weil error $O(p^{n/2})$ per degree is vacuous for an orbit at a single degree per step. | — | 1 |
| 154 | LSD/Wirsing density along the orbit | 299 | No exponentially-sparse LSD theorem exists; the orbit contributes $O(\log x)$ terms below $x$, far under every LSD error term (Wirsing 1961, Tenenbaum II.5, Serre 1976 checked: nothing for sparse sequences). | — | 1 |
| 155 | Nonstandard / ultraproduct receptacle | 299 | Detection is honest (Łoś transfers avoidance) but the Loeb measure of the hyperfinite orbit is $0$ for every sequence, avoiding or not; a conservative extension yields no new Gap by definition. | — | 0 |

### Methodological rules (MR, 3) — not mathematical obstructions but standing rules of the project (no numerical certificates, no instance-by-instance work), numbered in the earliest sessions
| # | Dead end | S | Why it fails | Witness | Rev |
|---|---|---|---|---|---|
| 1 | Computing concrete sequence values | 1 | Methodological rule: concrete values prove nothing about all primes $q$; breaks the build, contributes nothing (Guiding Principle). Closest code OS: finite data says nothing about the whole orbit | — | - |
| 2 | Raising ThresholdHitting by computation | 1 | Checking individual primes does not prove the conjecture; $T=11$ is the proved reduction (`threshold_11_implies_mullin'`) and no finite $T$ closes MC | — | - |
| 3 | Brute-force SubgroupEscape instances | 1 | SE is already proved globally via PRE $\Rightarrow$ SE; instance-by-instance work is redundant with the global theorem | — | - |

<!-- END GENERATED CATALOGUE -->

## Run S-Receptacle (Session 299): entries #146–#155

Ten entries added in one sweep.  Each was tested against the *Detection / Gap* template:
a receptacle must both **detect** the avoidance hypothesis and produce a **gap**
(a quantity the avoiding orbit cannot pay).  Most receptacles fail on the Gap side.

- **#146 (SF) — the zero-configuration branch.**  On the branch where `Pₙ + 1` is prime for
  all large `n`, the walk modulo `q` becomes *autonomous*: `w ↦ w² + w`.  Since `w² + w + 1`
  has no root in `𝔽_q` when `q ≡ 2 mod 3`, MC would fail on a density-`1/2` set of primes.
  Every consumption receptacle is *vacuous* on this branch, because `ω(Pₙ + 1) − 1 ≡ 0`:
  the orbit spends nothing, so Detection and Gap fail together.  All ledger-style arguments
  therefore gate on **(C∞)**: infinitely many `Pₙ + 1` are composite.
- **#147 (TM) — avoidance ⇏ factor-set diversity.**  The contrapositive of the diversity
  chain is unavailable for three independent reasons.  (F1) `meanCharValue` contracts by
  *averaging* over a factor set, whereas the walk *selects* one factor and `‖χ(s)‖ = 1`
  pointwise.  (F2) The conclusion of the chain is that *some* branch reaches `−1`, while
  avoidance constrains *one* branch.  (F3) `productMultiset` is assembled from factor sets
  fixed in advance; the real factor sets are path-dependent.
- **#148 (OS) — the consumption ledger is one-sided.**  It yields caps only
  (`hittingSet_ncard_le_appearing`, starvation).  A contradiction needs a *lower* bound on
  spending, which requires orbit control — exactly what the consumption discipline forbids.
- **#149 (CO) — ledger small-prime output is weaker than injectivity.**  The ledger gives
  `Σ_{p ≤ y} h_∞(p) ≤ π(y)²`, strictly weaker than the injectivity bound `π(y)`, because
  "∃ p ≤ y with p ∣ Nₙ" ⟺ "minFac Nₙ ≤ y".  This is the roughness trap, quantified.
- **#150 (CO) — covering systems.**  Covering systems are finite by definition, and
  `no_finite_prime_covering` kills fixed-finite-prime-set covering outright;
  `no_cvdp_obstruction` is set-generic, so lcm-composition of moduli is already covered.
- **#151 (SF) — confinement cohomology.**  `free_transition` together with
  `exists_tail_coprime` makes every tail state free, so the Fact-4 confinement box is
  forward-mobile under the (over-approximated) `Transition`; `H⁰` of the avoidance
  subcomplex is nonzero, i.e. the Gap is false.  Restricting to orbit-realizable edges
  is DSL.
- **#152 (TM) — support-invisibility.**  Missingness is a *support* condition on `Σ_p e_p`,
  but every computable algebraic invariant factors through `p ↦ p mod m`, hence through the
  walk, which sees only the product.
- **#153 (AG) — Iwasawa / Euler systems.**  Kolyvagin derivatives need classes over the full
  squarefree *lattice*; the EM orbit supplies a single maximal *flag* `P₀ ∣ P₁ ∣ …`.  There
  is no ℤ_p-tower (layer degrees are not p-powers), no motive, and no period formula.
- **#154 (SM) — LSD/Wirsing density along the orbit.**  No exponentially-sparse
  Landau–Selberg–Delange theorem exists; the orbit contributes `O(log x)` terms below `x`,
  far under every LSD error term.
- **#155 (SM) — nonstandard / ultraproduct receptacle.**  Detection is honest: Łoś transfers
  the avoidance statement to the hyperfinite orbit.  The Gap is vacuous: the Loeb measure of
  the hyperfinite orbit is `0` for *every* sequence, avoiding or not, and a conservative
  extension yields no new Gap by definition.

**New facet of the Four-Way Blocker.**  Entry #146 is not a fourth copy of the existing
facets: the obstruction there is **anatomy** (compositeness and smoothness of `Pₙ + 1`),
which is invisible to congruences.  Any ledger or consumption argument must therefore be
stated conditionally on (C∞).

**Min/max dichotomy correction.**  The true break point between the min and max rules is the
capture condition (`forcingState_captures`), *not* Free-state Fullness: `free_transition` is
rule-symmetric.  Corrected in `Reduction/NoInvariant.lean` this session; see #151, whose
witness is exactly that rule-symmetric step.

## Run T-MC-Proper (Session 307): entries #156–#159

Four entries added while auditing the catalogue against **MC proper** (no variants).
The first three come from the route-4 audit (`tmp/route4_assessment_2026-08-15.md`),
re-verified against the definitions on disk this session; the fourth records the
verdict on the ε-interpolation programme.

- **#156 (SF) — the uncentered ensemble character layer is false at the trivial
  character.**  `StepDecorrelation` (`Ensemble/Decorrelation.lean`) quantifies over
  *all* `χ : ℕ → ℂ` with no side condition whatsoever ("nontrivial" appears only in a
  comment).  Taking `χ ≡ 1` gives `ensembleAvg X (fun _ => 1) = 1`, so the asserted
  limit is `1`, not `0`.  The same instantiation falsifies `CharSumVarianceBound C`
  (energy `K² ≰ C·K`), `EnsembleCharSumConcentration` (bad density `1` for `ε < 1`),
  `FourPointPCV` (four-point average `≡ 1`), and `SecondMomentSquaredBound D`
  (`E[E²] = K⁴ ≰ D·K²`).  Note `χ ≡ 1` *does* satisfy the `normSq ≤ 1` hypothesis
  those Props carry, so the refutations are immediate.  The repo already knows the
  correct side conditions — `MultCancelToWalkCancel`, sitting a few lines above
  `StepDecorrelation` in the same file, carries `χ 0 = 0`, `∑_a χ a = 0`,
  `normSq (χ a) ≤ 1` — they were simply never back-ported to the SD/PCV layer.
  Consequence: five entries the registry advertises as `@[open_point]` are
  unsatisfiable, so any campaign to "prove SD" attacks a false statement.
  **Repair, not abandonment**: the centered per-χ forms (covariance
  `E[χ(m_j)χ̄(m_k)] − E[χ(m_j)]E[χ̄(m_k)] → 0` plus a drift condition
  `c_{χ,k} → 0` in Cesàro form) still yield `E[|S_K|²] = o(K²)`.
- **#157 (SF) — fixed-step ensemble multiplier equidistribution is false:
  small-prime domination.**  `genSeq n 0 = minFac (n+1)`, and `genSeq_zero_of_odd`
  (`Ensemble/FirstMoment.lean`) gives `genSeq n 0 = 2` for every odd `n`, while
  `odd_sf_card_ge_half` gives at least half the squarefree `n ≤ X` odd.  So the
  `k = 0` multiplier ensemble puts mass `≥ 1/2` on the single class `2 mod q`,
  refuting `EnsembleMultiplierEquidist` (`Ensemble/CRT.lean`, asserted limit
  `1/(q−1)`) for every `q ≥ 5` from lemmas already proved; the sharper odd-squarefree
  density `2/3` also kills `q = 3`.  `JointStepEquidist` (`Ensemble/PT.lean`, limit
  `1/(q−1)²`) falls the same way at `(j,k) = (0,1)`.  This defect is **independent**
  of the absorption trap of #136–#138: absorption drains accumulator classes,
  small-prime domination biases multiplier classes at every fixed `k`.  The
  reciprocal-sum chain was already corrected for exactly this mechanism
  (`K0LowerBound` section, `FirstMomentStep` flagged "likely false"); the
  correction was never propagated to the equidistribution layer.
  **Not merely a parity artifact (Session 307).**  One might hope the defect
  disappears once the ensemble is restricted to the correct parity, since the real
  Euclid–Mullin accumulator is always even and its candidates always odd.  It does
  not.  On the smallest correct-parity family — starting points `2p`, `p` prime,
  `ω = 2` — `Ensemble/MinFacShifted.lean` proves the Dirichlet density of
  `{p : minFac (2p+1) = 3}` is **exactly `1/2`**
  (`tendsto_minFacThree_density`), so equidistribution fails again, now by
  small-prime domination rather than parity, with an explicit constant
  (`first_multiplier_not_equidistributed`, for every prime modulus `Q ≥ 5`).
  Half of that ensemble is moreover *absorbed mod 3 at the first step*
  (`minFacThree_absorbed`) — Dead End #137's mechanism with a density attached.
  The refutation of #157 as literally stated (over all squarefree `n`) is still
  documented-not-witnessed; what is now proved is the correct-parity analogue.
- **#158 (OS) — the tail-identity Borel–Cantelli step is #90 in a new coat.**
  The tail identity (`genSeqCharEnergy (prod M) K` = tail energy of the standard
  orbit, PROVED) is genuine: `prod M` is a legitimate ensemble member.  But
  `FourPointPCVImpliesDSL`'s roadmap transfers a density-`O(1/K²)` bad-set bound to
  the *specific* points `prod M`, and `standard_tail_not_bad` in the same file needs
  the bad set to have `card = 0`, not density `→ 0`.  A density-zero bad set may
  contain the sparse sequence `{prod M}` at no cost.  The identity converts "orbit
  statement" into "ensemble-member statement", but the specificity reappears as
  *which* ensemble members are good.  Same shape kills routing the exit through
  `MultCancelToWalkCancel` (≡ CME; #58/#117).
- **#159 (CO) — the ε-interpolation family is a reformulation, not a relaxation.**
  `mullin_iff_exists_failWeight_bound` (`Stochastic/EpsilonDegeneration.lean`):
  for `q ≠ 2`, `∃ n, seq n = q` **iff** there are `ε, N, c` with `N·ε < c` and
  `failWeight ε q 2 N ≤ 1 − c`.  Together with `horizon_ge_of_minFacAvoids`
  (outside the window `N < c/ε` no such bound exists unless MC already holds at `q`)
  and `failWeight_ge_of_mullin_fails` (a.s. capture at every fixed `ε > 0` does NOT
  imply MC), this is the verdict on the whole noisy-interpolation programme: the
  ε-family relocates MC into a finite window rather than weakening it.  Listed as CO
  because it is a definitional collapse *onto* MC — but unlike the other CO entries
  it is a usable handle: it reduces MC at `q` to a **finite-horizon, quantitative**
  capture certificate.
- **#160 (SF) — the population hypotheses PE / MFRE / RoughLPFEquidist are false: head
  domination.**  `Population/HeadDomination.lean`.  For a prime `p` the density of
  `{m : minFac m = p}` is `w_p = (1/p)∏_{r<p}(1 − 1/r)`, and the weights telescope
  (`w_eq_cfun_sub`), so the density of the class `minFac ≡ a (mod q)` among `q`-rough
  integers is the **convergent** series `∑_{p ≡ a} w_p` (`tendsto_classCount_div`).  Hence
  `RoughLPFEquidist q ⟺ ∀ a, ∑_{p ≡ a} w_p = c_q/(q−1)` (`roughLPFEquidist_iff`), and — since
  Karamata made its hypothesis a theorem — the open point `PrimesEquidistAsympImpliesRoughLPF`
  IS that family of identities (`primesEquidistAsympImpliesRoughLPF_iff`).  Dirichlet's
  theorem is silent about them: the series is dominated by the first primes above `q`, the
  class of the least prime `p₀ > q` receives about twice its share unless the primes
  `≡ p₀` are systematically deficient thereafter, and they are not.  The informal derivation
  ("size-dependent weights are equidistributed by Dirichlet") mistook a statement about
  divergent counting functions for one about a convergent weighted sum; #137/#157 recorded
  the same mechanism one step earlier.  Consequences: `MinFacResidueEquidist` and
  `PopulationEquidist` fail the same way (sieve weights `g(r) = r/(r²−1)`);
  `DeterministicStabilityLemma := PE → CME`, `DSLHitting`, `PopulationTransfer` are vacuous;
  `full_chain_dsl`, `wpnt_dsl_implies_mc`, `alladi_dsl_implies_mc`, `dsl_closes_all` have a
  false premise; the "PE ⇒ CME" decomposition of the master gap is void and the honest headline
  is `CME ⇒ MC` with CME open.  Also `UniformConductorEquidist` (its `M = 1` clause is `RoughLPFEquidist`:
  `uce_implies_roughLPFEquidist`), so `UCEImpliesCME` is vacuous too; and
  `GenericLPFEquidist` ("Alladi's theorem", `Equidist/SieveTransfer.lean`), refuted by pure
  argument — `minFac n ≡ 1 (mod 3)` forces `n` coprime to 6, density ≤ 1/3 < 1/2
  (`not_genericLPFEquidist`) — so the open point `SieveTransfer` is vacuous
  (`sieveTransfer_vacuous`); and `MFREConditional` (`Ensemble/CRT.lean`, uniform `O(1/q²)`
  error, broken by the mass on `2 mod q`), with `EnsembleSelectionLemma`,
  `MSIImpliesMFREConditional` archived.  The Alladi attribution misread the Möbius-weighted
  duality theorem as unweighted equidistribution of the least prime factor.  The whole layer is
  archived (`EM/Archive/Population/PopulationEquidistArchive.lean`, `AlladiDensityArchive`,
  `Reduction/DSLVarianceArchive`, `Adelic/UniformConductorArchive`, `Meta/MarkovSieveArchive`,
  `Ensemble/TwoPointEnsembleArchive`; RED #11–#13 in `EM/Archive/README.md`).  Witness of the
  *reduction* (the equivalence) is formal; the finite head certificate at a specific `q` is
  deliberately not run (`not_roughLPFEquidist_of_head` is the criterion).  Same shape as
  #156–#157: false, not hard; score 0.

## MC-proper ledger (Session 307; #160 added 2026-08-17)

The revival scores above are a **weak-MC** axis and say nothing about MC proper.
For MC itself, the ledger is: every sufficient hypothesis in the reduction
network (`Reduction/Master.lean`) is an *orbit* statement, and #90 is the single
wall in front of all of them.

| Route to MC | Sufficient hypothesis | Killed / constrained by |
|-------------|-----------------------|--------------------------|
| Hitting | `DynamicalHitting`, `DSLHitting` | #20, #130 (generation ⇏ coverage), #145 |
| Character sums | `ComplexCharSumBound`, `MultiModularCSB` | #58, #81, #93, #106, #115, #117 |
| Conditional equidist | `CME` (= `SubstitutionPrinciple` = `OrbitConditionalEquidist`, `rfl`) | #90, #110, #121, #125 |
| Visit energy | `SVE` / `VisitEquidistribution` / `SelfCorrectingDrift` | #120 (SCD ≡ SVE, no new leverage) |
| Population transfer | `DSL` (PE → CME), `CRTPointwiseTransferBridge`, `UCEImpliesCME` | #90 (the wall itself), #127; **#160: PE false ⇒ DSL vacuous; UCE false (M = 1 clause is RoughLPFEquidist) ⇒ UCEImpliesCME vacuous** |
| Ensemble variance | `StepDecorrelation`, `FourPointPCV` → DSL | #156, #157 (false as stated), #158 (transfer walled) |
| Analytic / L-function | `L_EM` factorization, Tauberian | #132, #133, #134 |
| ANT entry (Alladi) | `PrimesEquidistAsympImpliesRoughLPF`, `RoughLPFImpliesMFRE` | #160 (endpoints MFRE/RoughLPFEquidist false; entry `WeightedPNTinAPAsymp` is a theorem) |
| Algebraic obstruction | congruence / reciprocity certificates | #143 (≡ MC), #150, #151, #152 |
| Geometric / p-adic | diamonds, Iwasawa, Euler systems | #128, #153 |
| Stochastic perturbation | ε-noised rule | #159 (faithful reformulation) |

**Two consequences for how the catalogue should be read.**

1. **The two fundamental entries are the two that are NOT machine-checked.**
   #90 and #117 carry the whole "why MC is hard" thesis and both have `—` in the
   witness column; everything with a formal witness is a peripheral entry.  Both
   admit cheap concrete witnesses:
   - #117: multipliers alternating `2, 3` in `(ZMod 5)ˣ` with `χ(2) = i` give
     `χ(3) = i³ = −i`, so multiplier partial sums are bounded (`O(1)`), while the
     walk positions alternate `1, 2` and `|W_K| = Θ(K)`.  A finite `decide`-scale
     statement on `(ZMod 5)ˣ`.
   - #90: two multiplier sequences with the **same** empirical distribution and
     different hitting behaviour — period `(2,2,3,3)` in `(ZMod 5)ˣ` gives walk
     `1, 2, 4, …` (hits `−1 = 4`), period `(2,3,2,3)` gives walk `1, 2, 1, 2, …`
     (never hits `4`), and both have marginal `1/2` on `2` and `1/2` on `3`.
     This is exactly "population statistics do not determine orbit hitting".
   The integer setting has no assembly theorem analogous to
   `FunctionField/OrbitBarrier.lean`'s `orbit_barrier_thesis`; building one is the
   natural home for these witnesses.
2. **The catalogue currently over-reports coverage of the anatomy axis.**  #146
   introduced *anatomy* (compositeness and smoothness of `Pₙ + 1`) as a fourth facet
   of the Four-Way Blocker, invisible to congruences.  No entry yet tests a technique
   that works *on* anatomy — every ledger-style argument is instead gated on (C∞)
   (infinitely many `Pₙ + 1` composite).  Conditional-on-anatomy statements about MC
   proper are the least-mapped region of the catalogue, not an exhausted one.

## Numbering aliases (do NOT add these twice)

Some session notes predate the current numbering. The tables above are the ground truth;
the following historical labels are aliases of rows already present:

- Session 180 "Dead End #136" (Universal Confinement Theorem: for any number field K/ℚ and
  prime 𝔭 the integer walk is confined to 𝔽_r ⊂ 𝒪_K/𝔭, killing all ring-of-integers
  approaches) is the same barrier as catalog **#135** (number field extensions invisible).
- Session 234 "Dead End #137" (Cauchy-Davenport coverage vacuous, `minOrder (ZMod q)ˣ = 2`)
  collided with #137 above; it is catalogued here as **#140**. The historical label "#137"
  was used for it in the Session 234 notes and in the comments of
  `Advanced/IteratedProductCoverage.lean`; those in-file comments were normalized to "#140"
  on 2026-08-12, so a log reference to "Cauchy-Davenport #137" means #140.
- The historical label "#138" was used for the AEP falsity in the comments of
  `Ensemble/CRT.lean` and of the Archive files (`Archive/Ensemble/CRTArchive`,
  `Archive/Ensemble/CRTFreedomArchive`, `Archive/Ensemble/BackwardDynamicsArchive`,
  `Archive/Ensemble/PTArchive`, `Archive/Advanced/EpsilonWalkArchive`, `Archive/README.md`),
  written before the Session 266 renumbering gave #138 to the SRE limit bug. The AEP falsity
  is catalogued here as **#137**; those in-file comments were normalized to "#137" on
  2026-08-12, so a log reference to "AEP #138" means #137.
- No dead end was ever assigned the label "#140" in the session logs; it is used here for
  the Cauchy-Davenport entry, which had no free number of its own.

## Revival Summary

**Tier A — Revives substantially (score 3)**
- #90 via ensemble averaging (AlmostAllRSD route)
- #125 via pairwise-only variance (second moment suffices)
- #129 via abelian Galois = Dirichlet (FF weak MC)

**Tier B — Medium revival (score 2)**
- #86 via ensemble quasi-randomness
- #106 via pigeonhole density of good fibers
- #120 via Lyapunov one-sided drift (upper_drift_bound_implies_mc)
- #121 via per-class certificate for positive density
- #127 via FF population + finite pool
- #136 via the corrected ETA hypothesis (death class c = -1 excluded)
- #146 via weak MC on the density-1/2 set q ≡ 1 mod 3 (the autonomous map has a fixed point)

**Tier C — Marginal (score 1)**
- #20, #108, #128, #130, #132, #134, #135, #137, #138, #140, #145, #147, #148, #154, GaussOS

**Tier D — Stays dead (score 0)**
- #58, #81, #93, #95, #96, #101, #109, #110, #115, #116, #117, #131, #133, #139, #141,
  #142, #143, #144, #149, #150, #151, #152, #153, #155, #156, #157, #158, #159, #160

(#156–#158 score 0 as *statements*: they are false, not hard.  Their repaired
forms — centered per-χ covariance plus Cesàro drift vanishing — are live ensemble
targets, but their endpoint is ensemble-level and walled from MC by #158.)
-/

noncomputable section
open Classical Mullin Euclid MullinGroup RotorRouter
open scoped BigOperators

/-! ## Formal witnesses: existence checks (silent `example := @name`, formerly `#check`) -/

-- Dead End #20: generation ≠ coverage (Z/4Z counterexample)
-- Walk with steps {1,3} generates Z/4Z but only visits {0,1}
example := @alternating_walk_misses_two   -- ∀ n, additiveWalk4 n ≠ 2
example := @alternating_walk_misses_three -- ∀ n, additiveWalk4 n ≠ 3

-- Dead End #95: spectral gap inapplicable to deterministic walks
example := @spectral_gap_inapplicable    -- SpectralGapInapplicable

-- Dead End #110: Doeblin/sieve add nothing beyond CME/CCSB
example := @no_new_leverage              -- conjunction: all routes collapse

-- Dead End #121: per-class bad set escape
example := @smsb_se_collapse_certificate -- Dead End certificate
example := @marginal_joint_barrier_witness -- pigeonhole gives one good class

-- Dead End #129: FFLM structurally false (cyclotomic counterexample)
example := @FunctionFieldAnalog.ff_cyclotomic_dead_end  -- (p : ℕ) → landscape

-- Dead End #130: selection bias (SE ⇏ DH)
example := @FunctionFieldAnalog.selection_bias_dead_end_analysis  -- (p : ℕ) → 4-clause

-- Dead End #131: Dobrushin coefficient = 1, MUB ≠ CME
example := @dobrushin_coefficient_one    -- trivially 1 for deterministic walks
example := @dobrushin_inapplicable       -- framework mismatch
example := @dead_end_131_witness         -- full conjunction

-- Dead End #132: L-function factorization circular
example := @dead_end_132_witness

-- Dead End #133: self-similar functional equation mismatch
example := @dead_end_133_witness

-- Dead End #134: no Tauberian lever for L_EM
example := @tauberian_lever_absent_witness

-- Dead End #135: number field extensions invisible to walk
example := @GaussEM.dead_end_135_certificate

-- Gaussian EM: orbit specificity barrier
example := @GaussEM.gauss_orbit_specificity_barrier

-- Dead End #146: zero-configuration branch (eventually prime ⇒ MC fails for q ≡ 2 mod 3)
example := @AutonomousBranch.eventually_prime_implies_not_mullin

-- Dead End #147: avoidance ⇏ factor-set diversity (averaging vs selection)
example := @diverse_steps_imply_vanishing

-- Dead End #148: the consumption ledger is one-sided (caps only)
example := @hittingSet_ncard_le
example := @hittingSet_ncard_le_appearing  -- the sharpened cap; still one-sided

-- Dead End #149: ledger small-prime output π(y)² is weaker than injectivity π(y)
example := @seq_injective

-- Dead End #150: covering-system / multi-modulus congruence obstructions
example := @CvdP.no_covering_family_obstruction
example := @CvdP.no_finite_prime_covering

-- Dead End #151: confinement-cohomology Gap is false (free tails ⇒ H⁰ ≠ 0)
-- `free_transition` is rule-symmetric: it is NOT the min/max break point.
example := @CvdP.free_transition

-- Dead ends #137, #140, #141, #142 have Lean witnesses in files this module does not import
-- (`Ensemble/CRT`, `Advanced/IteratedProductCoverage`, `Population/AvoidanceTube`,
-- `Advanced/MaxVariant`).
-- The witness names are recorded in the tables above; no `#check` re-export here, to keep
-- the registry's import surface minimal:
--   #137: `death_then_permanent_absorption` (+ `absorbed_not_in_death_class`)
--   #140: `iterated_product_dead_end_landscape`
--   #141: `perpetual_avoidance_rogue`
--   #142: `min_side_no_smoothness_forcing` (+ `cvdp_selection_rule_asymmetry`)

-- Dead End #143: congruence-certificate hypotheses collapse to MC
example := @CvdP.ic_min_network

-- Dead End #145: simultaneous avoidance decouples (Finite Hitting is real)
example := @CvdP.hittingSet_finite
example := @CvdP.hittingSet_ncard_le

-- Dead End #90: population statistics do not determine orbit hitting.
-- Two multiplier sequences that are rearrangements of one another (identical empirical
-- distribution in every window of four steps), one of whose walks hits the death class
-- -1 = 4 in (ZMod 5)ˣ while the other provably never does.
example := @OrbitBarrier.population_does_not_determine_hitting

-- Dead End #117: multiplier cancellation does not force walk cancellation.
-- Multipliers alternating 2, 3 mod 5 with χ(2) = i: multiplier sums bounded by 1,
-- walk sums ≥ M after 2M steps.  χ carries the exact side conditions of
-- `MultCancelToWalkCancel` (normSq ≤ 1, χ 0 = 0, orthogonality).
example := @OrbitBarrier.mult_cancel_not_walk_cancel

-- The assembly: the integer analogue of `FunctionFieldAnalog.orbit_barrier_thesis`.
example := @OrbitBarrier.integer_orbit_barrier_thesis

-- Dead End #159: the ε-interpolation family is a faithful reformulation of MC
example := @mullin_iff_exists_failWeight_bound  -- MC at q ↔ ∃ (ε, N, c), N·ε < c, bound
example := @horizon_ge_of_minFacAvoids          -- sharpness: no bound outside N < c/ε
example := @failWeight_ge_of_mullin_fails       -- a.s. capture ∀ε > 0 does NOT give MC

-- Dead End #160: PE / MFRE / RoughLPFEquidist are false (head domination).  The witness
-- is the exact characterization: the class density is the convergent series of the
-- telescoping weights, and the open point is that series identity.
example := @HeadDomination.w_eq_cfun_sub                        -- w p = cfun p − cfun (p+1)
example := @HeadDomination.tendsto_classCount_div               -- class density = ∑_{p ≡ a} w p
example := @HeadDomination.roughLPFEquidist_iff                 -- RoughLPFEquidist ⟺ series identity
example := @HeadDomination.primesEquidistAsympImpliesRoughLPF_iff -- the open point IS the identity
example := @HeadDomination.not_roughLPFEquidist_of_head         -- finite-head criterion
example := @uce_implies_roughLPFEquidist                        -- UCE (M = 1) is RoughLPFEquidist
example := @not_genericLPFEquidist                              -- GenericLPFEquidist is FALSE (pure argument)
example := @sieveTransfer_vacuous                               -- hence SieveTransfer is vacuous

-- Dead ends #156, #157 WITNESSED 2026-08-17 (EM/Ensemble/UncenteredRefutations.lean):
example := @UncenteredRefutations.not_stepDecorrelation
example := @UncenteredRefutations.not_fourPointPCV
example := @UncenteredRefutations.not_tailWindowDecorrelation
example := @UncenteredRefutations.not_charSumVarianceBound
example := @UncenteredRefutations.not_ensembleCharSumConcentration
example := @UncenteredRefutations.not_secondMomentSquaredBound
example := @UncenteredRefutations.not_ensembleMultiplierEquidist
example := @UncenteredRefutations.twdImpliesCCSB_vacuous
-- Dead end #158 remains documented-not-witnessed:
--   #158: `standard_tail_not_bad` needs card = 0, density → 0 is not enough
-- Dead end #144 (reciprocity transfer to the min sequence): witnessed since Session 307 by
-- `no_reciprocity_induction_proof` (`EM/Reciprocity/NoReciprocityInvariant.lean`, a real
-- `IsEmpty` proof, not a marker); first slice `char_non_constancy` (Session 300).
example := @Reciprocity.no_reciprocity_induction_proof

/-! ## Revival chains (proved in other files) -/

-- Revival of #90: ensemble route bypasses orbit specificity
-- AlmostAllSquarefreeRSD targets density-1 of starting points
example := @concentration_implies_rsd     -- RecipSumConcentration → AlmostAllRSD

-- Revival of #120: Lyapunov one-sided drift
-- Only the upper bound R(N) ≤ CN is needed; lower bound is free
example := @upper_drift_bound_implies_mc  -- one-sided upper → MC
example := @cumulativeDrift_lower_bound   -- FREE lower bound (unconditional)

-- Revival of #125: pairwise suffices for variance
-- Dead End #125 killed k-wise, but RSD only needs k=2
-- dead_end_125_pairwise_revival archived to EM/Archive/Population/ReciprocalSumArchive.lean (RED #8)
example := @chebyshev_concentration_proved -- ChebyshevConcentration PROVED (unconditional bridge)

-- Revival of #129: abelian Galois = good news for Dirichlet equidistribution
-- (FF weak MC attack — see FunctionField/WeakMC.lean when available)

/-! ## Aggregate statistics -/

/-- Highest catalogued dead-end number.  Numbers are assigned progressively in the session logs
and cited everywhere by number, so they are never renumbered.  Ten of the 160 numbers (#25,
#64–#72) were never assigned to any entry (2026-08-18 reconstruction, `tools/dead_ends.tsv`);
`deadEndEntryCount` is the number of actual entries. -/
def deadEndCount : ℕ := 160

/-- Number of catalogued dead-end entries: the 160 numbers minus the ten never assigned. -/
def deadEndEntryCount : ℕ := 150

/-- Entries with a genuine (non-placeholder) formal Lean witness, counted from
`tools/dead_ends.tsv` by `tools/gen_dead_ends.py`.

History: 24 on 2026-08-17 (after the placeholder audit reclassified #129, #131–#135 as
documented-not-witnessed and #156/#157 became witnessed).  The 2026-08-18 reconstruction of the
full catalogue found genuine witnesses for entries the old tables did not carry — #26
(`dirichlet_residues_independent`), #58 (via #117's counterexample), #93 (`cme_implies_feb`),
#96 (`prod_superlinear`), #110 (`doeblin_eq_cme`), #119 (`sp_eq_cme`), #120
(`lyapunov_telescope`) — and #144's `no_reciprocity_induction_proof` (Session 307, a real
proof), giving 29. -/
def witnessedDeadEndCount : ℕ := 29

/-- Dead ends with weak-MC revival score ≥ 2 (#86, #90, #106, #120, #121, #125, #127, #129,
#136, #146). -/
def revivableDeadEndCount : ℕ := 10

/-- Dead end registry summary. -/
theorem dead_end_registry :
    -- Witnessed dead ends have Lean proofs
    deadEndCount = 160 ∧
    deadEndEntryCount = 150 ∧
    witnessedDeadEndCount = 29 ∧
    revivableDeadEndCount = 10 ∧
    -- Key revival chains are proved
    (RecipSumConcentration → AlmostAllSquarefreeRSD) ∧  -- #90 revival
    (∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
      (N : ℕ), -((N : ℝ) * ((q : ℝ) - 2) / (2 * ((q : ℝ) - 1))) ≤
        cumulativeDrift hq hne N) ∧  -- #120 free lower bound
    (LinearDrift → MullinConjecture) :=  -- #120 chain
  ⟨rfl, rfl, rfl, rfl,
   concentration_implies_rsd,
   fun _q _ hq hne N => cumulativeDrift_lower_bound hq hne N,
   linearDrift_implies_mc⟩

end
