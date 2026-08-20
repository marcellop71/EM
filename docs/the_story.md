# The story of the EM formalization, told from above (2026-08-17, updated 2026-08-20)

*This is the narrative the paper is now organized around.  It was written after the day on
which the population layer (PE / DSL) was found to be false and archived, and after the
audit of every remaining hypothesis.  Keep it current: it is the shortest honest account of
what the project is.*

## 1. One map, one orbit

Let `X` be the squarefree integers and `T(n) = n · minFac(n+1)`.  Everything in the repo is
about the dynamics of `T`.  The Euclid–Mullin sequence is the orbit of `2` (or of `1`);
`genProd n k = Tᵏ n` is the ensemble; the tail identity is "the shift is `T`"; the factor
tree is the multivalued relative `n ↦ n·p` for `p | n+1`; the variants are other selection
rules; the function-field analogue is `T` over `𝔽_p[t]`.  MC says the orbit of `2` meets
every prime.  The question underneath most of the repo: *what structure does `(X,T)` have,
and how much of it does one orbit inherit?*

## 2. Two exact projections of `T`

* **The residue walk.**  Mod a prime `q`, `Tⁿ(2) mod q` is a multiplicative walk on
  `(ℤ/q)^×` with multiplier `minFac(P_n+1) mod q`; `q` appears iff the walk hits `−1` past
  the stage where smaller primes are exhausted (`walkZ_eq_neg_one_iff`; bootstrap with
  SubgroupEscape free via PRE).  MC is a hitting statement, exactly.
* **The growth constant.**  `C = lim log Tⁿ(2)/2ⁿ` exists, `C(Tm) = 2C(m)`, and
  `C = 0 ⟺ (C∞) ⟺ ¬ eventual perpetual primality` (`DefectTelescope`).  `C` semiconjugates
  `(X,T)` to doubling; doubling has no invariant probability except at `0`; so `(X,T)` has
  none and "generic orbit" is meaningless.  This is the ergodic content of the four-way
  blocker, and it is a theorem.

## 3. The top: CME, and why nothing sits under it

`CME ⇒ CCSB ⇒ hits ⇒ MC` is proved.  CME (conditional equidistribution of the multiplier
given the walk position, along the orbit, for a missing `q`) is where the story stops — and it
is a *reformulation* of MC: quantified over missing primes, so MC ⇒ CME vacuously and
CME ⟺ CCSB ⟺ DH ⟺ MC (`EM/CME/Equivalences.lean`, 2026-08-18 review). Its content is the
direction CME ⇒ MC.  Every attempt to put something under it met one
of three fates:
* **CME by definition** — `OCE`, `SP`, `CRTPointwiseTransferBridge` (its input PCE is a
  `True` placeholder), Doeblin convergence; all `rfl`/iff collapses.
* **Walled by orbit-specificity** — #90/#117, witnessed in `(ℤ/5)^×`: two multiplier
  sequences with identical statistics, one hits `−1`, one never does.
* **False** — the whole fixed-modulus population layer (PE, MFRE, RoughLPFEquidist,
  MFREConditional, GenericLPFEquidist, UCE): the class density of `minFac mod q` is the
  convergent, head-dominated series `∑_{p≡a} w_p`, `w_p = c(p) − c(p+1)`; Dirichlet's
  theorem constrains only its massless tail (`roughLPFEquidist_iff`).  DSL = PE ⇒ CME was
  vacuous.  Also false: the uncentered ensemble character layer (SD, CSVB, ECSC, FourPointPCV,
  SMSB, TWD) at `χ ≡ 1`, and fixed-step ensemble multiplier equidistribution at step 0
  (odd seeds ⇒ multiplier 2) — all refuted in Lean by argument (`UncenteredRefutations`).
  What ANT delivers, now unconditionally: Mertens in progressions, asymptotic form (Karamata).

## 4. The floor: (C∞)

Below MC: weak MC, reciprocal divergence, (S) "least factor < 2^{n−c} i.o.", (C∞) — all
implications proved.  (C∞) is Sylvester-tower primality (Fermat-shaped).  The arboreal
levels: the classical `Φ₃` death equation is level one of a finite ladder; the Chebotarev
input is free; the residual gap is a size condition on one integer's factorization.  **MC
implies "no infinite prime tower for a doubly-exponential sequence", which is open (a statement
of shape, not a difficulty lower bound — review 2026-08-18).**

## 5. Obstructions

No propagating congruence invariant blocks a prime under `minFac` (`no_cvdp_obstruction`);
the same class is inhabited under `maxFac` and machine-checks Cox–van der Poorten.
Reciprocity invariants and smoothness guards fail the same way.  A disproof would have to be
anatomical; symmetrically, no congruence model predicts the multiplier (`T` has no
continuous extension to any compactification), which is why generic-point arguments die.

## 6. The comparison class

Ensemble, factor tree, two-point, ε-random, function field: change one thing and see what
survives.  Almost-all tree hitting is unconditional; the ε-perturbed rule captures a.s. yet
ε→0 is a faithful reformulation of MC (#159); Booker's steered variant hits everything;
`maxFac` misses.  **Selection is where the difficulty lives** — access to the factor bag is
not the problem, the deterministic choice of its least element is.  Over `𝔽_p[t]` the Weil
statements in Lean are `True` placeholders (marked; badged `[placeholder]` in the paper); the
real FF content is the exact degree telescope, `Φ₃` exclusion, `FFDirichletDensity`.

## 7. The population, done properly: the seed-average law (2026-08-19)

If nothing population-level can settle the orbit of `2`, the population can still be
understood on its own terms, unconditionally.  Seeds `m` coprime to a fixed prime `q`, run
under `T`: for every `ε > 0` there is a horizon `n` such that the seeds in `[1, X]` that have
not selected `q` within `n` steps number at most `εX` for all large `X`
(`AlmostAllDensity.almost_all_genmc_density`, `_limsup`); hence the coprime seeds that *never*
select `q` have upper natural density `0` (`never_captures_limsup_eq_zero`).  Inputs: the
box-sieve selection law (`SelectionLaw`), the large-step roughness / charge budget, Theorem C
and its fibre form; no equidistribution hypothesis anywhere.  Per fixed `q`, and finitely many
`q` at a time (`finite_simultaneous_density`); the simultaneous-in-`q` natural-density form is
**open** because natural density is only finitely additive (#167/#168 — it is not a rate
problem).  The repair is a countably additive ambient measure: on the profinite ensemble
`Ω = ∏_q ℤ/q` with Haar measure, μ-almost every profinite seed captures every prime whose
coordinate it does not annihilate (`ProfiniteHeadline.measure_some_prime_missed_eq_zero`);
the integers are μ-null in `Ω`, so this says nothing about any integer orbit — #90/#117 stand.
The *orbit* direction of the sure (per-path) layer is closed (#169–#174).

## 8. Dead ends as the coastline

175 numbers, 165 entries, 33 witnessed (`EM/Meta/DeadEnds.lean`, generated from
`tools/dead_ends.tsv`); #90/#117 carry the thesis and are witnessed in `(ℤ/5)^×`; the rest
are peripheral instances of the four-way blocker or of head domination.  #175 (2026-08-20)
is a reminder that statements about the generalized sequence must exclude the primes dividing
the seed.

---

## What the retelling changes

The project is not "a reduction of MC to a hypothesis" — that framing died with DSL.  It is
**a complete map of what one orbit of `T` provably inherits from the structure of `T`**:
exact projections (walk, growth), an equivalent reformulation at the top (CME ⟺ MC), a
Fermat-shaped floor at the bottom ((C∞)), obstruction theorems on both sides, a comparison
class isolating selection as the culprit, and — on the population rather than the orbit — the
unconditional seed-average law.  The abstract and introduction now say it that way.

## The paper's flow (as of 2026-08-17)

1. Introduction — the story above (`introduction.tex`).
2. Bag structure; residue walk (projection 1).
3. **The composite floor (C∞)** (projection 2 + the floor) — moved up from the end.
4. Character-sum reduction (the top: CME ⇒ CCSB ⇒ MC).
5. Ensemble averaging and the reduction landscape (why nothing sits under CME; head domination
   as a theorem; the orbit hypothesis in the ensemble picture).
6. Spectral and variance routes.
7. Receptacle program.
8. **Min/max dichotomy** (obstructions) — moved before the comparison class.
9. Variants (landscape, factor tree, two-point, ensemble/weak); function field.
10. Why it's hard; Lean formalization; appendix.

## Ideas that came out of the retelling (pass 4) — status 2026-08-17

* **The bag-conditioned multiplier law — DONE** (`EM/Population/BagConditionedLaw.lean`).
  On the progression `m ≡ 1 (mod P)` (which contains every Euclid number with accumulator
  `P`), `minFac m = p ↔ p ∣ m ∧ Coprime m N'` with `N'` the product of primes below `p`
  outside the bag (`minFac_eq_iff_on_ap`); CRT + an affine block count
  (`card_coprime_affine_block`: `φ(N')` per block of `N'` along `c₀ + pP·t`) give the exact
  relative density `bagWeight P p = (1/p)∏_{r<p, r∤P}(1−1/r)` (`tendsto_bagClass_div_ap`).
  Corollary: the least prime outside the bag has relative density **exactly `1/q`**
  (`bagWeight_least_missing`, `tendsto_least_missing_div_ap`) — Shanks' heuristic with its
  correct biased law, at the population level.  Head-dominated as before; the orbit still
  inherits only the heuristic (`P_n+1` is one member of the progression).
  Open question left: is "all primes below `z` eventually captured, for every `z`" a real
  intermediate or MC itself?  (It is MC: it says every prime is captured.  What is not MC is
  the *rate*, i.e. the least missing prime as a function of `n`.)
* **`C` as a factor map — DONE** (`EM/Population/SeededGrowth.lean`).  `sgrowth m` for every
  seed `m ≥ 2`; `sgrowth (T m) = 2·sgrowth m`, `sgrowth (Tᵏ m) = 2ᵏ·sgrowth m`
  (`sgrowth_T`, `sgrowth_iterate`); `sgrowth m = 0 ⟺ (C∞) from seed m`;
  `sgrowth 2 = growthConstant`; **`MixedDiversity ⟺ ∀ m ≥ 2, sgrowth m = 0`**
  (`mixedDiversity_iff_sgrowth_zero`) — the invariant set `{C > 0}` is empty iff MixedDiversity.
  Paper: `composite_floor.tex` §"The seeded growth constant".
* **The genuinely distinct open statements** are now short: CME, CCSB, DH/HH/SHH, VE/SVE/SCD,
  DecorrelationHypothesis, MultiModularCSB (+ BV bridge), StrongSieveEquidist/window gains,
  EnsembleConcentration, and the floor ladder (WeakMullin, RD, (C∞), MixedDiversity — the
  last now read as "the doubling factor map `C` has empty positive part").

## The growth projection, measured (2026-08-18)

Prompted by the observation that the growth constant is far less explored than the walk — and
that this is structural (`C` sees only the floor; MC is invisible from it):

* **`{C>0}` is null threshold by threshold** (`EM/Population/GrowthDensity.lean`): primes have
  density zero by the elementary sieve (`primeCounting'_add_le` + `cfun → 0`, no PNT); density
  zero pulls back under `T` (split by `minFac(m+1) = p ≤ z`, tail = rough count); hence
  `{m : ∀ n ≥ N, Tⁿm+1 prime}` is null for every `N`.  Honest limit: `{C>0} = ⋃_N E_N` and
  density is not countably subadditive, so "MixedDiversity a.e." is NOT concluded (uniform
  version open, mild).
* **The joint object** (`EM/Population/SizeResidueDecoupling.lean`): position and size couple
  through one bit.  Prime stage ⇒ residue forced (`≡ w+1`, autonomous branch).  Composite stage:
  every `(w ≠ −1, a, size ≥ K)` is realized by a squarefree seed in the ensemble (`m = 2m'`,
  `m'` a Dirichlet prime in a CRT class; `minFac(2m'+1) = p ≡ a`, `p > K`).  So on `{C=0}` the
  growth side carries no residue information — the projections are not on a par, by theorem.
* **A second, unscaled invariant** (`EM/Population/RelativeSize.lean`):
  `ρ(m) = liminf log minFac(Tⁿm+1)/log Tⁿm`, `ρ(Tm) = ρ(m)` exactly; `C>0 ⟺ ρ=1`,
  `(C∞) ⟺ ρ ≤ 1/2`, so `ρ ∈ [0,1/2] ∪ {1}`; seeded RD ⇒ `ρ = 0`.  New rung on the orbit of 2:
  **MC ⇒ RD ⇒ ρ(2)=0 ⇒ ρ(2) ≤ 1/2 ⟺ (C∞)**.  Open: is `ρ(2)=0` strictly between RD and (C∞)?
  ((S) sits between RD and `ρ(2)=0`.)

## Where the retelling points next (after pass 4)

* The bag law makes the **rate** question precise: writing `q_n` for the least prime outside
  `B_n`, the population predicts `minFac(P_n+1) = q_n` with probability `1/q_n` at each step;
  MC is `q_n → ∞`.  A theorem of the form "if `q_n` stays bounded then …" would be an orbit
  statement — that is where CME lives.  Nothing population-level can settle it (#90/#117).
* ~~The seeded constant suggests studying `T` on the fibre `{C = 0}`: does the doubling factor
  map have a *second* invariant (a bounded quantity not scaled by `T`)?~~ — DONE: `ρ` above.
  It is not a hitting-time proxy (size–residue decoupling); it is a floor-ladder refinement.
