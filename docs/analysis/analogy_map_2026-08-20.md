# Where the situation is workable — an analogy map (Session 317, 2026-08-20)

Method: match each open EM statement to a *settled or well-understood problem of the same
logical shape*, read off what was provable there and by what mechanism, and let that decide
where to push.  Lean for the positive items is in `EM/Population/GrowingRange.lean`.

| EM statement | Same-shape problem | What is known there | Verdict for EM |
|---|---|---|---|
| (C∞) on the autonomous branch (`E_{n+1} = E_n² − E_n + 1`) | infinitely many composite Fermat / Sylvester numbers | open | no new leverage; consistent with 2026-08-17 (b)–(f) |
| MC for the orbit of 2 | Artin's conjecture for one fixed base | open without GRH | #90; do not attack |
| per-`q` seed-average law | Hooley-type "almost all bases" | here: done unconditionally | done (S311–312) |
| §G: all `q` simultaneously, natural density | Collatz, "almost all orbits reach 1" | open; Tao (2019) proved only "a.a. `N` reach below `f(N)`, any `f → ∞`" | same wall; but Tao's *growing-range* shape was missing here and is now a theorem |
| ∃ one seed with GenMC | Heath-Brown's unconditional Artin (all but ≤ 2 prime bases) | proved by **coupling failures of different bases at the same prime** through `(ℤ/p)^×`, then a sieve | §G ⇒ ∃ seed with GenMC (trivially), which is itself open; EM has no cross-seed coupling beyond `T`-invariance |

## What was proved

* **Growing-range simultaneity** (`GrowingRange.growing_range_density`,
  `seed_range_never_density`): there is a nondecreasing `Q → ∞` such that the seeds `m` which
  never select some prime `q ≤ Q(m)`, `q ∤ m`, have natural density `0`.  With a scale-level
  horizon `N X` and the explicit rate `X/(Q X + 1)`.
  * Compared with Tao–Collatz our situation is *better* in one respect — the per-range density
    is exactly `0`, not merely small, which is why a diagonal suffices and why no "any `f → ∞`"
    clause is needed on the small side — and *worse* in another: `Q` is one specific,
    ineffective function (Karamata threshold, (K2) of the §G scoping).  The monotonicity is
    opposite to Tao's: there a slower `f` is stronger; here a faster `Q` is stronger, and
    `Q(m) = m^{2^k}`-type ranges are exactly the §G wall.
  * A seed-dependent *horizon* cannot be added to the seed-dependent form: a larger horizon
    shrinks the bad set, so `N m ≤ N X` points the wrong way.
* **`GenMC` is `T`-invariant** (`genMC_genProd_iff`, `misses_genProd_iff`): the failure set
  is a union of full orbits of `T m = m · minFac(m+1)`.  The only cross-seed coupling available.
* **"(N2)" is an orbit statement** (`scaleUniformTail_cofinite`, `_mc`; dead end #176): the
  scoping doc's missing input, stated *for all `X`*, forces every seed to miss only finitely
  many primes, hence a cofinite MC for seed 2.  The honest input (N2′) carries an `X₀(δ)`.

## What the analogies say to do next

1. **Effective `Q`.**  The next honest population target is `Q(X) ≍ log log log X`
   (the scoping doc's §2.4 heuristic), which is not a dynamical question but Mertens' first
   theorem in APs with an `O(1)` error *and explicit constants* — the retracted "Mertens
   priority" of S309–312, now with a precise consumer.  Analogy: Tao's theorem is effective.
2. **Cross-orbit coupling.**  Any existence statement `∃ m, GenMullinConjecture m` needs, by
   the Heath-Brown analogy, a relation between the failure of seed `m` at `q` and the failure
   of seed `m'` at the same `q` for `m'` outside the `T`-orbit of `m`.  The walks of different
   seeds mod `q` share nothing (different multiplier sequences); no such relation is visible.
   This is the precise form of the demand, recorded so it is not rediscovered.
3. **Do not** look for a countably additive repair inside ℕ (#167, #168) or a rate-only repair
   (#176): both are now closed with witnesses.

## Second half of the session: what theory *could* work (`EM/Population/ProfiniteAttractor.lean`)

Asked to imagine a new theory, the honest answer starts from a reformulation and a sharpened
obstruction, both now in Lean:

* **MC is convergence to `0`.**  `mc_iff_tendsto_zero`: MC ⟺ `prod n → 0` in the profinite
  topology on `Ω = ∏_r ℤ/r` (`genMC_iff_tendsto_zero` for every seed).  So the question is
  whether the seed `2` lies in the basin of the attractor `0`; Session 314 says the basin has
  full Haar measure.
* **The first coincidence.**  `measure_divisorFinite_eq_zero`: μ-a.e. point has *infinitely
  many* vanishing coordinates (second Borel–Cantelli, `Σ 1/r = ∞`), while every integer has
  finitely many (`iota_mem_divisorFinite`).  The same event recurs at every step of an orbit,
  so an integer orbit is an *infinite sequence of measure-zero coincidences*: no product-type
  measure on the coordinates, Haar or otherwise, can charge it.  That is #90 stated
  structurally — the obstruction is not that ℕ is small but that it lies in a set carrying no
  countably additive coordinate-compatible measure at all.
* **Descent.**  `descent_empty`: a set of positive seeds closed under `T`-preimages is empty
  (`T m > m`).  The Vieta-jumping shape is the only measure-free route from invariance
  (`misses_genProd_iff`) to emptiness.  Unusable as stated: `T(ℕ) ⊆ 2ℕ`, odd seeds have no
  preimage (`odd_not_in_range_T`).

### Candidate theories, ranked

1. **Heights / product formula along the orbit** (Diophantine geometry).  The only theory
   whose native objects are "coincidence sets" (ℚ ⊂ 𝔸 discrete).  What is missing is
   geometry: `minFac` is not algebraic, so there is no variety behind the orbit (#128).  A
   height-type functional on the orbit forced to drop by divisibility avoidance would be the
   new input; none is visible.  Still the right place to look.
2. **A second descent relation** preserving "misses `q`" and decreasing on an infinite family.
   Worth a scoping pass; nothing beyond `T` is known.
3. **Ergodic theory of the profinite greedy map** (invariant measures, topology of the
   exceptional set).  Closed before it starts: by a box-sieve/Dirichlet construction the
   exceptional set contains integer-like points with genuine small prime multipliers, so no
   every-orbit theorem (unique ergodicity, Ratner) can be true here.

## Session 318 — the geometry behind `minFac`, and the transfer principle (`EM/Population/GrandOrbit.lean`)

### Geometry behind `minFac`: four readings, one placement

1. **Piecewise dilation.**  In Euclid coordinates `E = P+1`, on the sieve stratum
   `S_p = {minFac = p} = pℤ ∖ ⋃_{r<p} rℤ` the map is `E ↦ p(E−1)+1`, a dilation by `p`
   centred at the fixed point `1`; the class `1 + pℤ` is forward-invariant under *every*
   branch and `F(S_p) ⊂ 1 + pℤ`.  MC = the orbit enters every absorbing class.
2. **The Collatz / FRACTRAN class.**  Truncating the sieve at `Y` makes `F` one of Conway's
   generalized Collatz functions (affine on residue classes mod `Y#`); `F` is their limit.
   Conway: orbit problems in this class are undecidable in general; Lagarias: the 2-adic
   conjugacy for 3x+1 says nothing about integers.  Known theory there is population-only
   (Terras, Tao) — exactly the shape this project has.  This is the honest placement.
3. **Adelic.**  `T(P) = λP` with `λ = p` a principal idele: dilation at ∞, contraction at `p`,
   isometry elsewhere; the product formula equates archimedean growth with total local
   contraction.  MC = every local coordinate contracted once.  A height argument would need
   a second functional; none visible.
4. **Function fields are the one literal geometry.**  Over `𝔽_q[t]`, "least factor degree
   `= d`" is constructible (resultants against `t^{q^k} − t`), so the min-degree dynamics is
   piecewise algebraic.  Unasked: is the *backward* tree algebraic there?

### Descent beyond `T`: the question becomes a density question

`Misses q` and `GenMC` are invariants of the grand-orbit relation `m ≈ m'` ⟺ orbits
eventually coincide (`misses_congr`, `genMC_congr`).  Descent along `≈` bottoms out at class
minima, so emptiness would need orbit merging with a known-good seed — open and implausible.
But invariance gives the **transfer principle** (`transfer_principle`): for *any* relation
under which `Misses q` is invariant, a positive-upper-density class of `2` proves MC (the class
would otherwise sit inside the density-zero set of the seed-average law).  This is the precise
Heath-Brown coupling: "descent relation beyond `T`" = "GenMC-preserving relation with a fat
class of `2`".  For the grand orbit itself: preimages of `N` are `N/p`, `p ∣ N`, with the
square condition `p² ∣ N + p` (`preimage_iff`, `preimage_cond_iff_sq`), so extra branches of
the backward tree are mod-`p²` events of heuristic probability `1/p` — the class of `2` is
expected to be polylogarithmic and the instance vacuous.  Not proved; proving thinness is a
mod-`p²` orbit statement.  The open question isolated: does *any* GenMC-preserving relation
have a fat class of `2`?

### Condensed mathematics — a home, not a tool (assessed 2026-08-20)

`Ω = ∏_r ℤ/r` is a *light* condensed set; `Ω ∖ U = ⨆_p S_p` (clopens on which `T` is
multiplication by `p`) makes `T` a map of light condensed sets, band locality
(`profProd_agree_of_agree`) is its pro-structure, and the Haar/cylinder measure theory of
Sessions 314 and 317 is the solid module `ℤ[Ω]^■ = lim ℤ[Ω_Y]`.  All of that is exposition.
Condensed mathematics is a foundation for algebra with topology; its number-theoretic results are
cohomological and about spaces of algebraic origin.  It supplies no dynamical invariants, treats
the discrete subobject `ℕ_disc → Ω` exactly as classical topology does (the first coincidence
applies to solid measures verbatim), and `minFac` is not algebraic (#128).  The one apt angle is
the liquid/solid = archimedean/non-archimedean split: an eventual "height along the orbit"
argument would be written in the language of the adelic analytic ring (`T` = multiplication by a
principal idele, product formula balancing dilation at `∞` against contraction at `p`).  The
framework would be notation for such an argument, not a source of it.  **Verdict: no theorem
expected; recast for clarity only.**

### The adelic angle, developed (`EM/Population/AdelicShadow.lean`)

**Formalism.**  `T(P) = λP` with `λ = p_{n+1}` a principal idele: `|λ|_∞ = p`, `|λ|_p = 1/p`,
`|λ|_v = 1` otherwise; `∏_v |λ|_v = 1`.  Along the orbit, `log P_n = Σ_k log p_k` is the total
local contraction.  The divisor of the Euclid number, `div E_n = Σ_{p} v_p(E_n)[p]`, has degree
`log E_n` (product formula); the greedy rule keeps its *least* point and discards the rest.

**What the bookkeeping proves (Lean, orbit-level, unconditional).**
* *Local side.*  Hits `{n : q ∣ E_n}` inject into the primes `≤ q` via the multiplier
  (distinctness), hence are finite (`hits_finite`); more than `π(q−1)` hits force selection of
  `q` (`captured_of_many_hits`); so **every finite place is eventually a unit** on the Euclid
  numbers (`eventually_unit`), captured or not.  The failure of MC at `q` is therefore exactly
  "`P_n` and, eventually, `E_n` are `q`-adic units" (`misses_iff_eventually_unit_both`): the two
  classical failure modes collapse into the first up to finitely many steps.
* *Archimedean side.*  The defect `δ_n = log P_n − log p_{n+1}` of the growth telescope is,
  up to `log(1+1/P_n)`, the log of the discarded cofactor `E_n/p_{n+1}`
  (`defect_eq_log_cofactor`): the telescope is the product formula summed along the orbit with
  the chosen place removed at each step.  The growth constant `C` is the archimedean shadow of
  how much divisor the greedy rule throws away.

**What it would need.**  An inequality localising archimedean height at a *fixed small* place
`q` along the orbit.  The product formula yields totals dominated by huge primes.  `S`-unit and
subspace theorems (Mahler, Størmer, Corvaja–Zannier) localise at finitely many places but for a
*fixed* support; `P_n` is an `S_n`-unit with `S_n` growing, so every fixed-`S` statement is
exhausted after finitely many `n` — technique mismatch of the #134 type.  The strongest local
statement the bookkeeping yields, `eventually_unit`, is symmetric between capture and failure.

**Verdict.**  The adelic language is the right one for stating the dichotomy (and the Lean
above is the cleanest orbit-level formulation of MC-failure the project has), but it localises
nothing.  The condensed/analytic-stack framework would host a height argument; the argument
itself still does not exist.  Closed as a *source*; kept as *language*.
