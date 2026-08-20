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
