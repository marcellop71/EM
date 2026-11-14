# Arithmetic dynamics with feedback selection

Session 325, 2026-11-08. Follow-up to the catalogue sweep of 2026-11-07, which named
"arithmetic dynamics with feedback selection" as the one theory that would have to exist for
MC to become attackable. This memo defines the theory, proves what is provable today
(`EM/Population/FeedbackSelection.lean`, 0 sorry), classifies the known rules in its terms,
and locates its first open problem relative to MC.

Verdict in one line: the theory has a clean **necessity half** (feedback is forced, and all
steering happens at deviations) which is now theorems; its **positive half** (that the
deviations steer the walk into `−1`) is the conjecture itself, and its choice-free relaxation
`MixedMC` is already open. Dead end #183 records the autonomy route.

## 1. The object

A **Euclid rule** is a map `σ` assigning to every integer `E ≥ 2` a nontrivial divisor
(`EuclidRule`). The orbit from a seed `P₀` is

    E_n = P_n + 1,   ℓ_n = σ(E_n),   c_n = E_n / ℓ_n,   P_{n+1} = P_n ℓ_n.

Take-all `σ = id` is Sylvester, `P ↦ P² + P`. Greedy `σ = lpf` is Euclid–Mullin.
Every rule is **the Sylvester map divided by its cofactor**:

    P_{n+1} · c_n = P_n² + P_n,        c_n · E_{n+1} = P_n² + P_n + c_n.

Modulo a prime `q` this is `walkZ_succ_mul_cofactor`. So a rule is autonomous exactly to the
extent that its cofactors are `≡ 1`, and the whole non-autonomy of Euclid–Mullin is the
sequence of residues `(c_n mod q)_n`. "Feedback" means: `c_n` is read off the factorisation
of the current state and written back into the next one.

Two notions, for a fixed prime `q`:

* stage `n` is **`q`-autonomous** if `c_n ≡ 1 (mod q)` (`StageAutonomous`); a prime Euclid
  number is autonomous modulo every `q`, but the converse fails, so this is strictly weaker
  than the repository's `PerpetualPrimality` / `Frozen` hypotheses;
* stage `n` **deviates** modulo `q` otherwise (`Deviates`).

## 2. Theorems (all in Lean)

**Autonomy is take-all** (`sel_cast_eq_of_autonomous`). If the residue of `σ(E)` modulo a
prime `q` is a function of the residue of `E` on inputs coprime to `q`, then
`σ(E) ≡ E (mod q)` for all such `E`. Proof: Dirichlet puts a prime in every unit class; on a
prime the rule has no choice; so the function is the identity on units. Consequences:

* the cofactor of an autonomous rule is `≡ 1 (mod q)` (`cofactor_cast_eq_one_of_autonomous`),
  so its walk modulo `q` is the Sylvester walk;
* the greedy rule is autonomous modulo no odd prime (`greedy_not_autonomous`: a prime
  `r ≡ 2⁻¹` gives `lpf(2r) = 2` with `2r ≡ 1`).

This closes the route "find a modulus or a rule where the selection is autonomous, then use
arboreal Galois theory": the only autonomous rule is Sylvester, whose prime support has
density zero (Odoni 1985). The repository's sentence "provability needs rigidity, every
known rigidity destroys completeness" (logic memo, 2026-09-01) is now a theorem on the
rigidity side: autonomy modulo any prime *is* take-all modulo that prime.

**All steering happens at deviations.**

* Along a `q`-autonomous run the walk is the Sylvester iteration (`walkZ_add_of_run`).
* A capture of `q` at the end of a nonempty autonomous run forces a root of `Φ₃` modulo `q`,
  namely the state one step before (`phi3_root_of_capture_after_run`).
* Hence for `q ≡ 2 (mod 3)`, `q ≥ 5`: **every capture is immediately preceded by a
  deviation** (`deviates_of_dvd_two_mod_three`), and MC forces one for every such prime
  (`exists_deviation_before_capture_of_mc`). This upgrades the known "the stage before a
  capture of `q ≡ 2 (3)` is composite" from `c_n ≠ 1` to `c_n ≢ 1 (mod q)`.
* An autonomous **tail** freezes every `q ≡ 2 (mod 3)` outside the bag
  (`frozen_of_autonomous_tail`), generalising `QuadraticStep.frozen_of_perpetual`.
* On an autonomous tail capture is **decided in fewer than `q` steps**
  (`capture_iff_of_autonomous_tail`), by pigeonhole on the Sylvester orbit in `𝔽_q`
  (`exists_iterate_lt_card_of_exists`). This generalises "perpetual primality is the
  computationally easy branch" from `c_n = 1` to `c_n ≡ 1 (mod q)`.

**The rung** (`autonomous_rung`). Define `NoAutonomousTail`: for every prime `q ≡ 2 (mod 3)`,
`q ≥ 5`, not yet in the bag at stage `N`, some later cofactor is `≢ 1 (mod q)`. Then

    MC  ⟹  NoFrozen  ⟹  NoAutonomousTail  ⟹  (C∞)

(`noFrozen_of_mc`, `noAutonomousTail_of_noFrozen`, `infinitelyManyComposite_of_noAutonomousTail`).
The middle statement is the most elementary open statement about cofactor residues: it asks
only that one residue class modulo one prime not be hit forever, and it already implies
infinitely many composite Euclid numbers. It sits strictly below NoFrozen (an autonomous tail
has `D_n ≡ −3`, a frozen tail only has `D_n` a non-square) and strictly above `(C∞)` in
strength of hypothesis. This is where the `(C∞)` gap sits: in a single residue class of the
discarded part.

For `q ≡ 1 (mod 3)` the same mechanism gives a quantitative statement not yet in Lean: a
capture after `k` autonomous steps forces the state `k` steps earlier into the level-`k` set
of the backward orbit of `−1` under `y ↦ y² + y`, which has at most `2^k` points in `𝔽_q`
(the sets of `BackwardLevels.lean`). By Odoni's theorem the proportion of primes admitting
a level-`k` point tends to zero with `k`. So **for all but a density-`o(1)` set of primes,
a capture must be preceded by a deviation within a bounded number of steps.** Deviations
are the only places where the walk is placed; autonomous runs only transport it along a
fixed tree.

## 3. The function-field calibration: the threshold `2^{v₂(deg)}`

Over `𝔽_2[X]` the autonomous step is `P ↦ P² + P = (F + 1)P`, an `𝔽_2`-linear operator
(Frobenius plus one). Modulo an irreducible `π` of degree `d` the residue field is
`𝔽_{2^d}`, and a capture of `π` after `k` autonomous steps requires
`1 ∈ Im (F + 1)^k` on `𝔽_{2^d}`.

Theorem (Lean, `EM/FunctionField/AutonomousThreshold.lean`, added later on 2026-11-08):
**`1 ∈ Im (F+1)^k` on `𝔽_{2^d}` iff `k ≤ 2^{v₂(d)} − 1`**
(`AutonomousThreshold.one_mem_sylv_iterate_image_iff`, stated as
`(∃ x, x^{2^d} = x ∧ sylv^[k] x = 1) ↔ k < 2 ^ padicValNat 2 d`). So an irreducible of degree
`d = 2^v · odd` can be captured after at most `2^v − 1` consecutive autonomous steps; for odd
degree the step immediately before a capture must deviate.

Scope (corrected 2026-11-10). For runs of *irreducible* stages this adds nothing to what was
already in Lean: such a run has length at most `3` (`CompositeFloors.not_four_consecutive_irreducible`,
`AutonomousThreshold.run_lt_four`), `k = 1, 2` are `AutonomousDegrees.even_natDegree_of_dvd_euclid_succ`
and `four_dvd_natDegree_of_two_irreducible`, and `k = 3` gives `4 ∣ D`, the `k = 2` statement one
stage later. The sequence form `lt_two_pow_padicValNat_natDegree_of_run` is therefore empty for
`k ≥ 4`. What the field-level theorem does give:

* every solution of `(F+1)^k y = 1` has Frobenius period exactly `2^{⌊log₂ k⌋+1}`
  (`minimalPeriod_eq_of_sylv_iterate_eq_one`), so every irreducible factor of the level
  polynomial `Φ₆^k + 1` over `𝔽_2` has degree `2^{⌊log₂ k⌋+1}`
  (`natDegree_eq_of_irreducible_dvd_level`); the level polynomial is irreducible exactly for
  `k ≤ 2`, which is where the floor constant `3` comes from. Frobenius at `2` acts on level `k`
  of the Sylvester tree with all cycles of length `2^{⌊log₂ k⌋+1}`; at `5` it is one cycle
  (`StableTower`); over `ℚ` the group is the full wreath product (Odoni).
* the residue-autonomous form (`lt_two_pow_padicValNat_natDegree_of_residue_run`): `k` stages
  whose cofactors are `≡ 1` at a root of `f`, followed by a capture of `f`, force
  `k < 2^{v₂(deg f)}`. Here `k` is unbounded; this is the twin of
  `FeedbackSelection.level_prime_of_capture_after_run`.

Proof as formalised (no relative trace needed). *Necessity*: in characteristic `2`,
`(F+1)^{2^v} = F^{2^v} + 1` (`sylv_iterate_two_pow`), so if `(F+1)^k y = 1` with `k ≥ 2^v`
then `z = (F+1)^{k−2^v} y` solves `z^{2^{2^v}} = z + 1`; iterating, `z^{2^{2^{v+1}}} = z` and
`z^{2^{2^v}} ≠ z`, so `z` has Frobenius period exactly `2^{v+1}`
(`minimalPeriod_eq_of_sylv_iterate_two_pow_eq_one`; this is the period-2 and period-4
computation of `CharTwo.lean` in closed form), and that period divides the period of `y`
because `F+1` commutes with `F`. *Sharpness*: `(F+1)^j` is evaluation of a monic polynomial
of degree `2^j` (`sylvPoly_iterate_monic_natDegree`), so `(F+1)^{2^v−1}` has at most
`2^{2^v−1} < 2^{2^v}` zeros, while `(F+1)^{2^v} = 0` on `𝔽_{2^{2^v}}`; a nonzero value in
`ker(F+1) = {0,1}` is `1` (`exists_sylv_iterate_pred_eq_one`). The Jordan-block picture of
the first draft (single block on `𝔽_{2^{2^v}}` with socle `𝔽_2·1`) is the same fact; the
root count replaces the dimension count.

The parallel with `ℤ` is exact in shape: over `ℤ` the autonomous capture of `q` after `k`
steps is a Chebotarev condition in the degree-`2^k` field of the Sylvester tower, with
density tending to zero; over `𝔽_2` it is a linear-algebra condition with an explicit
cut-off. In both rings the feedback must arrive within bounded distance of the capture for
almost all targets. Neither ring offers anything on the positive side, because the residue of
the chosen factor at a deviation is the factorisation of one specific Euclid number.

## 4. The rules, classified

| rule | feedback | known theorem about capture | mechanism |
|---|---|---|---|
| take-all (Sylvester) | none: autonomous mod every `q` | prime support has density 0 (Odoni) | arboreal Galois group of `x² − x + 1` is the full wreath product |
| greedy (`lpf`) | autonomous mod no odd `q` (`greedy_not_autonomous`) | none, either way | no symmetry (`GreedyRigidity`), no autonomy (this file), no residue invariant (`NoInvariant`) |
| largest factor | full | infinitely many primes omitted (Cox–van der Poorten, Booker, Pollack–Treviño) | a quadratic-reciprocity invariant propagates because the small primes are kept out of the accumulator |
| uniformly random factor | full, averaged | a.s. capture ⟸ block-reachability + anatomy (`RandomVariant.capturesAS_of_blocks`); open | the a.s. statement implies reachability, so it is at least as strong as `MixedMC` |
| any factor (the Euclid tree) | full, with choice | `MixedMC` open; every prime below `10⁹` occurs (Booker–Irvine) | BFS in `(ℤ/q)^×` on reachable sets |
| steered (Booker 2016) | full, with choice of *which product* to add 1 to | **complete**: every prime appears (Lean: `EuclidClosed.generated_iff_prime`, 2026-11-14) | products of many primes from one residue class; pigeonhole and a sum over the attainable residues |

Reading the table top to bottom: the less feedback a rule has, the more is provable and the
less it captures; the only complete rule is the one that is not a Euclid rule in the sense
of §1 at all, because it changes the accumulator it adds `1` to. The greedy rule sits at the
point of maximal feedback with zero freedom.

## 5. The first open problem of the theory

`MixedMC` (`EM/Stochastic/MixedMC.lean`): for every prime `q`, some branch of the Euclid tree
from `2` has a node `P ≡ −1 (mod q)`. This removes the greedy choice entirely and keeps only
the feedback constraint `ℓ ∣ P + 1`. The theory says it is the right first target because:

* it is implied by MC and by the random-rule conjecture, so it is the weakest statement in
  the family;
* its difficulty is exactly the feedback constraint, since the same question with Booker's
  freedom of choosing the product is a theorem;
* it is still an orbit statement about specific integers (the tree's nodes), so the four
  no-go theorems of the catalogue sweep apply to it unchanged. In particular no population
  average over seeds reaches the tree from `2` (#90), and no symmetry relates branches (#181).

Nothing in §2–§3 helps with it: those results constrain *when* a capture can happen, never
*that* one does. A positive theorem would need the residue of some prime factor of a specific
Euclid number, which is the single-integer barrier in its original form.

## 6. What the theory yields, honestly

* **Necessity theorems**: feedback at bounded distance before almost every capture; exact
  over `𝔽_2` (threshold `2^{v₂(d)}`, now a Lean theorem with sharpness), Chebotarev-density
  over `ℤ`.
* **Classification**: autonomy = take-all; the taxonomy of §4.
* **A rung**: `NoAutonomousTail`, between NoFrozen and `(C∞)`.
* **Decidability on autonomous tails**: capture decided in `< q` steps; the only place where
  MC is finitely checkable, and the place where it is known to fail for half the primes.
* **No positive mechanism**, and a proof that none can come from autonomy.

## 7. Follow-ups

1. ~~Lean, moderate: the `𝔽_2` threshold theorem of §3.~~ Done:
   `EM/FunctionField/AutonomousThreshold.lean` (iff with sharpness at the field level; exact
   factor degrees of the level polynomials; the residue-autonomous form, added 2026-11-10
   together with the scope correction of §3).
2. Lean, small: seeded versions of §2 (`genProd`, `seedCofactor`), and the level-`k`
   statement for `q ≡ 1 (mod 3)` using `BackwardLevels.realizedLevels`.
3. Paper: a paragraph in `why_its_hard.tex` after the definition of the non-autonomous map
   (around line 657): "autonomy modulo a prime is take-all", with the identity
   `P_{n+1} c_n = P_n² + P_n` and the deviation principle.
4. Reading: whether any theorem places a *lower bound* on the density of primes captured by
   a non-autonomous Euclid rule; none is known to me, and the table of §4 predicts none.
