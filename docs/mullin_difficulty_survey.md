# Why Mullin's Conjecture Is Hard: A Survey

*EM project, 2026-10-25 (Session 322).  Every claim marked with a Lean anchor is machine-checked
in the repository; the anchors are collected in the appendix.*

---

Euclid's remark is the oldest construction in number theory: multiply the primes you have,
add one, and the result has a prime factor you did not have.  Mullin (1963) asked what happens
if one always keeps the *smallest* new prime and never stops.  Starting from 2 the process
produces 3, 7, 43, 13, 53, 5, 6221671, 38709183810571, 139, 2801, 11, 17, 5471, …, a sequence
in which every prime appears at most once and, apparently, every prime appears.  Mullin's
conjecture (MC) says that it does.

Nothing depends on MC.  No other theorem is waiting for it.  Its interest is of a different
kind: it is the cleanest known instance of a question that mathematics has no technique for,
and the difficulty can be *mapped*.  This survey is that map.  The thesis is that MC is
provably invisible to every averaging method, provably uncertifiable in the negative,
Fermat-hard in the positive, and the single undecided cell of a rigid/free dichotomy.  A
proof will not be a clever application of a known tool; it will be a new tool, and that tool is
the prize.

## 1. The object

Write `P_n = p_0 p_1 ⋯ p_n` for the running product, `E_n = P_n + 1` for the Euclid number,
`p_{n+1} = lpf(E_n)` for the least prime factor, and `c_n = E_n / p_{n+1}` for the *cofactor*,
the part of the Euclid number the rule discards.  The whole dynamics is the pair `(p_{n+1}, c_n)`.

Three immediate facts shape everything.  The primes `p_n` are distinct, since `E_n` is coprime
to `P_n`.  The products grow at least exponentially and at most doubly exponentially,
`n + 1 ≤ log₂ P_n ≤ 2^n`, since `P_{n+1} = P_n p_{n+1} ≤ P_n E_n`; `log P_n ≍ 2^n` is exactly the
prime-tower branch (`C > 0`), which refutes MC, so under MC `log P_n = o(2^n)`.  And at a prime stage (`E_n` prime, `c_n = 1`) the next
Euclid number is a polynomial in the current one: `E_{n+1} = E_n² − E_n + 1 = Φ₆(E_n)`.  A run
of prime stages is therefore a *Sylvester tower*, an orbit of the quadratic map `Φ₆`, and the
greedy rule leaves the tower exactly at a composite stage.

Computation is nearly powerless here.  To know `p_{n+1}` one must factor `E_n`, a number that
already has hundreds of digits around `n ≈ 50`, and about fifty terms are known.  This is not a problem on which
experiments accumulate.

## 2. What the conjecture says, in five languages

Each of the following is equivalent to MC, and each has been the starting point of a line of
attack.

1. **Residue walk.**  For a prime `q`, the walk `x_n = P_n mod q` moves by multiplication by
   `p_{n+1} mod q`.  The prime `q` divides `E_n` iff `x_n = −1`.  MC says: for every `q`, the walk
   reaches `−1`, and `q` is then the least prime doing so.  [`walkZ_eq_neg_one_iff`]
2. **Head.**  Let `head(n)` be the least prime not yet captured.  Then `lpf(E_n) ≥ head(n)`
   always, and MC is equivalent to equality infinitely often, equivalently `head → ∞`.
   [`mullin_iff_head_captured_io`, `mullin_iff_head_tendsto`]
3. **Divisibility.**  MC is equivalent to: every prime divides *some* Euclid number.  A hit of
   the head is a capture, since nothing smaller is missing; so hits suffice.  The least-factor
   rule plays no role in the *statement*, only in the dynamics that produces the `E_n`.
4. **Profinite.**  In the profinite completion `Ẑ`, MC says `P_n → 0`.  All limit points of the
   orbit lie in the singular set `−1 + Ẑ^×`, and MC says the only one is `0`.  [`hits_finite`]
5. **Class group.**  `E_{n+1} = N(p_{n+1}ω − 1)` in the imaginary quadratic order of
   discriminant `D_n = 1 − 4c_n`; MC says every prime `q ≥ 5` is at some stage the least norm
   among the prime ideals of the principal relation `(p_{n+1}ω − 1) = ∏𝔮_i`.
   [`euclid_succ_eq_norm`, `mullin_implies_nonprincipal_least_factor`]

The five languages are not five routes.  They are one target, and the project's main
structural theorem is that the natural analytic hypothesis in language 1, conditional
multiplier equidistribution (CME), is *equivalent* to MC rather than weaker than it.
[`cme_iff_mc`]

## 3. The ladder: MC is Fermat-hard

Below MC sits a ladder of weaker statements, each open, each saying that the least prime
factor of the Euclid number is small infinitely often:

    MC  ⟹  RD  ⟹  (S)  ⟹  (C∞)

where RD is `∑ 1/p_n = ∞`, (S) is `lpf(E_n) < 2^{n−c}` infinitely often, and (C∞) is that
infinitely many Euclid numbers are composite.  [`mc_implies_rd`,
`exists_small_minFac_of_reciprocalDivergence`, `infinitelyManyComposite_of_small_minFac`]

The bottom rung is the floor, and it is already out of reach.  The growth constant
`C = lim log(P_N)/2^N` exists and is a *complete* invariant: `C = 0` iff (C∞), and `C > 0` iff
the sequence is eventually a Sylvester tower of primes.  [`infinitelyManyComposite_iff_growthConstant_eq_zero`,
`growthConstant_pos_iff_perpetualPrimality`]  So the failure of (C∞) is exactly perpetual
primality from some stage on, and (C∞) says: *no* Sylvester-type tower seeded at a Euclid
number is prime forever.

That is a statement of the Fermat-numbers type, and it fails for the same reason those are
hard.  The map `Φ₆` has an absorbing fixed point: `0 ↦ 1 ↦ 1`.  A prime that divides one term
of a tower divides no later term.  There is no covering congruence, no periodicity of zero, no
recurrence.  Every tool that proves "every prime divides some term" (periodicity for linear
recurrences, Wilson's theorem for `n!+1`, the bijectivity of `x ↦ 2x+1` for Cunningham chains)
depends on zero being periodic, and here it is not.  Nor does the arboreal Galois theory of the
tower help: the Chebotarev-type input is free (for every level there are primes occupying it),
and the residual gap is a *size* condition on the factorization of one specific integer.
[`exists_large_prime_level_occupied`, `infinitelyManyComposite_iff_witness_proper`]

Consequently every improvement of the trivial coverage bound `S(x) ≥ log log x` on the number
of Euclid–Mullin primes up to `x` is Fermat-hard, since on the perpetual branch the trivial
bound is sharp up to a constant.  Even "the Euclid–Mullin primes have positive density among
primes" is open, and sits strictly above (C∞).  [`coverage_ladder`, `card_misses_ge`]

## 4. Why averaging cannot see it

The natural heuristic is probabilistic.  The multiplier `p_{n+1} mod q` looks random, each
step has probability about `1/(q−1)` of landing on `−1`, and so the walk hits `−1` almost
surely; summing over `q` with countable additivity, MC holds with probability one.  Everything
in this paragraph is true of a random model and false as a method.

**The orbit is one point.**  The decisive obstruction is a pair of periodic multiplier
sequences in `(ℤ/5)^×`: periods `(2,2,3,3)` and `(2,3,2,3)` have identical one-point
multiplier counts in every block of four steps, and only the first ever reaches `−1`.  One-point
population statistics do not determine hitting (the two-point statistics of this pair differ;
the example is an illustration, not a theorem about every statistic).  [`population_does_not_determine_hitting`, Dead End #90]
Its sharper form: multiplier character sums can cancel while walk character sums grow
linearly, so cancellation of the multipliers does not transfer to the walk.
[`mult_cancel_not_walk_cancel`, Dead End #117]  And generation is not coverage: multipliers
`(7,19,7,13,19,13)^∞` generate `(ℤ/5)^×`, show two residue classes at every visited position,
all exceed 5, and never reach `4`.  The reason is general: at position `x` exactly one
multiplier residue, `−x^{−1}`, is fatal, so the walk has the freedom of a full shift on `q−2`
symbols.  [`two_classes_not_coverage`, `death_multiplier_unique`, Dead End #179]

**The population layer is true and useless.**  One can average over the starting point
instead of the step.  The project proved the seed-average law: for a fixed prime `q`, almost
every seed `m` (in natural density) is captured by `q` in the generalized sequence started at
`m`, and the set of seeds that never capture `q` has density zero.  [`almost_all_genmc_density`,
`never_captures_limsup_eq_zero`]  This is a genuine theorem, and it says nothing about the
seed `2`, because a density-zero set may contain the sparse sequence of seeds `P_N` the orbit
actually visits, at no cost.  [Dead End #158]  Worse, the stronger population hypothesis that
would transfer (equidistribution of the prime that selects) is *false*: the least missing prime
dominates the selection statistics.  [`HeadDomination`, Dead End #160]  Even simultaneity in
`q` fails at the population level, because densities are finitely additive.
[Dead Ends #167, #168]

**Nothing else is available.**  Every equidistribution technique in number theory needs one
of independence, multiplicativity, algebraic-geometric structure, or ergodic stationarity.
The Euclid–Mullin multiplier is state-dependent (no independence), the rule `P ↦ P · lpf(P+1)`
is not multiplicative (no Euler product; the "+1" is additive), there is no fixed algebraic
correspondence (the map is not a function of `P mod q`), and there is no invariant measure on
any compactification that sees the orbit.  Model theory, ultraproducts, Loeb measures,
geometric logic, `p`-adic geometry, Zilber–Pink heights, entropy: each was assessed and each
reconstructs the population picture under another name.  [Dead Ends #128, #155, #177, #178,
#182]  The catalogue stands at 182 numbered dead ends, 37 with a Lean witness; it is the most
precise statement of the thesis.

## 5. Why there is no finite certificate of failure either

One might hope the conjecture is false and refutable.  For the *second* Euclid–Mullin
sequence, which takes the largest factor, this is exactly what happened: Cox and van der
Poorten showed `5` is omitted, and Booker showed infinitely many primes are.  The mechanism is
smoothness.  To be the largest factor of `E`, the prime `p` needs `E` to be `p`-smooth, a
finitely checkable condition, and `E ≡ 3 (mod 4)` rules out `E = 5^a`.  Omission is a
*congruence obstruction*: a residue class closed under the dynamics that the orbit never
leaves.

For the least-factor rule the dual condition is roughness, and roughness is not certifiable.
The project proved that no congruence obstruction, at any modulus, can witness a missed prime
for the first sequence, and extended the result to reciprocity invariants with a moving
modulus.  [`no_cvdp_obstruction`, `no_reciprocity_induction_proof`]  The only known way to certify an
omitted prime is closed.  So MC is a `Π₂` statement that computation can neither confirm
(infinitely many infeasible factorizations) nor refute (no finite witness of the known kind).

## 6. The rigid/free dichotomy

Variants locate the conjecture at a boundary.

*Rigid rules are incomplete.*  Over the polynomial ring `𝔽₅[t]`, where every residue-walk
feature is present and Weil's Riemann hypothesis is a theorem, the greedy sequence from the
seed `X` is a perpetual tower of irreducibles and the function-field Mullin conjecture is
**false**.  [`not_ffMullinConjecture_five`]  The reason is a finite-field accident: the
constant `−1/4` has a finite `Φ₆`-orbit modulo `5`.  The failure of the function-field
conjecture along perpetually irreducible paths was found by Kurokawa and Satoh
(Experiment. Math. 17, 2008), who also reported computations supporting the conjecture in
the remaining cases; the Lean theorem is the `p = 5` instance.  Over `𝔽₂[t]` and over `𝔽_p[t]` with
`p ≡ 1 (mod 3)` the composite floor (C∞) is a theorem with explicit constants, and the
conjecture is open and exactly as hard as over `ℤ`.  [`ffGrowthConstant_eq_zero_of_two`,
`ffGrowthConstant_eq_zero_of_one_mod_three`]

*Free rules are complete.*  Booker's steered variant, which may multiply any subset of the
primes in hand, captures every prime; the freedom to choose residues is what the proof uses.

*The greedy rule over `ℤ` is the unique tie-free canonical case.*  There is no symmetry to
exploit (the rule is not equivariant under anything), and no freedom to steer.  Every ring
with more units or a constant field either trivializes the problem or kills it with rigidity.
MC asks whether canonical greedy choice, alone, suffices.  It is the one undecided cell of the
table.

This gives a **litmus test** for proposed proofs: any argument that uses only the walk and its
residues would prove the false statement over `𝔽₅[t]`.  A proof of MC must use the
compositeness of Euclid numbers in characteristic zero.

## 7. What structure the sequence does have

The barriers are sharper for what survives them.

*Frozen facts.*  `E_n ≡ 3 (mod 4)` for all `n ≥ 1`, so every Euclid number has a prime factor
`≡ 3 (mod 4)`; and `E_n ≡ 7 (mod 12)`.  These are the only unconditional positive divisibility
facts, and they say which *class* a factor lies in, never which prime.
[`exists_prime_dvd_euclid_three_mod_four`]

*The splitting law.*  Every prime factor of `E_{n+1}` splits or ramifies in `ℚ(√D_n)`, with
`D_n = 1 − 4c_n`.  This is the cyclotomic constraint `ℓ ≡ 1 (mod 3)` after a prime stage,
generalized to arbitrary stages.  [`isSquare_disc_of_dvd`, `prime_dvd_euclid_succ_mod_three`]
Primes that are eventually non-split are *frozen* and missing, and MC ⟹ NoFrozen ⟹ (C∞) is the
first rung whose content is a splitting condition rather than a size condition.
[`frozen_rung`]  A prime frozen uniformly at one stage forces that stage to be *confined*,
`D_n = −3s²`.  [`confined_of_uniformly_frozen`]

*The step is a CM point.*  `E_{n+1} = Q_n(−1, p_{n+1})` for the principal form
`Q_n = x² + xy + c_n y²`, so the object attached to a step is the order of discriminant `D_n`, a
CM point on the `j`-line, with the weight-one theta series as automorphic side.  The principal
form takes no value below `c_n` off the axis, so a small least factor is a non-principal ideal of
class order at least `log c_n / log q`.  A stage is prime iff `D_n = −3`: the CM point is `ρ`,
`j = 0`, and `Φ₆(x) = N(x − ω)`.  A Sylvester tower is the *constant* CM point `j = 0`, and the
confined stages are its Hecke orbit.  The exceptional locus of the theory is the set of special
points of the `j`-line.  [`euclid_succ_eq_principalForm`, `not_represents_of_lt`,
`disc_eq_neg_three_iff`, `perpetual_disc_eq_neg_three`]  The correspondence is one step deep:
the order changes at every stage, and no automorphic object sees which factor is *least*.

*Second chances.*  A prime can divide a Euclid number, be outranked by a smaller factor, and be
captured later (`139 ∣ E_3 = 13·139`, and `139 = p_9`).  This happens iff the multiplier
product over the intervening window returns to `1` modulo the prime.  MissingFinite, hence MC,
forces infinitely many such second chances among the primes `≡ 3 (mod 4)`: every capture of a
prime `≡ 1 (mod 4)` discards a prime `≡ 3 (mod 4)`, and all but finitely many discarded primes
must return.  So MC cannot hold "on first sight".  Pigeonhole provides, for every missed prime,
windows with product `≡ 1`; what MC needs is a window *anchored at a hit*, and anchoring is
Dead End #90 in another language.  [`missingFinite_implies_secondChance_io`,
`not_mc_of_firstHitCapture`, `exists_window_prod_eq_one`]

*Head rigidity.*  `head(n) ≤ p_{n+2}` (the `(n+2)`-nd prime), every head capture after the
first stage is a composite Euclid number, and MC forces `lpf(E_n) ≤ p_{n+2}` infinitely often:
a prime factor below `(1+o(1)) log E_n`, infinitely often, in a number of up to `2^n` digits.
[`head_le_nth_prime`, `capture_composite`, `mullin_implies_lpf_le_nth_prime_io`]

## 8. What a proof would have to be

The necessary conditions assemble into screens.  A route to MC must (1) produce a *positive*
divisibility fact about a prescribed prime; (2) use characteristic-zero input, or it proves
the false statement over `𝔽₅[t]`; (3) be single-orbit; (4) yield (C∞) as a corollary; and (5)
produce, for infinitely many primes, a multiplier window with product `≡ 1` anchored at a
hit.  No proposed route passes all five, and most fail (3) by construction.

The conjecture these constraints point at is a dichotomy, uniform in the seed:

> **Dichotomy conjecture.**  For every seed `m`, the generalized Mullin conjecture holds for
> `m` iff infinitely many of its Euclid numbers are composite.  [`DichotomyConjecture`]

The easy direction is proved for every seed, and the algebraic part is exactly the tower: an
orbit whose multiplier is a polynomial in the Euclid number is a Sylvester tower.
[`sgrowth_eq_zero_of_genMC`, `algebraic_multiplier_implies_tower`]  If the conjecture is
true, the only obstruction to capturing every prime is algebraic, the constant CM point `j = 0`,
and MC is a 0/1 law for a single orbit: a "special points versus generic orbit" theorem with
the shape of André–Oort but without a symmetry group.  Nothing of that kind exists.

One more constraint is logical.  MC is a geometric sequent, so a proof from geometric axioms
would be constructive and would come with a primitive-recursive bound on the capture time of
each prime.  The single ineffective step in the present theory is Karamata's Tauberian theorem
in the population layer, which the orbit never uses.  A proof of MC may well be effective, and
then it would say something about the least prime factor of *one* rough integer in a known
class, a kind of statement number theory has never produced.

## 9. Closing

Mullin's conjecture has no consequences and needs no excuse.  Its claim on attention is that
its difficulty is *measured*: immune to averaging by proof, uncertifiable in the negative by
proof, Fermat-hard by proof, and the unique canonical case of a dichotomy whose other cells are
decided.  Euclid's remark, iterated greedily, produces the simplest deterministic orbit about
which number theory can say nothing, and it says nothing for reasons that can be written down.
Whoever proves the conjecture will have learned how to control one orbit.  That is the prize;
the sequence is only the first place to spend it.

---

## Appendix: Lean anchors

| statement | file (under `EM/`) | declaration |
|---|---|---|
| walk hits `−1` iff `q ∣ E_n` | `Group/Core.lean` | `walkZ_eq_neg_one_iff` |
| MC ⟺ head captured i.o. / head → ∞ | `Population/HeadDynamics.lean` | `mullin_iff_head_captured_io`, `mullin_iff_head_tendsto` |
| every prime hit finitely often | `Population/AdelicShadow.lean`, `Population/SecondChance.lean` | `hits_finite`, `hittingSet_finite_of_prime` |
| CME ⟺ MC | `CME/Equivalences.lean` | `cme_iff_mc` |
| the ladder MC ⟹ RD ⟹ (S) ⟹ (C∞) | `Population/WeakMullin.lean`, `Population/CompositeFloor.lean` | `mc_implies_rd`, `exists_small_minFac_of_reciprocalDivergence`, `infinitelyManyComposite_of_small_minFac` |
| growth constant complete invariant | `Population/DefectTelescope.lean` | `infinitelyManyComposite_iff_growthConstant_eq_zero`, `growthConstant_pos_iff_perpetualPrimality` |
| arboreal input free, gap is size | `Population/ArborealTower.lean` | `exists_large_prime_level_occupied`, `infinitelyManyComposite_iff_witness_proper` |
| coverage ladder, `S(x) ≥ log log x` | `Population/CoverageLadder.lean`, `Population/GapPrinciple.lean` | `coverage_ladder`, `card_misses_ge` |
| #90, #117, #179 witnesses | `Meta/OrbitBarrier.lean` | `population_does_not_determine_hitting`, `mult_cancel_not_walk_cancel`, `two_classes_not_coverage`, `death_multiplier_unique` |
| seed-average law | `Population/AlmostAllDensity.lean` | `almost_all_genmc_density`, `never_captures_limsup_eq_zero` |
| no congruence / reciprocity invariant | `Obstruction/NoInvariant.lean`, `Reciprocity/NoReciprocityInvariant.lean` | `no_cvdp_obstruction`, `no_reciprocity_induction_proof` |
| FF-MC false over `𝔽₅[t]` | `FunctionField/StableTower.lean` | `not_ffMullinConjecture_five` |
| FF composite floors | `FunctionField/CompositeFloors.lean` | `ffGrowthConstant_eq_zero_of_two`, `ffGrowthConstant_eq_zero_of_one_mod_three` |
| frozen facts mod 4 | `Population/ClassInfinitude.lean` | `exists_prime_dvd_euclid_three_mod_four`, `prime_dvd_euclid_succ_mod_three` |
| norm identity, splitting law, frozen rung | `Population/QuadraticStep.lean` | `euclid_succ_eq_norm`, `isSquare_disc_of_dvd`, `frozen_rung` |
| uniformly frozen ⟹ confined | `Population/UniformFreezing.lean` | `confined_of_uniformly_frozen` |
| the step as a CM point | `Population/CMPoint.lean` | `euclid_succ_eq_principalForm`, `not_represents_of_lt`, `disc_eq_neg_three_iff`, `perpetual_disc_eq_neg_three`, `mullin_implies_nonprincipal_least_factor` |
| second chances | `Population/SecondChance.lean` | `missingFinite_implies_secondChance_io`, `not_mc_of_firstHitCapture`, `exists_window_prod_eq_one`, `secondChance_tower_criterion` |
| head rigidity | `Population/HeadDynamics.lean` | `head_le_nth_prime`, `capture_composite`, `mullin_implies_lpf_le_nth_prime_io` |
| dichotomy conjecture and its algebraic part | `Population/Dichotomy.lean`, `Population/QuadraticStep.lean` | `DichotomyConjecture`, `algebraic_multiplier_implies_tower`, `sgrowth_eq_zero_of_genMC` |
| head domination (PE false) | `Population/HeadDomination.lean` | Dead End #160 |

Dead-end numbers refer to `tools/dead_ends.tsv`, the single source of truth, regenerated
into `EM/Meta/DeadEnds.lean` and the paper appendix.
