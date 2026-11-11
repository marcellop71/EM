# Analytic theory and the Mullin conjecture over ℤ

Session 325, 2026-11-08. Companion to `feedback_selection_2026-11-08.md` and
`catalogue_sweep_2026-11-07.md`. Question asked: *which analytic theory could move MC forward
over ℤ?* The answer is organised around one observation: every theorem analytic number theory
has produced in the Euclid–Mullin family came with a **family to average over**, and the greedy
orbit over ℤ has none (Dead End #90, `OrbitBarrier.population_does_not_determine_hitting`).

Verdict in one line: no existing analytic theory reaches the orbit; the one that *fits* its
autonomous part (arboreal Chebotarev, Odoni–Jones) yields a quantitative necessity principle,
proved today in its elementary half; the analytic theorems worth adding to the record are about
variants, and they calibrate rather than attack.

## 1. Where analytic number theory has produced theorems in the EM family

| theorem | analytic input | family averaged over | why it stops at greedy |
|---|---|---|---|
| Booker 2016: a divisor-steered Euclid sequence contains every prime; Booker–Pomerance 2017: squarefree smooth numbers in every residue class (Bagshaw 2022 over `𝔽_q[X]`, `q ≥ 7`) | distribution of smooth numbers in residue classes | the `2^n` subproducts `d ∣ P_n` | greedy uses `d = P_n` only; equidistribution of subset products is *generation*, and generation is not coverage (#90 witness `B`, #179) |
| Cloitre/Rowland lcm recurrences: increments are `1` or prime for density-one indices (arXiv:2510.18891) | Bombieri–Vinogradov; full statement needs strong Linnik | the index `n`, at linear scale | EM's index set is the orbit itself, one integer per `n`; the increment is `lpf` of one specific integer, not the least prime in a progression (sweep §2–§3) |
| seed-average law, a.a. `GenMC(q)` (`AlmostAllDensity.almost_all_genmc_density`) | Mertens in APs, box sieve, Karamata | seeds `m ≤ X` | population ≠ orbit (#90); range `Q(X) → ∞` ineffective |
| Odoni 1985, Jones 2008: the primes dividing some term of the Sylvester orbit have density `0` (`O(π(x)/log log log x)`), for any integer starting point | Chebotarev in the wreath-product tower of `x² − x + 1` | primes `q`, over a fixed tower | the actual orbit leaves the tower at every deviation; what survives is the necessity principle of §3 |

The pattern is exact: smooth-number theory averages over subproducts, BV over indices, the
sieve over seeds, Chebotarev over primes against a fixed tower. MC is a statement about one
subproduct, one index sequence, one seed, and a tower that is re-rooted at every deviation.

## 2. Single-object analytic theories, and the wall each meets

* **Baker / subspace / Ridout** (the only analytic theory of *specific* integers): gives lower
  bounds on the *largest* prime factor and on sizes (Stewart on `2^n − 1`); MC needs the *least*
  prime factor small, and the support of `E_n` is not fixed. Closed as #177.
* **GRH-Chebotarev à la Hooley (Artin's conjecture)**: reaches one object across all primes
  because the condition at `q` is Frobenius in a *fixed* Galois extension depending on the object
  and a parameter. For EM, `q ∣ E_n` is a fixed-extension condition only along autonomous runs,
  and autonomy is take-all (`FeedbackSelection.sel_cast_eq_of_autonomous`). Nothing analogous
  to Heath-Brown's cross-base coupling exists for seeds (analogy map, 2026-08-20).
* **Sieve / Buchstab / rough numbers**: `E_n` is `p`-rough for every `p ≤ lpf(E_n)`; the
  distribution of `lpf` on rough numbers is a population statement. Shanks's heuristic lives here.
* **Prime gaps**: `¬(C∞)` means the tail is a Sylvester tower, `E_n` the nearest integer to
  `A^{2^n}` for a real `A` (Aho–Sloane). Refuting "all prime" for such a sequence is a
  Legendre-gap-type question, open even under RH; Mills's constant shows the exponent-3 analogue
  is *true*, so no general gap theorem can do it. This is the Fermat shape of (C∞).
* **Additive combinatorics / expansion**: products of random words in a generating set
  equidistribute; the orbit is one word. #179 (`two_classes_not_coverage`).
* **Fourier / one-horizon / large sieve**: restatements of residue control of this orbit
  (`cme_iff_mc`); none says how it passes screens 1, 2 or 4 (frontier box).

## 3. What was added: the ℤ-twin of the `𝔽₂` threshold

`FeedbackSelection.lean` §5. Let `R_k := {q : ∃ w ∈ ℤ/q, sylvWalk^[k] w = −1}` be the
level-`k` primes of the Sylvester tree (`ArborealTower.levelPrimes_infinite`: each `R_k` is
infinite, unconditionally).

* `level_prime_of_capture_after_run`: a prime captured after `k` residue-autonomous stages lies
  in `R_k`. (`k = 1` is `phi3_root_of_capture_after_run`; over `𝔽₂` the same inclusion is the
  exact statement `k < 2^{v₂(d)}`, `AutonomousThreshold.one_mem_sylv_iterate_image_iff`.)
* `deviation_within_of_capture`: a captured prime outside `R_k` deviates at one of the `k`
  stages before its capture; `mc_deviation_within`: under MC this holds for every prime
  `q ≥ 5` outside `R_k` (or the capture is among the first `k` stages).
* `stageAutonomous_iff_dvd_cofactor_sub_one`, `finite_stageAutonomous_of_cofactor_ne_one`:
  stage `n` is autonomous modulo `q` iff `q ∣ c_n − 1`; at a composite stage only finitely many
  primes (at most `log₂ E_n`) see an autonomous stage. Under (C∞) deviation is the generic state.

The analytic input, cited not proved (Chebotarev is not in Mathlib): the natural density
`δ_k` of `R_k` is the proportion of elements of the arboreal Galois group of the `k`-th
iterate of `x² − x + 1` with a fixed point. `δ_1 = 1/2` (primes with a primitive cube root of
unity, Dirichlet); Odoni's theorem that the iterates of `x² − x + 1` have the full wreath
product as Galois group gives `δ_2 = 3/8` and `δ_k → 0`; Jones (2008) proves the density-zero
statement for the prime divisors of the orbit of any integer under `x² − x + 1`, which is the
`k → ∞` limit of the same count. `ArborealTower.ArborealChebotarev` records the positive half
(`δ_k > 0`); the two-sided statement `0 < δ_k → 0` is the honest input.

Consequence, modulo that input: MC forces all but a density-`δ_k` set of primes to be
captured within `k` stages of a deviation, for every `k`. This is weak (note added 2026-11-10):
at a composite stage every prime outside the finitely many dividing `c_n − 1` deviates, so the
statement constrains a capture only when the `k` stages before it are prime stages (or one of
those coincidences). Its content is the classical one: a prime that divides a Euclid number
at the end of a run of `k` prime stages is a level-`k` prime. Over `𝔽₂` the same statement is
exact with cut-off `2^{v₂(d)}`. In both rings it is necessity: it says where the feedback must
be, never that it arrives.

## 4. What an analytic breakthrough would have to be

A theorem about the least prime factor of **one** integer of the form `P + 1` with `P` fully
factored (the Pocklington class), asserting a *positive* divisibility by a prescribed prime
(screen 1), using characteristic-zero input (screen 2, the `𝔽₅[t]` litmus test and
Kurokawa–Satoh), single-orbit (screen 3) and implying (C∞) (screen 4). Analytic number theory
has no theorem of that type; its only single-integer tool (Baker) produces upper bounds on
smoothness, the wrong sign. The sweep's conclusion stands: the first provable member of the
lpf-recurrence class is at linear scale (strong Linnik), and MC has no conditional proof under
any named hypothesis.

## 5. Recommendation

1. Stop looking for an analytic *route*; the map above is closed by theorems at every entry.
2. Two analytic theorems would complete the record, both about variants: the steered
   completeness theorem (Booker 2016) over ℤ, and its `𝔽₂[X]` twin, which is open and is where
   Bagshaw's method stops. These are the analytic anchors of the taxonomy in
   `feedback_selection_2026-11-08.md` §4.
3. State `0 < δ_k → 0` as the arboreal input (extending `ArborealChebotarev`) when Chebotarev
   reaches Mathlib; until then the citation carries it.
4. The paper paragraph proposed in the sweep (§3, "Rowland–Mullin principle", next to "Does RH
   imply MC?") is where this calibration belongs.
