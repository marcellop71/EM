# Catalogue sweep: what direction, if any, is missing (2026-11-07)

Session 324, second half.  Question (user): go across the dead ends and figure out which
direction could be missing.  Source: `tools/dead_ends.tsv` (182 numbers, 172 entries, 40 with a
Lean witness), the memos under `docs/analysis/`, the frontier box of `why_its_hard.tex`.  One
literature check (Rowland / Cloitre recurrences), the reading item left open by the logic memo
(§8.1, §8.8 item 1).  No computation.

**Verdict.**  There is no missing *mechanism*.  The catalogue is exhaustive on techniques, and
not merely by accumulation: four theorems about proof strategies explain the pattern
(§1).  What the catalogue did not contain is (a) the linear-scale calibration, now filled and
sharper than expected (§2); (b) a statement of the conditional landscape — MC has no known
conditional proof under any *named* conjecture, and the linear-scale cousins show why
(§3); (c) a handful of unformalised language targets (§4); and (d) one direction closed by
policy rather than mathematics (§5).

---

## 1. The shape of the catalogue

By mechanism (counting entries, aliases included):

| mechanism | entries | how they die |
|---|---|---|
| character sums / equidistribution of the walk (CCSB, CME, Dec, HOD, large sieve, BV, Linnik, Halász, Weil) | ≈ 60 | reduce to CME, and `cme_iff_mc` (#178, #93, #110): restatements |
| ergodic / Markov / spectral (Doeblin, Furstenberg, Birkhoff, spectral gap, entropy, mixing) | ≈ 12 | #90: population statistics do not determine one orbit; walk is absorbing, not mixing |
| additive combinatorics (Cauchy–Davenport, Kneser, Littlewood–Offord, expanders, zero-sums) | ≈ 8 | generation ≠ coverage (#130, #140, #179) |
| sieve / rough numbers / level of distribution | ≈ 15 | scale mismatch (#96, #108, #111, #154) |
| algebraic receptacles (Chebotarev, Kummer, L-functions, Iwasawa, p-adic, heights, ZP, CM) | ≈ 15 | the walk is torsion data invisible to every height and every Galois object (#135, #152, #177, #182) |
| population / ensemble bookkeeping applied to the orbit | ≈ 25 | #90 again, or vacuous (#158, #169, #172, #173) |
| logic / nonstandard / model theory | ≈ 5 | conservative (#155, #171) |
| growth / compositeness | ≈ 8 | Fermat-shaped core: (C∞) is open at the first rung (#174, #178) |
| computation | 3 (MR) | excluded by rule |

Four theorems make the exhaustion structural rather than historical:

1. `OrbitBarrier.population_does_not_determine_hitting` — two walks with identical multiplier
   statistics, one hits `−1`, one never does.  Kills every mechanism whose input is a
   statistic of the multipliers (rows 1, 2, 6).
2. `NoInvariant.no_cvdp_obstruction` — no propagating union of residue classes blocks a prime.
   Kills every congruence-shaped *disproof* (row 3, #143, #150, #151).
3. `SeedCapture.genSeqAvoid_ne_avoided` (#171) — the whole sure layer is satisfied by a
   dynamics that misses `q` by construction.  Kills every argument from the proved layer alone
   (rows 6, 7).
4. `GreedyRigidity.eq_of_itinerary_eq` (2026-11-07) — the branch determines its seed, so no
   group acts on it.  Kills the amplification / generic-object family (#180–#182).

Every entry in the catalogue is an instance of one of these four, or a refutation (SF, 31
entries), or a collapse to MC (CO, 28 entries).  A new technique that is not an instance would
have to produce a positive divisibility fact about a prescribed prime from data that is
neither a multiplier statistic, nor a congruence invariant, nor a theorem of the sure layer,
nor an action on seeds.  I do not know of a branch of mathematics whose statements have that
form; the screening test of `why_its_hard.tex` is the same demand.

## 2. The linear-scale calibration (reading item executed)

The logic memo (§8.1) asked, as its first follow-up, whether "every prime appears" is *proved*
for any lpf-driven deterministic recurrence, in particular for Rowland's sequence
`a(n) = a(n−1) + gcd(n, a(n−1))`, `a(1) = 7`, which lives at linear scale where sieve methods
are at full strength.  Status, from the literature (checked 2026-11-07):

* **Rowland (2008).**  Proves the differences are always `1` or prime.  Does not prove that
  every odd prime appears.
* **Chamizo–Raboso–Ruiz-Cabello, "On Rowland's sequence" (EJC 18 (2011)).**  Prove that
  certain sequences in the family contain infinitely many primes and characterise the finite
  runs of consecutive prime differences.  "Every odd prime appears" is **open**.
* **Ruiz-Cabello (arXiv:1504.05041), the `lcm` variant (Cloitre's sequence).**  Even the
  *weaker* statement "every increment is `1` or prime" is open; the paper shows it is
  "connected to a strong version of Linnik's theorem", unproved.
* **Cloitre, "Primes in LCM recurrences" (arXiv:2510.18891, v3 2026).**  Proves the increment
  conjecture for a set of indices of **asymptotic density one**, by Bombieri–Vinogradov; states
  that a complete proof "requires a strengthening of Linnik's theorem on the least prime in an
  arithmetic progression that lies beyond current reach"; a related variant is tied to twin
  primes and handled only under a detection hypothesis.

So at linear scale the problem has **exactly the two-layer structure of this repository**: the
density-one (population) statement is a theorem by the standard mean-value machinery
(Bombieri–Vinogradov there, Mertens/Karamata here, `almost_all_genmc`), and the pointwise
statement needs "the least prime in a prescribed class is small", a Linnik-type statement with
an explicit exponent that no current method gives.  This is the demand of logic memo §8.7
("the least prime factor of one rough integer in a known class") met one level down, where
the integer is in a progression rather than a doubly-exponential sequence.  Two consequences:

1. **"Selection, not size" is now a calibrated fact, not a thesis.**  Removing the size
   obstruction entirely (linear scale, full sieve strength, Bombieri–Vinogradov available) does
   not remove the pointwise wall.  Reference calibration for the paper's hardness section.
2. **No mechanism is available for transfer.**  There is no proven "every prime appears" for
   any lpf-driven recurrence; the first one, if it comes, will be a least-prime-in-progression
   theorem, whose EM analogue would be a least-prime-factor theorem for one integer — the
   screen every route fails.  Not a route; a closure of the reading item.

## 3. The conditional landscape: no named conjecture implies MC

`why_its_hard.tex` records that RH/GRH do not imply MC (population statements; the
function-field model has RH as a theorem and the orbit statement stays open).  The sweep
sharpens this to a classification of what *would* be needed, using §2 as the contrast:

* At linear scale, a **named, believed** conjecture (Linnik with explicit exponent, a
  statement about *all* progressions) decides the pointwise problem, because the increment of
  the recurrence is "the least prime in a progression", a population object evaluated at the
  current index.
* For EM the increment is `lpf(E_n)`, the least prime factor of one specific integer.  No
  named conjecture controls the least prime factor of a specific integer — and none can, since
  some `E_n` may be prime; MC does not need `lpf(E_n)` small, it needs `lpf(E_n) = q` at some
  `n`, an existence statement over the sparse index set `n` for which only the sequence itself
  supplies candidates.  Named existence conjectures (Bunyakovsky, Schinzel, Bateman–Horn)
  cover polynomial values, not lpf-driven recurrences; the only hypotheses that imply MC are
  EM-specific and collapse to it (the 28 CO entries; `cme_iff_mc`).

Hence: **MC has no known conditional proof under any standard conjecture, and the sweep gives
the structural reason.**  The only way to put MC under a believed hypothesis is to *name* a
new one — a "Rowland–Mullin principle": every lpf-driven recurrence of the class
`P ↦ P · lpf(aP + b)` / `s ↦ s + lpf(s) − 1` captures every admissible prime — whose
linear-scale instances are the only ones with a foreseeable proof route (strong Linnik).  That
is conjecture-making, and the honest value is organisational: it places MC in a class whose
first proved member would be a Linnik-type theorem.  Candidate paragraph for
`why_its_hard.tex` next to "Does the Riemann Hypothesis imply MC?".

## 4. Unformalised language targets (not routes)

* Profinite classification of the closed invariant sets of the greedy map on `Ω`
  (logic memo §7.1) and the min/max dichotomy as profinite continuity (§7.2).
* Presburger extension of the No-Invariant Theorem (logic memo §3A).
* `UltrafilterHull.lean`: ω-limit set inside the singular set, `GenMC ⟺ ω-limit = {0}` (§3B).
* The reduction-theory reading of greedy (equivariance memo §2.3).

Each is a theorem that states an existing wall in a new language.  None passes the screens.

## 5. The direction closed by policy

The three MR entries (#1–#3) and the rule "proofs, not computation" exclude *anatomy*: the
empirical structure of the actual sequence (which primes are captured when, the residue
patterns of the cofactors, the frozen-symbol statistics, CI(3 mod 4) along the known terms).
This is the only closure in the catalogue that is a decision rather than a theorem.  The
memos agree that any disproof must be anatomical (No-Invariant Theorem) and that
CI(3 mod 4) is the statement to test any mechanism on first (Euclid memo §14.5).  If the rule
is ever relaxed, that is where computation would be informative: not to "verify MC further",
but to look for the anatomy of a frozen prime or of a long `≡ 1 (mod 4)` multiplier run.
Recorded so that the choice is explicit.

## 6. Summary for the story

The catalogue is complete on mechanisms, for structural reasons (four theorems).  The missing
piece was external: the linear-scale lpf recurrences, where size is no obstruction and the
pointwise statement is still open and Linnik-shaped.  That calibration and the conditional
landscape (§3) belong in `why_its_hard.tex`; nothing here opens a route.
