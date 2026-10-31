# Reasoning by recurrence: second chances in the Euclid–Mullin sequence (2026-10-25)

Status: theory memo with Lean (`EM/Population/SecondChance.lean`, 0 sorry, namespace
`SecondChances`).  Session 322.  Everything stated as a theorem below is machine-checked;
the rest is marked question or remark.

## 0. The way of reasoning

Every statement of the form "every prime divides some term of the sequence `(a_n)`" that
mathematics knows how to prove uses one of four mechanisms:

| mechanism | example | what makes it work |
|---|---|---|
| **periodic zero** | Fibonacci, Lucas, Cunningham chains `p, 2p+1, 4p+3, …` | the step map is a *bijection* mod `p`, so the orbit of `0` is periodic and returns to `0` (for a Cunningham chain the `(p−1)`-th term is `≡ 0 mod p`) |
| **complete product** | `n! + 1` (Wilson) | the term is the product of *all* residues |
| **steering** | Booker's subset-product variant | freedom to choose the next factor among many candidates |
| **population** | a.a. seeds capture `q` (seed-average law) | averaging over the starting point |

The Euclid–Mullin sequence has none of them: the state map `P ↦ P · lpf(P+1)` is not a
function of `P mod q`; `P_n` is the product of a *sparse* set of residues; the rule is
deterministic; and one orbit is not a population (Dead End #90).  On a Sylvester tower
`E_{n+1} = Φ₆(E_n)` the first mechanism fails in the strongest way: `0 ↦ 1 ↦ 1` under `Φ₆`, so a
prime dividing one tower term divides no later one.  That absorbing fixed point is the source
of the Fermat-hardness of `(C∞)` (`docs/analysis/compositeness_2026-09-02.md`).

The new angle: the EM sequence is **not** a tower.  At a composite stage the rule *discards* a
cofactor `c_n = E_n / lpf(E_n)`, and the primes of the cofactor are not absorbed — they can
divide later Euclid numbers, and they can be captured later.  So the only recurrence the
problem has is the recurrence of *discarded* primes.  This memo studies that recurrence as an
object in its own right and proves that **MC forces it infinitely often**.

Vocabulary (all in `SecondChance.lean`):

* `r` is **hit** at stage `n` if `r ∣ E_n` (`HittingSet r`, from `HittingSetStructure.lean`);
* `r` is **captured** at stage `m+1` if `r = seq (m+1) = lpf E_m`;
* `r` gets a **second chance** (`SecondChance r`) if it is hit at some stage `n` and captured
  at a stage `m + 1` with `m > n`: it divided a Euclid number, was outranked by a smaller
  factor, and was chosen later anyway.

The orbit of `2` has one visible instance: `E_3 = 1807 = 13 · 139`, the rule takes `13`, and
`139 = p_9`.  The intervening multipliers satisfy `13 · 53 · 5 · 6221671 · 38709183810571 ≡ 1
(mod 139)` (checked by hand: `13·53·5 ≡ 109`, `6221671 ≡ 31`, `109·31 ≡ 43`,
`38709183810571 ≡ 97`, `43·97 = 4171 ≡ 1`).

## 1. Hits are finite for every prime

`hittingSet_finite_of_prime`: every prime has a finite hitting set.  For a missed prime this
is the guardian argument of `HittingSetStructure.lean` (`hittingSet_finite`); for a captured
prime `seq k` it is immediate, since `seq k ∣ P_n` for `n ≥ k` (`not_dvd_euclid_of_captured`,
`lt_of_mem_hittingSet_captured`).  Consequently any *finite* set of primes is hit at only
finitely many stages in total (`exists_stage_no_hit`), which is the bookkeeping behind
everything below.

`secondChance_iff_two_hits`: `SecondChance r ⟺ r` is captured and hit at least twice (the
capture stage is one hit).

## 2. A second chance is a return to the identity

`secondChance_window`: if `r ∣ E_n` and `seq (m+1) = r` with `n < m`, then

    seq (n+1) · seq (n+2) ⋯ seq m ≡ 1  (mod r).

This is `HeadDynamics.dvd_euclid_iff_prod_mul_eq_one` read at the capture.  So a second chance
is a **return of the multiplier walk to the identity**, started at a stage where the position
walk sits at `−1`.  It is a different shape from a first hit (position walk reaching `−1`
from `2`): the window starts at the identity and must come back to it.

## 3. The theorem: MC forces infinitely many second chances

**Theorem** (`missingFinite_implies_secondChance_io`).  If only finitely many primes are
missed, then for every `N` there is a prime `r ≥ N`, `r ≡ 3 (mod 4)`, with `SecondChance r`.
In particular (`mc_implies_secondChance_io`) MC forces infinitely many second chances, and
the set of second-chance primes is infinite (`secondChance_infinite_of_missingFinite`).

Proof.  (i) Under MissingFinite all but finitely many primes `≡ 1 (mod 4)` are captured, at
arbitrarily late stages (`exists_capture_one_mod_four_ge`, Dirichlet via
`UniformFreezing.exists_prime_gt_mod`).  (ii) At a stage `k` whose multiplier `q = seq (k+1)`
is `≡ 1 (mod 4)`, the Euclid number `E_k ≡ 3 (mod 4)` has a prime factor `r ≡ 3 (mod 4)`,
necessarily `≠ q` (`exists_cofactor_prime_three_mod_four`, from
`EuclidClasses.exists_prime_dvd_euclid_three_mod_four`).  (iii) Choose `k` beyond the last hit
of every missed prime and of every prime `< N` (`exists_stage_no_hit`).  Then `r` is neither
missed nor small, so `r` is captured; it divides `E_k` and is not `seq (k+1)`, so it is
captured strictly later (`secondChance_of_dvd_of_captured`).  ∎

The mechanism is worth stating in words: **every capture of a prime `≡ 1 (mod 4)` discards a
prime `≡ 3 (mod 4)`**, and under MC every discarded prime must come back.  The theorem is the
first *positive* statement about what MC does to the cofactors.

**Corollary** (`not_mc_of_firstHitCapture`, `not_missingFinite_of_firstHitCapture`).  Define
`FirstHitCapture` := only finitely many primes get a second chance.  Then FirstHitCapture
refutes MissingFinite and MC.  *MC cannot hold on first sight.*

## 4. Placement: a fifth screen

The frontier box in `paper/why_its_hard.tex` lists four screens a route must pass.  §3 adds
a fifth, which is more concrete than the first:

> **Screen 5.**  A route to MC must produce, for infinitely many primes `r`, a window of
> consecutive multipliers whose product is `≡ 1 (mod r)` and which is *anchored at a hit*
> (`r ∣ E_n` at the start of the window), the window ending with `r` as the least factor.

Why this is a real screen and not a restatement:

* **Free windows are free.**  `exists_window_prod_eq_one`: for every missed prime `r` and
  every start `a`, pigeonhole on the `r` positions `P_a, …, P_{a+r−1}` in the `r − 1` nonzero
  residues gives `i < j` in `[a, a + r)` with `seq (i+1) ⋯ seq j ≡ 1 (mod r)`.  (This is the
  Davenport constant of a cyclic group in the orbit's language.)  So "the multiplier walk
  returns to the identity" is *always* true somewhere in every block of length `r`.
* **Anchored windows are the problem.**  What is needed is `i` with `r ∣ E_i`, i.e. the
  position walk at `−1`, and this is exactly where #90 lives: the witness sequences that
  avoid `−1` forever still have free windows.  The screen names the shape of the missing
  positive divisibility fact: not "the walk hits `−1`" but "the walk, having hit `−1`, sees
  the multiplier product return to `1` before a smaller prime is chosen".
* **Litmus test** (`𝔽₅[t]`, seed `X`): every Euclid polynomial is irreducible, there are no
  cofactors, no second chances, and MC is false.  A proof of screen 5 must therefore use
  compositeness of Euclid numbers (screen 1 and screen 4 in one), and it is not transplantable.

## 5. Second chances along a run of prime Euclid numbers are `Φ₆`-events

`euclid_succ_eq_phi6_of_prime`, `euclid_eq_phi6_iter_of_prime_run`: if `E_{n+1}, …, E_{m−1}`
are prime then `E_m = Φ₆^{m−(n+1)}(E_{n+1})` in any commutative ring.
`euclid_succ_eq_one_sub_seq_of_dvd`: after a hit `r ∣ E_n`, `E_{n+1} ≡ 1 − seq (n+1) (mod r)`.
Hence

**`secondChance_tower_criterion`.**  With `r ∣ E_n` and a run of prime Euclid numbers from
`n+1` to `m−1`: `r ∣ E_m ⟺ Φ₆^{m−(n+1)}(1 − seq (n+1)) = 0` in `ZMod r`; in particular the
residue `1 − seq (n+1)` lies in `BackwardOrbit.PreZero r` (`mem_preZero_of_dvd_of_prime_run`).

So inside a tower segment the anchored return is **autonomous**: it is the backward-orbit
tree of `0` under the Sylvester map, the object of `BackwardOrbit.lean`, evaluated at the
residue of the *first* multiplier after the hit.  Across a composite stage the cofactor
re-enters (`E_{j+1} = p² c − p + 1`, `QuadraticStep.lean`) and the map is no longer
autonomous.  This matches the picture that the only non-rigid part of the dynamics is the
cofactor.

## 6. Eventually `≡ 1 (mod 4)` multipliers

The same cofactor supply, run without the capture hypothesis, gives a rung that was claimed
in memos but not on file:

* `not_classInfinitude_three_mod_four_implies_missing_io`: if the multipliers are eventually
  `≡ 1 (mod 4)`, infinitely many distinct primes `≡ 3 (mod 4)` are missed (each late `E_n`
  has one, it cannot be captured before `n` since it divides `E_n`, nor after since late
  multipliers are `≡ 1 (mod 4)`; distinctness from finiteness of hits).
* `missingFinite_implies_classInfinitude_three_mod_four`: MissingFinite ⟹ CI(3 mod 4).  (The
  direct Dirichlet route also works; this proof goes through the cofactor supply.)

So CI(3 mod 4) sits under MissingFinite on the coverage ladder, and ¬CI(3 mod 4) is not just
`(C∞)` (as on file) but infinite missing.

## 7. What this does and does not do

* It does not attack MC.  Every theorem here is a *consequence* of MC or MissingFinite, or
  unconditional bookkeeping.  No mechanism for anchored returns is proposed.
* It gives a new *necessary condition* with a definite shape (screen 5), the first statement
  about cofactor primes under MC, and a rung (`FirstHitCapture ⟹ ¬MC`) that is not a residue
  statement about one prime but a global statement about the capture order.
* The ledger identity of `HittingSetStructure.hitting_ledger_sum` can now be read as:
  `Σ_n (ω(E_n) − 1)` = (second-chance pairs) + (hits of missed primes); under MissingFinite
  the second summand is finite, so **MissingFinite ⟹ `Σ_n (ω(E_n) − 1) = ∞ ⟺ (C∞)` with all
  but finitely many of the discarded prime factors eventually captured** (paper remark; the
  prime-power case `E_n = p^k`, `k ≥ 3` odd, is the only way a composite stage discards no new
  prime, and it is not excluded by anything on file).

## 8. Questions

1. **Second-chance conjecture (SCC)**: every prime that divides some cofactor is captured.
   MC ⟹ SCC.  SCC does not imply MC (a prime never hit is not covered).  SCC is the first
   named target whose content is *recurrence to the identity* rather than *hitting `−1`*;
   the `𝔽₅[t]` litmus makes it vacuous there, so it is not a mechanism, but it is the right
   test statement for any idea about anchored windows.
2. Is the number of second-chance primes `≤ x` under MC comparable to `π(x; 4, 1)`?  Each
   capture of a `1 (mod 4)` prime discards a `3 (mod 4)` prime; distinct captures may discard
   the same prime, but each prime is discarded at most `π(r)` times
   (`hittingSet_ncard_le_appearing`).  So the count is `≫ #{captures ≡ 1 (4)} / max hits`; a
   clean lower bound would need a bound on repeated discards.
3. On a tower segment the criterion is `1 − seq (n+1) ∈ PreZero r` at a prescribed level.
   `BackwardOrbit.realizedLevels_finite` says the levels are a bounded resource mod `r`; so
   a prime discarded just before a long tower segment has its second chance only within the
   first `depth(r)` steps of the segment.  Is there a *lower* bound on second-chance delays?
   (The orbit of `2` shows delay 6 for `139`.)
4. The same construction with other characters: at a capture of `q` with `χ(q) = 1` for a
   quadratic character `χ` with `χ(E_n) = −1` the cofactor carries a prime with `χ = −1`.
   `χ_4` is the only character with `χ(E_n)` constant (`E_n ≡ 3 (mod 4)`); for `χ_8` the sign
   of `χ(E_n)` is the frozen 2-deleted walk (`ClassThreeModFour.lean`).  Which other
   supplies are unconditional?
