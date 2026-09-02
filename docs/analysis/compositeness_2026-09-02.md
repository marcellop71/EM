# Compositeness of Euclid numbers — a dedicated memo (2026-09-02)

Scope: everything the project knows, can prove, and cannot prove about the factorization of the
Euclid numbers `E_n = P_n + 1` of the Euclid–Mullin sequence, organised around one thesis.  Lean:
`EM/Population/HeadDynamics.lean`, `EM/Population/ClassInfinitude.lean`,
`EM/Population/{DefectTelescope,CompositeFloor,SylvesterTower,AutonomousBranch,GenericTower}.lean`,
`EM/FunctionField/{StableTower,CompositeFloors,CharTwo,CharThree}.lean`.  Companion:
`logic_routes_2026-09-01.md` §§9–18.

## 0. Thesis

**Mullin's conjecture is itself an extremal compositeness statement.**  Let `head n` be the least
prime not yet selected (the least missing prime).  The next multiplier is a missing prime, so

    lpf(E_n) = seq(n+1) ≥ head n        for every n,

and the head is captured exactly when equality holds.  Then (all in Lean, `HeadDynamics`):

    MC ⟺ head n → ∞ ⟺ lpf(E_n) = head n infinitely often ⟺ ∃ f, ∀ n, lpf(E_n) ≤ f(head n).

So MC says: *the least prime factor of the Euclid number attains its trivial lower bound
infinitely often*, or equivalently, *the least factor is bounded by some function of the head*.
MC fails iff the head stalls while the multipliers, being distinct primes, escape to infinity.
"Sufficiently composed" has an exact meaning: not "composite", not "many factors", but "the
smallest factor is the smallest prime it could possibly be".

## 1. The ladder of smallness

Every unconditional rung below MC is a statement that `lpf(E_n)` is small; MC is the top:

| rung | statement | status |
|---|---|---|
| (C∞) | `lpf(E_n) ≤ E_n^{1/2}` i.o. (composite i.o.) | open, Fermat-shaped |
| (S) | `lpf(E_n) < 2^{n−c}` i.o. | open; `RD ⟹ (S)` |
| RD | `∑ 1/lpf(E_n) = ∞` | open; `MC ⟹ RD` |
| head | `lpf(E_n) = head n` i.o. | **⟺ MC** |

Implications `MC ⟹ RD ⟹ (S) ⟹ (C∞)` are on file (`CompositeFloor`, `WeakMullin`).  Nothing
weaker than equality with the head suffices: a sequence whose least factor is always the *second*
missing prime satisfies every lower rung and fails MC.

Heuristic sizes: `log E_n ≍ n log² n`, `head n ≍ √(n log n)`, and `lpf(E_n)` has the law
`P(lpf = p) ≈ log(head)/(p log p)`: typically `head^{O(1)}`, with a heavy tail (`> e^K` with
probability `log head / K`).  So MC needs factors with `~log n` digits inside numbers with
`~n log² n` digits, infinitely often — the relative size `log lpf / log E_n → 0` along a
divergent-reciprocal set of stages.

## 2. Rigidity: what "richly composed" cannot mean

* Each prime `q` divides at most `π(q)` Euclid numbers (`AdelicShadow.hits_finite`), and more
  than `π(q−1)` hits force its selection (`captured_of_many_hits`).  So "every prime divides
  many Euclid numbers" is false; richness can only come from *new* primes at every stage.
* The strongest true fixed-prime statement is MC′: every prime divides some `E_n`.  `MC ⟹ MC′`;
  the gap `MC′ ⇏ MC` is exactly the *wasted hits* — a hit on `q` while a smaller missing prime is
  the least factor — of which there are at most `π(q)`.
* Head capture is a hit (`seq_succ_eq_head_of_dvd`): for the head no exposure condition is
  needed, so MC ⟺ every eventual head is hit.
* Consecutive Euclid numbers are coprime (`coprime_euclid_succ`).  After a hit `r ∣ E_n`, later
  hits `r ∣ E_m` occur iff the multiplier product `seq(n+1)⋯seq(m)` returns to `1 (mod r)`
  (`dvd_euclid_iff_prod_mul_eq_one`).
* Wasted-hit accounting: `∑_{n<N} (ω(E_n) − 1)` = number of wasted hits before stage `N`; each
  lands on a missing prime larger than the least factor.  No contradiction is extractable: the
  supply of large primes is infinite.

## 3. The composite floor and its class rungs

`(C∞) ⟺ C = 0` (growth constant) `⟺` no perpetual Sylvester tower `s ↦ s² − s + 1` seeded at a
Euclid number (`DefectTelescope`, `SylvesterTower`).  New rungs (`ClassInfinitude`, `HeadDynamics`):

* Frozen residues: `E_n ≡ 3 (mod 4)` and, for `n ≥ 1`, `E_n ≡ 1 (mod 3)`, so a *prime* Euclid
  number is `≡ 7 (mod 12)`.  On the perpetual branch every late multiplier is `≡ 7 (mod 12)` and
  `≡ 1` modulo the whole accumulator `prod N₁` (`perpetual_seq_mod_twelve`, `perpetual_seq_mod_prod`).
* Hence, with `CI(a mod m)` := infinitely many Euclid–Mullin primes `≡ a (mod m)`:

      MC ⟹ CI(2 mod 3) ⟹ NotConfined ⟹ (C∞),   ¬CI(3 mod 4) ⟹ (C∞),   CI(1 mod 4) ⟹ (C∞),

  where `NotConfined` := the multipliers are not eventually `≡ 1 (mod prod N)` for every `N ≥ 1`
  (`MC ⟹ NotConfined` uses Dirichlet: infinitely many primes `≡ −1 (mod prod N)`, all appear).
* Every Euclid number has a prime factor `≡ 3 (mod 4)` (`exists_prime_dvd_euclid_three_mod_four`):
  the only positive divisibility fact the sequence yields for free.  `CI(3 mod 4)` — infinitely
  often that factor is the *least* one — is the one class statement the floor does not block
  (it holds on the branch), and remains the weakest open target with a positive ingredient.
* After a prime Euclid number every prime factor of the next one is `≡ 1 (mod 3)`
  (`prime_dvd_euclid_succ_mod_three`): the integer twin of the function-field even-degree
  exclusion.

## 4. Why every route to (C∞) fails, structurally

1. **Congruences and coverings.**  A Sierpiński-type covering needs residues periodic in `n`; a
   prime witnesses one stage of a Sylvester tower and is then absorbed (`Φ₆(−1) = 0`).  Tower
   terms are pairwise coprime.  No finite set of primes certifies infinitely many composites; a
   proof must produce infinitely many *distinct* proper factors.  (The No-Invariant Theorem is the
   same phenomenon for capture.)
2. **Sieves over the seed population.**  "A.a. seeds have (C∞)" needs a bound on
   `#{m ≤ X : E_N(m) prime}` uniform in `N`; for large `N` a.a. seeds have captured every prime
   `≤ log X`, so `E_N(m)` is rough beyond the sieve range reachable with `X` seeds.  Same wall as
   the simultaneous-in-`q` seed law (§G).
3. **Algebraic factorisation.**  The level polynomials `g_k = Φ₆^k + 1` are irreducible over `ℚ`
   (`GenericTower.gQ_irreducible`, via mod 5).  The char-2 and char-3 doors — `(F+1)³P + 1` factors,
   `Φ₃ = (y−1)²` — are closed over `ℤ`.  Compositeness of `g_k(P_N)` is about a *value*.
4. **Reciprocity.**  Quadratic: identically consistent (`no_reciprocity_induction_proof`).
   Cubic: `P_{N+k}` is a primitive cube root of unity mod `E_{N+k+1}` and never a cube there
   (`E ≢ 1 (mod 9)`, `P` squarefree); cubic reciprocity relates this to cubic characters of the
   bag primes mod `E`, undetermined by `E ≡ 1 (mod r)` for inert `r`.  Consistency only.
5. **Analytic / size.**  No method proves compositeness of one integer without exhibiting a
   factor.  Pocklington certifies primality of `E_n` in polynomial time (`E_n − 1 = P_n` is
   factored) and says nothing about compositeness.
6. **Random-model heuristics.**  Over `𝔽_5[X]` Euclid polynomials are reducible by default for
   random polynomials, yet the seed-`X` tower is entirely irreducible.  "Composite by default"
   proves nothing about one tower.

## 5. Calibration by the function-field model

| ring | floor (C∞) | conjecture | mechanism |
|---|---|---|---|
| `ℤ` | open | open | none |
| `𝔽_2[X]` | **true**, constant 3 (sharp) | open | additivity of `P ↦ P² + P` |
| `𝔽_3[X]` | **true**, constant 1 | open | `Φ₃ = (y−1)²`, squares |
| `𝔽_p[X]`, `p ≡ 1 (3)` | **true**, constant 1 | open | `Φ₃` splits |
| `𝔽_5[X]`, seed `X` (and `X+a`, `X²+1`, `X²+2`) | **false** | **false** | stable tower |

Two lessons.  (a) *Composite is not sufficiently composed*: over `𝔽_2`, `𝔽_3` compositeness is
forced and the conjecture is still open.  (b) *The litmus test*: `𝔽_5[X]` has every residue-side
structure and MC fails there; any proof of MC over `ℤ` must use compositeness, and since the tower
is irreducible over `ℚ` as well, the only usable difference is specialization at `P_N` — values,
not reductions.  Over `ℚ[x]` with the generic seed `x` the sequence is the tower itself; the
integer sequence is its specialization at 2 and leaves at stage 3 because `1807 = 13·139`
(`GenericTower.gZ_three_eval_two`).

## 6. Sharpened shape of the floor

Perpetual primality from `N` ⟺ `P_N` is a simultaneous prime value of the infinitely many
irreducible polynomials `g_k` (`deg g_k = 2^k`) ⟺ an infinite chain of primes under
`p ↦ p² − p + 1` seeded at `E_N`.  Even the positive single-polynomial Bunyakovsky statement
(`y² + y + 1` prime infinitely often) is open; the floor needs the negative direction.  Fermat
numbers have identical status.  Conservation law: `∑_n 2^{−n−1} log c_n = log 2 − C` with
`c_n = E_n / lpf(E_n)` the discarded cofactor (`DefectTelescope`) — exact, but weighted so that
late compositeness is invisible.

## 7. What is provable, what is not, what to do

* **Provable and done today**: the head reformulations (§0), the class rungs (§3), rigidity (§2),
  coprimality and the return-to-1 law, the frozen residues, the integer twin of the even-degree
  exclusion.  All in Lean, all published.
* **Not provable by any known method**: anything at or above (C∞) over `ℤ`, including (C∞) itself,
  (S), RD, NotConfined, CI(2 mod 3), CI(1 mod 4), and "a.a. seeds have (C∞)".
* **Open and not blocked by the floor**: CI(3 mod 4).  It is a marginal statement about the
  residues of least factors, it holds on the perpetual branch, and it has a positive ingredient.
  It is the recommended target if any new marginal technique appears.
* **Do not**: look for coverings, for a population (C∞), for factorisations of level polynomials,
  or for reciprocity contradictions — each is closed by a theorem or a structural argument above.

## 8. Sharpening the head equivalences (2026-09-02, second pass) — and whether it is a route

**What sharpens (all in Lean, `HeadDynamics` §5).**
* `head n ≤ p_{n+2}` (`head_le_nth_prime`): pigeonhole, the bag has `n+1` primes.  So the head
  grows at most like `n log n`; heuristically it grows like `√(n log n)`.
* **Every head capture after stage 0 is a composite Euclid number** (`capture_composite`): if
  `E_n` were prime it would be the head, so every prime below `E_n` would divide `E_n − 1`; by
  Bertrand a prime `p` with `(E_n−1)/2 < p < E_n` then gives `2p ∣ E_n − 1`, impossible.  Hence
  the number of head captures below stage `N` is at most the number of composite stages: the
  rate of MC is bounded by the rate of compositeness, locally and unconditionally.
* **The rung (H)**: `MC ⟹ lpf(E_n) ≤ p_{n+2}` infinitely often (`mullin_implies_lpf_le_nth_prime_io`),
  and `(H) ⟹ (C∞)` (`composite_of_lpf_le_nth_prime`).  Since `log E_n ≥ θ(p_{n+1}) ≈ p_{n+2}`,
  MC forces infinitely many Euclid numbers to have a prime factor below `(1+o(1)) log E_n` — a
  factor smaller than the number's own logarithm.  (H) sits between MC and (C∞); it is
  incomparable with RD a priori (RD allows all least factors above `p_{n+2}`, since `∑ 1/p_n`
  diverges; (H) allows a sparse set of small least factors).  Ladder:

      MC ⟹ (H) ⟹ (C∞),   MC ⟹ RD ⟹ (S) ⟹ (C∞),   MC ⟹ CI(2 mod 3) ⟹ NotConfined ⟹ (C∞).

* The headship decomposition: stages split into excursions during which the head `q` is fixed,
  all multipliers exceed `q`, `E_n` is `q`-rough and `q ∤ E_n`; the excursion ends exactly at
  `q ∣ E_n`.  MC ⟺ every excursion is finite.  In the seed population, Theorem C is precisely a
  tail bound on excursion lengths; §G is "all excursions finite for a.a. seeds".

**Is it a route?**  The head coordinates are the right *statement* of MC for the anatomical
viewpoint: they remove the exposure bookkeeping (head capture = hit), make the compositeness
content explicit (captures are composite steps, (H)), and unify the population results.  They do
not supply a mechanism.  The finiteness of one excursion is the walk-hitting problem for one
prime with all smaller primes captured — #90 in its purest form.  What would turn it into a route
is a quantity monotone along an excursion and bounded, a Lyapunov function; the candidates were
checked and fail: residues (the walk is an arbitrary sequence in `(ℤ/q)^× ∖ {−1}`), sizes (the
multipliers are distinct primes `> q`, unbounded above, no upper bound relates them to `E_n`),
the count of missing primes below the multiplier (no deterministic constraint), the growth
telescope (blind to residues).  Recurrence needs an invariant measure (none: dissipative),
compactness gives recurrence to *some* residue but not to `−1`, equidistribution is CME.
Verdict: **worth the sharpening, done; not a route by itself.**  The genuinely open weak target
it isolates remains CI(3 mod 4), and the newly visible quantitative consequence (H) is a clean
way to state how much compositeness MC needs: a factor below `log E_n`, infinitely often.

## 9. Head coordinates for the seed population (2026-09-02, third pass)

Lean: `EM/Population/SeedHead.lean`.  For a seed `m ≥ 1` let `head m n` be the least prime not
dividing the accumulator `genProd m n` (the bag of a seed contains the primes of the seed).

**Item 1 — the seed-average law re-indexed by the head.**
* `GenMC m ⟺ head m → ∞` (`genMC_iff_head_tendsto`); a bounded head is a missed prime, namely
  its eventual value (`exists_misses_of_head_le`).
* `head_stage_density`: for every `Q, ε` one horizon `n` and one threshold `X₀` with
  `#{m ≤ X : head m n ≤ Q} ≤ εX` for `X ≥ X₀` — at a fixed late stage the head exceeds `Q` for
  almost all seeds.  This is `finite_simultaneous_density` (the common sampling frame `[1,X]`
  already existed) read in head coordinates.
* `head_bounded_density`, `head_growing_range`: seeds whose head stays `≤ Q` (resp. `≤ Q(m)`,
  `Q → ∞` ineffective) forever have density 0.
* **§G ⟺ StallTail** (`headEscapesAA_iff_stallTail`), where StallTail is the thresholded
  (N2′): for every δ there are `Q, X₀` with `#{m ≤ X : m misses some prime > Q} ≤ δX` for
  `X ≥ X₀`.  The finite part is free, so §G is *exactly* "a head that has passed `Q` rarely
  stalls afterwards" — one monotone quantity, one missing tail bound.  (Also
  `headEscapesAA_iff_almostAllGenMC`.)

**Item 2 — what an effective excursion tail gives.**
* Where the ineffectivity lives.  `LemmaD` uses the *asymptotic* weighted PNT in progressions
  (`IK.weightedPNTinAP_asymp_proved`, proved by Karamata's Tauberian theorem, threshold `x₀(q,ε)`
  existential with no rate).  Everything downstream is explicit modulo that: `pathwise_compensator`
  has `n₀ = max(n₂, ⌈e^600⌉)`, Theorem C's `κ, K₀, n₁` come from `lemma_D_z`, `three_type_union_small`
  takes `n ≥ max(n₁, Cc)` with `Cc ≥ 48q` and a truncation `Y` with `log Y ≥ n²/2`, the sample
  space is one period `M = ∏_{r ≤ Y, r ≠ q} r ≈ e^Y`, and the density conversion
  (`PeriodicDensity.eventually_density_le`) takes `X₀ = M`.
* Consequence: even with every constant made explicit, the per-range threshold is
  `X₀(K) ≥ exp(exp(c K²))` (from `n ≥ 48K` and `log Y ≥ n²/2`), so the effective growing range
  extracted by `effective_range` / `head_effective_range` is at most **`Q(X) ≍ (log log X)^{1/2}`**.
  Replacing Karamata by an explicit PNT in APs (thresholds of order `exp(c√q log³q)` are in the
  literature, Bennett–Martin–O'Bryant–Rechnitzer 2018; not in Mathlib) would not change this
  shape, since `exp(√q log³ q) ≤ exp(n²/2)` already for `n ≥ 48q`.  The bottleneck is the
  design `Cc ≥ 48q` and the period `e^Y`, not the Tauberian input.
* What effective tails cannot do: `allScaleTail_cofinite_mc` — a per-prime bound
  `#{m ≤ X : m misses q} ≤ f(q)·X` valid at *all* scales with `f` of small tails implies that
  the Euclid–Mullin sequence contains every sufficiently large prime.  So "effective tails ⟹
  Borel–Cantelli ⟹ §G" is closed, not hard (#176 sharpened from the (N2) shape to the tail
  shape).  The reason is the same as before: at scale `X` the tail concerns primes `q > X`, for
  which no period `≤ X` sees the event.
* Correction: the predicate `GrowingRange.ScaleUniformTail` quantified over all `q`, and without
  primality it is false outright (every composite `q > X` is "missed" by every seed `m ≤ X`,
  `scaleUniformTail_without_primality_false`), which made `scaleUniformTail_cofinite_mc` vacuous.
  Statement corrected to primes; the proof and the conclusion of #176 are unchanged.

**Verdict.**  Item 1 done: the population law is now literally a statement about the head, and
§G is identified with the stall tail.  Item 2 done in the only honest form: the effective
program is stated (`effective_range`), its ceiling computed (`√(log log X)`), its analytic input
named (explicit PNT in APs, outside Mathlib), and its impossibility of reaching §G proved.
