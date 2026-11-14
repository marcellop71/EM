# Toward a theory of Euclid systems: the step as a norm (2026-09-23)

Status: analysis memo, no Lean yet.  §1 identities checked by hand and on the first six
steps; everything else is argued here and marked as proved-on-paper, target, or question.

## 0. What "a theory" has to be here

Every language the project has used is a **projection** of one step `E_n = p_{n+1} · c_n`
(`E_n = P_n + 1`, `p_{n+1} = lpf E_n`, `c_n` the discarded cofactor):

| language | what it keeps | what it loses |
|---|---|---|
| residue walk mod `q` | the torsion part of `P_n` in `ℤ_q^×` | everything at other primes; the cofactor |
| growth telescope, `ρ` | `log c_n` (the defect, `defect_eq_log_cofactor`) | all residues |
| seed population | laws over `m ≤ X` | the single orbit (#90) |
| profinite `Ω` | the topology of capture (clopen for ω-orders) | size; `ℕ` is null |
| heights / adelic | the torsion-free data | the walk (#177) |
| `𝔽_p[t]` | the same algebra | char 0; it has a constant field |

None of these has an object that carries the *pair* `(p_{n+1}, c_n)` as arithmetic, which is
the only thing a step really is.  A theory in the useful sense needs (a) such an object, (b) a
transition law written in its terms, (c) invariants with structure theorems, (d) a precise place
where characteristic-0 input acts (screen 2) and where positive divisibility is native
(screen 1).  §1–§3 propose the object.  It is an imaginary quadratic order attached to each step.

## 1. The core identity: every Euclid number is a norm

Let `E = E_n`, `p = p_{n+1}`, `c = c_n = E/p`.  Since `P_{n+1} = P_n p = (E−1)p`,

    E_{n+1} = (E − 1)p + 1 = c p² − p + 1.                                   (1)

Let `ω = ω_n` be a root of `y² − y + c`, so that `ω + ω̄ = 1` and `ω ω̄ = c`.  Set
`D_n = 1 − 4c_n` (always `≡ 1 mod 4`, always **negative**) and `O_n = ℤ[ω_n]`, the imaginary
quadratic order of discriminant `D_n`, with `K_n = ℚ(√D_n)`.  Then

    E_{n+1} = N(p_{n+1} ω_n − 1) = x² + xy + c_n y²  at (x, y) = (−1, p_{n+1}),     (2)
    4 c_n E_{n+1} = (2E_n − 1)² − D_n.                                              (3)

(Expand: `N(pω − 1) = p²c − p + 1`; and `(2E−1)² − 1 + 4c = 4(E² − E + c) = 4c E_{n+1}`, the
last step using `E² − E = cP_{n+1}`.)  **Each Euclid number is a value of the principal form of
discriminant `D_n`, at a primitive vector.**  The step is a transition between imaginary
quadratic orders:

    state (D_n, p_{n+1})  ↦  β_n = p_{n+1} ω_n − 1 ∈ O_n  ↦  (β_n) = 𝔩 · 𝔠  with N𝔩 = p_{n+2} least
                          ↦  c_{n+1} = N𝔠,  D_{n+1} = 1 − 4 c_{n+1}.

First terms:

| n | E_n | p_{n+1} | c_n | D_n | E_{n+1} |
|---|---|---|---|---|---|
| 0 | 3 | 3 | 1 | −3 | 7 |
| 1 | 7 | 7 | 1 | −3 | 43 |
| 2 | 43 | 43 | 1 | −3 | 13·139 |
| 3 | 1807 | 13 | 139 | −555 | 53·443 |
| 4 | 23479 | 53 | 443 | −1771 | 5·248867 |
| 5 | 1244335 | 5 | 248867 | −995467 | 6221671 |

At every row, every prime factor of `E_{n+1}` splits or ramifies in `K_n`.  For example `5`
enters at stage 6 because `−1771 ≡ 4 (mod 5)` is a square.

## 2. The discriminant sequence carries both shadows

The single integer `D_n = 1 − 4c_n` holds both of the cofactor's shadows (compare
`logic_routes` §7.3):

* **Archimedean shadow.**  The growth defect is `δ_n = log c_n + O(1/P_n) = log((1 − D_n)/4) + O(1/P_n)`
  (`defect_eq_log_cofactor`).  So the telescope reads
  `log P_N / 2^N = log 2 − Σ 2^{−(n+1)} log((1−D_n)/4) + (summable)`.  Prime stage ⟺ `D_n = −3`,
  and `(C∞) ⟺ D_n ≠ −3` infinitely often.
* **Arithmetic shadow.**  The quadratic character `χ_{D_n}` decides which primes may divide
  the next Euclid number.  This is (T1) below.

So the object is the **discriminant sequence** `(D_n)` together with the multipliers.  The walk
mod `q` sees one coordinate of `χ_{D_n}` at a time; the growth constant sees `|D_n|`.

## 3. First theorems of the theory (paper proofs, Lean-sized)

**(T1) Splitting law.**  For every odd prime `ℓ ∣ E_{n+1}`, `D_n` is a square mod `ℓ`.
Equivalently, `ℓ` splits or ramifies in `K_n`.  *Proof:* (3).  This is the first **cross-prime**
statement on file: the entire anatomy of `E_{n+1}` is supported on `{ℓ : χ_{D_n}(ℓ) ≠ −1}`, one
Chebotarev half-set, for all `ℓ` at once.  At `c_n = 1` it is the known fact
(`ClassInfinitude`) that after a prime Euclid number every factor of the next is `≡ 1 (mod 3)`.
Its first time on the orbit is a rephrasing of the `Φ₃` exclusion; after that it gives
something new at every composite stage.

**(T2) Head-capture criterion.**  If the head `q` is captured at stage `n+2`, then
`χ_{D_n}(q) ≠ −1`.  Given the splitting, capture is the congruence `p_{n+1} ≡ ω_n^{−1} (mod 𝔮)`
in `O_n/𝔮 ≅ 𝔽_q`.  In `(c, p)` coordinates the death locus is a conic with two roots in `p`; in
`(w, p)` coordinates it is the unique death class `−w^{−1}` (`death_multiplier_unique`).  These
agree because `c = (w+1)p^{−1}` makes the conic linear in `p`.

**(T3) Norm-form lower bound; small factors are non-principal.**  For `y ≠ 0`,
`x² + xy + c y² ≥ c − 1/4`.  Hence if `ℓ = p_{n+2} ∤ D_n` and `𝔩 ∣ β_n` has norm `ℓ`, then no
power `𝔩^k` with `ℓ^k < c_n − 1/4` is principal:

    ord [𝔩] in Pic(O_n)  ≥  log(c_n − 1/4) / log p_{n+2}.

The smallness ladder (`(C∞)`, (S), RD, the head) is therefore a statement about **large-order
ideal classes** in `Pic(1 − 4c_n)`.  Take a head capture after a small multiplier: then
`log c_n ≍ log E_n ≍ n log² n` and `p_{n+2} ≍ √(n log n)`, so MC forces classes of order
`≳ n log n` infinitely often.  This is consistent with Siegel's `h ≈ |D|^{1/2}`, so it is no
contradiction, but it is the first bridge from the ladder to class groups.

**(T4) The function-field dictionary, uniformly.**  On a tower `c = 1`, so `K = F(√−3)`.

| base | `y² − y + 1` over the constants | discriminant field of the tower | known result it explains |
|---|---|---|---|
| `𝔽_p`, `p ≡ 1 (3)` | splits: `ω₁, ω₂ ∈ 𝔽_p` | split | `E_{n+1} = (E_nω₁−1)(E_nω₂−1)`: **the floor with constant 1, in one line** (`CompositeFloors`) |
| `𝔽_p`, `p ≡ 2 (3)` | irreducible | **constant extension** `𝔽_{p²}(t)` | split primes = even degree (`AutonomousDegrees`); over `𝔽_5` the tower freezes there and FF-MC is false (`StableTower`) |
| `𝔽_3` | `(y+1)²` | inseparable | `E_{n+1} = (E_n+1)²`, a square (`CharThree`) |
| `𝔽_2` | Artin–Schreier, irreducible | constant `𝔽_4(t)` | floor from additivity, constant 3 (`CharTwo`) |
| `ℤ` | irreducible, `D = −3 < 0` | `ℚ(√−3)`, ramified at 3 | the `Φ₃` exclusion; the tower misses every `q ≡ 2 (3)` |

Two genuinely characteristic-0 features appear, and both are archimedean.
(i) Over `ℤ`, `D_n < 0` always, so `K_n` is never split and the norm form never factors over
`ℤ`.  Over `𝔽_q[t]` a square `1 − 4c` factors `E_{n+1}` for free.  This is why the floor is a
theorem over `𝔽_p[t]` and Fermat-hard over `ℤ`.
(ii) `ℚ` has no constant-field extension (Minkowski: every `K_n` ramifies somewhere).  The
`𝔽_5` counterexample is exactly a tower whose discriminant field is the constant extension.

## 4. The problem inside the theory: frozen versus unfrozen

For a missing head `q` there are exactly two ways to fail:

* **Frozen(q):** `χ_{D_n}(q) = −1` for all large `n`, so `q` is eventually inert in every `K_n`
  and cannot divide any `E_{n+1}`.  In walk coordinates (`c ≡ (w+1)m^{−1}`, `m = p_{n+1} mod q`)
  this reads
      `( m (m − 4(w+1)) / q ) = −1` at every late step.
  The conditional multiplier law is then confined, at every position, to a set of about
  `(q−1)/2` classes.  That is a gross violation of CME, not the one-class avoidance that
  `death_multiplier_unique` permits.  On a tower `m = w+1` and the symbol is `(−3/q)`, so
  **every `q ≡ 2 (mod 3)` is frozen on the autonomous branch.**
* **Unfrozen-missing(q):** `q` splits in `K_n` infinitely often, but the congruence of (T2)
  always misses.  This is the #90 residue and stays single-orbit statistical.

Define **NoFrozen**: no missing prime is frozen.  Then

    MC  ⟹  NoFrozen  ⟹  (C∞).

The first implication is vacuous, like every missing-quantified statement.  The second is proved
above (a tower freezes the infinitely many `q ≡ 2 (3)` outside the bag).  NoFrozen is a
**new rung with arithmetic rather than size character**, and it is the rung the `𝔽_5[t]`
counterexample violates: there the orbit is frozen by a constant field.

Screens (`why_its_hard.tex`, frontier box):
1. *Positive divisibility*: not yet.  The theory relocates the demand to "split, then one
   congruence in `O_n/𝔮`".  (T1) is a family of negative facts organised by one character.
2. *Char-0 input*: the location is identified.  Frozen is the `𝔽_5` mechanism, and the two
   archimedean facts of (T4) are what `ℤ` has and `𝔽_q[t]` lacks.  Neither kills the tower by
   itself: `ℚ(√−3)` ramifies only at `3`, which is already in the bag.  That residual is the
   Fermat-shaped core, now stated as "`ℚ(√−3)` cannot stay frozen".
3. *Single orbit*: yes; everything is an identity along the orbit.
4. *Yields (C∞)*: NoFrozen does.

## 5. What this does not do

It does not prove MC or `(C∞)`, and it is not evidence for either.  (1)–(3) are elementary
identities.  The value is organisational: one object (`D_n`, `O_n`, `β_n`) carries the size, the
residue pattern, the `𝔽_q[t]` phenomena and the smallness ladder.  The failure of MC also splits
into an arithmetic half (Frozen, which contains the floor and the `𝔽_5` counterexample) and a
statistical half (Unfrozen, which is #90).  Any per-`q` statement about `χ_{D_n}(q)` is again a
residue condition on the orbit and meets #90.  Do not expect Chebotarev or class-number
*averages* to move it.

## 6. Programme

Lean (small, one file, e.g. `EM/Population/QuadraticStep.lean`):
1. (1) as `E(n+1) + p = c·p² + 1` over `ℕ`, and (3) over `ℤ`.
2. (T1): odd prime `ℓ ∣ E(n+1)` ⟹ `IsSquare ((1 − 4c : ZMod ℓ))`; recover the `ClassInfinitude`
   `≡ 1 (mod 3)` lemma as the `c = 1` case.
3. The elementary norm bound behind (T3) (no class groups needed): `y ≠ 0 ⟹ 4(x²+xy+cy²) ≥ 4c − 1`.
4. `Frozen`, `NoFrozen`, and `infinitelyManyComposite_of_noFrozen` (`EM/Population/QuadraticStep.lean`; this memo first cited it as `noFrozen_implies_infinitelyManyComposite`, a name no declaration has).
5. Over `𝔽_q[t]`: the one-line proof of the `p ≡ 1 (3)` floor via the split norm (a second proof
   of `ffGrowthConstant_eq_zero_of_one_mod_three`), which tests whether the dictionary is right.

Questions:
* Is NoFrozen strictly between MC and `(C∞)`?  How does it compare with RD and `ρ(2) = 0`?
* Transfer of ramification: `ℓ ∣ D_n` and `ℓ ∣ E_{n+1}` force `ℓ ∣ 2E_n − 1`.  Is there any
  relation between `D_n` and `D_{n+1}` (for example through the class of `𝔠` in `Pic(O_n)`)?
  The cofactor ideal `𝔠 = β_n/𝔩` has class `[𝔩]^{−1}`, so `c_{n+1}` is represented by a
  specific (typically non-principal) form of discriminant `D_n`.  This is a "discriminant walk"
  through form classes.
* Over `𝔽_q[t]`: is every perpetual tower's discriminant field constant?  If so, "frozen ⟺
  constant field" is a theorem there, and screen 2 becomes concrete over `ℤ`: exclude frozen
  behaviour without a constant field.

## 7. The gap principle: what "a missed prime is a rare object" can mean (2026-09-24)

The intuition: a missed prime `q` should produce an object so special that it cannot exist,
or at least is very rare.  This section makes that precise and says where it stands.

### 7.1 The theorem (Lean: `EM/Population/GapPrinciple.lean`, 0 sorry)

Let `M_q` be the seeds `m ≥ 1` that miss `q` (`q ∤ m`, `q` never selected).  Missing `q` is
inherited along the orbit (`misses_genProd_iff`), orbit points are distinct, and
`genProd m k + 1 ≤ (m+1)^(2^k)` (`genProd_add_one_le_pow`, from `lpf(P+1) ≤ P+1`).  For
squarefree seeds the half of every later orbit point is an odd `T`-preimage (`N/2` odd implies
`lpf(N/2+1) = 2`), so it misses `q` too (`misses_half`).  Hence:

* `card_misses_ge`: `m ∈ M_q` implies `k+1` elements of `M_q` in `[1, (m+1)^(2^k)]`.
* `card_misses_ge_of_squarefree`: `2k` elements (even orbit points plus odd halves).
* `misses_eq_empty_or` (**gap principle**): `M_q` is empty or has `≳ log₂ log X` elements below `X`.
* `mem_seq_of_card_misses_lt`: if for one `k` fewer than `2k` seeds in `[1, 3^(2^k)]` miss `q`,
  then `q` is in the Euclid–Mullin sequence.

### 7.2 What "few" must mean

Provably the orbit has at least `log₂ log X` points below `X`.  Heuristically it has about
`log X/(log log X)²`, since `log P_n ≍ n log² n`.  The seed-average law gives `#M_q(X) = o(X)`
with no rate.  Between `o(X)` and `o(log log X)` there is nothing: at scale `X ≈ P_n` a counting
bound with that few exceptions is, in strength, a pointwise statement.  The gap principle is the
exact interface between "rare" and "none", and it shows that no density or rate improvement of
the population law can cross it by itself.  This is the counting form of #176.

### 7.3 Amplification: how many seeds does one missed prime force?

A counting argument needs the counterexample to generate *many* bad seeds.  Exact
amplification comes only from invariance.  `M_q` is a union of grand-orbit classes
(`misses_congr`), and a class is forward rays plus backward trees.  Backward branching at an
orbit point `N = P_n` through a prime `p ∣ N` is `p ∣ N/p + 1` with `lpf(N/p+1) = p`
(`preimage_iff`).  For a bag prime `p` all of whose smaller primes are in the bag, the
roughness is automatic and the condition is

    P_n / p ≡ −1 (mod p)      — the "p-deleted walk" hits −1.

* `p = 2`: always, because `−1 = 1` in `(ℤ/2)^×`.  This is the free branch of 7.1 (odd
  leaves).
* `p = 3`: iff `∏_{k=2}^{n} p_k ≡ 1 (mod 3)`, e.g. `T(14) = 42`.  It happens infinitely often
  if infinitely many Euclid–Mullin primes are `≡ 2 (mod 3)` (the CI(2 mod 3) rung), and
  otherwise possibly never.
* In general, **amplifying a missed prime is a hitting problem for captured primes**: the same
  problem one level up.  Nothing is gained in difficulty, but the symmetry is exact.

Heuristic only: at stage `n` the expected number of non-leaf branches is about
`Σ_{3 ≤ p ≤ head} 1/(p−1) ≈ log log head − 1/2`, which exceeds 1 once the head passes the
low twenties.  So the backward tree is plausibly *supercritical* (depth bounded by the number
of bag primes), and the class of 2 larger than the "polylogarithmic" guess in `GrandOrbit.lean`.
It is still far below positive density, so `grandOrbit_transfer` stays out of reach either way.
The docstring's guess should read "unknown".

### 7.4 No-go: finite-horizon (CRT) amplification is too thin

If 2 misses `q`, the whole class `2 mod M(y_n)` (`M(y)` the primorial, `y_n ≥ q` the largest of
the first `n` multipliers) avoids `q` for `n` steps (`genSeq_prefix_of_modEq`).  Its density is
`e^{−θ(y_n)}`, and `y_n ≥ p_n` (the `n`-th prime) because the multipliers are distinct.  A
contradiction with an upper bound `e^{−f(n)}` on `n`-step missers would need
`f(n) > θ(p_n) ≈ n log n`.  The truth is heuristically `f(n) ≈ n/q` (Shanks: capture
probability `1/q` per step), and Theorem C gives `f(n) ≍ e^{−128} n`.  **Distinctness makes the
finite-horizon family super-exponentially thinner than the finite-horizon missing set**, so no
bound of this kind can ever be contradicted.  The only amplification that survives the
infinite horizon is exact invariance (7.3).

### 7.5 Where it could bite

Either (a) an operation preserving "misses `q`" that produces a polynomially large family
(`≥ X^c` seeds below `X`) from one missing seed, together with a power-saving count
`#M_q(X) ≪ X^{1−δ}` (no rate is known); or (b) a thinner ambient family closed under `T` in
which missing seeds can be counted.  The factor tree from 1 is the natural candidate:
heuristically `X^{o(1)}` nodes below `X`, containing the orbit and closed under the greedy
step.  Nobody can count inside it, and #90 applies.  Neither (a) nor (b) exists.  The
gap principle fixes the target: *fewer than `2k` missing seeds below `3^(2^k)`, for one `k`*.

## 8. Ambition by analogy: what "a missed prime is a rare object" would need (2026-09-24)

Read with §7.  Everything below is either a theorem (marked Lean), an identification of shape,
or a heuristic labelled as such.

### 8.1 The Zilber–Pink architecture

Proofs that "unlikely" objects are finite (André–Oort, Zilber–Pink) run on two bounds that
cross: a **Galois-orbit lower bound** (a special point of complexity `H` has `≫ H^δ`
conjugates, all special) and a **Pila–Wilkie upper bound** (the transcendental part of a
definable set has `≪ H^ε` rational points of height `≤ H`).  The map onto MC is exact:

| ZP ingredient | EM analogue | strength available | strength needed |
|---|---|---|---|
| special points | seeds missing `q` (the set `M_q`) | — | — |
| Galois orbit of one special point | the missing seeds one missing seed forces: its orbit and backward tree | `log₂ log X` below `X` (`card_misses_ge`, Lean) | `X^c` |
| Pila–Wilkie count of the transcendental part | the seed-average law `#M_q(X) = o(X)` | `o(X)`, no rate | `X^{1−δ}` |
| algebraic part (special subvarieties) | missing for a structural reason: the Sylvester tower, where `q ≡ 2 (3)` is inert in every `ℚ(√D_n) = ℚ(√−3)` (§4, Frozen) | theorem | — |
| transcendental part | Unfrozen missing: the walk avoids one class per position with no reason | this is #90 | — |

Both bounds are far from what the architecture needs, and for a structural reason on the
lower-bound side: the symmetry group that would produce conjugates acts on the profinite
ring `Ω`, where the conjugates of an integer point are non-integers (the type cell of its
itinerary is `μ`-null and meets `ℕ` only in the point itself; §7.4 is the finite-horizon form).
The ZP philosophy nevertheless names the right conjecture: *a miss has a reason or does not
happen*, i.e. `(C∞) ⟹ MC`, which is what the frontier box already isolates as attackable.

### 8.2 Alternative histories are the Galois orbit

The grand-orbit class of `2` is the set of **alternative histories**: seeds whose greedy
orbit rejoins the Euclid–Mullin orbit.  Its structure is now explicit (Lean,
`GapPrinciple.lean`):

* `isPreimage_div_iff` — if `p ∣ N` and every prime below `p` divides `N`, then `N/p` is a
  `T`-preimage of `N` iff `N/p ≡ −1 (mod p)`.  So a bag prime `p` below the head gives a
  branch at `P_n` iff the **`p`-deleted walk** (product of the other bag primes, mod `p`) is at
  `−1`.  The deleted walk uses the same multipliers as the walk of a missing prime; it is a
  hitting problem for a *captured* prime, non-vacuous under MC.  These are the first hitting
  problems about the actual sequence whose quantifier is not over missing primes.
* `three_dvd_prod_div_three_succ_iff` — for `p = 3` the deleted walk is a parity: the branch
  `P_n/3` exists iff an even number of `seq 2, …, seq n` are `≡ 2 (mod 3)`.  So "infinitely
  many 3-branches" is a class-count statement of the CI type; if CI(2 mod 3) fails the branch
  is eventually always or never present.
* Heuristic size.  With independence across deletions, the ancestors of `P_n` number about
  `∑_R |R|! ∏_{p∈R} 1/(p−1)` over deletion sets `R` of bag primes `≥ 3` (`2` gives a leaf), which
  is `exp(c·head/log head) = exp(c π(head))`.  With `head ≍ √(n log n)` and `log X ≍ n log² n`
  this is `exp((log X)^{1/2+o(1)})`: far above polylogarithmic (the guess in `GrandOrbit.lean`
  should read "unknown; heuristically `X^{o(1)}` but not polylog"), far below `X^c`.  The
  transfer principle stays out of reach by this margin.

### 8.3 The tree from 1 as the ambient family

The factor tree `𝒯` from `1` (every Euclid history) contains the EM orbit as its leftmost
path and the class of `2` as the histories that rejoin it.  Facts and non-facts:

* Booker's theorem (one steered path through `𝒯` contains every prime) is a **coverage
  theorem for the tree**: the residues of tree nodes mod `q` reach `−1`, because at each step
  one may choose the factor.  The three steering axes — factor (Booker), seed (seed-average
  law), priority order (§7.2 of the logic memo) — all give population theorems; the EM orbit
  is one point on each axis.
* A `q`-avoiding history exists for every prime `q ∉ {2,3}` with `q ≢ 7 (mod 12)`: the rule
  "largest prime factor `≠ q`" never gets stuck, since `E_n ≡ 3 (mod 4)` and `E_n ≡ 1 (mod 3)`
  exclude `E_n = q^k`.  So the special object is never "a history missing `q`"; it is "the
  *leftmost* history missing `q`", i.e. the lexicographic minimum of the closed set `H_q` of
  `q`-avoiding paths coinciding with the global minimum.  Minimality is the whole content.
* Counting nodes: heuristically `|𝒯 ∩ [1,X]| = X^{o(1)}` (paths of length `d ≤ log X/log log X`
  with `≈ log log X` choices per step), comparable with the class of `2`.  Not proved: the
  worst-case `ω(N+1) ≈ log N/log log N` makes the trivial bound useless, and an average over
  chains is needed.
* The tree version of the transfer principle would need "nodes of `𝒯` missing `q` have
  density `0` in `𝒯`", a sieve on a thin set with no residue structure.  Whether `𝒯` is even
  equidistributed in the unit classes mod `q` is open and is the honest new question here.

### 8.4 "Few missed primes" is a rung, and it is open at every level

The intuition "there are really few missing primes" has an exact place.  `WeakMullin.lean`
already has `MissingFinite` and `WeakMullin` (`∑_{q missing} 1/q < ∞`).  The density rungs are
new (`EM/Population/CoverageLadder.lean`, 0 sorry): with `S(x)` the number of EM primes `≤ x`
and `M(x) = π(x) − S(x)`,

    MC ⟹ MissingFinite ⟹ MissingDensityZero (M = o(π)) ⟹ PositiveDensity (S ≥ cπ) ⟹ RD.

The last step is Abel summation (`abel_identity`: `∑_{a∈A, a≤N} 1/a = ∑_{n≤N} A(n)/(n(n+1)) +
A(N)/(N+1)`), no Chebyshev bound.  **Not even `PositiveDensity` is known**: the only proved
lower bound on `S(x)` is `log₂ log₃ x` (the gap principle at the level of primes).  The
Deuring–Heilbronn shape ("an exceptional object is alone") is reversed here: on a Sylvester
tower the missing primes come in bulk (all `q ≡ 2 (3)`, relative density `1/2`), so
`MissingDensityZero` fails on the frozen branch and every rung above RD implies `(C∞)`.

### 8.5 Verdict

No analogy supplies a mechanism; each supplies a calibration.  ZP says the two counts are
each off by a power of `X`.  Booker says the freedom that makes coverage provable is exactly
what the greedy rule removes.  The deleted walks say that amplifying a miss is hitting for
captured primes — the same problem with the vacuity removed, which makes them a fair test
bed: a technique that cannot decide whether the 3-deleted walk hits `−1` infinitely often (a
parity of a class count) has no chance at MC.  The coverage ladder says where "few" sits:
`PositiveDensity` is the weakest counting statement about the EM primes, and it is open.

## 9. Zilber–Pink, in depth (2026-09-24)

The André–Oort / Zilber–Pink proofs (Pila–Zannier strategy) have five moving parts.  Each is
matched below with its EM counterpart and the counterpart's status.  The point of the
exercise is not to import a mechanism — none imports — but to say, part by part, what a
"rare object" proof would have to contain and which parts are *structurally* absent.

### 9.1 The dictionary, part by part

| ZP ingredient | role in the proof | EM counterpart | status |
|---|---|---|---|
| ambient Shimura variety `S` | carries the special structure | seeds with the greedy map; residues live in `∏_q (ℤ/q)^×`; closure `Ω` | present |
| subvariety `V ⊂ S` | the object under study | the orbit of `2` (a "curve" indexed by `n`) | present |
| special subvarieties | the *reasons* for unlikely behaviour | the Sylvester tower (autonomous branch) | present, and **the only one** (§9.2) |
| special points on `V` | the unlikely events | the orbit missing a prime `q` | — |
| complexity `Δ` of a special point; Northcott | induction parameter; finiteness at bounded complexity | size `X` of a seed; the seed-average law at scale `X` | present (population only) |
| uniformization `π : X → S`, definable fundamental domain | makes `V` a *tame* set so points can be counted | none: the orbit is not definable in any tame structure (logic memo, 2026-09-01) | **absent** |
| Pila–Wilkie: `≪ Δ^ε` rational points on the transcendental part | upper bound | `#M_q(X) = o(X)` by sieve, no rate | present but off by a power of `X` |
| Galois orbit lower bound `≫ Δ^δ` (Masser; via `h(D) ≫ D^{1/2−ε}`) | lower bound | the orbit and backward tree of a missing seed: `≥ log₂ log X` (`card_misses_ge`); heuristically `exp((log X)^{1/2+o(1)})` | present but off by a power of `X` **for a structural reason** (§9.3) |
| Ax–Lindemann / Ax–Schanuel | identifies the algebraic part with the (weakly) special locus | "algebraic ⟹ tower" (§9.2) | provable, elementary |
| induction on dimension through special subvarieties | closes the argument | on the tower the question is *understood*: `q ≡ 2 (3)` missed (`Φ₃`), and by Odoni the captured primes have density `0` | present |

Two rows say **absent**, and they are the two that carry the proof: tameness (for the upper
bound) and a symmetry group (for the lower bound).  Everything else transfers.

### 9.2 The Ax–Lindemann analogue: the only algebraic reason is the tower

*Theorem (elementary; not yet in Lean).*  If there is `g ∈ ℤ[x]` with `p_{n+1} = g(E_n)` for
all `n ≥ N`, then `g = x` and `E_n` is prime for all `n ≥ N`.  Equivalently, if
`E_{n+1} = f(E_n)` for a polynomial `f` and all `n ≥ N`, then `f = x² − x + 1` and the orbit is
a Sylvester tower from `N`.

*Proof.*  `p_{n+1} ∣ E_n` and `2 ≤ p_{n+1} ≤ E_n`, with `E_n → ∞`.  So `2 ≤ g(E) ≤ E` on an
infinite set of `E`, forcing `deg g ≤ 1`, `g = ax + b` with `0 ≤ a ≤ 1`.  `a = 0` makes the
multiplier constant, against distinctness.  `a = 1` gives `E + b ∣ E`, hence `E + b ∣ b`, so
`b = 0` (else `E` is bounded).  For the second form, `f(x) − 1 = (x − 1)g(x) + r` with `r`
constant and `r/(E − 1) ∈ ℤ` for infinitely many `E`, so `r = 0` and the first form applies. ∎

This is the dichotomy ZP predicts: the orbit either satisfies an algebraic recursion (then
it is the tower, where missing has a reason) or it satisfies none (then no reason exists,
and the miss would be "transcendental" — #90).  `GenericTower.lean` already says the tower
is the generic orbit and the integer orbit its specialization; the theorem above says the
specialization never re-enters any *other* algebraic family.

### 9.3 Why the Galois lower bound fails: the greedy rule is not equivariant

The lower bound in ZP comes from a group acting on the ambient space, preserving both the
special locus and `V` (Galois acts on special points and fixes `V`, defined over a number
field).  Every candidate group here fails to preserve one of the two:

* ring automorphisms of `Ω = ∏ 𝔽_r`: trivial;
* relabelling primes: not even defined coordinatewise (`𝔽_r ≠ 𝔽_{r'}`), and it changes the
  order that `lpf` uses;
* automorphisms `x ↦ x^k` of `(ℤ/q)^×` preserve `−1` and "avoids `−1`", but the conjugate
  walk is not the walk of any integer orbit;
* the one genuine arithmetic group, `Pic(O_n)` with `O_n = ℤ[ω_n]` from §1, acts on the
  ideals of norm `E_{n+1}`: the greedy ideal `𝔩` (least norm) has conjugates = the other prime
  ideals above `E_{n+1}` = **the other branches of the factor tree**.  This is Booker's
  steering in algebraic clothing.  The action commutes with the tree but not with `T`, and the
  conjugate branches do not inherit "misses `q`".

So the class-group symmetry exists and moves *off* the orbit.  The only symmetry that stays
on the orbit is `T` itself, whose "orbit" is the gap principle.  That is the structural reason
the lower bound is `log log X` and not `X^δ`; it is not a quantitative deficiency that better
counting could repair.  A proof by amplification needs a symmetry of the seed space that
commutes with `T` and preserves `Misses q`; none is known beyond `T` and its backward
branches (the deleted walks, §8.2).  Over `𝔽_q[t]` the symmetric tie-break is affine-equivariant
(logic memo §8.5) — the only equivariance found anywhere — and MC is false there.

### 9.4 The special locus is where the unlikely is typical

In ZP a special subvariety is exactly a locus on which special points are Zariski-dense.
The tower behaves the same way, and quantitatively: on a perpetual tower from `P_N` the
captured primes are the primes dividing some term of a Sylvester-type recursion, and by
Odoni (for Sylvester's own sequence; the same Galois-of-iterates argument is expected for
every seed) those have **density zero** among the primes.  So on the special locus
`S(x)/π(x) → 0`, while off it the Shanks heuristic predicts `S(x)/π(x) → 1`.  The coverage
ladder of §8.4 thus has a sharp shape: `PositiveDensity` is expected to be a dichotomy —
either `0` (tower) or `1` — with nothing in between.  Also: the tower is where the reciprocal
sum is rational, `∑_{n ≥ N} 1/E_n = 1/P_N` (telescoping `1/E_n = 1/P_n − 1/P_{n+1}`), so
"`∑ 1/E_n` irrational ⟹ `(C∞)`" — the tower is the rational point of a transcendence-type
criterion, though Badea's criterion (growth `≥` Sylvester) runs the wrong way for us.

### 9.5 The conjecture in ZP form, and its function-field consequences

ZP says: an unlikely intersection that happens has a reason.  Translated, and generalised
to all seeds as §8.7 of the logic memo demands (a proof must be uniform in the seed):

> **Dichotomy conjecture.**  For every seed `m ≥ 1`: either the greedy orbit of `m` is
> eventually a Sylvester tower (`C(m) > 0`), in which case it misses every prime `q ≡ 2 (3)`
> outside its bag and, conjecturally, almost all primes; or `C(m) = 0` and the orbit captures
> every prime coprime to `m`.  In symbols: `GenMC(m) ⟺ (C∞)(m)`.

Proved direction: `GenMC(m) ⟹ (C∞)(m)` (seeded floor).  Open: `(C∞)(m) ⟹ GenMC(m)`, the
statement the frontier box isolates for seed `2`.  The conjecture is consistent with the
population layer (a.a. seeds satisfy both sides) and with `𝔽_5[t]` (the misses there are
towers).  Its function-field form is **falsifiable**: over `𝔽_2[t]` and over `𝔽_p[t]` with
`p ≡ 1 (mod 3)` the floor is a theorem for every seed (`CompositeFloors.lean`), so the
dichotomy conjecture there says FF-MC holds for every seed.  A single seed over `𝔽_2[t]`
provably missing an irreducible would refute the ZP form outright.  No such seed is known,
and no mechanism to prove a miss without a tower is known either — which is the conjecture's
content.

### 9.6 What a ZP-style proof of `(C∞) ⟹ MC` would need, stated as three absences

1. **A tame structure in which the orbit's finite-horizon truncations are uniformly
   definable**, so that the missing set has a "transcendental part" one can count.  The
   truncations are Presburger (periodic) sets with periods growing super-exponentially; no
   single tame structure holds all horizons.
2. **A symmetry commuting with `T` and preserving `Misses q`** with a class of `2` of positive
   density (the transfer principle would then finish).  Only `T` and the deleted-walk branches
   are known; class-group symmetries leave the orbit.
3. **A height/complexity with Northcott on the orbit itself**, not on seeds: a functional on
   the orbit that a miss forces to violate a bound.  Closed by #177 (the walk is the torsion
   component, invisible to heights).

Each absence is a theorem-shaped statement about proofs, not about the sequence; together
they are the precise content of "the analogy supplies calibration, not mechanism".  The
positive residue is 9.2 (algebraic part = tower) and 9.5 (the dichotomy conjecture and its
falsifiable FF form).

### 9.7 Lean (`EM/Population/Dichotomy.lean`, 0 sorry, 2026-09-24)

* `algebraic_multiplier_implies_tower`: `(∀ n ≥ N, seq (n+1) = g.eval (prod n + 1)) → g = X ∧
  ∀ n ≥ N, (prod n + 1).Prime`, via `natDegree_le_one_of_bounded` (a polynomial with
  `0 < g(x) ≤ x` on an unbounded set has degree `≤ 1`; `div_tendsto_atTop/atBot_of_degree_gt`
  over `ℝ`) and the linear case by divisibility.
* `algebraic_recursion_implies_tower`: `(∀ n ≥ N, prod (n+1) + 1 = f.eval (prod n + 1)) →`
  perpetual primality from `N` (division by `X − 1`, remainder killed by `prod n ∣ r`).
* `DichotomyConjecture : ∀ m ≥ 2, GenMullinConjecture m ↔ sgrowth m = 0`;
  `sgrowth_two_eq_zero_of_mc` (proved direction, seed 2); `mc_of_dichotomy` (under the
  conjecture, `growthConstant = 0 → MC`).
* `FFDichotomy p`; `ffMC_two_of_ffDichotomy`, `ffMC_of_ffDichotomy_one_mod_three` (the FF
  dichotomy implies FF-MC where the floor is a theorem); `stableTower_ffGrowthConstant_ne_zero`
  (the `𝔽_5` refutation is consistent with the dichotomy).
* Not done: the seeded direction `GenMC(m) → sgrowth m = 0` for general `m` (needs the
  autonomous-branch argument for `genProd`); on a tower `S(x)/π(x) → 0` needs Odoni/Jones.

## 10. The model problem: FF-MC over `𝔽_2[t]` (2026-09-24, scoping)

Under the dichotomy conjecture, MC is the statement `(C∞) ⟹ MC`.  Over `𝔽_2[t]` the floor
`(C∞)` is a theorem for every sequence (no four consecutive irreducible Euclid polynomials,
`CompositeFloors.ffGrowthConstant_eq_zero_of_two`), and there is no exceptional branch.  So
`FFMullinConjecture 2` is exactly the conjecture's content with the floor in hand
(`Dichotomy.ffMC_two_of_ffDichotomy`).  This section records what the model problem looks
like from inside, what characteristic 2 adds, and what it does not.

### 10.1 Structure specific to characteristic 2 (all theorems, mostly on file)

* **The death value is the identity.**  `Q ∣ E_n ⟺ P_n ≡ 1 (mod Q)`: in `(𝔽_2[t]/Q)^× ≅ 𝔽_{2^d}^×`
  the walk must return to `1`, not reach the element of order 2.  In discrete-log terms the
  partial sums of the multiplier logarithms must vanish mod `2^d − 1`.
* **The tower map is additive.**  `L(P) = P² + P = (F + 1)(P)` with `F` the Frobenius, so on a
  tower segment of length `k`, `E_{N+k} = (F+1)^k(P_N) + 1 = Σ_{j : C(k,j) odd} P_N^{2^j} + 1`
  (Lucas).  These are *linearized polynomials plus one*: their roots form an affine
  `𝔽_2`-space, and their factorisation over `𝔽_2` is governed by Frobenius orbits on that
  space.  `k = 3` gives `y⁸+y⁴+y²+y+1 = (y⁴+y³+1)(y⁴+y³+y²+y+1)`, which is the floor: **the only
  positive divisibility fact in the whole project** (screen 1) comes from additivity, but it
  exhibits a factor that is a polynomial in `P_N`, of degree `4·deg P_N`, and says nothing about
  the least factor.
* **Trace exclusion.**  On a tower step `E_{n+1} = L(P_n) + 1`, an irreducible `Q` of degree
  `d` divides `E_{n+1}` iff `w² + w = 1` is solvable in `𝔽_{2^d}`, iff `Tr(1) = d mod 2 = 0`.
  So after an irreducible Euclid polynomial every factor of the next has even degree, after two
  the degree is divisible by `4` (`AutonomousDegrees.lean`), and towers are at most three long
  (`CharTwo.lean`).  Additivity produces *exclusions* — negative facts — exactly as the sign
  asymmetry predicts.
* **Automatic roughness at the head.**  The first four terms are forced,
  `X, X+1, X²+X+1, X⁴+X+1` (`CharTwo.ff_two_first_terms`), and these are all the monic
  irreducibles of degree `≤ 2` plus one quartic.  Hence for every `FFEMData 2` and every
  `n ≥ 2`, a cubic `Q` divides `E_n` iff the next multiplier is a cubic
  (`CharTwoHead.cubic_capture`, new): for the cubics, capture is a bare hit, no sieve
  condition.  The head after stage 3 is degree 3.
* **The involution `σ : X ↦ X + 1`.**  `P_1 = X(X+1)` is `σ`-invariant, so `σ` maps every
  sequence to a sequence with the conjugate tie-breaks: runs come in `σ`-conjugate pairs with
  identical degree sequences and `σ`-conjugate missing sets.  The stage-3 tie (two quartics
  swapped by `σ`) is forced.  This is the only cross-run symmetry, and it is an involution.

### 10.2 Reconnaissance (computation, not evidence for the conjecture)

Forty stages of every branch (four branches: ties at stages 3 and 33 only, each pair
`σ`-conjugate).  Multiplier degrees of one branch:
`1,2,4,4,5,3,3,7,7,7,8,8,60,4,5,7,13,20,5,43,5,6,5,8,9,73,12,8,14,22,7,48,5,7,13,15,27,20,7,6`.
The head degree climbs `2,3,3,3,3,3,4,…,4,5,…,5,6,…`: every monic irreducible of degree `≤ 5`
is collected by stage 33 in every branch, both cubics at stages 6–7.  `E_{12}` is irreducible
of degree 60 and is followed by a quartic (even, as the trace exclusion demands).  Nothing
resembling an obstruction; nothing resembling a mechanism either.  Recorded only to calibrate
the model problem, per the project's rule against numerical surveys.

### 10.3 Verdict

Characteristic 2 supplies exactly what the litmus test said it would: the floor (a positive
factorisation, but of the wrong kind of factor) and a family of exclusions.  It supplies no
capture mechanism, and the hitting problem for a fixed `Q` — a walk on `𝔽_{2^d}^×` driven by
the residues of the least-degree factors — is #90 verbatim.  The model problem therefore
confirms rather than shortcuts the diagnosis: if `(C∞) ⟹ MC` has a proof, it must be a proof
that a specific deterministic walk returns to the identity, and `𝔽_2[t]` is where every other
ingredient is already a theorem.  The right use of the model is as the **first test** of any
proposed mechanism for `(C∞) ⟹ MC`: run it on `𝔽_2[t]` for the two cubics before anything
else.

Lean added: `EM/FunctionField/CharTwoHead.lean` — classification of monic irreducibles of
degree `≤ 2` over `𝔽_2`, `ffMCBelow_three` (every sequence has collected everything below
degree 3), `cubic_capture`.

## 11. Item 3: does Frozen force the tower? (2026-09-24)

### 11.1 The question in coordinates

Write `u_n = c_n mod q` for the cofactor residue.  In walk coordinates the step is
`w_{n+1} = w_n(w_n+1)/u_n` (the cofactor's second shadow, logic memo §7.3), and

    Frozen(q)  ⟺  u_n ∈ U_q := {u : χ_q(1 − 4u) = −1} for all n ≥ N,

a set of exactly `(q−1)/2` residues (`∑_m χ(m² + bm) = −1`).  At position `w` the allowed
multipliers form the half-set `A(w) = {m : χ(m(m − 4(w+1))) = −1}`, and the death class
`m = −w⁻¹` is never in it (`m(m − 4(w+1)) = ((2w+1)/w)²`), which is the splitting law again.
So Frozen is a half-set confinement of the multiplier at every step, against the one-class
avoidance of an unfrozen miss.  It is *not* a propagating congruence invariant of `P_n`
(the No-Invariant Theorem does not apply and does not need to): `u_{n+1} = (u_n m_n² − m_n + 1)/m_{n+1}`
with `m_{n+1}` free, so nothing propagates.  Frozen is an *anatomical* congruence, on the
cofactor, and holding it forever is a probability-zero event with no mechanism — unless the
cofactor is `1`.

### 11.2 The decomposition: three questions, one of them provable

Between the tower and a single frozen prime there is an intermediate locus:

    tower (c_n = 1)  ⊂  Confined (D_n = −3 s_n²)  ⊂  UniformlyFrozenClass  ⊂  Frozen(q)  ⊂  Missing(q)

* **Confined** (`Confinement.Confined`): the discriminant stays in the tower's field
  `ℚ(√−3)`, with conductor `s_n`; `c_n = 3t² + 3t + 1 = (t+1)³ − t³` is a cuban number and
  `E_{n+1} = N_{ℚ(ω)}(p ω_n − 1)` with `ω_n = −t + (2t+1)ω ∈ ℤ[ω]`.  This is the analogue of a
  constant-field extension — the `𝔽_5[t]` mechanism — and it is exactly the room between
  "special" and "weakly special" in the Zilber–Pink dictionary: the tower is the maximal
  order (`s = 1`, "`j = 0`"), a confined orbit runs through orders of `ℚ(√−3)` of growing
  conductor, like CM points of one field and unbounded conductor.
* **UniformlyFrozenClass**: `χ_q(D_n) = −1` for all `n ≥ N` and all primes `q ≡ 2 (3)` beyond
  a bound `y` *independent of `n`*.

**Theorem A (Lean: `EM/Population/UniformFreezing.lean`,
`eq_neg_three_mul_sq_of_nonsquare_two_mod_three`, `confined_of_uniformly_frozen`).**  If at a
single stage `n` the discriminant `D_n` is a non-square modulo every sufficiently large prime
`q ≡ 2 (mod 3)`, then `D_n = −3 s²`.
*Proof.*  `D_n ≡ 1 (mod 4)` gives `χ_q(D_n) = (q / |D_n|)` (Jacobi).  If `3 ∤ D_n`, choose
`q ≡ 1 (mod |D_n|)`, `q ≡ 2 (mod 3)` by Dirichlet: `χ_q(D_n) = +1`.  If `3 ∣ D_n` and
`M = |D_n|/3` is not a square, the Jacobi character mod `M` is nontrivial, so some class `b`
has `(b/M) = −1`; primes `q ≡ b (mod M)`, `q ≡ 2 (mod 3)` give `(q/|D_n|) = (q/3)(q/M) = +1`.
Hence `|D_n|/3` is a square. ∎
So **UniformlyFrozenClass ⟹ Confined from `N` on**.  (The converse is *not* automatic: on a
confined stage `D_n = −3 s_n²` is `0`, hence a square, modulo every prime dividing `s_n`, so a
confined run is uniformly frozen only if the conductors `s_n` have no prime factor `≡ 2 (3)`
beyond a fixed bound.  The correct inclusions are tower ⊂ UniformlyFrozenClass ⊂ ConfinedRun;
corrected 2026-09-24, §12.)  The three questions are then:

1. *Non-uniform ⟹ uniform?*  Frozen at each `q ≡ 2 (3)` with its own threshold `N(q)`, versus
   one threshold for all: the §G / #176 quantifier wall, verbatim.  Not attackable.
2. *Frozen at one `q` ⟹ frozen at a class?*  A statement about the cofactor residues at
   infinitely many primes from one: #90.  Not attackable.
3. **Confined ⟹ tower?**  Purely Diophantine: if `4c_n − 1 = 3 s_n²` for all large `n`, is
   `s_n = 1` eventually?  This is the arithmetic core, and it is new.

### 11.3 What confinement forces (Lean: `EM/Population/Confinement.lean`)

Confinement is the first hypothesis in the project from which a **positive divisibility
fact** follows (screen 1): from `4 c_n E_{n+1} = (2E_n − 1)² + 3 s_n²` and the inertness of
`ℓ ≡ 2 (3)` in `ℚ(√−3)` (`dvd_of_dvd_sq_add_three_sq`, via `not_isSquare_neg_three`), every
prime `ℓ ≡ 2 (mod 3)` dividing `E_{n+1}` divides it **twice** (`sq_dvd_of_confined`; consecutive
Euclid numbers are coprime, `not_dvd_euclid_of_dvd_euclid_succ`, so `ℓ ∤ c_n`).  Hence on a
confined orbit with squarefree Euclid numbers every multiplier is `≡ 1 (mod 3)`
(`multiplier_not_two_mod_three`): confinement is a strong form of `¬CI(2 mod 3)`, and
`CI(2 mod 3) ⟹ (C∞)` is on file.  Squarefreeness of the Euclid numbers is the same open
question as for Sylvester's sequence (Vardi).

### 11.4 The confined step equation

On a confined orbit, consecutive stages satisfy the norm equation

    (p − 2)² + 3 (p s)² = p' (3 s'² + 1),      p = p_{n+1}, s = s_n, p' = p_{n+2}, s' = s_{n+1},

i.e. `4E_{n+1} = N((p−2) + ps√−3) = N(π') · N(1 + s'√−3)` in `ℤ[ω]`.  The tower is `s = s' = 1`,
`p' = p² − p + 1`.  So a confined orbit is a chain of integer points on the quadric
`X² + 3Y² = Z(3W² + 1)` linked by `Y = sX`-type relations and the greedy rule.  Three
analogies, kept open:
* *Squares in recurrences* (Cohn, Bugeaud–Mignotte–Siksek): "`(4c_n − 1)/3` is a perfect
  square for all large `n`" is a square-in-a-recurrence condition, the kind of statement that
  is finite for linear recurrences.  Our recurrence is nonlinear and carries the `lpf`
  twist; the finiteness technology (Baker, modularity) does not apply as it stands.
* *CM points of one field with unbounded conductor* (the tractable case of André–Oort):
  confined stages are orders `ℤ[s_n ω]`; the analogy suggests confinement is the *easy*
  side of the dichotomy, where the Galois theory (ring class fields of `ℚ(√−3)`) is explicit.
  The obstruction of §9.3 persists: the class group of `ℤ[s_n ω]` acts on the ideals above
  `E_{n+1}`, i.e. on the tree, not on the orbit.
* *Function fields*: over `𝔽_p[t]` a confined orbit has `D_n = a·s_n²` with `a` a
  non-square constant, and the constant-field mechanism forces nothing about `s_n`; the
  `𝔽_5[t]` towers are confined with `s_n = 1`.  Whether a confined non-tower orbit exists over
  any `𝔽_p[t]` is open and would be a decisive calibration: it would show confinement does
  not force the tower where every other tool is a theorem.

### 11.4a Calibration over `𝔽_p[t]` (computation, not evidence)

Thirty stages from six seeds over `p = 3, 5, 7, 11, 13`, tagging each stage as a tower stage
(`c_n = 1`), constant-field confined (`1 − 4c_n = a·s²`, `a` a non-square constant), split
(`a` a square) or neither.  Over `𝔽_5` the seeds `X, X+1, X+2, X²+1, X(X+1)` are perpetual
towers (all confined trivially); `X²+X+2` is not a tower.  Isolated confined *composite*
stages do occur at low degree — `𝔽_11`, seed `X²+1`, stage 1: `D = 7(t+4)²`; `𝔽_3`, seed
`X²+1`, stage 3: `D = 2(t³+1)²` — each followed by an unconfined stage; no confined run of
length two was seen anywhere.  So single-stage confinement is an ordinary low-degree
coincidence (probability `≍ p^{−deg/2}`), and question (3) is genuinely about *runs*: the
right statement is "no orbit is confined at all large stages unless it is a tower".

### 11.5 Verdict

"Frozen ⟹ tower" is not one question but three.  Two of them (1, 2) are the familiar walls
in new clothing and should not be attacked.  The third — **Confined ⟹ tower** — is a
genuinely Diophantine statement about the conductor of the tower's field along the orbit,
the first hypothesis with a positive divisibility consequence, and the natural next
research question of the theory.  Its function-field form is the right first test.  Two
concrete sub-targets: (a) Theorem A in Lean — done (`UniformFreezing.lean`: reciprocity for a
negative discriminant `≡ 1 (4)`, the nontrivial Jacobi character of an odd non-square,
Dirichlet in a class mod `3M`);
(b) over `𝔽_2[t]` and `𝔽_5[t]`, decide whether a confined stage other than a tower stage
ever occurs in the computed branches — a finite question that calibrates (3).  Over `𝔽_2[t]`
the discriminant degenerates (`4 = 0`) and confinement reads `c_n + 1 ∈ ℘(𝔽_2[t])`,
`℘(f) = f² + f` (Artin–Schreier; the tower has `c_n = 1`).  Checked on the 40-stage branches
of §10.2: the only confined stages are the four irreducible ones (stages 0, 1, 2, 12); no
composite stage is confined.  Consistent with (3), and no more than that.


## 12. Question (3), faced: confined runs (2026-09-24)

### 12.1 What a confined run is, exactly

Stage `n` confined ⟺ `4c_n − 1 = 3 s_n²` ⟺ the cofactor is a **cuban number**
`c_n = 3t² + 3t + 1 = (t+1)³ − t³ = N(t + (t+1)ω)`, the norm of an Eisenstein integer of real
part `1/2`.  Cuban numbers: `1, 7, 19, 37, 61, 91, 127, …`; the tower is `c_n = 1`.  A
**confined run** (`Confinement.ConfinedRun`) is "confined at every stage from some `N` on".
Question (3) in its honest form: *a confined run has only finitely many composite stages*,
i.e. it is eventually a tower.

Three facts, all in Lean now (`Confinement.lean`):
* `multiplier_one_mod_three_of_confined_pair`: on two consecutive confined stages the
  multiplier is `≡ 1 (mod 3)`, **unconditionally** — a `p ≡ 2 (3)` would divide `E_{n+1}`
  twice (stage `n` confined) hence divide the cuban cofactor `c_{n+1}` (stage `n+1`
  confined), which has no prime factor `≡ 2 (3)` because `3s'² ≡ −1` would make `−3` a square.
  This removes the squarefreeness hypothesis of §11.3 on runs.
* `not_mc_of_confinedRun`: **a confined run refutes MC** — no prime `≡ 2 (mod 3)` is ever
  a multiplier past the start of the run, so a Dirichlet prime beyond the bag is missing.
* `perpetual_of_confinedRun_of_dichotomy`: under the dichotomy conjecture a confined run is
  eventually a Sylvester tower.  **Question (3) is a consequence of the dichotomy
  conjecture**, i.e. it is the *weakest* statement in the family: MC-failure ⟹ tower is the
  conjecture, and confined runs are a very special way of failing MC.

### 12.2 The dynamics on confined states is a partial map

Encode a composite confined stage by `(p, s)` with `E = p·(3s²+1)/4`, `p = lpf(E)`
(i.e. `(3s²+1)/4` is `p`-rough).  The next stage is determined: `4E' = (p−2)² + 3p²s²`,
`p' = lpf(E')`, and the stage is confined iff `(4E'/p' − 1)/3` is a perfect square.  So the
confined composite states carry a **partial deterministic map** `(p, s) ↦ (p', s')`, defined
only when the coincidence holds, with `E' > E` (no cycles).  Question (3) for all seeds says:
*no orbit of this partial map is infinite* — the same shape as "every Collatz orbit
terminates", in Conway's generalized-Collatz class where the general problem is undecidable.
Without the `lpf` condition the step equation

    (p − 2)² + 3 (p s)² = p' (3 s'² + 1)

is a Pell-type equation in `(s, s')` for each fixed `(p, p')` (discriminant `p'`), with
infinitely many solutions whenever one exists; the condition that makes chains thin is
exactly `p' = lpf(E')`, i.e. `(3s'²+1)/4` is `p'`-rough — an anatomical condition.  For `p' = 7`
that roughness is automatic (`3s'²+1` is never divisible by `2, 3, 5`), and the equation with
`p = 7` has no solutions at all (`49 s² − 7 s'² = −6` is impossible mod 7); with `p = 13` it
reduces to `Y² − 7X² = −38` with `13 ∣ Y`, a congruence condition on a Pell orbit.

### 12.3 Reconnaissance over `ℤ` (computation, calibration only)

All composite confined states `(p, s)` with `p ≡ 1 (3)` prime `< 400`, `s < 4000` odd,
`(3s²+1)/4` `p`-rough, `E ≡ 1 (3)`: 29,734 states.  Of these 3,875 have a confined
successor — 3,869 because `E'` is *prime* (a tower stage, `s' = 1`; about 13%, the norm-form
values having no prime factor `≡ 2 (3)`), and **6 whose successor is again composite and
confined**:

    (19, 793) → (37, 2477) → prime stage;   (37, 51) → (1483, 49);   (67, 2917) → (7, 73869);
    (73, 471) → (127, 3051);   (193, 259) → (37831, 257);   (277, 371) → (77563, 369).

None continues to a third composite confined stage.  Three of the six lie on a line,
`s = (4p+5)/3`, `s' = s − 2`, `p' = p² + 3p + 3 = Φ₃(p+1)` — and that is an **identity**
(`Confinement.shifted_tower_identity`, `confined_pair_of_shifted_tower`): with `p = 3k+1`,

    (p c − 1) p + 1 = p' c',   c = 12k²+18k+7,   p' = 9k²+15k+7,   c' = 12k²+6k+1,

both cofactors cuban.  So a composite confined stage of the form `E_n = p(4p²+10p+7)/3` with
`p = lpf E_n` has a confined successor whenever `p² + 3p + 3` is the least prime factor of
`E_{n+1}` — three quadratics in `k` simultaneously prime, which Schinzel's hypothesis makes
infinitely frequent.  **Length-2 composite confined runs are not a finite accident; they have
an algebraic source**, the shifted tower `p ↦ Φ₃(p+1)` next to the tower's `p ↦ Φ₃(p−1)`.  The
family does not extend: `s' = s − 2` is not `(4p'+5)/3`, so the third stage is generic again.
The other three pairs are off the line and may be genuine coincidences or members of other
families; not examined.

### 12.4 Analogies, with verdicts

* *Collatz / generalized Collatz* (Conway): the partial map of 12.2 is in the class where
  termination is undecidable in general; population theorems only (Terras, Tao).  Same wall,
  now stated for a much thinner map.
* *Squares in recurrences* (Cohn; Bugeaud–Mignotte–Siksek): finiteness of perfect powers in
  Lucas sequences uses linear-recurrence identities plus Baker or modularity.  Our condition
  `(4c_n − 1)/3 = □` is of that type, but `c_n` is not a recurrence: it is `E_n / lpf(E_n)`.
  The one place a genuine recurrence exists is a tower segment, where `c = 1` and there is
  nothing to prove.
* *Pell chains / Vieta jumping*: consecutive states satisfy Pell-type equations sharing a
  variable; Vieta jumping produces *smaller* solutions from larger ones on a single Markov-type
  equation, but here the equations change with `(p, p')` and the chain goes up in size.  No
  descent.
* *Ramanujan–Nagell* (`x² + 7 = 2^n`): one exponential and one square, finitely many
  solutions by Skolem/Baker.  Our "exponential" is the doubly exponential growth of `E_n`
  along the orbit and the square is the conductor; but the coupling passes through `lpf`,
  which no transcendence method sees.
* *CM points of growing conductor* (§11.4): the explicit Galois theory of ring class fields
  of `ℚ(√−3)` acts on the ideals above `E_{n+1}`, i.e. on the tree; it does not see which
  factor is least.  Same as §9.3.
* *Function fields*: over `𝔽_q[t]` isolated confined composite stages exist (§11.4a); a
  confined run would be a sequence of cofactors all of the form `(1 − a s²)/4`.  The same
  partial map exists there and the same question is open; it is again the right first test.

### 12.5 Verdict on (3)

The reconnaissance changed the question.  The naive heuristic — a confined successor is a
coincidence of probability `≍ E^{−1/2}`, so runs of length two are finite in number and runs of
length three never occur — is **wrong at length two**: the unlikely locus contains an
algebraic curve on which the coincidence is automatic, and the arithmetic condition on that
curve is a Schinzel-type primality condition, satisfied infinitely often conjecturally.  This is
the Zilber–Pink picture realised inside question (3) itself: special subvarieties (here the
tower and the shifted tower) sit inside the exceptional locus, and the honest form of (3) is a
**structure question**: *is every long confined run explained by an algebraic family, and do
such families exist for every length?*  Length 1: the tower.  Length 2: the shifted tower.
Length 3: none found, no identity found.  If families of every length exist, confined runs of
every finite length exist (under Schinzel) and (3) — an infinite run forces the tower — becomes
a statement about the *limit* of a tower of algebraic families, which is where Ax–Schanuel-type
functional transcendence would enter in the analogy.  If they do not, (3) reduces to length-3
finiteness plus the tower.  Either way the next concrete step is algebraic, not statistical:
search for identities `(p'−2)² + 3p'²s'² = p''(3s''²+1)` along `(p', s') = (Φ₃(p+1), (4p−1)/3)`.

Facing (3) moved it from a slogan to a precise place: it is the weakest member of the
dichotomy family (a consequence of the conjecture, `perpetual_of_confinedRun_of_dichotomy`),
it is a termination statement for a partial deterministic map on pairs `(p, s)`, and the only
thing that makes that map thin is the least-prime-factor condition — the same anatomical
condition that blocks every other route.  What is new and positive: confined pairs force
`≡ 1 (mod 3)` multipliers unconditionally, confined runs refute MC outright, and the step
equation is explicit enough to be searched.  What is not available: any mechanism for
termination.  I would not attack (3) directly; I would keep it as the cleanest *test case*
for a future mechanism, because a mechanism that cannot show that cuban cofactors stop must
fail on the general problem, and one that can is already saying something about `lpf`.

## 13. The algebra of confined runs (2026-09-24; theory only, no computation)

### 13.1 Eisenstein form

Put `δ_n = (1 + s_n√−3)/2 ∈ ℤ[ω]`, `ω = (1+√−3)/2`, `N(x + yω) = x² + xy + y²`.  A confined stage
is one with `c_n = N(δ_n)`, and `δ_n` is the root `ω_n` of `y² − y + c_n` of §1, so the norm
identity reads

    E_{n+1} = N(p_{n+1} δ_n − 1),        4E_{n+1} = N((p − 2) + s p √−3)

(`EisensteinFamilies.four_euclid_succ_eq_norm`).  The next stage is confined iff
`N(p δ_n − 1) = p_{n+2} · N(δ_{n+1})` with `δ_{n+1}` again of real part `1/2`.  Since `ℤ[ω]` is
a PID this says: `p δ_n − 1` and `π_{n+2} δ_{n+1}` (`N(π) = p_{n+2}`) have the same prime ideal
factors up to conjugation of each factor and a unit.  A **polynomial family** — a family of
confined pairs indexed by `p` with `s, s', p'` polynomial in `p` — is the case where the
conjugation pattern is uniform, i.e. a factorization in the unique factorization domain
`ℤ[ω][p]`:

    (F)   p δ(p) − 1 = ε · π'(p) · δ'(p)^{σ},   σ ∈ {id, conj},   N(π') = p'(p),   δ' = (1 + s'(p)√−3)/2.

### 13.2 The two known families are the two conjugation choices

* **Tower** (`s = 1`, `δ = ω`, a unit):  `p ω − 1 = ω · (p − ω̄)`, so `π' = p − ω̄`,
  `p' = N(p − ω̄) = p² − p + 1 = Φ₃(p − 1)`, `δ' = ω = δ`, `σ = id`
  (`tower_factorization`: `2((p−2) + p√−3) = (1+√−3)(2p − 1 + √−3)`).
* **Shifted tower** (`s = (4p+5)/3`):  `p δ − 1 = −π' · δ̄'` with `π' = (p+1) + ω̄`,
  `p' = N((p+1) + ω̄) = p² + 3p + 3 = Φ₃(p + 1)`, `δ' = (1 + s'√−3)/2`, `s' = (4p−1)/3`, `σ = conj`
  (`shifted_tower_factorization`: `2√−3·3α = −3(2p + 3 − √−3)(4p − 1 + √−3)`, using
  `2p − ω̄ = √−3 · δ̄'`).

So the tower and the shifted tower are the *same* mechanism with the two possible conjugation
choices of the `δ`-factor, and the two Eisenstein primes `p − ω̄`, `(p+1) + ω̄` at distance one
from `p`.  The tower is degenerate because its `δ` is a unit (`N(δ) = 1`, a prime stage); the
shifted tower is the first non-degenerate solution of (F).

### 13.3 Classification of linear families

Take `s = m p + r`, `s' = m p + v` (the leading coefficients must agree up to sign), and
`p' = p² + α p + β` monic.  Comparing coefficients in `N(2(pδ−1)) = p'(p) · (1 + 3s'(p)²)`:

    β (3v²+1) = 4,     (3v²+1) α + 6 m v β = −4,     2r = 2v + m α,     m α²/4 − v α − m β = 0.

With `w = 3v² + 1` the last equation becomes `36 v m³ + 12 w m² + 3 v w² m + w³ = 0`, which
factors as `(3 v m + w)(12 m² + w²)` (`linear_family_cubic`, `linear_family_root`).  The second
factor is positive, so `m = −w/(3v)`, and then `α = β = 4/w`, `r = v − 2/(3v)`.  Every linear
family is therefore

    p' = p² + (4/w) p + 4/w,   s = (v − 2/(3v)) − (w/(3v)) p,   s' = v − (w/(3v)) p,   w = 3v² + 1,

a one-parameter *rational* family indexed by `v ∈ ℚ^×`, plus the degenerate branch `m = 0`
(the tower, `r = ±1`).  Integrality of `p'` needs `4/w ∈ ℤ`: `w ∈ {1, 2, 4, 4/3}`.  `w = 1` is
`v = 0` (tower); `w = 4/3` is `v = ±1/3`, the shifted tower; `w = 4` is `v = ±1`, giving
`p' = Φ₃(p)` and `s = (4p−1)/3` but `s' = (4p−3)/3 ∉ ℤ` for `p ≡ 1 (3)` — a rational family
with no integral points on the relevant residue class; `w = 2` has no rational `v`.
**The tower and the shifted tower are the only integral linear families** (with monic `p'`;
a non-monic `p' = λ p² + …` needs `λ` a rational square and is a small extension).

### 13.4 Length three and reducibility towers

Along a polynomial family the next Euclid polynomial is `E_{n+2}(p) = N(p'(p) δ'(p) − 1)`, with
`p' δ' − 1` a polynomial of degree `deg p' + deg s'` over `ℚ(ω)`.  If it is *irreducible* in
`ℚ(ω)[p]`, the only polynomial continuation is a tower step (`p'' = E_{n+2}(p)` itself, `s'' = 1`),
which is confined but prime.  A *composite* confined continuation needs `p' δ' − 1` reducible
with a factor of norm `1 + 3(polynomial)²`.  For the shifted tower `p' δ' − 1` is a cubic in `p`
over `ℚ(ω)`; reducibility means a root in `ℚ(ω)`, a finite check by the rational root theorem
in `ℤ[ω]` (not carried out; the three instances found did not continue, consistent with
irreducibility).  So the object behind (3) is a **reducibility tower**: a polynomial orbit
`E_k(p)` with `E_{k+1} = (E_k − 1) q_k + 1`, `q_k ∣ E_k` an irreducible factor, *all* `E_k`
reducible — the exact opposite of the generic tower of `GenericTower.lean`, where every level
polynomial is irreducible and the only polynomial orbit is the tower itself.

### 13.5 What (3) is, in this language

The exceptional locus of (3) is stratified:

* the **algebraic part** — the union of all polynomial families, each of finite composite
  length unless an infinite reducibility tower exists;
* the **transcendental part** — confined pairs of the integer orbit lying on no family
  (three of the six pairs found in §12.3 may be of this kind).

Hence (3) splits into an algebraic question and a #90 question:

1. *Is there an infinite polynomial confined orbit with infinitely many reducible stages?*
   This is about factorizations in `ℤ[ω][p]`, in principle decidable level by level, and the
   honest algebraic core.  Conjecture: no — the length of composite confined polynomial
   families is bounded (perhaps by 2), by the same principle that makes the generic tower
   irreducible (Hilbert irreducibility, Capelli): reducibility of a specialization is the
   exception, and an infinite sequence of reducible Euclid polynomials would be an identity
   the generic tower forbids.
2. *Does the integer orbit meet the union of the finite families infinitely often, or is it
   confined by coincidence infinitely often?*  Each family is a curve in the `(p, s)`-plane,
   the union is thin, and this is the orbit-statistics wall.

The Zilber–Pink analogy is now literal rather than metaphorical: (3) has an algebraic part
made of special curves (the tower, the shifted tower, the rational families of 13.3) and a
transcendental part; the functional equation (F) plays the role of the Ax–Schanuel input
that classifies the special curves; and the conjecture "the algebraic part has bounded length"
is the analogue of "there are only finitely many special subvarieties of a given complexity".

### 13.6 Analogies, with verdicts

* **Hilbert irreducibility / Capelli.**  The right frame for question 1: polynomial orbits
  are generic, integer orbits are specializations, and `GenericTower.lean` already says the
  generic orbit is irreducible at every level.  A reducibility tower would be a polynomial
  identity of infinite length; none is known and the classification of 13.3 gives none of
  length three among linear families.  *Verdict: the tool that matches question 1.*
* **Markov / Vieta.**  The cubic `(3vm + w)(12m² + w²)` is a Markov-type factorization (a
  linear factor times a definite quadratic), which is why the linear families form a single
  rational curve.  *Verdict: explains the classification, no descent.*
* **CM conductors.**  Confined stages are orders `ℤ[s_n ω]`; a family is a polynomial law for
  the conductor.  *Verdict: language.*
* **Function fields.**  Over `𝔽_q[t]` a polynomial family *is* an orbit (`p := t` or any
  polynomial) whenever the least-degree conditions hold, so families are exactly the confined
  orbits of the generic dynamics, and integer confined pairs on a family are its
  specializations — the same specialization principle as the generic tower.  *Verdict: the
  place to decide question 1 first.*
* **Schinzel / Bunyakovsky.**  Realizing a family over `ℤ` needs its polynomials
  simultaneously prime; this is what makes length-2 confined runs infinite in number
  conjecturally.  *Verdict: the bridge from families to integer orbits, conjectural.*

### 13.7 Verdict

Question (3) is now two questions.  The algebraic one — bounded length of composite confined
polynomial families, i.e. no infinite reducibility tower — is a statement about factorizations
in `ℤ[ω][p]` that can be attacked level by level and whose first level is completely classified
here (tower, shifted tower, and nothing else among linear families).  The other is #90.  The
theory's contribution is that the "probability-zero" reading of (3) was wrong exactly where
Zilber–Pink says it should be, and that the correction is computable algebra.

## 14. `CI(3 mod 4)`: theories and analogies (2026-09-24; no computation)

`CI(3 mod 4)`: infinitely many Euclid–Mullin primes are `≡ 3 (mod 4)`.  Known: every Euclid
number is `≡ 3 (mod 4)`, hence has a prime factor `≡ 3 (mod 4)` (the class-hit fact); on the
Sylvester tower the multipliers are the Euclid numbers themselves, so `CI(3 mod 4)` holds there
(`¬CI(3 mod 4) ⟹ (C∞)`, `ClassInfinitude.lean`).  Its content is therefore
**`(C∞) ⟹ CI(3 mod 4)`**: on the branch with infinitely many composite Euclid numbers, the
least factor is `≡ 3 (mod 4)` infinitely often.

### 14.1 What kind of statement it is

* **A half-set confinement of the multiplier.**  `¬CI(3 mod 4)` says the multipliers
  eventually all lie in `1 + 4ℤ₂`, the index-2 subgroup of `ℤ₂^×`.  This is the same shape as
  Frozen (§11: cofactor residue in a half-set) and as confinement to `ℚ(√−3)` (§12: all late
  multipliers split in `ℚ(√−3)`, proved as a *consequence*): here "all late multipliers split
  in `ℚ(i)`" is the *hypothesis*.  In general, for a quadratic field `K`, "all late
  multipliers split in `K`" makes every inert prime beyond the bag missing, hence refutes MC;
  the class-infinitude statements are the negations of these split-runs, `CI(3 mod 4)` being
  `NotSplit(ℚ(i))`, `CI(2 mod 3)` being `NotSplit(ℚ(√−3))`.
* **Why the 2-power (and `p²`) moduli are the weak targets.**  Write `W(m)` for "infinitely
  many multipliers `≢ 1 (mod m)`".  On the tower the multiplier is `E_n ≡ 1 + P_n (mod m)`, which
  is `≡ 1` iff `m ∣ P_n`; so for squarefree `m` with captured prime factors (`m = 3`, `6`, …) the
  tower has all late multipliers `≡ 1 (mod m)` and `W(m)` sits *above* the floor (`W(3) = CI(2 mod 3)
  ⟹ (C∞)`), while for `m = 4`, `9`, `p²` with `p` in the bag, `E_n ≢ 1 (mod m)` and `W(m)` holds
  on the tower.  `W(4) = CI(3 mod 4)` is the cleanest member of the family `{W(p²)}` of targets
  not blocked by the floor.
* **The 2-adic reformulation** (Lean, `ClassThreeModFour.lean`): `P_n ≡ 2 (mod 4)`, and a
  multiplier `≡ 3 (mod 4)` is exactly a change of `P_n mod 8`.  So `CI(3 mod 4)` ⟺ **the
  accumulator (equivalently the Euclid number) is not eventually constant modulo 8** ⟺ the
  torsion component `{±1}` of the 2-deleted walk `O_n = P_n/2` in `ℤ₂^×` keeps flipping.  It is a
  deleted-walk statement (§8.2) for the seed prime `2`, the first captured prime, exactly as
  "the 3-deleted walk hits `−1` infinitely often" is a class-count parity for the prime `3`.
  And it is a *torsion* statement, the kind #177 says heights and logarithms cannot see.
* **The Legendre reading.**  `P_n ≡ −1 (mod p_{n+1})`, so `(P_n / p_{n+1}) = χ₄(p_{n+1})`:
  `CI(3 mod 4)` ⟺ the accumulator is a quadratic non-residue modulo its own next multiplier
  infinitely often.  Reciprocity turns this into a law along the orbit: with `O_n` the odd part,
  `(p_{n+1} / O_n) = χ₄(p_{n+1}) · (2/p_{n+1}) · (−1)^{(O_n−1)(p_{n+1}−1)/4}` — a one-bit
  constraint on the new prime modulo the old accumulator, of the type
  `Reciprocity.no_reciprocity_induction_proof` shows cannot block anything.

### 14.2 Genus theory, and why the max rule is different

`E_n ≡ 1 (mod P_n)` puts `E_n` in the principal genus for every fundamental discriminant built
from bag primes: the Kronecker symbols `(d/q)` over the prime factors `q` of `E_n` multiply to
`+1` for all such `d`, and to `−1` for `d = −4` (`E_n ≡ 3 (mod 4)`).  Hence the multiplier `p`
and the cofactor `c` share all bag characters, and `χ₄(c) = −χ₄(p)`.  These are exactly the
"mod-4 law" and "discriminant law" behind Cox–van der Poorten and Booker for the *largest*
factor.  Their proofs work because under the max rule the cofactor is *smooth* (all its primes
are smaller than the chosen one), so when the small primes are all known the cofactor's
factorization is known and the symbols can be evaluated.  Under the min rule the cofactor is
*rough* — its primes are the unknown large ones — and the same laws say nothing about which
factor is least.  This is the reciprocity memo's verdict, now specialized to the one class
statement where the positive fact (a `3 (mod 4)` factor always exists) is available.

### 14.3 The Gaussian locus is empty (Lean)

The quadratic-step theory attaches to each stage the field `ℚ(√D_n)`; the tower lives in
`ℚ(√−3)`, and §12 showed the failure of `(C∞)` has that algebraic locus.  The corresponding
locus for `CI(3 mod 4)` would be confinement to `ℚ(i)`: `D_n = −s²`, i.e. `4c_n − 1` a perfect
square.  **This never happens** (`four_cofactor_sub_one_not_square`): it would make
`4c_n E_{n+1} = (2E_n − 1)² + s²` a sum of two squares, so every prime `≡ 3 (mod 4)` would divide
`E_{n+1}` to even order (the cofactor being coprime to `E_{n+1}`), against `E_{n+1} ≡ 3 (mod 4)`.
So a failure of `CI(3 mod 4)` has **no quadratic-field locus**: in the Zilber–Pink language its
exceptional set has empty algebraic part at this level.  That is a precise sense in which
`CI(3 mod 4)` is the *purest* instance of #90 — nothing algebraic could make it fail, and
nothing algebraic can prove it; only the orbit statistics remain.

### 14.4 Analogies, with verdicts

* **Euclid's proof for primes `≡ 3 (mod 4)`.**  `4m + 3` has a prime factor `≡ 3 (mod 4)`; take
  *any* such factor and the infinitude follows.  Mullin's rule takes the *least* factor, which
  may be `≡ 1 (mod 4)`; `CI(3 mod 4)` is Euclid's argument with the least-factor rule.  The gap
  between "some factor" and "the least factor" is the whole content.  *Verdict: the exact
  shape, and the reason the statement is weak but open.*
* **The primorial analogue.**  For explicit sequences of the same shape — `x_k = 4·k# + 3`, or
  `k# − 1` — "the least prime factor is `≡ 3 (mod 4)` infinitely often" is, to my knowledge,
  equally open: nothing controls the class of the least prime factor of a sparse deterministic
  sequence, dynamics or not.  *Verdict: `CI(3 mod 4)` is at least as hard as a dynamics-free
  problem nobody can do; the dynamics is not what makes it hard.*
* **Chebyshev's bias** (Rubinstein–Sarnak): primes `≡ 3 (mod 4)` lead in logarithmic density.
  The population analogue here is exact and head-dominated (`HeadDomination.lean`): among
  `y`-rough integers `≡ 3 (mod 4)` the least factor is `≡ 3 (mod 4)` with an explicit relative
  density near `1/2`.  *Verdict: population only; the orbit inherits nothing (#90).*
* **Prime divisors of recurrences** (Hasse, Lagarias: the primes dividing some Lucas number
  have density `2/3`, by Chebotarev in Kummer extensions).  Class distribution of prime
  *divisors* of a sequence is accessible when the sequence is a linear recurrence; ours is not,
  and in any case "divides some `E_n` in class `3 (mod 4)`" is already trivial here — the
  question is about the *least* divisor.  *Verdict: wrong quantity.*
* **Zsigmondy / primitive divisors.**  Positive existence of new prime divisors, no class
  control.  *Verdict: not applicable to the class.*
* **Fermat's two-squares theorem.**  The one place a `3 (mod 4)` statement becomes algebraic —
  odd multiplicity of `3 (mod 4)` primes in a non-sum-of-two-squares — and it gave the only
  theorem of this section (14.3).  *Verdict: yields an exclusion, as the sign asymmetry
  predicts; nothing positive.*
* **2-adic torsion vs heights (#177).**  `CI(3 mod 4)` is a statement about the `{±1}` component
  of a 2-adic walk; every functional built from sizes or logarithms factors through the
  torsion-free part.  *Verdict: heights are blind to it, as to MC.*

### 14.5 Verdict

`CI(3 mod 4)` is the weakest open statement about the sequence with a positive ingredient, and
the theory says exactly why it is still out of reach: it is the least-factor version of
Euclid's `3 (mod 4)` argument, equivalent to non-constancy of the 2-adic torsion of the
accumulator, with no algebraic locus on which it could fail and hence no algebraic mechanism
by which it could be proved.  Its function-field twin over `𝔽_2[t]` is the trace exclusion
(§10.1) — there the "class" `Tr = 1` is *forced* on tower steps and open otherwise — and the
primorial analogue is open with no dynamics at all.  What was provable was proved: the mod-8
reformulation and the emptiness of the Gaussian locus.  A route to `CI(3 mod 4)` would be a
route to controlling the least prime factor of one sparse sequence in a residue class, which
is the same demand every other target makes.  I would not attack it directly either; I would
keep it as the statement to test any future mechanism on *first*, before `(C∞) ⟹ MC`, because
it asks for a half-set rather than a single class.

## 15. The object: CM points, and the Langlands side of one step (2026-10-25)

Question (user, Session 322): the Mullin sequence should be linked to an *object*, as modular
forms are linked to elliptic curves, so that arithmetic properties of the sequence become
properties of the object.  What object?  Lean: `EM/Population/CMPoint.lean`.

**What Langlands needs and what the sequence lacks.**  Modularity transports an Euler product:
one local factor per prime, primes entering through Frobenius.  The rule `P ↦ P · lpf(P+1)` is
not multiplicative; the `+1` is an additive step inside a multiplicative recursion, and the
walk's "L-function" `Σ χ(P_n) n^{−s}` has no Euler product.  This is the Four-Way Blocker in
Langlands language.  The GL(1) correspondence (Dirichlet characters of the walk) is the
existing character-sum layer, and it is a tautology: CME ⟺ MC.

**Where the `+1` becomes algebraic: one step.**  §1 writes `E_{n+1} = N(p_{n+1} ω − 1)`.  Read
as a binary quadratic form,

    E_{n+1} = Q_n(−1, p_{n+1}),   Q_n(x, y) = x² + x y + c_n y²,   disc Q_n = 1 − 4 c_n = D_n

(`euclid_succ_eq_principalForm`, `four_mul_principalForm`).  Inside one step the `+1` is
absorbed into the principal form.  That is why an object exists there and nowhere else.
The object: the order `O_n` of discriminant `D_n`, equivalently the **CM point of
discriminant `D_n` on the `j`-line**; its automorphic side is the weight-one theta series of
the forms of discriminant `D_n`, Galois side the dihedral representations `Ind χ` for class
group characters `χ` of `K_n = ℚ(√D_n)`.

Dictionary:

| sequence | object |
|---|---|
| prime factor `ℓ` of `E_{n+1}` | `ℓ` splits or ramifies in `K_n` (§3 (T1)); inert-prime coefficients of the theta series vanish |
| `E_{n+1}` itself | represented by the principal form at `(−1, p_{n+1})` (`represents_euclid_succ`) |
| least factor `q = lpf E_{n+1}` | least norm among the prime ideals in the principal relation `(p_{n+1}ω − 1) = ∏ 𝔮_i` |
| `q < c_n` (a small least factor) | `𝔮` non-principal: the principal form takes no value `< c_n` off the axis `y = 0` (`principalForm_ge_of_ne_zero`, `not_represents_of_lt`); class order `≥ log c_n / log q` (`represents_pow_imp_le`) |
| prime stage (`c_n = 1`) | `D_n = −3`: the CM point is `ρ`, the elliptic point of order 3, `j = 0`; `Φ₆(x) = N(x − ω)` in `ℤ[ω]` (`disc_eq_neg_three_iff`) |
| Sylvester tower | the **constant** CM point `j = 0` (`perpetual_disc_eq_neg_three`, converse `perpetual_of_disc_eq_neg_three`) |
| `(C∞)` | the CM point leaves `ρ` infinitely often (`infinitelyManyComposite_iff_disc_ne_neg_three_io`) |
| confined stage `D_n = −3 s²` (§11) | the order `ℤ[sω]` of conductor `s`: a point of the **Hecke orbit of `ρ`**, `j = 0` with growing conductor (`confined_iff_disc_eq_neg_three_mul_sq`) |
| frozen prime (§4) | a prime inert in every late `K_n` |
| MC | for every `q ≥ 5`, at some stage `q` is the least-norm prime in the principal relation, non-principal when `q < c_n` (`mullin_implies_nonprincipal_least_factor`) |

So the exceptional locus of the paper (tower ⊂ confined ⊂ frozen) is literally "special points
of the `j`-line": the tower is one CM point, confined runs are its Hecke orbit, and
`MC ⟹ NoFrozen` says the orbit must leave that locus.  This is the André–Oort shape, which is
why the Zilber–Pink analogy (§9) was right as an *object* even though it is dead as a
*mechanism* (#182).

**The honest limit.**  The order changes at every step and `|D_n| ≈ 4E_n/p_{n+1}` has the size
of the Euclid number.  The correspondence is one step deep: chaining steps means asking how the
element `p_{n+1}ω_n − 1` factors in `O_n` and then feeding the *least* factor into `O_{n+1}`.
No automorphic object sees "least".  The only object that follows the whole path is the
arboreal Galois representation of the re-seeded Sylvester tree, and arboreal representations
have no automorphic side; the 2026-08-17 (f) result measured that object (Chebotarev input
free, residual gap a size condition).  Elliptic curves do not enter: `Φ₆` is not post-critically
finite (`1/2 ↦ 3/4 ↦ 13/16 ↦ …`), so there is no Lattès structure, and the confined step
equation is a surface, not a curve.

**What the dictionary buys.**  Two things.  (i) A positive, screen-1-shaped translation of
"the least factor is small": a small least factor is a high-order ideal class appearing in a
principal relation.  (ii) The exceptional locus is now a geometric object with a theory
(CM points, Hecke orbits, heights of CM points `≈ log |D_n|` = the growth defect of §2), which
is the right language for the dichotomy conjecture: the generic orbit has unbounded CM height
and the special orbits are those of bounded `j`-complexity.
