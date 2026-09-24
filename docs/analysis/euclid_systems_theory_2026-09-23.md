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
4. `Frozen`, `NoFrozen`, and `noFrozen_implies_infinitelyManyComposite`.
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

**Theorem A (paper).**  If at a single stage `n` the discriminant `D_n` is a non-square modulo
every sufficiently large prime `q ≡ 2 (mod 3)`, then `D_n = −3 s²`.
*Proof.*  `D_n ≡ 1 (mod 4)` gives `χ_q(D_n) = (q / |D_n|)` (Jacobi).  If `3 ∤ D_n`, choose
`q ≡ 1 (mod |D_n|)`, `q ≡ 2 (mod 3)` by Dirichlet: `χ_q(D_n) = +1`.  If `3 ∣ D_n` and
`M = |D_n|/3` is not a square, the Jacobi character mod `M` is nontrivial, so some class `b`
has `(b/M) = −1`; primes `q ≡ b (mod M)`, `q ≡ 2 (mod 3)` give `(q/|D_n|) = (q/3)(q/M) = +1`.
Hence `|D_n|/3` is a square. ∎
So **UniformlyFrozenClass ⟹ Confined from `N` on**, and the converse holds trivially.  The
three questions are then:

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

### 11.5 Verdict

"Frozen ⟹ tower" is not one question but three.  Two of them (1, 2) are the familiar walls
in new clothing and should not be attacked.  The third — **Confined ⟹ tower** — is a
genuinely Diophantine statement about the conductor of the tower's field along the orbit,
the first hypothesis with a positive divisibility consequence, and the natural next
research question of the theory.  Its function-field form is the right first test.  Two
concrete sub-targets: (a) Theorem A in Lean (Jacobi reciprocity + Dirichlet);
(b) over `𝔽_2[t]` and `𝔽_5[t]`, decide whether a confined stage other than a tower stage
ever occurs in the computed branches — a finite question that calibrates (3).  Over `𝔽_2[t]`
the discriminant degenerates (`4 = 0`) and confinement reads `c_n + 1 ∈ ℘(𝔽_2[t])`,
`℘(f) = f² + f` (Artin–Schreier; the tower has `c_n = 1`).  Checked on the 40-stage branches
of §10.2: the only confined stages are the four irreducible ones (stages 0, 1, 2, 12); no
composite stage is confined.  Consistent with (3), and no more than that.
