# Equivariance scoping: is there a structure in which the greedy step is an orbit? (2026-11-07)

Session 324.  Question (user): go beyond the single-orbit viewpoint — the Mullin orbit could be
a generic object from some other point of view.  The repo had already pushed "generic" along
four axes (seed, branch, time, type; summary in §0 below), and the one direction left open by
dead end #181 was: *find a structure in which the Euclid–Mullin step is equivariant, with the
action on the greedy branch itself rather than on the factor tree.*  This memo is that scoping
pass.  No computation.  Lean: `EM/Population/GreedyRigidity.lean` (0 sorry).

**Verdict up front.**  No such structure exists, and the reason is now a theorem rather than a
failure to find one.  On the seed space the greedy branch has trivial stabiliser and determines
its seed (`eq_of_itinerary_eq`), and the only affine self-conjugacy of the step is the identity
(`affine_commute_eq_id`).  Every group that does appear in one step — the dilation group
centred at `1`, Galois conjugation of `O_n`, `SL₂(ℤ)` through reduction of forms, `Pic(O_n)` —
acts on the fibre or on nothing, never on the branch; the greedy rule is a *selection* inside
each fibre, and a selection with trivial stabiliser is the opposite of an orbit.  What the pass
leaves is one piece of language (greedy = minimum of its ideal class, §2.3) and a sharper
statement of the dichotomy behind #171 and #181 (§1.3).

---

## 0. The four senses of "generic" already on file

| axis | generic object | theorem | why it stops at `2` |
|---|---|---|---|
| seed (Haar on `Ω = ∏ 𝔽_r`) | a.a. seeds | `ProfiniteHeadline.measure_some_prime_missed_eq_zero` (density form: `AlmostAllDensity.almost_all_genmc_density`) | countable sets are null (#90, #155) |
| branch (factor tree) | random / Baire-generic branch | `RandomFactorMC`, `DenseCapture` | purification: the greedy branch is one point of the branch space |
| time (Cesàro, ultrafilter hull) | stationary joint law | logic memo §1.3 | #90 witness `(2,2,3,3)` vs `(2,3,2,3)` |
| type of `2` (model theory) | hyperseed with the type of `2` | #158, #171, logic memo §5 | Loeb-null; axioms weak enough to admit it admit `genSeqAvoid` |

Two further facts frame the question.  In the algebraic sense of "generic point" the generic
Mullin orbit is the *worst* one: the sequence seeded at the indeterminate `x` is a Sylvester
tower (`GenericTower.lean`), and over `𝔽_5[t]` MC is false.  And every effective notion of
genericity excludes the orbit by definition, since it is computable (compare normality of a
computable real: Champernowne is proved by structure, `√2` is open).

So the remaining way for "the orbit is generic" to carry a mechanism is the one that works
elsewhere (Ratner, Furstenberg, André–Oort): a group acting transitively and commuting with the
dynamics, or a height with a lower bound on special points.  Heights were tried on 2026-08-20.
This memo settles the group side.

---

## 1. What an action on the branch must be, and why none exists

The step is `T m = m · minFac(m + 1)` on seeds `m ≥ 1`; `T` is strictly increasing in value,
so the functional graph of `T` is a forest of trees each with one end (the forward ray), and
`T` is not injective (`T 2 = T 3 = 6`, `step_two_eq_step_three`).  An "action on the branch"
is a group `G` acting on seeds, commuting with `T`, whose orbit of `2` is large enough to feed
the transfer principle (`GrandOrbit.transfer_principle`): one seed missing `q` must give
`X^δ` seeds missing `q` below `X`.  Three levels of demand, each closed.

### 1.1 Arithmetic symmetries of `ℕ`: affine rigidity (Lean)

**Theorem** (`affine_commute_eq_id`).  If `m ↦ a m + b` with `a ≥ 1` commutes with `T` on all
seeds `m ≥ 1`, then `a = 1` and `b = 0`.

*Proof.*  `m = 1`: `(a + b) · minFac(a + b + 1) = 2a + b` with `minFac ≥ 2` gives `b = 0`.
Then `minFac(am + 1) = minFac(m + 1)` for all `m`; at `m = r − 1` for a prime `r` this says
`r ∣ a(r − 1) + 1`, i.e. `r ∣ a − 1`, for every prime `r`; so `a = 1`.  ∎

The same two lines kill every "local" candidate: multiplication by a unit of `Ẑ`, translation,
and (logic memo §2, #181) ring automorphisms of `Ω`, coordinate relabelling, and `x ↦ x^k` on
`(ℤ/q)^×`.  The `+1` is the obstruction in every case: it fixes the point `1` of the affine
line, and the only dilation centred at `1` that commutes with "multiply by `minFac(E)`" is the
identity.

### 1.2 Combinatorial symmetries: the forest has many, none arithmetic

Dropping arithmetic, any bijection `φ` of the seeds with `φ ∘ T = T ∘ φ` is an automorphism of
the functional forest.  It permutes components (grand orbits) and, inside a component,
preserves the end; it maps forward orbits to forward orbits
(`genProd_comm_of_step_comm`).  Such automorphisms exist in abundance — infinitely many
components are isomorphic as rooted-end trees (bare rays, for instance) and may be permuted
freely — but the commutation alone constrains nothing about *which primes the image orbit
captures*.  So the demand "preserve `Misses q`" is an additional arithmetic axiom, and the
question becomes: which arithmetic data must a symmetry preserve to be useful, and does any
non-trivial map preserve it?

### 1.3 The dichotomy: itinerary rigidity (Lean)

**Theorem** (`eq_of_itinerary_eq`).  If `m, m' ≥ 1` have the same multiplier sequence,
`genSeq m j = genSeq m' j` for all `j`, then `m = m'`.

*Proof.*  Write `P_k = ∏_{j<k} p_j` for the common product of the first `k` multipliers.
`p_k ∣ m P_k + 1` and `p_k ∣ m' P_k + 1`, so `p_k ∣ (m − m') P_k`; `p_k` is coprime to `P_k`
(the multipliers are distinct primes, `AdelicShadow.genSeq_ne_of_lt`), so `p_k ∣ m − m'` for
every `k`; the multipliers are unbounded.  ∎

Hence (`eq_id_of_preserves_itinerary`) a symmetry of the seed space that preserves the
itinerary is the identity.  Now the dichotomy:

* **preserve the finite-horizon data** (the itinerary, equivalently the type of `2` to every
  horizon, #158): the symmetry is trivial by the theorem;
* **preserve only the eventual capture set**: under MC every seed in the basin has the same
  capture set, so the "symmetry group" is `Sym(basin)` and carries no information; outside the
  basin it relabels one hypothetical miss to another and is exactly the hypothesis it was meant
  to prove.

Nothing lies between the two.  This is the group-theoretic form of #171 (axioms weak enough to
be provable admit `genSeqAvoid`; axioms strong enough pin down the orbit) and of the
automorphism row of the logic memo (`(ℕ, ·, S)` is rigid).  The three statements are one fact:
**the greedy branch is a rigid object — its own itinerary is a complete invariant and nothing
moves it.**  A rigid object is not generic for any group.

---

## 2. Where groups do act inside one step, and why none chains

The one-step algebra (`QuadraticStep`, `CMPoint`): `E_{n+1} = N(p ω_n − 1)` in `O_n = ℤ[ω_n]`,
`D_n = 1 − 4c_n`, `c_n = E_n / p_{n+1}`.  Each group below is real; each acts on the wrong
thing.

### 2.1 The dilation group centred at `1`

`E_{n+1} = 1 + p_{n+1}(E_n − 1)`: the Euclid numbers move by dilations `x ↦ 1 + a(x − 1)`,
`a ∈ ℚ^×`, a group isomorphic to `ℚ^×` acting on the affine line and on `Ω`.  The orbit of
`E_0 = 3` under the *semigroup* generated by the chosen primes contains the sequence, but the
choice `a = minFac(E_n)` depends on the point: the dynamics is a cocycle over the walk, not an
action.  Equivariance under the group would mean `minFac(1 + a(x−1)) = minFac(x)` for all `x`,
which is §1.1 again.

### 2.2 Galois conjugation of `O_n`

`β_n = p ω − 1 ↦ β̄_n = (p − 1) − p ω` preserves the norm `E_{n+1}` and swaps each split prime
ideal above it with its conjugate.  Since `β_n` is primitive (`gcd(−1, p) = 1`), `(β_n)`
contains exactly one of `𝔮, 𝔮̄` for every split `q ∣ E_{n+1}`, so conjugation maps the
greedy ideal to the greedy ideal of `β̄_n`.  The sequence of integers `E_n, p_n` is blind to
which of the two is used: conjugation acts **trivially** on the branch.

### 2.3 `SL₂(ℤ)`: greedy as the minimum of its ideal class (language)

Reduction theory is the one place where "least" is a group-theoretic notion: the reduced form
in a class is the fundamental-domain representative of the `SL₂(ℤ)`-action on forms, and its
leading coefficient is the minimum of the class, with CM point of height `√|D| / (2a)`, the
highest in the orbit.

**Proposition** (standard; not in Lean).  Let `q = p_{n+2} = minFac E_{n+1}`, `q ∤ D_n`, and
suppose `4q² ≤ |D_n|` (equivalently `q² < c_n`).  Then the class of the prime ideal `𝔮 ∣ (β_n)`
of norm `q` contains the reduced form `(q, b, (b² − D_n)/4q)` with `|b| ≤ q`; so `q` is the
**minimum of its class**, and the CM point of that class has imaginary part `√|D_n| / (2q)`.

*Proof.*  From `4E_{n+1} = (2x + y)² − D_n y²` at `(x, y) = (−1, p)`, `q ∣ E_{n+1}` and
`q ∤ p` give `D_n ≡ ((2x+y) y^{−1})² (mod q)`; `D_n` odd lifts this to `b² ≡ D_n (mod 4q)`
with `|b| ≤ q`.  The form `(q, b, c)`, `c = (b² − D_n)/4q`, is primitive (`q ∤ D_n`) of
discriminant `D_n`, and `c ≥ |D_n| / 4q ≥ q`, so it is reduced; the leading coefficient of a
reduced form is the minimum of the class.  ∎

Compare `CMPoint.not_represents_of_lt`: `q < c_n` makes `𝔮` non-principal; `q² < c_n` makes
`q` the class minimum.  MC then reads: *for every prime `q`, at some stage `q` is the least norm
in the principal relation `(β_n) = ∏ 𝔮_i`, and at that stage (for `n` large, since
`c_n → ∞` along any orbit with `(C∞)`) `q` is the minimum of its class and the chosen CM point
sits at height `√|D_n| / (2q)`.*  This is language, and it is the honest extent of the
`SL₂(ℤ)`-equivariance: the group acts on `ℍ`, the quotient is already taken, and the fibre
`{𝔮_i}` is a finite set of points of `Y(1)` of different classes.  The greedy rule picks the
one of least norm; among the small factors that is the highest point, but a large factor can
belong to a class with a small minimum (the principal class at a prime stage sits at `ρ`, the
*lowest* point of the fundamental domain), so "greedy = highest" is not monotone over the
whole fibre and defines no section of an action.

### 2.4 `Pic(O_n)`

The class group acts on ideal classes, not on the set `{𝔮_i}` of prime ideals above
`E_{n+1}`, which is not an orbit of anything.  The "conjugate branches" of #181 are Booker's
steering (choose another factor), i.e. the factor tree, and `Pic(O_n)` does not act on it
either; it indexes it.  Moreover `O_{n+1}` is a different order with discriminant
`1 − 4N𝔠` of the size of `E_{n+1}`: the field changes at every step except on confined runs
(`D_n = −3 s_n²`), where the step is a move in the Hecke orbit of `ρ`.  Hecke correspondences
preserve the CM field; a generic step does not; so the branch is not a Hecke orbit except on
the exceptional locus — which is the André–Oort shape already recorded (#182, memo §15).

### 2.5 The affine group over `𝔽_q[t]`, and the shift

The symmetric tie-break over `𝔽_q[t]` is equivariant under `t ↦ at + b` (logic memo §8.5);
it is the only equivariance found anywhere and MC is false there.  Over `ℤ` the only action on
the branch is the shift `n ↦ n + 1`, whose invariant measures are the Cesàro statistics (#90).

---

## 3. What the pass concludes

1. **Greedy is a selection, and selections are rigid.**  In every space where the branch is a
   point — seeds, itineraries, sequences of CM points — the branch has trivial stabiliser and
   is a complete invariant of its seed (§1.3).  Groups appear only inside one step, acting on
   the fibre of possible factors (§2), and the greedy rule is the choice of one point of the
   fibre by an order (`<` on norms) that no group preserves.  "The orbit of `2` is generic for
   a group action" is therefore not an open question but a category error: the rule that
   defines the branch is exactly a symmetry-breaking.
2. **The group side of the "generic object" programme is closed.**  Transitive actions
   commuting with `T` do not exist on `ℕ`, `Ω`, `Ẑ`, the affine line, or the `j`-line.  The
   remaining mechanism of that programme is the height side (CM height
   `≈ log |D_n|` = growth defect, dichotomy conjecture "generic orbit has unbounded CM height");
   its lower bound on special points was the 2026-08-20 height attempt, and #182 records why
   the two bounds are off by a power of `X`.
3. **What to record.**  Dead end #181 now has a theorem as witness
   (`GreedyRigidity.eq_of_itinerary_eq`) and the 2026-11-07 note; no new number, since the
   finding sharpens #181 rather than opening a new approach.  §2.3 is a one-line addition
   to the dictionary of memo §15 if the paper's exceptional-locus section is revised.

Screens (`why_its_hard.tex`): positive divisibility fact about a prescribed prime — none;
char-0 input — none; single orbit — yes (everything is an identity along the orbit); yields
`(C∞)` — no.  Not a route; a closure.
