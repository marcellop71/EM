# The rule minFac(N + 1) over 𝔽_p[X]: the fibre frame and the twisted threshold

2026-11-15. Lean: `EM/FunctionField/FibreRule.lean`, `EM/FunctionField/TwistedThreshold.lean`,
`EM/FunctionField/RunMonodromy.lean`, `EM/FunctionField/FirstComposite.lean`,
`EM/FunctionField/CriticalValues.lean`, `EM/FunctionField/CompositeEntry.lean`.

Status of the claims below: the facts in §1 are standard and were recalled from memory, not
looked up; their arrangement around this problem is ours. Everything in §2 and §3 marked
with a Lean name is machine-checked. Nothing here proves a case of the function-field
Mullin conjecture.

## 1. The frame

**1.1 A polynomial is a map.** `N ∈ 𝔽_p[X]` is a self-map `x ↦ N(x)` of the affine line.
The roots of `N` are the fibre over `0`; the roots of `N + 1` are the fibre over `−1`. So
"+1" keeps the map and moves the base point from `0` to `−1`. The integers have no
analogue: an integer is not a self-map of Spec ℤ.

**1.2 Prime factors are Frobenius orbits.** `N(α^p) = N(α)^p` and `−1` is Frobenius-fixed,
so Frobenius permutes the fibre over `−1`. Its orbits are the irreducible factors of
`N + 1`; the orbit length is the degree.

**1.3 minFac is the most symmetric point of the fibre.** The factor of least degree is the
shortest Frobenius orbit, i.e. the point defined over the smallest field:

> deg minFac(N + 1) = the least d such that −1 is a value of N on 𝔽_{p^d}.

Over ℤ "smallest" has no Galois meaning, because the residue fields 𝔽_2, 𝔽_3, 𝔽_5, … do not
form a tower. Here the selection is canonical for the Galois action, up to ties between
orbits of equal length.

**1.4 The Galois object.** Take the family `N(x) − y` over the `y`-line and its monodromy
group `G`. Each base point `c ∈ 𝔽_p` that is not a critical value gives a Frobenius class
in `G` whose cycle type is the factorisation type of `N − c`.

* Frobenius at `0`: cycle type = the degrees of the primes collected so far (the state).
* Frobenius at `−1`: cycle type = the factorisation of `N + 1` (the menu).

They are two elements of one group and nothing forces a relation between them. This is the
exact meaning of "+1 destroys". Dead End #129 considered the Galois group of the single
polynomial `N + 1` over `𝔽_p`, which is always cyclic; the group that matters is the one of
the family. Equidistribution statements (Chebotarev over the base, Cohen-type theorems)
average over the base point or over `N`; the sequence needs one base point and one `N`.

**1.5 One kernel for both roles of a prime.** If `π` has roots `α₁, …, α_d`, then
`π(β) = ∏ (β − αᵢ)`. So "`π` mod `Q`" and "`Q` mod `π`" are both built from the differences
of their roots, and the process is a dynamical system on finite Frobenius-stable sets of
points `Z ⊂ 𝔽̄_p`: adjoin a shortest Frobenius orbit among the `α` with
`∏_{γ ∈ Z} (α − γ) = −1`. Over ℤ primes are points without coordinates and there is no
such kernel; the two roles of a prime (as a modulus, as a residue) are linked only by
Lagrange's theorem and quadratic reciprocity.

**1.6 The two kinds of stage.** Write `P` for the running product, `π` for the chosen
factor, `c` for the cofactor: `P + 1 = π·c`, next product `P′ = P·π`.

* Prime stage (`c = 1`): `P′ = P² + P = g(P)`, `g(x) = x² + x`. The step is a composition
  of maps. The next fibre over `−1` is the preimage under `P` of the fixed set `g⁻¹(−1)`,
  the primitive cube roots of unity. This is the source of the Φ₃ criterion, the 𝔽_5 tower
  and the 𝔽_2 threshold.
* Composite stage: `c·P′ = g(P)`, and `c·(P′ + 1) = P² + P + c`. The next fibre is
  `{α : P(α)² + P(α) + c(α) = 0}`. It is not the preimage of a fixed set: the cofactor
  twists the tower, differently at each step.

So the open part over function fields is the cofactor twist, the object called "deviation"
in `EM/Population/FeedbackSelection.lean`.

## 2. What is formalized of the frame (`FibreRule.lean`, any prime p)

| Statement | Lean name |
|---|---|
| `N + 1` has an irreducible factor of degree dividing `d` iff `−1 ∈ N(𝔽_{p^d})` | `exists_irreducible_dvd_iff` |
| along a sequence, `deg` of the next term is the least `m ≠ 0` with `−1 ∈ P_n(𝔽_{p^m})` | `ffSeq_natDegree_le_of_value`, `exists_value_ffSeq` |
| `∏_{c ∈ 𝔽_p} (N + c) = N^p − N` | `prod_add_C` |
| `f` divides some `N + c`, `c ∈ 𝔽_p`, iff `N` is Frobenius-fixed at a root of `f` | `exists_dvd_add_C_iff` |
| composite stage: `c·(P_{n+1} + 1) = P_n² + P_n + c` | `cofactor_mul_euclid_succ` |
| at a root `β` of `P_{n+1} + 1`: `y = P_n(β)` solves `y² + y + c(β) = 0`; iff when `c(β) ≠ 0` | `aeval_quadratic_of_root`, `dvd_euclid_succ_iff` |
| splitting law: `1 − 4c(β)` is a square in `𝔽_p(β)` | `isSquare_disc_of_root` |

The last three are the function-field twin of the integer identities in
`EM/Population/QuadraticStep.lean` (`E_{n+1}` as a norm from the order of discriminant
`1 − 4c_n`). Items 1.4 and 1.5 are not formalized.

## 3. The first twisted case over 𝔽_2 (`TwistedThreshold.lean`)

Over 𝔽_2 the prime stage is `P ↦ P² + P = (F + 1)P`, `F` = Frobenius. Let stages
`n, …, n+k−1` be irreducible and stage `n+k` arbitrary with cofactor `c`. By §2, a root `β`
of the next Euclid polynomial satisfies

> (F + 1)^{k+1} (P_n(β)) = c(β).

So `c(β)` lies in the image of `(F + 1)^{k+1}` on `𝔽_{2^d}`, `d = deg f`.

**Theorem (image of (F+1)^k; `mem_image_sylv_iterate_iff`).** Let `d = 2^u·m` with `m` odd
and `2^u ≤ k`. For `w ∈ 𝔽_{2^d}`:

> w ∈ (F + 1)^k (𝔽_{2^d})  ⟺  Tr_{𝔽_{2^d} / 𝔽_{2^{2^u}}}(w) = 0.

Necessity: `(F+1)^{2^u} = F^{2^u} + 1` in characteristic 2, and the relative trace of
`(F^{2^u} + 1) z` telescopes to `F^d z + z = 0`. This direction holds for every `u` with
`2^u ∣ d` and `2^u ≤ k`, without `m` odd (`relTr_eq_zero_of_sylv_iterate`). Sufficiency:
on the trace-zero part `F + 1` is injective, because its kernel `{0, 1}` meets it only in
`0` (the relative trace of `1` is `m`, odd); an injective self-map of a finite set is
bijective.

**Theorem (twisted threshold; `relTr_cofactor_eq_zero`).** With the notation above, if the
irreducible `f` of degree `2^u·m` with root `β` divides the next Euclid polynomial and
`2^u ≤ k + 1`, then `Tr_{𝔽_{2^d} / 𝔽_{2^{2^u}}}(c(β)) = 0`.

**Corollary (splitting law over 𝔽_2; `trace_cofactor_eq_zero`).** At every stage, the
absolute trace of `c_n(β)` vanishes at every root `β` of `P_{n+1} + 1`. Equivalently every
prime factor of `P_{n+1} + 1` splits in the Artin–Schreier extension `y² + y = c_n` of
`𝔽_2(X)`.

**Recovering the autonomous threshold.** For `c = 1` the relative trace is the degree ratio
`m` (`relTr_one`), so the condition reads "`m` is even": `2^{u+1} ∣ deg f` whenever
`2^u ≤ k + 1`. This is `AutonomousThreshold.two_pow_succ_dvd_natDegree_of_run`.

### What one cofactor does

A run of irreducible stages *forbids degrees*. One cofactor removes the prohibition and
replaces it by *trace conditions on the cofactor's value*: one bit for odd degrees, `2^u`
bits for degrees divisible by `2^u ≤ k + 1`. The degree prohibition is the special case in
which the cofactor is a constant, whose relative trace only sees the degree.

In the language of §1.6: at a prime stage the extension that the new primes must split in
is the constant extension `𝔽_4(X)` (hence a condition on degrees); at a composite stage it
is the geometric extension `y² + y = c_n(X)`, a curve that changes with `n` (hence a
character condition, satisfied by about half of the primes of each large degree).

### Limits

* The field-level theorem is sharp; the sequence-level theorem is only necessary. `c(β)` in
  the image says that some `x` works, not that `P_n(β)` does.
* The condition is the function-field form of the one-bit constraint of the integer case.
  It does not decide a capture.
* Runs have length at most 3 over 𝔽_2 (`CompositeFloors.not_four_consecutive_irreducible`),
  so `k + 1 ≤ 4` and the conditions concern the subfields `𝔽_2, 𝔽_4, 𝔽_16`.

## 4. Open after this

1. **Two cofactors.** After two composite stages the relation is
   `g(g(y)/w₁) = w₂` in the residue field: an additive (Artin–Schreier) condition applied
   to a multiplicative twist. No trace form is expected; the question is whether any
   closed condition survives.
2. **Odd `p`.** The same analysis with `y² + y + c = 0` and the quadratic character of
   `1 − 4c(β)`; the role of the relative trace is played by norms to subfields only for
   prime stages (Φ₃), and the general twisted statement is `isSquare_disc_of_root`.
3. **The monodromy group of `N(x) − y`** for the actual running products: answered in
   part in §5. It is not the symmetric group after a prime stage.

## 5. The monodromy question (`RunMonodromy.lean`)

**The tower breaks exactly at composite stages (`exists_comp_iff_irreducible`, any p).**
`P_{n+1}` is a polynomial in `P_n` iff `P_n + 1` is irreducible. If it is, `P_{n+1} = g∘P_n`
and the monodromy group of `P_{n+1}(x) − y` is imprimitive: it preserves the fibres of
`P_n` and sits inside a wreath product with `ℤ/2`. If it is not, the degree of `P_{n+1}`
lies strictly between `deg P_n` and `2·deg P_n`, so no such factorisation exists.

**Imprimitivity at every base point (`two_dvd_natDegree_of_inert`, any p).** At a prime
stage, if `y² + y = c` has no solution in `𝔽_p`, every irreducible factor of `P_{n+1} − c`
has even degree. The `Φ₃` criterion is the base point `c = −1`.

**A prime run has 2-group monodromy over 𝔽_2 (`aeval_ffProd_pow_eq_of_run`).** If stages
`n, …, n+k−1` are prime and `k < 2^u`, then for every base point `c ∈ 𝔽_{2^e}` and every `β`
with `P_{n+k}(β) = c`, the value `P_n(β)` lies in `𝔽_{2^{e·2^u}}`. Proof: `F^e + 1` is
divisible by `F + 1`, so `(F^e + 1)^{k+1}` kills `P_n(β)`, and
`(F^e + 1)^{2^u} = F^{e·2^u} + 1`.

Reading: over `𝔽_2` the step `g` is additive, so `P_n ↦ P_{n+k}` is a torsor under
`ker (F+1)^k`, on which Frobenius acts unipotently. The arithmetic monodromy of a run is a
2-group. The degree prohibitions of the threshold theorem and the trace conditions of §3 are
what a 2-group allows. So "+1 destroys" is false inside a run (the menu is rigidly tied to
the state) and the freedom enters only at composite stages, where the tower restarts.

**Still open.** After a composite stage: is `P_{n+1}` indecomposable, and what is the
monodromy group of `P_{n+1}(x) − y`? Nothing here bounds it from below. The statements above
are about the group of the family; the sequence still needs one base point (`−1`) and one
map.

## 6. Across the first composite stage over 𝔽_2 (`FirstComposite.lean`)

Over `𝔽_2` the start is forced: `P_3 = X⁸ + X⁴ + X² + X = g∘g∘g`, and
`P_3 + 1 = (X⁴+X³+1)(X⁴+X³+X²+X+1)`. The next term is one of the two quartics
(`ffSeq_four`); the two choices differ by `X ↦ X + 1`. In the first branch
`P_4 = (X¹⁶ + X)/Φ₅ = X¹² + X¹¹ + X⁷ + X⁶ + X² + X`.

**Theorem (`ffProd_four_indecomposable`).** If `P_4 = h∘q` over `𝔽_2` then `q` or `h` is
linear.

Proof. `P_4' = s²` with `s` a quintic without roots in `𝔽_2` (`derivative_ffProd_four`).
Over `𝔽_2` every derivative is a square (`exists_sq_eq_derivative`): `q' = a²`, `h' = b²`.
The chain rule gives `s = b(q)·a`, so `deg b·deg q + deg a = 5` with `2·deg a < deg q`,
`2·deg b < deg h`, `deg q·deg h = 12`. The only non-trivial solution is `deg q = 4`,
`deg a = 1`, which gives `s` a root in `𝔽_2`.

**Consequence (not formalized).** Intermediate fields of `𝔽_2(x)/𝔽_2(P_4)` correspond to
decompositions, so the monodromy group `G` of `P_4(x) − y` over `𝔽_2(y)` is primitive of
degree 12. The base point `0` is not a critical value, and `P_4` factors there with degrees
`1, 1, 2, 4, 4`, so `G` contains a permutation of that cycle type: it is odd, and its square
fixes four points. The primitive groups of degree 12 are `PSL₂(11)`, `PGL₂(11)`, `M₁₁`,
`M₁₂`, `A₁₂`, `S₁₂` (list recalled from memory, not looked up). The first, third, fourth and
fifth contain no odd permutation; in `PGL₂(11)` a non-identity element fixes at most two
points. Hence `G = S₁₂`. The geometric group (over `𝔽̄_2(y)`) is `A₁₂` or `S₁₂`; which one
is not decided. Indecomposability over `𝔽̄_2` follows from the same derivative argument but
is not in Lean.

**Reading.** For `P_3` the group is a 2-group of order at most 32 acting on 8 points; one
composite stage later it is the symmetric group on 12 points. So the answer to question 3
of §4 is: no inside a run, yes (in this first case) right after a composite stage. The
averaged form of "+1 destroys" holds for `P_4`: over base points `c ∈ 𝔽_{2^k}`, the
factorisation types of `P_4 − c` are distributed like cycle types in `S₁₂` (or in a coset
of `A₁₂`), by Chebotarev. This says nothing about the single base point `1`.

**Open.** Whether the group stays symmetric at later composite stages, and what a prime
stage after a composite one does (the group is then inside `S₂ ≀ G_n`; is it all of it?).

## 7. What a prime stage adds back (`CriticalValues.lean`)

Work over `K = 𝔽̄_2`. Let `P` have degree `m ≥ 5`, `P' ≠ 0`, geometric monodromy group
`G ⊇ A_m`, and let `B` be its set of critical values. Let `V_k = ker (F+1)^k`, the `2^k`
roots of `g^k`.

**Proposition (proof below; not formalized).** If some `b ∈ B` has `B ∩ (b + V_k) = {b}`,
then the geometric monodromy group of `g^k ∘ P` is `H ⋊ V_k` with
`A_m^{2^k} ≤ H ≤ S_m^{2^k}`.

So a run of `k` prime stages adds exactly the top group `V_k` (the 2-group of §5) and no
relation at all between the `2^k` copies of the previous cover, up to the sign characters.

Proof. The roots of `g^k(t) = y` are `t + κ`, `κ ∈ V_k`, so `K(t)/K(y)` is Galois with
group `V_k`, unramified over finite `y`. Let `L_κ` be the splitting field of
`P(x) − (t + κ)` over `K(t)`; its group is `G`, and its finite branch locus is
`{t ∈ B − κ}`. For `κ ≠ κ'` the hypothesis gives `B − κ ≠ B − κ'`, so `L_κ ≠ L_κ'`. The
group of `L_κ L_κ'` is a subgroup of `G × G` projecting onto both factors; its
intersections with the factors are normal subgroups of `G`, hence trivial or `⊇ A_m`;
trivial would give `L_κ = L_κ'`. So every pair of coordinates carries `A_m × A_m`. The
commutator subgroup of the full group lies in `A_m^{2^k}` and projects onto every pair, so
it is `A_m^{2^k}` (a subgroup of a product of non-abelian simple groups that projects onto
every pair of factors is the whole product).

**Lean support.**

| Statement | Lean name |
|---|---|
| prime stage: `P_{n+1}' = (2P_n + 1)·P_n'` (any `p`) | `derivative_ffProd_succ_of_irreducible` |
| over `𝔽_2` the derivative is constant along a run: critical points stay, critical values move by `g^k` | `derivative_ffProd_add_of_run` |
| `v ∈ 𝔽_{2^m}`, `m` odd ⇒ `v + 1` is not a conjugate of `v` | `pow_ne_add_one_of_odd` |
| `δ` a root of an irreducible of odd degree ⇒ `N(δ^{2^j}) ≠ N(δ) + 1` | `aeval_conj_ne_add_one` |

**Application to `P_4`.** Its critical points are the roots of the quintic `s` of §6, which
is irreducible (no root in `𝔽_2`, not divisible by `X² + X + 1`; checked by hand, not in
Lean). By `aeval_conj_ne_add_one`, `B ∩ (B + 1) = ∅`. With §6 (group `⊇ A₁₂`, which rests
on the recalled classification): *if* stage 4 is prime, the geometric group of `P_5` contains
`A₁₂ × A₁₂`. Whether stage 4 is prime (`P_4 + 1` irreducible of degree 12) is not known
here; its factors have degrees `12`, `6+6` or `5+7`.

**Picture after §5–§7.** The monodromy along the sequence is built from two moves. A prime
stage wraps the current group in a wreath product with `ℤ/2` and (under the critical-value
condition) adds nothing else. A composite stage destroys the block structure (§5), and in
the first case replaces the group by the full symmetric group (§6). Rigidity is therefore
confined to the top 2-group of the current run. The selection rule reads one base point of
this family, and none of the above constrains that point beyond the trace conditions of §3.

**Open.** (i) The proposition for odd `p` (the top cover `g(t) = y` is then ramified at
`−1/4`, and the condition becomes `B ≠ −1 − B`). (ii) A general statement at composite
stages: indecomposability of `P_{n+1}`, and largeness of its group, beyond the first case.

## 8. The 𝔽_5 screen (`CompositeEntry.lean`)

The conjecture is false over `𝔽_5` and the Riemann hypothesis holds over every `𝔽_p`, so a
proof over `𝔽_2` must use something that fails over `𝔽_5`. The only known failure over
`𝔽_5` is perpetual irreducibility. Stated for every `p`:

| Statement | Lean name |
|---|---|
| two terms entering at prime stages have different degrees | `eq_of_natDegree_eq_of_irreducible` |
| of two different terms of equal degree, one entered at a composite stage | `not_irreducible_of_natDegree_eq` |
| all stages prime from `N` on ⇒ some prime never appears | `exists_missed_of_perpetual` |
| the conjecture ⇒ infinitely many composite stages | `infinitelyManyReducible_of_ffMullinConjecture` |

So prime stages supply at most one prime per degree, out of about `p^D/D`. The conjecture is
a statement about composite stages: which of several factors of `P_n + 1` has least degree.

**What 𝔽_2 has and 𝔽_5 does not.**

1. *Composite stages are forced.* For odd `p` the tower of prime stages is a tower of
   quadratic extensions governed by the orbit of the critical point `−1/2` of `g`; over
   `𝔽_5` that orbit is `2 → 1 → 2` and the relevant discriminants are never squares. Over
   `𝔽_2`, `g` has no critical point, the tower is Artin–Schreier, and
   `g³(P) + 1 = Φ₅(P)·Φ₅(P + 1)` for every `P`
   (`CharTwo.euclid_three_factor`, with `X⁴+X³+1 = Φ₅(X+1)`).
2. *The forced composite stage is cyclotomic.* After three prime stages from `n`, a prime
   `Q` divides the Euclid polynomial iff `P_n` or `P_n + 1` has multiplicative order `5`
   modulo `Q`. The two factors are exchanged by `P ↦ P + 1`, the involution that swaps the
   base points `0` and `1`.
3. *The target is the identity.* `−1 = 1`, so `Q ∣ P_n + 1` iff the product of the terms
   so far is `1` in `(𝔽_2[X]/Q)^×`, a group of odd order. Over `ℤ` and over odd `p` the
   target has order 2, and a subgroup of the residues can avoid it; here no subgroup can.

None of these decides a capture. The first is a theorem, the second is a reformulation of
it, the third is the one not yet used anywhere in the repository.

## 9. The target is the identity (`IdentityTarget.lean`)

Point 3 of §8, used. A finite group gives one thing for free: **recurrence**. Every walk in
`G_Q = (𝔽_p[X]/Q)^×` repeats a value and every element has finite order. Recurrence produces
the value `1`; it never produces a prescribed other value. So finiteness alone proves the
*Mersenne form* `Q ∣ W − 1`, uniformly in `p`, and the Euclid rule asks for the *Euclid
form* `Q ∣ W + 1`. The two differ by the element `−1` of the group of constants `𝔽_p^×`.
For odd `p` (and over `ℤ`) it has order 2 and a subgroup can avoid it. Over `𝔽_2` the group
of constants is trivial and the two forms are one statement.

| statement | Lean |
|---|---|
| any `p`: `Q ∣ N^(p^deg Q − 1) − 1` (recurrence in the exponent) | `dvd_pow_sub_one` |
| `𝔽_2`: `Q ∣ N^(2^deg Q − 1) + 1` | `dvd_pow_add_one` |
| `𝔽_2`: every prime outside a finite set `D` divides `(∏D)^(2^deg Q − 1) + 1` | `dvd_prod_pow_add_one` |
| any `p`: a prime never dividing the product divides `a_{i+1}⋯a_{i+k} − 1` for a window inside every stretch of `p^deg Q` stages (recurrence in time) | `exists_window_sub_one` |
| `𝔽_2`: every missed prime divides a window Euclid polynomial `a_{i+1}⋯a_{i+k} + 1`, infinitely often, gaps `≤ 2^deg Q` | `exists_window_add_one` |

**Reading.** Mullin's conjecture for `Q` is the anchored case `i = 0` of the last line plus
minimality. The unanchored statement is a weakening of the conjecture which holds over
`𝔽_2`, and its proof is exactly `−1 = 1`: the same argument over `𝔽_5` or `ℤ` gives windows
`≡ 1`, the wrong sign (the sign studied in `mersenne_duality_2026-10-27.md`; in
characteristic 2 the Euclid and Mersenne problems coincide). Whether the window statement in
Euclid form is true or false over `𝔽_5` is not known to me; only the proof is specific.

**The same fact in the exponent direction** is the norm: `N^(2^d − 1) = ∏_{j<d} N^{2^j}` is
the norm of `N mod Q` to `𝔽_2`, and it is `1` because `𝔽_2^× = 1`. Over `𝔽_p` the norm is
(up to sign) the resultant of `N` and `Q`, an element of `𝔽_p^×`, and the capture at this
level is a reciprocity condition. Over `𝔽_2` there is no reciprocity symbol with values in
the constants, hence no character obstruction of the kind that traps residues over `ℤ`.

**What it does not give.** An anchored window. The walk `n ↦ P_n mod Q` returns to values
it has visited; the conjecture needs it to visit the value `1`, starting from the seed.
Recurrence gives `P_j ≡ P_i`, i.e. the walk closes a loop somewhere, not at the origin. What
remains of the conjecture over `𝔽_2` after this section is therefore: *the loop passes
through the identity*, and the least-degree rule.

### 9.1 Joint recurrence and the anchoring wall

The recurrence argument does not need the modulus to be prime. For any monic `M` coprime to
every running product, windows `≡ 1 (mod M)` occur beyond every stage
(`exists_window_sub_one_of_coprime`, any `p`). Two consequences over `𝔽_2`:

* a finite set of missed primes is captured *jointly* by one window Euclid polynomial
  (`exists_window_add_one_joint`);
* taking `M = Q^k`: the window Euclid polynomials tend to `0` in the `Q`-adic topology, for
  all missed `Q` at once. In the compact group `∏_{Q missed} A_Q^×` the identity is a limit
  point of window products. This is compactness and nothing else.

**Why this does not anchor.** The conjecture needs the window to start at the empty product
(over `𝔽_2` the empty Euclid number is `1 + 1 = 0`, divisible by every prime: every prime is
"captured at stage −1", and the conjecture asks the walk to return there). Recurrence says
that *some* earlier value returns. It would say that the *initial* value returns if the step
were a bijection of a finite set, and it is not a self-map of the residue group at all: the
factor `a_{n+1}` depends on `P_n`, not on `P_n mod Q`. On a prime run it is a self-map, the
linear map `F + 1` of `𝔽_Q`, and its only failure of injectivity is its kernel `𝔽_2 = {0, 1}`:
the dead state and the target. By Fitting, `𝔽_Q = 𝔑 ⊕ 𝔘` with `F + 1` nilpotent on
`𝔑 = 𝔽_{2^{2^u}}` and bijective on `𝔘` (the kernel of the relative trace,
`TwistedThreshold.mem_image_sylv_iterate_iff`); the target lies in `𝔑`, so a prime run can
never remove a non-zero `𝔘`-component. This is the autonomous threshold again. Anchoring is
therefore entirely a matter of the cofactor at composite stages, which is where §8 already
located the conjecture. Recurrence is as far as the identity target goes by itself.

## 10. The dichotomy (`Dichotomy.lean`)

**Statement (open, any `p`).** `FFDichotomy p`: a sequence over `𝔽_p` that misses a prime
is eventually a tower (all Euclid polynomials irreducible from some stage on). The converse
is `CompositeEntry.exists_missed_of_perpetual`.

| statement | Lean |
|---|---|
| a tower misses a prime | `misses_of_eventuallyPrime` |
| conjecture ⇒ dichotomy | `ffDichotomy_of_ffMullinConjecture` |
| conjecture ⟺ dichotomy ∧ (every sequence has infinitely many composite stages) | `ffMullinConjecture_iff` |
| the dichotomy holds over `𝔽_5` | `ffDichotomy_five` |
| over `𝔽_2`, `𝔽_3`: dichotomy ⟺ conjecture | `ffDichotomy_two_iff`, `ffDichotomy_three_iff` |

**Reading.** The conjecture over `𝔽_p` is the conjunction of two statements of different
nature.

* *Dynamics.* The tower `g^n(X) + 1`, `g = X² + X`, does not stay irreducible. This depends
  on `p`: false over `𝔽_5`, true over `𝔽_2` and `𝔽_3`. For odd `p` it is a question about
  the finite orbit of the critical point `−1/2`, hence a finite condition for each `p`.
* *Selection.* The dichotomy. Its form does not depend on `p`, no instance is known to
  fail, and the `𝔽_5` counterexample to the conjecture is an instance where it holds.

So the dichotomy is the uniform-in-`p` statement that the `𝔽_5` screen cannot kill, and
"is the conjecture true over `𝔽_p`" becomes "does `p` have a stable tower", provided the
dichotomy holds. Nothing here is evidence for the dichotomy: over `𝔽_2` and `𝔽_3` it is the
conjecture itself. A failure would be a sequence with infinitely many composite stages that
still misses a prime; for odd `p` the candidate mechanism is a character of the residue group
trivial on every term and non-trivial on `−1`, which over `𝔽_2` cannot exist (§9).

## 11. The classification by the tower (`TowerClassification.lean`, `StabilityCriterion.lean`)

Let `T k = g^k(Y) + 1`, `g = Y² + Y`. Call `p` *stable* if every `T k` is irreducible over
`𝔽_p`.

**The tower bounds every run.** If stages `n, …, n+k−1` are prime then `P_{n+k} = g^k ∘ P_n`,
so the Euclid polynomial at stage `n+k` is `T k ∘ P_n`, and a composition `T ∘ B` is
irreducible only if `T` is. So the level polynomials of the one tower control the prime runs
of every sequence from every stage (`level_irreducible_of_run`). Conversely, if `p` is
stable every sequence is the tower (`perpetual_of_stable`).

**Classification (any `p`), `ffMullinConjecture_iff_not_stable_and_dichotomy`:**

    FF-MC(p)  ⟺  p is not stable  ∧  Dichotomy(p).

* stable `p`: the conjecture is false and the dichotomy is true;
* unstable `p`: composite stages are forced for every sequence, and the conjecture *is* the
  dichotomy.

The earlier case results are instances: `𝔽_2` (`T 3` reducible), `𝔽_3` and `p ≡ 1 (mod 3)`
(`T 1` reducible), `𝔽_5` (stable).

**Stability criterion (odd `p`), `stable_iff`.** A root `α` of `T (k+1)` lies over the root
`θ = g(α)` of `T k` by a quadratic equation with discriminant `1 + 4θ`. With `T k`
irreducible, `T (k+1)` is irreducible iff `α ∉ 𝔽_p(θ)` iff `1 + 4θ` is not a square there
iff its norm to `𝔽_p` is not a square, and the norm is `(−4)^{2^k} · T k(−1/4)`
(`prod_sub_conj`). So

    p stable  ⟺  for all k,  (−4)^{2^k} · (g^k(−1/4) + 1) is a non-square mod p,

the first element being `−3` (`disc_zero`). `−1/4 = g(−1/2)` is the critical value of `g`,
and its orbit in `𝔽_p` is eventually periodic, so stability is a finite condition for each
`p`. This is the criterion stated without proof in the header of `StableTower.lean`; the
`𝔽_5` case there was proved by a separate induction.

**Answer to "is the conjecture true for large `p`".** By the classification, for each odd
`p` exactly one of two things holds: the critical orbit avoids squares for ever, and the
conjecture over `𝔽_p` is false; or it does not, and the conjecture over `𝔽_p` is the
dichotomy. Which `p` are stable is a question about the orbit of `−1/4` under `g` modulo
`p`. Heuristically stable `p` are rare (an orbit of length about `√p` must avoid the
squares); nothing is proved about their number, not even that it is finite or that `5` is
not the only one.

## 12. Which primes are stable (`StablePrimes.lean`)

**Small cases.** `2`, `3` and every `p ≡ 1 (mod 3)` are not stable; `5` is
(`not_stable_two`, `not_stable_three`, `not_stable_of_one_mod_three`, `stable_five`).

**One integer sequence.** The elements of `𝔽_p` that decide stability are the reductions of
integers that do not depend on `p`. With `n_0 = −1`, `n_{k+1} = n_k (n_k + 4^{2^k})`, so that
`g^k(−1/4) = n_k / 4^{2^k}`, put `e_k = n_k + 4^{2^k}` and `Δ_k = (−1)^{2^k} e_k`
(`Δ_0 = −3`, `Δ_1 = 13`). Then (`stable_iff_discZ`)

    odd p is stable  ⟺  Δ_k is a non-square mod p for every k.

* *Pairwise coprime* (`isCoprime_discZ`). `n_{k+1} = n_k e_k`, so `e_k ∣ n_j` for `j > k`
  and `e_j ≡ 4^{2^j}` modulo `e_k`, which is odd. This is Euclid's argument, on the critical
  orbit.
* *No `Δ_k` is a square in `ℤ`* (`not_isSquare_discZ`). A stable prime certifies it: a
  square in `ℤ` is a square mod `p`. The prime `5` is stable.
* *Independence* (`not_isSquare_prod_discZ`). No non-empty product of distinct `Δ_k` is a
  square: a coprime factor of a square is `±` a square, and `−1` is a square mod `5`.

So the existence of one stable prime gives the independence of all the conditions.

**Proposition (not in Lean): the stable primes have density zero.** For `K ≥ 0` let `S_K`
be the set of odd primes `p` with `Δ_k` a non-square mod `p` for all `k ≤ K`. Its indicator
is `∏_{k ≤ K} (1 − (Δ_k/p))/2`. Expanding, the term of a non-empty `A ⊆ {0..K}` is
`±(Δ_A/p)` with `Δ_A = ∏_{k∈A} Δ_k`, which by independence is not a square, so
`p ↦ (Δ_A/p)` is a non-trivial quadratic Dirichlet character (reciprocity) and averages to
zero over primes (Dirichlet). Hence `S_K` has density `2^{−(K+1)}`. Stable primes lie in
every `S_K`.

**What this does and does not give.**

* Density zero: yes, by the argument above (standard inputs only).
* A rate: the moduli `Δ_k` grow doubly exponentially, so unconditionally one can take only
  `K` of size about `log log log x`, and the bound is `π(x)` divided by a power of
  `log log x`. Under GRH `K ≈ log log x` and the saving is a power of `log x`. Neither gives
  a convergent count.
* Finiteness: not provable this way. The heuristic (an orbit of length about `√p` avoiding
  the squares) predicts finitely many, possibly only `5`; nothing of the kind is proved.

**Remark.** `g(x) = x² + x` is conjugate by `y = x + 1/2` to `y² + 1/4`, the parabolic
parameter at the cusp of the Mandelbrot set, and the level polynomials are `f^k(y) + 1/2`.
Density-zero statements for stable primes of quadratic polynomials are part of arithmetic
dynamics (R. Jones and others); I have not checked whether this case is in the literature.

## 13. The dichotomy: what an attack must look like (analysis, no new Lean)

For unstable `p`, in particular `p = 2`, the dichotomy is the conjecture (§10–§11). I found
no proof. What follows are the constraints on any proof.

**13.1 Three equivalent forms** (all already in the repository in substance). For a sequence
`d` and the missed prime `Q` of least degree:

* *avoidance*: from some stage on `Q ∤ P_n + 1` (`Bootstrap.FFDynamicalHitting` is the
  negation; a missed prime is offered only finitely often, because each late offer captures
  one of the finitely many uncaptured primes of that degree);
* *walk*: the residue walk `w_n = P_n mod Q` avoids `−1` for ever, with steps
  `w_{n+1} = g(w_n) / c_n(β)`, `c_n` the cofactor (`FibreRule.cofactor_mul_euclid_succ`);
* *dichotomy*: this can happen only if all cofactors are eventually `1`.

So the dichotomy says: **a walk that receives infinitely many non-trivial cofactors cannot
avoid `−1`.**

**13.2 The cofactor screen.** The same statement is false for the *take-all* rule
(`P_{n+1} = P_n (P_n + 1)` at every stage, composite or not). There the walk is the
autonomous map `w ↦ g(w)` for ever, Euclid polynomials are composite, and over `𝔽_2` every
prime of odd degree `> 1` is missed (`AutonomousThreshold.lean`). So a proof of the
dichotomy must use that the cofactor is *discarded*. Together with the `𝔽_5` screen: a proof
must use (a) a property of the cofactor at composite stages, (b) nothing that holds for the
take-all rule, (c) nothing uniform in the rule "least" versus "any" unless it also proves the
tree statement.

**13.3 Soft arguments stop here.** After the exhaustion point every term has degree larger
than `deg Q`, hence is a unit modulo every missed prime of that degree, and by the
function-field Dirichlet theorem such terms realise every element of the residue group. So
"avoids `−1` for ever" contradicts nothing that is expressed through residues, degrees, or
recurrence (§9.1). The contradiction, if there is one, must come from the factorisation of
the specific polynomials `P_n + 1`. This is the same wall as over `ℤ` (`MixedTree.lean` §2).

**13.4 A caution on the statement.** "Eventually every Euclid polynomial is irreducible"
could fail for a harmless reason: a stage where `P_n + 1` is a prime *power* involves no
choice either. Over `𝔽_3` every prime stage is followed by such a stage
(`P_{n+1} + 1 = (P_n − 1)²`). The robust form of the dichotomy is "eventually no choice":
every Euclid polynomial is a prime power. For `p = 2, 3` the two forms agree with the
conjecture, since choices are forced to occur; for general `p` the robust form is the safer
conjecture. Not formalised.

**13.5 Where a real idea would enter.** The one piece of exact information on a cofactor is
the trace condition (`TwistedThreshold.lean`): modulo the next captured prime, the cofactor
lies in the image of `F + 1`. An argument for the dichotomy over `𝔽_2` would be a statement
of the same kind but in the other direction: a property of the discarded cofactor that
*forces* the walk modulo `Q` to move. None is known.

