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

