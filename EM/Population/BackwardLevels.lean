import EM.Population.BackwardOrbit
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Raising the Hit Level Past `Φ₃`

`EM/Population/BackwardOrbit.lean` reduces (C∞) to a hitting statement: for every `N` the
walk value `walkZ ℓ N + 1` must enter `PreZero ℓ`, the backward orbit of `0` under
`Φ₆(x) = x² - x + 1`.  Its *first* level is the classical death equation
`Φ₃(w) = w² + w + 1 = 0`, and every argument the project has aimed at that target uses that
level only.  This file goes deeper.

## The conjugacy: levels are take-all steps

The translation `y ↦ y + 1` conjugates the **take-all (Sylvester) walk**

    q(y) = y² + y          (`sylvWalk`, the map of `FunctionFieldAnalog.ffAutonomousMap`)

to `Φ₆`, because `Φ₆(w + 1) = (w+1)w + 1 = q(w) + 1` (`phi6_add_one_eq`).  Iterating,

    Φ₆^[k] (w + 1) = q^[k] (w) + 1        (`iterate_phi6_add_one`)

and therefore

> **`walkZ ℓ N + 1 ∈ PreZero ℓ` ⟺ the take-all walk started at `walkZ ℓ N` reaches `-1`**

(`mem_preZero_iff_sylvWalk_reaches_neg_one`).  So the hit *level* is exactly the number of
take-all steps before death:

* level `0` — the walk value is already `-1`;
* level `1` — `q(w) = -1`, i.e. `Φ₃(w) = 0`: **the classical condition**, the death
  equation whose insolubility modulo `q ≡ 2 (mod 3)` drives the density-`1/2` failure of
  the take-all rule;
* level `k` — death after `k` take-all steps.

Two consequences are immediate and structural.  Levels are **disjoint**: `q(-1) = 0` and
`q(0) = 0`, so an orbit that reaches `-1` falls into the absorbing `0` and never returns
(`death_level_unique`).  And raising the level buys **no new moduli**: a hit at any level
`≥ 1` produces a root of `Φ₃`, hence a primitive cube root of unity, hence `6 ∣ ℓ - 1`
(`six_dvd_sub_one_of_death`).  What it buys is a strictly larger target inside those
moduli.

## Past `Φ₃`: level two exists, and reciprocity decides when

Getting from level `m` to level `m+1` means solving `y² + y = z` for a level-`m` point `z`,
which is possible exactly when `1 + 4z` is a square (`sylvWalk_step_of_isSquare`).  For
`m = 1` the two level-one points are the primitive cube roots of unity `ω` and `ω² = -ω-1`,
and Vieta gives the identity that decides the matter:

    (1 + 4ω) (1 + 4ω²) = 1 + 4(ω + ω²) + 16 ω³ = 1 - 4 + 16 = 13

(`cube_root_pair_product_eq_thirteen`).  If `13` is a quadratic **non**-residue then the
product of the two discriminants is a non-residue, so exactly one of them is a residue, and
**level two is non-empty** (`exists_death_level_two`).  By quadratic reciprocity — `13 ≡ 1
(mod 4)`, so the reciprocity sign is trivial — that is a congruence condition on `ℓ` alone:

> `13` is a non-residue mod `ℓ` ⟺ `ℓ` is a non-residue mod `13`
> (`isSquare_thirteen_iff`),

i.e. `ℓ mod 13 ∈ {2, 5, 6, 7, 8, 11}`, a set of density `1/2`.  So for half of the primes
`ℓ ≡ 1 (mod 3)` the target is strictly bigger than the classical one, and on the branch the
walk must avoid the level-two points as well (`psi_two_ne_zero_of_perpetual`):

    walkZ ℓ N ^ 4 + 2 walkZ ℓ N ^ 3 + 2 walkZ ℓ N ^ 2 + walkZ ℓ N + 1 ≠ 0 .

This is the first constraint on the perpetual-primality branch that is not a consequence of
the `Φ₃` obstruction.

## Level three, and the mechanism behind every level

Level two turns out not to be a special case.  The two `q`-preimages of a point are `y` and
`-1 - y`, since `q(-1-y) = q(y)`, so their discriminants satisfy the **ring identity**

    (1 + 4y) (1 + 4(-1-y)) = -3 - 16 q(y)          (`preimage_pair_discriminant`)

with no appeal to Vieta and no field hypothesis.  Writing `Δ(z) = -3 - 16z`: the pair of
discriminants one level above `z` multiplies to `Δ(z)`, and the entire level structure is
governed by evaluating `Δ` along backward orbits.  The `13` of level two is `Δ(-1)`.

This gives the **lift** (`exists_death_level_add_two`): if `z` is at level `m`, `1 + 4z` is
a square, and `Δ(z)` is a non-square, then level `m+2` is occupied.  Level three is its
`m = 1` instance (`exists_death_level_three`), and the level-three constant is
`Δ(ω) Δ(ω²) = 217 = 7 · 31` (`delta_pair_product_eq_217`).  Since `217 ≡ 1 (mod 4)` as well,
the same Jacobi reciprocity applies (`not_isSquare_217_iff`), so when both level-two
branches are present the criterion is again a congruence on `ℓ` alone
(`exists_death_level_three_of_split`).

Two limits emerge at level three, and both are worth recording.

*The criteria stop being rational.*  When `13` is a non-residue only one level-two branch
exists, and the level-three criterion is `¬ IsSquare (-3 - 16ω)` — a condition on `ω`, not
on a rational constant.  This is exactly where the tower stops being decided by congruences
on `ℓ` and becomes a splitting condition in a larger field; the general statement is an
arboreal-Chebotarev question, and it is not formalised here.

*The tower has a top.*  Levels are disjoint and live in a finite field, so only finitely
many are occupied (`realizedLevels_finite`).  "Raising the level" is a bounded resource: the
depth of the backward-orbit tree of `-1` is an invariant of `ℓ`, and it is what the
heuristic `|PreZero ℓ| ≍ √ℓ` is really measuring.

## Honest accounting

The gain is real but bounded: the moduli never change, the tower is finite, and the barrier
is untouched — the criterion still asks where one specific orbit sits.  What the file
establishes is that the classical `Φ₃` condition is level one of a tower of disjoint levels
driven by a single ring identity, that levels two and three are occupied on explicit
congruence classes of `ℓ`, and that the mechanism is quadratic reciprocity rather than
search.

## Contents

* `sylvWalk`, `phi6_add_one_eq`, `iterate_phi6_add_one` — the conjugacy.
* `mem_preZero_iff_sylvWalk_reaches_neg_one` — levels are take-all steps.
* `death_level_unique`, `six_dvd_sub_one_of_death` — disjointness; no new moduli.
* `sylvWalk_step_of_isSquare`, `cube_root_pair_product_eq_thirteen`,
  `exists_death_level_two` — past `Φ₃`.
* `preimage_pair_discriminant`, `exists_death_level_add_two` — the engine and the lift.
* `delta_pair_product_eq_217`, `exists_death_level_three`,
  `exists_death_level_three_of_split` — level three.
* `realizedLevels_finite` — the tower has a top.
* `not_isSquare_iff_jacobiSym`, `isSquare_thirteen_iff`, `not_isSquare_217_iff` —
  reciprocity turns each criterion into a congruence on `ℓ`.
* `psi_two_ne_zero_of_perpetual`, `psi_three_ne_zero_of_perpetual`,
  `backward_levels_landscape`.
-/

noncomputable section

open Mullin Euclid MullinGroup AutonomousBranch BackwardOrbit

namespace BackwardLevels

/-! ## Part 1: the take-all walk, and the conjugacy with `Φ₆` -/

/-- The **take-all (Sylvester) walk** `q(y) = y² + y`.  This is the autonomous map the
accumulator degenerates to when every prime factor of the Euclid number is banked; over
`ZMod p` it is `FunctionFieldAnalog.ffAutonomousMap`. -/
def sylvWalk {R : Type*} [CommRing R] (y : R) : R := y * y + y

/-- `Φ₃(y) = y² + y + 1`, the death polynomial of the take-all walk. -/
def phi3 {R : Type*} [CommRing R] (y : R) : R := y * y + y + 1

theorem sylvWalk_eq_neg_one_iff {R : Type*} [CommRing R] (y : R) :
    sylvWalk y = -1 ↔ phi3 y = 0 := by
  unfold sylvWalk phi3
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

theorem sylvWalk_neg_one {R : Type*} [CommRing R] : sylvWalk (-1 : R) = 0 := by
  unfold sylvWalk; ring

theorem sylvWalk_zero {R : Type*} [CommRing R] : sylvWalk (0 : R) = 0 := by
  unfold sylvWalk; ring

/-- **The conjugacy.**  Translation by `1` carries the take-all walk to `Φ₆`. -/
theorem phi6_add_one_eq {R : Type*} [CommRing R] (w : R) :
    phi6 (w + 1) = sylvWalk w + 1 := by
  unfold phi6 sylvWalk; ring

/-- **The conjugacy, iterated.**  The `k`-th `Φ₆`-preimage level corresponds to `k` steps
of the take-all walk. -/
theorem iterate_phi6_add_one {R : Type*} [CommRing R] (k : ℕ) (w : R) :
    (phi6)^[k] (w + 1) = (sylvWalk)^[k] w + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, phi6_add_one_eq, Function.iterate_succ_apply']

/-- **Levels are take-all steps.**  Membership in the backward orbit of `0` is exactly
death of the take-all walk. -/
theorem mem_preZero_iff_sylvWalk_reaches_neg_one {ℓ : ℕ} (w : ZMod ℓ) :
    w + 1 ∈ PreZero ℓ ↔ ∃ k : ℕ, (sylvWalk)^[k] w = -1 := by
  constructor
  · rintro ⟨k, hk⟩
    rw [iterate_phi6_add_one] at hk
    exact ⟨k, by linear_combination hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [iterate_phi6_add_one, hk]; ring⟩

/-! ## Part 2: the levels are disjoint, and they buy no new moduli -/

/-- After death the take-all walk is absorbed at `0`. -/
theorem sylvWalk_iterate_eq_zero_of_death {R : Type*} [CommRing R] {w : R} {i : ℕ}
    (h : (sylvWalk)^[i] w = -1) (m : ℕ) : (sylvWalk)^[i + m + 1] w = 0 := by
  induction m with
  | zero =>
      rw [Function.iterate_succ_apply', h]
      exact sylvWalk_neg_one
  | succ m ih =>
      rw [show i + (m + 1) + 1 = (i + m + 1) + 1 from by ring,
        Function.iterate_succ_apply', ih]
      exact sylvWalk_zero

/-- **The level of a hit is unique.**  The backward orbit of `0` is a *disjoint* union of
preimage levels; nothing sits at two levels at once. -/
theorem death_level_unique {R : Type*} [CommRing R] [Nontrivial R] {w : R} {i j : ℕ}
    (hi : (sylvWalk)^[i] w = -1) (hj : (sylvWalk)^[j] w = -1) : i = j := by
  by_contra hne
  rcases Nat.lt_or_ge i j with h | h
  · obtain ⟨m, rfl⟩ : ∃ m, j = i + m + 1 := ⟨j - i - 1, by omega⟩
    rw [sylvWalk_iterate_eq_zero_of_death hi m] at hj
    exact zero_ne_one (by linear_combination -hj)
  · have hlt : j < i := by omega
    obtain ⟨m, rfl⟩ : ∃ m, i = j + m + 1 := ⟨i - j - 1, by omega⟩
    rw [sylvWalk_iterate_eq_zero_of_death hj m] at hi
    exact zero_ne_one (by linear_combination -hi)

/-- `Φ₆` and `Φ₃` are related by negation, so a `Φ₃` root gives a `Φ₆` root. -/
theorem phi6_neg {R : Type*} [CommRing R] (y : R) : phi6 (-y) = phi3 y := by
  unfold phi6 phi3; ring

/-- **Raising the level buys no new moduli.**  A hit at any level `≥ 1` forces a primitive
cube root of unity, hence `6 ∣ ℓ - 1` — the very same condition the classical level-one
target requires. -/
theorem six_dvd_sub_one_of_death {ℓ : ℕ} [Fact (Nat.Prime ℓ)] (h2 : ℓ ≠ 2) (h3 : ℓ ≠ 3)
    {w : ZMod ℓ} {k : ℕ} (h : (sylvWalk)^[k + 1] w = -1) : 6 ∣ ℓ - 1 := by
  rw [Function.iterate_succ_apply'] at h
  have hstep : sylvWalk ((sylvWalk)^[k] w) = -1 := h
  have h3' : phi3 ((sylvWalk)^[k] w) = 0 := (sylvWalk_eq_neg_one_iff _).mp hstep
  exact six_dvd_sub_one_of_phi6_root h2 h3 (y := -((sylvWalk)^[k] w))
    (by rw [phi6_neg]; exact h3')

/-! ## Part 3: past `Φ₃` — the step lemma and the number `13`

Getting from level `m` to level `m+1` is solving `y² + y = z`, whose discriminant is
`1 + 4z`.  For `m = 1` the two targets are the primitive cube roots of unity, and the
product of their two discriminants is the *constant* `13`. -/

/-- **The step lemma.**  A square discriminant lifts a hit one level deeper. -/
theorem sylvWalk_step_of_isSquare {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {z : F} {m : ℕ}
    (hz : (sylvWalk)^[m] z = -1) (hsq : IsSquare (1 + 4 * z)) :
    ∃ y : F, (sylvWalk)^[m + 1] y = -1 := by
  obtain ⟨t, ht⟩ := hsq
  refine ⟨(t - 1) / 2, ?_⟩
  have hstep : sylvWalk ((t - 1) / 2) = z := by
    unfold sylvWalk
    field_simp
    linear_combination -ht
  rw [Function.iterate_succ_apply, hstep]
  exact hz

/-- **The Vieta identity that decides level two.**  The two primitive cube roots of unity
have discriminants multiplying to `13`:
`(1 + 4ω)(1 + 4ω²) = 1 + 4(ω + ω²) + 16 ω³ = 1 - 4 + 16 = 13`.  It is the `q(y) = -1`
instance of the general `preimage_pair_discriminant` of Part 6. -/
theorem cube_root_pair_product_eq_thirteen {R : Type*} [CommRing R] {ω : R}
    (h : phi3 ω = 0) : (1 + 4 * ω) * (1 + 4 * (-1 - ω)) = 13 := by
  unfold phi3 at h
  linear_combination (-16 : R) * h

/-- The other primitive cube root of unity, written as the second `q`-preimage. -/
theorem phi3_neg_one_sub {R : Type*} [CommRing R] {ω : R} (h : phi3 ω = 0) :
    phi3 (-1 - ω) = 0 := by
  unfold phi3 at h ⊢
  linear_combination h

/-- **Non-squares multiply to squares.**  In a finite field, a non-square product has a
square factor: the squares form a subgroup of index at most two, read off from the
multiplicativity of the quadratic character. -/
theorem isSquare_or_isSquare_of_not_isSquare_mul {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {a b : F} (h : ¬ IsSquare (a * b)) :
    IsSquare a ∨ IsSquare b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ha, hb⟩ := hcon
  have h1 : quadraticChar F a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr ha
  have h2 : quadraticChar F b = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hb
  have hab0 : a * b ≠ 0 := by
    intro h0
    exact h (by rw [h0]; exact IsSquare.zero)
  have hone : quadraticChar F (a * b) = 1 := by rw [map_mul, h1, h2]; norm_num
  exact h ((quadraticChar_one_iff_isSquare hab0).mp hone)

/-- **Level two exists.**  If the classical level-one target is non-empty and `13` is a
quadratic non-residue, then the *second* preimage level is non-empty too — a target
strictly beyond `Φ₃`, since by `death_level_unique` the levels are disjoint. -/
theorem exists_death_level_two {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ω : F} (hω : phi3 ω = 0) (h13 : ¬ IsSquare (13 : F)) :
    ∃ y : F, (sylvWalk)^[2] y = -1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hω' : phi3 (-1 - ω) = 0 := phi3_neg_one_sub hω
  have hns : ¬ IsSquare ((1 + 4 * ω) * (1 + 4 * (-1 - ω))) := by
    rw [cube_root_pair_product_eq_thirteen hω]; exact h13
  have hlev : ∀ z : F, phi3 z = 0 → (sylvWalk)^[1] z = -1 := by
    intro z hz
    simpa using (sylvWalk_eq_neg_one_iff z).mpr hz
  rcases isSquare_or_isSquare_of_not_isSquare_mul hns with hs | hs
  · exact sylvWalk_step_of_isSquare h2 (hlev ω hω) hs
  · exact sylvWalk_step_of_isSquare h2 (hlev (-1 - ω) hω') hs

/-! ## Part 4: reciprocity turns the criterion into a congruence on `ℓ`

`13 ≡ 1 (mod 4)`, so the reciprocity sign is trivial and the criterion of Part 3 depends
only on `ℓ mod 13`. -/

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- **Quadratic reciprocity.**  Whether `13` is a residue modulo `ℓ` is decided by
`ℓ mod 13`; the non-residues mod `13` are `{2,5,6,7,8,11}`, a set of density `1/2`. -/
theorem isSquare_thirteen_iff {ℓ : ℕ} [Fact (Nat.Prime ℓ)] (h2 : ℓ ≠ 2) :
    IsSquare ((13 : ℕ) : ZMod ℓ) ↔ IsSquare ((ℓ : ℕ) : ZMod 13) :=
  (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 13) (q := ℓ) (by norm_num) h2).symm

/-! ## Part 5: what the branch must now avoid -/

/-- **The branch avoids every level.**  Restatement of
`BackwardOrbit.walkZ_notMem_preZero_of_perpetual` through the conjugacy: on the
perpetual-primality branch the take-all walk started at the branch value never dies,
modulo any prime `ℓ ≤ prod N`. -/
theorem sylvWalk_iterate_ne_neg_one_of_perpetual {N : ℕ} (hpp : PerpetualPrimality N)
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ) (hle : ℓ ≤ prod N) (k : ℕ) :
    (sylvWalk)^[k] (walkZ ℓ N) ≠ -1 := fun h =>
  walkZ_notMem_preZero_of_perpetual hpp hℓ hle
    ((mem_preZero_iff_sylvWalk_reaches_neg_one _).mpr ⟨k, h⟩)

theorem sylvWalk_iterate_two {R : Type*} [CommRing R] (w : R) :
    (sylvWalk)^[2] w = w ^ 4 + 2 * w ^ 3 + 2 * w ^ 2 + w := by
  show sylvWalk (sylvWalk w) = _
  unfold sylvWalk
  ring

/-- **The new constraint, written out.**  Beyond the classical `Φ₃` condition
`walkZ ℓ N ^ 2 + walkZ ℓ N + 1 ≠ 0`, the branch must also satisfy the level-two
condition — and by Part 3 that target is non-empty for a density-`1/2` set of the usable
primes, so this is not a consequence of the `Φ₃` obstruction. -/
theorem psi_two_ne_zero_of_perpetual {N : ℕ} (hpp : PerpetualPrimality N)
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ) (hle : ℓ ≤ prod N) :
    walkZ ℓ N ^ 4 + 2 * walkZ ℓ N ^ 3 + 2 * walkZ ℓ N ^ 2 + walkZ ℓ N + 1 ≠ 0 := by
  intro h
  refine sylvWalk_iterate_ne_neg_one_of_perpetual hpp hℓ hle 2 ?_
  rw [sylvWalk_iterate_two]
  linear_combination h

/-- **(C∞) as death of the take-all walk.**  A single death, at any level, modulo any
prime below the accumulator, refutes the branch at that stage. -/
theorem infinitelyManyComposite_of_sylvWalk_death
    (h : ∀ N : ℕ, ∃ ℓ : ℕ, Nat.Prime ℓ ∧ ℓ ≤ prod N ∧
      ∃ k : ℕ, (sylvWalk)^[k] (walkZ ℓ N) = -1) :
    InfinitelyManyComposite := by
  refine infinitelyManyComposite_of_small_backward_hit (fun N => ?_)
  obtain ⟨ℓ, hℓ, hle, hk⟩ := h N
  exact ⟨ℓ, hℓ, hle, (mem_preZero_iff_sylvWalk_reaches_neg_one _).mpr hk⟩

/-! ## Part 6: the lift, and level three

Everything in Part 3 was the `m = 1` case of one polynomial identity.  The two `q`-preimages
of a point `z` are `y` and `-1-y` (because `q(-1-y) = q(y)`), so their discriminants satisfy

    (1 + 4y) (1 + 4(-1-y)) = -3 - 16 q(y)          (`preimage_pair_discriminant`)

— an identity in the ring, provable by `ring`, with **no** appeal to Vieta or to the field.
Writing `Δ(z) = -3 - 16 z`, the pair of discriminants one level above `z` multiplies to
`Δ(z)`, and the whole level structure is governed by evaluating `Δ` along backward orbits.

At `z = -1` (level zero) this is `Δ(-1) = 13`, which is Part 3.  At `z = ω` (level one) it
is `Δ(ω) = -3 - 16ω`, and the two cube roots give `Δ(ω) Δ(ω²) = 217 = 7 · 31`.  The lift
below turns any such non-residue into a point two levels deeper. -/

/-- The two `q`-preimages of a point are `y` and `-1 - y`. -/
theorem sylvWalk_neg_one_sub {R : Type*} [CommRing R] (y : R) :
    sylvWalk (-1 - y) = sylvWalk y := by
  unfold sylvWalk; ring

/-- **The engine.**  The discriminants of the two preimages of `q(y)` multiply to
`Δ(q y) = -3 - 16 q(y)`.  A ring identity: Part 3's `13` is the case `q(y) = -1`. -/
theorem preimage_pair_discriminant {R : Type*} [CommRing R] (y : R) :
    (1 + 4 * y) * (1 + 4 * (-1 - y)) = -3 - 16 * sylvWalk y := by
  unfold sylvWalk; ring

/-- Solving `y² + y = z` explicitly. -/
theorem sylvWalk_half {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {z t : F}
    (ht : 1 + 4 * z = t * t) : sylvWalk ((t - 1) / 2) = z := by
  unfold sylvWalk
  field_simp
  linear_combination -ht

/-- **The lift.**  If a level-`m` point `z` has a square discriminant — so level `m+1` is
occupied above it — and `Δ(z) = -3 - 16z` is a *non*-square, then level `m+2` is occupied
as well.  Iterating this is how the tower is climbed. -/
theorem exists_death_level_add_two {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {z : F} {m : ℕ} (hz : (sylvWalk)^[m] z = -1)
    (hsq : IsSquare (1 + 4 * z)) (hΔ : ¬ IsSquare (-3 - 16 * z)) :
    ∃ y : F, (sylvWalk)^[m + 2] y = -1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨t, ht⟩ := hsq
  have hqy : sylvWalk ((t - 1) / 2) = z := sylvWalk_half h2 ht
  set y : F := (t - 1) / 2 with hydef
  have hy : (sylvWalk)^[m + 1] y = -1 := by
    rw [Function.iterate_succ_apply, hqy]; exact hz
  have hy' : (sylvWalk)^[m + 1] (-1 - y) = -1 := by
    rw [Function.iterate_succ_apply, sylvWalk_neg_one_sub, hqy]; exact hz
  have hprod : ¬ IsSquare ((1 + 4 * y) * (1 + 4 * (-1 - y))) := by
    rw [preimage_pair_discriminant, hqy]; exact hΔ
  rcases isSquare_or_isSquare_of_not_isSquare_mul hprod with hs | hs
  · exact sylvWalk_step_of_isSquare h2 hy hs
  · exact sylvWalk_step_of_isSquare h2 hy' hs

/-- **Level three.**  The `m = 1` instance of the lift. -/
theorem exists_death_level_three {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ω : F} (hω : phi3 ω = 0) (hsq : IsSquare (1 + 4 * ω))
    (hΔ : ¬ IsSquare (-3 - 16 * ω)) : ∃ y : F, (sylvWalk)^[3] y = -1 :=
  exists_death_level_add_two hF (m := 1)
    (by simpa using (sylvWalk_eq_neg_one_iff ω).mpr hω) hsq hΔ

/-- **The level-three constant.**  `Δ(ω) Δ(ω²) = 217 = 7 · 31`, the exact analogue of
`Δ(-1) Δ(-1) `'s role at level two — again by Vieta on `Φ₃`. -/
theorem delta_pair_product_eq_217 {R : Type*} [CommRing R] {ω : R} (h : phi3 ω = 0) :
    (-3 - 16 * ω) * (-3 - 16 * (-1 - ω)) = 217 := by
  unfold phi3 at h
  linear_combination (-256 : R) * h

/-- **Level three from a rational constant.**  If *both* level-two branches are present —
which is the case `13` is a residue, level two being then four points — and `217` is a
quadratic non-residue, then level three is occupied.

Note what this does *not* cover: when `13` is a non-residue exactly one branch is present,
and the level-three criterion `¬ IsSquare (-3 - 16ω)` genuinely depends on `ω`, not on a
rational constant.  That is the point at which the tower stops being decided by congruences
on `ℓ` alone and becomes a splitting condition in a larger field. -/
theorem exists_death_level_three_of_split {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {ω : F} (hω : phi3 ω = 0)
    (hs : IsSquare (1 + 4 * ω)) (hs' : IsSquare (1 + 4 * (-1 - ω)))
    (h217 : ¬ IsSquare (217 : F)) : ∃ y : F, (sylvWalk)^[3] y = -1 := by
  have hsplit : ¬ IsSquare (-3 - 16 * ω) ∨ ¬ IsSquare (-3 - 16 * (-1 - ω)) := by
    by_contra hc
    push Not at hc
    exact h217 (by rw [← delta_pair_product_eq_217 hω]; exact hc.1.mul hc.2)
  rcases hsplit with h | h
  · exact exists_death_level_three hF hω hs h
  · exact exists_death_level_three hF (phi3_neg_one_sub hω) hs' h

/-! ## Part 7: the tower has a top

Levels are disjoint (`death_level_unique`) and live in a finite field, so only finitely many
of them are occupied.  "Raising the level" is therefore a genuinely bounded resource: the
depth of the backward orbit tree of `-1` is an invariant of `ℓ`, and it is what the
heuristic `|PreZero ℓ| ≍ √ℓ` is really about. -/

/-- **Only finitely many levels are occupied.** -/
theorem realizedLevels_finite (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    Set.Finite {k : ℕ | ∃ y : ZMod ℓ, (sylvWalk)^[k] y = -1} := by
  classical
  set f : ℕ → ZMod ℓ := fun k =>
    if h : ∃ y : ZMod ℓ, (sylvWalk)^[k] y = -1 then h.choose else 0 with hf
  have hspec : ∀ k, (hk : ∃ y : ZMod ℓ, (sylvWalk)^[k] y = -1) →
      (sylvWalk)^[k] (f k) = -1 := by
    intro k hk
    simp only [hf, dif_pos hk]
    exact hk.choose_spec
  have hinj : Set.InjOn f {k : ℕ | ∃ y : ZMod ℓ, (sylvWalk)^[k] y = -1} := by
    intro a ha b hb hab
    have ha' := hspec a ha
    have hb' := hspec b hb
    rw [hab] at ha'
    exact death_level_unique ha' hb'
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

/-! ## Part 8: reciprocity, uniformly

Both level constants are `≡ 1 (mod 4)` — `13` and `217` — so the Jacobi reciprocity sign is
trivial and each criterion is a congruence condition on `ℓ` alone. -/

/-- **Reciprocity for a level constant.**  For `a ≡ 1 (mod 4)` and odd prime `ℓ`, whether
`a` is a non-residue mod `ℓ` is decided by `ℓ mod a`. -/
theorem not_isSquare_iff_jacobiSym {a ℓ : ℕ} [Fact (Nat.Prime ℓ)] (ha : a % 4 = 1)
    (hℓ : Odd ℓ) : ¬ IsSquare ((a : ℕ) : ZMod ℓ) ↔ jacobiSym (ℓ : ℤ) a = -1 := by
  have hcast : ((a : ℕ) : ZMod ℓ) = (((a : ℕ) : ℤ) : ZMod ℓ) := by push_cast; ring
  have h1 : ¬ IsSquare ((((a : ℕ) : ℤ)) : ZMod ℓ) ↔ jacobiSym ((a : ℕ) : ℤ) ℓ = -1 :=
    ZMod.nonsquare_iff_jacobiSym_eq_neg_one.symm
  have h2 : jacobiSym ((a : ℕ) : ℤ) ℓ = jacobiSym ((ℓ : ℕ) : ℤ) a :=
    jacobiSym.quadratic_reciprocity_one_mod_four ha hℓ
  rw [hcast, h1, h2]

/-- The level-two criterion as a congruence on `ℓ mod 13`. -/
theorem not_isSquare_thirteen_iff {ℓ : ℕ} [Fact (Nat.Prime ℓ)] (h2 : ℓ ≠ 2) :
    ¬ IsSquare ((13 : ℕ) : ZMod ℓ) ↔ jacobiSym (ℓ : ℤ) 13 = -1 :=
  not_isSquare_iff_jacobiSym (by norm_num) ((Fact.out : Nat.Prime ℓ).odd_of_ne_two h2)

/-- The level-three criterion as a congruence on `ℓ mod 217`. -/
theorem not_isSquare_217_iff {ℓ : ℕ} [Fact (Nat.Prime ℓ)] (h2 : ℓ ≠ 2) :
    ¬ IsSquare ((217 : ℕ) : ZMod ℓ) ↔ jacobiSym (ℓ : ℤ) 217 = -1 :=
  not_isSquare_iff_jacobiSym (by norm_num) ((Fact.out : Nat.Prime ℓ).odd_of_ne_two h2)

/-! ## Part 9: the level-three constraint on the branch -/

theorem sylvWalk_iterate_three {R : Type*} [CommRing R] (w : R) :
    (sylvWalk)^[3] w =
      w ^ 8 + 4 * w ^ 7 + 8 * w ^ 6 + 10 * w ^ 5 + 9 * w ^ 4 + 6 * w ^ 3 + 3 * w ^ 2 + w := by
  show sylvWalk (sylvWalk (sylvWalk w)) = _
  unfold sylvWalk
  ring

/-- **The level-three constraint.**  A third avoidance condition on the
perpetual-primality branch, independent of the level-one (`Φ₃`) and level-two conditions
because the levels are disjoint. -/
theorem psi_three_ne_zero_of_perpetual {N : ℕ} (hpp : PerpetualPrimality N)
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ) (hle : ℓ ≤ prod N) :
    walkZ ℓ N ^ 8 + 4 * walkZ ℓ N ^ 7 + 8 * walkZ ℓ N ^ 6 + 10 * walkZ ℓ N ^ 5
        + 9 * walkZ ℓ N ^ 4 + 6 * walkZ ℓ N ^ 3 + 3 * walkZ ℓ N ^ 2 + walkZ ℓ N + 1 ≠ 0 := by
  intro h
  refine sylvWalk_iterate_ne_neg_one_of_perpetual hpp hℓ hle 3 ?_
  rw [sylvWalk_iterate_three]
  linear_combination h

/-! ## Landscape -/

/-- **Raising the level.**  The classical `Φ₃` obstruction is level one of a tower of
disjoint levels, all living on the same moduli `ℓ ≡ 1 (mod 6)`; level two is non-empty
whenever `13` is a quadratic non-residue, which quadratic reciprocity turns into a
congruence condition on `ℓ` of density `1/2`. -/
theorem backward_levels_landscape :
    -- the conjugacy: `Φ₆` levels are take-all steps
    (∀ (R : Type) (_ : CommRing R) (k : ℕ) (w : R),
      (phi6)^[k] (w + 1) = (sylvWalk)^[k] w + 1) ∧
    (∀ (ℓ : ℕ) (w : ZMod ℓ), w + 1 ∈ PreZero ℓ ↔ ∃ k, (sylvWalk)^[k] w = -1) ∧
    -- levels are disjoint, and buy no new moduli
    (∀ (R : Type) (_ : CommRing R) (_ : Nontrivial R) (w : R) (i j : ℕ),
      (sylvWalk)^[i] w = -1 → (sylvWalk)^[j] w = -1 → i = j) ∧
    (∀ (ℓ : ℕ) (_ : Fact (Nat.Prime ℓ)), ℓ ≠ 2 → ℓ ≠ 3 → ∀ (w : ZMod ℓ) (k : ℕ),
      (sylvWalk)^[k + 1] w = -1 → 6 ∣ ℓ - 1) ∧
    -- past `Φ₃`: the step lemma, the Vieta constant, and level two
    (∀ (R : Type) (_ : CommRing R) (ω : R), phi3 ω = 0 →
      (1 + 4 * ω) * (1 + 4 * (-1 - ω)) = 13) ∧
    (∀ (ℓ : ℕ) (_ : Fact (Nat.Prime ℓ)), ringChar (ZMod ℓ) ≠ 2 →
      ∀ ω : ZMod ℓ, phi3 ω = 0 → ¬ IsSquare (13 : ZMod ℓ) →
        ∃ y : ZMod ℓ, (sylvWalk)^[2] y = -1) ∧
    -- the engine behind every level: the two preimages of `z` have discriminant product `Δ(z)`
    (∀ (R : Type) (_ : CommRing R) (y : R),
      (1 + 4 * y) * (1 + 4 * (-1 - y)) = -3 - 16 * sylvWalk y) ∧
    -- the lift, and level three
    (∀ (ℓ : ℕ) (_ : Fact (Nat.Prime ℓ)), ringChar (ZMod ℓ) ≠ 2 →
      ∀ (z : ZMod ℓ) (m : ℕ), (sylvWalk)^[m] z = -1 → IsSquare (1 + 4 * z) →
        ¬ IsSquare (-3 - 16 * z) → ∃ y : ZMod ℓ, (sylvWalk)^[m + 2] y = -1) ∧
    (∀ (R : Type) (_ : CommRing R) (ω : R), phi3 ω = 0 →
      (-3 - 16 * ω) * (-3 - 16 * (-1 - ω)) = 217) ∧
    (∀ (ℓ : ℕ) (_ : Fact (Nat.Prime ℓ)), ringChar (ZMod ℓ) ≠ 2 →
      ∀ ω : ZMod ℓ, phi3 ω = 0 → IsSquare (1 + 4 * ω) → IsSquare (1 + 4 * (-1 - ω)) →
        ¬ IsSquare (217 : ZMod ℓ) → ∃ y : ZMod ℓ, (sylvWalk)^[3] y = -1) ∧
    -- but the tower has a top: only finitely many levels are occupied
    (∀ (ℓ : ℕ) (_ : Fact (Nat.Prime ℓ)),
      Set.Finite {k : ℕ | ∃ y : ZMod ℓ, (sylvWalk)^[k] y = -1}) ∧
    -- and the branch must now avoid levels two and three as well
    (∀ N : ℕ, PerpetualPrimality N → ∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ≤ prod N →
      walkZ ℓ N ^ 4 + 2 * walkZ ℓ N ^ 3 + 2 * walkZ ℓ N ^ 2 + walkZ ℓ N + 1 ≠ 0) ∧
    (∀ N : ℕ, PerpetualPrimality N → ∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ≤ prod N →
      walkZ ℓ N ^ 8 + 4 * walkZ ℓ N ^ 7 + 8 * walkZ ℓ N ^ 6 + 10 * walkZ ℓ N ^ 5
        + 9 * walkZ ℓ N ^ 4 + 6 * walkZ ℓ N ^ 3 + 3 * walkZ ℓ N ^ 2 + walkZ ℓ N + 1 ≠ 0) ∧
    (∀ N : ℕ, PerpetualPrimality N → ∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ≤ prod N → ∀ k : ℕ,
      (sylvWalk)^[k] (walkZ ℓ N) ≠ -1) :=
  ⟨fun _ _ k w => iterate_phi6_add_one k w,
    fun _ w => mem_preZero_iff_sylvWalk_reaches_neg_one w,
    fun _ _ _ _ _ _ hi hj => death_level_unique hi hj,
    fun _ inst h2 h3 _ _ h => by have := inst; exact six_dvd_sub_one_of_death h2 h3 h,
    fun _ _ _ h => cube_root_pair_product_eq_thirteen h,
    fun _ inst hF _ hω h13 => by have := inst; exact exists_death_level_two hF hω h13,
    fun _ _ y => preimage_pair_discriminant y,
    fun _ inst hF _ _ hz hsq hΔ => by
      have := inst; exact exists_death_level_add_two hF hz hsq hΔ,
    fun _ _ _ h => delta_pair_product_eq_217 h,
    fun _ inst hF _ hω hs hs' h217 => by
      have := inst; exact exists_death_level_three_of_split hF hω hs hs' h217,
    fun _ inst => by have := inst; exact realizedLevels_finite _,
    fun _ hpp _ hℓ hle => psi_two_ne_zero_of_perpetual hpp hℓ hle,
    fun _ hpp _ hℓ hle => psi_three_ne_zero_of_perpetual hpp hℓ hle,
    fun _ hpp _ hℓ hle k => sylvWalk_iterate_ne_neg_one_of_perpetual hpp hℓ hle k⟩

end BackwardLevels

end
