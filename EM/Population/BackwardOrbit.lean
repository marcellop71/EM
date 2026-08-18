import EM.Population.SylvesterTower
import EM.Population.DefectTelescope

/-!
# (C∞) as a Hitting Statement: the Backward Orbit of Zero

`EM/Population/SylvesterTower.lean` identifies (C∞) with the failure of Sylvester-tower
primality, and `EM/Population/DefectTelescope.lean` shows the growth constant is a
complete invariant for it.  Both leave (C∞) as a statement about the *primality* of
specific integers, which is the axis on which the project has no leverage.

This file moves it onto the axis the project is actually built on: **hitting statements
for the residue walk** `walkZ ℓ n = prod n mod ℓ`.

## The criterion

A prime `ℓ` divides the `k`-th term of the Sylvester tower seeded at `s` exactly when
`s mod ℓ` reaches `0` after `k` steps of

    Φ₆(x) = x² - x + 1          (`phi6`).

So, writing `PreZero ℓ ⊆ ZMod ℓ` for the **backward orbit of `0`** — the set of residues
whose `Φ₆`-orbit reaches `0` — the whole of (C∞) is

> for every `N` there is a prime `ℓ` with `walkZ ℓ N + 1 ∈ PreZero ℓ`,
> witnessed below the tower term it kills

(`backwardOrbitHitting_iff_infinitelyManyComposite`).  Contrapositively, on the
perpetual-primality branch the walk value at the branch point must **avoid** `PreZero ℓ`
for every prime `ℓ ≤ prod N` at once (`walkZ_notMem_preZero_of_perpetual`).

## Why this is worth doing: the target is large

Compare the two hitting problems the project now contains.

| statement | target in `ZMod q` | quantifier over moduli |
|---|---|---|
| `MullinConjecture` | the single residue `-1` | **every** prime `q` |
| (C∞), via this file | `PreZero ℓ` | **some** prime `ℓ`, per stage |

`PreZero` is backward-closed under `Φ₆` (`mem_preZero_of_phi6_mem`): it is the union of
all iterated preimages of `0`, not one point.  For a map on `ZMod ℓ` whose functional
graph behaves generically the in-tree of a node has size of order `√ℓ`, so the target has
density about `ℓ^(-1/2)` rather than `ℓ^(-1)`, and `∑_ℓ ℓ^(-1/2)` diverges at the rate
`√L / log L`.  (That count is a heuristic and is *not* formalised here; what is formalised
is the criterion and the backward-closure that makes the target a union of levels.)

Against that, `PreZero ℓ` is trivial for most primes: a nonzero element of it forces a
root of `Φ₆`, hence a primitive sixth root of unity, hence `ℓ ≡ 1 (mod 6)`
(`cube_eq_neg_one_of_phi6_eq_zero`, `six_dvd_sub_one_of_phi6_root`).  So the supply of
useful moduli is half the primes — still infinite, and still summing to infinity.

The upshot is a calibration rather than a proof: (C∞) needs an *existential* hit against a
large target, where MC needs a *universal* hit against a single residue.  Any hitting
hypothesis strong enough for MC is far more than (C∞) requires.

## What this does not do

It does not evade Dead End #90.  The criterion still asks where one specific orbit sits
modulo some prime, and no sieve constrains a single integer.  What it does is put the
question in the same language as the rest of the programme, so that the existing hitting
hypotheses can be measured against it — and every one of them is now visibly overkill.

## Contents

* `phi6`, `PreZero` — the Sylvester map on a ring, and the backward orbit of `0`.
* `cast_tower` — the tower reduces to iterating `Φ₆` in `ZMod ℓ`.
* `walkZ_notMem_preZero_of_perpetual` — the branch criterion.
* `BackwardOrbitHitting`, `backwardOrbitHitting_iff_infinitelyManyComposite` — (C∞)
  restated as a hitting statement.
* `backward_orbit_landscape` — the audit: everything above (C∞) implies it.
-/

noncomputable section

open Mullin Euclid MullinGroup AutonomousBranch SylvesterTower

namespace BackwardOrbit

/-! ## Part 1: the Sylvester map and the backward orbit of zero -/

/-- The **Sylvester map** `Φ₆(x) = x² - x + 1`, written so that it makes sense over any
commutative ring and matches `SylvesterTower.tower` on `ℕ`. -/
def phi6 {R : Type*} [CommRing R] (x : R) : R := x * (x - 1) + 1

/-- The **backward orbit of `0`**: residues whose `Φ₆`-orbit reaches `0`.  A prime `ℓ`
divides some term of the Sylvester tower seeded at `s` exactly when `s mod ℓ` lies here. -/
def PreZero (ℓ : ℕ) : Set (ZMod ℓ) := {x | ∃ k : ℕ, (phi6)^[k] x = 0}

theorem zero_mem_preZero (ℓ : ℕ) : (0 : ZMod ℓ) ∈ PreZero ℓ := ⟨0, rfl⟩

/-- **`PreZero` is backward-closed.**  This is what makes the target a union of preimage
levels rather than a single point. -/
theorem mem_preZero_of_phi6_mem {ℓ : ℕ} {x : ZMod ℓ} (h : phi6 x ∈ PreZero ℓ) :
    x ∈ PreZero ℓ := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- A root of `Φ₆` is a primitive sixth root of unity: `y ^ 3 = -1`. -/
theorem cube_eq_neg_one_of_phi6_eq_zero {R : Type*} [CommRing R] {y : R}
    (h : phi6 y = 0) : y ^ 3 = -1 := by
  have h' : y * (y - 1) + 1 = 0 := h
  linear_combination (y + 1) * h'

theorem phi6_zero {R : Type*} [CommRing R] : phi6 (0 : R) = 1 := by
  unfold phi6; ring

/-- **`PreZero` is trivial unless `ℓ ≡ 1 (mod 6)`.**  A root of `Φ₆` modulo `ℓ` has
multiplicative order `6`, so `6 ∣ ℓ - 1`.  Half the primes therefore supply no target at
all. -/
theorem six_dvd_sub_one_of_phi6_root {ℓ : ℕ} [Fact (Nat.Prime ℓ)] (h2 : ℓ ≠ 2)
    (h3 : ℓ ≠ 3) {y : ZMod ℓ} (h : phi6 y = 0) : 6 ∣ ℓ - 1 := by
  have hcube : y ^ 3 = -1 := cube_eq_neg_one_of_phi6_eq_zero h
  have hy6 : y ^ 6 = 1 := by
    have : y ^ 6 = (y ^ 3) ^ 2 := by ring
    rw [this, hcube]; ring
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, phi6_zero] at h
    exact one_ne_zero h
  -- `orderOf y` divides `6` and `ℓ - 1`
  have hdvd6 : orderOf y ∣ 6 := orderOf_dvd_of_pow_eq_one hy6
  have hdvdF : orderOf y ∣ ℓ - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hy0)
  -- rule out order dividing 2 or 3
  have hne2 : ¬ orderOf y ∣ 2 := by
    intro hd
    have hy2 : y ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
    -- `y ^ 2 = y - 1`, so `y = 2` and then `Φ₆(2) = 3 = 0`
    have hy2' : y * (y - 1) + 1 = 0 := h
    have : y = 2 := by linear_combination hy2 - hy2'
    rw [this] at h
    have h3' : (3 : ZMod ℓ) = 0 := by rw [← h]; unfold phi6; ring
    have hd3 : (ℓ : ℕ) ∣ 3 := (ZMod.natCast_eq_zero_iff 3 ℓ).mp (by exact_mod_cast h3')
    rcases Nat.prime_three.eq_one_or_self_of_dvd ℓ hd3 with h1 | h1
    · exact (Fact.out : Nat.Prime ℓ).ne_one h1
    · exact h3 h1
  have hne3 : ¬ orderOf y ∣ 3 := by
    intro hd
    have hy3 : y ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
    rw [hcube] at hy3
    have h2' : (2 : ZMod ℓ) = 0 := by linear_combination -hy3
    have hd2 : (ℓ : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 ℓ).mp (by exact_mod_cast h2')
    rcases Nat.prime_two.eq_one_or_self_of_dvd ℓ hd2 with h1 | h1
    · exact (Fact.out : Nat.Prime ℓ).ne_one h1
    · exact h2 h1
  have hord : orderOf y = 6 := by
    have hle : orderOf y ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
    interval_cases h : orderOf y <;> simp_all
  rw [← hord]
  exact hdvdF

/-! ## Part 2: the tower reduces to iterating `Φ₆` -/

theorem two_le_tower {s : ℕ} (hs : 2 ≤ s) (k : ℕ) : 2 ≤ tower s k := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
      rw [tower_succ]
      have h1 : 1 ≤ tower s k - 1 := by omega
      have : 2 * 1 ≤ tower s k * (tower s k - 1) := Nat.mul_le_mul ih h1
      omega

theorem self_le_tower {s : ℕ} (hs : 2 ≤ s) (k : ℕ) : s ≤ tower s k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [tower_succ]
      have h2 := two_le_tower hs k
      have h1 : 1 ≤ tower s k - 1 := by omega
      have : tower s k * 1 ≤ tower s k * (tower s k - 1) := Nat.mul_le_mul_left _ h1
      omega

/-- **The reduction.**  Reducing the Sylvester tower modulo `ℓ` is iterating `Φ₆`. -/
theorem cast_tower {s : ℕ} (hs : 2 ≤ s) (ℓ k : ℕ) :
    ((tower s k : ℕ) : ZMod ℓ) = (phi6)^[k] ((s : ℕ) : ZMod ℓ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ← ih, tower_succ]
      have h1 : (1 : ℕ) ≤ tower s k := by have := two_le_tower hs k; omega
      unfold phi6
      push_cast [Nat.cast_sub h1]
      ring

/-- A prime divides a tower term exactly when the seed's residue reaches `0`. -/
theorem dvd_tower_iff {s : ℕ} (hs : 2 ≤ s) (ℓ k : ℕ) :
    ℓ ∣ tower s k ↔ (phi6)^[k] ((s : ℕ) : ZMod ℓ) = 0 := by
  rw [← cast_tower hs ℓ k, ZMod.natCast_eq_zero_iff]

/-! ## Part 3: the criterion -/

/-- **The branch criterion.**  On the perpetual-primality branch the walk value at the
branch point must avoid the backward orbit of `0` modulo *every* prime `ℓ ≤ prod N`
simultaneously.  A single hit anywhere refutes the branch. -/
theorem walkZ_notMem_preZero_of_perpetual {N : ℕ} (hpp : PerpetualPrimality N)
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ) (hle : ℓ ≤ prod N) :
    walkZ ℓ N + 1 ∉ PreZero ℓ := by
  rintro ⟨k, hk⟩
  have hs : 2 ≤ prod N + 1 := by have := prod_ge_two N; omega
  rw [← walk_add_one_cast] at hk
  have hdvd : ℓ ∣ tower (prod N + 1) k := (dvd_tower_iff hs ℓ k).mpr hk
  have hprime : Nat.Prime (tower (prod N + 1) k) :=
    perpetualPrimality_iff_tower_prime.mp hpp k
  have hself := self_le_tower hs k
  rcases (Nat.Prime.eq_one_or_self_of_dvd hprime ℓ hdvd) with h1 | h1
  · exact hℓ.ne_one h1
  · omega

/-! ### Level 1 of the target is the classical death equation

`Φ₆(w + 1) = w² + w + 1 = Φ₃(w)`.  So the *first* preimage level of `0` is exactly the
death condition of the take-all rule — the equation whose insolubility modulo
`q ≡ 2 (mod 3)` drives `AutonomousBranch.perpetual_primality_excludes_two_mod_three` and
the density-`1/2` failure of the Sylvester rule.

`PreZero` is the entire backward orbit of that condition.  So where the classical
obstruction uses one level, (C∞) may use any level, and the levels accumulate: this is the
precise sense in which the target here is larger than the one the project has been aiming
at. -/

theorem phi6_add_one (ℓ : ℕ) (w : ZMod ℓ) : phi6 (w + 1) = w ^ 2 + w + 1 := by
  unfold phi6; ring

/-- A root of `Φ₃` gives a level-`1` hit. -/
theorem mem_preZero_of_phi3_root {ℓ : ℕ} {w : ZMod ℓ} (h : w ^ 2 + w + 1 = 0) :
    w + 1 ∈ PreZero ℓ :=
  ⟨1, by rw [Function.iterate_one, phi6_add_one]; exact h⟩

/-- **The branch avoids the death equation at every small prime.**  A special case of
`walkZ_notMem_preZero_of_perpetual` at level `1`, and the point of contact with the
existing `Φ₃` analysis: there the obstruction is that no root exists modulo
`q ≡ 2 (mod 3)`; here, even where roots do exist, the walk must miss them. -/
theorem phi3_ne_zero_of_perpetual {N : ℕ} (hpp : PerpetualPrimality N)
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ) (hle : ℓ ≤ prod N) :
    walkZ ℓ N ^ 2 + walkZ ℓ N + 1 ≠ 0 := fun h =>
  walkZ_notMem_preZero_of_perpetual hpp hℓ hle (mem_preZero_of_phi3_root h)

/-- **(BO)** — the backward-orbit hitting hypothesis.  For every stage `N` some prime
lands the seed's residue in the backward orbit of `0`, witnessed strictly below the tower
term it kills. -/
def BackwardOrbitHitting : Prop :=
  ∀ N : ℕ, ∃ ℓ : ℕ, Nat.Prime ℓ ∧ ∃ k : ℕ,
    (phi6)^[k] (walkZ ℓ N + 1) = 0 ∧ ℓ < tower (prod N + 1) k

/-- **(C∞) is a hitting statement.**  The two are equivalent, so nothing is lost in the
translation and the whole target ladder transfers. -/
theorem backwardOrbitHitting_iff_infinitelyManyComposite :
    BackwardOrbitHitting ↔ InfinitelyManyComposite := by
  rw [SylvesterTower.infinitelyManyComposite_iff_tower_composite]
  constructor
  · intro h N
    obtain ⟨ℓ, hℓ, k, hk, hlt⟩ := h N
    have hs : 2 ≤ prod N + 1 := by have := prod_ge_two N; omega
    rw [← walk_add_one_cast] at hk
    have hdvd : ℓ ∣ tower (prod N + 1) k := (dvd_tower_iff hs ℓ k).mpr hk
    refine ⟨k, fun hp => ?_⟩
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp ℓ hdvd) with h1 | h1
    · exact hℓ.ne_one h1
    · omega
  · intro h N
    obtain ⟨k, hk⟩ := h N
    have hs : 2 ≤ prod N + 1 := by have := prod_ge_two N; omega
    have hT : 2 ≤ tower (prod N + 1) k := two_le_tower hs k
    refine ⟨Nat.minFac (tower (prod N + 1) k), Nat.minFac_prime (by omega), k, ?_, ?_⟩
    · rw [← walk_add_one_cast]
      exact (dvd_tower_iff hs _ k).mp (Nat.minFac_dvd _)
    · rcases lt_or_eq_of_le (Nat.minFac_le (show 0 < tower (prod N + 1) k by omega))
        with h' | h'
      · exact h'
      · exact absurd (by rw [← h']; exact Nat.minFac_prime (by omega)) hk

/-- **The convenient sufficient form.**  A hit modulo any prime at most `prod N` suffices,
because every tower term exceeds the seed. -/
theorem infinitelyManyComposite_of_small_backward_hit
    (h : ∀ N : ℕ, ∃ ℓ : ℕ, Nat.Prime ℓ ∧ ℓ ≤ prod N ∧ walkZ ℓ N + 1 ∈ PreZero ℓ) :
    InfinitelyManyComposite := by
  refine backwardOrbitHitting_iff_infinitelyManyComposite.mp (fun N => ?_)
  obtain ⟨ℓ, hℓ, hle, k, hk⟩ := h N
  have hs : 2 ≤ prod N + 1 := by have := prod_ge_two N; omega
  exact ⟨ℓ, hℓ, k, hk, lt_of_le_of_lt hle (by have := self_le_tower hs k; omega)⟩

/-! ## Part 4: the audit

Since (BO) is *equivalent* to (C∞), everything the project has placed above (C∞) sits
above (BO) too — and (BO) asks for far less than any of them.  The list below is the
calibration: read it as "each of these hypotheses is strong enough to force a single
`PreZero` hit per stage, which is all that is needed". -/

theorem backwardOrbitHitting_of_reciprocalDivergence (h : ReciprocalDivergence) :
    BackwardOrbitHitting :=
  backwardOrbitHitting_iff_infinitelyManyComposite.mpr
    (CompositeFloor.infinitelyManyComposite_of_reciprocalDivergence h)

theorem backwardOrbitHitting_of_mullin (h : MullinConjecture) : BackwardOrbitHitting :=
  backwardOrbitHitting_iff_infinitelyManyComposite.mpr
    (CompositeFloor.infinitelyManyComposite_of_mullin h)

theorem backwardOrbitHitting_of_everyPrimeDividesEuclid
    (h : WeakHitting.EveryPrimeDividesEuclid) : BackwardOrbitHitting :=
  backwardOrbitHitting_iff_infinitelyManyComposite.mpr
    (SylvesterTower.infinitelyManyComposite_of_everyPrimeDividesEuclid h)

/-- (BO) is also exactly the vanishing of the growth constant. -/
theorem backwardOrbitHitting_iff_growthConstant_eq_zero :
    BackwardOrbitHitting ↔ DefectTelescope.growthConstant = 0 :=
  backwardOrbitHitting_iff_infinitelyManyComposite.trans
    DefectTelescope.infinitelyManyComposite_iff_growthConstant_eq_zero

/-- **Landscape.**  (C∞) is a hitting statement for the residue walk against the backward
orbit of `0`; the branch criterion is its contrapositive; and every hypothesis the project
has placed above (C∞) implies it. -/
theorem backward_orbit_landscape :
    -- the reduction and the criterion
    (∀ s : ℕ, 2 ≤ s → ∀ ℓ k : ℕ, (ℓ ∣ tower s k ↔ (phi6)^[k] ((s : ℕ) : ZMod ℓ) = 0)) ∧
    (∀ N : ℕ, PerpetualPrimality N → ∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ≤ prod N →
      walkZ ℓ N + 1 ∉ PreZero ℓ) ∧
    -- (C∞) restated as hitting, with nothing lost
    (BackwardOrbitHitting ↔ InfinitelyManyComposite) ∧
    (BackwardOrbitHitting ↔ DefectTelescope.growthConstant = 0) ∧
    -- the target is a union of preimage levels, and is trivial off `ℓ ≡ 1 (mod 6)`
    (∀ ℓ : ℕ, ∀ x : ZMod ℓ, phi6 x ∈ PreZero ℓ → x ∈ PreZero ℓ) ∧
    -- level 1 is exactly the classical death equation `Φ₃`
    (∀ (ℓ : ℕ) (w : ZMod ℓ), phi6 (w + 1) = w ^ 2 + w + 1) ∧
    (∀ N : ℕ, PerpetualPrimality N → ∀ ℓ : ℕ, Nat.Prime ℓ → ℓ ≤ prod N →
      walkZ ℓ N ^ 2 + walkZ ℓ N + 1 ≠ 0) ∧
    (∀ (ℓ : ℕ) (_ : Fact (Nat.Prime ℓ)), ℓ ≠ 2 → ℓ ≠ 3 →
      ∀ y : ZMod ℓ, phi6 y = 0 → 6 ∣ ℓ - 1) ∧
    -- the audit
    (ReciprocalDivergence → BackwardOrbitHitting) ∧
    (MullinConjecture → BackwardOrbitHitting) ∧
    (WeakHitting.EveryPrimeDividesEuclid → BackwardOrbitHitting) :=
  ⟨fun _ hs ℓ k => dvd_tower_iff hs ℓ k,
    fun _ hpp _ hℓ hle => walkZ_notMem_preZero_of_perpetual hpp hℓ hle,
    backwardOrbitHitting_iff_infinitelyManyComposite,
    backwardOrbitHitting_iff_growthConstant_eq_zero,
    fun _ _ h => mem_preZero_of_phi6_mem h,
    phi6_add_one,
    fun _ hpp _ hℓ hle => phi3_ne_zero_of_perpetual hpp hℓ hle,
    fun _ inst h2 h3 _ h => @six_dvd_sub_one_of_phi6_root _ inst h2 h3 _ h,
    backwardOrbitHitting_of_reciprocalDivergence,
    backwardOrbitHitting_of_mullin,
    backwardOrbitHitting_of_everyPrimeDividesEuclid⟩

end BackwardOrbit

end
