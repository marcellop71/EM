import EM.Population.BackwardLevels

/-!
# The Arboreal Tower: Witnesses Are Free, Smallness Is Everything

`EM/Population/BackwardLevels.lean` ends at a wall.  The levels of the backward orbit of
`-1` under the take-all walk `q(y) = y² + y` are disjoint and finite in number, so climbing
them one at a time terminates; and past level three the criteria stop being congruence
conditions on `ℓ` and become splitting conditions in larger fields.  The natural next move
is to stop climbing and ask about the **whole tree** at once — the arboreal picture, where
the tool of record is the Chebotarev density theorem applied to the splitting fields of the
iterates.

This file does that, and the outcome is not the one the setup suggests.

## The tree

Write `Ψ n (w) = q^[n] (w) + 1`, so that level `n` is occupied at `w` exactly when
`Ψ n (w) = 0`.  Two identities organise everything:

* `Ψ n (0) = 1` — the constant term of every level polynomial is `1`, because `q(0) = 0`;
* `q^[n+1] (w) = w · ∏_{j ≤ n} Ψ j (w)` (`sylvWalk_iterate_succ_eq_prod`) — the exact
  polynomial shadow of the Euclid–Mullin accumulator identity `prod (n+1) = ∏ seq`.

## Chebotarev is not needed for the qualitative statement

The question Chebotarev is usually invoked for is: *for how many primes `ℓ` is level `n`
occupied?*  Its qualitative half — that there are infinitely many, for every level — is
**unconditional here**, by the argument this whole project is named after.  Since
`Ψ n (0) = 1`, feeding `q^[n]` a multiple of `B !` returns a value `≡ 1 (mod B !)`, so every
prime factor of it exceeds `B`:

> **For every level `n` and every bound `B` there is a prime `ℓ > B` at which level `n` is
> occupied** (`exists_large_prime_level_occupied`), hence infinitely many
> (`levelPrimes_infinite`).

No density theorem is used.  What Chebotarev would add is the *density* of those primes —
and that turns out not to be the missing ingredient, for the reason below.

## What is actually missing: a size condition

Specialise the same construction to `w = prod N`.  A prime `ℓ` puts the walk value
`walkZ ℓ N` at level `k` exactly when `ℓ` divides `Ψ k (prod N)`
(`level_witness_iff`), and `Ψ k (prod N)` is the `k`-th Sylvester tower term above the
Euclid number (`tower_eq_sylvNat`).  So a witness prime always exists — take the least
prime factor — and

> **(C∞) ⟺ for every `N` some witness is a *proper* factor**
> (`infinitelyManyComposite_iff_witness_proper`).

That is the whole of it.  Existence of a prime witnessing any level is free; the entire
difficulty is that the witness produced must be **smaller than the number it divides**.  On
the perpetual-primality branch the witness at level `k` is forced to be `Ψ k (prod N)`
itself — a prime larger than `prod N` — which is exactly the branch
(`witness_eq_self_of_perpetual`).

And the supply of witnesses is genuinely infinite, not a repetition of one prime: the level
values are pairwise coprime (`coprime_level_values`, the Euclid cascade one level up), so
the witnesses at distinct levels are **distinct primes** (`minFac_level_injective`).  Each
stage `N` therefore carries an infinite sequence of distinct primes, free of charge, and
(C∞) asks only that one of them be smaller than the value it divides.

This is the same shape as `(S)` in `EM/Population/CompositeFloor.lean`: not "does something
exist", but "is the thing that exists small".  A density theorem over `ℓ` cannot supply it,
because the required prime must divide one specific integer.  That is Dead End #90, and the
arboreal picture makes it as sharp as it can be made: **the arboreal input is free and the
residual gap is disjoint from it.**

## Contents

* `sylvNat`, `cast_sylvNat_iterate` — the walk over `ℕ` and its reduction mod `ℓ`.
* `sylvWalk_iterate_succ_eq_prod` — the accumulator identity for the tree.
* `exists_large_prime_level_occupied`, `levelPrimes_infinite` — every level is occupied at
  infinitely many primes, unconditionally.
* `level_witness_iff`, `infinitelyManyComposite_iff_witness_proper` — witnesses are free;
  smallness is everything.
* `coprime_level_values`, `minFac_level_injective` — the witnesses at distinct levels are
  distinct primes.
* `ArborealChebotarev`, `arboreal_tower_landscape`.
-/

noncomputable section

open Mullin MullinGroup AutonomousBranch SylvesterTower BackwardLevels

namespace ArborealTower

/-! ## Part 1: the take-all walk over `ℕ`, and its reduction -/

/-- The take-all walk on `ℕ`: `q(y) = y² + y`.  Written without subtraction so that it
reduces to `BackwardLevels.sylvWalk` under any ring homomorphism. -/
def sylvNat (y : ℕ) : ℕ := y * y + y

theorem cast_sylvNat {R : Type*} [CommRing R] (x : ℕ) :
    ((sylvNat x : ℕ) : R) = sylvWalk ((x : ℕ) : R) := by
  unfold sylvNat sylvWalk
  push_cast
  ring

/-- **Reduction commutes with iteration.** -/
theorem cast_sylvNat_iterate {R : Type*} [CommRing R] (n : ℕ) (x : ℕ) :
    ((sylvNat^[n] x : ℕ) : R) = (sylvWalk)^[n] ((x : ℕ) : R) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, cast_sylvNat]

theorem sylvNat_zero : sylvNat 0 = 0 := by unfold sylvNat; ring

theorem le_sylvNat (y : ℕ) : y ≤ sylvNat y := by unfold sylvNat; omega

theorem le_sylvNat_iterate (n y : ℕ) : y ≤ sylvNat^[n] y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (le_sylvNat _)

/-- **`Ψ n` has constant term `1`.**  Divisors of the argument survive into the iterate,
because `q(y) = y (y+1)`. -/
theorem dvd_sylvNat_iterate {d : ℕ} (n : ℕ) {x : ℕ} (h : d ∣ x) : d ∣ sylvNat^[n] x := by
  induction n generalizing x with
  | zero => simpa using h
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      refine ih ?_
      unfold sylvNat
      exact dvd_add (h.mul_right x) h

/-! ## Part 2: the accumulator identity for the tree -/

/-- **The tree's accumulator identity.**  `q^[n+1] w = w · ∏_{j ≤ n} (q^[j] w + 1)`: the
exact polynomial shadow of `prod (n+1) = seq 0 ⋯ seq (n+1)`.  It is what makes the level
polynomials pairwise coprime, hence the levels disjoint. -/
theorem sylvWalk_iterate_succ_eq_prod {R : Type*} [CommRing R] (w : R) (n : ℕ) :
    (sylvWalk)^[n + 1] w = w * ∏ j ∈ Finset.range (n + 1), ((sylvWalk)^[j] w + 1) := by
  induction n with
  | zero =>
      rw [Finset.prod_range_one]
      show sylvWalk w = w * ((sylvWalk)^[0] w + 1)
      simp only [Function.iterate_zero_apply]
      unfold sylvWalk
      ring
  | succ n ih =>
      rw [Function.iterate_succ_apply', Finset.prod_range_succ, ← mul_assoc, ← ih]
      unfold sylvWalk
      ring

/-- The same identity over `ℕ`. -/
theorem sylvNat_iterate_succ_eq_prod (x : ℕ) (n : ℕ) :
    sylvNat^[n + 1] x = x * ∏ j ∈ Finset.range (n + 1), (sylvNat^[j] x + 1) := by
  induction n with
  | zero =>
      rw [Finset.prod_range_one]
      show sylvNat x = x * (sylvNat^[0] x + 1)
      simp only [Function.iterate_zero_apply]
      unfold sylvNat
      ring
  | succ n ih =>
      rw [Function.iterate_succ_apply', Finset.prod_range_succ, ← mul_assoc, ← ih]
      unfold sylvNat
      ring

/-- **The level values are pairwise coprime.**  Exactly the Euclid coprimality cascade,
one level up: `Ψ (j) - 1` is a product containing `Ψ i` for every `i < j`. -/
theorem coprime_level_values (x : ℕ) {i j : ℕ} (hij : i < j) :
    Nat.Coprime (sylvNat^[i] x + 1) (sylvNat^[j] x + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  set d := Nat.gcd (sylvNat^[i] x + 1) (sylvNat^[m + 1] x + 1) with hd
  have hdi : d ∣ sylvNat^[i] x + 1 := Nat.gcd_dvd_left _ _
  have hdj : d ∣ sylvNat^[m + 1] x + 1 := Nat.gcd_dvd_right _ _
  have hmem : sylvNat^[i] x + 1 ∈
      (Finset.range (m + 1)).image (fun r => sylvNat^[r] x + 1) := by
    refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
    exact Finset.mem_range.mpr (by omega)
  have hdprod : d ∣ sylvNat^[m + 1] x := by
    rw [sylvNat_iterate_succ_eq_prod]
    refine Dvd.dvd.mul_left ?_ x
    exact hdi.trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega)))
  have : d ∣ 1 := (Nat.dvd_add_right hdprod).mp hdj
  exact Nat.eq_one_of_dvd_one this

/-! ## Part 3: every level is occupied at infinitely many primes — unconditionally

This is the qualitative half of what the Chebotarev density theorem would give for the
splitting field of `Ψ n`, and it needs no density theorem: the Euclid argument suffices,
because `Ψ n (0) = 1`. -/

/-- **The arboreal existence theorem.**  For every level `n` and every bound `B` there is a
prime `ℓ > B` at which level `n` is occupied. -/
theorem exists_large_prime_level_occupied (n B : ℕ) :
    ∃ ℓ : ℕ, Nat.Prime ℓ ∧ B < ℓ ∧ ∃ w : ZMod ℓ, (sylvWalk)^[n] w = -1 := by
  set x : ℕ := Nat.factorial B with hx
  have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero B)
  have hval : 1 ≤ sylvNat^[n] x := le_trans hx1 (le_sylvNat_iterate n x)
  set T : ℕ := sylvNat^[n] x + 1 with hT
  have hT2 : 2 ≤ T := by omega
  refine ⟨Nat.minFac T, Nat.minFac_prime (by omega), ?_, ?_⟩
  · -- the least factor exceeds `B`, since `T ≡ 1 (mod B !)`
    by_contra hle
    push Not at hle
    have hpos : 0 < Nat.minFac T := (Nat.minFac_prime (by omega : T ≠ 1)).pos
    have hdvdx : Nat.minFac T ∣ x := Nat.dvd_factorial hpos hle
    have hdvdit : Nat.minFac T ∣ sylvNat^[n] x := dvd_sylvNat_iterate n hdvdx
    have hdvdT : Nat.minFac T ∣ T := Nat.minFac_dvd T
    have hone : Nat.minFac T ∣ 1 := (Nat.dvd_add_right hdvdit).mp hdvdT
    have := (Nat.minFac_prime (show T ≠ 1 by omega)).two_le
    have := Nat.le_of_dvd one_pos hone
    omega
  · refine ⟨((x : ℕ) : ZMod (Nat.minFac T)), ?_⟩
    rw [← cast_sylvNat_iterate]
    have hdvd : Nat.minFac T ∣ sylvNat^[n] x + 1 := Nat.minFac_dvd T
    have : ((sylvNat^[n] x + 1 : ℕ) : ZMod (Nat.minFac T)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at this
    linear_combination this

/-- **Infinitely many primes occupy each level.** -/
theorem levelPrimes_infinite (n : ℕ) :
    {ℓ : ℕ | Nat.Prime ℓ ∧ ∃ w : ZMod ℓ, (sylvWalk)^[n] w = -1}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨B, hB⟩
  obtain ⟨ℓ, hℓ, hlt, hw⟩ := exists_large_prime_level_occupied n B
  exact absurd (hB (Set.mem_ofPred.mpr ⟨hℓ, hw⟩)) (by omega)

/-! ## Part 4: witnesses are free; smallness is everything -/

/-- The Sylvester tower is the `ℕ`-valued take-all walk, shifted by one. -/
theorem tower_eq_sylvNat (w k : ℕ) : tower (w + 1) k = sylvNat^[k] w + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [tower_succ, ih, Function.iterate_succ_apply']
      have h1 : sylvNat^[k] w + 1 - 1 = sylvNat^[k] w := by omega
      rw [h1]
      unfold sylvNat
      ring

/-- **The witness primes at level `k`.**  A prime `ℓ` puts the walk value at stage `N` on
level `k` exactly when it divides the `k`-th level value at `prod N`. -/
theorem level_witness_iff (N k ℓ : ℕ) :
    (sylvWalk)^[k] (walkZ ℓ N) = -1 ↔ ℓ ∣ sylvNat^[k] (prod N) + 1 := by
  have hcast : walkZ ℓ N = ((prod N : ℕ) : ZMod ℓ) := rfl
  rw [hcast, ← cast_sylvNat_iterate]
  constructor
  · intro h
    refine (ZMod.natCast_eq_zero_iff _ _).mp ?_
    push_cast
    linear_combination h
  · intro h
    have := (ZMod.natCast_eq_zero_iff (sylvNat^[k] (prod N) + 1) ℓ).mpr h
    push_cast at this
    linear_combination this

/-- **The reformulation.**  Witnesses always exist; (C∞) says one of them is proper. -/
theorem infinitelyManyComposite_iff_witness_proper :
    InfinitelyManyComposite ↔
      ∀ N : ℕ, ∃ k : ℕ,
        Nat.minFac (sylvNat^[k] (prod N) + 1) < sylvNat^[k] (prod N) + 1 := by
  rw [SylvesterTower.infinitelyManyComposite_iff_tower_composite]
  constructor
  · intro h N
    obtain ⟨k, hk⟩ := h N
    refine ⟨k, ?_⟩
    rw [tower_eq_sylvNat] at hk
    set T := sylvNat^[k] (prod N) + 1 with hT
    have hT2 : 2 ≤ T := by
      have := le_sylvNat_iterate k (prod N)
      have := prod_ge_two N
      omega
    rcases lt_or_eq_of_le (Nat.minFac_le (show 0 < T by omega)) with h' | h'
    · exact h'
    · exact absurd (by rw [← h']; exact Nat.minFac_prime (by omega)) hk
  · intro h N
    obtain ⟨k, hk⟩ := h N
    refine ⟨k, ?_⟩
    rw [tower_eq_sylvNat]
    intro hp
    rw [Nat.Prime.minFac_eq hp] at hk
    omega

/-- **On the branch the witness is the number itself.**  Perpetual primality from `N` says
exactly that the least prime factor of every level value is that value — a prime far
larger than `prod N`. -/
theorem witness_eq_self_of_perpetual {N : ℕ} (hpp : PerpetualPrimality N) (k : ℕ) :
    Nat.minFac (sylvNat^[k] (prod N) + 1) = sylvNat^[k] (prod N) + 1 := by
  have hprime : Nat.Prime (tower (prod N + 1) k) :=
    perpetualPrimality_iff_tower_prime.mp hpp k
  rw [tower_eq_sylvNat] at hprime
  exact Nat.Prime.minFac_eq hprime

/-- **Distinct levels give distinct witness primes.**  So each stage `N` carries an
infinite sequence of *pairwise distinct* primes, one per level, all free of charge.  (C∞)
asks only that one of them be smaller than the number it divides. -/
theorem minFac_level_injective (N : ℕ) :
    Function.Injective (fun k : ℕ => Nat.minFac (sylvNat^[k] (prod N) + 1)) := by
  intro i j hij
  by_contra hne
  have hlt : i < j ∨ j < i := by omega
  have key : ∀ a b : ℕ, a < b →
      Nat.minFac (sylvNat^[a] (prod N) + 1) ≠ Nat.minFac (sylvNat^[b] (prod N) + 1) := by
    intro a b hab heq
    have hTa : 2 ≤ sylvNat^[a] (prod N) + 1 := by
      have := le_sylvNat_iterate a (prod N); have := prod_ge_two N; omega
    have hTb : 2 ≤ sylvNat^[b] (prod N) + 1 := by
      have := le_sylvNat_iterate b (prod N); have := prod_ge_two N; omega
    have hpa : Nat.Prime (Nat.minFac (sylvNat^[a] (prod N) + 1)) :=
      Nat.minFac_prime (by omega)
    have hda : Nat.minFac (sylvNat^[a] (prod N) + 1) ∣ sylvNat^[a] (prod N) + 1 :=
      Nat.minFac_dvd _
    have hdb : Nat.minFac (sylvNat^[a] (prod N) + 1) ∣ sylvNat^[b] (prod N) + 1 := by
      rw [heq]; exact Nat.minFac_dvd _
    have hcop := coprime_level_values (prod N) hab
    have h1 : Nat.minFac (sylvNat^[a] (prod N) + 1) = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left hda (Nat.Coprime.coprime_dvd_right hdb hcop)) dvd_rfl
    exact hpa.ne_one h1
  rcases hlt with h | h
  · exact key i j h hij
  · exact key j i h hij.symm

/-! ## Part 5: what Chebotarev would add, and why it is not the gap

The Chebotarev density theorem, applied to the splitting field of the `n`-th level
polynomial and its arboreal Galois image, upgrades `levelPrimes_infinite` from "infinitely
many" to "a positive density of" primes.  It is stated here as a hypothesis because Mathlib
does not carry Chebotarev; nothing below uses it, which is the point. -/

open scoped Classical in
/-- **Arboreal Chebotarev**, stated: for each level, the primes occupying it have positive
density among all primes. -/
def ArborealChebotarev : Prop :=
  ∀ n : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ L : ℕ in Filter.atTop,
    c * (((Finset.range L).filter (fun ℓ => Nat.Prime ℓ)).card : ℝ)
      ≤ (((Finset.range L).filter
          (fun ℓ => Nat.Prime ℓ ∧ ∃ w : ZMod ℓ, (sylvWalk)^[n] w = -1)).card : ℝ)

/-! ## Landscape -/

/-- **The arboreal tower.**  The tree question splits cleanly into a free half and the
whole difficulty: witnesses at every level exist, at infinitely many primes,
unconditionally and without any density theorem; and (C∞) is exactly the statement that
some witness is a proper factor.  A density theorem over `ℓ` cannot supply the second half,
because the prime it must produce has to divide one specific integer. -/
theorem arboreal_tower_landscape :
    -- the tree's accumulator identity
    (∀ (R : Type) (_ : CommRing R) (w : R) (n : ℕ),
      (sylvWalk)^[n + 1] w = w * ∏ j ∈ Finset.range (n + 1), ((sylvWalk)^[j] w + 1)) ∧
    -- every level is occupied at infinitely many primes, unconditionally
    (∀ n B : ℕ, ∃ ℓ : ℕ, Nat.Prime ℓ ∧ B < ℓ ∧ ∃ w : ZMod ℓ, (sylvWalk)^[n] w = -1) ∧
    (∀ n : ℕ, {ℓ : ℕ | Nat.Prime ℓ ∧ ∃ w : ZMod ℓ, (sylvWalk)^[n] w = -1}.Infinite) ∧
    -- witnesses are exactly the prime factors of the level values
    (∀ N k ℓ : ℕ, ((sylvWalk)^[k] (walkZ ℓ N) = -1 ↔ ℓ ∣ sylvNat^[k] (prod N) + 1)) ∧
    -- and (C∞) is exactly the properness of some witness
    (InfinitelyManyComposite ↔
      ∀ N : ℕ, ∃ k : ℕ,
        Nat.minFac (sylvNat^[k] (prod N) + 1) < sylvNat^[k] (prod N) + 1) ∧
    (∀ N : ℕ, PerpetualPrimality N → ∀ k : ℕ,
      Nat.minFac (sylvNat^[k] (prod N) + 1) = sylvNat^[k] (prod N) + 1) ∧
    -- the level values are pairwise coprime, so the witnesses are pairwise distinct
    (∀ (x : ℕ) {i j : ℕ}, i < j →
      Nat.Coprime (sylvNat^[i] x + 1) (sylvNat^[j] x + 1)) ∧
    (∀ N : ℕ, Function.Injective
      (fun k : ℕ => Nat.minFac (sylvNat^[k] (prod N) + 1))) :=
  ⟨fun _ _ w n => sylvWalk_iterate_succ_eq_prod w n,
    exists_large_prime_level_occupied,
    levelPrimes_infinite,
    level_witness_iff,
    infinitelyManyComposite_iff_witness_proper,
    fun _ hpp k => witness_eq_self_of_perpetual hpp k,
    fun x _ _ h => coprime_level_values x h,
    minFac_level_injective⟩

end ArborealTower

end
