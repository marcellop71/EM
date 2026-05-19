import EM.Stochastic.MixedWalk

/-!
# Perpetual Primality: Structural Constraints and Periodicity

## Overview

If the minFac walk produces P(n)+1 prime for ALL n >= N ("perpetual primality"),
then the walk follows the autonomous recurrence P(n+1) = P(n) * (P(n)+1) (since
minFac of a prime is itself), giving P(n+1) + 1 = P(n)^2 + P(n) + 1 = Phi_3(P(n)).
This file collects the structural consequences.

This file merges Part 23 of the original epsilon-random MC development with
Part 13 (Perpetual Primality Periodicity) of the original interpolation MC
development.

## Contents

* Part 23 (from EpsilonRandomMC): structural constraints --
  `perpetual_prime_recurrence`, `perpetual_prime_cyclotomic`,
  `mod3_one_divides_cyclotomic`, `cyclotomic_ge_seven`,
  `cyclotomic_not_prime_of_mod3_one`, `perpetual_prime_excludes_mod3_one`,
  `perpetual_primality_landscape`
* Part 13 (from InterpolationMC): periodicity mod q and orbit exclusions --
  `perpetual_prime_autonomous_mod`, `perpetual_prime_eventually_periodic`,
  `perpetual_prime_mod5_orbit`, `perpetual_prime_mod11_orbit`,
  `perpetual_prime_mod17_orbit`, `perpetual_prime_mod23_orbit`,
  `perpetual_primality_multi_exclusion`, `perpetual_primality_periodicity_landscape`
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 23: Perpetual Primality Structural Constraints

If the minFac walk produces P(n)+1 prime for ALL n ≥ N, then the walk follows
the recurrence P(n+1) = P(n) * (P(n)+1) (since minFac of a prime is itself),
giving P(n+1) + 1 = P(n)² + P(n) + 1.

This is the cyclotomic polynomial Phi_3 evaluated at P(n). We prove:
- The recurrence P → P*(P+1) holds under perpetual primality.
- P² + P + 1 ≡ 0 mod 3 whenever P ≡ 1 mod 3.
- Therefore, under perpetual primality, the walk can never reach P ≡ 1 mod 3
  (which would force P²+P+1 to be composite, contradicting perpetual primality). -/

section PerpetualPrimality

/-- Under perpetual primality (P+1 is prime at all steps from N onward),
    the walk follows P(n+1) = P(n) * (P(n)+1), because minFac of a prime is
    itself, so the factor chosen at each step is P(n)+1. -/
theorem perpetual_prime_recurrence (acc : ℕ) (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) (k : ℕ) :
    mixedWalkProd acc minFacMixed (N + k + 1) =
    mixedWalkProd acc minFacMixed (N + k) *
      (mixedWalkProd acc minFacMixed (N + k) + 1) := by
  rw [mixedWalkProd_succ]
  congr 1
  simp only [mixedWalkFactor, minFacMixed]
  exact (hperp k).minFac_eq

/-- Under perpetual primality, the "+1 recurrence" takes the form
    P(n+1) + 1 = P(n)² + P(n) + 1, which is Phi_3(P(n)). -/
theorem perpetual_prime_cyclotomic (acc : ℕ) (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) (k : ℕ) :
    mixedWalkProd acc minFacMixed (N + k + 1) + 1 =
    (mixedWalkProd acc minFacMixed (N + k)) ^ 2 +
      mixedWalkProd acc minFacMixed (N + k) + 1 := by
  rw [perpetual_prime_recurrence acc N hperp k]
  ring

/-- If P ≡ 1 mod 3 and P ≥ 2, then 3 divides P² + P + 1.

    Proof: P ≡ 1 mod 3 means P = 3k+1 for some k. Then
    P² + P + 1 = (3k+1)² + (3k+1) + 1 = 9k² + 6k + 1 + 3k + 1 + 1
    = 9k² + 9k + 3 = 3(3k² + 3k + 1). -/
theorem mod3_one_divides_cyclotomic (P : ℕ) (hmod : P % 3 = 1) :
    3 ∣ P ^ 2 + P + 1 := by
  obtain ⟨k, hk⟩ : ∃ k, P = 3 * k + 1 := by
    exact ⟨P / 3, by omega⟩
  rw [hk]; ring_nf
  -- 9*k^2 + 9*k + 3 = 3 * (3*k^2 + 3*k + 1)
  exact ⟨3 * k ^ 2 + 3 * k + 1, by ring⟩

/-- If P ≡ 1 mod 3 and P ≥ 2, then P² + P + 1 ≥ 7. -/
theorem cyclotomic_ge_seven (P : ℕ) (hP : 2 ≤ P) :
    7 ≤ P ^ 2 + P + 1 := by
  nlinarith [sq_nonneg P]

/-- If P ≡ 1 mod 3 and P ≥ 2, then P² + P + 1 is composite (divisible by 3 and ≥ 7,
    hence not 1, 2, or 3). -/
theorem cyclotomic_not_prime_of_mod3_one (P : ℕ) (hP : 2 ≤ P) (hmod : P % 3 = 1) :
    ¬(P ^ 2 + P + 1).Prime := by
  have hdvd := mod3_one_divides_cyclotomic P hmod
  have hge := cyclotomic_ge_seven P hP
  intro hprime
  have h3_or := hprime.eq_one_or_self_of_dvd 3 hdvd
  rcases h3_or with h1 | h3
  · omega
  · omega

/-- Under perpetual primality from step N, the walk at step N+k can never
    satisfy P ≡ 1 mod 3 (for k ≥ 1): if it did, P²+P+1 would be composite
    (by `cyclotomic_not_prime_of_mod3_one`), contradicting perpetual primality.

    This gives a structural constraint: the walk mod 3 stays in {0, 2} forever. -/
theorem perpetual_prime_excludes_mod3_one (acc : ℕ) (hacc : 2 ≤ acc) (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) (k : ℕ) :
    (mixedWalkProd acc minFacMixed (N + k)) % 3 ≠ 1 := by
  intro hmod
  have hge := mixedWalkProd_ge_two acc hacc minFacMixed (minFacMixed_valid acc) (N + k)
  have hcycl := perpetual_prime_cyclotomic acc N hperp k
  have hnp := cyclotomic_not_prime_of_mod3_one
    (mixedWalkProd acc minFacMixed (N + k)) hge hmod
  have hp := hperp (k + 1)
  rw [show N + (k + 1) = N + k + 1 from by omega] at hp
  rw [hcycl] at hp
  exact hnp hp

/-- **Perpetual primality landscape**: summary of structural constraints.

    1. perpetual_prime_recurrence -- P(n+1) = P(n) * (P(n)+1) under perpetual primality
    2. perpetual_prime_cyclotomic -- P(n+1)+1 = P(n)² + P(n) + 1 (Phi_3 recurrence)
    3. mod3_one_divides_cyclotomic -- P ≡ 1 mod 3 ⇒ 3 | P²+P+1
    4. cyclotomic_not_prime_of_mod3_one -- P ≡ 1 mod 3, P ≥ 2 ⇒ P²+P+1 composite
    5. perpetual_prime_excludes_mod3_one -- perpetual primality ⇒ walk never ≡ 1 mod 3
    6. not_prime_quotient_ge_two -- composite P+1 ⇒ (P+1)/minFac ≥ 2
    7. not_prime_exists_quotient_factor -- composite P+1 ⇒ ∃ prime factor ≥ minFac -/
theorem perpetual_primality_landscape (acc : ℕ) (hacc : 2 ≤ acc) (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) :
    -- 1. Recurrence holds
    (∀ k, mixedWalkProd acc minFacMixed (N + k + 1) =
      mixedWalkProd acc minFacMixed (N + k) *
        (mixedWalkProd acc minFacMixed (N + k) + 1))
    ∧
    -- 2. Cyclotomic form
    (∀ k, mixedWalkProd acc minFacMixed (N + k + 1) + 1 =
      (mixedWalkProd acc minFacMixed (N + k)) ^ 2 +
        mixedWalkProd acc minFacMixed (N + k) + 1)
    ∧
    -- 3. Walk never ≡ 1 mod 3
    (∀ k, (mixedWalkProd acc minFacMixed (N + k)) % 3 ≠ 1)
    ∧
    -- 4. Phi_3 at P ≡ 1 mod 3 is composite
    (∀ P, 2 ≤ P → P % 3 = 1 → ¬(P ^ 2 + P + 1).Prime) :=
  ⟨perpetual_prime_recurrence acc N hperp,
   perpetual_prime_cyclotomic acc N hperp,
   perpetual_prime_excludes_mod3_one acc hacc N hperp,
   fun P hP hmod => cyclotomic_not_prime_of_mod3_one P hP hmod⟩

end PerpetualPrimality

-- ============================================================================
-- The following section came from `InterpolationMC.lean` (Part 13:
-- Perpetual Primality Periodicity), merged here during the 2026-08 split.
-- ============================================================================

/-! ## Part 13: Perpetual Primality Periodicity

Under perpetual primality (all P(n)+1 prime from some step onward), the walk mod q
follows the autonomous map w -> w*(w+1) on the finite set ZMod q. By pigeonhole,
the walk is eventually periodic mod q. For specific small q (e.g., q = 5), the orbit
can be computed and shown to avoid -1, providing structural obstructions to hitting. -/

section PerpetualPrimalityPeriodicity

/-- Under perpetual primality, the walk mod q follows an autonomous recurrence:
    w(n+1) = w(n) * (w(n) + 1) mod q. This is because P(n+1) = P(n) * (P(n)+1)
    under perpetual primality (minFac of a prime is itself). -/
theorem perpetual_prime_autonomous_mod (acc : ℕ) (_hacc : 2 ≤ acc) (q : ℕ)
    (N : ℕ) (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) (k : ℕ) :
    (mixedWalkProd acc minFacMixed (N + k + 1) : ZMod q) =
    (mixedWalkProd acc minFacMixed (N + k) : ZMod q) *
    ((mixedWalkProd acc minFacMixed (N + k) : ZMod q) + 1) := by
  rw [perpetual_prime_recurrence acc N hperp k]
  push_cast
  ring

/-- Helper: the autonomous mod-q function applied to a walk value gives the next. -/
private theorem perpetual_prime_step_eq (acc : ℕ) (hacc : 2 ≤ acc) (q : ℕ)
    (N : ℕ) (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime)
    (i j : ℕ) (heq : (mixedWalkProd acc minFacMixed (N + i) : ZMod q) =
                      (mixedWalkProd acc minFacMixed (N + j) : ZMod q)) :
    (mixedWalkProd acc minFacMixed (N + i + 1) : ZMod q) =
    (mixedWalkProd acc minFacMixed (N + j + 1) : ZMod q) := by
  rw [perpetual_prime_autonomous_mod acc hacc q N hperp i,
      perpetual_prime_autonomous_mod acc hacc q N hperp j, heq]

/-- Under perpetual primality, the walk is eventually periodic mod q.
    Since the map w -> w*(w+1) is autonomous on the finite set ZMod q,
    pigeonhole gives a collision, and the autonomous recurrence propagates periodicity. -/
theorem perpetual_prime_eventually_periodic (acc : ℕ) (hacc : 2 ≤ acc) (q : ℕ) (hq : 2 ≤ q)
    (N : ℕ) (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) :
    ∃ n₀ T : ℕ, N ≤ n₀ ∧ 0 < T ∧
    ∀ j, (mixedWalkProd acc minFacMixed (n₀ + j + T) : ZMod q) =
         (mixedWalkProd acc minFacMixed (n₀ + j) : ZMod q) := by
  -- Define the sequence mod q on Fin (q+1) → ZMod q
  have : NeZero q := ⟨by omega⟩
  let f : Fin (q + 1) → ZMod q := fun i => (mixedWalkProd acc minFacMixed (N + i.val) : ZMod q)
  -- Pigeonhole: q+1 > q = card (ZMod q), so f is not injective
  have hcard : Fintype.card (ZMod q) < Fintype.card (Fin (q + 1)) := by
    rw [ZMod.card q, Fintype.card_fin]
    omega
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  -- Extract i < j with f(i) = f(j) using WLOG a < b or b < a
  have hval_ne : a.val ≠ b.val := Fin.val_ne_of_ne hab
  -- Get i, j with i < j
  obtain ⟨i, j, hij, hfij⟩ : ∃ i j : ℕ, i < j ∧
      (mixedWalkProd acc minFacMixed (N + i) : ZMod q) =
      (mixedWalkProd acc minFacMixed (N + j) : ZMod q) := by
    rcases Nat.lt_or_gt_of_ne hval_ne with h | h
    · exact ⟨a.val, b.val, h, hfab⟩
    · exact ⟨b.val, a.val, h, hfab.symm⟩
  -- Set n₀ = N + i, T = j - i
  refine ⟨N + i, j - i, by omega, by omega, ?_⟩
  -- Prove periodicity by induction on j
  intro m
  induction m with
  | zero =>
    simp only [Nat.add_zero]
    have e : N + i + (j - i) = N + j := by omega
    rw [e]; exact hfij.symm
  | succ m ih =>
    -- Goal: f(n₀ + (m+1) + T) = f(n₀ + (m+1))
    -- By autonomous map: f(n₀ + m + T + 1) = f(n₀ + m + T) * (f(n₀ + m + T) + 1)
    -- and f(n₀ + m + 1) = f(n₀ + m) * (f(n₀ + m) + 1)
    -- By IH: f(n₀ + m + T) = f(n₀ + m), so they're equal.
    have e1 : N + i + (m + 1) + (j - i) = N + (i + m + (j - i)) + 1 := by omega
    have e2 : N + i + (m + 1) = N + (i + m) + 1 := by omega
    have e3 : N + i + m + (j - i) = N + (i + m + (j - i)) := by omega
    have e4 : N + i + m = N + (i + m) := by omega
    show (mixedWalkProd acc minFacMixed (N + i + (m + 1) + (j - i)) : ZMod q) =
         (mixedWalkProd acc minFacMixed (N + i + (m + 1)) : ZMod q)
    rw [e1, e2]
    rw [perpetual_prime_autonomous_mod acc hacc q N hperp (i + m + (j - i)),
        perpetual_prime_autonomous_mod acc hacc q N hperp (i + m)]
    rw [show N + (i + m + (j - i)) = N + i + m + (j - i) from by omega,
        show N + (i + m) = N + i + m from by omega]
    rw [ih]

/-- The autonomous map on ZMod 5: w * (w + 1). We show it maps 1 -> 2 and 2 -> 1. -/
private theorem autonomous_map_mod5_one :
    (1 : ZMod 5) * ((1 : ZMod 5) + 1) = 2 := by decide

private theorem autonomous_map_mod5_two :
    (2 : ZMod 5) * ((2 : ZMod 5) + 1) = 1 := by decide

/-- Under perpetual primality from acc = 2, if the walk position mod 5 is 1 or 2,
    then it stays in {1, 2} forever, never reaching -1 = 4 mod 5. -/
theorem perpetual_prime_mod5_orbit (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
    (hN_mod5 : (mixedWalkProd 2 minFacMixed N : ZMod 5) = 2 ∨
               (mixedWalkProd 2 minFacMixed N : ZMod 5) = 1) (k : ℕ) :
    (mixedWalkProd 2 minFacMixed (N + k) : ZMod 5) ≠ -1 := by
  -- First show that the walk stays in {1, 2} by induction on k
  suffices h : (mixedWalkProd 2 minFacMixed (N + k) : ZMod 5) = 2 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 5) = 1 by
    -- Since -1 = 4 in ZMod 5, and 1 ≠ 4, 2 ≠ 4, done
    rcases h with h | h <;> simp [h] <;> decide
  induction k with
  | zero => simpa using hN_mod5
  | succ k ih =>
    have hstep := perpetual_prime_autonomous_mod 2 (by omega) 5 N hperp k
    have e : N + (k + 1) = N + k + 1 := by omega
    rw [show (mixedWalkProd 2 minFacMixed (N + (k + 1)) : ZMod 5) =
        (mixedWalkProd 2 minFacMixed (N + k + 1) : ZMod 5) from by rw [e]]
    rw [hstep]
    rcases ih with h | h <;> rw [h]
    · -- w = 2: 2 * (2 + 1) = 6 = 1 mod 5
      right; decide
    · -- w = 1: 1 * (1 + 1) = 2 mod 5
      left; decide

-- === Mod-11 orbit exclusion ===

/-- The autonomous map on ZMod 11: 2 * 3 = 6 mod 11. -/
private theorem autonomous_map_mod11_two :
    (2 : ZMod 11) * ((2 : ZMod 11) + 1) = 6 := by decide

/-- The autonomous map on ZMod 11: 6 * 7 = 42 = 9 mod 11. -/
private theorem autonomous_map_mod11_six :
    (6 : ZMod 11) * ((6 : ZMod 11) + 1) = 9 := by decide

/-- The autonomous map on ZMod 11: 9 * 10 = 90 = 2 mod 11. -/
private theorem autonomous_map_mod11_nine :
    (9 : ZMod 11) * ((9 : ZMod 11) + 1) = 2 := by decide

/-- Under perpetual primality from acc = 2, if the walk position mod 11 is in {2, 6, 9},
    then it stays in {2, 6, 9} forever, never reaching -1 = 10 mod 11.
    The orbit is a 3-cycle: 2 -> 6 -> 9 -> 2. -/
theorem perpetual_prime_mod11_orbit (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
    (hN_mod11 : (mixedWalkProd 2 minFacMixed N : ZMod 11) = 2 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 11) = 6 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 11) = 9) (k : ℕ) :
    (mixedWalkProd 2 minFacMixed (N + k) : ZMod 11) ≠ -1 := by
  suffices h : (mixedWalkProd 2 minFacMixed (N + k) : ZMod 11) = 2 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 11) = 6 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 11) = 9 by
    rcases h with h | h | h <;> simp [h] <;> decide
  induction k with
  | zero => simpa using hN_mod11
  | succ k ih =>
    have hstep := perpetual_prime_autonomous_mod 2 (by omega) 11 N hperp k
    have e : N + (k + 1) = N + k + 1 := by omega
    rw [show (mixedWalkProd 2 minFacMixed (N + (k + 1)) : ZMod 11) =
        (mixedWalkProd 2 minFacMixed (N + k + 1) : ZMod 11) from by rw [e]]
    rw [hstep]
    rcases ih with h | h | h <;> rw [h]
    · -- w = 2: 2 * 3 = 6 mod 11
      right; left; decide
    · -- w = 6: 6 * 7 = 9 mod 11
      right; right; decide
    · -- w = 9: 9 * 10 = 2 mod 11
      left; decide

-- === Mod-17 orbit exclusion ===

/-- The autonomous map on ZMod 17: 2 * 3 = 6 mod 17. -/
private theorem autonomous_map_mod17_two :
    (2 : ZMod 17) * ((2 : ZMod 17) + 1) = 6 := by decide

/-- The autonomous map on ZMod 17: 6 * 7 = 42 = 8 mod 17. -/
private theorem autonomous_map_mod17_six :
    (6 : ZMod 17) * ((6 : ZMod 17) + 1) = 8 := by decide

/-- The autonomous map on ZMod 17: 8 * 9 = 72 = 4 mod 17. -/
private theorem autonomous_map_mod17_eight :
    (8 : ZMod 17) * ((8 : ZMod 17) + 1) = 4 := by decide

/-- The autonomous map on ZMod 17: 4 * 5 = 20 = 3 mod 17. -/
private theorem autonomous_map_mod17_four :
    (4 : ZMod 17) * ((4 : ZMod 17) + 1) = 3 := by decide

/-- The autonomous map on ZMod 17: 3 * 4 = 12 mod 17. -/
private theorem autonomous_map_mod17_three :
    (3 : ZMod 17) * ((3 : ZMod 17) + 1) = 12 := by decide

/-- The autonomous map on ZMod 17: 12 * 13 = 156 = 3 mod 17. -/
private theorem autonomous_map_mod17_twelve :
    (12 : ZMod 17) * ((12 : ZMod 17) + 1) = 3 := by decide

/-- Under perpetual primality from acc = 2, if the walk position mod 17 is in
    {2, 3, 4, 6, 8, 12}, then it stays in that set forever, never reaching -1 = 16 mod 17.
    The dynamics: 2 -> 6 -> 8 -> 4 -> 3 -> 12 -> 3 (tail + 2-cycle {3, 12}). -/
theorem perpetual_prime_mod17_orbit (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
    (hN_mod17 : (mixedWalkProd 2 minFacMixed N : ZMod 17) = 2 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 17) = 6 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 17) = 8 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 17) = 4 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 17) = 3 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 17) = 12) (k : ℕ) :
    (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) ≠ -1 := by
  suffices h : (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) = 2 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) = 6 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) = 8 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) = 4 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) = 3 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) = 12 by
    rcases h with h | h | h | h | h | h <;> simp [h] <;> decide
  induction k with
  | zero => simpa using hN_mod17
  | succ k ih =>
    have hstep := perpetual_prime_autonomous_mod 2 (by omega) 17 N hperp k
    have e : N + (k + 1) = N + k + 1 := by omega
    rw [show (mixedWalkProd 2 minFacMixed (N + (k + 1)) : ZMod 17) =
        (mixedWalkProd 2 minFacMixed (N + k + 1) : ZMod 17) from by rw [e]]
    rw [hstep]
    rcases ih with h | h | h | h | h | h <;> rw [h]
    · -- w = 2: 2 * 3 = 6 mod 17
      right; left; decide
    · -- w = 6: 6 * 7 = 8 mod 17
      right; right; left; decide
    · -- w = 8: 8 * 9 = 4 mod 17
      right; right; right; left; decide
    · -- w = 4: 4 * 5 = 3 mod 17
      right; right; right; right; left; decide
    · -- w = 3: 3 * 4 = 12 mod 17
      right; right; right; right; right; decide
    · -- w = 12: 12 * 13 = 3 mod 17
      right; right; right; right; left; decide

-- === Mod-23 orbit exclusion ===

/-- The autonomous map on ZMod 23: 2 * 3 = 6 mod 23. -/
private theorem autonomous_map_mod23_two :
    (2 : ZMod 23) * ((2 : ZMod 23) + 1) = 6 := by decide

/-- The autonomous map on ZMod 23: 6 * 7 = 42 = 19 mod 23. -/
private theorem autonomous_map_mod23_six :
    (6 : ZMod 23) * ((6 : ZMod 23) + 1) = 19 := by decide

/-- The autonomous map on ZMod 23: 19 * 20 = 380 = 12 mod 23. -/
private theorem autonomous_map_mod23_nineteen :
    (19 : ZMod 23) * ((19 : ZMod 23) + 1) = 12 := by decide

/-- The autonomous map on ZMod 23: 12 * 13 = 156 = 18 mod 23. -/
private theorem autonomous_map_mod23_twelve :
    (12 : ZMod 23) * ((12 : ZMod 23) + 1) = 18 := by decide

/-- The autonomous map on ZMod 23: 18 * 19 = 342 = 20 mod 23. -/
private theorem autonomous_map_mod23_eighteen :
    (18 : ZMod 23) * ((18 : ZMod 23) + 1) = 20 := by decide

/-- The autonomous map on ZMod 23: 20 * 21 = 420 = 6 mod 23. -/
private theorem autonomous_map_mod23_twenty :
    (20 : ZMod 23) * ((20 : ZMod 23) + 1) = 6 := by decide

/-- Under perpetual primality from acc = 2, if the walk position mod 23 is in
    {2, 6, 12, 18, 19, 20}, then it stays in that set forever, never reaching -1 = 22 mod 23.
    The dynamics: 2 -> 6 -> 19 -> 12 -> 18 -> 20 -> 6 (tail {2} + 5-cycle {6,19,12,18,20}). -/
theorem perpetual_prime_mod23_orbit (N : ℕ)
    (hperp : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
    (hN_mod23 : (mixedWalkProd 2 minFacMixed N : ZMod 23) = 2 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 23) = 6 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 23) = 19 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 23) = 12 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 23) = 18 ∨
                (mixedWalkProd 2 minFacMixed N : ZMod 23) = 20) (k : ℕ) :
    (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) ≠ -1 := by
  suffices h : (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) = 2 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) = 6 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) = 19 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) = 12 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) = 18 ∨
               (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) = 20 by
    rcases h with h | h | h | h | h | h <;> simp [h] <;> decide
  induction k with
  | zero => simpa using hN_mod23
  | succ k ih =>
    have hstep := perpetual_prime_autonomous_mod 2 (by omega) 23 N hperp k
    have e : N + (k + 1) = N + k + 1 := by omega
    rw [show (mixedWalkProd 2 minFacMixed (N + (k + 1)) : ZMod 23) =
        (mixedWalkProd 2 minFacMixed (N + k + 1) : ZMod 23) from by rw [e]]
    rw [hstep]
    rcases ih with h | h | h | h | h | h <;> rw [h]
    · -- w = 2: 2 * 3 = 6 mod 23
      right; left; decide
    · -- w = 6: 6 * 7 = 19 mod 23
      right; right; left; decide
    · -- w = 19: 19 * 20 = 12 mod 23
      right; right; right; left; decide
    · -- w = 12: 12 * 13 = 18 mod 23
      right; right; right; right; left; decide
    · -- w = 18: 18 * 19 = 20 mod 23
      right; right; right; right; right; decide
    · -- w = 20: 20 * 21 = 6 mod 23
      right; left; decide

-- === Multi-prime perpetual primality exclusion landscape ===

/-- **Multi-prime perpetual primality exclusion landscape**:
    Under perpetual primality, the walk simultaneously avoids -1 mod 5, 11, 17, and 23.
    For each prime q in {5, 11, 17, 23}, the autonomous map w -> w*(w+1) on ZMod q
    has a closed orbit (starting from w = 2) that does not contain -1.
    This provides structural obstructions: these primes CANNOT appear in the EM sequence
    under perpetual primality (from the appropriate initial condition). -/
theorem perpetual_primality_multi_exclusion :
    -- 1. Mod 5: orbit {1, 2}, -1 = 4 avoided
    (∀ N (_ : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
      (_ : (mixedWalkProd 2 minFacMixed N : ZMod 5) = 2 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 5) = 1),
      ∀ k, (mixedWalkProd 2 minFacMixed (N + k) : ZMod 5) ≠ -1)
    ∧
    -- 2. Mod 11: orbit {2, 6, 9}, -1 = 10 avoided
    (∀ N (_ : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
      (_ : (mixedWalkProd 2 minFacMixed N : ZMod 11) = 2 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 11) = 6 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 11) = 9),
      ∀ k, (mixedWalkProd 2 minFacMixed (N + k) : ZMod 11) ≠ -1)
    ∧
    -- 3. Mod 17: orbit {2, 3, 4, 6, 8, 12}, -1 = 16 avoided
    (∀ N (_ : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
      (_ : (mixedWalkProd 2 minFacMixed N : ZMod 17) = 2 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 17) = 6 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 17) = 8 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 17) = 4 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 17) = 3 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 17) = 12),
      ∀ k, (mixedWalkProd 2 minFacMixed (N + k) : ZMod 17) ≠ -1)
    ∧
    -- 4. Mod 23: orbit {2, 6, 12, 18, 19, 20}, -1 = 22 avoided
    (∀ N (_ : ∀ k, (mixedWalkProd 2 minFacMixed (N + k) + 1).Prime)
      (_ : (mixedWalkProd 2 minFacMixed N : ZMod 23) = 2 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 23) = 6 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 23) = 19 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 23) = 12 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 23) = 18 ∨
           (mixedWalkProd 2 minFacMixed N : ZMod 23) = 20),
      ∀ k, (mixedWalkProd 2 minFacMixed (N + k) : ZMod 23) ≠ -1) :=
  ⟨perpetual_prime_mod5_orbit, perpetual_prime_mod11_orbit,
   perpetual_prime_mod17_orbit, perpetual_prime_mod23_orbit⟩

/-- **Perpetual primality periodicity landscape**: structural consequences of perpetual primality
    for the walk mod q.

    1. Autonomous recurrence: w(n+1) = w(n) * (w(n) + 1) mod q
    2. Eventually periodic mod q (pigeonhole + autonomous propagation)
    3. Mod-3 exclusion (walk never = 1 mod 3, from EpsilonRandomMC)
    4. Multi-prime orbit exclusion for q in {5, 11, 17, 23} -/
theorem perpetual_primality_periodicity_landscape (acc : ℕ) (hacc : 2 ≤ acc) (q : ℕ) (hq : 2 ≤ q)
    (N : ℕ) (hperp : ∀ k, (mixedWalkProd acc minFacMixed (N + k) + 1).Prime) :
    -- 1. Autonomous recurrence mod q
    (∀ k, (mixedWalkProd acc minFacMixed (N + k + 1) : ZMod q) =
      (mixedWalkProd acc minFacMixed (N + k) : ZMod q) *
      ((mixedWalkProd acc minFacMixed (N + k) : ZMod q) + 1))
    ∧
    -- 2. Eventually periodic mod q
    (∃ n₀ T : ℕ, N ≤ n₀ ∧ 0 < T ∧
      ∀ j, (mixedWalkProd acc minFacMixed (n₀ + j + T) : ZMod q) =
           (mixedWalkProd acc minFacMixed (n₀ + j) : ZMod q))
    ∧
    -- 3. Walk never = 1 mod 3
    (∀ k, (mixedWalkProd acc minFacMixed (N + k)) % 3 ≠ 1) :=
  ⟨perpetual_prime_autonomous_mod acc hacc q N hperp,
   perpetual_prime_eventually_periodic acc hacc q hq N hperp,
   perpetual_prime_excludes_mod3_one acc hacc N hperp⟩

end PerpetualPrimalityPeriodicity
