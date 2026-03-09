import EM.EquidistSelfAvoidance

/-!
# Integer Diophantine View: The T-Iteration

The Euclid-Mullin sequence can be viewed through a purely integer-level lens.
Define the **T-map** `T(n) = (n - 1) * minFac(n) + 1` on positive integers.
Then the EM sequence satisfies `T(prod(k) + 1) = prod(k+1) + 1`, and the
orbit `{T^k(3) : k in N}` is exactly `{prod(k) + 1 : k in N}`.

Mullin's Conjecture for odd primes is equivalent to: every odd prime divides
some element of the T-orbit starting from 3. (The prime 2 is excluded because
all T-orbit elements are odd.)

This file provides:
1. The T-map definition and its connection to EM accumulators
2. Orbit-level structural properties (strict monotonicity, coprimality)
3. GCD constraints on consecutive orbit elements
4. A "new prime factor" theorem: each step introduces a prime not in the product
5. MC reformulations in terms of the T-orbit

All results work at the integer (Nat) level -- no modular arithmetic needed.
-/

open Mullin Euclid

/-! ## Phase 1: T-map and orbit -/

section TMapDefinition

/-- The EM iteration on positive integers: `T(n) = (n - 1) * minFac(n) + 1`.
    When applied to `prod(k) + 1`, this yields `prod(k+1) + 1`.
    The iteration captures the entire EM dynamics at the integer level. -/
noncomputable def emIterationT (n : ℕ) : ℕ := (n - 1) * n.minFac + 1

/-- `Nat.minFac` agrees with `Euclid.minFac` on numbers >= 2.
    Both compute the smallest factor >= 2. -/
private theorem nat_minFac_eq_euclid_minFac (n : ℕ) (hn : 2 ≤ n) :
    n.minFac = Euclid.minFac n := by
  apply Nat.le_antisymm
  · exact Nat.minFac_le_of_dvd (two_le_minFac n hn) (minFac_dvd n hn)
  · exact minFac_min' n n.minFac hn (Nat.minFac_prime (by omega)).two_le
      (Nat.minFac_dvd n)

/-- **T applied to prod(n)+1 gives prod(n+1)+1.**
    This is the fundamental orbit recurrence: the T-map advances the
    shifted accumulator by one step of the EM sequence. -/
theorem emIterationT_prod_succ (n : ℕ) :
    emIterationT (prod n + 1) = prod (n + 1) + 1 := by
  unfold emIterationT
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  rw [Nat.add_sub_cancel, nat_minFac_eq_euclid_minFac _ hge, ← seq_succ, prod_succ, Nat.mul_comm]

/-- **The k-th iterate of T starting from 3 gives prod(k)+1.**
    Base: `T^0(3) = 3 = prod(0) + 1` (since `prod(0) = 2`).
    Step: `T^(k+1)(3) = T(T^k(3)) = T(prod(k)+1) = prod(k+1)+1`. -/
theorem emIterationT_iterate_eq (k : ℕ) :
    emIterationT^[k] 3 = prod k + 1 := by
  induction k with
  | zero => simp [prod_zero]
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply, ih]
    exact emIterationT_prod_succ k

/-- **Hitting iff T-orbit divisible**: `q | prod(n) + 1 ↔ q | T^n(3)`.
    Immediate from `emIterationT_iterate_eq`. -/
theorem hitting_iff_T_orbit (q n : ℕ) :
    q ∣ prod n + 1 ↔ q ∣ emIterationT^[n] 3 := by
  rw [emIterationT_iterate_eq]

end TMapDefinition

/-! ## Phase 2: T-orbit parity and MC reformulation -/

section ParityAndMC

/-- **All T-orbit elements are odd**: `prod(k)` is always even (divisible by 2),
    so `prod(k) + 1` is always odd. -/
theorem T_orbit_odd (k : ℕ) : ¬(2 ∣ emIterationT^[k] 3) := by
  rw [emIterationT_iterate_eq]
  intro h
  have h2 : seq 0 ∣ prod k := seq_dvd_prod 0 k (Nat.zero_le k)
  rw [seq_zero] at h2
  have hsub := Nat.dvd_sub h h2
  have : prod k + 1 - prod k = 1 := by omega
  rw [this] at hsub
  exact absurd hsub (by omega)

/-- **T-orbit elements are at least 3**: since `prod(k) >= 2`, we have
    `T^k(3) = prod(k) + 1 >= 3`. -/
theorem T_orbit_ge_three (k : ℕ) : 3 ≤ emIterationT^[k] 3 := by
  rw [emIterationT_iterate_eq]
  have := prod_ge_two k
  omega

/-- **MC implies T-orbit divisibility for odd primes**: if every prime appears
    in the EM sequence, then every odd prime divides some T-orbit element.
    For `q = seq(n+1)` (with `n >= 0`), we have `q | prod(n) + 1 = T^n(3)`.
    The prime 2 = seq(0) is excluded since all T-orbit elements are odd. -/
theorem mc_implies_orbit_divisible_of_odd
    (hmc : MullinConjecture) (q : ℕ) (hq : IsPrime q) (hq2 : q ≠ 2) :
    ∃ k, q ∣ emIterationT^[k] 3 := by
  obtain ⟨n, hn⟩ := hmc q hq
  have hn0 : n ≠ 0 := by
    intro h; subst h; rw [seq_zero] at hn; exact hq2 hn.symm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨m, (hitting_iff_T_orbit q m).mp (hn ▸ seq_dvd_succ_prod m)⟩

end ParityAndMC

/-! ## Phase 3: Structural properties of the T-orbit -/

section StructuralProperties

/-- **T-orbit is strictly increasing at each step**: `T^k(3) < T^(k+1)(3)`.
    Since `T^k(3) = prod(k) + 1` and products are strictly increasing. -/
theorem emIterationT_orbit_step_lt (k : ℕ) :
    emIterationT^[k] 3 < emIterationT^[k + 1] 3 := by
  simp only [emIterationT_iterate_eq]
  have := prod_strictMono (Nat.lt_add_one k)
  omega

/-- **T-orbit is strictly monotone**: `j < k -> T^j(3) < T^k(3)`. -/
theorem emIterationT_orbit_strictMono : StrictMono (fun k => emIterationT^[k] 3) := by
  intro j k hjk
  simp only [emIterationT_iterate_eq]
  have := prod_strictMono hjk
  omega

/-- **T-orbit elements are injective**: `T^j(3) = T^k(3) -> j = k`. -/
theorem emIterationT_orbit_injective :
    Function.Injective (fun k => emIterationT^[k] 3) :=
  emIterationT_orbit_strictMono.injective

/-- **T-orbit coprime to accumulator**: `Nat.Coprime (prod(n) + 1) (prod(n))`.
    Consecutive integers are always coprime. -/
theorem T_orbit_coprime_prod (n : ℕ) :
    Nat.Coprime (prod n + 1) (prod n) :=
  Nat.coprime_self_add_left.mpr (Nat.coprime_one_left_iff (prod n) |>.mpr trivial)

/-- **T-orbit coprime to accumulator (iterate form)**. -/
theorem T_orbit_iterate_coprime_prod (n : ℕ) :
    Nat.Coprime (emIterationT^[n] 3) (prod n) := by
  rw [emIterationT_iterate_eq]
  exact T_orbit_coprime_prod n

end StructuralProperties

/-! ## Phase 4: GCD of consecutive orbit elements -/

section GCDProperties

/-- **GCD of consecutive shifted accumulators divides seq(n+1) - 1**.
    If `d | prod(n) + 1` and `d | prod(n+1) + 1`, then since
    `prod(n+1) + 1 = prod(n) * seq(n+1) + 1` and
    `seq(n+1) * (prod(n) + 1) = prod(n) * seq(n+1) + seq(n+1)`, we get
    `d | seq(n+1) * (prod(n)+1) - (prod(n+1)+1) = seq(n+1) - 1`. -/
theorem T_orbit_consecutive_gcd_dvd (n : ℕ) :
    Nat.gcd (prod n + 1) (prod (n + 1) + 1) ∣ seq (n + 1) - 1 := by
  set d := Nat.gcd (prod n + 1) (prod (n + 1) + 1) with hd_def
  have hd1 : d ∣ prod n + 1 := Nat.gcd_dvd_left (prod n + 1) (prod (n + 1) + 1)
  have hd2 : d ∣ prod (n + 1) + 1 := Nat.gcd_dvd_right (prod n + 1) (prod (n + 1) + 1)
  rw [prod_succ] at hd2
  -- hd2 : d | prod n * seq(n+1) + 1
  -- hd1 : d | prod n + 1
  -- d | seq(n+1) * (prod n + 1) since d | prod n + 1
  have hd3 : d ∣ seq (n + 1) * (prod n + 1) := dvd_mul_of_dvd_right hd1 _
  -- seq(n+1) * (prod n + 1) = prod n * seq(n+1) + seq(n+1)
  -- So seq(n+1) * (prod n + 1) - (prod n * seq(n+1) + 1) = seq(n+1) - 1
  -- seq(n+1) * (prod n + 1) = prod n * seq(n+1) + seq(n+1) ≥ prod n * seq(n+1) + 1
  have hseq_ge : 1 ≤ seq (n + 1) := by have := (seq_isPrime (n + 1)).1; omega
  have hle : prod n * seq (n + 1) + 1 ≤ seq (n + 1) * (prod n + 1) := by
    have : seq (n + 1) * (prod n + 1) = prod n * seq (n + 1) + seq (n + 1) := by ring
    omega
  have hsub := Nat.dvd_sub hd3 hd2
  have heq : seq (n + 1) * (prod n + 1) - (prod n * seq (n + 1) + 1) = seq (n + 1) - 1 := by
    have : seq (n + 1) * (prod n + 1) = prod n * seq (n + 1) + seq (n + 1) := by ring
    omega
  rw [heq] at hsub
  exact hsub

/-- **GCD of consecutive T-orbit elements divides seq(n+1) - 1** (iterate form). -/
theorem T_orbit_iterate_gcd_dvd (n : ℕ) :
    Nat.gcd (emIterationT^[n] 3) (emIterationT^[n + 1] 3) ∣ seq (n + 1) - 1 := by
  simp only [emIterationT_iterate_eq]
  exact T_orbit_consecutive_gcd_dvd n

end GCDProperties

/-! ## Phase 5: New prime factor at each step -/

section NewPrimeFactor

/-- **seq(n+1) does not divide prod(n)**: the new sequence term is coprime
    to the running product. This is because `seq(n+1) | prod(n) + 1` and
    if also `seq(n+1) | prod(n)`, then `seq(n+1) | 1`, contradicting
    `seq(n+1) >= 2`. -/
theorem seq_succ_not_dvd_prod (n : ℕ) : ¬(seq (n + 1) ∣ prod n) := by
  intro h
  have h2 : seq (n + 1) ∣ prod n + 1 := seq_dvd_succ_prod n
  have h3 := Nat.dvd_sub h2 h
  simp at h3
  exact absurd h3 (by have := (seq_isPrime (n + 1)).1; omega)

/-- **Euclid.IsPrime implies Nat.Prime**: bridge between the two primality notions. -/
theorem isPrime_implies_natPrime {p : ℕ} (hp : IsPrime p) : Nat.Prime p := by
  have hge : 2 ≤ p := hp.1
  rw [Nat.prime_def_minFac]
  refine ⟨hge, ?_⟩
  -- Goal: p.minFac = p
  -- p.minFac ∣ p and p.minFac ≥ 2 (since p ≥ 2)
  -- By IsPrime: p.minFac = 1 ∨ p.minFac = p
  -- Since p.minFac ≥ 2, it must be p.minFac = p
  have hmf_dvd := Nat.minFac_dvd p
  rcases hp.2 p.minFac hmf_dvd with h | h
  · -- p.minFac = 1, contradiction with p.minFac ≥ 2
    have := (Nat.minFac_prime (show p ≠ 1 by omega)).two_le
    omega
  · exact h

/-- **seq values are Nat.Prime**: bridge for seq values. -/
theorem seq_natPrime (n : ℕ) : (seq n).Prime :=
  isPrime_implies_natPrime (seq_isPrime n)

/-- **New prime factor theorem**: `seq(k+1)` is prime, divides `prod(k) + 1`,
    and does NOT divide `prod(k)`. This means `seq(k+1)` is a genuinely new
    prime factor introduced at step k. -/
theorem T_orbit_new_prime_factor (k : ℕ) :
    (seq (k + 1)).Prime ∧ seq (k + 1) ∣ (prod k + 1) ∧ ¬(seq (k + 1) ∣ prod k) :=
  ⟨seq_natPrime (k + 1), seq_dvd_succ_prod k, seq_succ_not_dvd_prod k⟩

/-- **New prime factor (iterate form)**: `seq(k+1)` is prime, divides `T^k(3)`,
    and is coprime to `prod(k)`. -/
theorem T_orbit_new_prime_iterate (k : ℕ) :
    (seq (k + 1)).Prime ∧ seq (k + 1) ∣ emIterationT^[k] 3 ∧
      Nat.Coprime (seq (k + 1)) (prod k) := by
  refine ⟨seq_natPrime (k + 1), ?_, ?_⟩
  · rw [emIterationT_iterate_eq]
    exact seq_dvd_succ_prod k
  · exact (seq_natPrime (k + 1)).coprime_iff_not_dvd.mpr (seq_succ_not_dvd_prod k)

end NewPrimeFactor

/-! ## Phase 6: Divisibility and separation -/

section DivisibilityChain

/-- **seq(k+1) divides every later accumulator**: for `n >= k+1`, `seq(k+1) | prod(n)`.
    This is `seq_dvd_prod` with the appropriate indices. -/
theorem seq_succ_dvd_later_prod (k n : ℕ) (h : k + 1 ≤ n) :
    seq (k + 1) ∣ prod n :=
  seq_dvd_prod (k + 1) n h

/-- **Different orbit elements introduce distinct primes**: if `j ≠ k`, then
    `seq(j + 1) ≠ seq(k + 1)`. This is immediate from `seq_injective`. -/
theorem orbit_new_primes_distinct {j k : ℕ} (h : j ≠ k) :
    seq (j + 1) ≠ seq (k + 1) := by
  intro heq
  have := seq_injective _ _ heq
  omega

/-- **Earlier primes do not divide later orbit elements**: for `j < k`,
    `seq(j + 1)` does not divide `T^k(3) = prod(k) + 1`.
    This is because `seq(j+1) | prod(k)` (since `j+1 <= k`) and a prime
    that divides both `prod(k)` and `prod(k) + 1` would divide 1. -/
theorem orbit_early_prime_not_dvd_later (j k : ℕ) (h : j < k) :
    ¬(seq (j + 1) ∣ emIterationT^[k] 3) := by
  rw [emIterationT_iterate_eq]
  exact seq_not_dvd_prod_succ (by omega : j + 1 ≤ k)

end DivisibilityChain

/-! ## Phase 7: Integer-level cofactor properties -/

section CofactorProperties

/-- The Euclid cofactor at step n (local definition to avoid heavy imports):
    `emCofactor(n) = (prod(n) + 1) / seq(n+1)`. -/
private noncomputable def emCofactor (n : ℕ) : ℕ := (prod n + 1) / seq (n + 1)

/-- **Cofactor factorization**: `prod(n) + 1 = seq(n+1) * emCofactor(n)`. -/
private theorem emCofactor_mul (n : ℕ) :
    prod n + 1 = seq (n + 1) * emCofactor n := by
  rw [emCofactor, Nat.mul_div_cancel' (seq_dvd_succ_prod n)]

/-- **Cofactor is positive**: `emCofactor(n) >= 1`. -/
private theorem emCofactor_pos (n : ℕ) : 0 < emCofactor n := by
  rw [emCofactor]
  exact Nat.div_pos
    (Nat.le_of_dvd (by have := prod_ge_two n; omega) (seq_dvd_succ_prod n))
    (by have := (seq_isPrime (n + 1)).1; omega)

/-- **Cofactor identity at integer level**: `prod(n+1) + 1 = seq(n+1)^2 * cof(n) - seq(n+1) + 1`.

    Derivation: `prod(n) + 1 = seq(n+1) * cof(n)`, so `prod(n) = seq(n+1) * cof(n) - 1`.
    Then `prod(n+1) + 1 = prod(n) * seq(n+1) + 1 = (seq(n+1) * cof(n) - 1) * seq(n+1) + 1`
    `= seq(n+1)^2 * cof(n) - seq(n+1) + 1`. -/
theorem prod_succ_add_one_cofactor (n : ℕ) :
    prod (n + 1) + 1 = seq (n + 1) ^ 2 * emCofactor n - seq (n + 1) + 1 := by
  have hcof := emCofactor_mul n
  have hcof_pos := emCofactor_pos n
  have hseq_ge := (seq_isPrime (n + 1)).1
  -- Work in integers to avoid Nat subtraction issues
  -- Then convert back
  set s := seq (n + 1)
  set c := emCofactor n
  -- prod n + 1 = s * c, so prod n = s * c - 1
  have hprod : prod n = s * c - 1 := by omega
  -- prod(n+1) + 1 = prod(n) * s + 1 = (s*c - 1) * s + 1
  rw [prod_succ, hprod]
  -- Goal: (s * c - 1) * s + 1 = s ^ 2 * c - s + 1
  -- Both sides equal s^2*c - s + 1 in integers.
  -- In Nat: need s*c ≥ 1 (true since s ≥ 2 and c ≥ 1)
  -- and s^2*c ≥ s (true since s*c ≥ 1 implies s^2*c ≥ s)
  have hsc : 1 ≤ s * c := by
    calc 1 ≤ 2 * 1 := by omega
      _ ≤ s * c := Nat.mul_le_mul hseq_ge (by omega)
  have hsqc : s ≤ s ^ 2 * c := by
    calc s = s * 1 := (Nat.mul_one _).symm
      _ ≤ s * (s * c) := Nat.mul_le_mul_left s hsc
      _ = s ^ 2 * c := by ring
  -- Goal: (s * c - 1) * s + 1 = s ^ 2 * c - s + 1
  show (s * c - 1) * s + 1 = s ^ 2 * c - s + 1
  -- (s*c - 1) * s + s = s*c*s = s^2*c, and both sides + s give s^2*c + 1
  -- Equivalently: (s*c - 1)*s + 1 + s = s^2*c + 1 and s^2*c - s + 1 + s = s^2*c + 1
  -- So both sides + s = s^2*c + 1
  suffices h : (s * c - 1) * s + s = s ^ 2 * c by omega
  -- (s*c - 1)*s + s = (s*c - 1 + 1)*s = s*c*s = s^2*c
  have : s * c - 1 + 1 = s * c := by omega
  calc (s * c - 1) * s + s = (s * c - 1 + 1) * s := by ring
    _ = s * c * s := by rw [this]
    _ = s ^ 2 * c := by ring

/-- **T-map value in terms of cofactor**: `T(prod(n)+1) = seq(n+1)^2 * cof(n) - seq(n+1) + 1`. -/
theorem emIterationT_eq_cofactor (n : ℕ) :
    emIterationT (prod n + 1) =
      seq (n + 1) ^ 2 * emCofactor n - seq (n + 1) + 1 := by
  rw [emIterationT_prod_succ, prod_succ_add_one_cofactor]

end CofactorProperties
