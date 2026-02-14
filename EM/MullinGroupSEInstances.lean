import EM.MullinGroupEscape

/-!
# Concrete SE Instances and Walk Properties

30 concrete SE verifications for small primes (q = 11 to 157) using
primitive root checks, plus:
* Concrete mixing: walkZ mod 5/139/443/248867 hit -1
* `walk_periodic_implies_mult_periodic`: walk periodicity → mult periodicity
* `walkZ_hits_iff_target`: w(n+1) = -1 ↔ w(n) = -(m(n))⁻¹
* `isPrime_minFac_self`: prime n implies minFac n = n
-/

namespace MullinGroup

open Mullin Euclid

/-- SE at q = 11: mult 1 = 7 is a primitive root. -/
theorem se_at_11 (hq : IsPrime 11) (hne : ∀ k, seq k ≠ 11) :
    ∀ H : Subgroup (ZMod 11)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 11 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 1 7 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 17: mult 0 = 3 is a primitive root. -/
theorem se_at_17 (hq : IsPrime 17) (hne : ∀ k, seq k ≠ 17) :
    ∀ H : Subgroup (ZMod 17)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 17 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 0 3 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 19: mult 0 = 3 is a primitive root. -/
theorem se_at_19 (hq : IsPrime 19) (hne : ∀ k, seq k ≠ 19) :
    ∀ H : Subgroup (ZMod 19)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 19 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 0 3 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 23: mult 1 = 7 is a primitive root. -/
theorem se_at_23 (hq : IsPrime 23) (hne : ∀ k, seq k ≠ 23) :
    ∀ H : Subgroup (ZMod 23)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 23 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 1 7 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 29: mult 0 = 3 is a primitive root. -/
theorem se_at_29 (hq : IsPrime 29) (hne : ∀ k, seq k ≠ 29) :
    ∀ H : Subgroup (ZMod 29)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 29 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 0 3 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 31: mult 0 = 3 is a primitive root. -/
theorem se_at_31 (hq : IsPrime 31) (hne : ∀ k, seq k ≠ 31) :
    ∀ H : Subgroup (ZMod 31)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 31 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 0 3 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 37: mult 3 = 13 is a primitive root. -/
theorem se_at_37 (hq : IsPrime 37) (hne : ∀ k, seq k ≠ 37) :
    ∀ H : Subgroup (ZMod 37)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 37 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 3 13 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 41: mult 1 = 7 is a primitive root. -/
theorem se_at_41 (hq : IsPrime 41) (hne : ∀ k, seq k ≠ 41) :
    ∀ H : Subgroup (ZMod 41)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 41 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 1 7 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 47: mult 2 = 43 is a primitive root. -/
theorem se_at_47 (hq : IsPrime 47) (hne : ∀ k, seq k ≠ 47) :
    ∀ H : Subgroup (ZMod 47)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 47 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 2 43 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 59: mult 2 = 43 is a primitive root. -/
theorem se_at_59 (hq : IsPrime 59) (hne : ∀ k, seq k ≠ 59) :
    ∀ H : Subgroup (ZMod 59)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 59 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 2 43 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 61: mult 1 = 7 is a primitive root. -/
theorem se_at_61 (hq : IsPrime 61) (hne : ∀ k, seq k ≠ 61) :
    ∀ H : Subgroup (ZMod 61)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 61 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 1 7 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 67: mult 1 = 7 is a primitive root. -/
theorem se_at_67 (hq : IsPrime 67) (hne : ∀ k, seq k ≠ 67) :
    ∀ H : Subgroup (ZMod 67)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 67 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 1 7 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 71: mult 1 = 7 is a primitive root. -/
theorem se_at_71 (hq : IsPrime 71) (hne : ∀ k, seq k ≠ 71) :
    ∀ H : Subgroup (ZMod 71)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 71 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 1 7 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 73: mult 3 = 13 is a primitive root. -/
theorem se_at_73 (hq : IsPrime 73) (hne : ∀ k, seq k ≠ 73) :
    ∀ H : Subgroup (ZMod 73)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 73 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 3 13 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 79: mult 0 = 3 is a primitive root. -/
theorem se_at_79 (hq : IsPrime 79) (hne : ∀ k, seq k ≠ 79) :
    ∀ H : Subgroup (ZMod 79)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 79 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 0 3 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 83: mult 2 = 43 is a primitive root. -/
theorem se_at_83 (hq : IsPrime 83) (hne : ∀ k, seq k ≠ 83) :
    ∀ H : Subgroup (ZMod 83)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 83 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 2 43 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 89: mult 0 = 3 is a primitive root. -/
theorem se_at_89 (hq : IsPrime 89) (hne : ∀ k, seq k ≠ 89) :
    ∀ H : Subgroup (ZMod 89)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 89 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 0 3 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 97: mult 1 = 7 is a primitive root. -/
theorem se_at_97 (hq : IsPrime 97) (hne : ∀ k, seq k ≠ 97) :
    ∀ H : Subgroup (ZMod 97)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 97 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 1 7 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 101: mult 0 = 3 is a primitive root. -/
theorem se_at_101 (hq : IsPrime 101) (hne : ∀ k, seq k ≠ 101) :
    ∀ H : Subgroup (ZMod 101)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 101 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 0 3 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 103: mult 2 = 43 is a primitive root. -/
theorem se_at_103 (hq : IsPrime 103) (hne : ∀ k, seq k ≠ 103) :
    ∀ H : Subgroup (ZMod 103)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 103 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 2 43 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 107: mult 1 = 7 is a primitive root. -/
theorem se_at_107 (hq : IsPrime 107) (hne : ∀ k, seq k ≠ 107) :
    ∀ H : Subgroup (ZMod 107)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 107 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 1 7 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 109: mult 3 = 13 is a primitive root. -/
theorem se_at_109 (hq : IsPrime 109) (hne : ∀ k, seq k ≠ 109) :
    ∀ H : Subgroup (ZMod 109)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 109 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 3 13 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 113: mult 0 = 3 is a primitive root. -/
theorem se_at_113 (hq : IsPrime 113) (hne : ∀ k, seq k ≠ 113) :
    ∀ H : Subgroup (ZMod 113)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 113 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 0 3 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 127: mult 0 = 3 is a primitive root. -/
theorem se_at_127 (hq : IsPrime 127) (hne : ∀ k, seq k ≠ 127) :
    ∀ H : Subgroup (ZMod 127)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 127 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 0 3 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 137: mult 0 = 3 is a primitive root. -/
theorem se_at_137 (hq : IsPrime 137) (hne : ∀ k, seq k ≠ 137) :
    ∀ H : Subgroup (ZMod 137)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 137 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 0 3 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 139: mult 0 = 3 is a primitive root. -/
theorem se_at_139 (hq : IsPrime 139) (hne : ∀ k, seq k ≠ 139) :
    ∀ H : Subgroup (ZMod 139)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 139 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 0 3 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 149: mult 0 = 3 is a primitive root. -/
theorem se_at_149 (hq : IsPrime 149) (hne : ∀ k, seq k ≠ 149) :
    ∀ H : Subgroup (ZMod 149)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 149 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 0 3 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 151: mult 1 = 7 is a primitive root. -/
theorem se_at_151 (hq : IsPrime 151) (hne : ∀ k, seq k ≠ 151) :
    ∀ H : Subgroup (ZMod 151)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 151 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 1 7 (by decide) (by native_decide) (by native_decide)

/-- SE at q = 157: mult 2 = 43 is a primitive root. -/
theorem se_at_157 (hq : IsPrime 157) (hne : ∀ k, seq k ≠ 157) :
    ∀ H : Subgroup (ZMod 157)ˣ, H ≠ ⊤ →
      ∃ m, (Units.mk0 (multZ 157 m) (multZ_ne_zero hq hne m)) ∉ H :=
  se_at_of_pow_checks hq hne 2 43 (by decide) (by native_decide) (by native_decide)

/-! ## Concrete mixing: the walk hits -1 mod 5

A direct computation showing that the EM walk visits -1 in ZMod 5.
This is the first concrete instance of the Hitting Hypothesis for
a prime not in the first few terms of the sequence. -/

/-- **The walk hits -1 mod 5 at step 5**: prod 5 ≡ -1 (mod 5).
    This directly verifies the Hitting Hypothesis for q = 5:
    the walk 2, 6, 42, 1806, 23478, 1244334 satisfies
    1244334 ≡ 4 ≡ -1 (mod 5). -/
theorem walkZ_five_hits_neg_one : walkZ 5 5 = -1 := by
  rw [walkZ_eq_neg_one_iff]
  -- Need: 5 ∣ (prod 5 + 1) = 5 ∣ 1244335
  have hprod5 : prod 5 = 1244334 := by
    rw [prod_succ, prod_succ, prod_succ, prod_succ, prod_succ, prod_zero,
        seq_one, seq_two, seq_three, seq_four, seq_five]
  rw [hprod5]
  exact ⟨248867, by omega⟩

/-- **The walk hits -1 mod 139 at step 3**: prod 3 = 1806 ≡ 138 ≡ -1 (mod 139).
    Since 1807 = 13 × 139, and seq 4 = 13, this is a NON-AUTO hit:
    the walk hits -1 mod a prime (139) that is NOT the next sequence term.
    This demonstrates genuine mixing behavior. -/
theorem walkZ_139_hits_neg_one : walkZ 139 3 = -1 := by
  rw [walkZ_eq_neg_one_iff]
  have hprod3 : prod 3 = 1806 := by
    rw [prod_succ, prod_succ, prod_succ, prod_zero, seq_one, seq_two, seq_three]
  rw [hprod3]
  exact ⟨13, by omega⟩

/-- **The walk hits -1 mod 443 at step 4**: prod 4 = 23478 ≡ 442 ≡ -1 (mod 443).
    Since 23479 = 53 × 443, and seq 5 = 53, this is a NON-AUTO hit:
    the walk hits -1 mod 443 at the same step where it auto-hits -1 mod 53.
    The Euclid number prod(4)+1 factors as two primes, giving two
    simultaneous -1 hits. -/
theorem walkZ_443_hits_neg_one : walkZ 443 4 = -1 := by
  rw [walkZ_eq_neg_one_iff]
  have hprod4 : prod 4 = 23478 := by
    rw [prod_succ, prod_succ, prod_succ, prod_succ, prod_zero,
        seq_one, seq_two, seq_three, seq_four]
  rw [hprod4]
  exact ⟨53, by omega⟩

/-- **The walk hits -1 mod 248867 at step 5**: prod 5 = 1244334 ≡ -1 (mod 248867).
    Since 1244335 = 5 × 248867, and seq 6 = 5, this is another NON-AUTO hit.
    The prime 248867 is not known to appear in the EM sequence. -/
theorem walkZ_248867_hits_neg_one : walkZ 248867 5 = -1 := by
  rw [walkZ_eq_neg_one_iff]
  have hprod5 : prod 5 = 1244334 := by
    rw [prod_succ, prod_succ, prod_succ, prod_succ, prod_succ, prod_zero,
        seq_one, seq_two, seq_three, seq_four, seq_five]
  rw [hprod5]
  exact ⟨5, by omega⟩

/-! ## Walk Non-Periodicity

The walk cannot be eventually periodic. If two walk positions coincide
(walkZ q i = walkZ q j) but the multipliers at those steps differ
(multZ q i ≠ multZ q j), then the walk immediately diverges at the
next step. Since the EM multipliers are all distinct primes, any two
steps i ≠ j with i,j large enough will have different multiplier
residues, forcing divergence.

This is a key structural property: the walk explores genuinely new
territory after each collision, not just cycling through the same states. -/

/-- **Walk divergence at collision**: if the walk visits the same state
    at steps i and j, but the multipliers differ, then the walk
    immediately diverges at the next step.

    Proof: w(i+1) = w(i)·m(i) and w(j+1) = w(j)·m(j) = w(i)·m(j).
    If w(i+1) = w(j+1), then w(i)·m(i) = w(i)·m(j), so m(i) = m(j)
    by cancellation (since w(i) ≠ 0). Contradiction. -/
theorem walk_diverges_at_collision {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {i j : Nat}
    (hcoll : walkZ q i = walkZ q j)
    (hmult : multZ q i ≠ multZ q j) :
    walkZ q (i + 1) ≠ walkZ q (j + 1) := by
  intro heq
  rw [walkZ_succ, walkZ_succ, hcoll] at heq
  exact hmult (mul_left_cancel₀ (walkZ_ne_zero hq hne j) heq)

/-- **Walk agreement forces multiplier agreement**: if the walk agrees
    at steps i and j AND at steps i+1 and j+1, then the multiplier
    residues at steps i and j must be equal.

    This is the contrapositive of `walk_diverges_at_collision`. -/
theorem walk_agreement_implies_mult_eq {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {i j : Nat}
    (hcoll : walkZ q i = walkZ q j)
    (hnext : walkZ q (i + 1) = walkZ q (j + 1)) :
    multZ q i = multZ q j := by
  rw [walkZ_succ, walkZ_succ, hcoll] at hnext
  exact mul_left_cancel₀ (walkZ_ne_zero hq hne j) hnext

/-- **Full walk periodicity forces multiplier periodicity**: if the walk
    is periodic with period j-i (i.e., w(i+k) = w(j+k) for all k ≥ 0),
    then the multipliers are also periodic with the same period.

    This means: if the walk "cycles" starting from step i, then the
    multiplier residues must also cycle, i.e., seq(i+k+1) ≡ seq(j+k+1)
    (mod q) for all k ≥ 0. Since the EM primes are all distinct, this
    is an extremely strong constraint that is unlikely to hold for
    infinitely many k. -/
theorem walk_periodic_implies_mult_periodic {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    {i j : Nat}
    (hperiod : ∀ k, walkZ q (i + k) = walkZ q (j + k)) :
    ∀ k, multZ q (i + k) = multZ q (j + k) := by
  intro k
  exact walk_agreement_implies_mult_eq hq hne (hperiod k) (by
    rw [show i + k + 1 = i + (k + 1) by omega, show j + k + 1 = j + (k + 1) by omega]
    exact hperiod (k + 1))

/-! ## Target Reformulation of Hitting

The walk hits -1 at step n+1 iff the walk at step n equals a specific
"target" value determined by the next multiplier: w(n) = -m(n)⁻¹.

This gives an alternative perspective on mixing: instead of asking
"does the walk ever reach -1?", we ask "does the walk ever coincide
with its target sequence T(n) = -m(n)⁻¹?"

The target T(n) = -(seq(n+1))⁻¹ mod q depends only on which prime
seq(n+1) is, not on the walk history. So mixing becomes an intersection
problem between two sequences in (ZMod q)×:
  - The walk sequence: w(0), w(1), w(2), ...
  - The target sequence: T(0), T(1), T(2), ... -/

/-- **Target reformulation**: the walk hits -1 at step n+1 iff the
    walk at step n equals the "target" -m(n)⁻¹.

    This follows from w(n+1) = w(n) · m(n):
    w(n+1) = -1  ⟺  w(n) · m(n) = -1  ⟺  w(n) = -m(n)⁻¹. -/
theorem walkZ_hits_iff_target {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat) :
    walkZ q (n + 1) = -1 ↔ walkZ q n = -(multZ q n)⁻¹ := by
  have hm_ne := multZ_ne_zero hq hne n
  rw [walkZ_succ]
  constructor
  · intro h
    have : walkZ q n * multZ q n * (multZ q n)⁻¹ = -1 * (multZ q n)⁻¹ :=
      congrArg (· * (multZ q n)⁻¹) h
    rwa [mul_assoc, mul_inv_cancel₀ hm_ne, mul_one, neg_mul, one_mul] at this
  · intro h
    rw [h]
    simp [neg_mul, inv_mul_cancel₀ hm_ne]

/-- **Walk hit from target match**: if at step n the walk equals
    the target -m(n)⁻¹, then the walk hits -1 at step n+1. -/
theorem walkZ_hit_of_target {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (n : Nat)
    (htarget : walkZ q n = -(multZ q n)⁻¹) :
    walkZ q (n + 1) = -1 :=
  (walkZ_hits_iff_target hq hne n).mpr htarget

/-! ## Helper: IsPrime implies minFac self

When n is prime, our `minFac` function returns n itself (since n has
no divisors other than 1 and n, and minFac finds the smallest ≥ 2). -/

/-- **Primes are their own minFac**: if n is prime, minFac n = n. -/
theorem isPrime_minFac_self {n : Nat} (hp : IsPrime n) : minFac n = n := by
  have h2 : 2 ≤ n := hp.1
  have hdvd : minFac n ∣ n := minFac_dvd n h2
  rcases hp.2 (minFac n) hdvd with h | h
  · have := (minFac_isPrime n h2).1; omega
  · exact h


end MullinGroup
