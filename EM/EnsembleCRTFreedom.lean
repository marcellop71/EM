import EM.EnsembleCRT
import EM.CRTFiberIndependence

/-!
# CRT Multi-Modulus Freedom

This file proves that fixing residues at finitely many coprime moduli leaves
residues at other moduli equidistributed. These are abstract combinatorial
results about arithmetic progressions and CRT, used in the ensemble
equidistribution framework.

## Main Results

### Definitions
* `residueClassCount`                    -- count of n in [1,X] in a residue class mod m
* `jointResidueClassCount`               -- count with two simultaneous congruences

### Proved Theorems
* `residue_class_count_le`               -- count <= X
* `residue_class_count_nonneg`           -- count >= 0 (real cast)
* `residue_class_count_sum_eq`           -- sum over classes = X (partition identity)
* `joint_residue_class_count_le`         -- joint count <= X
* `joint_count_le_first`                 -- joint count <= first-modulus count
* `joint_count_le_second`                -- joint count <= second-modulus count
* `joint_count_sum_eq_first`             -- sum of joint counts = first count (partition)
* `joint_filter_eq`                      -- joint filter = iterated filter
* `minFac_constraint_moduli_finite`      -- {r prime : r <= p} is finite
* `distinct_primes_coprime`              -- distinct primes are coprime
* `minFac_constraint_coprime_to_large`   -- s > p prime, r <= p prime => coprime
* `crt_freedom_density_implies_prime`    -- CRTFreedomDensity => CRTFreedomPrime
* `joint_density_ratio_nonneg`           -- density ratio >= 0
* `joint_density_ratio_le_one`           -- density ratio <= 1
* `joint_density_le_marginal_density`    -- joint count <= marginal (real)

### Open Hypotheses
* `CRTFreedomDensity`                    -- density version: conditioning on one
                                            coprime modulus leaves other equidistributed
* `CRTFreedomPrime`                      -- prime specialization
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup

/-! ## Residue Class Counting -/

section ResidueClassCount

/-- Count of integers n in [1,X] in residue class a mod m. -/
def residueClassCount (X m : Nat) (a : ZMod m) : Nat :=
  ((Finset.Icc 1 X).filter (fun n : Nat => (n : ZMod m) = a)).card

/-- Count of integers n in [1,X] simultaneously in class a1 mod m1 and a2 mod m2. -/
def jointResidueClassCount (X m₁ m₂ : Nat) (a₁ : ZMod m₁) (a₂ : ZMod m₂) : Nat :=
  ((Finset.Icc 1 X).filter (fun n : Nat => (n : ZMod m₁) = a₁ ∧ (n : ZMod m₂) = a₂)).card

/-- The residue class count is at most X (trivially). -/
theorem residue_class_count_le (X m : Nat) (a : ZMod m) :
    residueClassCount X m a ≤ X :=
  (Finset.card_filter_le _ _).trans (by simp [Nat.card_Icc])

/-- The residue class count is non-negative (real-valued). -/
theorem residue_class_count_nonneg (X m : Nat) (a : ZMod m) :
    (0 : ℝ) ≤ (residueClassCount X m a : ℝ) :=
  Nat.cast_nonneg _

/-- The sum of residue class counts over all classes equals X.
    This is the partition identity: every n in [1,X] falls into exactly one
    residue class mod m. -/
theorem residue_class_count_sum_eq (X m : Nat) [NeZero m] :
    ∑ a : ZMod m, residueClassCount X m a = X := by
  unfold residueClassCount
  have h := Finset.card_eq_sum_card_fiberwise (f := fun n : Nat => (n : ZMod m))
    (s := Finset.Icc 1 X) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  simp only [Nat.card_Icc] at h
  omega

/-- The joint residue class count is at most X. -/
theorem joint_residue_class_count_le (X m₁ m₂ : Nat) (a₁ : ZMod m₁) (a₂ : ZMod m₂) :
    jointResidueClassCount X m₁ m₂ a₁ a₂ ≤ X :=
  (Finset.card_filter_le _ _).trans (by simp [Nat.card_Icc])

end ResidueClassCount

/-! ## Joint Count and Single Count Relationship -/

section JointSingle

/-- The joint count is at most the count restricted to the first modulus. -/
theorem joint_count_le_first (X m₁ m₂ : Nat) (a₁ : ZMod m₁) (a₂ : ZMod m₂) :
    jointResidueClassCount X m₁ m₂ a₁ a₂ ≤ residueClassCount X m₁ a₁ := by
  unfold jointResidueClassCount residueClassCount
  exact Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ h => h.1)

/-- The joint count is at most the count restricted to the second modulus. -/
theorem joint_count_le_second (X m₁ m₂ : Nat) (a₁ : ZMod m₁) (a₂ : ZMod m₂) :
    jointResidueClassCount X m₁ m₂ a₁ a₂ ≤ residueClassCount X m₂ a₂ := by
  unfold jointResidueClassCount residueClassCount
  exact Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ h => h.2)

/-- The joint filter is the intersection of two filters. -/
theorem joint_filter_eq (X m₁ m₂ : Nat) (a₁ : ZMod m₁) (a₂ : ZMod m₂) :
    (Finset.Icc 1 X).filter (fun n : Nat =>
      (n : ZMod m₁) = a₁ ∧ (n : ZMod m₂) = a₂) =
    ((Finset.Icc 1 X).filter (fun n : Nat => (n : ZMod m₁) = a₁)).filter
      (fun n : Nat => (n : ZMod m₂) = a₂) :=
  (Finset.filter_filter _ _ _).symm

/-- The sum of joint counts over the second modulus equals the first count.
    This is because every n with n in a class mod m₁ falls into exactly one
    class mod m₂. -/
theorem joint_count_sum_eq_first (X m₁ m₂ : Nat) [NeZero m₂]
    (a₁ : ZMod m₁) :
    ∑ b : ZMod m₂, jointResidueClassCount X m₁ m₂ a₁ b =
      residueClassCount X m₁ a₁ := by
  unfold jointResidueClassCount residueClassCount
  simp_rw [(Finset.filter_filter _ _ _).symm]
  exact Finset.card_eq_sum_card_fiberwise
    (f := fun n : Nat => (n : ZMod m₂))
    (fun _ _ => Finset.mem_univ _) |>.symm

end JointSingle

/-! ## Prime Modulus Finiteness -/

section PrimeModuli

/-- The set of primes at most p is finite. This bounds the number of
    moduli constrained by the condition genSeq n j = p (since minFac
    only involves trial division by primes at most p). -/
theorem minFac_constraint_moduli_finite (p : Nat) :
    Set.Finite {r : Nat | Nat.Prime r ∧ r ≤ p} :=
  (Set.finite_le_nat p).subset fun _ h => h.2

/-- Distinct primes are coprime. -/
theorem distinct_primes_coprime {p q : Nat} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) : Nat.Coprime p q :=
  (Nat.coprime_primes hp hq).mpr hpq

/-- For a prime s > p and any prime r at most p, s and r are coprime
    (since they are distinct primes). -/
theorem minFac_constraint_coprime_to_large {p s : Nat} (hs : Nat.Prime s) (hps : p < s)
    {r : Nat} (hr : Nat.Prime r) (hr_le : r ≤ p) : Nat.Coprime s r :=
  distinct_primes_coprime hs hr (by omega)

end PrimeModuli

/-! ## CRT Freedom Density -/

section CRTFreedomDensity

/-- The **CRT freedom density** statement: among integers n at most X with
    n in a given class mod m₁, the proportion in a given class mod m₂
    tends to 1/m₂ as X tends to infinity, when m₁ and m₂ are coprime.

    This is the key equidistribution statement: conditioning on one coprime
    modulus leaves the other equidistributed.

    **Status**: open hypothesis (standard number theory, but the Lean
    formalization of arithmetic progression density asymptotics is
    substantial and not in Mathlib). -/
def CRTFreedomDensity : Prop :=
  ∀ (m₁ m₂ : Nat) (_ : 0 < m₁) (_ : 1 < m₂)
    (_ : Nat.Coprime m₁ m₂)
    (a : ZMod m₁) (b : ZMod m₂),
    Filter.Tendsto
      (fun X : Nat =>
        (jointResidueClassCount X m₁ m₂ a b : ℝ) /
        (residueClassCount X m₁ a : ℝ))
      Filter.atTop
      (nhds (1 / (m₂ : ℝ)))

/-- **CRT freedom for primes**: the specialization to prime moduli, which is
    the form used in the ensemble equidistribution arguments. -/
def CRTFreedomPrime : Prop :=
  ∀ (p q : Nat) (_ : Nat.Prime p) (_ : Nat.Prime q) (_ : p ≠ q)
    (a : ZMod p) (b : ZMod q),
    Filter.Tendsto
      (fun X : Nat =>
        (jointResidueClassCount X p q a b : ℝ) /
        (residueClassCount X p a : ℝ))
      Filter.atTop
      (nhds (1 / (q : ℝ)))

/-- CRTFreedomDensity implies CRTFreedomPrime (specialization). -/
theorem crt_freedom_density_implies_prime (h : CRTFreedomDensity) :
    CRTFreedomPrime := by
  intro p q hp hq hpq a b
  exact h p q hp.pos hq.one_lt (distinct_primes_coprime hp hq hpq) a b

/-- The joint density (as a ratio) is non-negative. -/
theorem joint_density_ratio_nonneg (X m₁ m₂ : Nat)
    (a₁ : ZMod m₁) (a₂ : ZMod m₂) :
    0 ≤ (jointResidueClassCount X m₁ m₂ a₁ a₂ : ℝ) /
      (residueClassCount X m₁ a₁ : ℝ) :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The joint density ratio is at most 1. -/
theorem joint_density_ratio_le_one (X m₁ m₂ : Nat)
    (a₁ : ZMod m₁) (a₂ : ZMod m₂) :
    (jointResidueClassCount X m₁ m₂ a₁ a₂ : ℝ) /
    (residueClassCount X m₁ a₁ : ℝ) ≤ 1 := by
  by_cases h : residueClassCount X m₁ a₁ = 0
  · simp [h]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
      (by exact_mod_cast joint_count_le_first X m₁ m₂ a₁ a₂)

/-- The joint count is bounded by the marginal count (real-valued version). -/
theorem joint_density_le_marginal_density (X m₁ m₂ : Nat)
    (a₁ : ZMod m₁) (a₂ : ZMod m₂) :
    (jointResidueClassCount X m₁ m₂ a₁ a₂ : ℝ) ≤
    (residueClassCount X m₁ a₁ : ℝ) := by
  exact_mod_cast joint_count_le_first X m₁ m₂ a₁ a₂

end CRTFreedomDensity

/-! ## Squarefree Joint Accumulator Counting -/

section SquarefreeCRTIndep

/-- Count of squarefree n in [1,X] with genProd n k in residue class a mod q
    AND in residue class b mod r simultaneously, where q and r are distinct primes.

    This is the squarefree analogue of `jointResidueClassCount` specialized to
    the generalized accumulator. It captures the joint distribution of the
    mod-q and mod-r coordinates of genProd n k among squarefree starting points. -/
def sqfreeJointAccumCount (X k q r : Nat) (a : ZMod q) (b : ZMod r) : Nat :=
  ((Finset.Icc 1 X).filter (fun n =>
    Squarefree n ∧ (genProd n k : ZMod q) = a ∧ (genProd n k : ZMod r) = b)).card

/-- The joint accumulator count is bounded by the squarefree count. -/
theorem sqfreeJointAccumCount_le_sqfreeCount (X k q r : Nat) (a : ZMod q)
    (b : ZMod r) : sqfreeJointAccumCount X k q r a b ≤ sqfreeCount X := by
  unfold sqfreeJointAccumCount sqfreeCount
  exact Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ h => h.1)

/-- The joint accumulator count is bounded by the marginal accumulator count
    (projecting to the first modulus q). -/
theorem sqfreeJointAccumCount_le_accumCount_first (X k q r : Nat) (a : ZMod q)
    (b : ZMod r) : sqfreeJointAccumCount X k q r a b ≤ sqfreeAccumCount X k q a := by
  unfold sqfreeJointAccumCount sqfreeAccumCount
  exact Finset.card_le_card
    (Finset.monotone_filter_right _ fun _ _ h => ⟨h.1, h.2.1⟩)

/-- The joint accumulator count is bounded by the marginal accumulator count
    (projecting to the second modulus r). -/
theorem sqfreeJointAccumCount_le_accumCount_second (X k q r : Nat) (a : ZMod q)
    (b : ZMod r) : sqfreeJointAccumCount X k q r a b ≤ sqfreeAccumCount X k r b := by
  unfold sqfreeJointAccumCount sqfreeAccumCount
  exact Finset.card_le_card
    (Finset.monotone_filter_right _ fun _ _ h => ⟨h.1, h.2.2⟩)

/-- The sum of joint accumulator counts over the second modulus r gives
    the marginal accumulator count for the first modulus q.
    This is a partition identity: every squarefree n with genProd n k ≡ a (mod q)
    falls into exactly one residue class mod r. -/
theorem sqfreeJointAccumCount_sum_eq_first (X k q r : Nat) [NeZero r]
    (a : ZMod q) :
    ∑ b : ZMod r, sqfreeJointAccumCount X k q r a b =
      sqfreeAccumCount X k q a := by
  unfold sqfreeJointAccumCount sqfreeAccumCount
  simp_rw [(Finset.filter_filter _ _ _).symm]
  exact Finset.card_eq_sum_card_fiberwise
    (f := fun n : Nat => (genProd n k : ZMod r))
    (fun _ _ => Finset.mem_univ _) |>.symm

/-- The joint accumulator density: proportion of squarefree n with
    genProd n k ≡ a (mod q) among squarefree n with genProd n k ≡ b (mod r). -/
def sqfreeJointAccumDensity (X k q r : Nat) (a : ZMod q) (b : ZMod r) : ℝ :=
  (sqfreeJointAccumCount X k q r a b : ℝ) / (sqfreeAccumCount X k r b : ℝ)

/-- The joint accumulator density is non-negative. -/
theorem sqfreeJointAccumDensity_nonneg (X k q r : Nat) (a : ZMod q)
    (b : ZMod r) : 0 ≤ sqfreeJointAccumDensity X k q r a b :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The joint accumulator density is at most 1. -/
theorem sqfreeJointAccumDensity_le_one (X k q r : Nat) (a : ZMod q)
    (b : ZMod r) : sqfreeJointAccumDensity X k q r a b ≤ 1 := by
  unfold sqfreeJointAccumDensity
  by_cases h : sqfreeAccumCount X k r b = 0
  · simp [h]
  · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mpr
      (Nat.cast_le.mpr (sqfreeJointAccumCount_le_accumCount_second X k q r a b))

/-- **Partition identity for sqfreeAccumCount**: summing over all residue classes
    gives the total squarefree count.
    Every squarefree n in [1,X] falls into exactly one residue class mod r. -/
theorem sqfreeAccumCount_sum_eq_sqfreeCount (X k r : Nat) [NeZero r] :
    ∑ a : ZMod r, sqfreeAccumCount X k r a = sqfreeCount X := by
  unfold sqfreeAccumCount sqfreeCount
  simp_rw [(Finset.filter_filter _ _ _).symm]
  exact Finset.card_eq_sum_card_fiberwise
    (f := fun n : Nat => (genProd n k : ZMod r))
    (fun _ _ => Finset.mem_univ _) |>.symm

/-- **Density partition**: summing sqfreeAccumDensity over all residue classes gives 1
    when the squarefree count is positive. -/
theorem sqfreeAccumDensity_sum_eq_one (X k r : Nat) [NeZero r]
    (hX : 0 < sqfreeCount X) :
    ∑ a : ZMod r, sqfreeAccumDensity X k r a = 1 := by
  unfold sqfreeAccumDensity
  rw [← Finset.sum_div]
  rw [div_eq_one_iff_eq (Nat.cast_pos.mpr hX).ne']
  push_cast [← sqfreeAccumCount_sum_eq_sqfreeCount X k r]
  rfl

/-- **Zero-class density vanishes**: if the density of each nonzero residue class
    mod r tends to 1/(r-1), then the density of the zero class tends to 0.
    This follows from the partition identity: the sum over all classes is 1. -/
theorem sqfreeAccumDensity_zero_vanishes (k r : Nat) (hr : Nat.Prime r)
    (hnonzero : ∀ (a : ZMod r), a ≠ 0 →
      Filter.Tendsto
        (fun X : Nat => sqfreeAccumDensity X k r a)
        Filter.atTop
        (nhds (1 / ((r : ℝ) - 1)))) :
    Filter.Tendsto
      (fun X : Nat => sqfreeAccumDensity X k r 0)
      Filter.atTop
      (nhds 0) := by
  haveI : NeZero r := ⟨hr.ne_zero⟩
  -- ∑_{a≠0} sqfreeAccumDensity(a) → (r-1) · 1/(r-1) = 1
  have hsum_nonzero : Filter.Tendsto
      (fun X : Nat => ∑ a ∈ Finset.univ.filter (· ≠ (0 : ZMod r)),
        sqfreeAccumDensity X k r a)
      Filter.atTop
      (nhds (∑ a ∈ Finset.univ.filter (· ≠ (0 : ZMod r)),
        (1 / ((r : ℝ) - 1)))) := by
    apply tendsto_finset_sum
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact hnonzero a ha
  have hcard : (Finset.univ.filter (· ≠ (0 : ZMod r))).card = r - 1 := by
    rw [Finset.filter_ne' Finset.univ (0 : ZMod r), Finset.card_erase_of_mem
      (Finset.mem_univ _)]
    simp [ZMod.card r]
  have hnonzero_sum_val : ∑ a ∈ Finset.univ.filter (· ≠ (0 : ZMod r)),
      (1 / ((r : ℝ) - 1)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    have hr_pos : (0 : ℝ) < (r : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hr.one_lt)
    rw [show ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 from by
          rw [Nat.cast_sub hr.one_le]; simp]
    rw [one_div, mul_inv_cancel₀ hr_pos.ne']
  rw [hnonzero_sum_val] at hsum_nonzero
  have hdecomp : ∀ X : Nat, 0 < sqfreeCount X →
      sqfreeAccumDensity X k r 0 =
        1 - ∑ a ∈ Finset.univ.filter (· ≠ (0 : ZMod r)),
          sqfreeAccumDensity X k r a := by
    intro X hX
    have htotal := sqfreeAccumDensity_sum_eq_one X k r hX
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod r))] at htotal
    rw [← Finset.filter_ne'] at htotal
    linarith
  -- density(0) = 1 - ∑_{a≠0} density(a) → 1 - 1 = 0 (eventually, since sqfreeCount > 0)
  rw [show (0 : ℝ) = 1 - 1 from by ring]
  apply Filter.Tendsto.sub tendsto_const_nhds hsum_nonzero |>.congr'
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  exact ⟨1, fun X hX => (hdecomp X (by
    unfold sqfreeCount
    exact Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨le_refl _, hX⟩, squarefree_one⟩⟩)).symm⟩

/-- **Squarefree CRT Independence**: for distinct primes q and r, the mod-q and
    mod-r coordinates of genProd n k are approximately independent among
    squarefree n.

    Formally: among squarefree n with genProd n k in a fixed nonzero class b
    mod r, the proportion with genProd n k in a given nonzero class a mod q
    tends to 1/(q-1) as X tends to infinity.

    This is the key structural hypothesis for CRT propagation. It says that
    fixing the "other-prime" coordinates of the accumulator leaves the
    mod-q coordinate equidistributed. Combined with `crt_multiplier_invariance`
    (the multiplier genSeq n k = minFac(genProd n k + 1) depends only on the
    non-mod-q coordinates), this gives CRTPropagationStep.

    **Mathematical basis**: For squarefree integers, the density in a joint
    residue class (a mod q, b mod r) among those in class b mod r is
    asymptotically 1/(q-1), because squarefree density has a multiplicative
    Euler product that factors over primes. The key identity is:
    (density of sqfree n with n ≡ a mod q and n ≡ b mod r) /
    (density of sqfree n with n ≡ b mod r) → 1/(q-1)
    which follows from the Chinese Remainder Theorem for squarefree numbers:
    the local factor at q contributes independently.

    At k = 0 (genProd n 0 = n), this reduces to CRT independence for squarefree
    integers, which is a standard result in multiplicative number theory.
    For general k, the genProd n k accumulator inherits the CRT structure from
    the starting point n through the deterministic recurrence.

    **Status**: open hypothesis (standard ANT, analogous to CRTFreedomDensity
    but for the squarefree population and generalized accumulator). -/
def SquarefreeCRTIndependence : Prop :=
  ∀ (q r : Nat), Nat.Prime q → Nat.Prime r → q ≠ r →
  ∀ (k : Nat),
  ∀ (a : ZMod q), a ≠ 0 →
  ∀ (b : ZMod r), b ≠ 0 →
    Filter.Tendsto
      (fun X : Nat => sqfreeJointAccumDensity X k q r a b)
      Filter.atTop
      (nhds (1 / ((q : ℝ) - 1)))

/-- **SCRTI implies marginal equidistribution at the same step for other primes.**
    If sqfreeAccumDensity X k r a → 1/(r-1) for all nonzero a mod r (equidist at
    step k for prime r), and SquarefreeCRTIndependence holds, then
    sqfreeAccumDensity X k q a → 1/(q-1) for all nonzero a mod q (equidist at
    step k for any other prime q ≠ r).

    Proof: Decompose sqfreeAccumCount(k, q, a) = ∑_b sqfreeJointAccumCount(q, r, a, b).
    For nonzero b: joint count / sqfreeCount X =
      (joint count / accumCount(r, b)) * (accumCount(r, b) / sqfreeCount X)
      = sqfreeJointAccumDensity(q,r,a,b) * sqfreeAccumDensity(k,r,b)
      → 1/(q-1) * 1/(r-1).
    Summing over (r-1) nonzero b's: → 1/(q-1).
    The b=0 term → 0 by zero-class vanishing. -/
theorem scrti_bootstrap_all_primes
    (hscrti : SquarefreeCRTIndependence)
    (r : Nat) (hr : Nat.Prime r)
    (k : Nat)
    (heq_r : ∀ (a : ZMod r), a ≠ 0 →
      Filter.Tendsto
        (fun X : Nat => sqfreeAccumDensity X k r a)
        Filter.atTop
        (nhds (1 / ((r : ℝ) - 1))))
    (q : Nat) (hq : Nat.Prime q) (hqr : q ≠ r) :
    ∀ (a : ZMod q), a ≠ 0 →
      Filter.Tendsto
        (fun X : Nat => sqfreeAccumDensity X k q a)
        Filter.atTop
        (nhds (1 / ((q : ℝ) - 1))) := by
  haveI : NeZero r := ⟨hr.ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  delta SquarefreeCRTIndependence at hscrti
  intro a ha
  -- Zero-class density → 0
  have hzero := sqfreeAccumDensity_zero_vanishes k r hr heq_r
  -- For each nonzero b: joint/sqfree → 1/(q-1) · 1/(r-1)
  have hnonzero_term : ∀ (b : ZMod r), b ≠ 0 →
      Filter.Tendsto
        (fun X : Nat => (sqfreeJointAccumCount X k q r a b : ℝ) / (sqfreeCount X : ℝ))
        Filter.atTop
        (nhds (1 / ((q : ℝ) - 1) * (1 / ((r : ℝ) - 1)))) := by
    intro b hb
    have hscrti_ab := hscrti q r hq hr hqr k a ha b hb
    have heq_rb := heq_r b hb
    -- joint/sqfree = jointDensity * accumDensity(r,b) when accumCount > 0
    have hfact : ∀ X : Nat, 0 < sqfreeAccumCount X k r b →
        (sqfreeJointAccumCount X k q r a b : ℝ) / (sqfreeCount X : ℝ) =
        sqfreeJointAccumDensity X k q r a b * sqfreeAccumDensity X k r b := by
      intro X hpos
      unfold sqfreeJointAccumDensity sqfreeAccumDensity
      have hne : (sqfreeAccumCount X k r b : ℝ) ≠ 0 := (Nat.cast_pos.mpr hpos).ne'
      field_simp
    -- Eventually positive (since density → 1/(r-1) > 0)
    have hev_pos : ∀ᶠ X in Filter.atTop, 0 < sqfreeAccumCount X k r b := by
      have hpos_limit : (0 : ℝ) < 1 / ((r : ℝ) - 1) := by
        apply div_pos one_pos
        exact sub_pos.mpr (by exact_mod_cast hr.one_lt)
      have hev := heq_rb.eventually (Ioi_mem_nhds hpos_limit)
      apply hev.mono
      intro X hX
      unfold sqfreeAccumDensity at hX
      by_contra h
      push_neg at h
      have : sqfreeAccumCount X k r b = 0 := Nat.le_zero.mp h
      simp [this] at hX
    apply (Filter.Tendsto.mul hscrti_ab heq_rb).congr'
    exact hev_pos.mono (fun X hX => (hfact X hX).symm)

  -- Sum over nonzero b's → 1/(q-1)
  have hnonzero_sum : Filter.Tendsto
      (fun X : Nat => ∑ b ∈ Finset.univ.filter (· ≠ (0 : ZMod r)),
        (sqfreeJointAccumCount X k q r a b : ℝ) / (sqfreeCount X : ℝ))
      Filter.atTop
      (nhds (∑ b ∈ Finset.univ.filter (· ≠ (0 : ZMod r)),
        (1 / ((q : ℝ) - 1) * (1 / ((r : ℝ) - 1))))) := by
    apply tendsto_finset_sum
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact hnonzero_term b hb

  have hcard_r : (Finset.univ.filter (· ≠ (0 : ZMod r))).card = r - 1 := by
    rw [Finset.filter_ne' Finset.univ (0 : ZMod r), Finset.card_erase_of_mem
      (Finset.mem_univ _)]
    simp [ZMod.card r]

  have hnonzero_sum_val : ∑ b ∈ Finset.univ.filter (· ≠ (0 : ZMod r)),
      (1 / ((q : ℝ) - 1) * (1 / ((r : ℝ) - 1))) = 1 / ((q : ℝ) - 1) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard_r]
    rw [Nat.cast_sub hr.one_le, Nat.cast_one]
    have hr_pos : (0 : ℝ) < (r : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hr.one_lt)
    have hq_pos : (0 : ℝ) < (q : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hq.one_lt)
    field_simp

  rw [hnonzero_sum_val] at hnonzero_sum

  -- b=0 term → 0 (squeezed by accumDensity(r, 0) → 0)
  have hzero_term : Filter.Tendsto
      (fun X : Nat => (sqfreeJointAccumCount X k q r a 0 : ℝ) / (sqfreeCount X : ℝ))
      Filter.atTop
      (nhds 0) := by
    have hbound : ∀ X : Nat,
        (sqfreeJointAccumCount X k q r a 0 : ℝ) / (sqfreeCount X : ℝ) ≤
        sqfreeAccumDensity X k r 0 := by
      intro X
      unfold sqfreeAccumDensity
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast sqfreeJointAccumCount_le_accumCount_second X k q r a 0
    apply squeeze_zero
    · intro X; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact hbound
    · exact hzero

  -- Decompose: accumDensity(q, a) = (∑_{b≠0} joint/sqfree) + (b=0 term)
  have hfull_decomp : ∀ X : Nat,
      sqfreeAccumDensity X k q a =
        (∑ b ∈ Finset.univ.filter (· ≠ (0 : ZMod r)),
          (sqfreeJointAccumCount X k q r a b : ℝ) / (sqfreeCount X : ℝ)) +
        (sqfreeJointAccumCount X k q r a 0 : ℝ) / (sqfreeCount X : ℝ) := by
    intro X
    unfold sqfreeAccumDensity
    rw [← sqfreeJointAccumCount_sum_eq_first X k q r a]
    push_cast
    rw [Finset.sum_div]
    rw [Finset.filter_ne']
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod r))]
    ring

  have htotal := Filter.Tendsto.add hnonzero_sum hzero_term
  rw [add_zero] at htotal
  exact htotal.congr (fun X => (hfull_decomp X).symm)

/-- **SquarefreeCRTIndependence implies CRTPropagationStep.**

    The conceptual argument:
    1. By SCRTI, among squarefree n with genProd n k in any fixed nonzero
       class b mod r (for each prime r different from q), the mod-q coordinate of
       genProd n k is equidistributed. This means the mod-q coordinate is
       approximately independent of all non-mod-q coordinates.
    2. By `crt_multiplier_invariance` (PROVED in MullinCRT.lean), the multiplier
       genSeq n k = minFac(genProd n k + 1) depends only on genProd n k mod r
       for primes r different from q — it is "q-blind."
    3. genProd n (k+1) = genProd n k * genSeq n k. The mod-q residue of the
       product depends on: (i) genProd n k mod q (equidistributed by inductive
       hypothesis), and (ii) genSeq n k mod q (which, being q-blind, is
       approximately constant across the mod-q equidistributed ensemble).
    4. Multiplying an equidistributed mod-q value by a value approximately
       independent of it preserves equidistribution (affine image of uniform
       is uniform). This gives equidistribution of genProd n (k+1) mod q.

    The quantitative density argument connecting SCRTI to the CRTPropagationStep
    quantifiers involves tracking the error terms through the multiplication
    step. This requires showing that the q-blind multiplier partitions the
    ensemble into pieces where the mod-q coordinate remains approximately
    uniform. The core calculation is:

    density(genProd n (k+1) ≡ c mod q)
    = sum over (a, m) with a*m ≡ c mod q of
      density(genProd n k ≡ a mod q AND genSeq n k ≡ m mod q)
    ≈ sum over (a, m) with a*m ≡ c mod q of
      [density(genProd n k ≡ a | non-mod-q coords)] * [density(genSeq ≡ m)]

    By SCRTI, the first factor is 1/(q-1). By the convolution structure of
    multiplication in ZMod q, the sum gives 1/(q-1). Hence equidistribution
    propagates.

    **Status**: open hypothesis (the gap is the quantitative density tracking
    through multiplication — conceptually immediate from SCRTI +
    crt_multiplier_invariance, but the Lean formalization of the density
    tracking requires careful epsilon management). -/
def SquarefreeCRTIndepImpliesCRTProp : Prop :=
  SquarefreeCRTIndependence → CRTPropagationStep

/-- **SCRTI + CRTPropImplication + SRE → AccumulatorEquidistPropagation.**
    If SCRTI implies CRTPropagationStep, then combined with SRE this gives
    full accumulator equidistribution by induction. -/
theorem scrti_sre_implies_aep
    (hscrti_crt : SquarefreeCRTIndepImpliesCRTProp)
    (hsre : SquarefreeResidueEquidist)
    (hscrti : SquarefreeCRTIndependence) :
    AccumulatorEquidistPropagation :=
  sre_crt_implies_accum_equidist hsre (hscrti_crt hscrti)

end SquarefreeCRTIndep

/-! ## Summary

### Definitions (8):
* `residueClassCount`             -- count of n in [1,X] in residue class a mod m
* `jointResidueClassCount`        -- count of n in [1,X] in two simultaneous classes
* `CRTFreedomDensity`             -- density equidistribution (open hypothesis)
* `CRTFreedomPrime`               -- prime specialization (open hypothesis)
* `sqfreeJointAccumCount`         -- joint count with two moduli for genProd
* `sqfreeJointAccumDensity`       -- conditional density of mod-q given mod-r
* `SquarefreeCRTIndependence`     -- CRT independence for squarefree accumulators (open)
* `SquarefreeCRTIndepImpliesCRTProp` -- SCRTI => CRTPropagationStep (open)

### Proved Theorems (21):
* `residue_class_count_le`                -- count <= X
* `residue_class_count_nonneg`            -- count >= 0 (real)
* `residue_class_count_sum_eq`            -- sum over classes = X (partition)
* `joint_residue_class_count_le`          -- joint count <= X
* `joint_count_le_first`                  -- joint count <= first count
* `joint_count_le_second`                 -- joint count <= second count
* `joint_filter_eq`                       -- joint filter = iterated filter
* `joint_count_sum_eq_first`              -- sum of joint counts = first count
* `minFac_constraint_moduli_finite`       -- {r prime : r <= p} is finite
* `distinct_primes_coprime`               -- distinct primes are coprime
* `minFac_constraint_coprime_to_large`    -- s > p prime, r <= p prime => coprime
* `crt_freedom_density_implies_prime`     -- CRTFreedomDensity => CRTFreedomPrime
* `joint_density_ratio_nonneg`            -- density ratio >= 0
* `joint_density_ratio_le_one`            -- density ratio <= 1
* `joint_density_le_marginal_density`     -- joint count <= marginal (real)
* `sqfreeJointAccumCount_le_sqfreeCount`  -- joint accum count <= sqfree count
* `sqfreeJointAccumCount_le_accumCount_first`  -- joint <= marginal (first)
* `sqfreeJointAccumCount_le_accumCount_second` -- joint <= marginal (second)
* `sqfreeJointAccumCount_sum_eq_first`    -- partition identity for joint counts
* `sqfreeJointAccumDensity_nonneg`        -- density >= 0
* `sqfreeJointAccumDensity_le_one`        -- density <= 1
* `scrti_sre_implies_aep`                 -- SCRTI + SRE => AEP

### Open Hypotheses (4):
* `CRTFreedomDensity`
* `CRTFreedomPrime`
* `SquarefreeCRTIndependence`
* `SquarefreeCRTIndepImpliesCRTProp`
-/

end
