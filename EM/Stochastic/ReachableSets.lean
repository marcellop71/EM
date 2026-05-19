import EM.Stochastic.MixedMC

/-!
# Reachable Sets: Growth, Coset Impossibility, and Factor Confinement

## Overview

This file (Parts 21-22 and 24-26 of the original epsilon-random MC development)
develops the reachable-set perspective on the mixed walk: the set
`reachableAt q acc n` of residues mod q attainable by SOME valid mixed walk of
length n from acc, and its union `reachableEver q acc` = R_inf(q, acc).

The mixed walk from acc=2 implicitly defines the factor tree T(2):
- Root has accumulator 2
- At each node with accumulator P, children are P*p for each prime p | P+1
- Standard EM = leftmost path (always choosing minFac)
- MixedMC asks: does some path capture q? (= does -1 ∈ R_inf(q,2)?)

Key structural results (all proved):
- reachableAt_from_factor: every prime factor extends R_inf
- reachableEver_not_in_coset: R_inf escapes every proper coset
- factor_confinement: if R_inf is proper, ALL factors are sieve-confined
- mixed_hitting_iff_neg_one_reachable: hitting = reachability of -1

The sole remaining gap is FactorEscapeHypothesis: along the standard
EM orbit, Euclid numbers eventually escape step-dependent factor confinement.

## Contents

* Part 21: Reachable set infrastructure -- `reachableAt`, `reachableEver`,
  `reachableAt_zero`, `reachableAt_nonempty`, `reachableEver_nonempty`,
  `minFac_walk_in_reachable`, `mixed_hitting_iff_neg_one_reachable`
* Part 22: Reachable set growth from branching -- `factorSetModQ`,
  `minFac_mem_factorSetModQ`, `factorSetModQ_nonempty`,
  `not_prime_exists_quotient_factor`, `not_prime_quotient_ge_two`
* Part 24: Reachable set growth properties -- `reachableAt_subset_reachableEver`,
  `acc_mem_reachableEver`, `reachableAt_from_factor`, `reachableAt_minFac_step`,
  `reachable_grows_pair`, `reachable_composite_branch`, `reachableEver_from_factor`,
  `reachable_growth_landscape`
* Part 25: Reachable set coset impossibility -- `mixedWalkProd_two_minFac_eq_prod`,
  `reachableEver_ratios_escape_subgroup`, `reachableEver_not_in_coset`,
  `coset_impossibility_landscape`
* Part 26: Factor confinement and sieve obstruction -- `allowedFactors`,
  `forbiddenFactors`, `AllFactorsInSet`, `factor_confinement`,
  `all_factors_confined`, `standard_euclid_factors_confined`,
  `FactorEscapeHypothesis`, `factor_escape_implies_mixed_hitting`,
  `factor_escape_implies_reachable_full`, `factor_escape_implies_mixed_mc_at`,
  `factor_confinement_arbitrary`, `reachable_closed_under_allowed`,
  `factor_confinement_landscape`
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 21: Reachable Set Infrastructure

The **reachable set** R_n(acc, q) is the set of positions mod q that can be reached
by some valid mixed walk from accumulator acc in exactly n steps. This captures the
"breadth-first search" advantage of the mixed walk over the deterministic minFac walk.

Key properties:
1. R_0 = {acc mod q} (singleton)
2. R_n ⊆ R_{n+1} is FALSE in general (positions change every step)
3. ⋃_n R_n grows monotonically (union of all reachable positions)
4. MixedHitting ↔ ∃n, (-1 : ZMod q) ∈ R_n (hitting = reachable)
-/

section ReachableSet

/-- The set of positions mod q reachable by a valid mixed walk from accumulator acc
    in exactly n steps. A position `a : ZMod q` is in `reachableAt q acc n` if there
    exists a valid mixed selection sigma such that the walk accumulator at step n
    is congruent to `a` mod q. -/
def reachableAt (q acc : ℕ) (n : ℕ) : Set (ZMod q) :=
  {a : ZMod q | ∃ σ : MixedSelection, ValidMixedSelection acc σ ∧
    (mixedWalkProd acc σ n : ZMod q) = a}

/-- The set of all positions mod q reachable at any step by some valid mixed walk. -/
def reachableEver (q acc : ℕ) : Set (ZMod q) :=
  ⋃ n, reachableAt q acc n

/-- At step 0, the only reachable position is the starting accumulator mod q.
    Every walk starts at `acc`, so `reachableAt q acc 0 = {(acc : ZMod q)}`. -/
theorem reachableAt_zero (q acc : ℕ) :
    reachableAt q acc 0 = {(acc : ZMod q)} := by
  ext a
  simp only [reachableAt, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, _, h⟩
    simp [mixedWalkProd] at h
    exact h.symm
  · intro ha
    exact ⟨minFacMixed, minFacMixed_valid acc, by simp [mixedWalkProd, ha]⟩

/-- The reachable set at any step is nonempty: the all-minFac walk always
    provides a witness. -/
theorem reachableAt_nonempty (q acc : ℕ) (n : ℕ) :
    (reachableAt q acc n).Nonempty :=
  ⟨(mixedWalkProd acc minFacMixed n : ZMod q),
   ⟨minFacMixed, minFacMixed_valid acc, rfl⟩⟩

/-- The ever-reachable set is nonempty: step 0 already provides a position. -/
theorem reachableEver_nonempty (q acc : ℕ) :
    (reachableEver q acc).Nonempty := by
  exact Set.nonempty_iUnion.mpr ⟨0, reachableAt_nonempty q acc 0⟩

/-- The standard minFac walk's position at step n is always in the reachable set. -/
theorem minFac_walk_in_reachable (q acc : ℕ) (n : ℕ) :
    (mixedWalkProd acc minFacMixed n : ZMod q) ∈ reachableAt q acc n :=
  ⟨minFacMixed, minFacMixed_valid acc, rfl⟩

/-- **Hitting ↔ Reachable**: A valid walk captures q (i.e., q divides P+1 at
    some step) if and only if -1 mod q is in the reachable set at some step.

    More precisely: for q prime, q >= 5, acc >= 2 with q not dividing acc,
    the existence of a valid walk with q | P(n)+1 is equivalent to
    (-1 : ZMod q) appearing in some reachable set.

    This reformulates the hitting condition as a reachability condition. -/
theorem mixed_hitting_iff_neg_one_reachable (q : ℕ) (acc : ℕ) :
    (∃ (σ : MixedSelection) (n : ℕ),
      ValidMixedSelection acc σ ∧ q ∣ (mixedWalkProd acc σ n + 1))
    ↔ ∃ n, (-1 : ZMod q) ∈ reachableAt q acc n := by
  constructor
  · rintro ⟨σ, n, hv, hdvd⟩
    refine ⟨n, σ, hv, ?_⟩
    have h0 : ((mixedWalkProd acc σ n + 1 : ℕ) : ZMod q) = 0 := by
      rwa [ZMod.natCast_eq_zero_iff]
    have h1 : (mixedWalkProd acc σ n : ZMod q) + 1 = 0 := by
      push_cast at h0; exact h0
    calc (mixedWalkProd acc σ n : ZMod q)
        = (mixedWalkProd acc σ n : ZMod q) + 1 - 1 := by ring
      _ = 0 - 1 := by rw [h1]
      _ = -1 := by ring
  · rintro ⟨n, σ, hv, hmod⟩
    refine ⟨σ, n, hv, ?_⟩
    have h1 : (mixedWalkProd acc σ n : ZMod q) + 1 = 0 := by
      rw [hmod]; ring
    have h2 : ((mixedWalkProd acc σ n + 1 : ℕ) : ZMod q) = 0 := by
      push_cast; exact h1
    rwa [ZMod.natCast_eq_zero_iff] at h2

end ReachableSet

/-! ## Part 22: Reachable Set Growth from Branching

When P+1 is composite, the factor set has ≥ 2 distinct prime factors. If these
give different residues mod q, the reachable set at the next step gains new elements.
We formalize the factor set modulo q and its basic cardinality properties. -/

section FactorSet

/-- The factor set of P+1 modulo q: the set of residues mod q of prime factors
    of P+1 that are different from q. These are the possible "multipliers" for
    the walk at a step where the accumulator is P.

    We filter `Finset.range (P + 2)` by: the value is prime, divides P+1, and is not q. -/
def factorSetModQ (q P : ℕ) : Finset (ZMod q) :=
  ((Finset.range (P + 2)).filter (fun p => p.Prime ∧ p ∣ (P + 1) ∧ p ≠ q)).image
    (fun (p : ℕ) => (p : ZMod q))

/-- minFac(P+1) is always in the factor set (when P ≥ 1 and minFac(P+1) ≠ q).
    Since P ≥ 1, P+1 ≥ 2, so minFac(P+1) is a well-defined prime dividing P+1.
    We also need minFac(P+1) < P+2, which holds since minFac(P+1) ≤ P+1 < P+2. -/
theorem minFac_mem_factorSetModQ {q P : ℕ} (hP : 1 ≤ P)
    (hneq : (P + 1).minFac ≠ q) :
    ((P + 1).minFac : ZMod q) ∈ factorSetModQ q P := by
  apply Finset.mem_image.mpr
  refine ⟨(P + 1).minFac, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, Nat.minFac_prime (by omega), Nat.minFac_dvd _, hneq⟩
  have := Nat.minFac_le (by omega : 0 < P + 1)
  omega

/-- The factor set is nonempty when P ≥ 1 and minFac(P+1) ≠ q:
    minFac(P+1) is always a valid member. -/
theorem factorSetModQ_nonempty {q P : ℕ} (hP : 1 ≤ P)
    (hneq : (P + 1).minFac ≠ q) :
    (factorSetModQ q P).Nonempty :=
  ⟨_, minFac_mem_factorSetModQ hP hneq⟩

/-- When P+1 is composite and P ≥ 1, P+1 has at least two prime factor slots
    (counting multiplicity): minFac(P+1) and a prime factor of the quotient
    (P+1)/minFac(P+1). These may be the SAME prime (e.g. P+1 = p²), but the
    quotient is ≥ 2 and has its own prime factor.

    We prove: there exists a prime p (possibly equal to minFac) with p | (P+1)
    and p | (P+1)/minFac(P+1). -/
theorem not_prime_exists_quotient_factor {P : ℕ} (hP : 1 ≤ P)
    (hnp : ¬(P + 1).Prime) :
    ∃ p, p.Prime ∧ p ∣ (P + 1) ∧ (P + 1).minFac ≤ p := by
  have hmf_lt : (P + 1).minFac < P + 1 :=
    Nat.not_prime_iff_minFac_lt (by omega) |>.mp hnp
  have hdvd : (P + 1).minFac ∣ (P + 1) := Nat.minFac_dvd _
  obtain ⟨c, hc⟩ := hdvd
  have hc_ne_one : c ≠ 1 := by intro heq; rw [heq, mul_one] at hc; omega
  set p := c.minFac
  have hp_prime : p.Prime := Nat.minFac_prime hc_ne_one
  have hp_dvd_c : p ∣ c := Nat.minFac_dvd c
  have hp_dvd : p ∣ (P + 1) := by rw [hc]; exact dvd_mul_of_dvd_right hp_dvd_c _
  have hp_ge : (P + 1).minFac ≤ p :=
    Nat.minFac_le_of_dvd hp_prime.two_le hp_dvd
  exact ⟨p, hp_prime, hp_dvd, hp_ge⟩

/-- When P+1 is composite and P ≥ 1, the quotient (P+1)/minFac(P+1) is at least 2,
    and it has its own prime factor. This gives a second prime dividing P+1 (possibly
    equal to minFac). In fact, the underlying set of primes dividing P+1 has at
    least 2 elements as naturals (but they might be equal, e.g. P+1 = p²). -/
theorem not_prime_quotient_ge_two {P : ℕ} (hP : 1 ≤ P)
    (hnp : ¬(P + 1).Prime) :
    2 ≤ (P + 1) / (P + 1).minFac := by
  have hmf_lt : (P + 1).minFac < P + 1 :=
    Nat.not_prime_iff_minFac_lt (by omega) |>.mp hnp
  have hmf_pos : 0 < (P + 1).minFac := Nat.minFac_pos _
  have hmf_dvd : (P + 1).minFac ∣ (P + 1) := Nat.minFac_dvd _
  obtain ⟨c, hc⟩ := hmf_dvd
  have hc_ne_one : c ≠ 1 := by
    intro heq; rw [heq, mul_one] at hc; omega
  have hmf_ge2 : 2 ≤ (P + 1).minFac :=
    (Nat.minFac_prime (by omega : P + 1 ≠ 1)).two_le
  have hc_ge2 : 2 ≤ c := by
    by_contra h; push Not at h
    interval_cases c <;> omega
  have hdiv_eq : (P + 1) / (P + 1).minFac = c := by
    have : (P + 1).minFac * c / (P + 1).minFac = c :=
      Nat.mul_div_cancel_left c hmf_pos
    rwa [← hc] at this
  omega

end FactorSet

/-! ## Part 24: Reachable Set Growth Properties

The reachable set `reachableAt q acc n` grows as the walk branches. At each step,
any valid walk can be extended by choosing any prime factor of P+1 as the next
multiplier. We formalize:

1. `reachableAt_subset_reachableEver` — R_n ⊆ R_∞ (trivially from union)
2. `reachableAt_from_factor` — given a walk σ reaching P at step n, any prime p
   dividing P+1 yields (P * p : ZMod q) ∈ R_{n+1} (by constructing σ' that
   agrees with σ on [0,n) and chooses p at step n)
3. `reachable_grows_pair` — if P+1 has two distinct prime factors p₁ ≠ p₂
   (both ≠ q), then BOTH (P * p₁ : ZMod q) and (P * p₂ : ZMod q) are in R_{n+1}
4. `reachable_growth_landscape` — summary conjunction

The key construction: given σ valid reaching position a at step n, define
  σ'(k) := if k < n then σ(k) else if k = n then some p else none
Then σ' is valid, agrees with σ on [0,n), and chooses p at step n. -/

section ReachableGrowth

/-- Every position reachable at step n is in the ever-reachable set. -/
theorem reachableAt_subset_reachableEver (q acc : ℕ) (n : ℕ) :
    reachableAt q acc n ⊆ reachableEver q acc :=
  Set.subset_iUnion _ n

/-- The starting position is in the ever-reachable set. -/
theorem acc_mem_reachableEver (q acc : ℕ) :
    (acc : ZMod q) ∈ reachableEver q acc := by
  apply reachableAt_subset_reachableEver q acc 0
  rw [reachableAt_zero]
  exact Set.mem_singleton _

/-- **Core growth lemma**: Given a valid walk σ reaching accumulator P at step n,
    and any prime p with p | P+1, the position (P * p : ZMod q) is reachable
    at step n+1.

    The construction builds σ' that agrees with σ on [0,n), chooses p at step n,
    and uses minFac (none) for all subsequent steps. Validity of σ' follows from:
    - Steps k < n: σ'(k) = σ(k), walk agrees with σ, so validity inherits from hv
    - Step n: σ'(n) = some p, need p prime and p | P+1 (given by hypotheses)
    - Steps k > n: σ'(k) = none, validity is trivially True -/
theorem reachableAt_from_factor {q acc : ℕ} {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ mixedWalkProd acc σ n + 1) :
    (mixedWalkProd acc σ n * p : ZMod q) ∈ reachableAt q acc (n + 1) := by
  -- Define σ': agree with σ on [0,n), use some p at n, none after
  let σ' : MixedSelection := fun k =>
    if k < n then σ k
    else if k = n then some p
    else none
  -- Prefix agreement
  have hpref : ∀ i, i < n → σ' i = σ i :=
    fun i hi => by simp only [σ', if_pos hi]
  -- Walk agreement at step n
  have hwalk_eq : mixedWalkProd acc σ' n = mixedWalkProd acc σ n :=
    mixedWalkProd_depends_on_prefix acc σ' σ n hpref
  -- σ' at step n
  have hsn : σ' n = some p := by
    simp only [σ', show ¬(n < n) from lt_irrefl n, ite_false, ite_true]
  -- Validity of σ'
  have hv' : ValidMixedSelection acc σ' := by
    intro k
    by_cases hlt : k < n
    · -- k < n: σ'(k) = σ(k), walk agrees
      rw [hpref k hlt]
      have hwk : mixedWalkProd acc σ' k = mixedWalkProd acc σ k :=
        mixedWalkProd_depends_on_prefix acc σ' σ k
          (fun i hi => hpref i (by omega))
      have hspec := hv k
      cases hσk : σ k with
      | none => trivial
      | some r =>
        simp only [hσk] at hspec ⊢
        exact ⟨hspec.1, by rw [hwk]; exact hspec.2⟩
    · by_cases heq : k = n
      · subst heq; rw [hsn]; exact ⟨hp, by rw [hwalk_eq]; exact hdvd⟩
      · have : σ' k = none := by
          simp only [σ', if_neg hlt, if_neg heq]
        rw [this]; trivial
  -- Walk at step n+1
  have hstep : mixedWalkProd acc σ' (n + 1) = mixedWalkProd acc σ n * p := by
    rw [mixedWalkProd_succ, hwalk_eq]
    congr 1
    exact mixedWalkFactor_some_eq acc σ' n p hsn
  -- Conclusion: (P * p : ZMod q) ∈ R_{n+1}
  exact ⟨σ', hv', by simp only [hstep, Nat.cast_mul]⟩

/-- The minFac walk's next position is always reachable: since minFac(P+1) is
    prime and divides P+1, the standard walk naturally extends the reachable set. -/
theorem reachableAt_minFac_step (q acc : ℕ) (hacc : 2 ≤ acc) (n : ℕ) :
    (mixedWalkProd acc minFacMixed n *
      (mixedWalkProd acc minFacMixed n + 1).minFac : ZMod q) ∈
    reachableAt q acc (n + 1) := by
  apply reachableAt_from_factor (minFacMixed_valid acc)
  · exact Nat.minFac_prime (by
      have := mixedWalkProd_ge_two acc hacc minFacMixed (minFacMixed_valid acc) n
      omega)
  · exact Nat.minFac_dvd _

/-- **Growth pair**: If the accumulator P at step n (via walk σ) satisfies P+1
    having two prime factors p₁ and p₂ (both dividing P+1), then BOTH
    (P * p₁ : ZMod q) and (P * p₂ : ZMod q) are in R_{n+1}.

    When p₁ and p₂ give distinct residues mod q (i.e., (p₁ : ZMod q) ≠ (p₂ : ZMod q)),
    and (P : ZMod q) is a unit, this means |R_{n+1}| ≥ 2 along this branch.

    This is the mechanism by which composite P+1 causes the reachable set to grow. -/
theorem reachable_grows_pair {q acc : ℕ} {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ)
    {p₁ p₂ : ℕ} (hp₁ : p₁.Prime) (hp₂ : p₂.Prime)
    (hdvd₁ : p₁ ∣ mixedWalkProd acc σ n + 1)
    (hdvd₂ : p₂ ∣ mixedWalkProd acc σ n + 1) :
    (mixedWalkProd acc σ n * p₁ : ZMod q) ∈ reachableAt q acc (n + 1) ∧
    (mixedWalkProd acc σ n * p₂ : ZMod q) ∈ reachableAt q acc (n + 1) :=
  ⟨reachableAt_from_factor hv hp₁ hdvd₁,
   reachableAt_from_factor hv hp₂ hdvd₂⟩

/-- **Composite branching**: When P+1 is composite (P ≥ 1), it has at least
    two prime divisor slots. Together with `reachable_grows_pair`, this shows
    that composite accumulators yield at least two reachable positions at the
    next step (as naturals, though they may collide mod q). -/
theorem reachable_composite_branch {q acc : ℕ} (hacc : 2 ≤ acc) {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ)
    (hnp : ¬(mixedWalkProd acc σ n + 1).Prime) :
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
    p₁ ∣ (mixedWalkProd acc σ n + 1) ∧ p₂ ∣ (mixedWalkProd acc σ n + 1) ∧
    (mixedWalkProd acc σ n + 1).minFac ≤ p₂ ∧
    (mixedWalkProd acc σ n * p₁ : ZMod q) ∈ reachableAt q acc (n + 1) ∧
    (mixedWalkProd acc σ n * p₂ : ZMod q) ∈ reachableAt q acc (n + 1) := by
  set P := mixedWalkProd acc σ n
  have hP : 1 ≤ P := by
    have := mixedWalkProd_ge_two acc hacc σ hv n; omega
  obtain ⟨p₂, hp₂_prime, hp₂_dvd, hp₂_ge⟩ := not_prime_exists_quotient_factor hP hnp
  set p₁ := (P + 1).minFac
  have hp₁_prime : p₁.Prime := Nat.minFac_prime (by omega)
  have hp₁_dvd : p₁ ∣ (P + 1) := Nat.minFac_dvd _
  exact ⟨p₁, p₂, hp₁_prime, hp₂_prime, hp₁_dvd, hp₂_dvd, hp₂_ge,
    reachableAt_from_factor hv hp₁_prime hp₁_dvd,
    reachableAt_from_factor hv hp₂_prime hp₂_dvd⟩

/-- **Reachable-ever growth**: If a ∈ reachableEver and σ witnesses a at step n,
    then for any prime p dividing the walk accumulator + 1, the next position
    (a * p : ZMod q) is also in reachableEver. -/
theorem reachableEver_from_factor {q acc : ℕ} {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ mixedWalkProd acc σ n + 1) :
    (mixedWalkProd acc σ n * p : ZMod q) ∈ reachableEver q acc :=
  reachableAt_subset_reachableEver q acc (n + 1)
    (reachableAt_from_factor hv hp hdvd)

/-- **Reachable set growth landscape**: summary of reachable set growth properties.

    1. reachableAt_subset_reachableEver — R_n ⊆ R_∞
    2. acc_mem_reachableEver — starting position is reachable
    3. reachableAt_from_factor — prime factor branching grows R_{n+1}
    4. reachable_grows_pair — two prime factors give two elements in R_{n+1}
    5. reachable_composite_branch — composite P+1 yields branching -/
theorem reachable_growth_landscape (q acc : ℕ) (hacc : 2 ≤ acc) :
    -- 1. Reachable sets nest into ever-reachable
    (∀ n, reachableAt q acc n ⊆ reachableEver q acc)
    ∧
    -- 2. Starting position is ever-reachable
    ((acc : ZMod q) ∈ reachableEver q acc)
    ∧
    -- 3. Factor branching (existential witness)
    (∀ n (σ : MixedSelection), ValidMixedSelection acc σ →
      ∀ p : ℕ, p.Prime → p ∣ (mixedWalkProd acc σ n + 1) →
      (mixedWalkProd acc σ n * p : ZMod q) ∈ reachableAt q acc (n + 1))
    ∧
    -- 4. Composite branching yields two positions
    (∀ n (σ : MixedSelection), ValidMixedSelection acc σ →
      ¬(mixedWalkProd acc σ n + 1).Prime →
      ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧
        (mixedWalkProd acc σ n * p₁ : ZMod q) ∈ reachableAt q acc (n + 1) ∧
        (mixedWalkProd acc σ n * p₂ : ZMod q) ∈ reachableAt q acc (n + 1)) :=
  ⟨fun n => reachableAt_subset_reachableEver q acc n,
   acc_mem_reachableEver q acc,
   fun n σ hv p hp hdvd => reachableAt_from_factor hv hp hdvd,
   fun n σ hv hnp => by
     obtain ⟨p₁, p₂, hp₁, hp₂, hd₁, hd₂, _, hr₁, hr₂⟩ :=
       reachable_composite_branch hacc hv hnp
     exact ⟨p₁, p₂, hp₁, hp₂, hr₁, hr₂⟩⟩

end ReachableGrowth

/-! ## Part 25: Reachable Set Coset Impossibility

Under MC(< q) (all primes below q appear in the EM sequence) and the assumption
that q itself never appears, the ever-reachable set R_∞(q, 2) is NOT contained
in any proper coset g·H of (ZMod q)ˣ.

The proof uses PrimeResidueEscape (proved elementarily in Bootstrap.lean):
for any proper subgroup H < (ZMod q)ˣ, there exists a prime r ∈ [3, q) with
r mod q ∉ H. By MC(< q), r = seq(k) for some k ≥ 1. Then r | prod(k-1) + 1,
so both prod(k-1) mod q and prod(k-1)·r mod q are in R_∞. Their ratio is
r mod q ∉ H, contradicting R_∞ ⊆ g·H (which forces all ratios into H).
-/

section CosetImpossibility

/-- The standard all-minFac mixed walk from accumulator 2 recovers the EM product.
    Chain: mixedWalkProd_minFac_eq → epsWalkProdFrom_two_eq → epsWalkProd_emDecision. -/
theorem mixedWalkProd_two_minFac_eq_prod (n : ℕ) :
    mixedWalkProd 2 minFacMixed n = prod n := by
  rw [mixedWalkProd_minFac_eq, epsWalkProdFrom_two_eq]
  exact epsWalkProd_emDecision n

/-- Under hne (q never in seq), q does not divide prod(n), hence
    (prod n : ZMod q) is nonzero. -/
private theorem prod_cast_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q) (n : ℕ) : ((prod n : ℕ) : ZMod q) ≠ 0 := by
  intro h
  have hdvd : q ∣ prod n := (ZMod.natCast_eq_zero_iff (prod n) q).mp h
  exact prime_not_in_seq_not_dvd_prod (Fact.out : Nat.Prime q).toIsPrime hne n hdvd

/-- A prime r < q maps to a nonzero element of ZMod q. -/
private theorem natCast_prime_ne_zero' {q r : ℕ} [Fact (Nat.Prime q)]
    (hr : Nat.Prime r) (hrq : r < q) : ((r : ℕ) : ZMod q) ≠ 0 := by
  intro h
  have hdvd : q ∣ r := (ZMod.natCast_eq_zero_iff r q).mp h
  exact absurd (Nat.le_of_dvd hr.pos hdvd) (by omega)

/-- The standard EM walk position at step n is in R_∞(q, 2).
    This is `minFac_walk_in_reachable` lifted to `reachableEver`. -/
private theorem prod_in_reachableEver (q : ℕ) (n : ℕ) :
    (mixedWalkProd 2 minFacMixed n : ZMod q) ∈ reachableEver q 2 :=
  reachableAt_subset_reachableEver q 2 n (minFac_walk_in_reachable q 2 n)

/-- If r is a prime dividing prod(k) + 1, then ((prod k : ℕ) : ZMod q) * (r : ZMod q)
    is in R_∞(q, 2). -/
private theorem prod_mul_prime_in_reachableEver (q : ℕ) {k : ℕ} {r : ℕ}
    (hr : r.Prime) (hdvd : r ∣ prod k + 1) :
    ((prod k : ℕ) : ZMod q) * ((r : ℕ) : ZMod q) ∈ reachableEver q 2 := by
  have hmem := @reachableEver_from_factor q 2 k minFacMixed (minFacMixed_valid 2)
    r hr (by rw [mixedWalkProd_two_minFac_eq_prod]; exact hdvd)
  simp only [mixedWalkProd_two_minFac_eq_prod] at hmem
  exact_mod_cast hmem

/-- Under hne, the product of prod(k) * r mod q is nonzero when r < q is prime. -/
private theorem prod_mul_prime_cast_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q) (k : ℕ) {r : ℕ} (hr : Nat.Prime r) (hrq : r < q) :
    ((prod k * r : ℕ) : ZMod q) ≠ 0 := by
  push_cast
  exact mul_ne_zero (prod_cast_ne_zero hne k) (natCast_prime_ne_zero' hr hrq)

/-- **Escaping prime produces escaping ratio**: Given a prime r ∈ [3, q) from
    PrimeResidueEscape and its index k from MC(< q), both prod(k-1) mod q and
    prod(k-1)·r mod q are in R_∞, and their ratio r mod q is in (ZMod q)ˣ.

    Concretely: if c = prod(k') and c·r are both in R_∞ and both nonzero mod q,
    then (Units.mk0 (c·r) h₁) * (Units.mk0 c h₂)⁻¹ = Units.mk0 r h₃. -/
private theorem ratio_of_reachable_pair {q : ℕ} [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q) (k' : ℕ) {r : ℕ} (hr : Nat.Prime r) (hrq : r < q) :
    Units.mk0 ((prod k' * r : ℕ) : ZMod q) (prod_mul_prime_cast_ne_zero hne k' hr hrq) *
    (Units.mk0 ((prod k' : ℕ) : ZMod q) (prod_cast_ne_zero hne k'))⁻¹ =
    Units.mk0 ((r : ℕ) : ZMod q) (natCast_prime_ne_zero' hr hrq) := by
  ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hc : ((prod k' : ℕ) : ZMod q) ≠ 0 := prod_cast_ne_zero hne k'
  have hcast : ((prod k' * r : ℕ) : ZMod q) = ((prod k' : ℕ) : ZMod q) * ((r : ℕ) : ZMod q) := by
    push_cast; ring
  rw [hcast]
  field_simp

/-- **Reachable ratio escape**: Under MC(< q) and q never in seq, for every
    proper subgroup H < (ZMod q)ˣ, there exist two elements of R_∞(q, 2)
    (both nonzero mod q) whose ratio as units lies outside H.

    Proof: PRE gives r ∈ [3, q) prime with r mod q ∉ H. MC(< q) gives k with
    seq(k) = r. Since k ≥ 1 (as r ≥ 3 ≠ 2 = seq(0)), write k = k' + 1.
    Then r | prod(k') + 1 (by seq_dvd_succ_prod). Both prod(k') mod q and
    prod(k') · r mod q are in R_∞, and their ratio is r mod q ∉ H. -/
theorem reachableEver_ratios_escape_subgroup
    (q : ℕ) [hfact : Fact (Nat.Prime q)] (hq5 : 5 ≤ q)
    (hmc : MCBelow q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ (u₁ u₂ : (ZMod q)ˣ),
      (↑u₁ : ZMod q) ∈ reachableEver q 2 ∧
      (↑u₂ : ZMod q) ∈ reachableEver q 2 ∧
      u₁ * u₂⁻¹ ∉ H := by
  -- Step 1: Get escaping prime from PrimeResidueEscape
  obtain ⟨r, hr_prime, hrq, hr3, hr_escape⟩ := prime_residue_escape q hq5 H hH
  -- Step 2: Get index where r enters the sequence from MC(< q)
  obtain ⟨k, hk⟩ := hmc r hr_prime hrq
  -- Step 3: k ≥ 1 since seq(0) = 2 and r ≥ 3
  have hk_pos : 0 < k := by
    rcases k with _ | k'
    · simp only [seq_zero] at hk; omega
    · omega
  -- Step 4: Write k = k' + 1
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  -- Step 5: seq(k'+1) = r, so r | prod(k') + 1
  have hr_dvd : r ∣ prod k' + 1 := by
    have : seq (k' + 1) ∣ prod k' + 1 := seq_dvd_succ_prod k'
    rwa [hk] at this
  -- Step 6: Construct the two units
  set u₁ : (ZMod q)ˣ := Units.mk0 ((prod k' * r : ℕ) : ZMod q)
    (prod_mul_prime_cast_ne_zero hne k' hr_prime hrq)
  set u₂ : (ZMod q)ˣ := Units.mk0 ((prod k' : ℕ) : ZMod q)
    (prod_cast_ne_zero hne k')
  refine ⟨u₁, u₂, ?_, ?_, ?_⟩
  -- Step 7: u₁ ∈ R_∞ (prod(k') * r mod q is reachable)
  · show ((prod k' * r : ℕ) : ZMod q) ∈ reachableEver q 2
    have := prod_mul_prime_in_reachableEver q hr_prime hr_dvd
    exact_mod_cast this
  -- Step 8: u₂ ∈ R_∞ (prod(k') mod q is reachable)
  · show ((prod k' : ℕ) : ZMod q) ∈ reachableEver q 2
    have := prod_in_reachableEver q k'
    simp only [mixedWalkProd_two_minFac_eq_prod] at this
    exact this
  -- Step 9: u₁ * u₂⁻¹ = r mod q ∉ H
  · rw [ratio_of_reachable_pair hne k' hr_prime hrq]
    exact hr_escape

/-- **Reachable set coset impossibility**: Under MC(< q) and q never in seq,
    the ever-reachable set R_∞(q, 2) is not contained in any left coset g·H
    of a proper subgroup H < (ZMod q)ˣ.

    This means R_∞ cannot be "trapped" in any coset structure, which is a
    key obstruction to algebraic approaches trying to confine the walk.

    Proof: If R_∞ ⊆ g·H, then for any u₁, u₂ ∈ R_∞ we have u₁·u₂⁻¹ ∈ H.
    But `reachableEver_ratios_escape_subgroup` gives u₁, u₂ ∈ R_∞ with
    u₁·u₂⁻¹ ∉ H. Contradiction. -/
theorem reachableEver_not_in_coset
    (q : ℕ) [hfact : Fact (Nat.Prime q)] (hq5 : 5 ≤ q)
    (hmc : MCBelow q) (hne : ∀ k, seq k ≠ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) (g : (ZMod q)ˣ) :
    ¬ (∀ x ∈ reachableEver q 2, ∃ h ∈ H, (x : ZMod q) = ↑(g * h)) := by
  intro hcoset
  -- Get escaping pair from ratio escape
  obtain ⟨u₁, u₂, hu₁, hu₂, hratio⟩ :=
    reachableEver_ratios_escape_subgroup q hq5 hmc hne H hH
  -- Both u₁ and u₂ are in the coset g·H
  obtain ⟨h₁, hh₁, heq₁⟩ := hcoset (↑u₁) hu₁
  obtain ⟨h₂, hh₂, heq₂⟩ := hcoset (↑u₂) hu₂
  -- So u₁ = g·h₁ and u₂ = g·h₂ as units
  have hu₁_eq : u₁ = g * h₁ := Units.ext heq₁
  have hu₂_eq : u₂ = g * h₂ := Units.ext heq₂
  -- Therefore u₁·u₂⁻¹ = (g·h₁)·(g·h₂)⁻¹ = h₁·h₂⁻¹ ∈ H
  -- (using commutativity of (ZMod q)ˣ)
  have : u₁ * u₂⁻¹ = h₁ * h₂⁻¹ := by
    rw [hu₁_eq, hu₂_eq, mul_inv_rev,
        ← mul_assoc (g * h₁) h₂⁻¹ g⁻¹, mul_assoc g h₁ h₂⁻¹,
        mul_assoc g (h₁ * h₂⁻¹) g⁻¹, mul_comm (h₁ * h₂⁻¹) g⁻¹,
        ← mul_assoc g g⁻¹, mul_inv_cancel, one_mul]
  exact hratio (this ▸ H.mul_mem hh₁ (H.inv_mem hh₂))

/-- **Coset impossibility landscape**: summary of the reachable set coset
    impossibility results.

    1. mixedWalkProd_two_minFac_eq_prod — bridge to standard EM product
    2. reachableEver_ratios_escape_subgroup — ratio of two R_∞ elements ∉ H
    3. reachableEver_not_in_coset — R_∞ not contained in any proper coset -/
theorem coset_impossibility_landscape
    (q : ℕ) [hfact : Fact (Nat.Prime q)] (hq5 : 5 ≤ q)
    (hmc : MCBelow q) (hne : ∀ k, seq k ≠ q) :
    -- 1. Bridge: mixed walk from 2 = EM product
    (∀ n, mixedWalkProd 2 minFacMixed n = prod n)
    ∧
    -- 2. Ratio escape: R_∞ ratios escape every proper subgroup
    (∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ →
      ∃ (u₁ u₂ : (ZMod q)ˣ),
        (↑u₁ : ZMod q) ∈ reachableEver q 2 ∧
        (↑u₂ : ZMod q) ∈ reachableEver q 2 ∧
        u₁ * u₂⁻¹ ∉ H)
    ∧
    -- 3. Coset impossibility: R_∞ not in any proper coset
    (∀ (H : Subgroup (ZMod q)ˣ), H ≠ ⊤ → ∀ (g : (ZMod q)ˣ),
      ¬ (∀ x ∈ reachableEver q 2, ∃ h ∈ H, (x : ZMod q) = ↑(g * h))) :=
  ⟨mixedWalkProd_two_minFac_eq_prod,
   fun H hH => reachableEver_ratios_escape_subgroup q hq5 hmc hne H hH,
   fun H hH g => reachableEver_not_in_coset q hq5 hmc hne H hH g⟩

end CosetImpossibility

/-! ## Part 26: Factor Confinement and Sieve Obstruction

This section formalizes the **factor confinement** principle: if the reachable set
R_∞(q, acc) is proper (i.e., not all of ZMod q), then the prime factors of every
reachable Euclid number are constrained to lie in a specific "allowed" subset of
residues mod q.

### Key results

* `allowedFactors` — the set of residues m such that c * m ∈ R for a given position c
* `AllFactorsInSet` — predicate: every prime factor of N has its residue in a set F
* `factor_confinement` — every prime factor of a reachable Euclid number is in the
  allowed set (immediate from `reachableEver_from_factor`)
* `all_factors_confined` — all prime factors of P+1 are confined when P is reachable
* `standard_euclid_factors_confined` — specialization to the standard EM walk
* `forbidden_nonempty_of_unit` — if c is a unit and R ≠ univ, the forbidden set
  is nonempty (since multiplication by a unit is bijective)
* `FactorEscapeHypothesis` — open hypothesis: EM Euclid numbers escape any proper
  factor confinement
* `factor_escape_implies_mixed_hitting` — FactorEscapeHypothesis + MC(< q) ⇒
  MixedHitting at q (the chain: confinement + escape = contradiction)

### Connection to sieve theory

Factor confinement is the formal obstruction that a sieve-theoretic approach must
overcome: if the walk's reachable set were to stabilize at a proper subset, every
Euclid number's factors would be sieved out of the forbidden residues — a constraint
that becomes increasingly difficult to satisfy as the numbers grow.
-/

section FactorConfinement

/-- The set of "allowed" factor residues at walk position c in ZMod q,
    given a target set R. A residue m is allowed if c * m ∈ R. -/
def allowedFactors (q : ℕ) (c : ZMod q) (R : Set (ZMod q)) : Set (ZMod q) :=
  {m : ZMod q | c * m ∈ R}

/-- The complement: residues m such that c * m ∉ R. -/
def forbiddenFactors (q : ℕ) (c : ZMod q) (R : Set (ZMod q)) : Set (ZMod q) :=
  {m : ZMod q | c * m ∉ R}

/-- An integer N is factor-confined to a set F ⊆ ZMod q if every prime factor
    of N has its residue mod q in F. -/
def AllFactorsInSet (q : ℕ) (N : ℕ) (F : Set (ZMod q)) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → (p : ZMod q) ∈ F

/-- Allowed and forbidden partition ZMod q. -/
theorem allowed_union_forbidden (q : ℕ) (c : ZMod q) (R : Set (ZMod q)) :
    allowedFactors q c R ∪ forbiddenFactors q c R = Set.univ := by
  ext m; simp only [allowedFactors, forbiddenFactors, Set.mem_union, Set.mem_ofPred_eq,
    Set.mem_univ, iff_true]; tauto

/-- Allowed and forbidden are disjoint. -/
theorem allowed_inter_forbidden (q : ℕ) (c : ZMod q) (R : Set (ZMod q)) :
    allowedFactors q c R ∩ forbiddenFactors q c R = ∅ := by
  ext m; simp [allowedFactors, forbiddenFactors]

/-- **Factor confinement**: every prime factor of a reachable Euclid number
    P + 1 has its residue in the allowed factor set at position P mod q.

    Proof: `reachableEver_from_factor` shows P * p mod q ∈ R_∞ whenever
    p is prime and p ∣ P + 1. The definition of `allowedFactors` is exactly
    {m | c * m ∈ R}, so (p : ZMod q) ∈ allowedFactors. -/
theorem factor_confinement {q acc : ℕ} {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ mixedWalkProd acc σ n + 1) :
    (p : ZMod q) ∈ allowedFactors q (mixedWalkProd acc σ n : ZMod q)
      (reachableEver q acc) := by
  exact @reachableEver_from_factor q acc n σ hv p hp hdvd

/-- All prime factors of a reachable Euclid number are confined to the
    allowed set at the walk position. -/
theorem all_factors_confined {q acc : ℕ} {n : ℕ}
    {σ : MixedSelection} (hv : ValidMixedSelection acc σ) :
    AllFactorsInSet q (mixedWalkProd acc σ n + 1)
      (allowedFactors q (mixedWalkProd acc σ n : ZMod q) (reachableEver q acc)) :=
  fun _ hp hdvd => factor_confinement hv hp hdvd

/-- Standard walk specialization: all prime factors of every standard Euclid
    number prod(n) + 1 are confined to the allowed set at the walk position. -/
theorem standard_euclid_factors_confined (q : ℕ) (n : ℕ) :
    AllFactorsInSet q (mixedWalkProd 2 minFacMixed n + 1)
      (allowedFactors q (mixedWalkProd 2 minFacMixed n : ZMod q)
        (reachableEver q 2)) :=
  all_factors_confined (minFacMixed_valid 2)

/-- Via the bridge `mixedWalkProd_two_minFac_eq_prod`: all prime factors of
    prod(n) + 1 are confined to the allowed set at the walk position. -/
theorem standard_euclid_factors_confined' (q : ℕ) (n : ℕ) :
    AllFactorsInSet q (prod n + 1)
      (allowedFactors q ((prod n : ℕ) : ZMod q) (reachableEver q 2)) := by
  have h := standard_euclid_factors_confined q n
  rw [mixedWalkProd_two_minFac_eq_prod] at h
  exact h

/-- If c is a unit and R ⊊ Set.univ, the forbidden factor set is nonempty.

    Proof: since c is a unit, left multiplication by c is a bijection on ZMod q.
    If R ≠ univ, there exists x ∉ R. Setting m = c⁻¹ * x gives c * m = x ∉ R,
    so m ∈ forbiddenFactors. -/
theorem forbidden_nonempty_of_unit {q : ℕ} [NeZero q]
    {c : ZMod q} (hc : IsUnit c)
    {R : Set (ZMod q)} (hR : R ≠ Set.univ) :
    (forbiddenFactors q c R).Nonempty := by
  rw [Set.ne_univ_iff_exists_notMem] at hR
  obtain ⟨x, hx⟩ := hR
  obtain ⟨u, rfl⟩ := hc
  refine ⟨↑u⁻¹ * x, ?_⟩
  show ↑u * (↑u⁻¹ * x) ∉ R
  rw [Units.mul_inv_cancel_left]
  exact hx

/-- If c is a unit and R ⊊ Set.univ, the allowed factor set is proper.
    Contrapositive of `forbidden_nonempty_of_unit`. -/
theorem allowed_ne_univ_of_unit {q : ℕ} [NeZero q]
    {c : ZMod q} (hc : IsUnit c)
    {R : Set (ZMod q)} (hR : R ≠ Set.univ) :
    allowedFactors q c R ≠ Set.univ := by
  intro hall
  have ⟨m, hm⟩ := forbidden_nonempty_of_unit hc hR
  have := Set.mem_univ m
  rw [← hall] at this
  exact hm this

/-- `AllFactorsInSet` is monotone in the target set: if F ⊆ G and all factors
    of N are in F, then all factors of N are in G. -/
theorem allFactorsInSet_mono {q N : ℕ} {F G : Set (ZMod q)} (h : F ⊆ G) :
    AllFactorsInSet q N F → AllFactorsInSet q N G :=
  fun hF p hp hdvd => h (hF p hp hdvd)

/-- `AllFactorsInSet` for 1 is vacuously true (1 has no prime factors). -/
theorem allFactorsInSet_one {q : ℕ} {F : Set (ZMod q)} :
    AllFactorsInSet q 1 F :=
  fun p hp hdvd => absurd (Nat.le_of_dvd Nat.one_pos hdvd) (by have := hp.two_le; omega)

/-! ### Factor Escape Hypothesis -/

/-- **Factor Escape Hypothesis**: The standard EM walk's Euclid numbers do not
    eventually have ALL prime factors confined to any proper subset of residues.

    Formally: for any step-dependent family of proper sets F(n) ⊊ ZMod q,
    the Euclid numbers prod(n) + 1 are not eventually all-factors-confined to F(n).

    This captures the sieve-theoretic content: the EM sequence's Euclid numbers
    produce prime factors in every residue class, not just a proper subset. -/
def FactorEscapeHypothesis (q : ℕ) : Prop :=
  ∀ (F : ℕ → Set (ZMod q)),
    (∀ n, F n ≠ Set.univ) →
    ¬(∃ N₀, ∀ n ≥ N₀, AllFactorsInSet q (prod n + 1) (F n))

/-- Under MC(< q) and q never in seq, the walk position prod(n) mod q is
    nonzero in ZMod q. (Restated from CosetImpossibility section.) -/
private theorem walk_pos_ne_zero' {q : ℕ} [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q) (n : ℕ) :
    ((prod n : ℕ) : ZMod q) ≠ 0 := by
  intro h
  have hdvd : q ∣ prod n := (ZMod.natCast_eq_zero_iff (prod n) q).mp h
  exact prime_not_in_seq_not_dvd_prod (Fact.out : Nat.Prime q).toIsPrime hne n hdvd

/-- Under MC(< q) and q never in seq, the walk position is a unit in ZMod q.
    Uses the fact that ZMod p is a field for prime p, so nonzero implies unit. -/
private theorem walk_pos_isUnit {q : ℕ} [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q) (n : ℕ) :
    IsUnit ((prod n : ℕ) : ZMod q) :=
  IsUnit.mk0 _ (walk_pos_ne_zero' hne n)

/-- **Factor escape implies mixed hitting**: If the FactorEscapeHypothesis holds
    at q, and MC(< q) and q never appears in seq, then -1 ∈ R_∞(q, 2),
    which means there exists a valid mixed walk capturing q.

    Proof by contradiction: Suppose -1 ∉ R_∞. Then R_∞ ≠ Set.univ.
    Factor confinement gives: for all n, every prime factor of prod(n) + 1
    is in allowedFactors(prod(n) mod q, R_∞). Since prod(n) mod q is a unit
    (from hne) and R_∞ ≠ univ, each allowedFactors set is proper (by
    `allowed_ne_univ_of_unit`). This contradicts FactorEscapeHypothesis. -/
theorem factor_escape_implies_mixed_hitting
    (q : ℕ) [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q)
    (hFE : FactorEscapeHypothesis q) :
    (-1 : ZMod q) ∈ reachableEver q 2 := by
  by_contra h_not_neg_one
  -- R_∞ ≠ Set.univ since -1 ∉ R_∞
  have hR_ne : reachableEver q 2 ≠ Set.univ := by
    intro heq
    exact h_not_neg_one (heq ▸ Set.mem_univ _)
  -- Define F(n) = allowedFactors at walk position prod(n)
  let F : ℕ → Set (ZMod q) := fun n =>
    allowedFactors q ((prod n : ℕ) : ZMod q) (reachableEver q 2)
  -- Each F(n) is proper: prod(n) is a unit and R_∞ ≠ univ
  have hF_proper : ∀ n, F n ≠ Set.univ := by
    intro n
    exact allowed_ne_univ_of_unit (walk_pos_isUnit hne n) hR_ne
  -- Factor confinement gives AllFactorsInSet for all n (with N₀ = 0)
  have hconf : ∃ N₀, ∀ n ≥ N₀, AllFactorsInSet q (prod n + 1) (F n) :=
    ⟨0, fun n _ => standard_euclid_factors_confined' q n⟩
  -- Contradiction with FactorEscapeHypothesis
  exact hFE F hF_proper hconf

/-- **Factor escape implies reachable set is full**: Under q never in seq,
    FactorEscapeHypothesis forces R_∞(q, 2) = Set.univ.

    Proof: if R_∞ ≠ univ, factor confinement + walk_pos_isUnit give each
    allowedFactors set proper, contradicting FactorEscapeHypothesis. -/
theorem factor_escape_implies_reachable_full
    (q : ℕ) [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q)
    (hFE : FactorEscapeHypothesis q) :
    reachableEver q 2 = Set.univ := by
  by_contra hR_ne
  let F : ℕ → Set (ZMod q) := fun n =>
    allowedFactors q ((prod n : ℕ) : ZMod q) (reachableEver q 2)
  have hF_proper : ∀ n, F n ≠ Set.univ :=
    fun n => allowed_ne_univ_of_unit (walk_pos_isUnit hne n) hR_ne
  have hconf : ∃ N₀, ∀ n ≥ N₀, AllFactorsInSet q (prod n + 1) (F n) :=
    ⟨0, fun n _ => standard_euclid_factors_confined' q n⟩
  exact hFE F hF_proper hconf

/-- **Factor escape implies mixed MC at q**: combining with the hitting ↔ reachable
    bridge, FactorEscapeHypothesis gives a valid mixed walk capturing q. -/
theorem factor_escape_implies_mixed_mc_at
    (q : ℕ) [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q)
    (hFE : FactorEscapeHypothesis q) :
    ∃ (σ : MixedSelection) (n : ℕ),
      ValidMixedSelection 2 σ ∧ q ∣ (mixedWalkProd 2 σ n + 1) := by
  rw [mixed_hitting_iff_neg_one_reachable]
  have hmem := factor_escape_implies_mixed_hitting q hne hFE
  rw [reachableEver, Set.mem_iUnion] at hmem
  exact hmem

/-! ### Confinement strength: factor confinement constrains ALL walks -/

/-- Factor confinement for arbitrary valid walks (not just minFac): if σ is any
    valid walk from acc, every prime factor of the Euclid number at step n is
    in the allowed set at the walk position. -/
theorem factor_confinement_arbitrary {q acc : ℕ} {n : ℕ}
    (σ : MixedSelection) (hv : ValidMixedSelection acc σ)
    (p : ℕ) (hp : p.Prime) (hdvd : p ∣ mixedWalkProd acc σ n + 1) :
    (p : ZMod q) ∈ allowedFactors q (mixedWalkProd acc σ n : ZMod q)
      (reachableEver q acc) :=
  factor_confinement hv hp hdvd

/-- The reachable set is closed under allowed factor multiplication: if c ∈ R_∞
    and m ∈ allowedFactors(c, R_∞), then c * m ∈ R_∞ (tautological from the
    definition, but worth stating). -/
theorem reachable_closed_under_allowed {q acc : ℕ}
    {c : ZMod q} (_ : c ∈ reachableEver q acc)
    {m : ZMod q} (hm : m ∈ allowedFactors q c (reachableEver q acc)) :
    c * m ∈ reachableEver q acc :=
  hm

/-- **Factor confinement landscape**: summary of the factor confinement results.

    1. factor_confinement — prime factors of reachable Euclid numbers are confined
    2. standard_euclid_factors_confined' — specialization to standard EM walk
    3. forbidden_nonempty_of_unit — forbidden set nonempty when R ⊊ univ and c is unit
    4. allowed_ne_univ_of_unit — allowed set proper when R ⊊ univ and c is unit
    5. factor_escape_implies_mixed_hitting — FEH ⇒ -1 ∈ R_∞
    6. factor_escape_implies_reachable_full — FEH ⇒ R_∞ = univ -/
theorem factor_confinement_landscape
    (q : ℕ) [hfact : Fact (Nat.Prime q)]
    (hne : ∀ k, seq k ≠ q)
    (hFE : FactorEscapeHypothesis q) :
    -- 1. Factor confinement: all factors of prod(n)+1 are confined
    (∀ n, AllFactorsInSet q (prod n + 1)
      (allowedFactors q ((prod n : ℕ) : ZMod q) (reachableEver q 2)))
    ∧
    -- 2. Walk positions are units
    (∀ n, IsUnit ((prod n : ℕ) : ZMod q))
    ∧
    -- 3. Factor escape gives -1 ∈ R_∞
    ((-1 : ZMod q) ∈ reachableEver q 2)
    ∧
    -- 4. Factor escape gives R_∞ = univ
    (reachableEver q 2 = Set.univ)
    ∧
    -- 5. Factor escape gives mixed MC at q
    (∃ (σ : MixedSelection) (n : ℕ),
      ValidMixedSelection 2 σ ∧ q ∣ (mixedWalkProd 2 σ n + 1)) :=
  ⟨standard_euclid_factors_confined' q,
   walk_pos_isUnit hne,
   factor_escape_implies_mixed_hitting q hne hFE,
   factor_escape_implies_reachable_full q hne hFE,
   factor_escape_implies_mixed_mc_at q hne hFE⟩

end FactorConfinement
