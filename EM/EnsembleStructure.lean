import EM.PopulationTransferStrategy
import EM.SDDSBridge

/-!
# Ensemble Structure: Structural Properties of Generalized EM Sequences

This file extends the generalized EM sequence infrastructure from
`ReciprocalSumDivergence.lean` with structural properties needed for
the ensemble averaging framework (Steps 6–10 of the master proof strategy).

## New Results

### Divisibility and Growth
* `genProd_dvd_genProd`       — genProd n k ∣ genProd n (k + j) (PROVED)
* `genSeq_dvd_genProd_later`  — genSeq n k ∣ genProd n (k + 1 + j) (PROVED)
* `genProd_strict_mono`       — genProd n k < genProd n (k + 1) when n ≥ 1 (PROVED)

### Distinctness
* `genSeq_ne_of_lt`           — genSeq n j ≠ genSeq n k when j < k, n sqfree (PROVED)
* `genSeq_injective`          — genSeq n is injective when n is squarefree (PROVED)

### Connection to Standard EM
* `genProd_two_eq_prod`       — genProd 2 k = prod k for all k (PROVED)
* `genSeq_two_eq_seq_succ`    — genSeq 2 k = seq (k + 1) for all k (PROVED)

### DSL-Hitting (Weaker Variant)
* `DSLHitting`                — PE → DH (weaker than DSL, sufficient for MC)
* `pe_dsl_hitting_implies_mc` — PE + DSLHitting → MC (PROVED)
* `equidist_dsl_hitting_implies_mc` — MinFacResidueEquidist + DSLHitting → MC (PROVED)
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Divisibility Structure -/

section Divisibility

/-- The generalized accumulator divides all later accumulators:
    genProd n k ∣ genProd n (k + j) for all j. This follows from the
    recurrence genProd n (k+1) = genProd n k * genSeq n k. -/
theorem genProd_dvd_genProd (n k j : Nat) : genProd n k ∣ genProd n (k + j) := by
  induction j with
  | zero => exact dvd_refl _
  | succ j ih =>
    rw [show k + (j + 1) = (k + j) + 1 from by omega, genProd_succ]
    exact dvd_mul_of_dvd_left ih _

/-- Each generalized EM prime divides all later accumulators:
    genSeq n k ∣ genProd n (k + 1 + j) for all j. This is because
    genSeq n k divides genProd n (k+1) = genProd n k * genSeq n k,
    and genProd n (k+1) divides genProd n (k+1+j). -/
theorem genSeq_dvd_genProd_later (n k j : Nat) :
    genSeq n k ∣ genProd n (k + 1 + j) := by
  have h : genSeq n k ∣ genProd n (k + 1) := by
    rw [genProd_succ]; exact dvd_mul_left _ _
  exact dvd_trans h (genProd_dvd_genProd n (k + 1) j)

end Divisibility

/-! ## Monotonicity -/

section Monotonicity

/-- The generalized accumulator is strictly increasing: genProd n k < genProd n (k+1)
    whenever n ≥ 1. Since genProd n (k+1) = genProd n k * genSeq n k and
    genSeq n k ≥ 2 (prime), the accumulator at least doubles at each step. -/
theorem genProd_strict_mono {n : Nat} (hn : 1 ≤ n) (k : Nat) :
    genProd n k < genProd n (k + 1) := by
  rw [genProd_succ]
  exact lt_mul_of_one_lt_right
    (by have := genProd_pos hn k; omega)
    (by have := (genSeq_prime hn k).two_le; omega)

end Monotonicity

/-! ## Distinctness of Generalized EM Primes -/

section Distinctness

/-- Generalized EM primes at different steps are distinct: if j < k and n is
    squarefree, then genSeq n j ≠ genSeq n k.

    Proof: genSeq n j divides genProd n (j+1), which divides genProd n k
    (by `genSeq_dvd_genProd_later` and `genProd_dvd_genProd`). But genSeq n k
    is coprime to genProd n k (by `genSeq_coprime_genProd`). If genSeq n j
    equalled genSeq n k, then genSeq n j would both divide and be coprime to
    genProd n k, forcing genSeq n j ∣ 1, contradicting primality. -/
theorem genSeq_ne_of_lt {n : Nat} (hn : Squarefree n) {j k : Nat} (hjk : j < k) :
    genSeq n j ≠ genSeq n k := by
  have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero (Squarefree.ne_zero hn)
  intro heq
  -- genSeq n j divides genProd n k (since j + 1 ≤ k)
  have h_dvd : genSeq n j ∣ genProd n k := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hjk)
    rw [hd]; exact genSeq_dvd_genProd_later n j d
  -- genSeq n k is coprime to genProd n k; substituting gives coprimality for j
  have h_cop : Nat.Coprime (genSeq n j) (genProd n k) := by
    rw [heq]; exact genSeq_coprime_genProd hn_pos k
  -- genSeq n j divides gcd(genSeq n j, genProd n k) = 1
  have h_dvd_gcd : genSeq n j ∣ Nat.gcd (genSeq n j) (genProd n k) :=
    Nat.dvd_gcd dvd_rfl h_dvd
  rw [h_cop] at h_dvd_gcd
  -- genSeq n j ∣ 1 but genSeq n j ≥ 2 (prime): contradiction
  exact absurd (Nat.le_of_dvd one_pos h_dvd_gcd)
    (by linarith [(genSeq_prime hn_pos j).two_le])

/-- The generalized EM sequence from a squarefree starting point is injective:
    distinct steps always produce distinct primes. -/
theorem genSeq_injective {n : Nat} (hn : Squarefree n) :
    Function.Injective (genSeq n) := by
  intro j k hjk
  by_contra h
  have : j < k ∨ k < j := by omega
  rcases this with h' | h'
  · exact genSeq_ne_of_lt hn h' hjk
  · exact genSeq_ne_of_lt hn h' hjk.symm

end Distinctness

/-! ## Connection to Standard EM Sequence -/

section StandardConnection

/-- The generalized accumulator from starting point 2 equals the standard
    EM accumulator at every step: genProd 2 k = prod k.

    This connects the ensemble framework (which averages over starting points)
    to the standard EM sequence (starting from n = 2), ensuring that ensemble
    results about "almost all squarefree starting points" include the
    specific trajectory relevant to Mullin's Conjecture.

    The proof is by induction, using `euclid_minFac_eq_nat_minFac` to bridge
    the two implementations of minFac (Euclid.minFac in MullinDefs and
    Nat.minFac in ReciprocalSumDivergence). -/
theorem genProd_two_eq_prod (k : Nat) : genProd 2 k = prod k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    -- First prove the genSeq connection at step k
    have h_seq : genSeq 2 k = seq (k + 1) := by
      rw [genSeq_def, ih]
      -- Goal: Nat.minFac (prod k + 1) = seq (k + 1)
      -- seq (k+1) is definitionally Euclid.minFac (prod k + 1)
      exact (euclid_minFac_eq_nat_minFac _
        (by have := prod_ge_two k; omega)).symm
    -- Now close: genProd 2 (k+1) = genProd 2 k * genSeq 2 k
    --          = prod k * seq (k+1) = prod (k+1)
    rw [genProd_succ, prod_succ, ih, h_seq]

/-- The generalized EM primes from starting point 2 equal the standard EM
    sequence shifted by 1: genSeq 2 k = seq (k + 1).

    This says: the k-th prime produced by the generalized construction starting
    from 2 is exactly the (k+1)-th term of the Euclid-Mullin sequence. -/
theorem genSeq_two_eq_seq_succ (k : Nat) : genSeq 2 k = seq (k + 1) := by
  rw [genSeq_def, genProd_two_eq_prod]
  exact (euclid_minFac_eq_nat_minFac _
    (by have := prod_ge_two k; omega)).symm

end StandardConnection

/-! ## DSL-Hitting: A Weaker Form of DSL -/

section DSLHitting

/-- **DSL-Hitting**: Population Equidistribution implies Dynamical Hitting.

    This is a weaker form of `DeterministicStabilityLemma` (= PE → CME): rather
    than requiring full conditional equidistribution of the multipliers, it
    only asks that the walk hits −1 mod q (sufficient for MC via the
    `dynamical_hitting_implies_mullin` reduction in EquidistBootstrap.lean).

    DSLHitting is sufficient for MC because:
    - DynamicalHitting → MC (proved in EquidistBootstrap.lean)
    - PE is provable from standard ANT (pe_of_equidist in PopulationEquidistProof.lean)

    The three structural conditions that support DSLHitting are the same
    as for DSL:
    1. **Generation** (SubgroupEscape, PROVED): multipliers generate (ℤ/qℤ)×
    2. **Position-blindness** (crt_multiplier_invariance, PROVED): minFac is q-blind
    3. **Population support** (PE, from standard ANT): every residue class
       has positive density of minFac values

    **Value:** DSLHitting is strictly weaker than DSL and may be more
    accessible to prove. DSL requires quantitative equidistribution
    (character sum cancellation), while DSLHitting only needs the walk
    to visit −1 at least once — a qualitative property. -/
def DSLHitting : Prop := PopulationEquidist → DynamicalHitting

/-- **PE + DSLHitting → MC.** The reduction chain with DSLHitting as the
    sole gap: PE → (by DSLHitting) DH → MC. -/
theorem pe_dsl_hitting_implies_mc
    (hpe : PopulationEquidist) (hdsl : DSLHitting) :
    MullinConjecture :=
  dynamical_hitting_implies_mullin (hdsl hpe)

/-- **MinFacResidueEquidist + DSLHitting → MC.** The full chain from standard
    analytic number theory: MinFacResidueEquidist → PE → (by DSLHitting) DH → MC. -/
theorem equidist_dsl_hitting_implies_mc
    (h_equidist : ∀ (q : Nat), Nat.Prime q → MinFacResidueEquidist q)
    (hdsl : DSLHitting) :
    MullinConjecture :=
  pe_dsl_hitting_implies_mc (pe_of_equidist h_equidist) hdsl

end DSLHitting

/-! ## Hierarchy of Open Hypotheses

The open hypotheses form a strict hierarchy:

```
DSL (PE → CME)          — strongest: full conditional equidistribution
  ↓ (implies)
DSLHitting (PE → DH)    — weaker: walk hits −1 mod q
  ↓ (implies MC)
MullinConjecture        — the target
```

Both DSL and DSLHitting give MC with PE provable from standard ANT
(via `pe_of_equidist`). The hierarchy is:

- `pe_dsl_implies_mc` (PopulationTransferStrategy.lean): PE + DSL → MC
- `pe_dsl_hitting_implies_mc` (this file): PE + DSLHitting → MC

DSL is strictly stronger: CME gives character sum cancellation, which implies
both CCSB (the character sum bound) and DH (hitting −1). DSLHitting only
gives the hitting property.

### Why DSLHitting may be easier to prove

DSL requires |∑ χ(m_n)| = o(N) for all nontrivial characters — a quantitative
bound on correlations. DSLHitting only requires ∃ n, q ∣ prod(n)+1 — an
existential statement. The three structural conditions (generation, position-
blindness, population support) are the same for both.

For the specific EM walk:
- The ensemble framework (PopulationTransferStrategy.lean) shows that for
  almost all squarefree starting points, equidistribution holds.
- The structural properties proved in this file (distinctness, injectivity,
  connection to standard EM) provide the infrastructure for transferring
  ensemble results to the specific trajectory.
-/

end
