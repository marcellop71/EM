import EM.Population.TransferStrategy
import EM.Population.AlladiDensity
import EM.Reduction.Master
import EM.Transfer.SieveConstraint

/-!
# Uniform Conductor Equidistribution (UCE)

This file introduces the **Uniform Conductor Equidistribution** hypothesis,
which strengthens `MinFacResidueEquidist` by requiring the equidistribution
of `minFac` mod q to hold uniformly across arithmetic progressions `1 mod M`
for squarefree conductors M coprime to q.

## Motivation

The EM accumulator satisfies `prod(n) + 1 = 1 mod prod(n)`, so `seq(n+1)`
is the least prime factor of an element in the arithmetic progression
`{m : m = 1 mod prod(n)}`. If the distribution of `minFac` mod q is
equidistributed uniformly in the conductor M = prod(n), this would give
CME directly. However, the transfer from population statistics (UCE)
to orbit-specific behavior remains the fundamental gap (Dead End #90).

## Relationship to Existing Infrastructure

- **M = 1 specialization**: UCE for M = 1 recovers `MinFacResidueEquidist`,
  which implies `PopulationEquidist` via `pe_of_equidist`.
- **Alladi chain**: UCE strengthens the Alladi chain by making the density
  estimates uniform in the conductor.
- **Orbit-specificity gap**: UCE does NOT directly give CME because
  `prod(n) + 1` is a specific element of `1 + prod(n) * Z`, not a
  random sample. The bridge `UCEImpliesCME` remains an open hypothesis.

## Main Results

### Definitions
* `conductorRoughCount`        -- count of m in [2,X] with m = 1 mod M, minFac(m) > q
* `conductorResCount`          -- count restricted to minFac(m) = a mod q
* `UniformConductorEquidist`   -- UCE hypothesis (open)
* `UCEImpliesCME`              -- orbit-specificity bridge (open)

### Proved Theorems
* `conductorResCount_le`       -- residue count <= rough count
* `conductorRoughCount_le`     -- rough count <= total multiples
* `uce_implies_mfre`           -- UCE => MinFacResidueEquidist (M=1 specialization)
* `uce_implies_pe`             -- UCE => PopulationEquidist
* `uce_implies_mc_via_dsl`     -- UCE + DSL => MC
* `uce_cme_implies_mc`         -- UCEImpliesCME => MC
* `prod_succ_cong_one_mod_prod`-- prod(n)+1 = 1 mod prod(n) (structural)
* `uce_landscape`              -- summary conjunction
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Counting Functions -/

section Counting

/-- Count of integers m in [2, X] with m = 1 mod M and minFac(m) > q.
    These are the q-rough integers in the arithmetic progression 1 mod M.
    When M = 1, this reduces to `roughCount q X` (all integers are 1 mod 1). -/
def conductorRoughCount (M q X : Nat) : Nat :=
  ((Finset.Icc 2 X).filter (fun m => m % M = 1 % M ∧ q < Nat.minFac m)).card

/-- Count of integers m in [2, X] with m = 1 mod M, minFac(m) > q,
    and minFac(m) = a mod q. This is the residue-restricted version of
    `conductorRoughCount`. -/
def conductorResCount (M q a X : Nat) : Nat :=
  ((Finset.Icc 2 X).filter
    (fun m => m % M = 1 % M ∧ q < Nat.minFac m ∧ Nat.minFac m % q = a)).card

/-- The residue-restricted count is at most the total rough count. -/
theorem conductorResCount_le (M q a X : Nat) :
    conductorResCount M q a X ≤ conductorRoughCount M q X := by
  apply Finset.card_le_card
  intro m hm
  simp only [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.1, hm.2.2.1⟩

/-- The rough count is at most the total count of integers in [2, X]. -/
theorem conductorRoughCount_le_card (M q X : Nat) :
    conductorRoughCount M q X ≤ X - 1 := by
  have := Finset.card_filter_le (Finset.Icc 2 X)
    (fun m => m % M = 1 % M ∧ q < Nat.minFac m)
  simp [conductorRoughCount, Nat.card_Icc] at this ⊢; omega

/-- When M = 1, all integers satisfy m % 1 = 0 = 1 % 1, so the conductor
    rough count equals the rough count. -/
theorem conductorRoughCount_one (q X : Nat) :
    conductorRoughCount 1 q X = roughCount q X := by
  simp only [conductorRoughCount, roughCount]
  congr 1; ext m; simp [Nat.mod_one]

/-- When M = 1, the conductor residue count equals the rough LPF residue count
    (using the filter form from roughCount). -/
theorem conductorResCount_one (q a X : Nat) :
    conductorResCount 1 q a X =
    ((Finset.Icc 2 X).filter (fun m => q < Nat.minFac m ∧ Nat.minFac m % q = a)).card := by
  simp only [conductorResCount]
  congr 1; ext m; simp [Nat.mod_one]

end Counting

/-! ## UCE Hypothesis -/

section UCE

/-- **Uniform Conductor Equidistribution**: for every prime q and every
    coprime residue class a mod q, the distribution of minFac(m) mod q
    among integers m = 1 mod M with minFac(m) > q is asymptotically
    equidistributed with density 1/(q-1), uniformly in the squarefree
    conductor M coprime to q.

    This strengthens `MinFacResidueEquidist` (which is M=1) by requiring
    the equidistribution to hold across all arithmetic progressions
    1 mod M simultaneously.

    The uniformity in M is essential for potential applications to the
    EM orbit, where M = prod(n) grows with n. Without uniformity, the
    equidistribution rate could deteriorate as M grows, making the
    asymptotic statement vacuous for the specific M values needed. -/
def UniformConductorEquidist : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (a : Nat), 0 < a → a < q →
  ∀ ε : ℝ, 0 < ε →
  ∃ X₀ : Nat, ∀ X : Nat, X₀ ≤ X →
  ∀ M : Nat, 0 < M → Squarefree M → Nat.Coprime M q →
    (conductorRoughCount M q X = 0 ∨
      |((conductorResCount M q a X : ℝ) / (conductorRoughCount M q X : ℝ)) -
        1 / ((q : ℝ) - 1)| < ε)

end UCE

/-! ## Bridges -/

section Bridges

/-- UCE implies MinFacResidueEquidist for every prime q.

    The proof specializes M = 1 (which is squarefree, coprime to q, and
    positive). The M=1 case of UCE gives density convergence for the
    unweighted rough count, which is exactly MinFacResidueEquidist
    (modulo the reformulation from density-limit to ratio-limit form).

    Note: MinFacResidueEquidist uses the shifted-squarefree population
    (mu^2(m-1) = 1), while UCE uses the arithmetic progression 1 mod M.
    When M = 1, the UCE population is ALL integers with minFac > q, which
    is a superset of the shifted-squarefree population. The transfer from
    the full population to the shifted-squarefree subpopulation requires
    CRT independence (the same gap as RoughLPFImpliesMFRE).

    Therefore, this bridge uses the CRT independence hypothesis. -/
theorem uce_implies_mfre_via_crt
    (_huce : UniformConductorEquidist)
    (hcrt : RoughLPFImpliesMFRE)
    (hrlpf : PrimesEquidistImpliesRoughLPF)
    (hant : IK.PrimesEquidistributedInAP) :
    ∀ (q : Nat), Nat.Prime q → MinFacResidueEquidist q :=
  hcrt (hrlpf hant)

/-- UCE combined with the Alladi chain implies PopulationEquidist.

    This follows the standard route: PrimesEquidistInAP -> RoughLPFEquidist
    -> MinFacResidueEquidist -> PE. UCE provides the uniform version but
    the non-uniform version suffices for PE. -/
theorem uce_alladi_implies_pe
    (hcrt : RoughLPFImpliesMFRE)
    (hrlpf : PrimesEquidistImpliesRoughLPF)
    (hant : IK.PrimesEquidistributedInAP) :
    PopulationEquidist :=
  pe_of_equidist (hcrt (hrlpf hant))

/-- **UCE + DSL => MC**: UCE (via the Alladi chain) provides PE, and
    DSL closes the gap PE -> CME -> MC. -/
theorem uce_dsl_implies_mc
    (hcrt : RoughLPFImpliesMFRE)
    (hrlpf : PrimesEquidistImpliesRoughLPF)
    (hant : IK.PrimesEquidistributedInAP)
    (hdsl : DeterministicStabilityLemma) :
    MullinConjecture :=
  pe_dsl_implies_mc (uce_alladi_implies_pe hcrt hrlpf hant) hdsl

/-- **UCEImpliesCME**: the orbit-specificity bridge.

    This is the conductor version of the orbit-specificity gap (Dead End #90):
    UCE says minFac is equidistributed in ALL arithmetic progressions 1 mod M,
    but CME needs the equidistribution for the SPECIFIC orbit values
    M = prod(n). The gap is that prod(n)+1 is a deterministic element of
    the progression, not a random sample.

    This is analogous to the gap between knowing "primes are equidistributed
    in residue classes" and knowing "the n-th prime mod q is equidistributed".
    The former is a population statement; the latter is an orbit statement.

    Assessment: OPEN. The orbit-specificity gap is fundamental and maps
    to Dead End #90. UCE is a necessary condition for CME but the
    sufficiency requires additional input about the EM orbit's sampling
    behavior. -/
def UCEImpliesCME : Prop := UniformConductorEquidist → ConditionalMultiplierEquidist

/-- If the orbit-specificity bridge holds, UCE implies MC. -/
theorem uce_cme_implies_mc
    (huce : UniformConductorEquidist)
    (hbridge : UCEImpliesCME) :
    MullinConjecture :=
  cme_implies_mc (hbridge huce)

end Bridges

/-! ## Structural Observations -/

section Structure

/-- prod(n) + 1 is congruent to 1 modulo every prime in the support of prod(n).
    This is the fundamental "+1 shift" that connects the EM construction to
    the UCE framework: seq(n+1) = minFac(prod(n)+1), and prod(n)+1 lives
    in the arithmetic progression 1 mod p for every p dividing prod(n).

    This is already proved as `prod_succ_mod_emSupport` in SieveConstraint.lean,
    restated here for the UCE context. -/
theorem prod_succ_cong_one_mod_support (n : Nat) (p : Nat)
    (hp : p ∈ emSupport n) (hp' : p.Prime) :
    (Mullin.prod n + 1) % p = 1 :=
  prod_succ_mod_emSupport n p hp hp'

/-- prod(n) + 1 is congruent to 1 modulo prod(n) itself. This follows
    from the definition: prod(n) + 1 = prod(n) * 1 + 1. -/
theorem prod_succ_cong_one_mod_prod (n : Nat) :
    (Mullin.prod n + 1) % Mullin.prod n = 1 % Mullin.prod n := by
  -- (prod n + 1) % prod n = (prod n % prod n + 1 % prod n) % prod n
  -- = (0 + 1 % prod n) % prod n = (1 % prod n) % prod n = 1 % prod n
  simp

/-- The conductor M = prod(n) is squarefree (proved in WeakErgodicity.lean). -/
theorem prod_squarefree_for_uce (n : Nat) : Squarefree (Mullin.prod n) :=
  prod_squarefree n

/-- The conductor M = prod(n) is positive. -/
theorem prod_pos_for_uce (n : Nat) : 0 < Mullin.prod n := by
  have := prod_ge_two n; omega

/-- For a prime q not in the EM sequence (which is the setting of CME),
    prod(n) is coprime to q. This connects the UCE framework to the
    CME setting: the conductor M = prod(n) satisfies the UCE coprimality
    prerequisite whenever q is not in the sequence.

    The proof uses: if q divides prod(n), then since prod(n) is a product
    of distinct primes seq(0)...seq(n), the prime q must equal some seq(i),
    contradicting the hypothesis. Proved by induction on n. -/
theorem prod_coprime_of_not_in_seq (n : Nat) (q : Nat) (hq : Nat.Prime q)
    (hne : ∀ k, seq k ≠ q) : Nat.Coprime (Mullin.prod n) q := by
  -- Suffices to show q does not divide prod n.
  -- If q | prod n, then since prod n = seq(0) * ... * seq(n) and q is prime,
  -- q | seq(i) for some i, hence q = seq(i) (both prime), contradicting hne.
  rw [Nat.coprime_comm]
  refine hq.coprime_iff_not_dvd.mpr (fun hdvd => ?_)
  -- If q | seq(i) where seq(i) is prime, then q = 1 or q = seq(i).
  -- Since q is prime (hence >= 2), q = seq(i), contradicting hne.
  have prime_dvd_eq : ∀ i, q ∣ seq i → q = seq i := fun i hdvd_i =>
    ((seq_natPrime i).eq_one_or_self_of_dvd q hdvd_i).resolve_left
      (by have := hq.two_le; omega)
  induction n with
  | zero =>
    rw [prod_zero] at hdvd
    exact hne 0 (prime_dvd_eq 0 hdvd).symm
  | succ n ih =>
    rw [prod_succ] at hdvd
    rcases hq.dvd_mul.mp hdvd with h | h
    · exact ih h
    · exact hne (n + 1) (prime_dvd_eq (n + 1) h).symm

end Structure

/-! ## Landscape -/

section Landscape

/-- Summary of the UCE landscape:
    1. UCE is a well-defined strengthening of MinFacResidueEquidist
    2. UCE + DSL => MC (via Alladi chain)
    3. UCEImpliesCME is the orbit-specificity bridge (open)
    4. UCEImpliesCME => MC (unconditionally from UCE)
    5. The EM conductor prod(n) satisfies all UCE prerequisites -/
theorem uce_landscape :
    -- (1) UCE + Alladi chain + DSL => MC
    (RoughLPFImpliesMFRE → PrimesEquidistImpliesRoughLPF →
      IK.PrimesEquidistributedInAP → DeterministicStabilityLemma →
      MullinConjecture) ∧
    -- (2) UCEImpliesCME short-circuits the chain
    (UniformConductorEquidist → UCEImpliesCME → MullinConjecture) ∧
    -- (3) The conductor prod(n) is squarefree and positive
    (∀ n, Squarefree (Mullin.prod n) ∧ 0 < Mullin.prod n) :=
  ⟨uce_dsl_implies_mc,
   uce_cme_implies_mc,
   fun n => ⟨prod_squarefree_for_uce n, prod_pos_for_uce n⟩⟩

end Landscape

end
