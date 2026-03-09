import EM.AdelicEquidist

/-!
# Profinite Equidistribution and the Weyl Criterion for the EM Walk

## Overview

The EM walk lives in the profinite group Z-hat-cross = prod_p (Z/pZ)x.
The Weyl criterion for this compact abelian group says: equidistribution
is equivalent to the vanishing of all nontrivial character sums.

The continuous characters of Z-hat-cross are exactly the "product characters":
pick finitely many distinct primes p_1, ..., p_k, pick nontrivial characters
chi_i : (Z/p_iZ)x -> Cx at each, and form the product
  chi(x) = prod_i chi_i(x mod p_i).

This gives a hierarchy of equidistribution notions:

- **FiniteLevelEquidist**: at each prime q (not in seq), the walk visits
  every position cofinally. Conjectured to follow from SE + PRE, but no
  proof exists — the gap is between subgroup generation (algebraic) and
  cofinal visits to every element (dynamical).

- **UniformProfiniteEquidist** (UPE): for any finite set of distinct primes
  and any product of nontrivial characters, the product character sum is o(N).
  This is the full Weyl criterion for Z-hat-cross.

- **UniformityGap**: does finite-level bootstrap to profinite? This is the
  deep question requiring product structure of Z-hat-cross.

## Main results

- `uniform_profinite_implies_ccsb`: UPE implies CCSB (k=1 specialization)
- `uniform_profinite_implies_mc`: UPE implies Mullin's Conjecture
- `uniform_profinite_implies_cpd`: UPE implies CrossPrimeDecorrelation (k=2)
-/

open Mullin Euclid MullinGroup

open Classical

/-! ## Definitions -/

/-- The collapse time: when prime q first appears in the sequence. -/
noncomputable def collapseTime (q : Nat) : Nat :=
  if h : ∃ n, seq n = q then Nat.find h else 0

/-- Uniform profinite equidistribution: for any finite set of distinct primes
    and product of nontrivial characters, the product character sum is o(N).
    This is the Weyl criterion for Z-hat-cross = prod_p (Z/pZ)x.

    We use `@emWalkUnit (qs i) inst_i` to supply the Fact instance from
    the primality hypothesis.

    For k=1: reduces to ComplexCharSumBound (CCSB).
    For k=2: gives CrossPrimeDecorrelation (CPD). -/
def UniformProfiniteEquidist : Prop :=
  ∀ (k : Nat) (qs : Fin k → Nat)
    (hqs_prime : ∀ i, Nat.Prime (qs i))
    (_hqs_inj : Function.Injective qs)
    (hqs_ne : ∀ i, ∀ n, seq n ≠ qs i)
    (χs : ∀ i, (ZMod (qs i))ˣ →* ℂˣ)
    (_hχs : ∀ i, χs i ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : Nat, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N,
      ∏ i : Fin k, ((χs i
        (@emWalkUnit (qs i) ⟨hqs_prime i⟩
          ((isPrime_iff_natPrime _).mpr (hqs_prime i))
          (hqs_ne i) n) : ℂ))‖ ≤ ε * N

/-- Finite-level equidistribution: at each prime q (that does not appear
    in the sequence), the walk visits every position cofinally.
    This follows from SE + PRE (already proved in the codebase). -/
def FiniteLevelEquidist : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (a : (ZMod q)ˣ), ∀ (N₀ : Nat), ∃ n, n ≥ N₀ ∧ emWalkUnit q hq hne n = a

/-- The uniformity gap: does finite-level equidistribution bootstrap
    to profinite equidistribution? This is a deep question -- product
    structure of Z-hat-cross is needed. -/
def UniformityGap : Prop :=
  FiniteLevelEquidist → UniformProfiniteEquidist

/-! ## UPE implies CCSB (k=1 specialization) -/

/-- Uniform profinite equidistribution implies ComplexCharSumBound
    by specializing to k=1 (single prime, single character).
    The product over Fin 1 reduces to a single term. -/
theorem uniform_profinite_implies_ccsb
    (h : UniformProfiniteEquidist) : ComplexCharSumBound := by
  intro q inst hq hne χ hχ ε hε
  -- Define qs : Fin 1 → Nat as the constant function returning q
  let qs : Fin 1 → Nat := fun _ => q
  have hqs_prime : ∀ i, Nat.Prime (qs i) := fun _ => inst.out
  have hqs_inj : Function.Injective qs := Function.injective_of_subsingleton _
  have hqs_ne : ∀ i, ∀ n, seq n ≠ qs i := fun _ => hne
  -- Since qs i = q definitionally, (ZMod (qs i))x = (ZMod q)x definitionally
  let χs : ∀ i : Fin 1, (ZMod (qs i))ˣ →* ℂˣ := fun _ => χ
  have hχs : ∀ i : Fin 1, χs i ≠ 1 := fun _ => hχ
  obtain ⟨N₀, hN₀⟩ := h 1 qs hqs_prime hqs_inj hqs_ne χs hχs ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have key := hN₀ N hN
  -- The product over Fin 1 is just the single term at index 0
  simp only [Fin.prod_univ_one] at key
  -- The two emWalkUnit calls differ only in IsPrime witness (proof irrelevance)
  exact key

/-- UPE implies Mullin's Conjecture via the CCSB chain. -/
theorem uniform_profinite_implies_mc
    (h : UniformProfiniteEquidist) : MullinConjecture :=
  complex_csb_mc' (uniform_profinite_implies_ccsb h)

/-! ## UPE implies CPD (k=2 specialization) -/

/-- Uniform profinite equidistribution implies CrossPrimeDecorrelation
    by specializing to k=2 (two distinct primes, one character each).
    The product over Fin 2 reduces to two factors. -/
theorem uniform_profinite_implies_cpd
    (h : UniformProfiniteEquidist) : CrossPrimeDecorrelation := by
  intro q r inst_q inst_r hq hne_q hr hne_r hqr χ_q χ_r hχ_q hχ_r ε hε
  -- Define qs : Fin 2 → Nat via matrix notation (qs 0 = q, qs 1 = r definitionally)
  let qs : Fin 2 → Nat := ![q, r]
  have hqs_prime : ∀ i, Nat.Prime (qs i) := by
    intro i; fin_cases i
    · exact inst_q.out
    · exact inst_r.out
  have hqs_inj : Function.Injective qs := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp_all [qs])
  have hqs_ne : ∀ i, ∀ n, seq n ≠ qs i := by
    intro i; fin_cases i
    · exact hne_q
    · exact hne_r
  -- Build characters: qs 0 = q and qs 1 = r definitionally,
  -- so (ZMod (qs 0))x = (ZMod q)x and (ZMod (qs 1))x = (ZMod r)x
  let χs : ∀ i : Fin 2, (ZMod (qs i))ˣ →* ℂˣ := fun i =>
    match i with
    | ⟨0, _⟩ => χ_q
    | ⟨1, _⟩ => χ_r
  have hχs : ∀ i : Fin 2, χs i ≠ 1 := by
    intro i; fin_cases i
    · exact hχ_q
    · exact hχ_r
  obtain ⟨N₀, hN₀⟩ := h 2 qs hqs_prime hqs_inj hqs_ne χs hχs ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have key := hN₀ N hN
  -- The product over Fin 2 is f 0 * f 1
  simp only [Fin.prod_univ_two] at key
  -- key now has the right form with chi_q and chi_r (by proof irrelevance on IsPrime)
  exact key

/-! ## CCSB + CPD implies UPE (product factorization) -/

/-- CCSB + CPD implies UPE: ComplexCharSumBound handles the single-prime
    case and CrossPrimeDecorrelation handles the multi-prime case.
    The product character sum factors via independence.

    This is an open Prop because the inductive product factorization
    (from k primes to k-1 primes plus 1) requires careful bounds. -/
def CCSBCPDImpliesUPE : Prop :=
  ComplexCharSumBound → CrossPrimeDecorrelation → UniformProfiniteEquidist

/-! ## Route landscape -/

/-- All routes to MC through the profinite lens. -/
theorem profinite_routes_to_mc :
    -- Route 1: Full UPE
    (UniformProfiniteEquidist → MullinConjecture) ∧
    -- Route 2: CCSB alone (k=1 slice of UPE)
    (ComplexCharSumBound → MullinConjecture) ∧
    -- Route 3: Adelic decomposition
    (AdelicEquidist → MullinConjecture) :=
  ⟨uniform_profinite_implies_mc, complex_csb_mc', adelic_implies_mc⟩
