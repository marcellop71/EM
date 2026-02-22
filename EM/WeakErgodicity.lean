import EM.CMEDecomposition
import Mathlib.Data.Nat.Squarefree

/-!
# Weak Ergodicity via the Shifted Squarefree Population

The EM accumulators P(n) are squarefree integers (products of distinct primes).
The Euclid numbers P(n)+1 therefore belong to the **shifted squarefree
population** S = {m ≥ 2 : m−1 squarefree}.

We decompose Weak Ergodicity (WE = EMDirichlet = DecorrelationHypothesis) into:
- **PopulationEquidist (PE)**: minFac is equidist mod q in S (provable by sieve)
- **PopulationTransfer (PT)**: EM trajectory samples S without bias (open)

The full reduction chain: PE + PT → EMDirichlet → (+ EMDImpliesCME) → CME → MC.

## Main Results

### S93. Squarefree Accumulator
* `seq_succ_dvd_euclid` : seq(n+1) ∣ prod(n)+1 (PROVED)
* `seq_succ_coprime_prod` : Coprime (seq(n+1)) (prod(n)) (PROVED)
* `prod_squarefree` : Squarefree (prod n) (PROVED)

### S94. Shifted Squarefree Population
* `ShiftedSquarefree` : the set {m ≥ 2 : m-1 squarefree} (DEF)
* `euclid_in_shifted_squarefree` : prod(n)+1 ∈ ShiftedSquarefree (PROVED)

### S95. Population Decomposition
* `PopulationEquidist` : minFac equidist mod q in S (OPEN, provable by sieve)
* `PopulationTransfer` : PE → EMDirichlet (OPEN = Unbiased Sampling)
* `pe_transfer_cme_implies_mc` : PE + PT + EMDImpliesCME → MC (PROVED)
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## S93. Squarefree Accumulator -/

section SquarefreeAccumulator

/-- **The EM accumulator is squarefree.** `prod(n) = em(0) · em(1) · ⋯ · em(n)`
    is a product of distinct primes, hence squarefree. The proof is by induction:
    at each step, the new prime seq(n+1) is coprime to the existing product
    (by `seq_succ_coprime_prod`), so the product remains squarefree. -/
theorem prod_squarefree (n : Nat) : Squarefree (prod n) := by
  induction n with
  | zero =>
    rw [prod_zero]
    exact (show Nat.Prime 2 by decide).squarefree
  | succ n ih =>
    rw [prod_succ]
    exact Nat.squarefree_mul_iff.mpr
      ⟨(seq_succ_coprime_prod n).symm, ih,
       ((isPrime_iff_natPrime _).mp (seq_isPrime (n + 1))).squarefree⟩

end SquarefreeAccumulator

/-! ## S94. Shifted Squarefree Population -/

section ShiftedSquarefreePopulation

/-- The **shifted squarefree population**: the set of integers m ≥ 2 whose
    predecessor m−1 is squarefree. This set has density 6/π² ≈ 0.608 among
    the positive integers.

    Every Euclid number P(n)+1 belongs to this set, since P(n) is squarefree
    (a product of distinct primes). -/
def ShiftedSquarefree : Set Nat :=
  {m : Nat | 2 ≤ m ∧ Squarefree (m - 1)}

/-- Every Euclid number `prod(n) + 1` is in the shifted squarefree population. -/
theorem euclid_in_shifted_squarefree (n : Nat) :
    prod n + 1 ∈ ShiftedSquarefree :=
  ⟨by have := prod_ge_two n; omega,
   by rw [show prod n + 1 - 1 = prod n from by omega]; exact prod_squarefree n⟩

end ShiftedSquarefreePopulation

/-! ## S95. Population Decomposition -/

section PopulationDecomposition

/-- **Population Equidistribution (PE)**: among q-rough shifted squarefree
    numbers (those with minFac > q), the smallest prime factor is
    equidistributed in residue classes modulo any prime q.

    Concretely: the ratio
      |{m ∈ S_q ∩ [2,X] : minFac(m) ≡ a (mod q)}| / |S_q ∩ [2,X]|
    tends to 1/(q−1) as X → ∞, for each 0 < a < q, where
    S_q = {m ∈ S : minFac(m) > q} is the q-rough shifted squarefree population.

    The restriction to minFac(m) > q is essential: small primes (e.g., p = 2)
    create asymmetry across residue classes mod q. For instance, 2/3 of
    shifted squarefree numbers are even (minFac = 2), so the unrestricted
    ratio is biased toward a ≡ 2 (mod 3). Conditioning on minFac > q
    removes the finitely many small primes that break symmetry.

    This is provable from:
    1. **Sieve axiom** for S: divisibility by r has density g(r) = r/(r²−1).
    2. **Buchstab identity**: minFac(m) = p has density g(p) · ∏_{r<p}(1−g(r)).
    3. **Key fact**: d_S(p) depends on p only through its size, not p mod q.
    4. **Dirichlet's theorem**: primes in APs are equidistributed.

    Proved from `QRoughShiftedSquarefreeDensity` and `MinFacResidueEquidist`
    in `PopulationEquidistProof.lean`. -/
def PopulationEquidist : Prop :=
  ∀ (q : Nat), Nat.Prime q →
  ∀ (a : Nat), 0 < a → a < q →
  Filter.Tendsto
    (fun X : Nat =>
      (((Finset.Icc 2 X).filter
        (fun m => Squarefree (m - 1) ∧ q < Nat.minFac m ∧ Nat.minFac m % q = a)).card : ℝ) /
      ((Finset.Icc 2 X).filter (fun m => Squarefree (m - 1) ∧ q < Nat.minFac m)).card)
    Filter.atTop
    (nhds (1 / (q - 1 : ℝ)))

/-- **Population Transfer (PT)**: the EM trajectory's sampling of the shifted
    squarefree population preserves the mod-q equidistribution of minFac.

    Formally: PopulationEquidist → EMDirichlet. This is the **Unbiased
    Sampling** hypothesis from the working note.

    The structural basis is `crt_multiplier_invariance` (proved): the minFac
    mechanism is q-blind — em(n+1) mod q does not depend on P(n) mod q.
    A q-blind sampling rule from an equidistributed population should preserve
    equidistribution, but converting pointwise q-blindness to time-averaged
    unbiasedness requires that the non-q CRT coordinates (which drive the
    sampling) do not systematically select shifted squarefree numbers with
    biased mod-q minFac.

    The gap between PE and WE (= EMDirichlet) is the orbit-specificity
    transfer: the EM trajectory visits a specific deterministic subsequence
    of S, and the question is whether this subsequence inherits the population
    statistics. This is the same transfer problem that appears in Artin's
    conjecture (where Hooley's conditional proof uses GRH to control individual
    orbits) and in the Bombieri-Vinogradov theorem (where averaging over moduli
    achieves the transfer). -/
def PopulationTransfer : Prop := PopulationEquidist → EMDirichlet

/-- PE + PT → EMDirichlet. -/
theorem pe_transfer_implies_emd
    (hpe : PopulationEquidist) (hpt : PopulationTransfer) :
    EMDirichlet :=
  hpt hpe

/-- PE + PT + EMDImpliesCME → MC.
    This chains: PE + PT → EMDirichlet → CME → CCSB → MC. -/
theorem pe_transfer_cme_implies_mc
    (hpe : PopulationEquidist) (hpt : PopulationTransfer)
    (hcme : EMDImpliesCME) :
    MullinConjecture :=
  emd_cme_implies_mc hcme (hpt hpe)

/-- PE + PT + EMDImpliesCME → CCSB. -/
theorem pe_transfer_cme_implies_ccsb
    (hpe : PopulationEquidist) (hpt : PopulationTransfer)
    (hcme : EMDImpliesCME) :
    ComplexCharSumBound :=
  emd_cme_implies_ccsb hcme (hpt hpe)

end PopulationDecomposition
