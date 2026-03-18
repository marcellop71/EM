import EM.FunctionField.IrreducibilityDensity
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Fintype.BigOperators

/-!
# Necklace Formula Infrastructure for Polynomials over Finite Fields

We prove that there are exactly p^n monic polynomials of degree n over F_p,
state the necklace identity (sum_{d|n} d * pi_p(d) = p^n), and derive
consequences for irreducible polynomial counts.

## Main results

- `card_monic_of_degree` : there are exactly p^n monic polys of degree n over F_p
- `ffIrredCount` : number of monic irreducible polys of degree d over F_p
- `ffIrredCount_pos` : pi_p(d) >= 1 for all d >= 1
- `NecklaceIdentity` : sum_{d|n} d * pi_p(d) = p^n (open hypothesis)
- `necklace_implies_irred_lower_bound` : necklace identity rearrangement
- `necklace_formula_landscape` : summary conjunction

## Proof strategy

For `card_monic_of_degree`, we compose `monicEquivDegreeLT` (monic degree-n polys
equiv to degreeLT n) with `degreeLTEquiv` (degreeLT n linear equiv to Fin n -> R),
then use `Fintype.card_congr` + `Fintype.card_fun` + `ZMod.card`.
-/

namespace FunctionFieldAnalog

open Polynomial Classical Filter

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Part 1: Counting monic polynomials -/

/-- The Fintype instance for the submodule `degreeLT (ZMod p) n`,
    derived from the linear equivalence to `Fin n -> ZMod p`. -/
noncomputable instance degreeLT_fintype (n : ℕ) :
    Fintype (Polynomial.degreeLT (ZMod p) n) :=
  Fintype.ofEquiv _ (Polynomial.degreeLTEquiv (ZMod p) n).toEquiv.symm

/-- The Fintype instance for monic polynomials of degree n over ZMod p,
    derived from `monicEquivDegreeLT`. -/
noncomputable instance monicDegreeFintype (n : ℕ) :
    Fintype {f : Polynomial (ZMod p) // f.Monic ∧ f.natDegree = n} :=
  haveI : Nontrivial (ZMod p) := inferInstance
  Fintype.ofEquiv _ (monicEquivDegreeLT n).symm

/-- There are exactly p^n monic polynomials of degree n over F_p. -/
theorem card_monic_of_degree (n : ℕ) :
    Fintype.card {f : Polynomial (ZMod p) // f.Monic ∧ f.natDegree = n} = p ^ n := by
  haveI : Nontrivial (ZMod p) := inferInstance
  -- Step 1: monic degree-n equiv degreeLT n
  have h1 := Fintype.card_congr (monicEquivDegreeLT (R := ZMod p) n)
  -- Step 2: degreeLT n equiv (Fin n -> ZMod p)
  have h2 := Fintype.card_congr (degreeLTEquiv (ZMod p) n).toEquiv
  -- Step 3: card (Fin n -> ZMod p) = p^n
  have h3 : Fintype.card (Fin n → ZMod p) = p ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  -- Compose
  rw [h1, h2, h3]

/-! ## Part 2: Irreducible count definition -/

private theorem irredSet_finite (d : ℕ) :
    Set.Finite {Q : Polynomial (ZMod p) | Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d} :=
  Set.Finite.subset (monic_natDegree_finite (ZMod p) d)
    (fun _ ⟨hm, _, hd'⟩ => ⟨hm, hd'⟩)

/-- The finite set of monic irreducible polynomials of degree d. -/
private noncomputable def irredFinset (d : ℕ) : Finset (Polynomial (ZMod p)) :=
  (irredSet_finite p d).toFinset

/-- The number of monic irreducible polynomials of degree d over F_p. -/
noncomputable def ffIrredCount (d : ℕ) : ℕ :=
  (irredFinset p d).card

/-- Membership characterization of irredFinset. -/
private theorem mem_irredFinset {d : ℕ} {Q : Polynomial (ZMod p)} :
    Q ∈ irredFinset p d ↔ Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d := by
  simp [irredFinset]

/-- For every d >= 1, there is at least one monic irreducible polynomial of degree d over F_p.
    This follows from `ffExistsIrreducibleOfDegree`. -/
theorem ffIrredCount_pos (d : ℕ) (hd : 0 < d) : 0 < ffIrredCount p d := by
  obtain ⟨Q, hm, hirr, hdeg⟩ := @ffExistsIrreducibleOfDegree p hp d hd
  exact Finset.card_pos.mpr ⟨Q, (mem_irredFinset (p := p)).mpr ⟨hm, hirr, hdeg⟩⟩

/-! ## Part 3: Necklace identity -/

/-- The necklace identity: for every n >= 1, the sum of d * pi_p(d) over divisors d of n
    equals p^n. This is a standard identity in finite field theory, equivalent to the
    factorization X^(p^n) - X = prod of all monic irreducibles of degree d | n. -/
def NecklaceIdentity : Prop :=
  ∀ n : ℕ, 0 < n →
    ∑ d ∈ n.divisors, d * ffIrredCount p d = p ^ n

/-- From the necklace identity, the d=n term plus proper divisor terms equals p^n. -/
theorem necklace_implies_irred_lower_bound
    (hni : NecklaceIdentity p) (n : ℕ) (hn : 0 < n) :
    p ^ n = n * ffIrredCount p n +
      ∑ d ∈ n.divisors.erase n, d * ffIrredCount p d := by
  have hmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, hn.ne'⟩
  have heq := hni n hn
  rw [← Finset.add_sum_erase _ _ hmem] at heq
  linarith

/-- From the necklace identity, n * pi_p(n) <= p^n. -/
theorem necklace_count_mul_le
    (hni : NecklaceIdentity p) (n : ℕ) (hn : 0 < n) :
    n * ffIrredCount p n ≤ p ^ n := by
  have hmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, hn.ne'⟩
  have heq := hni n hn
  rw [← Finset.add_sum_erase _ _ hmem] at heq
  omega

/-- The necklace identity implies pi_p(n) <= p^n / n. -/
theorem necklace_irred_count_le
    (hni : NecklaceIdentity p) (n : ℕ) (hn : 0 < n) :
    ffIrredCount p n ≤ p ^ n / n :=
  (Nat.le_div_iff_mul_le hn).mpr (by linarith [necklace_count_mul_le p hni n hn])

/-- The necklace identity implies pi_p(n) >= 1 (weaker than `ffIrredCount_pos`,
    which is unconditional). -/
theorem necklace_implies_irred_count_pos
    (_hni : NecklaceIdentity p) (n : ℕ) (hn : 0 < n) :
    0 < ffIrredCount p n :=
  ffIrredCount_pos p n hn

/-! ## Part 4: Landscape -/

/-- Summary of necklace formula infrastructure. -/
theorem necklace_formula_landscape :
    -- (1) Monic polynomial count (PROVED)
    (∀ n, Fintype.card {f : Polynomial (ZMod p) // f.Monic ∧ f.natDegree = n} = p ^ n) ∧
    -- (2) Irreducible count positive (PROVED)
    (∀ d, 0 < d → 0 < ffIrredCount p d) ∧
    -- (3) NecklaceIdentity implies rearrangement (PROVED)
    (NecklaceIdentity p →
      ∀ n, 0 < n →
        p ^ n = n * ffIrredCount p n +
          ∑ d ∈ n.divisors.erase n, d * ffIrredCount p d) ∧
    -- (4) NecklaceIdentity implies upper bound (PROVED)
    (NecklaceIdentity p → ∀ n, 0 < n → ffIrredCount p n ≤ p ^ n / n) :=
  ⟨card_monic_of_degree p,
   ffIrredCount_pos p,
   fun hni n hn => necklace_implies_irred_lower_bound p hni n hn,
   fun hni n hn => necklace_irred_count_le p hni n hn⟩

end FunctionFieldAnalog
