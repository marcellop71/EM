import EM.FunctionField.IrreducibilityDensity
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Fintype.BigOperators
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IntermediateField.Algebraic

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

/-! ### Step 1: Divisibility transitivity -/

/-- If d | n, then every monic irreducible Q of degree d divides X^(p^n) - X.
    Proof: Q | X^(p^d) - X (by monic_irreducible_dvd_X_pow_sub_X) and
    X^(p^d) - X | X^(p^n) - X (by dvd_pow_pow_sub_self_of_dvd). -/
private theorem irred_dvd_X_pow_sub_X_of_dvd {n d : ℕ} (hn : 0 < n) (hd : d ∣ n)
    {Q : Polynomial (ZMod p)} (hm : Q.Monic) (hirr : Irreducible Q) (hdeg : Q.natDegree = d) :
    Q ∣ (X ^ p ^ n - X : Polynomial (ZMod p)) := by
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  have h1 : Q ∣ (X ^ p ^ d - X : Polynomial (ZMod p)) :=
    monic_irreducible_dvd_X_pow_sub_X p hd_pos.ne' hm hirr hdeg
  have h2 : (X ^ p ^ d - X : Polynomial (ZMod p)) ∣ (X ^ p ^ n - X) :=
    dvd_pow_pow_sub_self_of_dvd hd
  exact dvd_trans h1 h2

/-! ### Step 2: Build the combined finite set of all irreds with degree dividing n -/

/-- The Finset of all monic irreducible polynomials whose degree divides n. -/
private noncomputable def allIrredsDividingN (n : ℕ) : Finset (Polynomial (ZMod p)) :=
  n.divisors.biUnion (fun d => irredFinset p d)

private theorem mem_allIrredsDividingN {n : ℕ} {Q : Polynomial (ZMod p)} :
    Q ∈ allIrredsDividingN p n ↔ ∃ d ∈ n.divisors, Q ∈ irredFinset p d := by
  simp [allIrredsDividingN]

/-- The product of all monic irreducibles with degree dividing n divides X^(p^n) - X. -/
private theorem prod_allIrreds_dvd (n : ℕ) (hn : 0 < n) :
    (∏ Q ∈ allIrredsDividingN p n, Q) ∣ (X ^ p ^ n - X : Polynomial (ZMod p)) := by
  apply Finset.prod_dvd_of_coprime
  · intro Q₁ hQ₁ Q₂ hQ₂ hne
    obtain ⟨_, _, hQ₁'⟩ := (mem_allIrredsDividingN p).mp hQ₁
    obtain ⟨_, _, hQ₂'⟩ := (mem_allIrredsDividingN p).mp hQ₂
    exact monic_irreducible_isCoprime p
      ((mem_irredFinset p).mp hQ₁').1 ((mem_irredFinset p).mp hQ₂').1
      ((mem_irredFinset p).mp hQ₁').2.1 ((mem_irredFinset p).mp hQ₂').2.1 hne
  · intro Q hQ
    obtain ⟨d, hd_mem, hQ'⟩ := (mem_allIrredsDividingN p).mp hQ
    have ⟨hm, hirr, hdeg⟩ := (mem_irredFinset p).mp hQ'
    have hd_dvd : d ∣ n := (Nat.mem_divisors.mp hd_mem).1
    exact irred_dvd_X_pow_sub_X_of_dvd p hn hd_dvd hm hirr hdeg

/-! ### Step 3: Every irreducible factor of X^(p^n) - X has degree dividing n -/

/-- If a monic irreducible Q divides X^(p^n) - X over ZMod p, then deg(Q) | n.
    Proof: Q has a root alpha in GaloisField p n (since X^(p^n) - X splits there).
    Then [ZMod_p(alpha) : ZMod_p] = deg(Q), and this divides
    [GF(p,n) : ZMod_p] = n by the tower law. -/
private theorem irred_degree_dvd_of_dvd_X_pow_sub_X {n : ℕ} (hn : 0 < n)
    {Q : Polynomial (ZMod p)} (hm : Q.Monic) (hirr : Irreducible Q)
    (hdvd : Q ∣ (X ^ p ^ n - X : Polynomial (ZMod p))) :
    Q.natDegree ∣ n := by
  -- GaloisField p n is the splitting field
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  -- X^(p^n) - X splits in GaloisField p n
  have hsplits : Splits (map (algebraMap (ZMod p) (GaloisField p n)) (X ^ p ^ n - X)) :=
    (FiniteField.isSplittingField_of_card_eq p n
      (by rw [Fintype.card_eq_nat_card, GaloisField.card p n hn.ne'])).splits
  -- Q divides X^(p^n) - X, so Q splits in GaloisField p n
  have hQ_ne : Q ≠ 0 := hirr.ne_zero
  have hXpn_ne : (X ^ p ^ n - X : Polynomial (ZMod p)) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero _ hn.ne' hp.out.one_lt
  have hQ_splits : (map (algebraMap (ZMod p) (GaloisField p n)) Q).Splits :=
    hsplits.of_dvd (Polynomial.map_ne_zero hXpn_ne) ((map_dvd_map' _).mpr hdvd)
  -- Q has a root in GaloisField p n
  have hQ_deg_pos : 0 < Q.natDegree := Irreducible.natDegree_pos hirr
  -- There exists a root of Q in GaloisField p n
  have hQ_map_degree_ne : (map (algebraMap (ZMod p) (GaloisField p n)) Q).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap (ZMod p) (GaloisField p n)).injective]
    intro h
    have := Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h)
    omega
  obtain ⟨α, hα⟩ := hQ_splits.exists_eval_eq_zero hQ_map_degree_ne
  -- α is a root of Q, so α is integral with minpoly dividing Q
  have hα_aeval : Polynomial.aeval α Q = 0 := by
    rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  -- α is integral since GaloisField is a finite extension
  have hα_int : IsIntegral (ZMod p) α := IsIntegral.of_finite _ _
  -- minpoly divides Q
  have hmin_dvd : minpoly (ZMod p) α ∣ Q := minpoly.dvd _ _ hα_aeval
  -- Since Q is irreducible and minpoly is a non-unit divisor, they're associated
  have hmin_ne_unit : ¬ IsUnit (minpoly (ZMod p) α) :=
    minpoly.not_isUnit _ _
  have hmin_assoc : Associated (minpoly (ZMod p) α) Q :=
    (minpoly.irreducible hα_int).associated_of_dvd hirr hmin_dvd
  -- Associated monic polynomials are equal
  have hmin_eq : minpoly (ZMod p) α = Q :=
    eq_of_monic_of_associated (minpoly.monic hα_int) hm hmin_assoc
  -- deg(Q) = deg(minpoly) = finrank(ZMod p)(ZMod p⟮α⟯)
  -- and finrank(ZMod p⟮α⟯) divides finrank(ZMod p)(GaloisField p n) = n
  have hfinrank_gf : Module.finrank (ZMod p) (GaloisField p n) = n :=
    GaloisField.finrank p hn.ne'
  -- The degree of minpoly equals the finrank of the adjunction
  have hmin_deg : (minpoly (ZMod p) α).natDegree =
      Module.finrank (ZMod p) (IntermediateField.adjoin (ZMod p) {α}) := by
    rw [IntermediateField.adjoin.finrank hα_int]
  -- The finrank of the adjunction divides the finrank of the full extension
  have hfinrank_dvd : Module.finrank (ZMod p) (IntermediateField.adjoin (ZMod p) {α}) ∣
      Module.finrank (ZMod p) (GaloisField p n) := by
    conv_rhs => rw [← IntermediateField.finrank_top' (F := ZMod p) (E := GaloisField p n)]
    exact IntermediateField.finrank_dvd_of_le_right le_top
  -- Combine: deg(Q) = deg(minpoly) | finrank = n
  rw [← hmin_eq]
  rw [hmin_deg]
  rwa [hfinrank_gf] at hfinrank_dvd

/-! ### Step 4: The big product equals X^(p^n) - X -/

/-- Every irreducible factor of X^(p^n) - X is in the big product. -/
private theorem irred_factor_in_allIrreds {n : ℕ} (hn : 0 < n)
    {Q : Polynomial (ZMod p)} (hm : Q.Monic) (hirr : Irreducible Q)
    (hdvd : Q ∣ (X ^ p ^ n - X : Polynomial (ZMod p))) :
    Q ∈ allIrredsDividingN p n := by
  rw [mem_allIrredsDividingN]
  have hd_dvd := irred_degree_dvd_of_dvd_X_pow_sub_X p hn hm hirr hdvd
  exact ⟨Q.natDegree, Nat.mem_divisors.mpr ⟨hd_dvd, hn.ne'⟩,
    (mem_irredFinset p).mpr ⟨hm, hirr, rfl⟩⟩

/-! ### Step 5: Degree computation -/

/-- irredFinsets for distinct divisors are disjoint. -/
private theorem irredFinset_disjoint {d₁ d₂ : ℕ} (hne : d₁ ≠ d₂) :
    Disjoint (irredFinset p d₁) (irredFinset p d₂) := by
  rw [Finset.disjoint_left]
  intro Q hQ₁ hQ₂
  have h₁ := ((mem_irredFinset p).mp hQ₁).2.2
  have h₂ := ((mem_irredFinset p).mp hQ₂).2.2
  exact hne (h₁.symm.trans h₂)

/-- The degree of the big product is ∑_{d|n} d * ffIrredCount p d. -/
private theorem natDegree_prod_allIrreds (n : ℕ) (_hn : 0 < n) :
    (∏ Q ∈ allIrredsDividingN p n, Q).natDegree =
      ∑ d ∈ n.divisors, d * ffIrredCount p d := by
  -- The product over allIrredsDividingN equals the double product
  have hne_zero : ∀ Q ∈ allIrredsDividingN p n, Q ≠ 0 := by
    intro Q hQ
    obtain ⟨_, _, hQ'⟩ := (mem_allIrredsDividingN p).mp hQ
    exact ((mem_irredFinset p).mp hQ').2.1.ne_zero
  -- Degree of product = sum of degrees
  rw [Polynomial.natDegree_prod _ _ hne_zero]
  -- Rewrite allIrredsDividingN as biUnion
  rw [show allIrredsDividingN p n = n.divisors.biUnion (fun d => irredFinset p d) from rfl]
  rw [Finset.sum_biUnion (fun d₁ _ d₂ _ hne => irredFinset_disjoint p hne)]
  apply Finset.sum_congr rfl
  intro d hd
  -- For each d, ∑_{Q ∈ irredFinset d} deg(Q) = d * |irredFinset d|
  rw [Finset.sum_const_nat (fun Q hQ => ((mem_irredFinset p).mp hQ).2.2)]
  simp [ffIrredCount, mul_comm]

/-! ### Step 6: Prove the necklace identity -/

/-- **The necklace identity proved**: ∑_{d|n} d * π_p(d) = p^n.

    Proof strategy: We show that the product P of all monic irreducibles of degree d | n
    equals X^(p^n) - X. Both directions:
    (a) P | X^(p^n) - X (coprimality + individual divisibility)
    (b) X^(p^n) - X | P (every irreducible factor of X^(p^n)-X is in P, and
        X^(p^n)-X is squarefree so has no repeated factors)
    Then deg(P) = deg(X^(p^n)-X) = p^n, and deg(P) = ∑ d * π_p(d). -/
theorem necklace_identity_proved :
    ∀ n : ℕ, 0 < n → ∑ d ∈ n.divisors, d * ffIrredCount p d = p ^ n := by
  intro n hn
  -- The big product P
  set P := ∏ Q ∈ allIrredsDividingN p n, Q with hP_def
  -- P divides X^(p^n) - X
  have hP_dvd : P ∣ (X ^ p ^ n - X : Polynomial (ZMod p)) := prod_allIrreds_dvd p n hn
  -- X^(p^n) - X is nonzero
  have hXpn_ne : (X ^ p ^ n - X : Polynomial (ZMod p)) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero _ hn.ne' hp.out.one_lt
  -- X^(p^n) - X has degree p^n
  have hXpn_deg : (X ^ p ^ n - X : Polynomial (ZMod p)).natDegree = p ^ n :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ hn.ne' hp.out.one_lt
  -- deg(P) = ∑ d * π_p(d)
  have hP_deg : P.natDegree = ∑ d ∈ n.divisors, d * ffIrredCount p d :=
    natDegree_prod_allIrreds p n hn
  -- deg(P) ≤ p^n (since P | X^(p^n) - X)
  have hP_deg_le : P.natDegree ≤ (X ^ p ^ n - X : Polynomial (ZMod p)).natDegree :=
    Polynomial.natDegree_le_of_dvd hP_dvd hXpn_ne
  -- So ∑ d * π_p(d) ≤ p^n
  rw [hP_deg, hXpn_deg] at hP_deg_le
  -- For the reverse inequality, we show X^(p^n) - X | P
  -- X^(p^n) - X is separable, hence squarefree
  have hXpn_sep : (X ^ p ^ n - X : Polynomial (ZMod p)).Separable :=
    galois_poly_separable p _ (dvd_pow (dvd_refl p) hn.ne')
  have hXpn_sqfree : Squarefree (X ^ p ^ n - X : Polynomial (ZMod p)) :=
    hXpn_sep.squarefree
  -- P is monic (product of monics)
  have hP_monic : P.Monic := by
    apply Polynomial.monic_prod_of_monic
    intro Q hQ
    obtain ⟨_, _, hQ'⟩ := (mem_allIrredsDividingN p).mp hQ
    exact ((mem_irredFinset p).mp hQ').1
  -- X^(p^n) - X is monic
  have hXpn_monic : (X ^ p ^ n - X : Polynomial (ZMod p)).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    have h1lt : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp.out.one_lt
    exact_mod_cast h1lt
  -- Every irreducible factor of X^(p^n) - X divides P
  -- Since X^(p^n) - X is squarefree, it equals (up to unit) the product of its irred factors
  -- Each irred factor Q of X^(p^n)-X has degree d|n, so Q ∈ allIrredsDividingN
  -- The product of coprime factors in allIrredsDividingN that include all irred factors of
  -- X^(p^n)-X implies X^(p^n)-X | P (since squarefree = product of distinct irred factors)

  -- Alternative approach: use that P | X^(p^n)-X and P is monic.
  -- Show deg(P) ≥ deg(X^(p^n)-X) = p^n
  -- For this, we count: GaloisField p n has p^n elements.
  -- Each element is a root of exactly one Q in allIrredsDividingN (its minimal polynomial).
  -- Each Q in allIrredsDividingN of degree d has exactly d roots in GaloisField p n.
  -- So #(roots of P) = ∑_{d|n} d * π_p(d) = deg(P) (since P is separable).
  -- And #(roots of P) = p^n (every element of GF(p,n) is a root of some factor).

  -- Let's use the direct approach: show deg(P) ≥ p^n by showing every element of GF(p,n)
  -- is a root of P.
  suffices h_ge : p ^ n ≤ ∑ d ∈ n.divisors, d * ffIrredCount p d from le_antisymm hP_deg_le h_ge
  -- We show: p^n = |GF(p,n)| ≤ |roots of P in GF(p,n)| ≤ deg(P) = ∑ d * π(d)
  -- For this, every element of GF(p,n) is a root of P.
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  have hcard_gf : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p n hn.ne']
  -- Show every element of GF(p,n) is a root of P
  -- Each element alpha has minpoly Q which is monic, irreducible, degree d | n
  -- So Q ∈ allIrredsDividingN and Q | P, so alpha is a root of P
  have hP_eval : ∀ α : GaloisField p n,
      Polynomial.eval₂ (algebraMap (ZMod p) (GaloisField p n)) α P = 0 := by
    intro α
    have hα_int : IsIntegral (ZMod p) α := IsIntegral.of_finite _ _
    set Q := minpoly (ZMod p) α with hQ_def
    have hm : Q.Monic := minpoly.monic hα_int
    have hirr : Irreducible Q := minpoly.irreducible hα_int
    -- Q is the minimal polynomial of α
    have hα_root : Polynomial.aeval α Q = 0 := minpoly.aeval _ _
    -- α satisfies α^(p^n) = α (Frobenius)
    have hfrob : α ^ Fintype.card (GaloisField p n) = α := FiniteField.pow_card α
    rw [hcard_gf] at hfrob
    -- Q | X^(p^n) - X
    have hQ_dvd_Xpn : Q ∣ (X ^ p ^ n - X : Polynomial (ZMod p)) := by
      apply minpoly.dvd
      simp only [map_sub, map_pow, aeval_X]
      rw [hfrob, sub_self]
    -- deg(Q) | n
    have hdeg_dvd := irred_degree_dvd_of_dvd_X_pow_sub_X p hn hm hirr hQ_dvd_Xpn
    -- Q ∈ allIrredsDividingN
    have hQ_mem : Q ∈ allIrredsDividingN p n := by
      rw [mem_allIrredsDividingN]
      exact ⟨Q.natDegree, Nat.mem_divisors.mpr ⟨hdeg_dvd, hn.ne'⟩,
        (mem_irredFinset p).mpr ⟨hm, hirr, rfl⟩⟩
    -- Q | P (since Q is one of the factors in the product P)
    have hQ_dvd_P : Q ∣ P := Finset.dvd_prod_of_mem _ hQ_mem
    -- α is a root of Q, so α is a root of P
    obtain ⟨R, hR⟩ := hQ_dvd_P
    rw [hR, Polynomial.eval₂_mul, show Polynomial.eval₂ (algebraMap _ _) α Q = Polynomial.aeval α Q from rfl]
    rw [hα_root, zero_mul]
  -- Now: every element of GF(p,n) is a root of map(P) in GF(p,n)
  -- The number of roots ≤ deg(P)
  -- The number of roots = p^n (since all p^n elements are roots)
  -- So p^n ≤ deg(P) = ∑ d * π(d)
  -- Use: the number of roots of a nonzero polynomial is at most its degree.
  -- The multiset of roots of map(P) has cardinality ≤ deg(P).
  -- Every element of GF(p,n) is in the root multiset (as a Finset member).
  -- So p^n = |GF(p,n)| ≤ card(roots of P) ≤ deg(P).
  have hP_ne : P ≠ 0 := hP_monic.ne_zero
  have hP_map_ne : (P.map (algebraMap (ZMod p) (GaloisField p n))) ≠ 0 :=
    Polynomial.map_ne_zero hP_ne
  -- roots of map(P) has card ≤ natDegree(map(P)) = natDegree(P)
  have hroots_le : (P.map (algebraMap (ZMod p) (GaloisField p n))).roots.card ≤ P.natDegree := by
    calc (P.map (algebraMap (ZMod p) (GaloisField p n))).roots.card
        ≤ (P.map (algebraMap (ZMod p) (GaloisField p n))).natDegree :=
          Polynomial.card_roots' _
      _ = P.natDegree := Polynomial.natDegree_map _
  -- Every element of GF(p,n) is in the roots
  have hα_in_roots : ∀ α : GaloisField p n,
      α ∈ (P.map (algebraMap (ZMod p) (GaloisField p n))).roots := by
    intro α
    rw [Polynomial.mem_roots hP_map_ne, Polynomial.IsRoot, Polynomial.eval_map]
    exact hP_eval α
  -- So Finset.univ maps into roots, giving card(GF(p,n)) ≤ card(roots)
  have huniv_le : Fintype.card (GaloisField p n) ≤
      (P.map (algebraMap (ZMod p) (GaloisField p n))).roots.card := by
    calc Fintype.card (GaloisField p n)
        = Finset.univ.card := (Finset.card_univ).symm
      _ ≤ (P.map (algebraMap (ZMod p) (GaloisField p n))).roots.toFinset.card := by
          apply Finset.card_le_card
          intro α _
          exact Multiset.mem_toFinset.mpr (hα_in_roots α)
      _ ≤ (P.map (algebraMap (ZMod p) (GaloisField p n))).roots.card :=
          (P.map (algebraMap (ZMod p) (GaloisField p n))).roots.toFinset_card_le
  -- Combine: p^n = |GF(p,n)| ≤ card(roots) ≤ deg(P) = ∑ d * π(d)
  rw [hcard_gf] at huniv_le
  rw [hP_deg] at hroots_le
  exact le_trans huniv_le hroots_le

/-- The necklace identity: for every n >= 1, the sum of d * pi_p(d) over divisors d of n
    equals p^n. This is a standard identity in finite field theory, equivalent to the
    factorization X^(p^n) - X = prod of all monic irreducibles of degree d | n. -/
def NecklaceIdentity : Prop :=
  ∀ n : ℕ, 0 < n →
    ∑ d ∈ n.divisors, d * ffIrredCount p d = p ^ n

/-- The necklace identity holds unconditionally. -/
theorem necklaceIdentity_holds : NecklaceIdentity p := necklace_identity_proved p

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
