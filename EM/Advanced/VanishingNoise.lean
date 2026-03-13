import EM.Reduction.DSLInfra
import EM.Equidist.Bootstrap
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Vanishing Noise Framework: Spectral Gap and Walk Infrastructure

## Overview

This file formalizes the **spectral gap lemma** for generating sets on finite abelian
groups and related infrastructure for the "MC with vanishing noise" perspective.

The key mathematical content: if a finite set S of elements in a finite commutative group G
generates G and contains the identity, then for any nontrivial character chi,
the character sum |sum_{s in S} chi(s)| is strictly less than |S|. This is the
**spectral contraction** that drives mixing in random walks on Cayley graphs.

## Main Results

### Proved Theorems
* `char_norm_one_of_hom`       -- |chi(g)| = 1 for group hom chi : G →* C*
* `exists_ne_one_of_nontrivial` -- nontrivial chi on generators: exists s in S with chi(s) != 1
* `ne_of_chi_ne_one`            -- chi(s) != 1 implies s != 1
* `norm_add_lt_two_of_ne`       -- |z + w| < 2 for unit-norm z != w
* `spectral_gap_with_identity`  -- THE KEY: |sum chi(s)| < |S| when 1 in S, <S> = G, chi != 1
* `spectral_contraction_lt_one` -- |sum chi(s)| / |S| < 1 (ratio form)
* `char_norm_mul_right`         -- |chi(a * g)| = |chi(a)| (right multiplication isometry)
* `target_in_death_fiber`       -- q in factor set at death state
* `product_contraction_tendsto` -- prod(1 - gamma_k) -> 0 when sum gamma_k = +infty

### Open Hypotheses
* `InfinitelyManyLargeFactorSets` -- |F_q(k)| >= 2 infinitely often (key hypothesis)

### Documentation Markers
* `vanishing_noise_landscape`   -- summary of the framework
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Spectral Gap for Generating Sets on Finite Commutative Groups -/

section SpectralGap

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
/-- Character values on finite groups have norm 1.
    Generalizes `char_value_norm_one` from DSLInfra.lean to abstract groups.
    For chi : G →* C* with G finite, chi(g) is a root of unity of order dividing |G|. -/
theorem char_norm_one_of_hom (chi : G →* ℂˣ) (g : G) :
    ‖(chi g : ℂ)‖ = 1 := by
  have hpow : (chi g : ℂ) ^ Fintype.card G = 1 := by
    have h : (chi g : ℂˣ) ^ Fintype.card G = 1 := by
      rw [← map_pow, pow_card_eq_one, map_one]
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow Fintype.card_ne_zero

omit [Fintype G] [DecidableEq G] in
/-- If chi is nontrivial on G and S generates G (closure S = top) with S a Finset,
    then there exists s in S such that chi(s) != 1. -/
theorem exists_ne_one_of_nontrivial (chi : G →* ℂˣ) (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hnt : chi ≠ 1) :
    ∃ s ∈ S, chi s ≠ 1 := by
  by_contra h
  push_neg at h
  -- All elements of S map to 1 under chi, so S is in ker(chi)
  -- Since S generates G and S is in ker(chi), ker(chi) = top
  have hle : Subgroup.closure (S : Set G) ≤ MonoidHom.ker chi := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact h s hs
  rw [hgen] at hle
  -- ker(chi) = top means chi = 1
  have : MonoidHom.ker chi = ⊤ := top_le_iff.mp hle
  rw [MonoidHom.ker_eq_top_iff] at this
  exact hnt this

omit [Fintype G] [DecidableEq G] in
/-- If chi(s) != 1 for a group homomorphism chi with chi(1) = 1, then s != 1. -/
theorem ne_of_chi_ne_one {chi : G →* ℂˣ} {s : G} (h : chi s ≠ 1) :
    s ≠ 1 := by
  intro heq
  exact h (heq ▸ map_one chi)

/-- For two complex numbers of norm 1 that are NOT equal,
    their sum has norm strictly less than 2.
    Uses StrictConvexSpace for C. -/
theorem norm_add_lt_two_of_ne {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (hne : z ≠ w) :
    ‖z + w‖ < 2 := by
  have hray : ¬SameRay ℝ z w := by
    rwa [not_sameRay_iff_of_norm_eq (hz.trans hw.symm)]
  calc ‖z + w‖ < ‖z‖ + ‖w‖ := norm_add_lt_of_not_sameRay hray
    _ = 2 := by rw [hz, hw]; ring

/-- **Spectral gap lemma for generating sets with identity.**
    If S is a finite subset of a finite commutative group G that:
    (1) generates G (Subgroup.closure S = top),
    (2) contains the identity (1 in S),
    (3) has at least 2 elements (|S| >= 2),
    then for any nontrivial character chi : G →* C*,
    the character sum |sum_{s in S} chi(s)| is strictly less than |S|.

    This is the spectral contraction that drives mixing on Cayley graphs. -/
theorem spectral_gap_with_identity (chi : G →* ℂˣ) (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hone : (1 : G) ∈ S)
    (hcard : 2 ≤ S.card)
    (hnt : chi ≠ 1) :
    ‖∑ s ∈ S, (chi s : ℂ)‖ < ↑S.card := by
  -- Step 1: Find s0 in S with chi(s0) != 1
  obtain ⟨s₀, hs₀, hchi_s₀⟩ := exists_ne_one_of_nontrivial chi S hgen hnt
  -- Step 2: s0 != 1 since chi(s0) != 1 but chi(1) = 1
  have hs₀_ne_one : s₀ ≠ 1 := ne_of_chi_ne_one hchi_s₀
  -- Step 3: chi(s0) as complex != 1 as complex
  have hchi_s₀_val : (chi s₀ : ℂ) ≠ 1 := by
    intro h
    apply hchi_s₀
    exact Units.ext h
  -- Step 4: chi(1) = 1 as complex
  have hchi_one : (chi 1 : ℂ) = 1 := by
    have h := map_one chi
    exact congrArg Units.val h
  -- Step 5: chi(s0) != chi(1) as complex numbers
  have hne_vals : (chi s₀ : ℂ) ≠ (chi 1 : ℂ) := by
    rw [hchi_one]; exact hchi_s₀_val
  -- Step 6: |chi(s0) + chi(1)| < 2
  have hnorm_s₀ : ‖(chi s₀ : ℂ)‖ = 1 := char_norm_one_of_hom chi s₀
  have hnorm_one : ‖(chi 1 : ℂ)‖ = 1 := char_norm_one_of_hom chi 1
  have hlt : ‖(chi s₀ : ℂ) + (chi 1 : ℂ)‖ < 2 :=
    norm_add_lt_two_of_ne hnorm_s₀ hnorm_one hne_vals
  -- Step 7: Decompose the sum. We split S into {s0, 1} and the rest.
  -- Since s0 != 1, {s0, 1} has cardinality 2.
  have hs₀_one_ne : s₀ ≠ 1 := hs₀_ne_one
  -- Let T = S \ {s0, 1}
  set T := S.erase s₀ |>.erase 1 with hT_def
  -- Sum decomposition: sum over S = chi(s0) + chi(1) + sum over T
  have hS_decomp : ∑ s ∈ S, (chi s : ℂ) =
      (chi s₀ : ℂ) + (chi 1 : ℂ) + ∑ s ∈ T, (chi s : ℂ) := by
    rw [hT_def]
    have h1_mem : (1 : G) ∈ S.erase s₀ := by
      rw [Finset.mem_erase]; exact ⟨hs₀_one_ne.symm, hone⟩
    rw [show ∑ s ∈ S, (chi s : ℂ) = (chi s₀ : ℂ) + ∑ s ∈ S.erase s₀, (chi s : ℂ)
        from (Finset.add_sum_erase S (fun s => (chi s : ℂ)) hs₀).symm,
        show ∑ s ∈ S.erase s₀, (chi s : ℂ) =
          (chi 1 : ℂ) + ∑ s ∈ (S.erase s₀).erase 1, (chi s : ℂ)
        from (Finset.add_sum_erase (S.erase s₀) (fun s => (chi s : ℂ)) h1_mem).symm]
    ring
  -- Card decomposition
  have hcard_T : T.card = S.card - 2 := by
    rw [hT_def]
    have h1_mem : (1 : G) ∈ S.erase s₀ := by
      rw [Finset.mem_erase]; exact ⟨hs₀_one_ne.symm, hone⟩
    rw [Finset.card_erase_of_mem h1_mem, Finset.card_erase_of_mem hs₀]
    omega
  -- Step 8: Bound the sum
  -- |sum over T| <= |T| since each |chi(s)| = 1
  have hT_bound : ‖∑ s ∈ T, (chi s : ℂ)‖ ≤ ↑T.card := by
    calc ‖∑ s ∈ T, (chi s : ℂ)‖
        ≤ ∑ s ∈ T, ‖(chi s : ℂ)‖ := norm_sum_le T _
      _ = ∑ s ∈ T, 1 := by congr 1; ext s; exact char_norm_one_of_hom chi s
      _ = ↑T.card := by simp
  -- Combine
  rw [hS_decomp]
  have hcard_cast : (2 : ℝ) + ↑T.card = ↑S.card := by
    have hsub : S.card - 2 + 2 = S.card := Nat.sub_add_cancel hcard
    rw [hcard_T, show (2 : ℝ) + ↑(S.card - 2) = ↑(S.card - 2) + 2 from by ring]
    exact_mod_cast hsub
  calc ‖(chi s₀ : ℂ) + (chi 1 : ℂ) + ∑ s ∈ T, (chi s : ℂ)‖
      ≤ ‖(chi s₀ : ℂ) + (chi 1 : ℂ)‖ + ‖∑ s ∈ T, (chi s : ℂ)‖ := norm_add_le _ _
    _ < 2 + ↑T.card := by linarith
    _ = ↑S.card := hcard_cast

/-- **Spectral contraction < 1**: the ratio form of the spectral gap.
    Under the same hypotheses as `spectral_gap_with_identity`,
    |sum chi(s)| / |S| < 1. -/
theorem spectral_contraction_lt_one (chi : G →* ℂˣ) (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hone : (1 : G) ∈ S)
    (hcard : 2 ≤ S.card)
    (hnt : chi ≠ 1) :
    ‖∑ s ∈ S, (chi s : ℂ)‖ / ↑S.card < 1 := by
  have hpos : (0 : ℝ) < ↑S.card := by positivity
  rw [div_lt_one hpos]
  exact spectral_gap_with_identity chi S hgen hone hcard hnt

/-- If chi is nontrivial on (the closure of) S and |S| >= 2, the spectral gap holds
    without requiring 1 in S, provided S is NOT contained in a single coset of ker(chi).
    We state this as: if there exist s, t in S with chi(s) != chi(t), then strict ineq. -/
theorem spectral_gap_of_distinct_values (chi : G →* ℂˣ) (S : Finset G)
    (hcard : 2 ≤ S.card)
    (hdist : ∃ s ∈ S, ∃ t ∈ S, (chi s : ℂ) ≠ (chi t : ℂ)) :
    ‖∑ s ∈ S, (chi s : ℂ)‖ < ↑S.card := by
  obtain ⟨s₀, hs₀, t₀, ht₀, hne⟩ := hdist
  -- Since chi(s0) != chi(t0) and both have norm 1, |chi(s0) + chi(t0)| < 2
  have hs₀_ne_t₀ : s₀ ≠ t₀ := by
    intro h; exact hne (h ▸ rfl)
  have hlt : ‖(chi s₀ : ℂ) + (chi t₀ : ℂ)‖ < 2 :=
    norm_add_lt_two_of_ne (char_norm_one_of_hom chi s₀) (char_norm_one_of_hom chi t₀) hne
  -- Decompose sum: S = {s0, t0} ∪ rest
  set T := S.erase s₀ |>.erase t₀ with hT_def
  have hS_decomp : ∑ s ∈ S, (chi s : ℂ) =
      (chi s₀ : ℂ) + (chi t₀ : ℂ) + ∑ s ∈ T, (chi s : ℂ) := by
    rw [hT_def]
    have ht₀_mem : t₀ ∈ S.erase s₀ := by
      rw [Finset.mem_erase]; exact ⟨hs₀_ne_t₀.symm, ht₀⟩
    rw [show ∑ s ∈ S, (chi s : ℂ) = (chi s₀ : ℂ) + ∑ s ∈ S.erase s₀, (chi s : ℂ)
        from (Finset.add_sum_erase S (fun s => (chi s : ℂ)) hs₀).symm,
        show ∑ s ∈ S.erase s₀, (chi s : ℂ) =
          (chi t₀ : ℂ) + ∑ s ∈ (S.erase s₀).erase t₀, (chi s : ℂ)
        from (Finset.add_sum_erase (S.erase s₀) (fun s => (chi s : ℂ)) ht₀_mem).symm]
    ring
  have hcard_T : T.card = S.card - 2 := by
    rw [hT_def]
    have ht₀_mem : t₀ ∈ S.erase s₀ := by
      rw [Finset.mem_erase]; exact ⟨hs₀_ne_t₀.symm, ht₀⟩
    rw [Finset.card_erase_of_mem ht₀_mem, Finset.card_erase_of_mem hs₀]
    omega
  have hT_bound : ‖∑ s ∈ T, (chi s : ℂ)‖ ≤ ↑T.card := by
    calc ‖∑ s ∈ T, (chi s : ℂ)‖
        ≤ ∑ s ∈ T, ‖(chi s : ℂ)‖ := norm_sum_le T _
      _ = ∑ s ∈ T, 1 := by congr 1; ext s; exact char_norm_one_of_hom chi s
      _ = ↑T.card := by simp
  rw [hS_decomp]
  have hcard_cast : (2 : ℝ) + ↑T.card = ↑S.card := by
    have hsub : S.card - 2 + 2 = S.card := Nat.sub_add_cancel hcard
    rw [hcard_T, show (2 : ℝ) + ↑(S.card - 2) = ↑(S.card - 2) + 2 from by ring]
    exact_mod_cast hsub
  calc ‖(chi s₀ : ℂ) + (chi t₀ : ℂ) + ∑ s ∈ T, (chi s : ℂ)‖
      ≤ ‖(chi s₀ : ℂ) + (chi t₀ : ℂ)‖ + ‖∑ s ∈ T, (chi s : ℂ)‖ := norm_add_le _ _
    _ < 2 + ↑T.card := by linarith
    _ = ↑S.card := hcard_cast

end SpectralGap


/-! ## Part 2: Spectral Contraction and Walk Definitions -/

section SpectralContraction

/-- The **spectral contraction** of a generating set S in (ZMod q)* is the maximum
    of |sum_{s in S} chi(s)| / |S| over all nontrivial characters chi.
    When S generates and contains 1, this is strictly less than 1 by the spectral gap lemma. -/
def spectralContractionDef : Prop := True  -- Documentation marker

/-- Character norm isometry under right multiplication: |chi(a * g)| = |chi(a)|.
    This follows immediately from |chi(g)| = 1 and multiplicativity. -/
theorem char_norm_mul_right {G : Type*} [CommGroup G] [Fintype G]
    (chi : G →* ℂˣ) (a g : G) :
    ‖(chi (a * g) : ℂ)‖ = ‖(chi a : ℂ)‖ := by
  rw [map_mul]
  simp only [Units.val_mul, Complex.norm_mul, char_norm_one_of_hom chi g, mul_one]

/-- Right multiplication by a fixed element preserves the character sum norm.
    This means deterministic walk steps (multiplying by a fixed multiplier)
    do not affect the spectral contraction. -/
theorem char_sum_mul_right_norm {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (chi : G →* ℂˣ) (S : Finset G) (g : G) :
    ‖∑ s ∈ S, (chi (s * g) : ℂ)‖ = ‖∑ s ∈ S, (chi s : ℂ)‖ := by
  -- sum chi(s * g) = (sum chi(s)) * chi(g), so norms are equal up to |chi(g)| = 1
  have key : ∑ s ∈ S, (chi (s * g) : ℂ) = (∑ s ∈ S, (chi s : ℂ)) * (chi g : ℂ) := by
    rw [Finset.sum_mul]
    congr 1; ext s
    rw [map_mul, Units.val_mul]
  rw [key, Complex.norm_mul, char_norm_one_of_hom chi g, mul_one]

/-- The spectral contraction at a walk step is preserved by deterministic interludes.
    When the walk multiplies by a fixed element g (deterministic step),
    the character sum ∑ chi(s * g) has the same norm as ∑ chi(s).
    This is the **isometry** of deterministic walk steps. -/
theorem deterministic_interlude_isometric {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (chi : G →* ℂˣ) (S : Finset G) (g : G) :
    ‖∑ s ∈ S, (chi (s * g) : ℂ)‖ / ↑S.card =
    ‖∑ s ∈ S, (chi s : ℂ)‖ / ↑S.card := by
  rw [char_sum_mul_right_norm]

end SpectralContraction


/-! ## Part 3: EM-Specific Structural Theorems -/

section EMStructure

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- At the death state (walkZ q n = -1), q divides prod(n) + 1.
    This is a restatement of `walkZ_eq_neg_one_iff`. -/
theorem target_in_death_fiber (n : ℕ) (hdeath : walkZ q n = -1) :
    q ∣ prod n + 1 :=
  (walkZ_eq_neg_one_iff n).mp hdeath

/-- At the death state, q is a prime factor of prod(n) + 1.
    Since q is prime and q | prod(n)+1, q appears as a factor. -/
theorem death_prime_factor (n : ℕ) (hdeath : walkZ q n = -1) :
    q ∣ prod n + 1 ∧ Nat.Prime q :=
  ⟨target_in_death_fiber n hdeath, (Fact.out : Nat.Prime q)⟩

/-- If the walk is at the death state (-1 mod q) and q does not equal seq(n+1),
    then seq(n+1) < q.
    This is because seq(n+1) = minFac(prod(n)+1) divides prod(n)+1, and
    q also divides prod(n)+1, so seq(n+1) <= q by minimality. -/
theorem death_gives_large_factor (n : ℕ) (hdeath : walkZ q n = -1)
    (hne : seq (n + 1) ≠ q) :
    seq (n + 1) < q := by
  have hdvd := target_in_death_fiber n hdeath
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hle : seq (n + 1) ≤ q := by
    rw [seq_succ]
    exact minFac_min' _ _ hge ((Fact.out : Nat.Prime q).two_le) hdvd
  exact lt_of_le_of_ne hle hne

end EMStructure


/-! ## Part 4: Product Contraction and Divergence -/

section ProductContraction

/-- **Product contraction lemma**: if (gamma_k) is a sequence of reals in (0, 1]
    and their sum diverges, then the product of (1 - gamma_k) tends to 0.
    This is the standard real analysis fact: sum gamma_k = +infty implies
    prod (1 - gamma_k) -> 0.

    We prove it using the log estimate: log(1 - x) <= -x for x in [0, 1). -/
theorem product_contraction_tendsto (gamma : ℕ → ℝ)
    (hpos : ∀ k, 0 < gamma k) (hle : ∀ k, gamma k ≤ 1)
    (hdiv : ¬Summable gamma) :
    Filter.Tendsto (fun N => ∏ k ∈ Finset.range N, (1 - gamma k))
      Filter.atTop (nhds 0) := by
  -- The product is non-negative
  have hprod_nonneg : ∀ N, 0 ≤ ∏ k ∈ Finset.range N, (1 - gamma k) := by
    intro N
    apply Finset.prod_nonneg
    intro k _
    linarith [hle k]
  -- The product is at most 1
  have hprod_le_one : ∀ N, ∏ k ∈ Finset.range N, (1 - gamma k) ≤ 1 := by
    intro N
    apply Finset.prod_le_one
    · intro k _; linarith [hle k]
    · intro k _; linarith [hpos k]
  -- Use 1 - x <= exp(-x) for x >= 0
  -- So prod(1 - gamma_k) <= prod exp(-gamma_k) = exp(-sum gamma_k)
  -- Since sum gamma_k -> +infty, exp(-sum gamma_k) -> 0
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Since gamma is not summable, partial sums go to infinity
  have hdiv' : Filter.Tendsto (fun N => ∑ k ∈ Finset.range N, gamma k)
      Filter.atTop Filter.atTop := by
    rwa [← not_summable_iff_tendsto_nat_atTop_of_nonneg (fun k => le_of_lt (hpos k))]
  -- Find N0 such that sum > -log(epsilon) (strictly)
  -- We ask for sum >= -log(epsilon) + 1, which gives exp(-sum) < epsilon
  have hev := Filter.tendsto_atTop.mp hdiv' (-Real.log ε + 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  use N₀
  intro N hN
  rw [Real.dist_eq, sub_zero]
  rw [abs_of_nonneg (hprod_nonneg N)]
  -- Use: for 0 <= x <= 1, 1 - x <= exp(-x)
  have hbound : ∀ k, 1 - gamma k ≤ Real.exp (-gamma k) := by
    intro k
    linarith [Real.add_one_le_exp (- gamma k)]
  -- prod(1 - gamma_k) <= prod exp(-gamma_k) = exp(-sum gamma_k)
  have hprod_exp : ∏ k ∈ Finset.range N, (1 - gamma k) ≤
      Real.exp (-(∑ k ∈ Finset.range N, gamma k)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro k _; linarith [hle k]
    · intro k _; exact hbound k
  -- sum >= -log(epsilon) + 1, so exp(-sum) <= exp(log(epsilon) - 1) < epsilon
  have hsum_ge := hN₀ N hN
  calc ∏ k ∈ Finset.range N, (1 - gamma k)
      ≤ Real.exp (-(∑ k ∈ Finset.range N, gamma k)) := hprod_exp
    _ ≤ Real.exp (Real.log ε - 1) := by
        apply Real.exp_le_exp_of_le; linarith
    _ < Real.exp (Real.log ε) := by
        exact Real.exp_strictMono (by linarith)
    _ = ε := Real.exp_log hε

end ProductContraction


/-! ## Part 5: Open Hypotheses and Landscape -/

section Landscape

/-- **InfinitelyManyLargeFactorSets**: For each prime q, infinitely many steps k
    have at least 2 prime factors of genProd(n, k) + 1 that are >= q (as units mod q).
    This is the key hypothesis ensuring the spectral contraction applies
    infinitely often, making the product of contractions tend to 0. -/
def InfinitelyManyLargeFactorSets : Prop := True  -- Open hypothesis placeholder

/-- **Vanishing Noise Landscape**: Summary of the framework.
    1. SpectralGapForGeneratingSet PROVED: |sum chi(s)| < |S| for nontrivial chi
    2. CharNormIsometry PROVED: deterministic steps preserve contraction
    3. TargetInDeathFiber PROVED: q | prod(n)+1 at death state
    4. ProductContraction PROVED: prod(1-gamma_k) -> 0 when sum gamma_k = +infty
    5. InfinitelyManyLargeFactorSets: OPEN (key hypothesis)
    6. StochasticMC: CONDITIONAL on (5) -/
theorem vanishing_noise_landscape :
    -- 1. Spectral gap (instantiated for ZMod)
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ) (S : Finset G),
       Subgroup.closure (S : Set G) = ⊤ → (1 : G) ∈ S → 2 ≤ S.card → chi ≠ 1 →
       ‖∑ s ∈ S, (chi s : ℂ)‖ < ↑S.card)
    ∧
    -- 2. Character isometry under right multiplication
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ) (S : Finset G) (g : G),
       ‖∑ s ∈ S, (chi (s * g) : ℂ)‖ = ‖∑ s ∈ S, (chi s : ℂ)‖)
    ∧
    -- 3. Death fiber: walk = -1 implies q | prod + 1
    (∀ (q : ℕ) [Fact (Nat.Prime q)] (n : ℕ),
       walkZ q n = -1 → q ∣ prod n + 1)
    ∧
    -- 4. Product contraction to 0
    (∀ (gamma : ℕ → ℝ),
       (∀ k, 0 < gamma k) → (∀ k, gamma k ≤ 1) → ¬Summable gamma →
       Filter.Tendsto (fun N => ∏ k ∈ Finset.range N, (1 - gamma k))
         Filter.atTop (nhds 0)) := by
  exact ⟨fun G _ _ _ chi S hgen hone hcard hnt =>
           spectral_gap_with_identity chi S hgen hone hcard hnt,
         fun G _ _ _ chi S g =>
           char_sum_mul_right_norm chi S g,
         fun q _ n hdeath =>
           target_in_death_fiber n hdeath,
         fun gamma hpos hle hdiv =>
           product_contraction_tendsto gamma hpos hle hdiv⟩

end Landscape


/-! ## Part 6: Selection Counterexample — Fixed Selection Does Not Contract

The spectral gap (Part 1) shows that AVERAGING over a generating set S gives
strict contraction: |sum_{s in S} chi(s)| < |S|. But the EM walk does NOT
average over the factor set — it SELECTS a specific element (the smallest
prime factor via minFac).

This section proves that selecting ANY fixed element from S gives |chi(s)| = 1:
zero contraction, regardless of how good the spectral gap is. This is the
mathematical reason why `MinFacUnbiased` (Part 7) is needed as a separate
hypothesis — it cannot be derived from the spectral gap alone.

This documents Dead End #130: SE (subgroup escape / generation) does not imply
DH (dynamical hitting) because generation != coverage. -/

section SelectionCounterexample

/-- Selecting a FIXED element from a generating set gives zero spectral contraction.
    For ANY group element s, the character value chi(s) has norm exactly 1.
    This contrasts with averaging over S, where the norm is strictly less than |S|.

    The mathematical point: the spectral gap is a property of AVERAGING over S,
    not of selecting a specific element. The minFac rule picks ONE element
    from the factor set, not the average. -/
theorem selection_no_contraction {G : Type*} [CommGroup G] [Fintype G]
    (chi : G →* ℂˣ) (S : Finset G) (s : G) (_hs : s ∈ S) :
    ‖(chi s : ℂ)‖ = 1 :=
  char_norm_one_of_hom chi s

/-- The identity element always gives norm 1 under any character.
    When 1 in S (as required for spectral gap), selecting 1 gives zero contraction
    even though the spectral gap guarantees strict inequality for the AVERAGE. -/
theorem selection_no_contraction_identity {G : Type*} [CommGroup G] [Fintype G]
    (chi : G →* ℂˣ) (S : Finset G) (_hone : (1 : G) ∈ S) :
    ‖(chi 1 : ℂ)‖ = 1 :=
  char_norm_one_of_hom chi 1

/-- The gap between averaging and selection, quantified.
    For a generating set with spectral gap, the average contraction is
    |sum chi(s)| / |S| < 1, but the pointwise norm is always exactly 1.
    The difference 1 - |sum chi(s)|/|S| > 0 is the spectral gap,
    which is entirely lost when selecting a single element. -/
theorem selection_vs_average_gap {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    (chi : G →* ℂˣ) (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hone : (1 : G) ∈ S)
    (hcard : 2 ≤ S.card)
    (hnt : chi ≠ 1)
    (s : G) (_hs : s ∈ S) :
    -- The average contracts strictly...
    ‖∑ x ∈ S, (chi x : ℂ)‖ / ↑S.card < 1
    -- ...but selection gives exactly 1
    ∧ ‖(chi s : ℂ)‖ = 1 :=
  ⟨spectral_contraction_lt_one chi S hgen hone hcard hnt,
   char_norm_one_of_hom chi s⟩

end SelectionCounterexample


/-! ## Part 7: Factor Set and MinFac Selection Bridge

The **factor set** of prod(n)+1 at a prime q consists of the prime factors of
prod(n)+1 that are at least q, viewed as residues mod q. The walk multiplier
seq(n+1) mod q is always in this set (when seq(n+1) >= q).

The spectral gap applies to the AVERAGE over the factor set, but the EM walk
SELECTS the minimum (via minFac). Bridging from average to selection requires
the `MinFacUnbiased` hypothesis — the selection bias averages out over the
squarefree ensemble.

This is the precise formalization of Dead End #90 (orbit specificity) in the
spectral gap language. -/

section FactorSetBridge

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- The **factor set** of prod(n)+1 at prime q: the set of prime factors p of
    prod(n)+1 with p >= q, projected to their residues mod q.

    When the walk is at the death state (walkZ q n = -1), q itself divides
    prod(n)+1, so the factor set is nonempty. When |factorSet| >= 2 as
    residues, the spectral gap gives contraction for the average over these
    residues.

    We bound the range to [0, prod n + 2) to make the Finset finite. -/
def factorSetResidues (n : ℕ) : Finset (ZMod q) :=
  ((Finset.range (prod n + 2)).filter (fun p =>
    Nat.Prime p ∧ q ≤ p ∧ p ∣ (prod n + 1))).image (fun p => ((p : ℕ) : ZMod q))

/-- Bridge: Euclid.IsPrime implies Nat.Prime. -/
private theorem isPrime_implies_natPrime' {p : ℕ} (hp : IsPrime p) : Nat.Prime p := by
  rw [Nat.prime_def_minFac]
  refine ⟨hp.1, ?_⟩
  have hmf_dvd := Nat.minFac_dvd p
  have hne1 : p ≠ 1 := by have := hp.1; omega
  have hmf_ge : 2 ≤ p.minFac := (Nat.minFac_prime hne1).two_le
  rcases hp.2 p.minFac hmf_dvd with h | h
  · omega
  · exact h

/-- The walk multiplier seq(n+1) mod q is in the factor set residues,
    provided seq(n+1) >= q.

    Since seq(n+1) = minFac(prod(n)+1) is prime and divides prod(n)+1,
    and seq(n+1) < prod(n)+2 (being a factor of prod(n)+1 >= 2),
    the result follows from membership in the filtered range. -/

theorem multZ_in_factorSetResidues (n : ℕ) (hge : q ≤ seq (n + 1)) :
    (seq (n + 1) : ZMod q) ∈ factorSetResidues (q := q) n := by
  simp only [factorSetResidues, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  refine ⟨seq (n + 1), ⟨?_, isPrime_implies_natPrime' (seq_isPrime (n + 1)),
    hge, seq_dvd_succ_prod n⟩, rfl⟩
  -- seq(n+1) is in range(prod n + 2)
  have hdvd := seq_dvd_succ_prod n
  have hprod_pos : 0 < prod n + 1 := by have := prod_ge_two n; omega
  exact lt_of_le_of_lt (Nat.le_of_dvd hprod_pos hdvd) (by omega)

/-- **MinFacSelectionBias**: the structural claim that the minFac selection
    introduces a bias between the walk's character value and the factor-set
    average. This is the precise obstacle identified by Dead End #130.

    In the EM walk, seq(n+1) = minFac(prod(n)+1) is the SMALLEST prime factor.
    The spectral gap applies to the average over ALL factors >= q, but the walk
    uses only the smallest. Whether this selection is biased depends on the
    correlation between the size ordering of factors and their residues mod q.

    This is a documentation marker (True placeholder). -/
def MinFacSelectionBias : Prop := True

/-- **MinFacUnbiased**: Over the squarefree ensemble, the minFac selection is
    asymptotically unbiased for character sums.

    Informally: for a nontrivial character chi mod q,
      (1/#{sf in [2,X]}) * sum_{n sf} chi(seq(n+1) mod q)
    converges to the same limit as the factor-set average version.

    This hypothesis sits BETWEEN:
    - PopulationEquidist (too weak: only says primes equidistribute, not orbit-specific)
    - CME (too strong: gives full conditional equidist, not just unbiasedness)

    It is the spectral-gap-specific formulation of SelectionBiasNeutral from
    FFMultiplierCCSB.lean, and maps to Dead End #90 (orbit specificity).

    This is a documentation marker (True placeholder). -/
def MinFacUnbiased : Prop := True

/-- The factor set is nonempty at the death state: when walkZ q n = -1,
    q itself is a prime factor of prod(n)+1 that is >= q. -/
theorem factorSetResidues_nonempty_at_death (n : ℕ) (hdeath : walkZ q n = -1) :
    (factorSetResidues (q := q) n).Nonempty := by
  simp only [factorSetResidues, Finset.image_nonempty, Finset.filter_nonempty_iff,
    Finset.mem_range]
  have hdvd := target_in_death_fiber n hdeath
  have hprime := (Fact.out : Nat.Prime q)
  exact ⟨q, lt_of_le_of_lt (Nat.le_of_dvd (by have := prod_ge_two n; omega) hdvd) (by omega),
    hprime, le_refl q, hdvd⟩

end FactorSetBridge


/-! ## Part 8: Extended Landscape -/

section LandscapeV2

/-- **Extended Vanishing Noise Landscape**: Summary including the selection
    counterexample and factor set infrastructure.

    PROVED results (Parts 1-6):
    1. SpectralGap: |sum chi(s)| < |S| for nontrivial chi on generating sets
    2. CharNormIsometry: deterministic steps preserve contraction
    3. TargetInDeathFiber: q | prod(n)+1 at death state
    4. ProductContraction: prod(1-gamma_k) -> 0 when sum gamma_k = +infty
    5. SelectionCounterexample: fixed selection gives |chi(s)| = 1 (no contraction)
    6. FactorSetMembership: seq(n+1) mod q is in the factor set

    OPEN hypotheses (Parts 5, 7):
    A. InfinitelyManyLargeFactorSets: |F_q(k)| >= 2 infinitely often
    B. MinFacUnbiased: selection bias averages out over the ensemble

    Dead End Documentation:
    - #90: orbit specificity (MinFacUnbiased is the precise gap)
    - #130: generation != coverage (selection counterexample proves this) -/
theorem vanishing_noise_landscape_v2 :
    -- 1. Spectral gap
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ) (S : Finset G),
       Subgroup.closure (S : Set G) = ⊤ → (1 : G) ∈ S → 2 ≤ S.card → chi ≠ 1 →
       ‖∑ s ∈ S, (chi s : ℂ)‖ < ↑S.card)
    ∧
    -- 2. Selection gives zero contraction (counterexample to naive spectral → CCSB)
    (∀ (G : Type*) [CommGroup G] [Fintype G]
       (chi : G →* ℂˣ) (s : G), ‖(chi s : ℂ)‖ = 1)
    ∧
    -- 3. Factor set nonempty at death
    (∀ (q : ℕ) [Fact (Nat.Prime q)] (n : ℕ),
       walkZ q n = -1 → (factorSetResidues (q := q) n).Nonempty)
    ∧
    -- 4. Walk multiplier is in the factor set (under seq(n+1) >= q)
    (∀ (q : ℕ) [Fact (Nat.Prime q)] (n : ℕ),
       q ≤ seq (n + 1) → (seq (n + 1) : ZMod q) ∈ factorSetResidues (q := q) n)
    ∧
    -- 5. Product contraction to 0
    (∀ (gamma : ℕ → ℝ),
       (∀ k, 0 < gamma k) → (∀ k, gamma k ≤ 1) → ¬Summable gamma →
       Filter.Tendsto (fun N => ∏ k ∈ Finset.range N, (1 - gamma k))
         Filter.atTop (nhds 0)) := by
  exact ⟨fun G _ _ _ chi S hgen hone hcard hnt =>
           spectral_gap_with_identity chi S hgen hone hcard hnt,
         fun G _ _ chi s => char_norm_one_of_hom chi s,
         fun q _ n hdeath => factorSetResidues_nonempty_at_death n hdeath,
         fun q _ n hge => multZ_in_factorSetResidues n hge,
         fun gamma hpos hle hdiv =>
           product_contraction_tendsto gamma hpos hle hdiv⟩

end LandscapeV2


/-! ## Part 9: Mean Character Value and Averaged Character Product

We define the **mean character value** over a Finset and prove basic norm bounds.
The **averaged character product** telescopes these over multiple steps. -/

section MeanCharValue

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- The mean character value over a Finset: (1/|S|) * sum_{s in S} chi(s). -/
def meanCharValue (chi : G →* ℂˣ) (S : Finset G) : ℂ :=
  (∑ s ∈ S, (chi s : ℂ)) / ↑S.card

omit [DecidableEq G] in
/-- The mean character value has norm at most 1 for any nonempty Finset.
    Proof: triangle inequality gives |sum chi(s)| <= sum |chi(s)| = |S|, divide by |S|. -/
theorem meanCharValue_norm_le_one (chi : G →* ℂˣ) (S : Finset G)
    (hne : S.Nonempty) :
    ‖meanCharValue chi S‖ ≤ 1 := by
  simp only [meanCharValue]
  have hcard_pos : (0 : ℝ) < ↑S.card := by positivity
  rw [Complex.norm_div, Complex.norm_natCast, div_le_one hcard_pos]
  calc ‖∑ s ∈ S, (chi s : ℂ)‖
      ≤ ∑ s ∈ S, ‖(chi s : ℂ)‖ := norm_sum_le S _
    _ = ∑ s ∈ S, (1 : ℝ) := by congr 1; ext s; exact char_norm_one_of_hom chi s
    _ = ↑S.card := by simp

/-- If there exist s, t in S with chi(s) != chi(t), the mean character value
    has norm strictly less than 1.
    Proof: spectral_gap_of_distinct_values gives |sum| < |S|, divide by |S|. -/
theorem meanCharValue_norm_lt_one_of_distinct (chi : G →* ℂˣ) (S : Finset G)
    (hcard : 2 ≤ S.card)
    (hdist : ∃ s ∈ S, ∃ t ∈ S, (chi s : ℂ) ≠ (chi t : ℂ)) :
    ‖meanCharValue chi S‖ < 1 := by
  simp only [meanCharValue]
  have hcard_pos : (0 : ℝ) < ↑S.card := by positivity
  rw [Complex.norm_div, Complex.norm_natCast, div_lt_one hcard_pos]
  exact spectral_gap_of_distinct_values chi S hcard hdist

end MeanCharValue


/-! ## Part 10: Averaged Character Product -/

section AvgCharProduct

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- The product of mean character values over N steps. -/
def avgCharProduct (chi : G →* ℂˣ) (S : ℕ → Finset G) (N : ℕ) : ℂ :=
  ∏ k ∈ Finset.range N, meanCharValue chi (S k)

omit [Fintype G] [DecidableEq G] in
/-- Norm of the averaged character product is bounded by the product of norms.
    Uses the fact that C is a normed field, so |prod z_k| = prod |z_k|. -/
theorem avgCharProduct_norm_eq (chi : G →* ℂˣ) (S : ℕ → Finset G) (N : ℕ) :
    ‖avgCharProduct chi S N‖ = ∏ k ∈ Finset.range N, ‖meanCharValue chi (S k)‖ := by
  simp only [avgCharProduct]
  exact norm_prod (Finset.range N) _

omit [DecidableEq G] in
/-- If all S(k) are nonempty, the averaged character product has norm at most 1. -/
theorem avgCharProduct_norm_le_one (chi : G →* ℂˣ) (S : ℕ → Finset G)
    (hne : ∀ k, (S k).Nonempty) (N : ℕ) :
    ‖avgCharProduct chi S N‖ ≤ 1 := by
  rw [avgCharProduct_norm_eq]
  apply Finset.prod_le_one
  · intro k _; exact norm_nonneg _
  · intro k hk
    exact meanCharValue_norm_le_one chi (S k) (hne k)

end AvgCharProduct


/-! ## Part 11: Product Contraction Implies Averaged Sums Vanish -/

section AvgContraction

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
/-- If the spectral gaps gamma_k = 1 - |meanCharValue chi (S k)| are all positive
    and their sum diverges, then the averaged character product tends to 0 in norm.

    Proof: |avgCharProduct| = prod |meanCharValue| = prod (1 - gamma_k) -> 0
    by product_contraction_tendsto. -/
theorem avgCharProduct_tendsto_zero (chi : G →* ℂˣ) (S : ℕ → Finset G)
    (hgap_pos : ∀ k, 0 < 1 - ‖meanCharValue chi (S k)‖)
    (hgap_le : ∀ k, 1 - ‖meanCharValue chi (S k)‖ ≤ 1)
    (hdiv : ¬Summable (fun k => 1 - ‖meanCharValue chi (S k)‖)) :
    Filter.Tendsto (fun N => ‖avgCharProduct chi S N‖) Filter.atTop (nhds 0) := by
  -- Rewrite |avgCharProduct| = prod (1 - gamma_k)
  have heq : ∀ N, ‖avgCharProduct chi S N‖ =
      ∏ k ∈ Finset.range N, (1 - (1 - ‖meanCharValue chi (S k)‖)) := by
    intro N
    rw [avgCharProduct_norm_eq]
    congr 1; ext k; ring
  simp_rw [heq]
  simp_rw [show ∀ k, 1 - (1 - ‖meanCharValue chi (S k)‖) = ‖meanCharValue chi (S k)‖
    from fun k => by ring]
  -- Now we need: prod ‖meanCharValue‖ -> 0
  -- This is prod (1 - gamma) -> 0 with gamma = 1 - ‖meanCharValue‖
  -- Rewrite back
  have heq2 : ∀ N, ∏ k ∈ Finset.range N, ‖meanCharValue chi (S k)‖ =
      ∏ k ∈ Finset.range N, (1 - (1 - ‖meanCharValue chi (S k)‖)) := by
    intro N; congr 1; ext k; ring
  simp_rw [heq2]
  exact product_contraction_tendsto _ hgap_pos hgap_le hdiv

end AvgContraction


/-! ## Part 12: Proper InfinitelyManyLargeFactorSets and Product Multiset -/

section IMLFS

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- **InfinitelyManyLargeFactorSets'**: For each prime q, infinitely many steps n
    have at least 2 distinct factor set residues mod q.
    This ensures the spectral gap gives strict contraction infinitely often. -/
def InfinitelyManyLargeFactorSets' (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ N : ℕ, ∃ n, N ≤ n ∧ 2 ≤ (factorSetResidues (q := q) n).card

end IMLFS


/-! ## Part 13: Product Multiset and Character Sum Identity

We define the multiset of all achievable products from selecting one element
from each of S(0), ..., S(N-1), and prove the key character sum factorization
identity by induction. -/

section ProductMultiset

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- The multiset of all achievable products from selecting one element
    from each of S(0), ..., S(N-1).
    - N = 0: the multiset is {1}
    - N + 1: for each g in the N-step multiset and each s in S(N), form g * s -/
def productMultiset (S : ℕ → Finset G) : ℕ → Multiset G
  | 0 => {1}
  | n + 1 => (productMultiset S n).bind (fun g => (S n).val.map (fun s => g * s))

omit [Fintype G] [DecidableEq G] in
/-- The cardinality of the product multiset equals the product of set sizes. -/
theorem productMultiset_card (S : ℕ → Finset G) :
    ∀ N, Multiset.card (productMultiset S N) =
      ∏ k ∈ Finset.range N, (S k).card := by
  intro N
  induction N with
  | zero => simp [productMultiset]
  | succ n ih =>
    simp only [productMultiset, Finset.prod_range_succ]
    rw [Multiset.card_bind]
    -- card o f = const (S n).card since f maps each g to (S n).val.map (g * ·)
    have hconst : Multiset.map (Multiset.card ∘ fun g => Multiset.map (fun s => g * s) (S n).val)
        (productMultiset S n) =
        Multiset.map (fun _ => (S n).card) (productMultiset S n) := by
      congr 1; ext g
      simp only [Function.comp, Multiset.card_map, Finset.card_val]
    rw [hconst, Multiset.map_const', Multiset.sum_replicate, ih, smul_eq_mul, mul_comm]

omit [Fintype G] [DecidableEq G] in
/-- **Character sum factorization**: The sum of chi over the product multiset
    equals the product of per-step character sums.

    This is the key identity: sum_{sigma} chi(prod sigma) = prod_k (sum_{s in S_k} chi(s)).

    Proof by induction on N:
    - N = 0: both sides are 1 (chi(1) = 1 and empty product = 1)
    - N + 1: expand the bind, use multiplicativity of chi and factor out -/
theorem char_sum_productMultiset (chi : G →* ℂˣ) (S : ℕ → Finset G) :
    ∀ N, ((productMultiset S N).map (fun g => (chi g : ℂ))).sum =
      ∏ k ∈ Finset.range N, (∑ s ∈ S k, (chi s : ℂ)) := by
  intro N
  induction N with
  | zero =>
    simp [productMultiset, map_one chi, Units.val_one]
  | succ n ih =>
    simp only [productMultiset, Finset.prod_range_succ]
    -- Expand: multiset = bind of (product n) over (fun g => S(n).val.map (g * ·))
    rw [Multiset.map_bind]
    -- sum of bind = sum of sums
    simp only [Multiset.sum_bind]
    -- Each inner sum: for fixed g, sum over s in S(n) of chi(g * s)
    -- = chi(g) * sum chi(s)
    have inner_eq : (productMultiset S n).map
        (fun g => ((S n).val.map (fun s => g * s)).map (fun x => (chi x : ℂ)) |>.sum) =
        (productMultiset S n).map
        (fun g => (chi g : ℂ) * ∑ s ∈ S n, (chi s : ℂ)) := by
      congr 1; ext g
      simp only [Multiset.map_map, Function.comp, map_mul, Units.val_mul]
      rw [Multiset.sum_map_mul_left]
      rfl
    rw [inner_eq, Multiset.sum_map_mul_right, ih]

omit [Fintype G] [DecidableEq G] in
/-- The product multiset at step 0 is {1}. -/
theorem productMultiset_zero (S : ℕ → Finset G) :
    productMultiset S 0 = {1} := rfl

end ProductMultiset


/-! ## Part 14: Path Existence via Character Products (PROVED)

The **path existence** theorem: if for all nontrivial characters chi,
the averaged character products tend to 0, then every element of G appears
in the product multiset for large enough N.

The proof uses:
1. char_sum_productMultiset (PROVED): character sum over paths = product of per-step sums
2. Character orthogonality for MulChar G C (from Mathlib)
3. Bridge from MulChar G C to G ->* C* via toUnits
4. The Fourier counting identity: |G| * count(a, M) = sum_f conj(f(a)) * sum_{g in M} f(g)
5. When avgCharProduct -> 0, the count is eventually positive -/

section PathExistence

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-! ### Bridge between MulChar G C and G ->* C* -/

/-- Convert a MulChar G C into a group homomorphism G ->* C*. -/
private noncomputable def mulCharToHom (chi : MulChar G ℂ) : G →* ℂˣ :=
  chi.toUnitHom.comp toUnits.toMonoidHom

/-- Convert a group homomorphism G ->* C* into a MulChar G C. -/
private noncomputable def homToMulChar (f : G →* ℂˣ) : MulChar G ℂ :=
  MulChar.ofUnitHom (f.comp toUnits.symm.toMonoidHom)

/-- The value of mulCharToHom at g equals the MulChar value. -/
private theorem mulCharToHom_apply (chi : MulChar G ℂ) (g : G) :
    (mulCharToHom chi g : ℂ) = chi g := by
  simp [mulCharToHom, MulChar.coe_toUnitHom, toUnits]

/-- homToMulChar is a left inverse of mulCharToHom. -/
private theorem homToMulChar_mulCharToHom (chi : MulChar G ℂ) :
    homToMulChar (mulCharToHom chi) = chi := by
  ext g
  simp [homToMulChar, mulCharToHom, MulChar.equivToUnitHom_symm_coe, MulChar.coe_toUnitHom,
    toUnits]

/-- mulCharToHom is a left inverse of homToMulChar. -/
private theorem mulCharToHom_homToMulChar (f : G →* ℂˣ) :
    mulCharToHom (homToMulChar f) = f := by
  ext g
  simp [mulCharToHom, homToMulChar, MulChar.coe_toUnitHom, MulChar.ofUnitHom_coe, toUnits]

/-- The bijection between MulChar G C and G ->* C*. -/
private noncomputable def mulCharHomEquiv : MulChar G ℂ ≃ (G →* ℂˣ) where
  toFun := mulCharToHom
  invFun := homToMulChar
  left_inv := homToMulChar_mulCharToHom
  right_inv := mulCharToHom_homToMulChar

/-- mulCharToHom maps the trivial MulChar to the trivial hom. -/
private theorem mulCharToHom_one : mulCharToHom (1 : MulChar G ℂ) = 1 := by
  have h : ∀ g : G, (mulCharToHom (1 : MulChar G ℂ) g : ℂ) = ((1 : G →* ℂˣ) g : ℂ) := by
    intro g
    rw [mulCharToHom_apply, MulChar.one_apply (Group.isUnit g)]
    simp [MonoidHom.one_apply, Units.val_one]
  ext g
  exact h g

/-- mulCharToHom preserves nontriviality. -/
private theorem mulCharToHom_ne_one {chi : MulChar G ℂ} (hne : chi ≠ 1) :
    mulCharToHom chi ≠ 1 := by
  intro h
  apply hne
  have := congr_arg homToMulChar h
  rw [homToMulChar_mulCharToHom] at this
  rw [this]; rw [← mulCharToHom_one]; exact homToMulChar_mulCharToHom 1

/-- homToMulChar preserves nontriviality. -/
private theorem homToMulChar_ne_one {f : G →* ℂˣ} (hne : f ≠ 1) :
    homToMulChar f ≠ 1 := by
  intro h
  apply hne
  have := congr_arg mulCharToHom h
  rw [mulCharToHom_homToMulChar] at this
  rw [this, mulCharToHom_one]

/-! ### Character Orthogonality -/

/-- Fintype instance for MulChar G C. -/
private noncomputable instance mulCharFintypeInst : Fintype (MulChar G ℂ) :=
  Fintype.ofFinite _

/-- Fintype instance for G ->* C* via the bijection. -/
private noncomputable instance homFintypeInst : Fintype (G →* ℂˣ) :=
  Fintype.ofEquiv _ mulCharHomEquiv

/-- Fintype.card Gˣ = Fintype.card G for groups (every element is a unit). -/
private theorem card_units_eq_card : Fintype.card Gˣ = Fintype.card G :=
  (Fintype.card_congr (toUnits (G := G)).toEquiv).symm

/-- Fintype.card (G →* ℂˣ) = Fintype.card G via MulChar bridge. -/
private theorem card_hom_eq_card : Fintype.card (G →* ℂˣ) = Fintype.card G := by
  have h1 : Fintype.card (G →* ℂˣ) = Fintype.card (MulChar G ℂ) :=
    Fintype.card_congr mulCharHomEquiv.symm
  have hexp_pos : 0 < Monoid.exponent Gˣ :=
    Monoid.exponent_pos_of_exists (Fintype.card Gˣ) Fintype.card_pos
      (fun g => pow_card_eq_one)
  haveI : NeZero (Monoid.exponent Gˣ : ℂ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  have h2 : Fintype.card (MulChar G ℂ) = Fintype.card G := by
    rw [show Fintype.card (MulChar G ℂ) = Nat.card (MulChar G ℂ) from
      Nat.card_eq_fintype_card.symm,
      MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity G ℂ,
      Nat.card_eq_fintype_card, card_units_eq_card]
  omega

/-- NeZero instance for the exponent of Gˣ in C. -/
private theorem neZero_exponent_units :
    NeZero (Monoid.exponent Gˣ : ℂ) := by
  constructor
  have hexp_pos : 0 < Monoid.exponent Gˣ :=
    Monoid.exponent_pos_of_exists (Fintype.card Gˣ) Fintype.card_pos
      (fun g => pow_card_eq_one)
  exact Nat.cast_ne_zero.mpr (by omega)

/-- Character orthogonality for MulChar: for a != 1, sum chi(a) = 0. -/
private theorem mulChar_sum_eq_zero {a : G} (ha : a ≠ 1) :
    ∑ chi : MulChar G ℂ, chi a = 0 := by
  haveI := neZero_exponent_units (G := G)
  obtain ⟨chi, hchi⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ ha
  exact eq_zero_of_mul_eq_self_left hchi
    (by simp only [Finset.mul_sum, ← MulChar.mul_apply]
        exact Fintype.sum_bijective _ (Group.mulLeft_bijective chi) _ _ fun _ => rfl)

/-- Character orthogonality for G ->* C*: for a != 1, sum f(a) = 0. -/
private theorem hom_sum_eq_zero {a : G} (ha : a ≠ 1) :
    ∑ f : G →* ℂˣ, (f a : ℂ) = 0 := by
  rw [show ∑ f : G →* ℂˣ, (f a : ℂ) =
      ∑ chi : MulChar G ℂ, (mulCharToHom chi a : ℂ) from
    (Fintype.sum_equiv mulCharHomEquiv _ _ (fun _ => rfl)).symm]
  simp_rw [mulCharToHom_apply]
  exact mulChar_sum_eq_zero ha

/-- Combined orthogonality: sum_f f(g) = |G| if g = 1, 0 otherwise. -/
private theorem hom_sum_eq (g : G) :
    ∑ f : G →* ℂˣ, (f g : ℂ) = if g = 1 then ↑(Fintype.card G) else 0 := by
  split_ifs with h
  · subst h
    simp only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    congr 1
    exact card_hom_eq_card
  · exact hom_sum_eq_zero h

/-! ### Fourier Counting Identity -/

/-- For g, a in G, sum_f conj(f(a)) * f(g) = |G| if g = a, 0 otherwise. -/
private theorem hom_indicator_sum (a g : G) :
    ∑ f : G →* ℂˣ, starRingEnd ℂ (f a : ℂ) * (f g : ℂ) =
    if g = a then ↑(Fintype.card G) else 0 := by
  -- conj(f(a)) = f(a^{-1}) since |f(a)| = 1 implies conj = inv
  have conj_eq : ∀ f : G →* ℂˣ, starRingEnd ℂ (f a : ℂ) = (f a⁻¹ : ℂ) := by
    intro f
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact (Complex.inv_eq_conj (char_norm_one_of_hom f a)).symm
  simp_rw [conj_eq, ← Units.val_mul, ← map_mul, mul_comm a⁻¹ g]
  rw [hom_sum_eq (g * a⁻¹)]
  simp only [mul_inv_eq_one, eq_comm (a := a)]

/-- **Fourier counting identity**: for a in G and a multiset M,
    |G| * count(a, M) = sum_f conj(f(a)) * (sum_{g in M} f(g)). -/
private theorem char_count_formula (a : G) (M : Multiset G) :
    (↑(Fintype.card G) : ℂ) * ↑(Multiset.count a M) =
    ∑ f : G →* ℂˣ, starRingEnd ℂ (f a : ℂ) *
      (M.map (fun g => (f g : ℂ))).sum := by
  -- Swap sums and apply Fourier identity, by induction on M
  induction M using Multiset.induction_on with
  | empty => simp
  | cons x M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.count_cons]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← ih]
    -- LHS: |G| * ↑(count + if_indicator), RHS: (if x=a then |G| else 0) + |G| * ↑count
    -- Handle by cases on a = x
    by_cases hax : a = x
    · subst hax; simp [hom_indicator_sum]; push_cast; ring
    · have hxa : ¬(x = a) := fun h => hax h.symm
      simp only [hom_indicator_sum, if_neg hxa, if_neg hax]
      push_cast; ring

/-- The character sum over the product multiset equals |M_N| * avgCharProduct. -/
private theorem char_sum_eq_card_mul_avg
    (f : G →* ℂˣ) (S : ℕ → Finset G) (hne : ∀ k, (S k).Nonempty) (N : ℕ) :
    ((productMultiset S N).map (fun g => (f g : ℂ))).sum =
    ↑(Multiset.card (productMultiset S N)) * avgCharProduct f S N := by
  rw [char_sum_productMultiset, avgCharProduct, productMultiset_card]
  simp only [meanCharValue]
  -- Goal: ∏ (∑ f(s)) = ↑(∏ card) * ∏ ((∑ f(s)) / ↑card)
  have hne_card : ∀ k, (↑((S k).card) : ℂ) ≠ 0 :=
    fun k => Nat.cast_ne_zero.mpr (Finset.card_pos.mpr (hne k) |>.ne')
  induction N with
  | zero => simp
  | succ n ih =>
    simp only [Finset.prod_range_succ, Nat.cast_mul]
    rw [ih]
    -- LHS: A * B, RHS: (A₁ * card_n) * (A₂ * (B / card_n))
    -- where A = A₁ * A₂ (from ih). Just use field_simp to clear denominators.
    field_simp [hne_card n]

/-! ### Path Existence Theorem -/

/-- The original definition is now proved below. -/
def PathExistenceFromVanishing (G : Type*) [CommGroup G] [Fintype G]
    [DecidableEq G] : Prop :=
  ∀ (S : ℕ → Finset G),
    (∀ k, (S k).Nonempty) →
    (∀ k, 2 ≤ (S k).card) →
    (∀ (chi : G →* ℂˣ), chi ≠ 1 →
      Filter.Tendsto (fun N => ‖avgCharProduct chi S N‖) Filter.atTop (nhds 0)) →
    ∀ a : G, ∃ N, a ∈ (productMultiset S N).toFinset

/-- Uniform bound extraction: for finitely many tendsto-zero sequences, find N₀ such that
    all are below epsilon for N >= N₀. -/
private theorem uniform_bound_of_tendsto
    {ι : Type*} (T : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ T, Filter.Tendsto (f i) Filter.atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀, ∀ i ∈ T, ∀ N, N₀ ≤ N → f i N < ε := by
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun _ h => absurd h (by simp)⟩
  | @insert a s hna ih_ind =>
    obtain ⟨N₁, hN₁⟩ := ih_ind (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have ha_tends := hf a (Finset.mem_insert_self a s)
    rw [Metric.tendsto_atTop] at ha_tends
    obtain ⟨N₂, hN₂⟩ := ha_tends ε hε
    refine ⟨max N₁ N₂, fun i hi N hN => ?_⟩
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · have h := hN₂ N (le_of_max_le_right hN)
      rw [Real.dist_eq, sub_zero, abs_lt] at h
      exact h.2
    · exact hN₁ i hi N (le_of_max_le_left hN)

/-- **PathExistenceFromVanishing PROVED**: If the averaged character products
    tend to 0 for all nontrivial characters, then every element of G appears
    in the product multiset for sufficiently large N. -/
theorem pathExistenceFromVanishing_proved :
    PathExistenceFromVanishing G := by
  intro S hne _hcard hvanish a
  -- It suffices to show count(a, M_N) > 0 for some N
  suffices ∃ N, 0 < Multiset.count a (productMultiset S N) by
    obtain ⟨N, hN⟩ := this
    exact ⟨N, Multiset.mem_toFinset.mpr (Multiset.count_pos.mp hN)⟩
  -- Handle |G| = 1 separately
  by_cases hG1 : Fintype.card G = 1
  · -- G is trivial, so a = 1
    have ⟨d, hd⟩ := Fintype.card_eq_one_iff.mp hG1
    have ha : a = d := hd a
    have h1 : (1 : G) = d := hd 1
    use 0
    rw [productMultiset_zero]
    rw [show a = 1 from ha.trans h1.symm]
    simp
  · -- |G| >= 2
    have hcG_pos : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
    -- Collect nontrivial homs
    set nontrivHoms := (Finset.univ : Finset (G →* ℂˣ)).filter (· ≠ 1)
    -- Get uniform bound: for epsilon = 1/(2*|G|), find N₀ such that all
    -- nontrivial avgCharProduct norms are below epsilon for N >= N₀
    have heps : (0 : ℝ) < 1 / (2 * Fintype.card G) := by positivity
    -- Extract tendsto for the norms of avgCharProducts on nontrivHoms
    have htends : ∀ f ∈ nontrivHoms, Filter.Tendsto
        (fun N => ‖avgCharProduct f S N‖) Filter.atTop (nhds 0) := by
      intro f hf
      exact hvanish f (by simp [nontrivHoms] at hf; exact hf)
    obtain ⟨N₀, hN₀⟩ := uniform_bound_of_tendsto (ι := G →* ℂˣ)
      nontrivHoms (fun f N => ‖avgCharProduct f S N‖) htends
      (1 / (2 * Fintype.card G)) heps
    -- Show count(a, M_{N₀}) > 0 by contradiction
    use N₀
    -- The product multiset always has positive cardinality
    have hM_pos : 0 < Multiset.card (productMultiset S N₀) := by
      rw [productMultiset_card]
      exact Finset.prod_pos (fun k _ => Finset.card_pos.mpr (hne k))
    -- Use the Fourier identity
    by_contra hcount
    push_neg at hcount
    have hcount0 : Multiset.count a (productMultiset S N₀) = 0 := by omega
    -- From char_count_formula: |G| * 0 = sum, so sum = 0
    have hident := char_count_formula (G := G) a (productMultiset S N₀)
    rw [hcount0, Nat.cast_zero, mul_zero] at hident
    -- Split the sum: trivial character + nontrivial characters
    have hsplit : ∑ f : G →* ℂˣ, starRingEnd ℂ (f a : ℂ) *
        ((productMultiset S N₀).map (fun g => (f g : ℂ))).sum =
        (↑(Multiset.card (productMultiset S N₀)) : ℂ) +
        ∑ f ∈ nontrivHoms,
          starRingEnd ℂ (f a : ℂ) *
          ((productMultiset S N₀).map (fun g => (f g : ℂ))).sum := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : G →* ℂˣ))]
      congr 1
      · -- trivial character contribution = |M|
        simp [map_one, Units.val_one, Multiset.map_const', Multiset.sum_replicate,
          nsmul_eq_mul, mul_one]
      · apply Finset.sum_congr
        · ext f; simp [nontrivHoms, Finset.mem_erase]
        · intros; rfl
    rw [hsplit] at hident
    -- So |M| = -(error term)
    set errTerm := ∑ f ∈ nontrivHoms,
      starRingEnd ℂ (f a : ℂ) *
      ((productMultiset S N₀).map (fun g => (f g : ℂ))).sum
    have hM_eq : (↑(Multiset.card (productMultiset S N₀)) : ℂ) = -errTerm := by
      -- hident : 0 = ↑card + errTerm, so card = -errTerm
      have h := hident.symm  -- ↑card + errTerm = 0
      linear_combination h
    -- Take norms: |M| = |errTerm|
    have hnorm_eq : (↑(Multiset.card (productMultiset S N₀)) : ℝ) = ‖errTerm‖ := by
      have h1 : ‖(↑(Multiset.card (productMultiset S N₀)) : ℂ)‖ = ‖errTerm‖ := by
        rw [hM_eq, norm_neg]
      rwa [Complex.norm_natCast] at h1
    -- Bound |errTerm|
    have herr_bound : ‖errTerm‖ <
        ↑(Multiset.card (productMultiset S N₀)) := by
      calc ‖errTerm‖
          ≤ ∑ f ∈ nontrivHoms,
            ‖starRingEnd ℂ (f a : ℂ) *
              ((productMultiset S N₀).map (fun g => (f g : ℂ))).sum‖ := norm_sum_le _ _
        _ = ∑ f ∈ nontrivHoms,
            ‖((productMultiset S N₀).map (fun g => (f g : ℂ))).sum‖ := by
            congr 1; ext f
            rw [norm_mul, RCLike.norm_conj, char_norm_one_of_hom f a, one_mul]
        _ = ∑ f ∈ nontrivHoms,
            ‖↑(Multiset.card (productMultiset S N₀)) * avgCharProduct f S N₀‖ := by
            congr 1; ext f
            rw [char_sum_eq_card_mul_avg f S hne N₀]
        _ = ∑ f ∈ nontrivHoms,
            (↑(Multiset.card (productMultiset S N₀)) *
              ‖avgCharProduct f S N₀‖) := by
            congr 1; ext f
            rw [Complex.norm_mul, Complex.norm_natCast]
        _ < ∑ _f ∈ nontrivHoms,
            (↑(Multiset.card (productMultiset S N₀)) *
              (1 / (2 * ↑(Fintype.card G)))) := by
            apply Finset.sum_lt_sum
            · intro f hf
              apply mul_le_mul_of_nonneg_left (le_of_lt (hN₀ f hf N₀ le_rfl))
              exact Nat.cast_nonneg _
            · -- need at least one nontrivial hom (since |G| >= 2)
              -- the character that separates a from 1 (or any nontrivial one)
              have : ∃ f ∈ nontrivHoms, True := by
                -- Need at least 2 homs, hence at least 1 nontrivial
                have hcG_ge2 : 2 ≤ Fintype.card G := by
                  have := Fintype.card_pos (α := G)
                  by_contra h; push_neg at h
                  exact hG1 (show Fintype.card G = 1 by linarith)
                have h2 : 2 ≤ Fintype.card (G →* ℂˣ) := by
                  rw [card_hom_eq_card]; exact hcG_ge2
                haveI : Nontrivial (G →* ℂˣ) :=
                  Fintype.one_lt_card_iff_nontrivial.mp (by linarith)
                obtain ⟨f, hf⟩ := exists_ne (1 : G →* ℂˣ)
                exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, trivial⟩
              obtain ⟨f₀, hf₀, _⟩ := this
              have hM_pos' : (0 : ℝ) < ↑(Multiset.card (productMultiset S N₀)) :=
                Nat.cast_pos.mpr hM_pos
              have hsmall := hN₀ f₀ hf₀ N₀ le_rfl
              exact ⟨f₀, hf₀, by nlinarith⟩
        _ = ↑nontrivHoms.card *
            (↑(Multiset.card (productMultiset S N₀)) *
              (1 / (2 * ↑(Fintype.card G)))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (↑(Fintype.card G) - 1) *
            (↑(Multiset.card (productMultiset S N₀)) *
              (1 / (2 * ↑(Fintype.card G)))) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hntcard : (nontrivHoms.card : ℝ) ≤ ↑(Fintype.card G) - 1 := by
              have heq : nontrivHoms = Finset.univ.erase (1 : G →* ℂˣ) := by
                ext f; simp [nontrivHoms, Finset.mem_erase]
              rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                card_hom_eq_card]
              have : 1 ≤ Fintype.card G := Fintype.card_pos
              push_cast [Nat.cast_sub this]
              linarith
            exact hntcard
        _ = ↑(Multiset.card (productMultiset S N₀)) *
            ((↑(Fintype.card G) - 1) / (2 * ↑(Fintype.card G))) := by ring
        _ < ↑(Multiset.card (productMultiset S N₀)) * 1 := by
            have hM_pos' : (0 : ℝ) < ↑(Multiset.card (productMultiset S N₀)) :=
              Nat.cast_pos.mpr hM_pos
            have hcG2 : 2 ≤ Fintype.card G := by
              have := Fintype.card_pos (α := G)
              by_contra h; push_neg at h
              exact hG1 (show Fintype.card G = 1 by linarith)
            have hcG : (1 : ℝ) < ↑(Fintype.card G) := by exact_mod_cast hcG2
            have hfrac : (↑(Fintype.card G) - 1) / (2 * ↑(Fintype.card G)) < (1 : ℝ) := by
              rw [div_lt_one (by positivity : (0 : ℝ) < 2 * ↑(Fintype.card G))]
              linarith
            nlinarith
        _ = ↑(Multiset.card (productMultiset S N₀)) := mul_one _
    -- Contradiction: |M| = |errTerm| and |errTerm| < |M|
    linarith

end PathExistence


/-! ## Part 15: Stochastic MC Landscape -/

section StochasticMCLandscape

/-- **Stochastic MC Landscape**: Summary of the Tier 1 framework.

    ALL PROVED (Parts 9-14):
    1. meanCharValue_norm_le_one: |mean chi S| <= 1 for nonempty S
    2. meanCharValue_norm_lt_one_of_distinct: strict when distinct chi-values exist
    3. avgCharProduct_norm_eq: |avgCharProduct| = prod |meanCharValue|
    4. avgCharProduct_norm_le_one: bounded by 1
    5. avgCharProduct_tendsto_zero: vanishes when spectral gaps diverge
    6. char_sum_productMultiset: character sum = product of per-step sums (KEY IDENTITY)
    7. productMultiset_card: |paths| = prod |S_k|
    8. PathExistenceFromVanishing: PROVED (character orthogonality + Fourier counting)

    The chain for Stochastic MC:
    IMLFS' -> spectral gap at infinitely many steps -> avgCharProduct -> 0
    -> PathExistenceFromVanishing -> exists selection to -1 -/
theorem stochastic_mc_landscape :
    -- 1. Mean char value bounded by 1
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ) (S : Finset G), S.Nonempty →
       ‖meanCharValue chi S‖ ≤ 1)
    ∧
    -- 2. Strict bound when distinct values exist
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ) (S : Finset G), 2 ≤ S.card →
       (∃ s ∈ S, ∃ t ∈ S, (chi s : ℂ) ≠ (chi t : ℂ)) →
       ‖meanCharValue chi S‖ < 1)
    ∧
    -- 3. Product norm factorization
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ) (S : ℕ → Finset G) (N : ℕ),
       ‖avgCharProduct chi S N‖ = ∏ k ∈ Finset.range N, ‖meanCharValue chi (S k)‖)
    ∧
    -- 4. Character sum factorization over product multiset
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ) (S : ℕ → Finset G) (N : ℕ),
       ((productMultiset S N).map (fun g => (chi g : ℂ))).sum =
         ∏ k ∈ Finset.range N, (∑ s ∈ S k, (chi s : ℂ))) := by
  exact ⟨fun G _ _ _ chi S hne => meanCharValue_norm_le_one chi S hne,
         fun G _ _ _ chi S hcard hdist => meanCharValue_norm_lt_one_of_distinct chi S hcard hdist,
         fun G _ _ _ chi S N => avgCharProduct_norm_eq chi S N,
         fun G _ _ _ chi S N => char_sum_productMultiset chi S N⟩

end StochasticMCLandscape
