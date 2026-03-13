import EM.Reduction.DSLInfra
import EM.Equidist.Bootstrap
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex

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
