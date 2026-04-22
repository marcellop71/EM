import EM.Population.WeakMullin
import EM.Equidist.Sieve

/-!
# Profinite Avoidance Tube

Structural consequences of missing primes: if many primes are missing from
the EM sequence, the multiplier at each step is constrained to avoid a
forbidden class at each missing prime. The "tube ratio" ∏(q-2)/(q-1)
measures the proportion of allowed multiplier classes.

## Main Results

### S90. Tube Ratio
* `tubeRatio` : product ∏_{q∈F} (q-2)/(q-1) measuring "allowed fraction"
* `tubeRatio_nonneg` : tubeRatio ≥ 0 for F ⊆ {primes ≥ 3}
* `tubeRatio_le_one` : tubeRatio ≤ 1 for F ⊆ {primes ≥ 3}
* `tubeRatio_monotone` : F ⊆ G → tubeRatio G ≤ tubeRatio F

### S91. Tube Collapse under ¬WM
* `tube_collapse` : ¬WM → tubeRatio can be made arbitrarily small

### S92. Confined Excess Energy (abstract)
* `confined_visit_energy_lb` : V(a)=0 ⇒ ∑V² ≥ N²/(p-2) (any walk, any unit)
* `confined_excess_energy_lb` : V(a)=0 ⇒ excessEnergy ≥ N²/(p-2)

### S93. Rogue Character (abstract)
* `rogue_character_exists` : V(a)=0 ⇒ ∃ χ≠1 with ‖S_χ‖² ≥ N²/(p-2)²
* `rogue_character_linear_lb` : ‖S_χ‖ ≥ N/(p-2)

### S94. SVE Contradicts Avoidance
* `sve_contradicts_avoidance` : SVE ⇒ for large N, no unit can have V(a)=0

### S95. Landscape
* `avoidance_tube_landscape` : 5-clause conjunction
-/

open Mullin Euclid MullinGroup RotorRouter
open Finset

/-! ## S90. Tube Ratio -/

section TubeRatio

/-- Tube ratio for a finite set of primes: ∏_{q∈F} (q-2)/(q-1).
    This is the "proportion of allowed multiplier classes" when the walk
    must avoid 1 forbidden class at each of |F| primes. -/
noncomputable def tubeRatio (F : Finset Nat) : ℝ :=
  ∏ q ∈ F, ((q : ℝ) - 2) / ((q : ℝ) - 1)

/-- Each factor (q-2)/(q-1) is nonneg for q ≥ 3. -/
private theorem tube_factor_nonneg {q : Nat} (hq : 3 ≤ q) :
    0 ≤ ((q : ℝ) - 2) / ((q : ℝ) - 1) :=
  div_nonneg (by linarith [show (3 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hq])
    (by linarith [show (3 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hq])

/-- Each factor (q-2)/(q-1) is ≤ 1 for q ≥ 3. -/
private theorem tube_factor_le_one {q : Nat} (hq : 3 ≤ q) :
    ((q : ℝ) - 2) / ((q : ℝ) - 1) ≤ 1 := by
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    linarith [show (3 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hq]
  rw [div_le_one hq1]; linarith

/-- tubeRatio F ≥ 0 when all q ∈ F satisfy q ≥ 3. -/
theorem tubeRatio_nonneg {F : Finset Nat} (hF : ∀ q ∈ F, 3 ≤ q) :
    0 ≤ tubeRatio F :=
  Finset.prod_nonneg (fun q hq => tube_factor_nonneg (hF q hq))

/-- tubeRatio F ≤ 1 when all q ∈ F satisfy q ≥ 3. -/
theorem tubeRatio_le_one {F : Finset Nat} (hF : ∀ q ∈ F, 3 ≤ q) :
    tubeRatio F ≤ 1 :=
  Finset.prod_le_one (fun q hq => tube_factor_nonneg (hF q hq))
    (fun q hq => tube_factor_le_one (hF q hq))

/-- tubeRatio is monotone decreasing: F ⊆ G → tubeRatio G ≤ tubeRatio F. -/
theorem tubeRatio_monotone {F G : Finset Nat}
    (hFG : F ⊆ G) (hG : ∀ q ∈ G, 3 ≤ q) :
    tubeRatio G ≤ tubeRatio F := by
  unfold tubeRatio
  calc ∏ q ∈ G, ((q : ℝ) - 2) / ((q : ℝ) - 1)
      = (∏ q ∈ G \ F, ((q : ℝ) - 2) / ((q : ℝ) - 1)) *
        (∏ q ∈ F, ((q : ℝ) - 2) / ((q : ℝ) - 1)) := by
          rw [← Finset.prod_union (Finset.sdiff_disjoint),
              Finset.sdiff_union_of_subset hFG]
    _ ≤ 1 * (∏ q ∈ F, ((q : ℝ) - 2) / ((q : ℝ) - 1)) := by
          apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg
            (fun q hq => tube_factor_nonneg (hG q (hFG hq))))
          exact Finset.prod_le_one
            (fun q hq => tube_factor_nonneg (hG q (Finset.sdiff_subset hq)))
            (fun q hq => tube_factor_le_one (hG q (Finset.sdiff_subset hq)))
    _ = ∏ q ∈ F, ((q : ℝ) - 2) / ((q : ℝ) - 1) := one_mul _

/-- tubeRatio equals the reciprocal of the inverted product. -/
theorem tubeRatio_eq_inv_prod {F : Finset Nat}
    (hF : ∀ q ∈ F, 3 ≤ q) :
    tubeRatio F = (∏ q ∈ F, ((q : ℝ) - 1) / ((q : ℝ) - 2))⁻¹ := by
  unfold tubeRatio
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro q hq
  have hq2 : ((q : ℝ) - 2) ≠ 0 := by
    linarith [show (3 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hF q hq]
  rw [inv_div]

/-- tubeRatio of empty set is 1. -/
theorem tubeRatio_empty : tubeRatio ∅ = 1 := Finset.prod_empty

/-- tubeRatio of singleton. -/
theorem tubeRatio_singleton (q : Nat) :
    tubeRatio {q} = ((q : ℝ) - 2) / ((q : ℝ) - 1) := by
  simp [tubeRatio]

end TubeRatio

/-! ## S91. Tube Collapse under ¬WM -/

section TubeCollapse

open Classical

/-- Under ¬WM, the tube ratio can be made arbitrarily small.
    not_wm_product_diverges gives ∏(q-1)/(q-2) ≥ C for any C.
    Since tubeRatio = (∏(q-1)/(q-2))⁻¹, we get tubeRatio < ε. -/
theorem tube_collapse (hnwm : ¬ WeakMullin) :
    ∀ ε : ℝ, 0 < ε → ∃ F : Finset Nat,
      (↑F : Set Nat) ⊆ MissingPrimes ∧ tubeRatio F < ε := by
  intro ε hε
  -- Ask for 1/ε + 1 to get strict inequality
  obtain ⟨F, hF_sub, hF_prod⟩ := not_wm_product_diverges hnwm (1 / ε + 1)
  have hF_ge3 : ∀ q ∈ F, 3 ≤ q := by
    intro q hq
    have ⟨hqp, hqne⟩ := hF_sub (Finset.mem_coe.mpr hq)
    have hge2 := hqp.two_le
    have h2 : q ≠ 2 := fun heq => hqne 0 (by rw [seq_zero]; exact heq.symm)
    omega
  refine ⟨F, hF_sub, ?_⟩
  rw [tubeRatio_eq_inv_prod hF_ge3]
  have hprod_pos : 0 < ∏ q ∈ F, ((q : ℝ) - 1) / ((q : ℝ) - 2) :=
    Finset.prod_pos (fun q hq => by
      have hq3 := hF_ge3 q hq
      exact div_pos (by linarith [show (3 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hq3])
        (by linarith [show (3 : ℝ) ≤ (q : ℝ) from by exact_mod_cast hq3]))
  -- hF_prod: 1/ε + 1 ≤ ∏...  so  ε⁻¹ < ∏...
  have hprod_strict : ε⁻¹ < ∏ q ∈ F, ((q : ℝ) - 1) / ((q : ℝ) - 2) := by
    rw [← one_div]; linarith
  rw [inv_lt_comm₀ hprod_pos hε]; exact hprod_strict

end TubeCollapse

/-! ## S92. Confined Excess Energy (abstract)

These results hold for ANY walk on (ZMod p)ˣ where some unit is never visited.
The "confinement" comes from an avoided unit, not from the EM structure. -/

section ConfinedEnergy

open DirichletCharacter

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP_AT : NeZero p := ⟨hp.out.ne_zero⟩

/-- Confined Cauchy-Schwarz: when one unit is never visited, the visit counts
    are distributed among at most p-2 units. By Cauchy-Schwarz over the
    p-2 non-avoided units: ∑ V(a)² ≥ N²/(p-2).

    This is strictly stronger than `visit_energy_lower_bound` which gives
    N²/(p-1) from Cauchy-Schwarz over all p-1 units. -/
theorem confined_visit_energy_lb {N : ℕ}
    (w : Fin N → (ZMod p)ˣ)
    (avoided : (ZMod p)ˣ)
    (hp3 : 3 ≤ p)
    (hmiss : walkVisitCount w avoided = 0) :
    (N : ℝ) ^ 2 / ((p : ℝ) - 2) ≤
    ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) ^ 2 := by
  have hsum : ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℕ) = N := walkVisitCount_sum w
  set S := Finset.univ.erase avoided
  have hS_card_eq : S.card = p - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ZMod.card_units_eq_totient, Nat.totient_prime hp.out]; omega
  have hsum_S : ∑ a ∈ S, (walkVisitCount w a : ℝ) = (N : ℝ) := by
    have h : ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) = (N : ℝ) := by
      exact_mod_cast hsum
    have h2 := Finset.add_sum_erase Finset.univ
      (fun a => (walkVisitCount w a : ℝ)) (Finset.mem_univ avoided)
    simp only at h2
    rw [hmiss, Nat.cast_zero, zero_add] at h2
    linarith
  have cs := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun (_ : (ZMod p)ˣ) => (1 : ℝ)) (fun a => (walkVisitCount w a : ℝ))
  simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at cs
  rw [hsum_S] at cs
  have hS_sub : ∑ a ∈ S, (walkVisitCount w a : ℝ) ^ 2 ≤
      ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun _ _ _ => by positivity)
  have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by
    linarith [show (3 : ℝ) ≤ (p : ℝ) from by exact_mod_cast hp3]
  have hS_cast : (S.card : ℝ) = (p : ℝ) - 2 := by
    rw [hS_card_eq]; push_cast [Nat.cast_sub (by omega : 2 ≤ p)]; ring
  rw [hS_cast] at cs
  have h_total : (N : ℝ) ^ 2 ≤ ((p : ℝ) - 2) *
      ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) ^ 2 :=
    cs.trans (mul_le_mul_of_nonneg_left hS_sub (le_of_lt hp2_pos))
  rw [div_le_iff₀ hp2_pos]; linarith [mul_comm ((p : ℝ) - 2) (∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) ^ 2)]

/-- Confined excess energy: when some unit is never visited,
    excessEnergy ≥ N²/(p-2).

    Proof: ∑V² ≥ N²/(p-2) (confined Cauchy-Schwarz), so
    (p-1)·∑V² ≥ (p-1)·N²/(p-2), hence
    excessEnergy = (p-1)·∑V² - N² ≥ (p-1)·N²/(p-2) - N² = N²/(p-2). -/
theorem confined_excess_energy_lb {N : ℕ}
    (w : Fin N → (ZMod p)ˣ)
    (avoided : (ZMod p)ˣ)
    (hp3 : 3 ≤ p)
    (hmiss : walkVisitCount w avoided = 0) :
    (N : ℝ) ^ 2 / ((p : ℝ) - 2) ≤ excessEnergy w := by
  unfold excessEnergy
  have hVlb := confined_visit_energy_lb w avoided hp3 hmiss
  have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by
    linarith [show (3 : ℝ) ≤ (p : ℝ) from by exact_mod_cast hp3]
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  -- hVlb: N²/(p-2) ≤ ∑V²
  -- Goal: N²/(p-2) ≤ (p-1)·∑V² - N²
  -- Suffices: N²/(p-2) + N² ≤ (p-1)·∑V²
  -- i.e., N²·(p-1)/(p-2) ≤ (p-1)·∑V²
  -- i.e., N²/(p-2) ≤ ∑V² ✓ (= hVlb, times (p-1))
  -- Goal: N²/(p-2) ≤ (p-1)·∑V² - N²
  -- From hVlb: ∑V² ≥ N²/(p-2), so (p-1)·∑V² ≥ (p-1)·N²/(p-2)
  -- Need: (p-1)·N²/(p-2) - N² ≥ N²/(p-2)
  -- i.e., (p-1)·N²/(p-2) ≥ N² + N²/(p-2) = N²·(p-2+1)/(p-2) = N²·(p-1)/(p-2) ✓
  suffices h : (N : ℝ) ^ 2 / ((p : ℝ) - 2) + (N : ℝ) ^ 2 ≤
      ((p : ℝ) - 1) * ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) ^ 2 by linarith
  have hmul := mul_le_mul_of_nonneg_left hVlb (le_of_lt hp1_pos)
  -- hmul: (p-1)·(N²/(p-2)) ≤ (p-1)·∑V²
  -- Need: N²/(p-2) + N² ≤ (p-1)·(N²/(p-2))
  -- i.e., N² ≤ (p-1-1)·N²/(p-2) = (p-2)·N²/(p-2) = N² ✓
  -- Goal: N²/(p-2) ≤ (p-1)*∑V² - N²
  -- Suffices: N²/(p-2) + N² ≤ (p-1)*∑V²
  suffices h : (N : ℝ) ^ 2 / ((p : ℝ) - 2) + (N : ℝ) ^ 2 ≤
      ((p : ℝ) - 1) * ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) ^ 2 by linarith
  -- From hmul: (p-1)*(N²/(p-2)) ≤ (p-1)*∑V²
  -- Need: N²/(p-2) + N² ≤ (p-1)*(N²/(p-2))
  -- i.e., N² ≤ (p-2)*(N²/(p-2)), which is N² ≤ N² by mul_div_cancel
  have hstep : (N : ℝ) ^ 2 / ((p : ℝ) - 2) + (N : ℝ) ^ 2 ≤
      ((p : ℝ) - 1) * ((N : ℝ) ^ 2 / ((p : ℝ) - 2)) := by
    have hdiv_cancel : ((p : ℝ) - 2) * ((N : ℝ) ^ 2 / ((p : ℝ) - 2)) = (N : ℝ) ^ 2 :=
      mul_div_cancel₀ _ (ne_of_gt hp2_pos)
    -- (p-1)*(N²/(p-2)) = N²/(p-2) + (p-2)*(N²/(p-2)) = N²/(p-2) + N²
    nlinarith
  linarith

end ConfinedEnergy

/-! ## S93. Rogue Character Existence (abstract) -/

section RogueCharacter

open DirichletCharacter Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP_RC : NeZero p := ⟨hp.out.ne_zero⟩

/-- Pigeonhole for finite sums: if ∑_{x∈S} f(x) ≥ B and S is nonempty,
    then ∃ x ∈ S with f(x) ≥ B / |S|. -/
private theorem pigeonhole_sum {α : Type*} {S : Finset α} {f : α → ℝ}
    {B : ℝ}
    (hS : S.Nonempty) (_hf : ∀ x ∈ S, 0 ≤ f x) (hsum : B ≤ ∑ x ∈ S, f x) :
    ∃ x ∈ S, B / S.card ≤ f x := by
  by_contra h; push Not at h
  have hcard_pos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  obtain ⟨x₀, hx₀⟩ := hS
  have hlt : ∑ x ∈ S, f x < ∑ x ∈ S, (fun _ => B / S.card) x :=
    Finset.sum_lt_sum (fun x hx => le_of_lt (h x hx))
      ⟨x₀, hx₀, h _ hx₀⟩
  simp only [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ B (ne_of_gt hcard_pos)] at hlt
  linarith

/-- The number of nontrivial Dirichlet characters mod p is p - 2. -/
private theorem nontrivial_dirichlet_card :
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).card = p - 2 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p,
    Nat.totient_prime hp.out]
  omega

/-- Nontrivial Dirichlet characters exist for p ≥ 3. -/
private theorem nontrivial_dirichlet_nonempty (hp3 : 3 ≤ p) :
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hcard := nontrivial_dirichlet_card (hp := hp)
  rw [h, Finset.card_empty] at hcard; omega

/-- Rogue character: when some unit is never visited, some nontrivial
    Dirichlet character has ‖S_χ(N)‖² ≥ N²/(p-2)².

    Proof: confined excess energy gives ∑_{χ≠1} ‖S_χ‖² ≥ N²/(p-2).
    There are p-2 nontrivial characters, so by pigeonhole some
    ‖S_χ‖² ≥ (N²/(p-2))/(p-2) = N²/(p-2)². -/
theorem rogue_character_exists {N : ℕ}
    (w : Fin N → (ZMod p)ˣ)
    (avoided : (ZMod p)ˣ)
    (hp3 : 3 ≤ p) (_hN : 0 < N)
    (hmiss : walkVisitCount w avoided = 0) :
    ∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧
      (N : ℝ) ^ 2 / ((p : ℝ) - 2) ^ 2 ≤
      ‖∑ n : Fin N, χ (↑(w n) : ZMod p)‖ ^ 2 := by
  have hexcess := confined_excess_energy_lb w avoided hp3 hmiss
  rw [excess_energy_eq_nontrivial_sum] at hexcess
  set S := Finset.univ.erase (1 : DirichletCharacter ℂ p)
  set f := fun χ : DirichletCharacter ℂ p =>
    ‖∑ n : Fin N, χ (↑(w n) : ZMod p)‖ ^ 2
  have hf_nn : ∀ χ ∈ S, 0 ≤ f χ := fun _ _ => by positivity
  obtain ⟨χ, hχS, hχ_lb⟩ := pigeonhole_sum (nontrivial_dirichlet_nonempty hp3)
    hf_nn hexcess
  refine ⟨χ, (Finset.mem_erase.mp hχS).1, ?_⟩
  have hcard : (S.card : ℝ) = (p : ℝ) - 2 := by
    rw [nontrivial_dirichlet_card]
    push_cast [Nat.cast_sub (by omega : 2 ≤ p)]; ring
  rw [hcard, div_div] at hχ_lb
  have : ((p : ℝ) - 2) ^ 2 = ((p : ℝ) - 2) * ((p : ℝ) - 2) := by ring
  rw [this]; exact hχ_lb

/-- Rogue character gives linear lower bound on character sum norm:
    ‖S_χ(N)‖ ≥ N/(p-2). -/
theorem rogue_character_linear_lb {N : ℕ}
    (w : Fin N → (ZMod p)ˣ)
    (avoided : (ZMod p)ˣ)
    (hp3 : 3 ≤ p) (hN : 0 < N)
    (hmiss : walkVisitCount w avoided = 0) :
    ∃ χ : DirichletCharacter ℂ p, χ ≠ 1 ∧
      (N : ℝ) / ((p : ℝ) - 2) ≤
      ‖∑ n : Fin N, χ (↑(w n) : ZMod p)‖ := by
  obtain ⟨χ, hχne, hχ_lb⟩ := rogue_character_exists w avoided hp3 hN hmiss
  refine ⟨χ, hχne, ?_⟩
  have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by
    linarith [show (3 : ℝ) ≤ (p : ℝ) from by exact_mod_cast hp3]
  have hN_nn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hnorm_nn := norm_nonneg (∑ n : Fin N, χ (↑(w n) : ZMod p))
  -- From ‖S‖² ≥ N²/(p-2)² = (N/(p-2))², deduce ‖S‖ ≥ N/(p-2)
  have h_sq : (N / ((p : ℝ) - 2)) ^ 2 ≤
      ‖∑ n : Fin N, χ (↑(w n) : ZMod p)‖ ^ 2 := by
    rw [div_pow]; exact hχ_lb
  nlinarith [sq_nonneg (‖∑ n : Fin N, χ (↑(w n) : ZMod p)‖ - N / ((p : ℝ) - 2)),
    sq_abs (N / ((p : ℝ) - 2))]

end RogueCharacter

/-! ## S94. SVE Contradicts Avoidance

SubquadraticVisitEnergy gives excessEnergy ≤ ε·N² for large N.
But confined excess energy gives excessEnergy ≥ N²/(p-2) when V(a)=0.
These are contradictory for small ε, so SVE forces every unit to be
visited (for large N). -/

section SVEContradictsAvoidance

open DirichletCharacter Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP_SVE : NeZero p := ⟨hp.out.ne_zero⟩

/-- SVE contradicts avoidance: if the excess energy is subquadratic,
    then for large N, no unit can have V(a) = 0.

    Proof: If V(a) = 0, then excessEnergy ≥ N²/(p-2) > 0.
    But SVE with ε = 1/(2(p-2)) gives excessEnergy ≤ N²/(2(p-2)) for large N.
    Contradiction for N ≥ 1. -/
theorem sve_contradicts_avoidance (hp3 : 3 ≤ p)
    (hq : IsPrime p) (hne : ∀ k, seq k ≠ p)
    (hsve : ∀ (ε : ℝ), 0 < ε →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        excessEnergy (fun (n : Fin N) => emWalkUnit p hq hne n.val) ≤ ε * (N : ℝ) ^ 2) :
    ∀ (a : (ZMod p)ˣ), ∃ N₀ : ℕ, ∀ N ≥ N₀,
      0 < walkVisitCount (fun (n : Fin N) => emWalkUnit p hq hne n.val) a := by
  intro a
  -- Choose ε = 1/(2*(p-2))
  have hp2_pos : (0 : ℝ) < (p : ℝ) - 2 := by
    linarith [show (3 : ℝ) ≤ (p : ℝ) from by exact_mod_cast hp3]
  set ε := 1 / (2 * ((p : ℝ) - 2))
  have hε_pos : 0 < ε := by positivity
  obtain ⟨N₀, hN₀⟩ := hsve ε hε_pos
  -- Take N₀' = max N₀ 1 to ensure N ≥ 1
  use max N₀ 1
  intro N hN
  -- Suppose V(a) = 0 for contradiction
  by_contra h; push Not at h
  have hV0 : walkVisitCount (fun n : Fin N => emWalkUnit p hq hne n.val) a = 0 := by
    omega
  -- Confined excess energy: excessEnergy ≥ N²/(p-2)
  have hconf := confined_excess_energy_lb _ a hp3 hV0
  -- SVE: excessEnergy ≤ ε·N²
  have hN₀_le : N₀ ≤ N := le_of_max_le_left hN
  have hsve_bound := hN₀ N hN₀_le
  -- Combine: N²/(p-2) ≤ ε·N² = N²/(2*(p-2))
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (le_of_max_le_right hN)
  have hN_sq_pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  -- N²/(p-2) ≤ excessEnergy ≤ ε·N²
  have h1 : (N : ℝ) ^ 2 / ((p : ℝ) - 2) ≤ ε * (N : ℝ) ^ 2 := le_trans hconf hsve_bound
  -- ε = 1/(2*(p-2)), so ε·N² = N²/(2*(p-2))
  -- But N²/(p-2) ≤ N²/(2*(p-2)) implies 1/(p-2) ≤ 1/(2*(p-2)), i.e., 2 ≤ 1. False.
  -- From h1: N²/(p-2) ≤ ε·N², dividing by N² > 0 gives 1/(p-2) ≤ ε.
  -- But ε = 1/(2*(p-2)) < 1/(p-2). Contradiction.
  have h3 : 1 / ((p : ℝ) - 2) ≤ ε := by
    -- h1 : N²/(p-2) ≤ ε * N²
    -- Since N² > 0: 1/(p-2) ≤ ε
    have h1' : (N : ℝ) ^ 2 / ((p : ℝ) - 2) / (N : ℝ) ^ 2 ≤
        ε * (N : ℝ) ^ 2 / (N : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right h1 (le_of_lt hN_sq_pos)
    rw [mul_div_cancel_right₀ ε (ne_of_gt hN_sq_pos)] at h1'
    rwa [div_div, mul_comm, ← div_div, div_self (ne_of_gt hN_sq_pos)] at h1'
  -- ε < 1/(p-2)
  have h4 : ε < 1 / ((p : ℝ) - 2) := by
    show 1 / (2 * ((p : ℝ) - 2)) < 1 / ((p : ℝ) - 2)
    exact div_lt_div_of_pos_left one_pos hp2_pos (by linarith)
  linarith

end SVEContradictsAvoidance

/-! ## S95. Avoidance Tube Obstruction to SVE

The avoidance tube gives a quantitative obstruction: for a walk that
avoids some unit at all times, the nontrivial character sum energy is
bounded BELOW by N²/(p-2), which contradicts SVE. This means SVE implies
every unit is eventually visited — a structural consequence that is strictly
weaker than equidistribution but still nontrivial. -/

section AvoidanceObstruction

open Classical

/-- Perpetual avoidance of a unit is an OPEN hypothesis for the EM walk
    at a missing prime. When the walk never hits -1 (meaning q never divides
    prod(n)+1), this gives V(-1) = 0 and triggers the confined energy bound.

    NOTE: A missing prime q can still have walkZ q n = -1 (meaning q | prod(n)+1)
    without entering the sequence (if seq(n+1) = minFac(prod(n)+1) < q).
    So PerpetualAvoidance is NOT automatic from q being missing.
    It is an additional structural hypothesis. -/
def PerpetualAvoidance (q : Nat) : Prop :=
  Nat.Prime q ∧ (∀ k, seq k ≠ q) ∧ (∀ n, walkZ q n ≠ -1)

/-- Under perpetual avoidance, the EM walk never visits -1. -/
theorem perpetual_avoidance_visit_zero {q : Nat} [hp : Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (havoid : ∀ n, walkZ q n ≠ -1) (N : Nat) :
    walkVisitCount (fun (n : Fin N) => emWalkUnit q hq hne n.val)
      (Units.mk0 (-1) (neg_ne_zero.mpr (by
        haveI : NeZero q := ⟨hp.out.ne_zero⟩; exact one_ne_zero))) = 0 := by
  simp only [walkVisitCount]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro n _
  simp only [emWalkUnit]
  intro h
  have h_val := congr_arg Units.val h
  simp only [Units.val_mk0] at h_val
  exact havoid n.val h_val

/-- Perpetual avoidance triggers the rogue character: there exists a nontrivial
    character with ‖S_χ(N)‖² ≥ N²/(q-2)². -/
theorem perpetual_avoidance_rogue {q : Nat} [hp : Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hq3 : 3 ≤ q) (havoid : ∀ n, walkZ q n ≠ -1)
    (N : Nat) (hN : 0 < N) :
    ∃ χ : DirichletCharacter ℂ q, χ ≠ 1 ∧
      (N : ℝ) ^ 2 / ((q : ℝ) - 2) ^ 2 ≤
      ‖∑ n : Fin N, χ (↑(emWalkUnit q hq hne n.val) : ZMod q)‖ ^ 2 := by
  exact rogue_character_exists _ _ hq3 hN
    (perpetual_avoidance_visit_zero hq hne havoid N)

end AvoidanceObstruction

/-! ## S96. Landscape -/

section Landscape

open Classical DirichletCharacter

/-- Profinite avoidance tube landscape:
    (1) tubeRatio F ≤ 1 for any F ⊆ {primes ≥ 3}
    (2) ¬WM ⇒ tubeRatio → 0 (tube collapses)
    (3) Confined energy: N²/(q-2) ≤ (q-1)·∑V² (from per_prime_confined_energy_lb)
    (4) Excess energy: 0 ≤ excessEnergy w for any walk
    (5) Confined avoidance: V(a)=0 ⇒ excessEnergy ≥ N²/(p-2) (abstract) -/
theorem avoidance_tube_landscape :
    -- (1) Tube ratio bounded
    (∀ F : Finset Nat, (∀ q ∈ F, 3 ≤ q) → tubeRatio F ≤ 1) ∧
    -- (2) Tube collapse
    (¬ WeakMullin → ∀ ε : ℝ, 0 < ε → ∃ F : Finset Nat,
      (↑F : Set Nat) ⊆ MissingPrimes ∧ tubeRatio F < ε) ∧
    -- (3) Confined energy bound (from per_prime_confined_energy_lb)
    (∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
      (_hq3 : 3 ≤ q) (N : Nat),
      (N : ℝ) ^ 2 / ((q : ℝ) - 2) ≤
      ((q : ℝ) - 1) * ∑ a : (ZMod q)ˣ,
        (walkVisitCount (fun (n : Fin N) => emWalkUnit q hq hne n.val) a : ℝ) ^ 2) ∧
    -- (4) Excess energy nonneg
    (∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
      (N : Nat),
      0 ≤ excessEnergy (fun (n : Fin N) => emWalkUnit q hq hne n.val)) ∧
    -- (5) Avoidance ⇒ confined excess energy
    (∀ (p : ℕ) [Fact (Nat.Prime p)] (_hp3 : 3 ≤ p) (N : ℕ)
      (w : Fin N → (ZMod p)ˣ) (a : (ZMod p)ˣ),
      walkVisitCount w a = 0 →
      (N : ℝ) ^ 2 / ((p : ℝ) - 2) ≤ excessEnergy w) := by
  exact ⟨fun F hF => tubeRatio_le_one hF, tube_collapse,
    fun q inst hq hne _hq3 N => per_prime_confined_energy_lb hq hne _hq3 N,
    fun q inst hq hne N => excessEnergy_nonneg _,
    fun p inst _hp3 N w a h => confined_excess_energy_lb w a _hp3 h⟩

end Landscape
