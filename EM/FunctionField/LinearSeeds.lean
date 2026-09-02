import EM.FunctionField.QuadraticSeeds
import EM.FunctionField.FrobeniusOrbit

/-!
# Linear seeds over `𝔽_5`: all five are perpetual towers

`StableTower.lean` treats the seed `X`; `QuadraticSeeds.lean` the seeds `X² + 1`, `X² + 2`.
Here: for **every** `a ∈ 𝔽_5` the seed `X + a` is a perpetual tower — every `g_n(X + a)` is
irreducible (`g_comp_linear_irreducible`), every valid factor selection from `X + a` follows the
tower and never selects a linear irreducible (`lin_seed_perpetual`, `lin_seed_sel_natDegree`).

The proof is one line on top of the tower: `α_n − a` is a root of `g_n(X + a)`, and subtracting
a constant does not change the Frobenius period (`minimalPeriod_sub_const`), so the period is
`2^n = deg g_n(X + a)` and the Frobenius-orbit criterion applies.  (Mathematically this is the
affine equivariance `X ↦ X + a` of the greedy dynamics; here it is proved directly.)

Together with `QuadraticSeeds.lean`: over `𝔽_5` all five linear seeds and ten of the
twenty-five monic quadratic seeds are perpetual towers, on which the function-field Mullin
conjecture fails.
-/

namespace FunctionFieldAnalog

namespace LinearSeeds

open Polynomial StableTower

/-! ## 1. Subtracting a constant preserves the Frobenius period -/

theorem iterate_sub_const (i : ℕ) (β : L) (a : ZMod 5) :
    (⇑φ)^[i] (β - algebraMap (ZMod 5) L a) = (⇑φ)^[i] β - algebraMap (ZMod 5) L a := by
  rw [φ_iterate, φ_iterate, sub_pow_char_pow, ← map_pow, ZMod.pow_card_pow]

theorem isPeriodicPt_sub_const_iff (i : ℕ) (β : L) (a : ZMod 5) :
    Function.IsPeriodicPt (⇑φ) i (β - algebraMap (ZMod 5) L a) ↔
      Function.IsPeriodicPt (⇑φ) i β := by
  simp only [Function.IsPeriodicPt, Function.IsFixedPt, iterate_sub_const, sub_left_inj]

theorem minimalPeriod_sub_const (β : L) (a : ZMod 5) :
    Function.minimalPeriod (⇑φ) (β - algebraMap (ZMod 5) L a) = Function.minimalPeriod (⇑φ) β := by
  apply Nat.dvd_antisymm
  · exact Function.IsPeriodicPt.minimalPeriod_dvd
      ((isPeriodicPt_sub_const_iff _ _ _).mpr (Function.isPeriodicPt_minimalPeriod _ _))
  · exact Function.IsPeriodicPt.minimalPeriod_dvd
      ((isPeriodicPt_sub_const_iff _ _ _).mp (Function.isPeriodicPt_minimalPeriod _ _))

/-! ## 2. `g_n(X + a)` is irreducible -/

/-- The linear seed `X + a`. -/
noncomputable abbrev linSeed (a : ZMod 5) : (ZMod 5)[X] := X + C a

theorem linSeed_monic (a : ZMod 5) : (linSeed a).Monic := monic_X_add_C a

theorem linSeed_natDegree (a : ZMod 5) : (linSeed a).natDegree = 1 := natDegree_X_add_C a

theorem g_comp_lin_monic (a : ZMod 5) (n : ℕ) : ((g n).comp (linSeed a)).Monic :=
  (g_monic n).comp_X_add_C a

theorem g_comp_lin_natDegree (a : ZMod 5) (n : ℕ) : ((g n).comp (linSeed a)).natDegree = 2 ^ n := by
  rw [natDegree_comp, g_natDegree, linSeed_natDegree, mul_one]

/-- **Every `g_n(X + a)` is irreducible over `𝔽_5`.** -/
theorem g_comp_linear_irreducible (a : ZMod 5) (n : ℕ) : Irreducible ((g n).comp (linSeed a)) := by
  rcases n with _ | n
  · have : (g 0).comp (linSeed a) = X - C (-(a + 1)) := by
      simp [g, iter, add_comp, X_comp, one_comp, sub_eq_add_neg, map_add]; ring
    rw [this]; exact irreducible_X_sub_C _
  · set β : L := alpha (n + 1) - algebraMap (ZMod 5) L a with hβ
    have hroot : aeval β ((g (n + 1)).comp (linSeed a)) = 0 := by
      rw [aeval_comp]
      have : aeval β (linSeed a) = alpha (n + 1) := by simp [linSeed, hβ]
      rw [this]; exact aeval_alpha_g (n + 1)
    apply FrobeniusOrbit.irreducible_of_natDegree_eq_minimalPeriod 5 (g_comp_lin_monic a (n + 1)) hroot
    show ((g (n + 1)).comp (linSeed a)).natDegree = Function.minimalPeriod (⇑φ) β
    rw [g_comp_lin_natDegree, hβ, minimalPeriod_sub_const, minimalPeriod_alpha]

/-! ## 3. The seeded greedy sequence follows the tower -/

theorem iter_comp_add_one (a : ZMod 5) (n : ℕ) :
    (iter n).comp (linSeed a) + 1 = (g n).comp (linSeed a) := by
  simp [g, add_comp, one_comp]

/-- **Perpetual irreducibility from every linear seed over `𝔽_5`.** -/
theorem lin_seed_perpetual (a : ZMod 5) (σ : FFMixedSelection 5)
    (hσ : FFMixedSelectionValid 5 (linSeed a) σ) (n : ℕ) :
    ffMixedWalkProd 5 (linSeed a) σ n = (iter n).comp (linSeed a) ∧
      Irreducible (ffMixedWalkProd 5 (linSeed a) σ n + 1) := by
  induction n with
  | zero =>
    refine ⟨by simp [ffMixedWalkProd, iter], ?_⟩
    have h := g_comp_linear_irreducible a 0
    rwa [← iter_comp_add_one, iter_zero, X_comp] at h
  | succ n ih =>
    obtain ⟨hacc, hirr⟩ := ih
    obtain ⟨hm, hi, hd⟩ := hσ.2.2 n
    have hEm : (ffMixedWalkProd 5 (linSeed a) σ n + 1).Monic := by
      rw [hacc, iter_comp_add_one]; exact g_comp_lin_monic a n
    have hsel : σ.sel n = ffMixedWalkProd 5 (linSeed a) σ n + 1 :=
      eq_of_monic_of_associated hm hEm (hi.associated_of_dvd hirr hd)
    have hacc' : ffMixedWalkProd 5 (linSeed a) σ (n + 1) = (iter (n + 1)).comp (linSeed a) := by
      rw [ffMixedWalkProd, hsel, hacc, iter_succ, mul_comp, add_comp, one_comp]
    refine ⟨hacc', ?_⟩
    rw [hacc', iter_comp_add_one]
    exact g_comp_linear_irreducible a (n + 1)

theorem lin_seed_sel_natDegree (a : ZMod 5) (σ : FFMixedSelection 5)
    (hσ : FFMixedSelectionValid 5 (linSeed a) σ) (n : ℕ) : (σ.sel n).natDegree = 2 ^ n := by
  obtain ⟨hacc, hirr⟩ := lin_seed_perpetual a σ hσ n
  obtain ⟨hm, hi, hd⟩ := hσ.2.2 n
  have hEm : (ffMixedWalkProd 5 (linSeed a) σ n + 1).Monic := by
    rw [hacc, iter_comp_add_one]; exact g_comp_lin_monic a n
  rw [eq_of_monic_of_associated hm hEm (hi.associated_of_dvd hirr hd), hacc, iter_comp_add_one,
    g_comp_lin_natDegree]

end LinearSeeds

end FunctionFieldAnalog
