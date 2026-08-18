import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.GroupTheory.OrderOfElement

/-!
# Character values on finite groups have norm 1 (Mathlib-only)

For a finite group `G` and a homomorphism `χ : G →* ℂˣ`, every value `χ g` is a root of unity,
hence has complex norm `1`.  This is the single home for the fact; it used to be proved
independently in several places (`char_norm_one`, `char_value_norm_one`,
`deterministic_walk_norm_one`, `walkTelescope_char_norm_one`).
-/

/-- Character values on a finite group have norm 1: for `χ : G →* ℂˣ` with `G` finite,
`χ g` is a root of unity, so `‖χ g‖ = 1`. -/
theorem char_norm_one_of_hom {G : Type*} [Group G] [Finite G] (χ : G →* ℂˣ) (g : G) :
    ‖(χ g : ℂ)‖ = 1 := by
  have hfin : IsOfFinOrder (χ g) := χ.isOfFinOrder (isOfFinOrder_of_finite g)
  obtain ⟨n, hn, hpow⟩ := hfin.exists_pow_eq_one
  have hpow' : (χ g : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one hpow' hn.ne'
