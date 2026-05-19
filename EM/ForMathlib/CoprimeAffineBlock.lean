import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Coprimality counts along an affine progression (Mathlib-only)

Mathlib's `Nat.filter_coprime_Ico_eq_totient` counts `t ∈ [k, k+N)` coprime to `N`.  Sieving an
arithmetic progression needs the same count for `a·t + b` with `Coprime a N`:

  `#{t ∈ [k, k+N) : Coprime N (a t + b)} = φ N`,   `#{t ∈ [k, k+B·N) : …} = B · φ N`.

Proof: periodicity plus `t ↦ (a t + b) mod N` being a bijection of `range N`.  Extracted
2026-08-18 from `EM/Population/BagConditionedLaw.lean` (candidate for upstreaming; Mathlib-style
name `Nat.card_filter_coprime_Ico_affine`).
-/

open Finset

namespace BagConditionedLaw

/-! ## Part 1: an affine block count -/

theorem coprime_mod_iff (N x : ℕ) : Nat.Coprime N (x % N) ↔ Nat.Coprime N x := by
  unfold Nat.Coprime
  rw [Nat.gcd_comm N (x % N), ← Nat.gcd_rec]

/-- On a block of `N` consecutive integers, exactly `φ N` values `t` have `a·t + b` coprime to
`N`, provided `a` is coprime to `N`. -/
theorem card_coprime_affine_block {N a : ℕ} (hN : 0 < N) (ha : Nat.Coprime a N) (b k : ℕ) :
    ((Ico k (k + N)).filter (fun t => Nat.Coprime N (a * t + b))).card = Nat.totient N := by
  -- periodicity reduces to the block `[0, N)`
  have hper : Function.Periodic (fun t => Nat.Coprime N (a * t + b)) N := by
    intro t
    simp only
    have : a * (t + N) + b = (a * t + b) + a * N := by ring
    rw [this, ← coprime_mod_iff, Nat.add_mul_mod_self_right, coprime_mod_iff]
  rw [Nat.filter_Ico_card_eq_of_periodic k N _ hper, Nat.count_eq_card_filter_range]
  -- the map `t ↦ (a t + b) % N` is a bijection of `range N`
  set f : ℕ → ℕ := fun t => (a * t + b) % N with hf
  have hinj : Set.InjOn f (range N : Set ℕ) := by
    intro t ht t' ht' h
    simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
    have h1 : ((a * t + b : ℕ) : ZMod N) = ((a * t' + b : ℕ) : ZMod N) := by
      rw [ZMod.natCast_eq_natCast_iff']; exact h
    push_cast at h1
    have hu : IsUnit (a : ZMod N) := (ZMod.isUnit_iff_coprime a N).mpr ha
    have h2 : (a : ZMod N) * t = (a : ZMod N) * t' := by linear_combination h1
    have h3 : (t : ZMod N) = (t' : ZMod N) := hu.mul_left_cancel h2
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at h3
    exact h3
  have himg : (range N).image f = range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hc
      exact Finset.mem_range.mpr (Nat.mod_lt _ hN)
    · rw [Finset.card_image_of_injOn hinj]
  -- coprimality is preserved by `f`
  have hcop : ∀ t, Nat.Coprime N (f t) ↔ Nat.Coprime N (a * t + b) := fun t => coprime_mod_iff N _
  have hL : ((range N).filter (fun t => Nat.Coprime N (a * t + b))).card
      = (((range N).image f).filter (fun c => Nat.Coprime N c)).card := by
    rw [Finset.filter_image, Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _))]
    congr 1; ext t
    simp only [Finset.mem_filter]
    exact and_congr Iff.rfl (hcop t).symm
  rw [hL, himg, Nat.totient_eq_card_coprime]

/-- `B` blocks of `N` starting at `k`: exactly `B · φ N` good values. -/
theorem card_coprime_affine_blocks {N a : ℕ} (hN : 0 < N) (ha : Nat.Coprime a N) (b k B : ℕ) :
    ((Ico k (k + B * N)).filter (fun t => Nat.Coprime N (a * t + b))).card = B * Nat.totient N := by
  induction B with
  | zero => simp
  | succ B ih =>
    have hsplit : Ico k (k + (B + 1) * N) = Ico k (k + B * N) ∪ Ico (k + B * N) (k + B * N + N) := by
      rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
      congr 1; ring
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint, ih,
      card_coprime_affine_block hN ha b (k + B * N)]
    · ring
    · exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)


end BagConditionedLaw

namespace Nat

/-- Mathlib-style name for `BagConditionedLaw.card_coprime_affine_block`. -/
theorem card_filter_coprime_Ico_affine {N a : ℕ} (hN : 0 < N) (ha : Nat.Coprime a N) (b k : ℕ) :
    ((Ico k (k + N)).filter (fun t => Nat.Coprime N (a * t + b))).card = Nat.totient N :=
  BagConditionedLaw.card_coprime_affine_block hN ha b k

end Nat
