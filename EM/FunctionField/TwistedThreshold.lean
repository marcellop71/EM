import EM.FunctionField.AutonomousThreshold
import EM.FunctionField.FibreRule

/-!
# The twisted threshold over `𝔽_2`: what one cofactor does

`AutonomousThreshold.lean` treats runs of irreducible stages: after `k` of them every
irreducible factor `f` of the next Euclid polynomial has `k < 2^{v₂(deg f)}`. That is the
case "cofactor `= 1`" of the statement proved here.

Let stages `n, …, n+k-1` be irreducible and let stage `n+k` be arbitrary, with
`P_{n+k} + 1 = π·c` (`c` the cofactor, possibly `1`). By
`FibreRule.cofactor_mul_euclid_succ`, a root `β` of the next Euclid polynomial satisfies
`(F + 1)^{k+1} (P_n(β)) = c(β)`, where `F` is Frobenius on `𝔽̄_2`. Hence `c(β)` lies in the
image of `(F + 1)^{k+1}` on `𝔽_{2^d}`, `d = deg f`.

## Main results

* `relTr u m w` — the relative trace `∑_{i<m} w^{2^{2^u·i}}` from `𝔽_{2^{2^u·m}}` to
  `𝔽_{2^{2^u}}`.
* `relTr_eq_zero_of_sylv_iterate` — if `(F+1)^k x = w`, `x ∈ 𝔽_{2^{2^u·m}}` and `2^u ≤ k`,
  then `relTr u m w = 0`.
* `relTr_cofactor_eq_zero` — **twisted threshold**: with the notation above, if
  `deg f = 2^u·m` and `2^u ≤ k + 1`, then `relTr u m (c(β)) = 0`.
* `trace_cofactor_eq_zero` — the case `u = 0`, valid at every stage: the absolute trace of
  `c(β)` vanishes. Equivalently every prime factor of `P_{n+1} + 1` splits in the
  Artin–Schreier extension `y² + y = c_n` of `𝔽_2(X)`.
* `mem_image_sylv_iterate_iff` — for `m` odd and `2^u ≤ k`, the image of `(F+1)^k` on
  `𝔽_{2^{2^u·m}}` is exactly the kernel of `relTr u m`.
* `relTr_one`, `even_of_relTr_one_eq_zero` — for `c = 1` the relative trace is `m`, so the
  condition reads "`m` even": the autonomous threshold.

## Reading

A run of irreducible stages forbids degrees (`2^{v+1} ∣ deg f`). One cofactor removes the
prohibition and replaces it by trace conditions on the cofactor's value: one bit for odd
degrees, and `2^u` bits for the degrees divisible by `2^u ≤ k + 1`. The degree condition is
the special case in which the cofactor is the constant `1`, whose relative trace is the
degree ratio `m`.

The condition is sharp at the level of the field: for `2^u` the exact power of `2` in `d`
and `k ≥ 2^u`, the image of `(F + 1)^k` on `𝔽_{2^d}` is exactly the kernel of the relative
trace (`mem_image_sylv_iterate_iff`). It is a necessary condition on the sequence, not a
sufficient one: `c(β)` in the image says that some `x` works, not that `P_n(β)` does.
-/

namespace FunctionFieldAnalog

namespace TwistedThreshold

open Polynomial FrobeniusOrbit CompositeFloors FunctionFieldAnalog.CharTwo AutonomousThreshold

/-- The relative trace from `𝔽_{2^{2^u·m}}` to `𝔽_{2^{2^u}}`, as a map on `𝔽̄_2`. -/
noncomputable def relTr (u m : ℕ) (w : Lp 2) : Lp 2 :=
  ∑ i ∈ Finset.range m, w ^ 2 ^ (2 ^ u * i)

/-- If `z^{2^{2^u}} + z = w` and `z ∈ 𝔽_{2^{2^u·m}}`, the relative trace of `w` vanishes. -/
theorem relTr_eq_zero_of_sylv {u m : ℕ} {z w : Lp 2} (hz : sylv^[2 ^ u] z = w)
    (hfix : z ^ 2 ^ (2 ^ u * m) = z) : relTr u m w = 0 := by
  rw [sylv_iterate_two_pow] at hz
  have hterm : ∀ i, w ^ 2 ^ (2 ^ u * i) =
      z ^ 2 ^ (2 ^ u * (i + 1)) - z ^ 2 ^ (2 ^ u * i) := by
    intro i
    have he : 2 ^ 2 ^ u * 2 ^ (2 ^ u * i) = 2 ^ (2 ^ u * (i + 1)) := by
      rw [← pow_add]
      congr 1
      ring
    rw [← hz, add_pow_char_pow, ← pow_mul, he, CharTwo.sub_eq_add]
  unfold relTr
  rw [Finset.sum_congr rfl (fun i _ => hterm i),
    Finset.sum_range_sub (fun i => z ^ 2 ^ (2 ^ u * i)), hfix]
  simp

/-- **Image of `(F + 1)^k`, necessity.** If `(F+1)^k x = w` with `x ∈ 𝔽_{2^{2^u·m}}` and
    `2^u ≤ k`, then the relative trace of `w` to `𝔽_{2^{2^u}}` vanishes. -/
theorem relTr_eq_zero_of_sylv_iterate {u m k : ℕ} (hk : 2 ^ u ≤ k) {x w : Lp 2}
    (hx : x ^ 2 ^ (2 ^ u * m) = x) (h : sylv^[k] x = w) : relTr u m w = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Function.iterate_add_apply] at h
  apply relTr_eq_zero_of_sylv h
  have := φ_iterate_sylv_iterate (2 ^ u * m) j x
  rw [φ_iterate, φ_iterate, hx] at this
  exact this

/-- The relative trace of `1` is the degree ratio `m`. -/
theorem relTr_one (u m : ℕ) : relTr u m 1 = (m : Lp 2) := by
  simp [relTr]

/-- For the constant `1` the trace condition says that `m` is even. -/
theorem even_of_relTr_one_eq_zero {u m : ℕ} (h : relTr u m 1 = 0) : Even m := by
  rw [relTr_one] at h
  have := (CharP.cast_eq_zero_iff (Lp 2) 2 m).mp h
  exact even_iff_two_dvd.mpr this

/-! ## Sufficiency: the image of `(F + 1)^k` is exactly the trace-zero part -/

theorem relTr_sub (u m : ℕ) (a b : Lp 2) : relTr u m (a - b) = relTr u m a - relTr u m b := by
  simp only [relTr, sub_pow_char_pow, Finset.sum_sub_distrib]

/-- The relative trace commutes with `F + 1`. -/
theorem relTr_sylv (u m : ℕ) (w : Lp 2) : relTr u m (sylv w) = sylv (relTr u m w) := by
  simp only [relTr, sylv, add_pow_char_pow, Finset.sum_add_distrib]
  congr 1
  rw [sum_pow_char]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_mul, ← pow_mul, mul_comm]

/-- **Image of `(F + 1)^k`, sufficiency.** For odd `m`, every `w ∈ 𝔽_{2^{2^u·m}}` of relative
    trace zero is `(F + 1)^k x` for some `x` in the same field, for every `k`: on the
    trace-zero part `F + 1` is injective (its kernel `{0, 1}` meets it in `0`, since the
    relative trace of `1` is `m`), hence bijective. -/
theorem exists_sylv_iterate_eq_of_relTr_eq_zero {u m : ℕ} (hm : Odd m) (k : ℕ) {w : Lp 2}
    (hw : w ^ 2 ^ (2 ^ u * m) = w) (htr : relTr u m w = 0) :
    ∃ x : Lp 2, x ^ 2 ^ (2 ^ u * m) = x ∧ sylv^[k] x = w := by
  have hd : 2 ^ u * m ≠ 0 := by
    have := hm.pos
    positivity
  let K : Set (Lp 2) := {y | y ^ 2 ^ (2 ^ u * m) = y ∧ relTr u m y = 0}
  have hfin : K.Finite := by
    have hne : (X ^ 2 ^ (2 ^ u * m) - X : (ZMod 2)[X]) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod 2) (Nat.one_lt_two_pow hd)
    refine (rootSet_finite (X ^ 2 ^ (2 ^ u * m) - X : (ZMod 2)[X]) (Lp 2)).subset ?_
    rintro y ⟨hy, -⟩
    rw [mem_rootSet]
    exact ⟨hne, by rw [map_sub, map_pow, aeval_X, hy, sub_self]⟩
  have hmaps : Set.MapsTo sylv K K := by
    rintro y ⟨hy, hty⟩
    refine ⟨?_, by rw [relTr_sylv, hty]; simp [sylv]⟩
    have : (y ^ 2 + y) ^ 2 ^ (2 ^ u * m) = (y ^ 2 ^ (2 ^ u * m)) ^ 2 + y ^ 2 ^ (2 ^ u * m) := by
      rw [add_pow_char_pow, ← pow_mul, ← pow_mul, mul_comm]
    show (y ^ 2 + y) ^ 2 ^ (2 ^ u * m) = y ^ 2 + y
    rw [this, hy]
  have hinj : Set.InjOn sylv K := by
    rintro a ⟨-, hta⟩ b ⟨-, htb⟩ hab
    have he : (a - b) * (a - b + 1) = 0 := by
      simp only [sylv] at hab
      linear_combination hab + (b ^ 2 - a * b) * two_eq_zero_L
    rcases mul_eq_zero.mp he with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have h1 : a - b = 1 := by linear_combination h - two_eq_zero_L
      have htr1 : relTr u m (1 : Lp 2) = 0 := by rw [← h1, relTr_sub, hta, htb, sub_self]
      exact (Nat.not_even_iff_odd.mpr hm) (even_of_relTr_one_eq_zero htr1)
  have hbij : Set.BijOn sylv K K := (hfin.injOn_iff_bijOn_of_mapsTo hmaps).mp hinj
  obtain ⟨x, hx, hxw⟩ := (hbij.iterate k).surjOn ⟨hw, htr⟩
  exact ⟨x, hx.1, hxw⟩

/-- **The image of `(F + 1)^k` on `𝔽_{2^d}`.** For `d = 2^u·m` with `m` odd and `2^u ≤ k`,
    an element `w` of `𝔽_{2^d}` is `(F + 1)^k x` with `x ∈ 𝔽_{2^d}` iff its relative trace to
    `𝔽_{2^{2^u}}` vanishes. For `w = 1` this is `AutonomousThreshold.one_mem_sylv_iterate_image_iff`
    in the range `k ≥ 2^{v₂(d)}`. -/
theorem mem_image_sylv_iterate_iff {u m k : ℕ} (hm : Odd m) (hk : 2 ^ u ≤ k) {w : Lp 2}
    (hw : w ^ 2 ^ (2 ^ u * m) = w) :
    (∃ x : Lp 2, x ^ 2 ^ (2 ^ u * m) = x ∧ sylv^[k] x = w) ↔ relTr u m w = 0 :=
  ⟨fun ⟨_, hx, h⟩ => relTr_eq_zero_of_sylv_iterate hk hx h,
    exists_sylv_iterate_eq_of_relTr_eq_zero hm k hw⟩

/-- **Twisted threshold.** Let stages `n, …, n+k-1` be irreducible and let
    `P_{n+k} + 1 = π·c`. If the irreducible `f` of degree `2^u·m` with root `β` divides the
    next Euclid polynomial and `2^u ≤ k + 1`, then the relative trace of `c(β)` to
    `𝔽_{2^{2^u}}` vanishes. -/
theorem relTr_cofactor_eq_zero (d : FFEMData 2) (n k : ℕ)
    (h : ∀ j, j < k → Irreducible (d.ffProd (n + j) + 1))
    {c : (ZMod 2)[X]} (hc : d.ffProd (n + k) + 1 = d.ffSeq (n + k + 1) * c)
    {f : (ZMod 2)[X]} (hf : Irreducible f) (hdvd : f ∣ d.ffProd (n + k + 1) + 1)
    {β : Lp 2} (hβ : aeval β f = 0) {u m : ℕ} (hdeg : f.natDegree = 2 ^ u * m)
    (hu : 2 ^ u ≤ k + 1) : relTr u m (aeval β c) = 0 := by
  have hroot : aeval β (d.ffProd (n + k + 1) + 1) = 0 := by
    obtain ⟨g, hg⟩ := hdvd
    rw [hg, map_mul, hβ, zero_mul]
  have hq := FibreRule.aeval_quadratic_of_root 2 d (n + k) hc hroot
  rw [ffProd_add_of_run d n k h, aeval_sylvPoly_iterate] at hq
  have hs : sylv^[k + 1] (aeval β (d.ffProd n)) = aeval β c := by
    rw [Function.iterate_succ_apply', sylv]
    linear_combination hq - (aeval β c) * two_eq_zero_L
  refine relTr_eq_zero_of_sylv_iterate hu ?_ hs
  rw [← hdeg]
  have h2 : (⇑(φ 2))^[f.natDegree] (aeval β (d.ffProd n)) = aeval β (d.ffProd n) := by
    rw [← aeval_iterate, (isPeriodicPt_natDegree 2 hf hβ).eq]
  rwa [φ_iterate] at h2

/-- **Splitting law over `𝔽_2`.** At every stage, if `P_n + 1 = π·c` and the irreducible
    `f` with root `β` divides the next Euclid polynomial, the absolute trace of `c(β)`
    vanishes. -/
theorem trace_cofactor_eq_zero (d : FFEMData 2) (n : ℕ) {c : (ZMod 2)[X]}
    (hc : d.ffProd n + 1 = d.ffSeq (n + 1) * c) {f : (ZMod 2)[X]} (hf : Irreducible f)
    (hdvd : f ∣ d.ffProd (n + 1) + 1) {β : Lp 2} (hβ : aeval β f = 0) :
    ∑ i ∈ Finset.range f.natDegree, aeval β c ^ 2 ^ i = 0 := by
  have := relTr_cofactor_eq_zero d n 0 (fun j hj => absurd hj (Nat.not_lt_zero j)) hc hf hdvd
    hβ (u := 0) (m := f.natDegree) (by simp) (by simp)
  simpa [relTr] using this

end TwistedThreshold

end FunctionFieldAnalog
