import EM.FunctionField.FirstComposite

/-!
# Critical points along the sequence

The monodromy group of `P_n(x) − y` is controlled by the critical values of `P_n` (the
branch points of the cover). This file records how critical points move at a prime stage and
the arithmetic fact that separates the branch loci of the two halves of a prime stage over
`𝔽_2`.

## Main results

* `derivative_ffProd_succ_of_irreducible` — at a prime stage,
  `P_{n+1}' = (2 P_n + 1) · P_n'` (any `p`): the critical points of `P_{n+1}` are those of
  `P_n` together with the fibre `P_n = −1/2`.
* `derivative_ffProd_add_of_run` — over `𝔽_2`, along a run of prime stages the derivative
  does not change: `P_{n+k}' = P_n'`. The critical points stay, the critical values move by
  `g^k`.
* `pow_ne_add_one_of_odd` — an element of `𝔽_{2^m}`, `m` odd, is not Frobenius-conjugate to
  itself plus `1`.
* `aeval_conj_ne_add_one` — hence for `δ` a root of an irreducible `f` of odd degree and any
  `N ∈ 𝔽_2[X]`, no Frobenius conjugate of `δ` has `N`-value `N(δ) + 1`.

## Reading

At a prime stage `P_{n+1} = g ∘ P_n`, and the two roots of `g(t) = y` are `t` and `t + 1`
(over `𝔽_2`). The cover splits into the two halves `P_n(x) = t` and `P_n(x) = t + 1`, with
branch loci `B` and `B + 1`, `B` the set of critical values of `P_n`. If `B ≠ B + 1` the two
halves are different covers, and when the group of `P_n` is alternating or symmetric this
forces them to be independent (`docs/analysis/fibre_rule_2026-11-15.md` §7). For `P_4` the
critical points are the roots of an irreducible quintic, so `aeval_conj_ne_add_one` gives
`B ∩ (B + 1) = ∅`.
-/

namespace FunctionFieldAnalog

namespace CriticalValues

open Polynomial FrobeniusOrbit CompositeFloors

/-- **Critical points at a prime stage.** `P_{n+1}' = (2 P_n + 1) · P_n'`. -/
theorem derivative_ffProd_succ_of_irreducible {p : ℕ} [Fact (Nat.Prime p)] (d : FFEMData p)
    (n : ℕ) (h : Irreducible (d.ffProd n + 1)) :
    derivative (d.ffProd (n + 1)) = (2 * d.ffProd n + 1) * derivative (d.ffProd n) := by
  rw [ffProd_succ_of_irreducible d n h, derivative_mul, derivative_add, derivative_one]
  ring

/-- Over `𝔽_2` a prime stage does not change the derivative. -/
theorem derivative_ffProd_succ_two (d : FFEMData 2) (n : ℕ)
    (h : Irreducible (d.ffProd n + 1)) :
    derivative (d.ffProd (n + 1)) = derivative (d.ffProd n) := by
  rw [derivative_ffProd_succ_of_irreducible d n h]
  linear_combination (d.ffProd n * derivative (d.ffProd n)) * two_eq_zero_poly

/-- **Over `𝔽_2` the critical points are constant along a run of prime stages.** -/
theorem derivative_ffProd_add_of_run (d : FFEMData 2) (n k : ℕ)
    (h : ∀ j, j < k → Irreducible (d.ffProd (n + j) + 1)) :
    derivative (d.ffProd (n + k)) = derivative (d.ffProd n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, derivative_ffProd_succ_two d (n + k) (h k (Nat.lt_succ_self k)),
      ih (fun j hj => h j (by omega))]

/-- An element of `𝔽_{2^m}` with `m` odd is not Frobenius-conjugate to itself plus one. -/
theorem pow_ne_add_one_of_odd {m : ℕ} (hm : Odd m) {v : Lp 2} (hv : v ^ 2 ^ m = v) (j : ℕ) :
    v ^ 2 ^ j ≠ v + 1 := by
  intro hj
  have hφj : (⇑(φ 2))^[j] v = v + 1 := by rw [φ_iterate]; exact hj
  have hper2 : Function.IsPeriodicPt (⇑(φ 2)) (2 * j) v := by
    show (⇑(φ 2))^[2 * j] v = v
    rw [two_mul, Function.iterate_add_apply, hφj, φ_iterate, add_pow_char_pow, one_pow, hj]
    linear_combination (1 : Lp 2) * FunctionFieldAnalog.CharTwo.two_eq_zero_L
  have hperm : Function.IsPeriodicPt (⇑(φ 2)) m v := by
    show (⇑(φ 2))^[m] v = v
    rw [φ_iterate]; exact hv
  have hcop : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
    (fun h2 => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2))
  have hg := hper2.gcd hperm
  rw [Nat.Coprime.gcd_mul_left_cancel j hcop] at hg
  have hperj : (⇑(φ 2))^[j] v = v := hg.trans_dvd (Nat.gcd_dvd_left j m)
  rw [hφj] at hperj
  exact one_ne_zero (add_eq_left.mp hperj)

/-- **Separation of the two branch loci.** If `δ` is a root of an irreducible `f` of odd
    degree over `𝔽_2`, then for every `N` and every `j` the value of `N` at the conjugate
    `δ^{2^j}` is not `N(δ) + 1`. -/
theorem aeval_conj_ne_add_one {f : (ZMod 2)[X]} (hf : Irreducible f) (hodd : Odd f.natDegree)
    {δ : Lp 2} (hδ : aeval δ f = 0) (N : (ZMod 2)[X]) (j : ℕ) :
    aeval (δ ^ 2 ^ j) N ≠ aeval δ N + 1 := by
  have hv : aeval δ N ^ 2 ^ f.natDegree = aeval δ N := by
    have h2 : (⇑(φ 2))^[f.natDegree] (aeval δ N) = aeval δ N := by
      rw [← aeval_iterate, (isPeriodicPt_natDegree 2 hf hδ).eq]
    rwa [φ_iterate] at h2
  have := pow_ne_add_one_of_odd hodd hv j
  rwa [← φ_iterate, ← aeval_iterate, φ_iterate] at this

end CriticalValues

end FunctionFieldAnalog
