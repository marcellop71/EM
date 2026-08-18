import EM.Population.LSPlus
import EM.Population.MertensLower

/-!
# Tail estimate for `(LS+)` — first slices

**Scope (honest).**  The goal of Group 7 / **C4** is the additive tail term of
`LSPlus.ls_plus`: under the policy `n² ≤ log Y ≤ n³` one wants

```
#{m ∈ sampleSpace q Y : ¬ (∀ j < n, 2 ≤ p̃(j) ∧ p̃(j) ≤ Y)}  ≤  C·(log n / n)·|sampleSpace q Y|.
```

This file contains only the *first slices* of that estimate; the assembly into
the displayed tail bound is future work.  What is proved here:

* **TL0** (`card_primeFactors_le_log`) — `ω(N) ≤ log₂ N`, the elementary
  divisor-counting utility.
* **TL1** (`old_count_le`, `old_count_le_log`) — the *old-position prime count*:
  at a fixed step `k` of a nondegenerate `q`-free orbit, the primes whose current
  cofactor residue has already been visited are at most `k · log₂ c_k`, hence at
  most `k · k · (log₂ Y + 1)` under the type bound `p̃(j) ≤ Y`.  The mechanism is
  that an old position forces `r ∣ c_k − c_j` for some `j < k`, and `c_k − c_j`
  is a *fixed nonzero* natural number, so it has few prime factors.
* **TL2** (`survival_le_exp`, `survival_le_of_active_lower`) — the *upper*
  direction of the survival product: `S_k(y) ≤ exp(−∑ 1/r)`, the sum running over
  the **active window** primes `z < r ≤ y` (out of the bag, at a new position).
  Together with `MertensLower.window_recip_lower` this is the engine that makes
  the "type failure at step `k`" event rare; the arithmetic of *how large* the
  active window sum is (bag exclusion + TL1 old-prime exclusion) is deliberately
  left for the next slice, and is packaged behind the abstract hypothesis
  `E ≤ active window sum` in `survival_le_of_active_lower`.

Group 7 / **C4 tail estimate**, `findings_ls_verification.md` §2.10 and §4
Group 7; interfaces per `findings.md` "Session 310 — interfaces".  Session 310.
-/

noncomputable section
open Classical

namespace TailEstimate

open SeedCapture SeedTypes LargeStepRoughness

variable {q m r j k n N Y z y : ℕ}

/-! ## TL0 — `ω(N) ≤ log₂ N` -/

/-- **TL0.**  A positive natural number has at most `log₂ N` distinct prime
factors: the radical `∏_{p ∣ N} p` divides `N` and is at least `2^{ω(N)}`.

Group 7 / C4, `findings_ls_verification.md` §2.10; Session 310. -/
theorem card_primeFactors_le_log (N : ℕ) (hN : 1 ≤ N) :
    N.primeFactors.card ≤ Nat.log 2 N := by
  have hprod : 2 ^ N.primeFactors.card ≤ ∏ p ∈ N.primeFactors, p := by
    calc 2 ^ N.primeFactors.card = ∏ _p ∈ N.primeFactors, 2 := by
          rw [Finset.prod_const]
      _ ≤ ∏ p ∈ N.primeFactors, p :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
            (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hdvd : (∏ p ∈ N.primeFactors, p) ∣ N := Nat.prod_primeFactors_dvd N
  have hpow : 2 ^ N.primeFactors.card ≤ N :=
    le_trans hprod (Nat.le_of_dvd (by omega) hdvd)
  exact Nat.le_log_of_pow_le (by norm_num) hpow

/-! ## TL1 — the old-position prime count -/

/-- The cofactor is strictly increasing along a nondegenerate orbit. -/
theorem cofactor_strict_mono (hnd : ∀ i < k, 2 ≤ genSeqAvoid q m i) :
    ∀ j < k, seedCofactorAvoid q m j < seedCofactorAvoid q m k := by
  induction k with
  | zero => intro j hj; omega
  | succ t ih =>
      intro j hj
      have hstep : seedCofactorAvoid q m t < seedCofactorAvoid q m (t + 1) := by
        have h2 : 2 ≤ genSeqAvoid q m t := hnd t (by omega)
        have hpos : 1 ≤ seedCofactorAvoid q m t := seedCofactorAvoid_pos q m t
        have hmul : seedCofactorAvoid q m t * 2
            ≤ seedCofactorAvoid q m t * genSeqAvoid q m t :=
          Nat.mul_le_mul_left _ h2
        rw [seedCofactorAvoid_succ]
        omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact lt_trans (ih (fun i hi => hnd i (by omega)) j h) hstep
      · subst h; exact hstep

/-- The primes `< N` whose current cofactor residue is **old** (already visited
at an exposed earlier step). -/
def oldSet (q m N k : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun r => r.Prime ∧ ¬ isNew q m r k)

theorem mem_oldSet {N : ℕ} (h : r ∈ oldSet q m N k) :
    r < N ∧ r.Prime ∧ ¬ isNew q m r k := by
  rw [oldSet, Finset.mem_filter, Finset.mem_range] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- The *active* old primes, i.e. those also out of the bag, form a subset of
`oldSet` — so the count below applies to them too. -/
theorem activeOld_subset_oldSet (q m N k : ℕ) :
    (Finset.range N).filter
        (fun r => r.Prime ∧ ¬ inBag q m r k ∧ ¬ isNew q m r k) ⊆ oldSet q m N k := by
  intro r hr
  rw [Finset.mem_filter] at hr
  rw [oldSet, Finset.mem_filter]
  exact ⟨hr.1, hr.2.1, hr.2.2.2⟩

/-- **TL1.**  At step `k` of a nondegenerate `q`-free orbit, at most
`k · log₂ c_k` primes sit at an old position.

*Mechanism.*  If the residue of `c_k` modulo `r` was already visited at an
exposed step `j < k`, then `r ∣ c_k − c_j`, and `c_k − c_j` is a **fixed nonzero**
natural number (the cofactor is strictly increasing).  So all the old primes for
a given `j` lie in `(c_k − c_j).primeFactors`, of which there are at most
`log₂(c_k − c_j) ≤ log₂ c_k` by TL0.  Union over the `k` choices of `j`.

Group 7 / C4, `findings_ls_verification.md` §2.10; Session 310. -/
theorem old_count_le (hnd : ∀ i < k, 2 ≤ genSeqAvoid q m i) (N : ℕ) :
    (oldSet q m N k).card ≤ k * Nat.log 2 (seedCofactorAvoid q m k) := by
  have hsub : oldSet q m N k ⊆ (Finset.range k).biUnion
      (fun j => (seedCofactorAvoid q m k - seedCofactorAvoid q m j).primeFactors) := by
    intro r hr
    obtain ⟨-, hrp, hold⟩ := mem_oldSet hr
    have hmem : ((seedCofactorAvoid q m k : ℕ) : ZMod r) ∈ visitedAt q m r k :=
      not_not.mp hold
    obtain ⟨j, hjk, -, heq⟩ := mem_visitedAt hmem
    have hlt : seedCofactorAvoid q m j < seedCofactorAvoid q m k :=
      cofactor_strict_mono hnd j hjk
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjk, ?_⟩
    refine Nat.mem_primeFactors.mpr ⟨hrp, ?_, by omega⟩
    have hcast : ((seedCofactorAvoid q m k - seedCofactorAvoid q m j : ℕ) : ZMod r) = 0 := by
      rw [Nat.cast_sub (le_of_lt hlt), heq, sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).mp hcast
  calc (oldSet q m N k).card
      ≤ ((Finset.range k).biUnion
          (fun j => (seedCofactorAvoid q m k - seedCofactorAvoid q m j).primeFactors)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range k,
          (seedCofactorAvoid q m k - seedCofactorAvoid q m j).primeFactors.card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range k, Nat.log 2 (seedCofactorAvoid q m k) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        have hlt : seedCofactorAvoid q m j < seedCofactorAvoid q m k :=
          cofactor_strict_mono hnd j hjk
        refine le_trans (card_primeFactors_le_log _ (by omega)) ?_
        exact Nat.log_mono_right (by omega)
    _ = k * Nat.log 2 (seedCofactorAvoid q m k) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- `log₂ c_k ≤ k·(log₂ Y + 1)` under the type bound `p̃(j) ≤ Y`. -/
theorem log_cofactor_le (hY : ∀ i < k, genSeqAvoid q m i ≤ Y) :
    Nat.log 2 (seedCofactorAvoid q m k) ≤ k * (Nat.log 2 Y + 1) := by
  have h1 : seedCofactorAvoid q m k ≤ Y ^ k := cofactor_le_pow hY
  have h2 : Y ≤ 2 ^ (Nat.log 2 Y + 1) := le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) Y)
  have h3 : Y ^ k ≤ (2 ^ (Nat.log 2 Y + 1)) ^ k := Nat.pow_le_pow_left h2 k
  have h4 : (2 ^ (Nat.log 2 Y + 1)) ^ k = 2 ^ ((Nat.log 2 Y + 1) * k) := by
    rw [← pow_mul]
  calc Nat.log 2 (seedCofactorAvoid q m k)
      ≤ Nat.log 2 (2 ^ ((Nat.log 2 Y + 1) * k)) := Nat.log_mono_right (by omega)
    _ = (Nat.log 2 Y + 1) * k := Nat.log_pow (by norm_num) _
    _ = k * (Nat.log 2 Y + 1) := by ring

/-- **TL1, explicit form.**  Under the type bound `p̃(j) ≤ Y` at most
`k²·(log₂ Y + 1)` primes are at an old position at step `k`. -/
theorem old_count_le_log (hnd : ∀ i < k, 2 ≤ genSeqAvoid q m i)
    (hY : ∀ i < k, genSeqAvoid q m i ≤ Y) (N : ℕ) :
    (oldSet q m N k).card ≤ k * (k * (Nat.log 2 Y + 1)) :=
  le_trans (old_count_le hnd N) (Nat.mul_le_mul_left k (log_cofactor_le hY))

/-! ## TL2 — the per-seed survival upper bound -/

/-- The **active window** `(z, y]`: primes `r` in the window, distinct from the
avoided prime `q`, out of the bag and at a new position at step `k`. -/
def activeWindow (q m z y k : ℕ) : Finset ℕ :=
  (Finset.Ioc z y).filter
    (fun r => r.Prime ∧ r ≠ q ∧ ¬ inBag q m r k ∧ isNew q m r k)

theorem mem_activeWindow {z y : ℕ} (h : r ∈ activeWindow q m z y k) :
    z < r ∧ r ≤ y ∧ r.Prime ∧ r ≠ q ∧ ¬ inBag q m r k ∧ isNew q m r k := by
  rw [activeWindow, Finset.mem_filter, Finset.mem_Ioc] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem activeWindow_subset_bandUpTo (q m z y k : ℕ) :
    activeWindow q m z y k ⊆ bandUpTo q y := by
  intro r hr
  obtain ⟨-, hry, hrp, hrq, -, -⟩ := mem_activeWindow hr
  rw [bandUpTo, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hrp, hrq⟩

/-- On an active window prime, `1/r ≤ ρ_r(k)`: the box is a nonempty subset of
the `r − 1` units. -/
theorem one_div_le_rho (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ i < k, 2 ≤ genSeqAvoid q m i) {z y : ℕ}
    (hr : r ∈ activeWindow q m z y k) : (1 : ℝ) / r ≤ rho q m r k := by
  obtain ⟨-, -, hrp, hrq, hbag, hnew⟩ := mem_activeWindow hr
  have hrm : ¬ r ∣ m := fun hd => hbag (Or.inl hd)
  have hpos : 0 < boxCard q m r k := boxCard_pos hq hm hrp hrq hrm hbag hnd
  have hle : boxCard q m r k ≤ r := le_trans (boxCard_le hrp) (by omega)
  have hposR : (0 : ℝ) < (boxCard q m r k : ℝ) := by exact_mod_cast hpos
  have hleR : (boxCard q m r k : ℝ) ≤ (r : ℝ) := by exact_mod_cast hle
  rw [rho_of_active ⟨hbag, hnew⟩]
  exact one_div_le_one_div_of_le hposR hleR

/-- **TL2.**  The survival product is at most `exp(−∑ 1/r)`, the sum over the
active window primes `z < r ≤ y`.

*Proof.*  Every factor `1 − ρ_r(k)` of `S_k(y)` lies in `[0,1]`, so the product
over `bandUpTo q y` is at most the sub-product over the active window; on an
active window prime `ρ_r(k) = 1/|box| ≥ 1/r`, so `1 − ρ ≤ 1 − 1/r ≤ exp(−1/r)`.

Group 7 / C4, `findings_ls_verification.md` §2.10; Session 310. -/
theorem survival_le_exp (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ i < k, 2 ≤ genSeqAvoid q m i) (z y : ℕ) :
    survival q m y k
      ≤ Real.exp (-(∑ r ∈ activeWindow q m z y k, (1 : ℝ) / r)) := by
  have hsub := activeWindow_subset_bandUpTo q m z y k
  -- every factor of the survival product lies in `[0,1]`
  have hband : ∀ s ∈ bandUpTo q y, 0 ≤ 1 - rho q m s k ∧ 1 - rho q m s k ≤ 1 := by
    intro s hs
    rw [bandUpTo, Finset.mem_filter] at hs
    have h1 : rho q m s k ≤ 1 := rho_le_one hq hm hs.2.1 hs.2.2 hnd
    exact ⟨by linarith, by linarith [rho_nonneg (q := q) (m := m) (r := s) (k := k)]⟩
  -- drop the non-window factors
  have hsplit : (∏ s ∈ bandUpTo q y \ activeWindow q m z y k, (1 - rho q m s k))
      * (∏ s ∈ activeWindow q m z y k, (1 - rho q m s k))
      = survival q m y k := Finset.prod_sdiff hsub
  have hdrop : (∏ s ∈ bandUpTo q y \ activeWindow q m z y k, (1 - rho q m s k)) ≤ 1 :=
    Finset.prod_le_one
      (fun s hs => (hband s (Finset.mem_sdiff.mp hs).1).1)
      (fun s hs => (hband s (Finset.mem_sdiff.mp hs).1).2)
  have hactive_nonneg : 0 ≤ ∏ s ∈ activeWindow q m z y k, (1 - rho q m s k) :=
    Finset.prod_nonneg (fun s hs => (hband s (hsub hs)).1)
  have hstep1 : survival q m y k ≤ ∏ s ∈ activeWindow q m z y k, (1 - rho q m s k) := by
    rw [← hsplit]
    nlinarith [hactive_nonneg, hdrop]
  -- compare with the exponential
  have hstep2 : (∏ s ∈ activeWindow q m z y k, (1 - rho q m s k))
      ≤ ∏ s ∈ activeWindow q m z y k, Real.exp (-((1 : ℝ) / s)) := by
    refine Finset.prod_le_prod (fun s hs => (hband s (hsub hs)).1) ?_
    intro s hs
    have hrho : (1 : ℝ) / s ≤ rho q m s k := one_div_le_rho hq hm hnd hs
    have hexp : -((1 : ℝ) / s) + 1 ≤ Real.exp (-((1 : ℝ) / s)) :=
      Real.add_one_le_exp _
    linarith
  have hexp_sum : (∏ s ∈ activeWindow q m z y k, Real.exp (-((1 : ℝ) / s)))
      = Real.exp (-(∑ r ∈ activeWindow q m z y k, (1 : ℝ) / r)) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  linarith [hstep1, hstep2, hexp_sum.ge, hexp_sum.le]

/-- **TL2, packaged.**  Any lower bound `E` for the active window reciprocal sum
gives the survival bound `S_k(y) ≤ e^{−E}`.

This is the interface the next slice will use: `MertensLower.window_recip_lower`
supplies `log log y − log log z − 16` for the *full* window, and one subtracts
the bag primes (at most `k + ω(m)` of them) and the old primes (at most
`k²(log₂ Y + 1)` of them, TL1), each contributing at most `1/z`.

Group 7 / C4, `findings_ls_verification.md` §2.10; Session 310. -/
theorem survival_le_of_active_lower (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ i < k, 2 ≤ genSeqAvoid q m i) (z y : ℕ) (E : ℝ)
    (hE : E ≤ ∑ r ∈ activeWindow q m z y k, (1 : ℝ) / r) :
    survival q m y k ≤ Real.exp (-E) :=
  le_trans (survival_le_exp hq hm hnd z y) (Real.exp_le_exp.mpr (by linarith))

/-- The active window is exactly the full window minus the primes that are in the
bag or at an old position — the shape needed to combine
`MertensLower.window_recip_lower` (a lower bound on the full window sum) with the
counting bounds of TL1. -/
theorem activeWindow_eq_filter (q m z y k : ℕ) :
    activeWindow q m z y k
      = ((Finset.Ioc z y).filter Nat.Prime).filter
          (fun r => r ≠ q ∧ ¬ inBag q m r k ∧ isNew q m r k) := by
  rw [activeWindow, Finset.filter_filter]

/-! ## TL3 — the divisor first moment over a period -/

/-- Telescoping: `∑_{z < t ≤ W} 1/t² ≤ 1/z − 1/W`, because `1/t² ≤ 1/(t−1) − 1/t`. -/
theorem sum_inv_sq_Ioc_le_sub (z : ℕ) (hz : 1 ≤ z) :
    ∀ W, z ≤ W → ∑ t ∈ Finset.Ioc z W, (1 : ℝ) / ((t : ℝ) * t) ≤ 1 / z - 1 / W := by
  intro W hzW
  induction W, hzW using Nat.le_induction with
  | base => simp
  | succ W hzW ih =>
      have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast (le_trans hz hzW)
      have hW0 : (0 : ℝ) < (W : ℝ) := by linarith
      have hW10 : (0 : ℝ) < (W : ℝ) + 1 := by linarith
      rw [Finset.sum_Ioc_succ_top (by omega)]
      have hcast : ((W + 1 : ℕ) : ℝ) = (W : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hstep : (1 : ℝ) / (((W : ℝ) + 1) * ((W : ℝ) + 1))
          ≤ 1 / (W : ℝ) - 1 / ((W : ℝ) + 1) := by
        have hkey : (1 : ℝ) / (((W : ℝ) + 1) * ((W : ℝ) + 1))
            ≤ 1 / ((W : ℝ) * ((W : ℝ) + 1)) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
        have hid : (1 : ℝ) / (W : ℝ) - 1 / ((W : ℝ) + 1)
            = 1 / ((W : ℝ) * ((W : ℝ) + 1)) := by
          field_simp
          ring
        linarith [hkey, hid.ge, hid.le]
      linarith [ih]

/-- `∑_{z < t ≤ W} 1/t² ≤ 1/z` for every `W`. -/
theorem sum_inv_sq_Ioc_le (z W : ℕ) (hz : 1 ≤ z) :
    ∑ t ∈ Finset.Ioc z W, (1 : ℝ) / ((t : ℝ) * t) ≤ 1 / z := by
  rcases le_or_gt z W with h | h
  · have hW0 : (0 : ℝ) < (W : ℝ) := by
      have : (1 : ℕ) ≤ W := le_trans hz h
      exact_mod_cast Nat.lt_of_lt_of_le hz h
    have := sum_inv_sq_Ioc_le_sub z hz W h
    have : (0 : ℝ) < 1 / (W : ℝ) := by positivity
    linarith [sum_inv_sq_Ioc_le_sub z hz W h]
  · rw [Finset.Ioc_eq_empty (by omega)]
    have : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
    simp only [Finset.sum_empty]
    positivity

/-- The multiples of `r` in `[1, M]` number at most `M / r`. -/
theorem card_dvd_Ico_le (r M : ℕ) (hr : 0 < r) :
    ((Finset.Ico 1 (M + 1)).filter (fun m => r ∣ m)).card ≤ M / r := by
  have hmain : ((Finset.Ico 1 (M + 1)).filter (fun m => r ∣ m)).card
      ≤ (Finset.Ico 1 (M / r + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun m => m / r) ?_ ?_
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at ha
      obtain ⟨⟨h1, h2⟩, hd⟩ := ha
      have hge : r ≤ a := Nat.le_of_dvd (by omega) hd
      have hone : 1 ≤ a / r := (Nat.one_le_div_iff hr).mpr hge
      have hle : a / r ≤ M / r := Nat.div_le_div_right (by omega)
      simp only [Finset.mem_coe, Finset.mem_Ico]
      omega
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      have ha' : a / r * r = a := Nat.div_mul_cancel ha.2
      have hb' : b / r * r = b := Nat.div_mul_cancel hb.2
      have hab' : a / r = b / r := hab
      rw [← ha', ← hb', hab']
  simpa using hmain

/-- **TL3 — the divisor first moment.**  Over one period `m ∈ [1, M]`, the mean
of `∑_{z < r ≤ W, r prime, r ∣ m} 1/r` is at most `1/z`:

```
∑_{m=1}^{M}  ∑_{z < r ≤ W, r ∣ m}  1/r   ≤   M/z.
```

*Proof.*  Swap the sums: `r` contributes `(1/r)·#{m ≤ M : r ∣ m} ≤ M/r²`, and
`∑_{r > z} 1/r² ≤ ∑_{t > z} 1/t² ≤ 1/z` by telescoping.

Group 7 / C4, `findings_ls_verification.md` §2.10; Session 310. -/
theorem seed_divisor_first_moment (z W M : ℕ) (hz : 1 ≤ z) :
    ∑ m ∈ Finset.Ico 1 (M + 1),
        (∑ r ∈ ((Finset.Ioc z W).filter Nat.Prime).filter (fun r => r ∣ m), (1 : ℝ) / r)
      ≤ (M : ℝ) / z := by
  have hrw : ∀ m : ℕ,
      (∑ r ∈ ((Finset.Ioc z W).filter Nat.Prime).filter (fun r => r ∣ m), (1 : ℝ) / r)
        = ∑ r ∈ (Finset.Ioc z W).filter Nat.Prime, if r ∣ m then (1 : ℝ) / r else 0 :=
    fun m => Finset.sum_filter _ _
  simp_rw [hrw]
  rw [Finset.sum_comm]
  have key : ∀ r ∈ (Finset.Ioc z W).filter Nat.Prime,
      (∑ m ∈ Finset.Ico 1 (M + 1), if r ∣ m then (1 : ℝ) / r else 0)
        ≤ (M : ℝ) * ((1 : ℝ) / ((r : ℝ) * r)) := by
    intro r hr
    have hrp : r.Prime := (Finset.mem_filter.mp hr).2
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrp.pos
    have hcard : (((Finset.Ico 1 (M + 1)).filter (fun m => r ∣ m)).card : ℝ) ≤ (M : ℝ) / r := by
      refine le_trans ?_ (Nat.cast_div_le)
      exact_mod_cast card_dvd_Ico_le r M hrp.pos
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hstep : (((Finset.Ico 1 (M + 1)).filter (fun m => r ∣ m)).card : ℝ) * ((1 : ℝ) / r)
        ≤ ((M : ℝ) / r) * ((1 : ℝ) / r) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have hid : ((M : ℝ) / r) * ((1 : ℝ) / r) = (M : ℝ) * ((1 : ℝ) / ((r : ℝ) * r)) := by
      field_simp
    linarith [hstep, hid.ge, hid.le]
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have htail : ∑ r ∈ (Finset.Ioc z W).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) * r)
      ≤ (1 : ℝ) / z := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_) ?_
    · intro t _ _; positivity
    · exact sum_inv_sq_Ioc_le z W hz
  calc ∑ r ∈ (Finset.Ioc z W).filter Nat.Prime,
          ∑ m ∈ Finset.Ico 1 (M + 1), (if r ∣ m then (1 : ℝ) / r else 0)
      ≤ ∑ r ∈ (Finset.Ioc z W).filter Nat.Prime, (M : ℝ) * ((1 : ℝ) / ((r : ℝ) * r)) :=
        Finset.sum_le_sum key
    _ = (M : ℝ) * ∑ r ∈ (Finset.Ioc z W).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) * r) := by
        rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * ((1 : ℝ) / z) := by
        exact mul_le_mul_of_nonneg_left htail hM
    _ = (M : ℝ) / z := by ring

/-- **TL3, Markov form.**  At most `M/(z·δ)` seeds of one period carry a
window-divisor mass exceeding `δ`. -/
theorem markov_divisor_mass (z W M : ℕ) (hz : 1 ≤ z) {δ : ℝ} (hδ : 0 < δ) :
    (((Finset.Ico 1 (M + 1)).filter (fun m =>
        δ ≤ ∑ r ∈ ((Finset.Ioc z W).filter Nat.Prime).filter (fun r => r ∣ m),
              (1 : ℝ) / r)).card : ℝ) ≤ (M : ℝ) / ((z : ℝ) * δ) := by
  set S : ℕ → ℝ := fun m =>
    ∑ r ∈ ((Finset.Ioc z W).filter Nat.Prime).filter (fun r => r ∣ m), (1 : ℝ) / r with hS
  show ((((Finset.Ico 1 (M + 1)).filter (fun m => δ ≤ S m)).card : ℝ))
      ≤ (M : ℝ) / ((z : ℝ) * δ)
  have hnonneg : ∀ m ∈ Finset.Ico 1 (M + 1), 0 ≤ S m := by
    intro m _
    exact Finset.sum_nonneg (fun r _ => by positivity)
  have hbig : ((Finset.Ico 1 (M + 1)).filter (fun m => δ ≤ S m)).card • δ
      ≤ ∑ m ∈ (Finset.Ico 1 (M + 1)).filter (fun m => δ ≤ S m), S m :=
    Finset.card_nsmul_le_sum _ _ _ (fun m hm => (Finset.mem_filter.mp hm).2)
  have hsub : ∑ m ∈ (Finset.Ico 1 (M + 1)).filter (fun m => δ ≤ S m), S m
      ≤ ∑ m ∈ Finset.Ico 1 (M + 1), S m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun m hm _ => hnonneg m hm)
  have htot : ∑ m ∈ Finset.Ico 1 (M + 1), S m ≤ (M : ℝ) / z :=
    seed_divisor_first_moment z W M hz
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  rw [nsmul_eq_mul] at hbig
  have hcd : ((((Finset.Ico 1 (M + 1)).filter (fun m => δ ≤ S m)).card : ℝ)) * δ
      ≤ (M : ℝ) / z := by linarith
  have hMz : (M : ℝ) / (z : ℝ) * (z : ℝ) = (M : ℝ) := by field_simp
  have h2 := mul_le_mul_of_nonneg_right hcd (le_of_lt hzR)
  rw [hMz] at h2
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (z : ℝ) * δ)]
  have hassoc : ((((Finset.Ico 1 (M + 1)).filter (fun m => δ ≤ S m)).card : ℝ)) * ((z : ℝ) * δ)
      = ((((Finset.Ico 1 (M + 1)).filter (fun m => δ ≤ S m)).card : ℝ)) * δ * (z : ℝ) := by
    ring
  linarith [h2, hassoc.ge, hassoc.le]

end TailEstimate

end
