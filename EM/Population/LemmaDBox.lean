import EM.Population.LemmaD
import EM.Population.TailEstimate

/-!
# Lemma D, box side: the class-selection lower bound inside a type cell

This file supplies the **combinatorial half of Lemma D** of the seed-average programme.  The
analytic half (`window_ap_recip_lower`, `window_recip_upper`) lives in
`EM/Population/LemmaD.lean`; here we convert it into the statement actually consumed by
Theorem C:

> inside a type cell, a fixed positive proportion (depending only on `q`) of the seeds that
> make a *large step* at depth `k` make it into a **prescribed** residue class mod `q`.

## The three ingredients

* **§4 — the exact hit count.**  The event "the `k`-th `q`-free multiplier of `m` equals a
  prescribed prime `p`" is, inside the cell, again cut out by local residue conditions:
  survival below `p` at every band prime `< p`, and *death* at `p`.  This gives the exact
  identity (`hitCell_card_mul`)

  ```
  #(cell ∩ {p̃_k = p}) · |box_k(p)|  =  #(cell ∩ {survives up to p-1}).
  ```

  Since `|box_k(p)| ≤ p - 1`, the left factor is at least `#(cell ∩ survives(p-1))/p`.

* **§5 — the window survival ratio.**  Raising the survival cut from `y` to `z` costs at most
  `exp(-4 ∑_{y < r ≤ z} 1/r)` (`survival_window_ge`), because every prime above `y ≥ 2k+2` is
  far-band, so `ρ_r ≤ 2/r` and `ρ_r ≤ 1/2`.  With `window_recip_upper` (constant `32`) and
  `z ≤ y²`, the cost is the absolute constant `c₂ = e^{-128}` (`survival_window_ge_c2`).

* **§6 — assembly.**  Summing the exact hit counts over the *good* primes of the window
  `(y_k, y_k²]` — prime, in the target class, not in the bag, and with a new cofactor position
  — the events are disjoint and each forces both survival at `y_k` and the target class.  The
  outcome is `lemma_D_of_good_mass`.

* **§7 — the good-window mass.**  `window_ap_recip_lower` minus the bad-prime mass of
  `findings.md` (d-2): the primes of the window that are *not* good are divisors of the seed
  (the `(d-2)` exclusion hypothesis), earlier multipliers (at most `k`, each `≥ Cc·k`), or old
  positions (at most `k·log₂ c_k` by `TailEstimate.old_count_le`, each `≥ Cc·k·log₂ c_k`).
  Each family carries mass `≤ 1/Cc`, so `≥ 1/(8φ) − 3/Cc ≥ 1/(16φ)` survives.

* **§8 — Lemma D.**  Specialised to the moving threshold `y_k = Cc·k·log₂ c_k`, with the
  `a`-dependent analytic threshold uniformised over the `q` residue classes by a `Finset.sup`.

The statement `lemma_D` is unconditional apart from its explicit hypotheses (nondegenerate
prefix, `y_k² ≤ Y`, and the `(d-2)` seed-divisor exclusion); the whole file is sorry-free.

References: `agents/state/findings.md`, Session 311 coordinator design note "Lemma D box-side".
-/

noncomputable section
open Classical

namespace LemmaD

open SeedCapture SeedTypes LargeStepRoughness SelectionLaw

/-! ## §4  The hit cell: `{m ∈ cell : p̃_k(m) = p}` -/

/-- **The local sets cutting out `{p̃_n = p}`.**

At the prime `p` itself the residue must be the *death point* `-c_n⁻¹`; at every band prime
`r < p` the residue must avoid the death point (survival below `p`); above `p` nothing is
imposed beyond the cell conditions.  Both the second and the third case are packaged by
`localSurvSet` at the cut `p - 1`. -/
def localHitSet (q p n m₀ r : ℕ) : Finset (ZMod r) :=
  if r = p then
    (localSurvSet q (p - 1) n m₀ r).filter
      (fun x => x * ((seedCofactorAvoid q m₀ n : ℕ) : ZMod r) + 1 = 0)
  else localSurvSet q (p - 1) n m₀ r

/-- **The multiplier is `p` iff nothing below `p` divides and `p` does.**

An elementary restatement of `genSeqAvoid = minFac ∘ qfreePart`: the `q`-free least prime
factor of the Euclid number equals `p` exactly when the number survives every prime `≤ p-1`
other than `q` and is divisible by `p`. -/
theorem genSeqAvoid_eq_iff {q n p m : ℕ} (hq : q.Prime) (hp : p.Prime) (hpq : p ≠ q) :
    genSeqAvoid q m n = p ↔
      (SurvivesUpTo q (p - 1) n m ∧ p ∣ genProdAvoid q m n + 1) := by
  have hNne : genProdAvoid q m n + 1 ≠ 0 := Nat.succ_ne_zero _
  have h2p := hp.two_le
  constructor
  · intro h
    have h2 : 2 ≤ qfreePart q (genProdAvoid q m n + 1) := by
      by_contra hcon
      have hpos := qfreePart_pos (N := genProdAvoid q m n + 1) q hNne
      have he : qfreePart q (genProdAvoid q m n + 1) = 1 := by omega
      rw [genSeqAvoid_def, he, Nat.minFac_one] at h
      omega
    obtain ⟨hpr, hdvd, hne⟩ := minFac_qfreePart_spec hq hNne h2
    rw [genSeqAvoid_def] at h
    rw [h] at hdvd
    refine ⟨?_, hdvd⟩
    intro r hr hry hrq hrdvd
    have hmin := minFac_qfreePart_least hq hNne hr hrq hrdvd
    rw [h] at hmin
    omega
  · rintro ⟨hsurv, hdvdp⟩
    have hpqf : p ∣ qfreePart q (genProdAvoid q m n + 1) :=
      (prime_dvd_qfreePart_iff hq hp hpq hNne).mpr hdvdp
    have h2 : 2 ≤ qfreePart q (genProdAvoid q m n + 1) :=
      le_trans hp.two_le (Nat.le_of_dvd (qfreePart_pos q hNne) hpqf)
    obtain ⟨htp, htd, htq⟩ := minFac_qfreePart_spec hq hNne h2
    have hle : (qfreePart q (genProdAvoid q m n + 1)).minFac ≤ p :=
      Nat.minFac_le_of_dvd hp.two_le hpqf
    rw [genSeqAvoid_def]
    by_contra hne'
    exact hsurv _ htp (by omega) htq htd

/-- **The hit cell is again a local-residue set.** -/
theorem mem_hitCell_iff_local {q Y n m₀ p : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y)
    (hp : p.Prime) (hpq : p ≠ q) (hpY : p ≤ Y) {m : ℕ} (hm : 1 ≤ m) :
    (((∀ j < n, genSeqAvoid q m j = genSeqAvoid q m₀ j) ∧
        (∀ r : ℕ, r.Prime → r ≤ Y → r ≠ q → (r ∣ m ↔ r ∣ m₀))) ∧ genSeqAvoid q m n = p)
      ↔ (∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ localHitSet q p n m₀ r) := by
  have hp1Y : p - 1 ≤ Y := le_trans (by omega) hpY
  have hpband : p ∈ bandUpTo q Y := mem_bandUpTo.mpr ⟨hpY, hp, hpq⟩
  have hiff := mem_survCell_iff_local (y := p - 1) hq hm₀ hnd hp1Y hm
  constructor
  · rintro ⟨hcell, hmult⟩
    have hcof : seedCofactorAvoid q m n = seedCofactorAvoid q m₀ n :=
      Finset.prod_congr rfl fun i hi => hcell.1 i (Finset.mem_range.mp hi)
    rw [genSeqAvoid_eq_iff hq hp hpq] at hmult
    have hL := hiff.mp ⟨hcell, hmult.1⟩
    intro r hr
    rw [localHitSet]
    by_cases hrp : r = p
    · subst hrp
      rw [if_pos rfl]
      refine Finset.mem_filter.mpr ⟨hL r hr, ?_⟩
      have hd := hmult.2
      rw [genProdAvoid_eq_seed_mul_cofactor, hcof] at hd
      have hz : ((m * seedCofactorAvoid q m₀ n + 1 : ℕ) : ZMod r) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hd
      push_cast at hz
      exact hz
    · rw [if_neg hrp]
      exact hL r hr
  · intro hH
    have hL : ∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ localSurvSet q (p - 1) n m₀ r := by
      intro r hr
      have hx := hH r hr
      rw [localHitSet] at hx
      by_cases hrp : r = p
      · rw [if_pos hrp] at hx
        exact (Finset.mem_filter.mp hx).1
      · rwa [if_neg hrp] at hx
    obtain ⟨hcell, hsu⟩ := hiff.mpr hL
    refine ⟨hcell, ?_⟩
    have hcof : seedCofactorAvoid q m n = seedCofactorAvoid q m₀ n :=
      Finset.prod_congr rfl fun i hi => hcell.1 i (Finset.mem_range.mp hi)
    rw [genSeqAvoid_eq_iff hq hp hpq]
    refine ⟨hsu, ?_⟩
    have hPp := hH p hpband
    rw [localHitSet, if_pos rfl] at hPp
    have hF := (Finset.mem_filter.mp hPp).2
    rw [genProdAvoid_eq_seed_mul_cofactor, hcof]
    have hz : ((m * seedCofactorAvoid q m₀ n + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact hF
    exact (ZMod.natCast_eq_zero_iff _ _).mp hz

/-- **The local factor at `p` is a singleton.**  For an active prime `p` whose current
cofactor position is new, the death point `-c_n⁻¹` lies in the box, so exactly one residue
class mod `p` produces the multiplier `p`. -/
theorem localHitSet_card_self {q n m₀ p : ℕ} (hp : p.Prime)
    (hnd2 : ∀ i < n, 2 ≤ genSeqAvoid q m₀ i)
    (hbag : ¬ inBag q m₀ p n) (hnew : isNew q m₀ p n) :
    (localHitSet q p n m₀ p).card = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2p := hp.two_le
  have hc0 : ((seedCofactorAvoid q m₀ n : ℕ) : ZMod p) ≠ 0 :=
    cofactor_ne_zero_of_not_inBag hp hbag hnd2 (le_refl n)
  have hmemb : -((seedCofactorAvoid q m₀ n : ℕ) : ZMod p)⁻¹ ∈ box q m₀ p n := by
    rw [box, Finset.mem_sdiff]
    refine ⟨(mem_unitFinset hp).mpr (by simpa using hc0), ?_⟩
    intro hmem
    obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hmem
    have hvc : v = ((seedCofactorAvoid q m₀ n : ℕ) : ZMod p) := neg_inv_injective hp hveq
    rw [hvc] at hv
    exact hnew hv
  rw [localHitSet, if_pos rfl, localSurvSet, if_neg (by omega : ¬ p ≤ p - 1),
    localSet_of_active hbag]
  have hfe : (box q m₀ p n).filter
        (fun x => x * ((seedCofactorAvoid q m₀ n : ℕ) : ZMod p) + 1 = 0)
      = (box q m₀ p n).filter (fun x => x = -((seedCofactorAvoid q m₀ n : ℕ) : ZMod p)⁻¹) := by
    refine Finset.filter_congr fun x _ => ?_
    rw [add_eq_zero_iff_eq_neg, hit_iff_eq_neg_inv hp hc0]
  rw [hfe, Finset.filter_eq', if_pos hmemb, Finset.card_singleton]

/-- **The exact hit count.**

`#(cell ∩ {p̃_n = p}) · |box_n(p)| = #(cell ∩ {survives up to p-1})`.

Both sides are products of local counts over the band; they differ only at `p`, where the hit
condition selects a single class out of the box. -/
theorem hitCell_card_mul {q Y n m₀ p : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y)
    (hp : p.Prime) (hpq : p ≠ q) (hpY : p ≤ Y)
    (hbag : ¬ inBag q m₀ p n) (hnew : isNew q m₀ p n) :
    ((((stepCell q Y n m₀).filter (fun m => genSeqAvoid q m n = p)).card : ℝ))
        * (boxCard q m₀ p n : ℝ)
      = ((((stepCell q Y n m₀).filter (fun m => SurvivesUpTo q (p - 1) n m)).card : ℝ)) := by
  have hnd2 : ∀ i < n, 2 ≤ genSeqAvoid q m₀ i := fun i hi => (hnd i hi).1
  have hp1Y : p - 1 ≤ Y := le_trans (by omega) hpY
  have hpband : p ∈ bandUpTo q Y := mem_bandUpTo.mpr ⟨hpY, hp, hpq⟩
  -- Both filtered cells are local-residue sets.
  have hhit : (stepCell q Y n m₀).filter (fun m => genSeqAvoid q m n = p)
      = (Finset.Ico 1 (modulus q Y + 1)).filter
        (fun m => ∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ localHitSet q p n m₀ r) := by
    rw [stepCell, Finset.filter_filter]
    refine Finset.filter_congr ?_
    intro m hm
    exact mem_hitCell_iff_local hq hm₀ hnd hp hpq hpY (Finset.mem_Ico.mp hm).1
  have hsurv : (stepCell q Y n m₀).filter (fun m => SurvivesUpTo q (p - 1) n m)
      = (Finset.Ico 1 (modulus q Y + 1)).filter
        (fun m => ∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ localSurvSet q (p - 1) n m₀ r) := by
    rw [stepCell, Finset.filter_filter]
    refine Finset.filter_congr ?_
    intro m hm
    exact mem_survCell_iff_local hq hm₀ hnd hp1Y (Finset.mem_Ico.mp hm).1
  rw [hhit, hsurv, card_local_filter, card_local_filter]
  -- Factor both products at `p`.
  have hoff : ∀ r ∈ (bandUpTo q Y).erase p,
      (localHitSet q p n m₀ r).card = (localSurvSet q (p - 1) n m₀ r).card := by
    intro r hr
    have hrp : r ≠ p := (Finset.mem_erase.mp hr).1
    rw [localHitSet, if_neg hrp]
  have hprodH : ∏ r ∈ bandUpTo q Y, (localHitSet q p n m₀ r).card
      = (localHitSet q p n m₀ p).card
        * ∏ r ∈ (bandUpTo q Y).erase p, (localSurvSet q (p - 1) n m₀ r).card := by
    rw [← Finset.mul_prod_erase _ _ hpband]
    exact congrArg _ (Finset.prod_congr rfl hoff)
  have hprodS : ∏ r ∈ bandUpTo q Y, (localSurvSet q (p - 1) n m₀ r).card
      = (localSurvSet q (p - 1) n m₀ p).card
        * ∏ r ∈ (bandUpTo q Y).erase p, (localSurvSet q (p - 1) n m₀ r).card :=
    (Finset.mul_prod_erase _ _ hpband).symm
  have hSp : (localSurvSet q (p - 1) n m₀ p).card = boxCard q m₀ p n := by
    have h2p := hp.two_le
    rw [localSurvSet, if_neg (by omega : ¬ p ≤ p - 1), localSet_card_of_active hbag]
  rw [hprodH, hprodS, hSp, localHitSet_card_self hp hnd2 hbag hnew]
  push_cast
  ring

/-! ## §5  The window survival ratio -/

/-- **Raising the survival cut costs a window product.**

For `2k+2 ≤ y ≤ z` the extra band primes are all far-band, so `ρ_r ≤ min (2/r) (1/2)` and

```
survival(z) ≥ exp(-4 ∑_{y < r ≤ z, r prime} 1/r) · survival(y).
```
-/
theorem survival_window_ge {q m₀ k : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd2 : ∀ j < k, 2 ≤ genSeqAvoid q m₀ j) (hk : 1 ≤ k)
    {y z : ℕ} (hy : 2 * k + 2 ≤ y) (hyz : y ≤ z) (E : ℝ)
    (hE : ∑ r ∈ (Finset.Ioc y z).filter Nat.Prime, (1 : ℝ) / r ≤ E) :
    Real.exp (-(4 * E)) * survival q m₀ y k ≤ survival q m₀ z k := by
  have hsub : bandUpTo q y ⊆ bandUpTo q z := by
    intro r hr
    obtain ⟨hry, hrp, hrq⟩ := mem_bandUpTo.mp hr
    exact mem_bandUpTo.mpr ⟨le_trans hry hyz, hrp, hrq⟩
  set W : Finset ℕ := (bandUpTo q z) \ (bandUpTo q y) with hW
  have hfar : ∀ r ∈ W, r.Prime ∧ 2 * k + 2 ≤ r ∧ r ≤ z ∧ y < r := by
    intro r hr
    rw [hW, Finset.mem_sdiff] at hr
    obtain ⟨hrz, hrp, hrq⟩ := mem_bandUpTo.mp hr.1
    have hgt : y < r := by
      by_contra hcon
      exact hr.2 (mem_bandUpTo.mpr ⟨by omega, hrp, hrq⟩)
    exact ⟨hrp, by omega, hrz, hgt⟩
  have hWsub : W ⊆ (Finset.Ioc y z).filter Nat.Prime := by
    intro r hr
    obtain ⟨hrp, _, hrz, hgt⟩ := hfar r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hgt, hrz⟩, hrp⟩
  have hmass : ∑ r ∈ W, rho q m₀ r k ≤ 2 * E := by
    calc ∑ r ∈ W, rho q m₀ r k
        ≤ ∑ r ∈ W, 2 * ((1 : ℝ) / r) := by
          refine Finset.sum_le_sum fun r hr => ?_
          obtain ⟨hrp, hrfar, _, _⟩ := hfar r hr
          have h := rho_le_far hrp hnd2 hrfar
          have he : (2 : ℝ) / (r : ℝ) = 2 * ((1 : ℝ) / (r : ℝ)) := by ring
          rw [he] at h
          exact h
      _ ≤ ∑ r ∈ (Finset.Ioc y z).filter Nat.Prime, 2 * ((1 : ℝ) / r) :=
          Finset.sum_le_sum_of_subset_of_nonneg hWsub (fun i _ _ => by positivity)
      _ = 2 * ∑ r ∈ (Finset.Ioc y z).filter Nat.Prime, (1 : ℝ) / r := by rw [Finset.mul_sum]
      _ ≤ 2 * E := by linarith
  have hprod : Real.exp (-(4 * E)) ≤ ∏ r ∈ W, (1 - rho q m₀ r k) := by
    have hstep : ∀ r ∈ W, Real.exp (-(2 * rho q m₀ r k)) ≤ 1 - rho q m₀ r k := by
      intro r hr
      obtain ⟨hrp, hrfar, _, _⟩ := hfar r hr
      exact one_sub_ge_exp rho_nonneg (rho_le_half_of_far hrp hnd2 hk hrfar)
    have hsum : ∑ r ∈ W, (-(2 * rho q m₀ r k)) = -(2 * ∑ r ∈ W, rho q m₀ r k) := by
      simp [Finset.mul_sum]
    calc Real.exp (-(4 * E)) ≤ Real.exp (-(2 * ∑ r ∈ W, rho q m₀ r k)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = ∏ r ∈ W, Real.exp (-(2 * rho q m₀ r k)) := by rw [← hsum, Real.exp_sum]
      _ ≤ ∏ r ∈ W, (1 - rho q m₀ r k) :=
          Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) hstep
  have hsplit : (∏ r ∈ W, (1 - rho q m₀ r k)) * survival q m₀ y k = survival q m₀ z k := by
    rw [survival, survival, hW]
    exact Finset.prod_sdiff hsub
  have h0 : 0 ≤ survival q m₀ y k := survival_nonneg hq hm₀ hnd2 y
  calc Real.exp (-(4 * E)) * survival q m₀ y k
      ≤ (∏ r ∈ W, (1 - rho q m₀ r k)) * survival q m₀ y k := by
        exact mul_le_mul_of_nonneg_right hprod h0
    _ = survival q m₀ z k := hsplit

/-- The absolute window constant `c₂ = e^{-128}`. -/
def c₂ : ℝ := Real.exp (-(128 : ℝ))

theorem c₂_pos : 0 < c₂ := Real.exp_pos _

/-- **The window survival ratio with the absolute constant.**  If the whole prime window
`(y, y²]` carries reciprocal mass at most `32` (which is `window_recip_upper` for `y ≥ 4`),
then raising the cut anywhere inside the window costs at most `c₂ = e^{-128}`. -/
theorem survival_window_ge_c₂ {q m₀ k : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd2 : ∀ j < k, 2 ≤ genSeqAvoid q m₀ j) (hk : 1 ≤ k)
    {y z : ℕ} (hy : 2 * k + 2 ≤ y) (hyz : y ≤ z) (hzy : z ≤ y ^ 2)
    (hwin : ∑ r ∈ (Finset.Ioc y (y ^ 2)).filter Nat.Prime, (1 : ℝ) / r ≤ 32) :
    c₂ * survival q m₀ y k ≤ survival q m₀ z k := by
  have hsub : (Finset.Ioc y z).filter Nat.Prime ⊆ (Finset.Ioc y (y ^ 2)).filter Nat.Prime := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_Ioc] at hr ⊢
    exact ⟨⟨hr.1.1, le_trans hr.1.2 hzy⟩, hr.2⟩
  have hE : ∑ r ∈ (Finset.Ioc y z).filter Nat.Prime, (1 : ℝ) / r ≤ 32 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)) hwin
  have h := survival_window_ge hq hm₀ hnd2 hk hy hyz 32 hE
  have hc : Real.exp (-(4 * (32 : ℝ))) = c₂ := by norm_num [c₂]
  rwa [hc] at h

/-! ## §6  Assembly: the class-selection lower bound -/

/-- **The good window.**  Primes of `(y, y²]` in the target class mod `q`, distinct from `q`,
outside the bag, and at which the current cofactor position is new. -/
def goodWindow (q m₀ k a y : ℕ) : Finset ℕ :=
  (Finset.Ioc y (y ^ 2)).filter
    (fun p => p.Prime ∧ p ≠ q ∧ p % q = a % q ∧ ¬ inBag q m₀ p k ∧ isNew q m₀ p k)

theorem mem_goodWindow {q m₀ k a y p : ℕ} :
    p ∈ goodWindow q m₀ k a y ↔
      (y < p ∧ p ≤ y ^ 2) ∧ p.Prime ∧ p ≠ q ∧ p % q = a % q ∧
        ¬ inBag q m₀ p k ∧ isNew q m₀ p k := by
  rw [goodWindow, Finset.mem_filter, Finset.mem_Ioc]

/-- **Per-prime lower bound.**  For a good window prime `p`, the seeds of the cell whose
`k`-th multiplier is exactly `p` make up at least a `c₂ · survival(y) / p` fraction. -/
theorem hitCell_card_ge {q Y k m₀ a y : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y)
    (hk : 1 ≤ k) (hy : 2 * k + 2 ≤ y) (hyY : y ^ 2 ≤ Y)
    (hwin : ∑ r ∈ (Finset.Ioc y (y ^ 2)).filter Nat.Prime, (1 : ℝ) / r ≤ 32)
    {p : ℕ} (hpg : p ∈ goodWindow q m₀ k a y) :
    c₂ * survival q m₀ y k * ((stepCell q Y k m₀).card : ℝ) * (1 / (p : ℝ))
      ≤ (((stepCell q Y k m₀).filter (fun m => genSeqAvoid q m k = p)).card : ℝ) := by
  obtain ⟨⟨hyp, hpy2⟩, hp, hpq, _, hbag, hnew⟩ := mem_goodWindow.mp hpg
  have hnd2 : ∀ j < k, 2 ≤ genSeqAvoid q m₀ j := fun j hj => (hnd j hj).1
  have hpY : p ≤ Y := le_trans hpy2 hyY
  have hp1Y : p - 1 ≤ Y := le_trans (by omega) hpY
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  -- The exact hit identity.
  have hid := hitCell_card_mul hq hm₀ hnd hp hpq hpY hbag hnew
  -- The survival count at the cut `p - 1`.
  have hsel := selection_law (y := p - 1) hq hm₀ hnd hp1Y
  -- The window survival ratio.
  have hratio : c₂ * survival q m₀ y k ≤ survival q m₀ (p - 1) k :=
    survival_window_ge_c₂ hq hm₀ hnd2 hk hy (by omega) (by omega) hwin
  set H : ℝ := (((stepCell q Y k m₀).filter (fun m => genSeqAvoid q m k = p)).card : ℝ) with hH
  have hH0 : 0 ≤ H := by positivity
  have hcell0 : (0 : ℝ) ≤ ((stepCell q Y k m₀).card : ℝ) := by positivity
  have hbox : (boxCard q m₀ p k : ℝ) ≤ (p : ℝ) := by
    have := boxCard_le (q := q) (m := m₀) (r := p) (k := k) hp
    have : (boxCard q m₀ p k : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast this
    have hle : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
      have : (p - 1 : ℕ) ≤ p := Nat.sub_le _ _
      exact_mod_cast this
    linarith
  -- Chain.
  have hkey : c₂ * survival q m₀ y k * ((stepCell q Y k m₀).card : ℝ) ≤ H * (p : ℝ) := by
    calc c₂ * survival q m₀ y k * ((stepCell q Y k m₀).card : ℝ)
        ≤ survival q m₀ (p - 1) k * ((stepCell q Y k m₀).card : ℝ) := by
          exact mul_le_mul_of_nonneg_right hratio hcell0
      _ = H * (boxCard q m₀ p k : ℝ) := by rw [← hsel, ← hid]
      _ ≤ H * (p : ℝ) := mul_le_mul_of_nonneg_left hbox hH0
  rw [mul_one_div, div_le_iff₀ hppos]
  exact hkey

/-- **Lemma D, box side (conditional on the good-window mass).**

Inside a type cell at depth `k`, at least a `c₂/(16 φ(q))` fraction of the seeds making a
large step land in the prescribed residue class `a` mod `q`.

The hypotheses are:
* `hnd` — the reference prefix is nondegenerate and `≤ Y` (the cell is well defined);
* `hy` — the cut `y` is above the near band `2k+2` (so window primes are far-band);
* `hyY` — the whole window `(y, y²]` is inside the truncation (`A = 2`);
* `hwin` — the crude window mass bound, i.e. `window_recip_upper` at `y ≥ 4`;
* `hmass` — the good-window reciprocal mass is at least `1/(16 φ(q))`, i.e.
  `window_ap_recip_lower` minus the bad-prime mass of `findings.md` (d-2). -/
theorem lemma_D_of_good_mass {q Y k m₀ a y : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y)
    (hk : 1 ≤ k) (hy : 2 * k + 2 ≤ y) (hyY : y ^ 2 ≤ Y)
    (hwin : ∑ r ∈ (Finset.Ioc y (y ^ 2)).filter Nat.Prime, (1 : ℝ) / r ≤ 32)
    (hmass : (1 : ℝ) / (16 * (Nat.totient q : ℝ))
      ≤ ∑ p ∈ goodWindow q m₀ k a y, (1 : ℝ) / p) :
    c₂ / (16 * (Nat.totient q : ℝ))
        * (((stepCell q Y k m₀).filter (fun m => SurvivesUpTo q y k m)).card : ℝ)
      ≤ (((stepCell q Y k m₀).filter
          (fun m => SurvivesUpTo q y k m ∧ genSeqAvoid q m k % q = a % q)).card : ℝ) := by
  have hnd2 : ∀ j < k, 2 ≤ genSeqAvoid q m₀ j := fun j hj => (hnd j hj).1
  have hyY' : y ≤ Y := by nlinarith [hyY, Nat.zero_le y]
  set C : Finset ℕ := stepCell q Y k m₀ with hC
  set G : Finset ℕ := goodWindow q m₀ k a y with hG
  set N : Finset ℕ := C.filter
    (fun m => SurvivesUpTo q y k m ∧ genSeqAvoid q m k % q = a % q) with hN
  -- The hit cells are pairwise disjoint and contained in `N`.
  have hdisj : ∀ p ∈ G, ∀ p' ∈ G, p ≠ p' →
      Disjoint (C.filter (fun m => genSeqAvoid q m k = p))
        (C.filter (fun m => genSeqAvoid q m k = p')) := by
    intro p _ p' _ hne
    rw [Finset.disjoint_left]
    intro m h1 h2
    exact hne (((Finset.mem_filter.mp h1).2).symm.trans (Finset.mem_filter.mp h2).2)
  have hsubN : G.biUnion (fun p => C.filter (fun m => genSeqAvoid q m k = p)) ⊆ N := by
    intro m hm
    obtain ⟨p, hpG, hmp⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨hmC, hmult⟩ := Finset.mem_filter.mp hmp
    obtain ⟨⟨hyp, _⟩, hp, hpq, hres, _, _⟩ := mem_goodWindow.mp hpG
    have hsurvp := (genSeqAvoid_eq_iff (m := m) hq hp hpq).mp hmult
    refine Finset.mem_filter.mpr ⟨hmC, ?_, ?_⟩
    · intro r hr hry hrq
      exact hsurvp.1 r hr (by omega) hrq
    · rw [hmult]; exact hres
  have hcount : ∑ p ∈ G, ((C.filter (fun m => genSeqAvoid q m k = p)).card : ℝ)
      ≤ (N.card : ℝ) := by
    have h1 : ∑ p ∈ G, (C.filter (fun m => genSeqAvoid q m k = p)).card
        = (G.biUnion (fun p => C.filter (fun m => genSeqAvoid q m k = p))).card :=
      (Finset.card_biUnion hdisj).symm
    have h2 : (G.biUnion (fun p => C.filter (fun m => genSeqAvoid q m k = p))).card ≤ N.card :=
      Finset.card_le_card hsubN
    have h3 : ∑ p ∈ G, (C.filter (fun m => genSeqAvoid q m k = p)).card ≤ N.card := by
      rw [h1]; exact h2
    exact_mod_cast (by exact_mod_cast h3 :
      ((∑ p ∈ G, (C.filter (fun m => genSeqAvoid q m k = p)).card : ℕ) : ℝ) ≤ (N.card : ℝ))
  -- Per-prime lower bound, summed.
  have hlow : ∀ p ∈ G,
      c₂ * survival q m₀ y k * ((C.card : ℝ)) * (1 / (p : ℝ))
        ≤ ((C.filter (fun m => genSeqAvoid q m k = p)).card : ℝ) := by
    intro p hpG
    exact hitCell_card_ge hq hm₀ hnd hk hy hyY hwin hpG
  have hsum : c₂ * survival q m₀ y k * ((C.card : ℝ)) * (∑ p ∈ G, (1 : ℝ) / p)
      ≤ (N.card : ℝ) := by
    calc c₂ * survival q m₀ y k * ((C.card : ℝ)) * (∑ p ∈ G, (1 : ℝ) / p)
        = ∑ p ∈ G, c₂ * survival q m₀ y k * ((C.card : ℝ)) * (1 / (p : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ G, ((C.filter (fun m => genSeqAvoid q m k = p)).card : ℝ) :=
          Finset.sum_le_sum hlow
      _ ≤ (N.card : ℝ) := hcount
  -- Replace the good-window mass by its lower bound.
  have hS0 : 0 ≤ survival q m₀ y k := survival_nonneg hq hm₀ hnd2 y
  have hcoef : (0 : ℝ) ≤ c₂ * survival q m₀ y k * ((C.card : ℝ)) := by
    have := c₂_pos
    have : (0 : ℝ) ≤ ((C.card : ℝ)) := by positivity
    positivity
  have hfin : c₂ * survival q m₀ y k * ((C.card : ℝ)) * (1 / (16 * (Nat.totient q : ℝ)))
      ≤ (N.card : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hmass hcoef) hsum
  -- Rewrite the denominator using the selection law.
  have hsel := selection_law (y := y) hq hm₀ hnd hyY'
  rw [← hC] at hsel
  rw [hsel]
  calc c₂ / (16 * (Nat.totient q : ℝ)) * (survival q m₀ y k * ((C.card : ℝ)))
      = c₂ * survival q m₀ y k * ((C.card : ℝ)) * (1 / (16 * (Nat.totient q : ℝ))) := by ring
    _ ≤ (N.card : ℝ) := hfin

/-! ## §7  The good-window reciprocal mass

The window `(y, y²]` of primes in the class `a` mod `q` carries mass `≥ 1/(8 φ(q))`
(`window_ap_recip_lower`).  The primes that are *not* good fall into three families, each of
mass `≤ 1/Cc`:

* **divisors of the seed** — the `(d-2)` exclusion hypothesis;
* **earlier multipliers** — at most `k` of them, each `≥ y ≥ Cc·k`;
* **old positions** — at most `k · log₂ c_k` of them (`TailEstimate.old_count_le`), each
  `≥ y = Cc·k·log₂ c_k`.

Hence at least `1/(8φ) − 3/Cc ≥ 1/(16φ)` survives, provided `Cc ≥ 48 q ≥ 48 φ(q)`. -/

/-- The full AP window: primes of `(y, y²]` in the class `a` mod `q`. -/
def apWindow (q a y : ℕ) : Finset ℕ :=
  (Finset.Ioc y (y ^ 2)).filter (fun p => p.Prime ∧ p % q = a % q)

theorem mem_apWindow {q a y p : ℕ} :
    p ∈ apWindow q a y ↔ (y < p ∧ p ≤ y ^ 2) ∧ p.Prime ∧ p % q = a % q := by
  rw [apWindow, Finset.mem_filter, Finset.mem_Ioc]

theorem goodWindow_subset_apWindow {q m₀ k a y : ℕ} :
    goodWindow q m₀ k a y ⊆ apWindow q a y := by
  intro p hp
  obtain ⟨hw, hpr, _, hres, _, _⟩ := mem_goodWindow.mp hp
  exact mem_apWindow.mpr ⟨hw, hpr, hres⟩

/-- A prime in a class coprime to `q` is not `q` itself. -/
theorem ne_avoided_of_mem_apWindow {q a y p : ℕ} (hq : q.Prime) (hcop : Nat.Coprime a q)
    (hp : p ∈ apWindow q a y) : p ≠ q := by
  obtain ⟨-, -, hres⟩ := mem_apWindow.mp hp
  intro hpq
  subst hpq
  have h0 : a % p = 0 := by
    have := Nat.mod_self p
    omega
  have hdvd : p ∣ a := Nat.dvd_of_mod_eq_zero h0
  have hg : Nat.gcd a p = 1 := hcop
  have hd : p ∣ Nat.gcd a p := Nat.dvd_gcd hdvd dvd_rfl
  rw [hg] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hq.two_le
  omega

/-- A finite set of primes all exceeding `y` carries reciprocal mass at most `card / y`. -/
private theorem sum_recip_le_card_div {S : Finset ℕ} {y : ℕ} (hy : 0 < y)
    (hS : ∀ p ∈ S, y < p) : ∑ p ∈ S, (1 : ℝ) / p ≤ (S.card : ℝ) / y := by
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
  have hstep : ∀ p ∈ S, (1 : ℝ) / p ≤ (1 : ℝ) / y := by
    intro p hp
    have h := hS p hp
    have : (y : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_of_lt h
    exact one_div_le_one_div_of_le hyR this
  calc ∑ p ∈ S, (1 : ℝ) / p ≤ ∑ _p ∈ S, (1 : ℝ) / y := Finset.sum_le_sum hstep
    _ = (S.card : ℝ) * ((1 : ℝ) / y) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (S.card : ℝ) / y := by ring

/-- **The good-window mass.**  Under the `(d-2)` seed-divisor exclusion and the size
conditions on the cut `y`, the good primes of the window carry at least half of the full AP
window mass. -/
theorem good_window_mass {q m₀ k a Cc Y y z : ℕ} (hq : q.Prime) (hcop : Nat.Coprime a q)
    (hnd2 : ∀ j < k, 2 ≤ genSeqAvoid q m₀ j)
    (hCc : 48 * q ≤ Cc) (hCcy : Cc ≤ y) (hky : Cc * k ≤ y)
    (holdy : Cc * k * Nat.log 2 (seedCofactorAvoid q m₀ k) ≤ y)
    (hy2Y : y ^ 2 ≤ Y) (hzy : z ≤ y)
    (hdiv : ∑ r ∈ (Finset.Ioc z Y).filter (fun r => r.Prime ∧ r ∣ m₀), (1 : ℝ) / r
      ≤ 1 / Cc)
    (hAP : (1 : ℝ) / (8 * (Nat.totient q : ℝ)) ≤ ∑ p ∈ apWindow q a y, (1 : ℝ) / p) :
    (1 : ℝ) / (16 * (Nat.totient q : ℝ)) ≤ ∑ p ∈ goodWindow q m₀ k a y, (1 : ℝ) / p := by
  have hq2 := hq.two_le
  have hCc0 : 0 < Cc := by omega
  have hy0 : 0 < y := by omega
  have hyR : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy0
  have hCcR : (0 : ℝ) < (Cc : ℝ) := by exact_mod_cast hCc0
  have hφ0 : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  set A : Finset ℕ := apWindow q a y with hA
  set G : Finset ℕ := goodWindow q m₀ k a y with hG
  have hGA : G ⊆ A := goodWindow_subset_apWindow
  set B : Finset ℕ := A \ G with hB
  have hsplit : ∑ p ∈ B, (1 : ℝ) / p + ∑ p ∈ G, (1 : ℝ) / p = ∑ p ∈ A, (1 : ℝ) / p :=
    Finset.sum_sdiff hGA
  -- Basic facts about the elements of `B`.
  have hBmem : ∀ p ∈ B, (y < p ∧ p ≤ y ^ 2) ∧ p.Prime ∧ p % q = a % q ∧ p ≠ q ∧ p ∉ G := by
    intro p hp
    rw [hB, Finset.mem_sdiff] at hp
    obtain ⟨hw, hpr, hres⟩ := mem_apWindow.mp hp.1
    exact ⟨hw, hpr, hres, ne_avoided_of_mem_apWindow hq hcop hp.1, hp.2⟩
  -- The three bad families.
  set D1 : Finset ℕ := B.filter (fun p => p ∣ m₀) with hD1
  set B' : Finset ℕ := B.filter (fun p => ¬ p ∣ m₀) with hB'
  set D2 : Finset ℕ := B'.filter (fun p => inBag q m₀ p k) with hD2
  set D3 : Finset ℕ := B'.filter (fun p => ¬ inBag q m₀ p k) with hD3
  have e1 : ∑ p ∈ D1, (1 : ℝ) / p + ∑ p ∈ B', (1 : ℝ) / p = ∑ p ∈ B, (1 : ℝ) / p :=
    Finset.sum_filter_add_sum_filter_not B (fun p => p ∣ m₀) _
  have e2 : ∑ p ∈ D2, (1 : ℝ) / p + ∑ p ∈ D3, (1 : ℝ) / p = ∑ p ∈ B', (1 : ℝ) / p :=
    Finset.sum_filter_add_sum_filter_not B' (fun p => inBag q m₀ p k) _
  -- (i) divisors of the seed.
  have hb1 : ∑ p ∈ D1, (1 : ℝ) / p ≤ 1 / Cc := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)) hdiv
    intro p hp
    rw [hD1, Finset.mem_filter] at hp
    obtain ⟨hw, hpr, -, -, -⟩ := hBmem p hp.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega, le_trans hw.2 hy2Y⟩, hpr, hp.2⟩
  -- (ii) earlier multipliers.
  have hb2 : ∑ p ∈ D2, (1 : ℝ) / p ≤ 1 / Cc := by
    have hcard : D2.card ≤ k := by
      have hsub : D2 ⊆ (Finset.range k).image (fun i => genSeqAvoid q m₀ i) := by
        intro p hp
        rw [hD2, Finset.mem_filter, hB', Finset.mem_filter] at hp
        rcases hp.2 with hd | ⟨i, hik, hieq⟩
        · exact absurd hd hp.1.2
        · exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hik, hieq⟩
      exact le_trans (Finset.card_le_card hsub)
        (le_trans Finset.card_image_le (le_of_eq (Finset.card_range k)))
    have hgt : ∀ p ∈ D2, y < p := by
      intro p hp
      rw [hD2, Finset.mem_filter, hB', Finset.mem_filter] at hp
      exact (hBmem p hp.1.1).1.1
    have hstep := sum_recip_le_card_div hy0 hgt
    have hck : (D2.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcard
    have hfin : (k : ℝ) / y ≤ 1 / Cc := by
      rw [div_le_div_iff₀ hyR hCcR]
      have : ((Cc * k : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hky
      push_cast at this
      linarith
    calc ∑ p ∈ D2, (1 : ℝ) / p ≤ (D2.card : ℝ) / y := hstep
      _ ≤ (k : ℝ) / y := by gcongr
      _ ≤ 1 / Cc := hfin
  -- (iii) old positions.
  have hb3 : ∑ p ∈ D3, (1 : ℝ) / p ≤ 1 / Cc := by
    set L : ℕ := Nat.log 2 (seedCofactorAvoid q m₀ k) with hL
    have hcard : D3.card ≤ k * L := by
      have hsub : D3 ⊆ TailEstimate.oldSet q m₀ (y ^ 2 + 1) k := by
        intro p hp
        rw [hD3, Finset.mem_filter, hB', Finset.mem_filter] at hp
        obtain ⟨hw, hpr, hres, hpq, hpG⟩ := hBmem p hp.1.1
        have hnew : ¬ isNew q m₀ p k := by
          intro hnew
          exact hpG (mem_goodWindow.mpr ⟨hw, hpr, hpq, hres, hp.2, hnew⟩)
        rw [TailEstimate.oldSet, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hpr, hnew⟩
      exact le_trans (Finset.card_le_card hsub) (TailEstimate.old_count_le hnd2 _)
    have hgt : ∀ p ∈ D3, y < p := by
      intro p hp
      rw [hD3, Finset.mem_filter, hB', Finset.mem_filter] at hp
      exact (hBmem p hp.1.1).1.1
    have hstep := sum_recip_le_card_div hy0 hgt
    have hck : (D3.card : ℝ) ≤ ((k * L : ℕ) : ℝ) := by exact_mod_cast hcard
    have hfin : ((k * L : ℕ) : ℝ) / y ≤ 1 / Cc := by
      rw [div_le_div_iff₀ hyR hCcR]
      have : ((Cc * k * L : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast holdy
      push_cast at this ⊢
      linarith
    calc ∑ p ∈ D3, (1 : ℝ) / p ≤ (D3.card : ℝ) / y := hstep
      _ ≤ ((k * L : ℕ) : ℝ) / y := by gcongr
      _ ≤ 1 / Cc := hfin
  -- Assemble.
  have hbad : ∑ p ∈ B, (1 : ℝ) / p ≤ 3 / Cc := by
    have : (3 : ℝ) / Cc = 1 / Cc + (1 / Cc + 1 / Cc) := by ring
    rw [this, ← e1, ← e2]
    linarith
  have h3 : (3 : ℝ) / Cc ≤ 1 / (16 * (Nat.totient q : ℝ)) := by
    rw [div_le_div_iff₀ hCcR (by positivity)]
    have hφq : (Nat.totient q : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
    have hCcq : (48 : ℝ) * (q : ℝ) ≤ (Cc : ℝ) := by exact_mod_cast hCc
    nlinarith
  have hhalf : (1 : ℝ) / (8 * (Nat.totient q : ℝ))
      = 2 * ((1 : ℝ) / (16 * (Nat.totient q : ℝ))) := by
    field_simp
    ring
  linarith

/-- **Lemma D, box side, mass form.**  Combining §6 with §7: under the `(d-2)` exclusion and
the analytic window inputs, the class-selection lower bound holds with the absolute constant
`κ = c₂/(16 φ(q))`. -/
theorem lemma_D_mass {q Y k m₀ a Cc y z : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hcop : Nat.Coprime a q)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y)
    (hk : 1 ≤ k) (hy : 2 * k + 2 ≤ y) (hyY : y ^ 2 ≤ Y)
    (hCc : 48 * q ≤ Cc) (hCcy : Cc ≤ y) (hky : Cc * k ≤ y)
    (holdy : Cc * k * Nat.log 2 (seedCofactorAvoid q m₀ k) ≤ y)
    (hwin : ∑ r ∈ (Finset.Ioc y (y ^ 2)).filter Nat.Prime, (1 : ℝ) / r ≤ 32)
    (hzy : z ≤ y)
    (hdiv : ∑ r ∈ (Finset.Ioc z Y).filter (fun r => r.Prime ∧ r ∣ m₀), (1 : ℝ) / r
      ≤ 1 / Cc)
    (hAP : (1 : ℝ) / (8 * (Nat.totient q : ℝ)) ≤ ∑ p ∈ apWindow q a y, (1 : ℝ) / p) :
    c₂ / (16 * (Nat.totient q : ℝ))
        * (((stepCell q Y k m₀).filter (fun m => SurvivesUpTo q y k m)).card : ℝ)
      ≤ (((stepCell q Y k m₀).filter
          (fun m => SurvivesUpTo q y k m ∧ genSeqAvoid q m k % q = a % q)).card : ℝ) :=
  lemma_D_of_good_mass hq hm₀ hnd hk hy hyY hwin
    (good_window_mass hq hcop (fun j hj => (hnd j hj).1) hCc hCcy hky holdy hyY hzy hdiv hAP)

/-! ## §8  Lemma D at the moving threshold `y_k = Cc·k·log₂ c_k` -/

private theorem floor_cast_self (y : ℕ) : Nat.floor ((y : ℝ)) = y := Nat.floor_natCast y

private theorem floor_cast_sq (y : ℕ) : Nat.floor (((y : ℝ)) ^ 2) = y ^ 2 := by
  rw [show ((y : ℝ)) ^ 2 = ((y ^ 2 : ℕ) : ℝ) by push_cast; ring]
  exact Nat.floor_natCast _

/-- **Lemma D (box side), final form, with a free exclusion window start `z`.**

For every prime `q` and every constant `Cc ≥ 48 q` there is an absolute-shape constant
`κ = c₂/(16 φ(q)) > 0` and a depth `k₀ = k₀(q, Cc)` such that: at every depth `k ≥ k₀`, in
every type cell whose reference prefix is nondegenerate and `≤ Y`, whose `A = 2` window fits
inside the truncation, and which satisfies the `(d-2)` seed-divisor exclusion on the window
`(z, Y]`, the seeds making a large step at depth `k` land in **any** prescribed class `a`
coprime to `q` with proportion at least `κ`.

The exclusion window start `z` is a free parameter: the only place it is used is the
divisor-of-the-seed family of §7, whose members lie in `(y_k, y_k²] ⊆ (z, Y]` under the
per-call hypothesis `z ≤ y_k`.  Neither `κ` nor `k₀` depends on `z`, so a caller discharging
the exclusion by a Markov argument at a larger start (e.g. `z = Cc²`) may do so freely.

The three analytic inputs are `window_ap_recip_lower` (the AP window mass, whose threshold is
made uniform in `a` by a `Finset.sup` over the `q` residues), `window_recip_upper` (the crude
window mass, constant `32`), and `TailEstimate.old_count_le` (the old-position count). -/
theorem lemma_D_z (q : ℕ) (hq : q.Prime) (Cc : ℕ) (hCc : 48 * q ≤ Cc) (z : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ k₀ : ℕ, ∀ Y k m₀ a : ℕ,
      1 ≤ m₀ →
      (∀ j < k, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y) →
      k₀ ≤ k →
      z ≤ bigThreshold q m₀ Cc k →
      (bigThreshold q m₀ Cc k) ^ 2 ≤ Y →
      (∑ r ∈ (Finset.Ioc z Y).filter (fun r => r.Prime ∧ r ∣ m₀), (1 : ℝ) / r ≤ 1 / Cc) →
      Nat.Coprime a q →
      κ * (((stepCell q Y k m₀).filter
             (fun m => SurvivesUpTo q (bigThreshold q m₀ Cc k) k m)).card : ℝ)
        ≤ (((stepCell q Y k m₀).filter
             (fun m => SurvivesUpTo q (bigThreshold q m₀ Cc k) k m
               ∧ genSeqAvoid q m k % q = a % q)).card : ℝ) := by
  have hq2 := hq.two_le
  have hφ0 : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  -- A threshold for each residue class, uniformised by a `Finset.sup`.
  have hchoice : ∀ b : ℕ, ∃ Y0 : ℝ, 2 ≤ Y0 ∧ (Nat.Coprime b q →
      ∀ z : ℝ, Y0 ≤ z → (1 : ℝ) / (8 * (Nat.totient q : ℝ)) ≤
        ∑ p ∈ (Finset.Ioc (Nat.floor z) (Nat.floor (z ^ 2))).filter
          (fun p => Nat.Prime p ∧ p % q = b % q), 1 / (p : ℝ)) := by
    intro b
    by_cases hb : Nat.Coprime b q
    · obtain ⟨Y0, h2, h⟩ := window_ap_recip_lower q b hq.one_lt hb
      exact ⟨Y0, h2, fun _ => h⟩
    · exact ⟨2, le_refl 2, fun hc => absurd hc hb⟩
  choose Y0 hY02 hY0 using hchoice
  refine ⟨c₂ / (16 * (Nat.totient q : ℝ)), div_pos c₂_pos (by positivity),
    max 1 ((Finset.range q).sup (fun b => Nat.ceil (Y0 b))), ?_⟩
  intro Y k m₀ a hm₀ hnd hk₀ hzy hyY hdiv hcop
  have hnd2 : ∀ j < k, 2 ≤ genSeqAvoid q m₀ j := fun j hj => (hnd j hj).1
  have hk : 1 ≤ k := le_trans (le_max_left _ _) hk₀
  -- Size facts about the moving threshold.
  set L : ℕ := Nat.log 2 (seedCofactorAvoid q m₀ k) with hL
  have hLk : k ≤ L := le_log_cofactor hnd2
  have hL1 : 1 ≤ L := le_trans hk hLk
  have hCc96 : 96 ≤ Cc := by omega
  have hybig : bigThreshold q m₀ Cc k = Cc * k * L := rfl
  set y : ℕ := bigThreshold q m₀ Cc k with hy
  have hy96 : 96 * k * k ≤ y := by
    rw [hybig]
    exact Nat.mul_le_mul (Nat.mul_le_mul hCc96 le_rfl) hLk
  have hyk : k ≤ y := by nlinarith
  have hy2k : 2 * k + 2 ≤ y := by nlinarith
  have hCcy : Cc ≤ y := by
    rw [hybig]
    calc Cc = Cc * 1 * 1 := by ring
      _ ≤ Cc * k * L := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hk) hL1
  have hky : Cc * k ≤ y := by
    rw [hybig]
    calc Cc * k = Cc * k * 1 := by ring
      _ ≤ Cc * k * L := Nat.mul_le_mul le_rfl hL1
  have holdy : Cc * k * L ≤ y := le_of_eq hybig.symm
  have hyR4 : (4 : ℝ) ≤ (y : ℝ) := by
    have : (4 : ℕ) ≤ y := by omega
    exact_mod_cast this
  -- The crude window mass.
  have hwin : ∑ r ∈ (Finset.Ioc y (y ^ 2)).filter Nat.Prime, (1 : ℝ) / r ≤ 32 := by
    have h := window_recip_upper (y : ℝ) hyR4
    rwa [floor_cast_self, floor_cast_sq] at h
  -- The AP window mass.
  have hbq : a % q < q := Nat.mod_lt _ (by omega)
  have hcopb : Nat.Coprime (a % q) q := by
    have h1 : Nat.gcd q a = Nat.gcd (a % q) q := Nat.gcd_rec q a
    have h2 : Nat.gcd q a = 1 := by rw [Nat.gcd_comm]; exact hcop
    rw [h1] at h2
    exact h2
  have hthresh : Y0 (a % q) ≤ (y : ℝ) := by
    have h1 : Nat.ceil (Y0 (a % q)) ≤ (Finset.range q).sup (fun b => Nat.ceil (Y0 b)) :=
      Finset.le_sup (f := fun b => Nat.ceil (Y0 b)) (Finset.mem_range.mpr hbq)
    have h2 : Nat.ceil (Y0 (a % q)) ≤ k := le_trans h1 (le_trans (le_max_right _ _) hk₀)
    have h3 : Nat.ceil (Y0 (a % q)) ≤ y := le_trans h2 hyk
    have h4 : Y0 (a % q) ≤ (Nat.ceil (Y0 (a % q)) : ℝ) := Nat.le_ceil _
    have h5 : ((Nat.ceil (Y0 (a % q)) : ℕ) : ℝ) ≤ (y : ℝ) := by exact_mod_cast h3
    linarith
  have hAP : (1 : ℝ) / (8 * (Nat.totient q : ℝ)) ≤ ∑ p ∈ apWindow q a y, (1 : ℝ) / p := by
    have h := hY0 (a % q) hcopb (y : ℝ) hthresh
    rw [floor_cast_self, floor_cast_sq] at h
    have hset : (Finset.Ioc y (y ^ 2)).filter
        (fun p => Nat.Prime p ∧ p % q = (a % q) % q) = apWindow q a y := by
      rw [apWindow]
      refine Finset.filter_congr ?_
      intro p _
      rw [Nat.mod_mod_of_dvd a dvd_rfl]
    rwa [hset] at h
  exact lemma_D_mass hq hm₀ hcop hnd hk hy2k hyY hCc hCcy hky holdy hwin hzy hdiv hAP

/-- **Lemma D (box side), `z = Cc` form.**  The specialisation of `lemma_D_z` to the exclusion
window `(Cc, Y]`; the hypothesis `Cc ≤ y_k` is automatic from `k ≥ 1` and `log₂ c_k ≥ 1`. -/
theorem lemma_D (q : ℕ) (hq : q.Prime) (Cc : ℕ) (hCc : 48 * q ≤ Cc) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ k₀ : ℕ, ∀ Y k m₀ a : ℕ,
      1 ≤ m₀ →
      (∀ j < k, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y) →
      k₀ ≤ k →
      (bigThreshold q m₀ Cc k) ^ 2 ≤ Y →
      (∑ r ∈ (Finset.Ioc Cc Y).filter (fun r => r.Prime ∧ r ∣ m₀), (1 : ℝ) / r ≤ 1 / Cc) →
      Nat.Coprime a q →
      κ * (((stepCell q Y k m₀).filter
             (fun m => SurvivesUpTo q (bigThreshold q m₀ Cc k) k m)).card : ℝ)
        ≤ (((stepCell q Y k m₀).filter
             (fun m => SurvivesUpTo q (bigThreshold q m₀ Cc k) k m
               ∧ genSeqAvoid q m k % q = a % q)).card : ℝ) := by
  obtain ⟨κ, hκ, k₀, h⟩ := lemma_D_z q hq Cc hCc Cc
  refine ⟨κ, hκ, max 1 k₀, ?_⟩
  intro Y k m₀ a hm₀ hnd hk₀ hyY hdiv hcop
  refine h Y k m₀ a hm₀ hnd (le_trans (le_max_right _ _) hk₀) ?_ hyY hdiv hcop
  have hk : 1 ≤ k := le_trans (le_max_left _ _) hk₀
  have hL1 : 1 ≤ Nat.log 2 (seedCofactorAvoid q m₀ k) :=
    le_trans hk (le_log_cofactor (fun j hj => (hnd j hj).1))
  show Cc ≤ Cc * k * Nat.log 2 (seedCofactorAvoid q m₀ k)
  calc Cc = Cc * 1 * 1 := by ring
    _ ≤ Cc * k * Nat.log 2 (seedCofactorAvoid q m₀ k) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl hk) hL1

end LemmaD

end
