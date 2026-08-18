import EM.Population.SelectionLaw
import EM.Population.TreeChernoff

/-!
# (LS+) — the tree Chernoff instantiated with the selection law

This file composes the two Session-310 layers,

* the **abstract finite-tree Chernoff bound** of `EM/Population/TreeChernoff.lean`
  (the C5-replacement: an elementary exponential supermartingale over a finite
  `Finset`), and
* the **selection law** of `EM/Population/SelectionLaw.lean` (the exact counting
  identity `#(cell ∩ {survives up to y}) = survival · #cell`),

into the honest population statement **(LS+)** of
`agents/state/findings_ls_verification.md` §2.5(f) T3 / §4 Group 6.

Correction **C6** (truncation of the process once the compensator misbehaves) is
handled by *localization* rather than by stopping: the bad event is intersected
with the compensator event, see `TreeChernoff.chernoff_quarter_local`.

## Setting

The sample space is **one full period** of the `q`-free dynamics,
`sampleSpace q Y = [1, M_Y]` with `M_Y = ∏ {r ≤ Y : r prime, r ≠ q}`.  The
filtration is the *type at depth `k`*

```
typeData q Y k m = (first k q-free multipliers of m, small prime divisors of m)
```

and the step event is the **large step**

```
bigStep q Cc k m  ↔  p̃_k(m) = 1  ∨  y_k(m) < p̃_k(m),   y_k = Cc·k·log₂ c_k,
```

which `bigStep_iff_survives` identifies with the survival event
`SurvivesUpTo q y_k k m` of the selection law (the `q`-power convention of
§2.8/§2.9 is folded in: `p̃_k = 1` means the Euclid number is a power of `q`,
and then *no* prime `≠ q` divides it).

## Main results

* `typeData_eq_iff`, `typeData_refine` — the filtration (D1).
* `cofactor_congr`, …, `stepSurvival_congr` — cell-constancy of the box process (D2).
* `fiber_eq_stepCell`, `bigStep_iff_survives` — fibers are selection-law cells (D3).
* `hcond_holds` — the conditional counting inequality, i.e. the selection law in
  the shape the tree Chernoff consumes (D4).
* `compensator_eq`, `ls_plus` — the headline (D5).

`findings_ls_verification.md` §2.5(f) T3, C6 handled by localization; Session 310.
-/

noncomputable section
open Classical

namespace LSPlus

open SeedCapture SeedTypes LargeStepRoughness SelectionLaw

/-! ## D1 — the filtration -/

/-- **The type at depth `k`.**  The first `k` `q`-free multipliers of the seed,
together with the set of band primes dividing the seed.  This is exactly the data
cut out by `SelectionLaw.stepCell`.

`findings_ls_verification.md` §2.5(f) T3; Session 310. -/
def typeData (q Y k m : ℕ) : List ℕ × Finset ℕ :=
  (List.ofFn (fun j : Fin k => genSeqAvoid q m j), (bandUpTo q Y).filter (fun r => r ∣ m))

/-- The type at depth `k` is *exactly* prefix agreement plus band divisibility
agreement. -/
theorem typeData_eq_iff {q Y k m m' : ℕ} :
    typeData q Y k m = typeData q Y k m' ↔
      ((∀ j < k, genSeqAvoid q m j = genSeqAvoid q m' j) ∧
        (∀ r ∈ bandUpTo q Y, (r ∣ m ↔ r ∣ m'))) := by
  rw [typeData, typeData, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro j hj
      have := congrFun (List.ofFn_inj.mp h1) ⟨j, hj⟩
      exact this
    · intro r hr
      have := Finset.ext_iff.mp h2 r
      rw [Finset.mem_filter, Finset.mem_filter] at this
      constructor
      · exact fun hd => (this.mp ⟨hr, hd⟩).2
      · exact fun hd => (this.mpr ⟨hr, hd⟩).2
  · rintro ⟨h1, h2⟩
    refine ⟨congrArg List.ofFn (funext fun j => h1 j j.isLt), ?_⟩
    exact Finset.filter_congr fun r hr => h2 r hr

/-- **`hrefine`.**  The type at depth `k+1` determines the type at depth `k`. -/
theorem typeData_refine {q Y k m m' : ℕ}
    (h : typeData q Y (k + 1) m = typeData q Y (k + 1) m') :
    typeData q Y k m = typeData q Y k m' := by
  obtain ⟨h1, h2⟩ := typeData_eq_iff.mp h
  exact typeData_eq_iff.mpr ⟨fun j hj => h1 j (by omega), h2⟩

/-! ## D2 — cell-constancy of the box process

Every ingredient of the roughness survival product at depth `k` is a function of
`typeData q Y k`.  The membership hypothesis `r ∈ bandUpTo q Y` is what makes the
`r ∣ m` disjunct of `inBag` type-measurable. -/

section Congr

variable {q Y k m m' : ℕ}

theorem cofactor_congr (h : typeData q Y k m = typeData q Y k m') {j : ℕ} (hj : j ≤ k) :
    seedCofactorAvoid q m j = seedCofactorAvoid q m' j := by
  rw [seedCofactorAvoid, seedCofactorAvoid]
  exact Finset.prod_congr rfl fun i hi =>
    (typeData_eq_iff.mp h).1 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)

theorem inBag_congr (h : typeData q Y k m = typeData q Y k m') {r j : ℕ}
    (hr : r ∈ bandUpTo q Y) (hj : j ≤ k) : inBag q m r j ↔ inBag q m' r j := by
  obtain ⟨h1, h2⟩ := typeData_eq_iff.mp h
  rw [inBag, inBag]
  refine or_congr (h2 r hr) ?_
  constructor
  · rintro ⟨i, hi, hieq⟩
    exact ⟨i, hi, by rw [← h1 i (by omega)]; exact hieq⟩
  · rintro ⟨i, hi, hieq⟩
    exact ⟨i, hi, by rw [h1 i (by omega)]; exact hieq⟩

theorem visitedAt_congr (h : typeData q Y k m = typeData q Y k m') {r j : ℕ} (hj : j ≤ k) :
    visitedAt q m r j = visitedAt q m' r j := by
  obtain ⟨h1, _⟩ := typeData_eq_iff.mp h
  rw [visitedAt, visitedAt]
  have hfil : (Finset.range j).filter (fun i => r < genSeqAvoid q m i)
      = (Finset.range j).filter (fun i => r < genSeqAvoid q m' i) :=
    Finset.filter_congr fun i hi => by
      rw [h1 i (lt_of_lt_of_le (Finset.mem_range.mp hi) hj)]
  rw [hfil]
  refine Finset.image_congr ?_
  intro i hi
  rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
  show ((seedCofactorAvoid q m i : ℕ) : ZMod r) = ((seedCofactorAvoid q m' i : ℕ) : ZMod r)
  rw [cofactor_congr h (le_of_lt (lt_of_lt_of_le hi.1 hj))]

theorem isNew_congr (h : typeData q Y k m = typeData q Y k m') {r j : ℕ} (hj : j ≤ k) :
    isNew q m r j ↔ isNew q m' r j := by
  rw [isNew, isNew, visitedAt_congr h hj, cofactor_congr h hj]

theorem box_congr (h : typeData q Y k m = typeData q Y k m') {r j : ℕ} (hj : j ≤ k) :
    box q m r j = box q m' r j := by
  rw [box, box, visitedAt_congr h hj]

theorem boxCard_congr (h : typeData q Y k m = typeData q Y k m') {r j : ℕ} (hj : j ≤ k) :
    boxCard q m r j = boxCard q m' r j := by
  rw [boxCard, boxCard, box_congr h hj]

theorem rho_congr (h : typeData q Y k m = typeData q Y k m') {r j : ℕ}
    (hr : r ∈ bandUpTo q Y) (hj : j ≤ k) : rho q m r j = rho q m' r j := by
  have hiff : (¬ inBag q m r j ∧ isNew q m r j) ↔ (¬ inBag q m' r j ∧ isNew q m' r j) :=
    and_congr (not_congr (inBag_congr h hr hj)) (isNew_congr h hj)
  by_cases hc : ¬ inBag q m r j ∧ isNew q m r j
  · rw [rho_of_active hc, rho_of_active (hiff.mp hc), boxCard_congr h hj]
  · rw [rho_eq_zero_of_inactive hc,
      rho_eq_zero_of_inactive (fun hcon => hc (hiff.mpr hcon))]

theorem bigThreshold_congr (h : typeData q Y k m = typeData q Y k m') (Cc : ℕ) :
    bigThreshold q m Cc k = bigThreshold q m' Cc k := by
  rw [bigThreshold, bigThreshold, cofactor_congr h le_rfl]

theorem survival_congr (h : typeData q Y k m = typeData q Y k m') {y : ℕ} (hy : y ≤ Y) :
    survival q m y k = survival q m' y k := by
  rw [survival, survival]
  refine Finset.prod_congr rfl fun r hr => ?_
  obtain ⟨hrY, hrp, hrq⟩ := mem_bandUpTo.mp hr
  rw [rho_congr h (mem_bandUpTo.mpr ⟨le_trans hrY hy, hrp, hrq⟩) le_rfl]

theorem stepSurvival_congr (h : typeData q Y k m = typeData q Y k m') {Cc : ℕ}
    (hthr : bigThreshold q m Cc k ≤ Y) :
    stepSurvival q m Cc k = stepSurvival q m' Cc k := by
  rw [stepSurvival, stepSurvival, ← bigThreshold_congr h Cc]
  exact survival_congr h hthr

end Congr

/-! ## D3 — fibers are cells, and the step event is the survival event -/

/-- The sample space: one full period of the `q`-free dynamics. -/
def sampleSpace (q Y : ℕ) : Finset ℕ := Finset.Ico 1 (modulus q Y + 1)

theorem mem_sampleSpace {q Y m : ℕ} :
    m ∈ sampleSpace q Y ↔ 1 ≤ m ∧ m < modulus q Y + 1 := Finset.mem_Ico

/-- **The large step at depth `k`.**  Either the Euclid number is a power of `q`
(`p̃_k = 1`, the degenerate case of §2.8) or its least prime factor `≠ q` exceeds
the moving threshold `y_k = Cc·k·log₂ c_k`. -/
def bigStep (q Cc k m : ℕ) : Prop :=
  genSeqAvoid q m k = 1 ∨ bigThreshold q m Cc k < genSeqAvoid q m k

instance decidableBigStep (q Cc k m : ℕ) : Decidable (bigStep q Cc k m) := by
  unfold bigStep
  infer_instance

/-- **D3(c) — the bridge.**  The large step at depth `k` is *exactly* the
selection-law survival event at the moving threshold.  Both degenerate regimes
line up: `p̃_k = 1` means the `q`-free part of the Euclid number is `1`, so no
prime `≠ q` divides it at all.

`findings_ls_verification.md` §2.8/§2.9, §2.5(f) T3; Session 310. -/
theorem bigStep_iff_survives {q Cc k m : ℕ} (hq : q.Prime) :
    bigStep q Cc k m ↔ SurvivesUpTo q (bigThreshold q m Cc k) k m := by
  have hNne : genProdAvoid q m k + 1 ≠ 0 := Nat.succ_ne_zero _
  have hgs : genSeqAvoid q m k = (qfreePart q (genProdAvoid q m k + 1)).minFac := rfl
  constructor
  · intro hbs r hr hry hrq hdvd
    have hle : (qfreePart q (genProdAvoid q m k + 1)).minFac ≤ r :=
      minFac_qfreePart_least hq hNne hr hrq hdvd
    rcases hbs with h1 | h2
    · rw [hgs] at h1
      have hq1 : qfreePart q (genProdAvoid q m k + 1) = 1 := by
        have hpos : 0 < qfreePart q (genProdAvoid q m k + 1) := qfreePart_pos q hNne
        by_contra hcon
        have h2le : 2 ≤ qfreePart q (genProdAvoid q m k + 1) := by omega
        have hp := (minFac_qfreePart_spec hq hNne h2le).1
        rw [h1] at hp
        exact Nat.not_prime_one hp
      have hrd : r ∣ qfreePart q (genProdAvoid q m k + 1) :=
        (prime_dvd_qfreePart_iff hq hr hrq hNne).mpr hdvd
      rw [hq1] at hrd
      have := Nat.dvd_one.mp hrd
      exact hr.one_lt.ne' this
    · rw [hgs] at h2
      omega
  · intro hsurv
    by_contra hcon
    obtain ⟨h1, h2⟩ := not_or.mp hcon
    have h2' : genSeqAvoid q m k ≤ bigThreshold q m Cc k := Nat.le_of_not_lt h2
    have h2le : 2 ≤ qfreePart q (genProdAvoid q m k + 1) := by
      have hpos : 0 < qfreePart q (genProdAvoid q m k + 1) := qfreePart_pos q hNne
      by_contra hc
      have he : qfreePart q (genProdAvoid q m k + 1) = 1 := by omega
      rw [hgs, he, Nat.minFac_one] at h1
      exact h1 rfl
    obtain ⟨hp, hpd, hpq⟩ := minFac_qfreePart_spec hq hNne h2le
    exact hsurv _ hp (by rw [← hgs]; exact h2') hpq hpd

/-- **D3(d) — the fibers of the filtration are exactly the selection-law cells.**
Purely definitional: `stepCell` filters the same period by the same prefix and
divisibility data. -/
theorem fiber_eq_stepCell (q Y k m₀ : ℕ) :
    (sampleSpace q Y).filter (fun m => typeData q Y k m = typeData q Y k m₀)
      = stepCell q Y k m₀ := by
  ext m
  rw [Finset.mem_filter, mem_sampleSpace, mem_stepCell, typeData_eq_iff]
  constructor
  · rintro ⟨hmem, hpref, hdvd⟩
    exact ⟨hmem, hpref, fun r hr hrY hrq => hdvd r (mem_bandUpTo.mpr ⟨hrY, hr, hrq⟩)⟩
  · rintro ⟨hmem, hpref, hdvd⟩
    refine ⟨hmem, hpref, fun r hr => ?_⟩
    obtain ⟨hrY, hrp, hrq⟩ := mem_bandUpTo.mp hr
    exact hdvd r hrp hrY hrq

/-! ## D4 — the predicted conditional survival, and `hcond` -/

/-- The survival product is at most `1`: every band factor lies in `[0, 1]`. -/
theorem survival_le_one {q m y k : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) : survival q m y k ≤ 1 := by
  rw [survival]
  refine Finset.prod_le_one (fun r hr => ?_) (fun r hr => ?_)
  · obtain ⟨_, hrp, hrq⟩ := mem_bandUpTo.mp hr
    have := rho_le_one hq hm hrp hrq hnd
    linarith
  · have h0 : 0 ≤ rho q m r k := rho_nonneg
    linarith

/-- The guard: the type `b` is realized by a seed of the period with a
nondegenerate, `Y`-bounded prefix and a threshold inside the band. -/
def cellGuard (q Y Cc k : ℕ) (b : List ℕ × Finset ℕ) : Prop :=
  ∃ m₀ ∈ sampleSpace q Y, typeData q Y k m₀ = b
    ∧ (∀ j < k, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y)
    ∧ bigThreshold q m₀ Cc k ≤ Y

/-- **The predicted conditional survival of a type.**  Well defined by D2: any
two representatives of the same type have the same `stepSurvival`. -/
def cellSurvival (q Y Cc k : ℕ) (b : List ℕ × Finset ℕ) : ℝ :=
  if h : cellGuard q Y Cc k b then stepSurvival q h.choose Cc k else 0

/-- **Well-definedness.**  On a realized type the predicted survival is the
`stepSurvival` of *any* representative. -/
theorem cellSurvival_eq {q Y Cc k m₀ : ℕ} (hm₀ : m₀ ∈ sampleSpace q Y)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y)
    (hthr : bigThreshold q m₀ Cc k ≤ Y) :
    cellSurvival q Y Cc k (typeData q Y k m₀) = stepSurvival q m₀ Cc k := by
  have hg : cellGuard q Y Cc k (typeData q Y k m₀) := ⟨m₀, hm₀, rfl, hnd, hthr⟩
  rw [cellSurvival, dif_pos hg]
  obtain ⟨_, htyp, _, hthr'⟩ := hg.choose_spec
  exact stepSurvival_congr htyp hthr'

theorem cellSurvival_nonneg {q Y Cc k : ℕ} (hq : q.Prime) (b : List ℕ × Finset ℕ) :
    0 ≤ cellSurvival q Y Cc k b := by
  rw [cellSurvival]
  split
  · rename_i hg
    obtain ⟨hmem, _, hnd, _⟩ := hg.choose_spec
    rw [stepSurvival]
    exact survival_nonneg hq (mem_sampleSpace.mp hmem).1 (fun j hj => (hnd j hj).1) _
  · exact le_rfl

theorem cellSurvival_le_one {q Y Cc k : ℕ} (hq : q.Prime) (b : List ℕ × Finset ℕ) :
    cellSurvival q Y Cc k b ≤ 1 := by
  rw [cellSurvival]
  split
  · rename_i hg
    obtain ⟨hmem, _, hnd, _⟩ := hg.choose_spec
    rw [stepSurvival]
    exact survival_le_one hq (mem_sampleSpace.mp hmem).1 (fun j hj => (hnd j hj).1)
  · exact zero_le_one

/-- **D4 — the conditional counting inequality.**  This *is* the selection law,
restated in the shape the abstract tree Chernoff bound consumes: inside a type
cell, the fraction of seeds taking a large step is at least the predicted
conditional survival of that type.

`findings_ls_verification.md` §2.5(f) T3; Session 310. -/
theorem hcond_holds {q Y Cc : ℕ} (hq : q.Prime) (k : ℕ) (b : List ℕ × Finset ℕ) :
    cellSurvival q Y Cc k b
        * (((sampleSpace q Y).filter (fun m => typeData q Y k m = b)).card : ℝ)
      ≤ (((sampleSpace q Y).filter
          (fun m => typeData q Y k m = b ∧ bigStep q Cc k m)).card : ℝ) := by
  by_cases hg : cellGuard q Y Cc k b
  · obtain ⟨m₀, hm₀mem, hm₀typ, hm₀nd, hm₀thr⟩ := hg
    subst hm₀typ
    have hand : (sampleSpace q Y).filter
          (fun m => typeData q Y k m = typeData q Y k m₀ ∧ bigStep q Cc k m)
        = (stepCell q Y k m₀).filter
          (fun m => SurvivesUpTo q (bigThreshold q m₀ Cc k) k m) := by
      ext m
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hmem, htyp, hbs⟩
        refine ⟨?_, ?_⟩
        · rw [← fiber_eq_stepCell q Y k m₀]
          exact Finset.mem_filter.mpr ⟨hmem, htyp⟩
        · have hsv := (bigStep_iff_survives hq).mp hbs
          rwa [bigThreshold_congr htyp Cc] at hsv
      · rintro ⟨hcell, hsurv⟩
        have hmemf : m ∈ (sampleSpace q Y).filter
            (fun m => typeData q Y k m = typeData q Y k m₀) := by
          rw [fiber_eq_stepCell]; exact hcell
        obtain ⟨hmem, htyp⟩ := Finset.mem_filter.mp hmemf
        refine ⟨hmem, htyp, (bigStep_iff_survives hq).mpr ?_⟩
        rwa [bigThreshold_congr htyp Cc]
    rw [hand, fiber_eq_stepCell, cellSurvival_eq hm₀mem hm₀nd hm₀thr, stepSurvival]
    exact selection_law_ge hq (mem_sampleSpace.mp hm₀mem).1 hm₀nd hm₀thr
  · rw [cellSurvival, dif_neg hg, zero_mul]
    exact Nat.cast_nonneg _

/-! ## D5 — the compensator, and the headline -/

/-- **D5(a) — compensator identification.**  On a seed of the period with a
nondegenerate, `Y`-bounded `n`-prefix whose thresholds stay inside the band, the
abstract compensator is the pathwise sum of step survivals of
`EM/Population/LargeStepRoughness.lean`. -/
theorem compensator_eq {q Y Cc n m : ℕ} (hmem : m ∈ sampleSpace q Y)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)
    (hthr : ∀ k < n, bigThreshold q m Cc k ≤ Y) :
    TreeChernoff.compensator (typeData q Y) (cellSurvival q Y Cc) n m
      = ∑ k ∈ Finset.range n, stepSurvival q m Cc k := by
  rw [TreeChernoff.compensator]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn := Finset.mem_range.mp hk
  exact cellSurvival_eq hmem (fun j hj => hnd j (by omega)) (hthr k hkn)

/-- **(LS+) — the headline.**

*Scope, stated honestly.*  This is a **population** statement over **one full
period** of the `q`-free dynamics (`sampleSpace q Y = [1, M_Y]`): apart from an
additive **tail** term — the seeds whose first `n` `q`-free multipliers are
degenerate (`= 1`) or exceed the truncation `Y` — all but an
`exp(-(3/8)·(c₁/2)·n)` fraction of the period take at least `(c₁/8)·n` large
steps in the first `n` steps.  The tail term is **not** estimated here; that is
Group 7's job.  Nothing is claimed about the actual Euler–Mullin orbit: this is
a statement about the seed ensemble, not about a single trajectory.

The threshold hypothesis (`∀ k < n, y_k ≤ Y` on the good part of the period) is
the localization of correction C6; discharging it from the policy
`log Y ≥ n²`-type bounds via `cofactor_le_pow` is deferred.

Proof: split the bad set into its intersection with the good-prefix part and the
tail; on the good part the compensator is the pathwise sum of step survivals
(`compensator_eq`), which the deterministic core bounds below by `c₁/2·n`
(`LargeStepRoughness.pathwise_compensator`); then apply the localized tree
Chernoff bound `TreeChernoff.chernoff_quarter_local` with the filtration
`typeData`, the step event `bigStep` and the predicted survival `cellSurvival`,
whose conditional counting inequality is the selection law (`hcond_holds`).

`findings_ls_verification.md` §2.5(f) T3, §4 Group 6; C6 handled by
localization; Session 310. -/
theorem ls_plus :
    ∃ n₀ : ℕ, ∀ q Y Cc n : ℕ, q.Prime → 1 ≤ Cc → (Cc : ℝ) ≤ (n : ℝ) →
      Real.log Y ≤ (n : ℝ) ^ 2 → n₀ ≤ n →
      (∀ m ∈ sampleSpace q Y,
          (∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y) →
          ∀ k < n, bigThreshold q m Cc k ≤ Y) →
      (((sampleSpace q Y).filter (fun m =>
          ((TreeChernoff.hitCount (bigStep q Cc) n m : ℝ) < c₁ / 8 * (n : ℝ)))).card : ℝ)
        ≤ ((sampleSpace q Y).card : ℝ) * Real.exp (-(3 / 8) * (c₁ / 2 * (n : ℝ)))
          + (((sampleSpace q Y).filter (fun m =>
              ¬ (∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y))).card : ℝ) := by
  obtain ⟨n₀, hpc⟩ := pathwise_compensator
  refine ⟨n₀, fun q Y Cc n hq hCc hCcap hpol hn hthr => ?_⟩
  have hv0 : (0 : ℝ) ≤ c₁ / 2 * (n : ℝ) :=
    mul_nonneg (by linarith [c₁_pos]) (Nat.cast_nonneg _)
  -- the filtration hypotheses
  have hrefine : ∀ k, ∀ ω ∈ sampleSpace q Y, ∀ ω' ∈ sampleSpace q Y,
      typeData q Y (k + 1) ω = typeData q Y (k + 1) ω' →
      typeData q Y k ω = typeData q Y k ω' :=
    fun _ _ _ _ _ h => typeData_refine h
  have hdet : ∀ k, ∀ ω ∈ sampleSpace q Y, ∀ ω' ∈ sampleSpace q Y,
      typeData q Y (k + 1) ω = typeData q Y (k + 1) ω' →
      (bigStep q Cc k ω ↔ bigStep q Cc k ω') := by
    intro k ω _ ω' _ h
    have hk := (typeData_eq_iff.mp h).1 k (by omega)
    have hb := bigThreshold_congr (typeData_refine h) Cc
    rw [bigStep, bigStep, hk, hb]
  have hS0 : ∀ k ω, ω ∈ sampleSpace q Y →
      0 ≤ cellSurvival q Y Cc k (typeData q Y k ω) :=
    fun k _ _ => cellSurvival_nonneg hq _
  have hS1 : ∀ k ω, ω ∈ sampleSpace q Y →
      cellSurvival q Y Cc k (typeData q Y k ω) ≤ 1 :=
    fun k _ _ => cellSurvival_le_one hq _
  have hcher := TreeChernoff.chernoff_quarter_local
    (Ω := sampleSpace q Y) (F := typeData q Y) (A := bigStep q Cc)
    (S := cellSurvival q Y Cc) (v := c₁ / 2 * (n : ℝ))
    hrefine hdet hS0 hS1 (fun k b => hcond_holds hq k b) n hv0
  -- split the bad set
  have hsub : (sampleSpace q Y).filter (fun m =>
        ((TreeChernoff.hitCount (bigStep q Cc) n m : ℝ) < c₁ / 8 * (n : ℝ)))
      ⊆ ((sampleSpace q Y).filter (fun ω =>
          (TreeChernoff.hitCount (bigStep q Cc) n ω : ℝ) < c₁ / 2 * (n : ℝ) / 4
            ∧ c₁ / 2 * (n : ℝ)
              ≤ TreeChernoff.compensator (typeData q Y) (cellSurvival q Y Cc) n ω))
        ∪ ((sampleSpace q Y).filter (fun m =>
            ¬ (∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y))) := by
    intro m hm
    obtain ⟨hmΩ, hlt⟩ := Finset.mem_filter.mp hm
    by_cases hgood : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y
    · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmΩ, ?_, ?_⟩)
      · have hquart : c₁ / 2 * (n : ℝ) / 4 = c₁ / 8 * (n : ℝ) := by ring
        rw [hquart]
        exact hlt
      · rw [compensator_eq hmΩ hgood (fun k hk => hthr m hmΩ hgood k hk)]
        exact hpc q m Y Cc n hq (mem_sampleSpace.mp hmΩ).1 hCc hCcap
          (fun j hj => (hgood j hj).1) (fun j hj => (hgood j hj).2) hpol hn
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmΩ, hgood⟩)
  have hcard := Finset.card_le_card hsub
  have hcard' : (((sampleSpace q Y).filter (fun m =>
        ((TreeChernoff.hitCount (bigStep q Cc) n m : ℝ) < c₁ / 8 * (n : ℝ)))).card : ℝ)
      ≤ (((sampleSpace q Y).filter (fun ω =>
          (TreeChernoff.hitCount (bigStep q Cc) n ω : ℝ) < c₁ / 2 * (n : ℝ) / 4
            ∧ c₁ / 2 * (n : ℝ)
              ≤ TreeChernoff.compensator (typeData q Y) (cellSurvival q Y Cc) n ω)).card : ℝ)
        + (((sampleSpace q Y).filter (fun m =>
            ¬ (∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y))).card : ℝ) := by
    refine le_trans (Nat.cast_le.mpr hcard) ?_
    exact_mod_cast Finset.card_union_le _ _
  linarith [hcher, hcard']

end LSPlus

end
