import Mathlib

/-!
# An abstract finite-tree Chernoff bound

This file is the *abstract probabilistic layer* of the (LS) formalization plan
(`agents/state/findings_ls_verification.md` §2.5(e) C5-replacement, §4 Group 6; Session 310).
It replaces the appeal to Freedman's inequality by a completely elementary
**finite-tree exponential supermartingale** argument: everything below is finite
counting over a `Finset`, with no measure theory whatsoever.

## Setting

* `Ω : Finset α` is the finite sample space (a level of the tree, say).
* `F : ℕ → α → β` assigns to each `ω` its *type at depth `k`*.  The hypotheses
  `Hrefine`/`Hdet` say that the types form a filtration: `F (k+1)` refines `F k`,
  and the step event `A k` is measurable with respect to `F (k+1)`.
* `A : ℕ → α → Prop` is the step ("success") event at depth `k`.
* `S : ℕ → β → ℝ` is the *predicted conditional survival probability*, and
  `Hcond` is the conditional counting inequality
  `S k b * |fiber| ≤ |fiber ∩ A k|`.

The two observables are

* `hitCount A n ω` — the number of successes among the first `n` steps (`N`), and
* `compensator F S n ω` — the sum of predicted survivals (`V`).

## Main results

* `exp_mul_one_sub_le_one` (T1) — the numeric one-step inequality `exp x * (1 - x) ≤ 1`.
* `exp_supermartingale` (T2) — `∑_{ω ∈ Ω} exp (-lam * N + θ * V) ≤ |Ω|`, where
  `θ = 1 - exp (-lam)`.  This is the core; the proof is a forward induction on `n`,
  partitioning `Ω` into the fibers of `F n`.
* `chernoff_bound` (T3) — the Markov/Chernoff consequence.
* `chernoff_quarter` (T4) — the clean specialization `lam = 1`, `K = v/4`,
  giving the decay `exp (-(3/8) v)`.
* `chernoff_bound_of_dominating` / `chernoff_quarter_of_dominating` (T5) — the
  robustness corollary: enlarging the step event only enlarges the hit count, so
  the same right-hand side controls the dominating process.
-/

set_option linter.unusedSectionVars false

namespace TreeChernoff

open Finset

/-! ## T1 — the numeric one-step lemma -/

/-- **T1 (raw form).**  For every real `x`, `exp x * (1 - x) ≤ 1`.

This is the elementary inequality driving the exponential supermartingale;
see `findings_ls_verification.md` §2.5(e) C5-replacement, §4 Group 6; Session 310. -/
theorem exp_mul_one_sub_le_one (x : ℝ) : Real.exp x * (1 - x) ≤ 1 := by
  have h1 : 1 - x ≤ Real.exp (-x) := by
    have h := Real.add_one_le_exp (-x)
    linarith
  have h2 : (0 : ℝ) < Real.exp x := Real.exp_pos x
  calc Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) :=
        mul_le_mul_of_nonneg_left h1 h2.le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The exponential tilt parameter `θ = 1 - e^{-lam}`. -/
noncomputable def theta (lam : ℝ) : ℝ := 1 - Real.exp (-lam)

theorem theta_nonneg {lam : ℝ} (h : 0 ≤ lam) : 0 ≤ theta lam := by
  have hx : Real.exp (-lam) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  simp only [theta]
  linarith

theorem theta_le_one (lam : ℝ) : theta lam ≤ 1 := by
  have := Real.exp_pos (-lam)
  simp only [theta]
  linarith

theorem exp_neg_eq_one_sub_theta (lam : ℝ) : Real.exp (-lam) = 1 - theta lam := by
  simp [theta]

/-- **T1 (the form used below).**  For `0 ≤ lam` and `0 ≤ s ≤ 1`, writing
`θ = 1 - exp (-lam)`, we have `exp (θ * s) * (1 - θ * s) ≤ 1`.

`findings_ls_verification.md` §2.5(e) C5-replacement, §4 Group 6; Session 310. -/
theorem exp_theta_mul_one_sub_le_one (lam s : ℝ) :
    Real.exp (theta lam * s) * (1 - theta lam * s) ≤ 1 :=
  exp_mul_one_sub_le_one _

/-! ## The two observables -/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The number of successes among the first `n` steps. -/
def hitCount (A : ℕ → α → Prop) [∀ k, DecidablePred (A k)] (n : ℕ) (ω : α) : ℕ :=
  ((Finset.range n).filter (fun k => A k ω)).card

/-- The compensator: the sum of the predicted conditional survivals. -/
noncomputable def compensator (F : ℕ → α → β) (S : ℕ → β → ℝ) (n : ℕ) (ω : α) : ℝ :=
  ∑ k ∈ Finset.range n, S k (F k ω)

/-- The exponential weight `exp (-lam * N + θ * V)`. -/
noncomputable def weight (F : ℕ → α → β) (A : ℕ → α → Prop) [∀ k, DecidablePred (A k)]
    (S : ℕ → β → ℝ) (lam : ℝ) (n : ℕ) (ω : α) : ℝ :=
  Real.exp (-lam * (hitCount A n ω : ℝ) + theta lam * compensator F S n ω)

theorem weight_pos (F : ℕ → α → β) (A : ℕ → α → Prop) [∀ k, DecidablePred (A k)]
    (S : ℕ → β → ℝ) (lam : ℝ) (n : ℕ) (ω : α) : 0 < weight F A S lam n ω :=
  Real.exp_pos _

section Basic

variable (A : ℕ → α → Prop) [∀ k, DecidablePred (A k)]

@[simp] theorem hitCount_zero (ω : α) : hitCount A 0 ω = 0 := by
  simp [hitCount]

theorem hitCount_succ (n : ℕ) (ω : α) :
    hitCount A (n + 1) ω = hitCount A n ω + (if A n ω then 1 else 0) := by
  classical
  simp only [hitCount, Finset.range_add_one, Finset.filter_insert]
  by_cases h : A n ω
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h, Nat.add_zero]

theorem hitCount_succ_cast (n : ℕ) (ω : α) :
    ((hitCount A (n + 1) ω : ℕ) : ℝ)
      = (hitCount A n ω : ℝ) + (if A n ω then (1 : ℝ) else 0) := by
  rw [hitCount_succ]
  by_cases h : A n ω <;> simp [h]

end Basic

@[simp] theorem compensator_zero (F : ℕ → α → β) (S : ℕ → β → ℝ) (ω : α) :
    compensator F S 0 ω = 0 := by
  simp [compensator]

theorem compensator_succ (F : ℕ → α → β) (S : ℕ → β → ℝ) (n : ℕ) (ω : α) :
    compensator F S (n + 1) ω = compensator F S n ω + S n (F n ω) := by
  simp [compensator, Finset.sum_range_succ]

/-! ## Filtration helpers -/

section Filtration

variable {Ω : Finset α} {F : ℕ → α → β} {A : ℕ → α → Prop} [∀ k, DecidablePred (A k)]
  {S : ℕ → β → ℝ}

/-- Iterated refinement, in the `j + d` form convenient for induction. -/
theorem F_eq_of_add
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    {ω ω' : α} (hω : ω ∈ Ω) (hω' : ω' ∈ Ω) :
    ∀ (d j : ℕ), F (j + d) ω = F (j + d) ω' → F j ω = F j ω' := by
  intro d
  induction d with
  | zero => intro j h; simpa using h
  | succ d ih =>
      intro j h
      refine ih j (hrefine (j + d) ω hω ω' hω' ?_)
      have hj : j + d + 1 = j + (d + 1) := by omega
      rw [hj]
      exact h

/-- The filtration refines: the type at depth `k` determines the type at every earlier depth. -/
theorem F_eq_of_le
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    {ω ω' : α} (hω : ω ∈ Ω) (hω' : ω' ∈ Ω) {j k : ℕ} (hjk : j ≤ k)
    (h : F k ω = F k ω') : F j ω = F j ω' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  exact F_eq_of_add hrefine hω hω' d j h

/-- The type at depth `k` determines every earlier step event. -/
theorem A_iff_of_lt
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    (hdet : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → (A k ω ↔ A k ω'))
    {ω ω' : α} (hω : ω ∈ Ω) (hω' : ω' ∈ Ω) {j k : ℕ} (hjk : j < k)
    (h : F k ω = F k ω') : (A j ω ↔ A j ω') :=
  hdet j ω hω ω' hω' (F_eq_of_le hrefine hω hω' hjk h)

/-- The hit count up to depth `n` is a function of the type at depth `n`. -/
theorem hitCount_congr
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    (hdet : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → (A k ω ↔ A k ω'))
    {ω ω' : α} (hω : ω ∈ Ω) (hω' : ω' ∈ Ω) {n : ℕ} (h : F n ω = F n ω') :
    hitCount A n ω = hitCount A n ω' := by
  simp only [hitCount]
  congr 1
  refine Finset.filter_congr ?_
  intro k hk
  exact A_iff_of_lt hrefine hdet hω hω' (Finset.mem_range.mp hk) h

/-- The compensator up to depth `n` is a function of the type at depth `n`. -/
theorem compensator_congr
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    {ω ω' : α} (hω : ω ∈ Ω) (hω' : ω' ∈ Ω) {n : ℕ} (h : F n ω = F n ω') :
    compensator F S n ω = compensator F S n ω' := by
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [F_eq_of_le hrefine hω hω' (le_of_lt (Finset.mem_range.mp hk)) h]

/-- The exponential weight at depth `n` is a function of the type at depth `n`. -/
theorem weight_congr
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    (hdet : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → (A k ω ↔ A k ω'))
    {ω ω' : α} (hω : ω ∈ Ω) (hω' : ω' ∈ Ω) {n : ℕ} (lam : ℝ) (h : F n ω = F n ω') :
    weight F A S lam n ω = weight F A S lam n ω' := by
  simp only [weight, hitCount_congr hrefine hdet hω hω' h,
    compensator_congr hrefine hω hω' h]

end Filtration

/-! ## T2 — the exponential supermartingale bound -/

section Supermartingale

variable {Ω : Finset α} {F : ℕ → α → β} {A : ℕ → α → Prop} [∀ k, DecidablePred (A k)]
  {S : ℕ → β → ℝ} {lam : ℝ}

/-- The one-fiber estimate: on the fiber `{ω ∈ Ω | F n ω = b}` the depth-`(n+1)` weights
sum to at most the sum of the depth-`n` weights. -/
private theorem fiber_step
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    (hdet : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → (A k ω ↔ A k ω'))
    (hS0 : ∀ k ω, ω ∈ Ω → 0 ≤ S k (F k ω))
    (hS1 : ∀ k ω, ω ∈ Ω → S k (F k ω) ≤ 1)
    (hcond : ∀ (k : ℕ) (b : β),
      S k b * ((Ω.filter (fun ω => F k ω = b)).card : ℝ)
        ≤ ((Ω.filter (fun ω => F k ω = b ∧ A k ω)).card : ℝ))
    (hlam : 0 ≤ lam) (n : ℕ) {b : β} (hb : b ∈ Ω.image (F n)) :
    ∑ ω ∈ Ω.filter (fun ω => F n ω = b), weight F A S lam (n + 1) ω
      ≤ ∑ ω ∈ Ω.filter (fun ω => F n ω = b), weight F A S lam n ω := by
  classical
  obtain ⟨ω₀, hω₀Ω, hω₀b⟩ := Finset.mem_image.mp hb
  set fib : Finset α := Ω.filter (fun ω => F n ω = b) with hfib
  set c : ℝ := weight F A S lam n ω₀ with hc
  set s : ℝ := S n b with hs
  have hθ : 0 ≤ theta lam := theta_nonneg hlam
  have hs0 : 0 ≤ s := by rw [hs, ← hω₀b]; exact hS0 n ω₀ hω₀Ω
  have hs1 : s ≤ 1 := by rw [hs, ← hω₀b]; exact hS1 n ω₀ hω₀Ω
  have hc0 : 0 ≤ c := (weight_pos F A S lam n ω₀).le
  -- the weight is constant on the fiber
  have hWn : ∀ ω ∈ fib, weight F A S lam n ω = c := by
    intro ω hω
    rw [hfib, Finset.mem_filter] at hω
    exact weight_congr hrefine hdet hω.1 hω₀Ω lam (by rw [hω.2, hω₀b])
  -- the depth-(n+1) weight factorizes on the fiber
  have hWs : ∀ ω ∈ fib, weight F A S lam (n + 1) ω
      = c * Real.exp (theta lam * s) * Real.exp (-lam * (if A n ω then (1 : ℝ) else 0)) := by
    intro ω hω
    have hω' := hω
    rw [hfib, Finset.mem_filter] at hω'
    have hFb : F n ω = b := hω'.2
    have hcnst : Real.exp (-lam * (hitCount A n ω : ℝ) + theta lam * compensator F S n ω) = c :=
      hWn ω hω
    simp only [weight, hitCount_succ_cast, compensator_succ, hFb]
    rw [show -lam * ((hitCount A n ω : ℝ) + (if A n ω then (1 : ℝ) else 0))
          + theta lam * (compensator F S n ω + s)
        = (-lam * (hitCount A n ω : ℝ) + theta lam * compensator F S n ω)
          + theta lam * s + (-lam * (if A n ω then (1 : ℝ) else 0)) from by ring]
    rw [Real.exp_add, Real.exp_add, hcnst]
  -- the indicator sum over the fiber
  have hmfilter : fib.filter (fun ω => A n ω) = Ω.filter (fun ω => F n ω = b ∧ A n ω) := by
    rw [hfib, Finset.filter_filter]
  have hsplit : (fib.filter (fun ω => A n ω)).card
      + (fib.filter (fun ω => ¬ A n ω)).card = fib.card :=
    Finset.card_filter_add_card_filter_not (s := fib) (fun ω => A n ω)
  have hsplitR : ((fib.filter (fun ω => ¬ A n ω)).card : ℝ)
      = (fib.card : ℝ) - ((fib.filter (fun ω => A n ω)).card : ℝ) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hsplit
    push_cast at h
    linarith
  have hind : ∑ ω ∈ fib, Real.exp (-lam * (if A n ω then (1 : ℝ) else 0))
      = (fib.card : ℝ) - theta lam * ((fib.filter (fun ω => A n ω)).card : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not fib (fun ω => A n ω)]
    have e1 : ∀ ω ∈ fib.filter (fun ω => A n ω),
        Real.exp (-lam * (if A n ω then (1 : ℝ) else 0)) = Real.exp (-lam) := by
      intro ω hω
      rw [if_pos (Finset.mem_filter.mp hω).2, mul_one]
    have e2 : ∀ ω ∈ fib.filter (fun ω => ¬ A n ω),
        Real.exp (-lam * (if A n ω then (1 : ℝ) else 0)) = 1 := by
      intro ω hω
      rw [if_neg (Finset.mem_filter.mp hω).2, mul_zero, Real.exp_zero]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, mul_one, exp_neg_eq_one_sub_theta, hsplitR]
    ring
  -- the conditional counting inequality on this fiber
  have hcondb : s * (fib.card : ℝ) ≤ ((fib.filter (fun ω => A n ω)).card : ℝ) := by
    rw [hmfilter, hs, hfib]
    exact hcond n b
  -- assemble
  have hsum1 : ∑ ω ∈ fib, weight F A S lam (n + 1) ω
      = c * Real.exp (theta lam * s)
        * ((fib.card : ℝ) - theta lam * ((fib.filter (fun ω => A n ω)).card : ℝ)) := by
    rw [Finset.sum_congr rfl hWs, ← Finset.mul_sum, hind]
  have hsum2 : ∑ ω ∈ fib, weight F A S lam n ω = c * (fib.card : ℝ) := by
    rw [Finset.sum_congr rfl hWn, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsum1, hsum2]
  have hcardnn : (0 : ℝ) ≤ (fib.card : ℝ) := Nat.cast_nonneg _
  have hstep1 : (fib.card : ℝ) - theta lam * ((fib.filter (fun ω => A n ω)).card : ℝ)
      ≤ (fib.card : ℝ) * (1 - theta lam * s) := by
    have := mul_le_mul_of_nonneg_left hcondb hθ
    nlinarith [this]
  have hfac0 : (0 : ℝ) ≤ c * Real.exp (theta lam * s) :=
    mul_nonneg hc0 (Real.exp_pos _).le
  calc c * Real.exp (theta lam * s)
        * ((fib.card : ℝ) - theta lam * ((fib.filter (fun ω => A n ω)).card : ℝ))
      ≤ c * Real.exp (theta lam * s) * ((fib.card : ℝ) * (1 - theta lam * s)) :=
        mul_le_mul_of_nonneg_left hstep1 hfac0
    _ = (c * (fib.card : ℝ)) * (Real.exp (theta lam * s) * (1 - theta lam * s)) := by ring
    _ ≤ (c * (fib.card : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left (exp_theta_mul_one_sub_le_one lam s)
          (mul_nonneg hc0 hcardnn)
    _ = c * (fib.card : ℝ) := by ring

/-- **T2 (weight form).**  The exponential supermartingale bound. -/
theorem sum_weight_le
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    (hdet : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → (A k ω ↔ A k ω'))
    (hS0 : ∀ k ω, ω ∈ Ω → 0 ≤ S k (F k ω))
    (hS1 : ∀ k ω, ω ∈ Ω → S k (F k ω) ≤ 1)
    (hcond : ∀ (k : ℕ) (b : β),
      S k b * ((Ω.filter (fun ω => F k ω = b)).card : ℝ)
        ≤ ((Ω.filter (fun ω => F k ω = b ∧ A k ω)).card : ℝ))
    (hlam : 0 ≤ lam) (n : ℕ) :
    ∑ ω ∈ Ω, weight F A S lam n ω ≤ (Ω.card : ℝ) := by
  classical
  induction n with
  | zero =>
      have : ∀ ω ∈ Ω, weight F A S lam 0 ω = 1 := by
        intro ω _
        simp [weight]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
  | succ n ih =>
      have hmaps : ∀ ω ∈ Ω, F n ω ∈ Ω.image (F n) := fun ω hω =>
        Finset.mem_image_of_mem _ hω
      calc ∑ ω ∈ Ω, weight F A S lam (n + 1) ω
          = ∑ b ∈ Ω.image (F n), ∑ ω ∈ Ω.filter (fun ω => F n ω = b),
              weight F A S lam (n + 1) ω :=
            (Finset.sum_fiberwise_of_maps_to hmaps _).symm
        _ ≤ ∑ b ∈ Ω.image (F n), ∑ ω ∈ Ω.filter (fun ω => F n ω = b),
              weight F A S lam n ω :=
            Finset.sum_le_sum (fun b hb =>
              fiber_step hrefine hdet hS0 hS1 hcond hlam n hb)
        _ = ∑ ω ∈ Ω, weight F A S lam n ω :=
            Finset.sum_fiberwise_of_maps_to hmaps _
        _ ≤ (Ω.card : ℝ) := ih

/-- **T2.**  The finite-tree exponential supermartingale bound: with
`θ = 1 - exp (-lam)` and `lam ≥ 0`, under the filtration hypotheses `hrefine`, `hdet`,
the range hypotheses `hS0`, `hS1`, and the conditional counting inequality `hcond`,
```
∑_{ω ∈ Ω} exp (-lam * hitCount n ω + θ * compensator n ω) ≤ |Ω|.
```
The proof is a forward induction on `n`, partitioning `Ω` into the fibers of `F n`;
on each fiber the depth-`n` weight is constant, the indicator sum is
`|fiber| - θ · |fiber ∩ A n|`, and `hcond` plus `T1` close the step.

`findings_ls_verification.md` §2.5(e) C5-replacement, §4 Group 6; Session 310. -/
theorem exp_supermartingale
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    (hdet : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → (A k ω ↔ A k ω'))
    (hS0 : ∀ k ω, ω ∈ Ω → 0 ≤ S k (F k ω))
    (hS1 : ∀ k ω, ω ∈ Ω → S k (F k ω) ≤ 1)
    (hcond : ∀ (k : ℕ) (b : β),
      S k b * ((Ω.filter (fun ω => F k ω = b)).card : ℝ)
        ≤ ((Ω.filter (fun ω => F k ω = b ∧ A k ω)).card : ℝ))
    (hlam : 0 ≤ lam) (n : ℕ) :
    ∑ ω ∈ Ω, Real.exp (-lam * (hitCount A n ω : ℝ) + theta lam * compensator F S n ω)
      ≤ (Ω.card : ℝ) :=
  sum_weight_le hrefine hdet hS0 hS1 hcond hlam n

end Supermartingale

/-! ## T3 — Chernoff via Markov -/

section Chernoff

variable {Ω : Finset α} {F : ℕ → α → β} {A : ℕ → α → Prop} [∀ k, DecidablePred (A k)]
  {S : ℕ → β → ℝ} {lam v K : ℝ}

/-- **T3.**  Chernoff bound: if the compensator is surely at least `v` on `Ω`, then the
number of `ω ∈ Ω` whose hit count is below `K` is at most `|Ω| · exp (lam·K - θ·v)`.

`findings_ls_verification.md` §2.5(e) C5-replacement, §4 Group 6; Session 310. -/
theorem chernoff_bound
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    (hdet : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → (A k ω ↔ A k ω'))
    (hS0 : ∀ k ω, ω ∈ Ω → 0 ≤ S k (F k ω))
    (hS1 : ∀ k ω, ω ∈ Ω → S k (F k ω) ≤ 1)
    (hcond : ∀ (k : ℕ) (b : β),
      S k b * ((Ω.filter (fun ω => F k ω = b)).card : ℝ)
        ≤ ((Ω.filter (fun ω => F k ω = b ∧ A k ω)).card : ℝ))
    (hlam : 0 ≤ lam) (n : ℕ)
    (hv : ∀ ω ∈ Ω, v ≤ compensator F S n ω) :
    ((Ω.filter (fun ω => (hitCount A n ω : ℝ) < K)).card : ℝ)
      ≤ (Ω.card : ℝ) * Real.exp (lam * K - theta lam * v) := by
  classical
  set θ : ℝ := theta lam with hθdef
  have hθ : 0 ≤ θ := theta_nonneg hlam
  set G : Finset α := Ω.filter (fun ω => (hitCount A n ω : ℝ) < K) with hG
  set E : ℝ := Real.exp (-lam * K + θ * v) with hE
  have hEpos : 0 < E := Real.exp_pos _
  -- on `G` the weight is at least `E`
  have hlower : ∀ ω ∈ G, E ≤ weight F A S lam n ω := by
    intro ω hω
    rw [hG, Finset.mem_filter] at hω
    have h1 : -lam * K ≤ -lam * (hitCount A n ω : ℝ) := by
      nlinarith [hω.2, hlam]
    have h2 : θ * v ≤ θ * compensator F S n ω :=
      mul_le_mul_of_nonneg_left (hv ω hω.1) hθ
    exact Real.exp_le_exp.mpr (by linarith)
  have hGsub : G ⊆ Ω := Finset.filter_subset _ _
  have hkey : (G.card : ℝ) * E ≤ (Ω.card : ℝ) := by
    calc (G.card : ℝ) * E = ∑ _ω ∈ G, E := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ω ∈ G, weight F A S lam n ω := Finset.sum_le_sum hlower
      _ ≤ ∑ ω ∈ Ω, weight F A S lam n ω :=
          Finset.sum_le_sum_of_subset_of_nonneg hGsub
            (fun ω _ _ => (weight_pos F A S lam n ω).le)
      _ ≤ (Ω.card : ℝ) := sum_weight_le hrefine hdet hS0 hS1 hcond hlam n
  have hEinv : Real.exp (lam * K - θ * v) = E⁻¹ := by
    rw [hE, ← Real.exp_neg]
    congr 1
    ring
  rw [hEinv]
  rw [le_mul_inv_iff₀ hEpos]
  exact hkey

/-- **T4.**  The clean specialization `lam = 1`, `K = v/4`: if the compensator is surely
at least `v ≥ 0`, then at most a fraction `exp (-(3/8)·v)` of `Ω` has hit count below `v/4`.

`findings_ls_verification.md` §2.5(e) C5-replacement, §4 Group 6; Session 310. -/
theorem chernoff_quarter
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    (hdet : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → (A k ω ↔ A k ω'))
    (hS0 : ∀ k ω, ω ∈ Ω → 0 ≤ S k (F k ω))
    (hS1 : ∀ k ω, ω ∈ Ω → S k (F k ω) ≤ 1)
    (hcond : ∀ (k : ℕ) (b : β),
      S k b * ((Ω.filter (fun ω => F k ω = b)).card : ℝ)
        ≤ ((Ω.filter (fun ω => F k ω = b ∧ A k ω)).card : ℝ))
    (n : ℕ) (hv : ∀ ω ∈ Ω, v ≤ compensator F S n ω) (hv0 : 0 ≤ v) :
    ((Ω.filter (fun ω => (hitCount A n ω : ℝ) < v / 4)).card : ℝ)
      ≤ (Ω.card : ℝ) * Real.exp (-(3 / 8) * v) := by
  have hbase :=
    chernoff_bound (lam := 1) (K := v / 4) (v := v) hrefine hdet hS0 hS1 hcond zero_le_one n hv
  refine hbase.trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
  have hθ : (5 : ℝ) / 8 ≤ theta 1 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : (8 : ℝ) / 3 < Real.exp 1 := by norm_num at h1 ⊢; linarith
    have hmul : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (-1) < 3 / 8 := by
      nlinarith [Real.exp_pos (-1), h2, hmul]
    simp only [theta]
    linarith
  nlinarith [hθ, hv0]

/-! ## T5 — robustness under enlarging the step event -/

/-- Enlarging the step event only enlarges the hit count. -/
theorem hitCount_mono {A A' : ℕ → α → Prop} [∀ k, DecidablePred (A k)]
    [∀ k, DecidablePred (A' k)] {Ω : Finset α}
    (h : ∀ k ω, ω ∈ Ω → A k ω → A' k ω) {ω : α} (hω : ω ∈ Ω) (n : ℕ) :
    hitCount A n ω ≤ hitCount A' n ω := by
  refine Finset.card_le_card ?_
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  exact ⟨hk.1, h k ω hω hk.2⟩

/-- **T5.**  Robustness (correction C6 hygiene): if `A'` dominates `A` on `Ω`, then the
`T3` conclusion for `A` transfers verbatim to `A'` with the *same* right-hand side.
The concrete instantiation uses `A := large step AND not yet truncated` and
`A' := large step`.

`findings_ls_verification.md` §2.5(e) C5-replacement, §4 Group 6; Session 310. -/
theorem chernoff_bound_of_dominating {A' : ℕ → α → Prop} [∀ k, DecidablePred (A' k)]
    (hdom : ∀ k ω, ω ∈ Ω → A k ω → A' k ω)
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    (hdet : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → (A k ω ↔ A k ω'))
    (hS0 : ∀ k ω, ω ∈ Ω → 0 ≤ S k (F k ω))
    (hS1 : ∀ k ω, ω ∈ Ω → S k (F k ω) ≤ 1)
    (hcond : ∀ (k : ℕ) (b : β),
      S k b * ((Ω.filter (fun ω => F k ω = b)).card : ℝ)
        ≤ ((Ω.filter (fun ω => F k ω = b ∧ A k ω)).card : ℝ))
    (hlam : 0 ≤ lam) (n : ℕ)
    (hv : ∀ ω ∈ Ω, v ≤ compensator F S n ω) :
    ((Ω.filter (fun ω => (hitCount A' n ω : ℝ) < K)).card : ℝ)
      ≤ (Ω.card : ℝ) * Real.exp (lam * K - theta lam * v) := by
  classical
  refine le_trans ?_ (chernoff_bound hrefine hdet hS0 hS1 hcond hlam n hv (K := K))
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro ω hω
  simp only [Finset.mem_filter] at hω ⊢
  refine ⟨hω.1, lt_of_le_of_lt ?_ hω.2⟩
  exact_mod_cast hitCount_mono hdom hω.1 n

/-- **T5 (quarter form).**  The `T4` conclusion for `A` transfers to any dominating `A'`. -/
theorem chernoff_quarter_of_dominating {A' : ℕ → α → Prop} [∀ k, DecidablePred (A' k)]
    (hdom : ∀ k ω, ω ∈ Ω → A k ω → A' k ω)
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    (hdet : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → (A k ω ↔ A k ω'))
    (hS0 : ∀ k ω, ω ∈ Ω → 0 ≤ S k (F k ω))
    (hS1 : ∀ k ω, ω ∈ Ω → S k (F k ω) ≤ 1)
    (hcond : ∀ (k : ℕ) (b : β),
      S k b * ((Ω.filter (fun ω => F k ω = b)).card : ℝ)
        ≤ ((Ω.filter (fun ω => F k ω = b ∧ A k ω)).card : ℝ))
    (n : ℕ) (hv : ∀ ω ∈ Ω, v ≤ compensator F S n ω) (hv0 : 0 ≤ v) :
    ((Ω.filter (fun ω => (hitCount A' n ω : ℝ) < v / 4)).card : ℝ)
      ≤ (Ω.card : ℝ) * Real.exp (-(3 / 8) * v) := by
  classical
  refine le_trans ?_ (chernoff_quarter hrefine hdet hS0 hS1 hcond n hv hv0)
  refine Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro ω hω
  simp only [Finset.mem_filter] at hω ⊢
  refine ⟨hω.1, lt_of_le_of_lt ?_ hω.2⟩
  exact_mod_cast hitCount_mono hdom hω.1 n

/-! ## T6 — the *localized* Chernoff bound

Correction C6 of `findings_ls_verification.md` §2.5(f) asks for a truncation of
the process at the first time the compensator misbehaves.  Rather than stopping
the process — which would force a stopped-filtration bookkeeping layer — we
*localize*: the bad event is intersected with the compensator event
`{v ≤ V_n}`.  The Markov step is completely insensitive to this: on the
intersection the exponential weight is bounded below exactly as before, and the
supermartingale bound `sum_weight_le` is unchanged (it never sees the bad set).

The downstream user then only has to exhibit the compensator lower bound on the
*part of the sample space it cares about*, leaving the complement as an additive
cardinality term. -/

/-- **T6.**  The localized Chernoff bound.  Same as `chernoff_bound`, but the
sure compensator hypothesis `hv` is replaced by intersecting the bad event with
the compensator event `{v ≤ V_n}`.

`findings_ls_verification.md` §2.5(f) T3, correction C6 handled by localization;
Session 310. -/
theorem chernoff_bound_local
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    (hdet : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → (A k ω ↔ A k ω'))
    (hS0 : ∀ k ω, ω ∈ Ω → 0 ≤ S k (F k ω))
    (hS1 : ∀ k ω, ω ∈ Ω → S k (F k ω) ≤ 1)
    (hcond : ∀ (k : ℕ) (b : β),
      S k b * ((Ω.filter (fun ω => F k ω = b)).card : ℝ)
        ≤ ((Ω.filter (fun ω => F k ω = b ∧ A k ω)).card : ℝ))
    (hlam : 0 ≤ lam) (n : ℕ) :
    ((Ω.filter (fun ω =>
        (hitCount A n ω : ℝ) < K ∧ v ≤ compensator F S n ω)).card : ℝ)
      ≤ (Ω.card : ℝ) * Real.exp (lam * K - theta lam * v) := by
  classical
  set θ : ℝ := theta lam with hθdef
  have hθ : 0 ≤ θ := theta_nonneg hlam
  set G : Finset α :=
    Ω.filter (fun ω => (hitCount A n ω : ℝ) < K ∧ v ≤ compensator F S n ω) with hG
  set E : ℝ := Real.exp (-lam * K + θ * v) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hlower : ∀ ω ∈ G, E ≤ weight F A S lam n ω := by
    intro ω hω
    rw [hG, Finset.mem_filter] at hω
    have h1 : -lam * K ≤ -lam * (hitCount A n ω : ℝ) := by
      nlinarith [hω.2.1, hlam]
    have h2 : θ * v ≤ θ * compensator F S n ω :=
      mul_le_mul_of_nonneg_left hω.2.2 hθ
    exact Real.exp_le_exp.mpr (by linarith)
  have hGsub : G ⊆ Ω := Finset.filter_subset _ _
  have hkey : (G.card : ℝ) * E ≤ (Ω.card : ℝ) := by
    calc (G.card : ℝ) * E = ∑ _ω ∈ G, E := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ω ∈ G, weight F A S lam n ω := Finset.sum_le_sum hlower
      _ ≤ ∑ ω ∈ Ω, weight F A S lam n ω :=
          Finset.sum_le_sum_of_subset_of_nonneg hGsub
            (fun ω _ _ => (weight_pos F A S lam n ω).le)
      _ ≤ (Ω.card : ℝ) := sum_weight_le hrefine hdet hS0 hS1 hcond hlam n
  have hEinv : Real.exp (lam * K - θ * v) = E⁻¹ := by
    rw [hE, ← Real.exp_neg]
    congr 1
    ring
  rw [hEinv, le_mul_inv_iff₀ hEpos]
  exact hkey

/-- **T6 (quarter form).**  The localized version of `chernoff_quarter`: at most
a fraction `exp (-(3/8)·v)` of `Ω` has hit count below `v/4` *and* compensator at
least `v ≥ 0`.

`findings_ls_verification.md` §2.5(f) T3, correction C6 handled by localization;
Session 310. -/
theorem chernoff_quarter_local
    (hrefine : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → F k ω = F k ω')
    (hdet : ∀ k, ∀ ω ∈ Ω, ∀ ω' ∈ Ω, F (k + 1) ω = F (k + 1) ω' → (A k ω ↔ A k ω'))
    (hS0 : ∀ k ω, ω ∈ Ω → 0 ≤ S k (F k ω))
    (hS1 : ∀ k ω, ω ∈ Ω → S k (F k ω) ≤ 1)
    (hcond : ∀ (k : ℕ) (b : β),
      S k b * ((Ω.filter (fun ω => F k ω = b)).card : ℝ)
        ≤ ((Ω.filter (fun ω => F k ω = b ∧ A k ω)).card : ℝ))
    (n : ℕ) (hv0 : 0 ≤ v) :
    ((Ω.filter (fun ω =>
        (hitCount A n ω : ℝ) < v / 4 ∧ v ≤ compensator F S n ω)).card : ℝ)
      ≤ (Ω.card : ℝ) * Real.exp (-(3 / 8) * v) := by
  have hbase :=
    chernoff_bound_local (lam := 1) (K := v / 4) (v := v) hrefine hdet hS0 hS1 hcond
      zero_le_one n
  refine hbase.trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Nat.cast_nonneg _)
  have hθ : (5 : ℝ) / 8 ≤ theta 1 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : (8 : ℝ) / 3 < Real.exp 1 := by norm_num at h1 ⊢; linarith
    have hmul : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (-1) < 3 / 8 := by
      nlinarith [Real.exp_pos (-1), h2, hmul]
    simp only [theta]
    linarith
  nlinarith [hθ, hv0]

end Chernoff

end TreeChernoff
