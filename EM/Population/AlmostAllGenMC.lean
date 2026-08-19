import EM.Population.TheoremC
import EM.Population.TailAssembly

/-!
# Almost all seeds capture `q` — the seed-average headline

This file assembles the three quantitative slices of the seed-average programme into a
single **population** statement: for a fixed prime `q` and any `ε > 0` there are a horizon
`n` and a truncation `Y` such that the seeds of `sampleSpace q Y` whose genuine greedy
orbit fails to select `q` in its first `n` steps form at most an `ε`-fraction of the
period.

## Scope — read this before quoting the result

* **Population, not orbit.**  `almost_all_genmc` is a counting statement over the seed
  ensemble `sampleSpace q Y = [1, M_Y]`, one full period of the modulus
  `SelectionLaw.modulus q Y`.  **Nothing whatsoever is claimed about the actual
  Euclid–Mullin orbit of the seed `2`**; the orbit-specificity gap (dead ends #90 and
  #117) is untouched by this file.
* **One prime at a time.**  The horizon `n` and the truncation `Y` depend on `q` (and on
  `ε`).  The simultaneous-in-`q` form — a single ensemble on which almost every seed
  captures *every* prime — remains **open**.
* **Finite horizon.**  The statement counts seeds that miss `q` in the first `n` steps of
  the `q`-free dynamics; it is a finite-horizon counting bound, with no limit taken and no
  equidistribution hypothesis anywhere.  Every input is unconditional: `TheoremC.theorem_C`
  (tree Chernoff over the selection law), `TailAssembly.tail_small` (Mertens tail of the
  degenerate/oversized prefixes) and `TailEstimate.markov_divisor_mass` (Markov on the
  window divisor mass).

## Main results

* `threshold_sq_le` — **D5c**, the policy lemma: under `n²/2 ≤ log Y` and `Cc ≤ n` the
  moving thresholds of a nondegenerate `Y`-bounded prefix satisfy `y_k² ≤ Y`, discharging
  the localization hypothesis of `TheoremC.theorem_C`.
* `policy_shifted` — the policy window is nonempty at the *shifted* horizon: some `Y` has
  `(n+1)²/2 ≤ log Y ≤ n²`.
* `uncaptured_decomposition` — the uncaptured seeds split into good seeds, degenerate
  prefixes, and heavy window divisor mass.
* `almost_all_genmc` — the headline.

Session 311, WP-A.
-/

noncomputable section
open Classical

namespace AlmostAllGenMC

open SeedCapture SeedTypes LargeStepRoughness SelectionLaw LSPlus TailEstimate TailAssembly
open TheoremC

/-! ## Part 1 — elementary real utilities -/

/-- `log x ≤ 2 √x` for `x > 0`: the crude polynomial envelope of the logarithm we use to
kill the `log n / n` tail. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hs
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  rw [h2] at h1
  linarith

/-- `(L/6)^6 ≤ exp L` for `L ≥ 0`. -/
theorem pow_six_le_exp {L : ℝ} (hL : 0 ≤ L) : (L / 6) ^ 6 ≤ Real.exp L := by
  have h1 : L / 6 ≤ Real.exp (L / 6) := by
    have := Real.add_one_le_exp (L / 6)
    linarith
  have h2 : (L / 6) ^ 6 ≤ (Real.exp (L / 6)) ^ 6 :=
    pow_le_pow_left₀ (by linarith) h1 6
  have h3 : (Real.exp (L / 6)) ^ 6 = Real.exp L := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  linarith [h2, h3.le, h3.ge]

/-! ## Part 2 — D5c: the moving thresholds stay inside the band -/

/-- **D5c — the policy lemma.**  Under the policy `n²/2 ≤ log Y`, with `Cc ≤ n` and
`n ≥ 4000`, every seed with a nondegenerate `Y`-bounded `n`-prefix has all its moving
thresholds `y_k`, `k < n`, satisfying `y_k² ≤ Y`.

*Proof.*  `TailEstimate.log_cofactor_le` gives `log₂ c_k ≤ k (log₂ Y + 1)`, so
`y_k = Cc·k·log₂ c_k ≤ n³ (log₂ Y + 1)` and `y_k² ≤ n⁶ (log₂ Y + 1)²`.  Passing to reals,
`log₂ Y ≤ 2 log Y` (as `log 2 > 1/2`) and `n² ≤ 2 log Y`, so the left side is at most
`72 L⁵` with `L = log Y`, while `Y = e^L ≥ (L/6)^6`; and `72 L⁵ ≤ L⁶/46656` once
`L ≥ 3359232`, which the policy grants at `n ≥ 4000`. -/
theorem threshold_sq_le (q Cc Y n : ℕ) (hCc : Cc ≤ n) (hn : 4000 ≤ n)
    (hpol : ((n : ℝ)) ^ 2 / 2 ≤ Real.log Y) (m : ℕ)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y) :
    ∀ k < n, (bigThreshold q m Cc k) ^ 2 ≤ Y := by
  intro k hk
  -- Nat-level bound on the threshold
  have hlogc : Nat.log 2 (seedCofactorAvoid q m k) ≤ k * (Nat.log 2 Y + 1) :=
    log_cofactor_le (fun i hi => (hnd i (lt_trans hi hk)).2)
  have hbt : bigThreshold q m Cc k ≤ n ^ 3 * (Nat.log 2 Y + 1) := by
    have h1 : Cc * k * Nat.log 2 (seedCofactorAvoid q m k)
        ≤ n * n * (k * (Nat.log 2 Y + 1)) := by
      exact Nat.mul_le_mul (Nat.mul_le_mul hCc (le_of_lt hk)) hlogc
    have h2 : n * n * (k * (Nat.log 2 Y + 1)) ≤ n ^ 3 * (Nat.log 2 Y + 1) := by
      have : k ≤ n := le_of_lt hk
      calc n * n * (k * (Nat.log 2 Y + 1)) = (n * n * k) * (Nat.log 2 Y + 1) := by ring
        _ ≤ (n * n * n) * (Nat.log 2 Y + 1) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
        _ = n ^ 3 * (Nat.log 2 Y + 1) := by ring
    exact le_trans (le_trans (le_of_eq rfl) h1) h2
  -- reals
  set L : ℝ := Real.log Y with hLdef
  have hnR : (4000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : (3359232 : ℝ) ≤ L := by nlinarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  have hY0 : Y ≠ 0 := by
    intro h
    rw [h] at hLdef
    simp at hLdef
    rw [hLdef] at hL; linarith
  have hYR : (0 : ℝ) < (Y : ℝ) := by
    have : 0 < Y := Nat.pos_of_ne_zero hY0
    exact_mod_cast this
  have hYexp : (Y : ℝ) = Real.exp L := (Real.exp_log hYR).symm
  -- log₂ Y ≤ 2 L
  have hlog2 : ((Nat.log 2 Y : ℕ) : ℝ) ≤ 2 * L := by
    have h1 : (2 : ℕ) ^ (Nat.log 2 Y) ≤ Y := Nat.pow_log_le_self 2 hY0
    have h2 : ((2 : ℝ)) ^ (Nat.log 2 Y) ≤ (Y : ℝ) := by exact_mod_cast h1
    have h3 : Real.log (((2 : ℝ)) ^ (Nat.log 2 Y)) ≤ L :=
      Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    have h4 : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 Y)]
  -- assemble in ℝ
  have hnL : ((n : ℝ)) ^ 2 ≤ 2 * L := by linarith
  have hn6 : ((n : ℝ)) ^ 6 ≤ 8 * L ^ 3 := by
    have h0 : (0 : ℝ) ≤ ((n : ℝ)) ^ 2 := sq_nonneg _
    have h1 : (((n : ℝ)) ^ 2) ^ 3 ≤ (2 * L) ^ 3 := pow_le_pow_left₀ h0 hnL 3
    calc ((n : ℝ)) ^ 6 = (((n : ℝ)) ^ 2) ^ 3 := by ring
      _ ≤ (2 * L) ^ 3 := h1
      _ = 8 * L ^ 3 := by ring
  have hbtR : ((bigThreshold q m Cc k : ℕ) : ℝ)
      ≤ ((n : ℝ)) ^ 3 * (((Nat.log 2 Y : ℕ) : ℝ) + 1) := by
    have := hbt
    have hc : ((bigThreshold q m Cc k : ℕ) : ℝ) ≤ ((n ^ 3 * (Nat.log 2 Y + 1) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at hc
    linarith
  have hbtnn : (0 : ℝ) ≤ ((bigThreshold q m Cc k : ℕ) : ℝ) := by positivity
  have hsq : ((bigThreshold q m Cc k : ℕ) : ℝ) ^ 2
      ≤ (((n : ℝ)) ^ 3 * (((Nat.log 2 Y : ℕ) : ℝ) + 1)) ^ 2 := by
    have hrhs : (0 : ℝ) ≤ ((n : ℝ)) ^ 3 * (((Nat.log 2 Y : ℕ) : ℝ) + 1) := by positivity
    nlinarith
  have hmid : (((n : ℝ)) ^ 3 * (((Nat.log 2 Y : ℕ) : ℝ) + 1)) ^ 2 ≤ 72 * L ^ 5 := by
    have hnn : (0 : ℝ) ≤ ((Nat.log 2 Y : ℕ) : ℝ) := by positivity
    have hbound : (((Nat.log 2 Y : ℕ) : ℝ) + 1) ^ 2 ≤ 9 * L ^ 2 := by nlinarith
    have hexpand : (((n : ℝ)) ^ 3 * (((Nat.log 2 Y : ℕ) : ℝ) + 1)) ^ 2
        = ((n : ℝ)) ^ 6 * (((Nat.log 2 Y : ℕ) : ℝ) + 1) ^ 2 := by ring
    rw [hexpand]
    have h1 : ((n : ℝ)) ^ 6 * (((Nat.log 2 Y : ℕ) : ℝ) + 1) ^ 2
        ≤ (8 * L ^ 3) * (9 * L ^ 2) := by
      have hA : (0 : ℝ) ≤ ((n : ℝ)) ^ 6 := by positivity
      have hB : (0 : ℝ) ≤ (((Nat.log 2 Y : ℕ) : ℝ) + 1) ^ 2 := by positivity
      have hC : (0 : ℝ) ≤ 8 * L ^ 3 := by positivity
      nlinarith
    nlinarith
  have hfin : 72 * L ^ 5 ≤ (Y : ℝ) := by
    have h1 : (L / 6) ^ 6 ≤ Real.exp L := pow_six_le_exp hL0
    rw [hYexp]
    have h2 : 72 * L ^ 5 ≤ (L / 6) ^ 6 := by nlinarith [pow_nonneg hL0 5]
    linarith
  have : ((bigThreshold q m Cc k : ℕ) : ℝ) ^ 2 ≤ (Y : ℝ) := by linarith
  have hnat : ((bigThreshold q m Cc k ^ 2 : ℕ) : ℝ) ≤ ((Y : ℕ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast hnat

/-! ## Part 3 — the policy window at the shifted horizon -/

/-- **The policy window is nonempty at the shifted horizon.**  For `n ≥ 4` there is a
truncation `Y` with `(n+1)²/2 ≤ log Y ≤ n²`: enough for `TailAssembly.tail_small` at
horizon `n + 1` *and* for `TheoremC.theorem_C` at horizon `n`. -/
theorem policy_shifted (n : ℕ) (hn : 4 ≤ n) : ∃ Y : ℕ,
    (((n : ℝ)) + 1) ^ 2 / 2 ≤ Real.log Y ∧ Real.log Y ≤ ((n : ℝ)) ^ 2 := by
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set t : ℝ := Real.exp ((((n : ℝ)) + 1) ^ 2 / 2) with ht
  set B : ℝ := Real.exp (((n : ℝ)) ^ 2 - 1) with hB
  have hstep1 : t ≤ B := by
    rw [ht, hB]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hB1 : (1 : ℝ) ≤ B := by
    rw [hB]; exact Real.one_le_exp (by nlinarith)
  have hBe : Real.exp (((n : ℝ)) ^ 2) = B * Real.exp 1 := by
    rw [hB, ← Real.exp_add]; ring_nf
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have hstep : t ≤ Real.exp (((n : ℝ)) ^ 2) - 1 := by
    rw [hBe]; nlinarith
  refine ⟨⌊Real.exp (((n : ℝ)) ^ 2)⌋₊, ?_, ?_⟩
  · have hfl : Real.exp (((n : ℝ)) ^ 2) - 1 < (⌊Real.exp (((n : ℝ)) ^ 2)⌋₊ : ℝ) :=
      Nat.sub_one_lt_floor _
    have hle : t ≤ (⌊Real.exp (((n : ℝ)) ^ 2)⌋₊ : ℝ) := by linarith
    have htpos : (0 : ℝ) < t := Real.exp_pos _
    have hlog : Real.log t ≤ Real.log (⌊Real.exp (((n : ℝ)) ^ 2)⌋₊ : ℝ) :=
      Real.log_le_log htpos hle
    rwa [ht, Real.log_exp] at hlog
  · have hle : ((⌊Real.exp (((n : ℝ)) ^ 2)⌋₊ : ℕ) : ℝ) ≤ Real.exp (((n : ℝ)) ^ 2) :=
      Nat.floor_le (le_of_lt (Real.exp_pos _))
    have hpos : (0 : ℝ) < ((⌊Real.exp (((n : ℝ)) ^ 2)⌋₊ : ℕ) : ℝ) := by
      have hfl : Real.exp (((n : ℝ)) ^ 2) - 1 < (⌊Real.exp (((n : ℝ)) ^ 2)⌋₊ : ℝ) :=
        Nat.sub_one_lt_floor _
      have htpos : (0 : ℝ) < t := Real.exp_pos _
      linarith
    have hlog := Real.log_le_log hpos hle
    rwa [Real.log_exp] at hlog

/-! ## Part 4 — the three-way decomposition of the uncaptured seeds -/

/-- **The uncaptured seeds decompose.**  A seed of the period that is coprime to `q` and
whose genuine orbit misses `q` before depth `n` is either a *good seed* in the sense of
`TheoremC.GoodSeed`, or has a degenerate/oversized `(n+1)`-prefix, or carries a window
divisor mass `≥ 1/Cc` in `(Cc², Y]`. -/
theorem uncaptured_decomposition (q Y Cc n : ℕ) :
    (sampleSpace q Y).filter (fun m => ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q)
      ⊆ ((sampleSpace q Y).filter (fun m => GoodSeed q Y Cc n m)
          ∪ (sampleSpace q Y).filter (fun m =>
              ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)))
        ∪ (sampleSpace q Y).filter (fun m =>
            (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
              (1 : ℝ) / r) := by
  intro m hm
  rw [Finset.mem_filter] at hm
  obtain ⟨hmem, hdvd, hcap⟩ := hm
  by_cases hnd : ∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y
  · by_cases hmass : (∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
        (1 : ℝ) / r) ≤ 1 / Cc
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hmem, hdvd, hcap, hnd, hmass⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hmem, le_of_lt (not_le.mp hmass)⟩)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨hmem, hnd⟩))

/-! ## Part 5 — the headline -/

/-- **Almost all seeds capture `q`.**

*Scope (honest, and load-bearing).*  This is a **population** theorem over the seed
ensemble `sampleSpace q Y = [1, M_Y]`, one full period of `SelectionLaw.modulus q Y`, at a
truncation `Y` chosen by the policy window.  It says: for a **fixed** prime `q` and any
`ε > 0` there are a horizon `n` and a truncation `Y` such that at most an `ε`-fraction of
the seeds are simultaneously coprime to `q` and *uncaptured* — their genuine greedy orbit
`genSeq m ·` does not select `q` in its first `n` steps.

What is **not** claimed:

* nothing about the actual Euclid–Mullin orbit of the seed `2` — the orbit-specificity
  barrier (dead ends #90, #117) is untouched;
* nothing simultaneous in `q`: `n` and `Y` depend on `q` and `ε`, and the uniform-in-`q`
  form remains open;
* nothing asymptotic: this is finite-horizon counting, with no equidistribution hypothesis
  anywhere in the chain.

*Proof.*  Split the uncaptured seeds by `uncaptured_decomposition`.  The good seeds are
exponentially rare by `TheoremC.theorem_C`, whose localization hypothesis is discharged by
`threshold_sq_le`; the degenerate prefixes are `O(log n / n)` rare by
`TailAssembly.tail_small` at horizon `n + 1`; the heavy divisor masses are `1/Cc` rare by
`TailEstimate.markov_divisor_mass`.  Choosing `Cc ≥ 3/ε` and `n` large in three explicit
ways makes each piece at most `ε/3`. -/
theorem almost_all_genmc (q : ℕ) (hq : q.Prime) :
    ∀ ε : ℝ, 0 < ε → ∃ n Y : ℕ,
      (((sampleSpace q Y).filter (fun m => ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q)).card : ℝ)
        ≤ ε * ((sampleSpace q Y).card : ℝ) := by
  intro ε hε
  classical
  -- the exclusion-window constant
  set Cc : ℕ := max (48 * q) ⌈3 / ε⌉₊ with hCcdef
  have hCc48 : 48 * q ≤ Cc := le_max_left _ _
  have hq2 := hq.two_le
  have hCc1 : 1 ≤ Cc := by omega
  have hCcR : (0 : ℝ) < (Cc : ℝ) := by exact_mod_cast hCc1
  have hCceps : (1 : ℝ) / Cc ≤ ε / 3 := by
    have h1 : (3 : ℝ) / ε ≤ (Cc : ℝ) := by
      have h2 : (⌈3 / ε⌉₊ : ℝ) ≤ (Cc : ℝ) := by
        exact_mod_cast le_max_right (48 * q) ⌈3 / ε⌉₊
      exact le_trans (Nat.le_ceil _) h2
    have h2 : (1 : ℝ) / (Cc : ℝ) ≤ 1 / ((3 : ℝ) / ε) :=
      one_div_le_one_div_of_le (by positivity) h1
    rwa [one_div_div] at h2
  -- Theorem C constants
  obtain ⟨κ, hκpos, K₀, n₁, hC⟩ := theorem_C q Cc hq hCc48
  obtain ⟨n₀, htail⟩ := tail_small
  -- the exponential threshold
  set A : ℝ := 3 / 8 * (κ * (c₁ / 2)) with hA
  set Bc : ℝ := 3 / 8 * (κ * (K₀ : ℝ)) with hBc
  have hApos : 0 < A := by
    rw [hA]; have := c₁_pos; positivity
  set E₁ : ℝ := (Real.log (3 / ε) + Bc) / A with hE₁
  set E₂ : ℝ := (6 * Real.exp 25 / ε) ^ 2 with hE₂
  set n : ℕ := n₁ + Cc + 4000 + n₀ + ⌈E₁⌉₊ + ⌈E₂⌉₊ with hn
  have hn₁ : n₁ ≤ n := by omega
  have hnCc : Cc ≤ n := by omega
  have hn4000 : 4000 ≤ n := by omega
  have hn₀ : n₀ ≤ n + 1 := by omega
  have hE₁n : E₁ ≤ (n : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast (by omega : ⌈E₁⌉₊ ≤ n)
  have hE₂n : E₂ ≤ (n : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast (by omega : ⌈E₂⌉₊ ≤ n)
  have hnR4 : (4000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4000
  have hCcRn : (Cc : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnCc
  -- the policy witness
  obtain ⟨Y, hlow, hhigh⟩ := policy_shifted n (by omega)
  refine ⟨n, Y, ?_⟩
  have hlown : ((n : ℝ)) ^ 2 / 2 ≤ Real.log Y := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  -- ### piece 1 : good seeds
  have hthr2 : ∀ m ∈ sampleSpace q Y, GoodSeed q Y Cc n m →
      ∀ k < n, (bigThreshold q m Cc k) ^ 2 ≤ Y := by
    intro m _ hgood
    exact threshold_sq_le q Cc Y n hnCc hn4000 hlown m
      (fun j hj => hgood.2.2.1 j (by omega))
  have hgoodcount := hC Y n hn₁ hCcRn hhigh hthr2
  have hexp : Real.exp (-(3 / 8) * (κ * (c₁ / 2 * (n : ℝ) - (K₀ : ℝ)))) ≤ ε / 3 := by
    have hkey : Real.log (3 / ε) ≤ A * (n : ℝ) - Bc := by
      rw [hE₁, div_le_iff₀ hApos] at hE₁n
      linarith
    have hstep : -(3 / 8) * (κ * (c₁ / 2 * (n : ℝ) - (K₀ : ℝ))) ≤ -Real.log (3 / ε) := by
      have : A * (n : ℝ) - Bc = 3 / 8 * (κ * (c₁ / 2 * (n : ℝ) - (K₀ : ℝ))) := by
        rw [hA, hBc]; ring
      linarith [hkey, this]
    have h2 : Real.exp (-(3 / 8) * (κ * (c₁ / 2 * (n : ℝ) - (K₀ : ℝ))))
        ≤ Real.exp (-Real.log (3 / ε)) := Real.exp_le_exp.mpr hstep
    have h3 : Real.exp (-Real.log (3 / ε)) = ε / 3 := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    linarith [h2, h3.le, h3.ge]
  have hcard0 : (0 : ℝ) ≤ ((sampleSpace q Y).card : ℝ) := by positivity
  have hpiece1 : (((sampleSpace q Y).filter (fun m => GoodSeed q Y Cc n m)).card : ℝ)
      ≤ ε / 3 * ((sampleSpace q Y).card : ℝ) := by
    refine le_trans hgoodcount ?_
    have := mul_le_mul_of_nonneg_left hexp hcard0
    linarith [this]
  -- ### piece 2 : degenerate prefixes
  have hlowshift : (((n + 1 : ℕ) : ℝ)) ^ 2 / 2 ≤ Real.log Y := by push_cast; linarith
  have hhighshift : Real.log Y ≤ (((n + 1 : ℕ) : ℝ)) ^ 3 := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have htailcount := htail q Y (n + 1) hq hn₀ hlowshift hhighshift
  have hlogsmall : Real.exp 25 * Real.log ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ)) : ℝ) ≤ ε / 3 := by
    set x : ℝ := ((n + 1 : ℕ) : ℝ) with hx
    have hxpos : (0 : ℝ) < x := by
      rw [hx]; exact_mod_cast Nat.succ_pos n
    set s : ℝ := Real.sqrt x with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hxpos
    have hsq : s ^ 2 = x := Real.sq_sqrt hxpos.le
    have hlogx : Real.log x ≤ 2 * s := log_le_two_sqrt hxpos
    have hslarge : 6 * Real.exp 25 / ε ≤ s := by
      have hE₂x : E₂ ≤ x := by rw [hx]; push_cast; linarith
      have hnn : (0 : ℝ) ≤ 6 * Real.exp 25 / ε := by positivity
      have := Real.sqrt_le_sqrt hE₂x
      rw [hE₂, Real.sqrt_sq hnn] at this
      exact this
    have he25 : (0 : ℝ) < Real.exp 25 := Real.exp_pos _
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hkey : Real.exp 25 * Real.log x / x ≤ 2 * Real.exp 25 / s := by
      rw [div_le_iff₀ hxpos]
      have h1 : Real.exp 25 * Real.log x ≤ Real.exp 25 * (2 * s) :=
        mul_le_mul_of_nonneg_left hlogx he25.le
      have h2 : 2 * Real.exp 25 / s * x = 2 * Real.exp 25 * s := by
        rw [← hsq]; field_simp
      linarith [h1, h2.le, h2.ge]
    have hfin : 2 * Real.exp 25 / s ≤ ε / 3 := by
      rw [div_le_iff₀ hspos]
      have h1 : 6 * Real.exp 25 ≤ s * ε := by
        rw [div_le_iff₀ hε] at hslarge
        linarith
      nlinarith [h1]
    linarith
  have hpiece2 : (((sampleSpace q Y).filter (fun m =>
      ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y))).card : ℝ)
      ≤ ε / 3 * ((sampleSpace q Y).card : ℝ) := by
    refine le_trans htailcount ?_
    exact mul_le_mul_of_nonneg_right hlogsmall hcard0
  -- ### piece 3 : heavy window divisor mass
  have hmk := markov_divisor_mass (Cc ^ 2) Y (modulus q Y) (Nat.one_le_pow _ _ hCc1)
    (show (0:ℝ) < 1 / Cc by positivity)
  have hfilterEq : ∀ m : ℕ,
      ((Finset.Ioc (Cc ^ 2) Y).filter Nat.Prime).filter (fun r => r ∣ m)
        = (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m) := by
    intro m; rw [Finset.filter_filter]
  have hpiece3 : (((sampleSpace q Y).filter (fun m =>
      (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
        (1 : ℝ) / r)).card : ℝ) ≤ ε / 3 * ((sampleSpace q Y).card : ℝ) := by
    have hrw : ((sampleSpace q Y).filter (fun m =>
        (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
          (1 : ℝ) / r))
        = (Finset.Ico 1 (modulus q Y + 1)).filter (fun m =>
          (1 : ℝ) / Cc ≤ ∑ r ∈ ((Finset.Ioc (Cc ^ 2) Y).filter Nat.Prime).filter
            (fun r => r ∣ m), (1 : ℝ) / r) := by
      simp only [sampleSpace, hfilterEq]
    rw [hrw]
    refine le_trans hmk ?_
    have hden : ((Cc : ℝ) ^ 2) * ((1 : ℝ) / Cc) = (Cc : ℝ) := by field_simp
    have hcast : ((Cc ^ 2 : ℕ) : ℝ) = ((Cc : ℝ)) ^ 2 := by push_cast; ring
    rw [hcast, hden]
    have hcardeq : ((sampleSpace q Y).card : ℝ) = ((modulus q Y : ℕ) : ℝ) := by
      rw [card_sampleSpace]
    rw [hcardeq]
    have hM0 : (0 : ℝ) ≤ ((modulus q Y : ℕ) : ℝ) := by positivity
    have : ((modulus q Y : ℕ) : ℝ) / (Cc : ℝ) = (1 / (Cc : ℝ)) * ((modulus q Y : ℕ) : ℝ) := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hCceps hM0
  -- ### assembly
  have hsub := uncaptured_decomposition q Y Cc n
  calc (((sampleSpace q Y).filter (fun m => ¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q)).card : ℝ)
      ≤ ((((sampleSpace q Y).filter (fun m => GoodSeed q Y Cc n m)
            ∪ (sampleSpace q Y).filter (fun m =>
                ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)))
          ∪ (sampleSpace q Y).filter (fun m =>
              (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter
                (fun r => r.Prime ∧ r ∣ m), (1 : ℝ) / r)).card : ℝ) := by
        exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ε * ((sampleSpace q Y).card : ℝ) := by
        have h1 := Finset.card_union_le
          ((sampleSpace q Y).filter (fun m => GoodSeed q Y Cc n m)
            ∪ (sampleSpace q Y).filter (fun m =>
              ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)))
          ((sampleSpace q Y).filter (fun m =>
              (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter
                (fun r => r.Prime ∧ r ∣ m), (1 : ℝ) / r))
        have h2 := Finset.card_union_le
          ((sampleSpace q Y).filter (fun m => GoodSeed q Y Cc n m))
          ((sampleSpace q Y).filter (fun m =>
              ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)))
        have hc1 : (((((sampleSpace q Y).filter (fun m => GoodSeed q Y Cc n m)
            ∪ (sampleSpace q Y).filter (fun m =>
              ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)))
          ∪ (sampleSpace q Y).filter (fun m =>
              (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter
                (fun r => r.Prime ∧ r ∣ m), (1 : ℝ) / r)).card : ℕ) : ℝ)
            ≤ ((((sampleSpace q Y).filter (fun m => GoodSeed q Y Cc n m)).card : ℕ) : ℝ)
              + ((((sampleSpace q Y).filter (fun m =>
                  ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j
                    ∧ genSeqAvoid q m j ≤ Y))).card : ℕ) : ℝ)
              + ((((sampleSpace q Y).filter (fun m =>
                  (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter
                    (fun r => r.Prime ∧ r ∣ m), (1 : ℝ) / r)).card : ℕ) : ℝ) := by
          have := Nat.le_trans h1 (Nat.add_le_add_right h2 _)
          exact_mod_cast this
        linarith [hpiece1, hpiece2, hpiece3, hc1]

end AlmostAllGenMC

end
