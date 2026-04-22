import EM.Ensemble.FirstMoment

/-!
# Ensemble First Moment (Part B): k>=1 Infrastructure and Mod-6 Density

This file continues the ensemble first moment analysis from `FirstMoment.lean`.

## Sections

* `K1Infrastructure`     -- genSeq(n,1)=3 for n equiv 1 mod 6 squarefree, factor-3 injection
* `K2Infrastructure`     -- genSeq(n,2)=5 for n equiv 19 mod 30 squarefree (CRT)
* `PartialSMLBSection`   -- PartialSMLB (finitely many steps), mean lower bound chain
* `Mod6DensitySection`   -- Mod6DensityLB proved unconditionally, implies SMLB at k=1
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## k=1 Lower Bound Infrastructure

For odd squarefree n with n % 3 = 1 (equivalently n ≡ 1 mod 6):
- genSeq n 0 = 2 (since n is odd, n+1 is even, minFac(n+1)=2)
- genProd n 1 = n · 2 (by genProd_succ)
- genProd n 1 + 1 = 2n + 1
- 3 ∣ (2n + 1) (since n ≡ 1 mod 3 → 2n + 1 ≡ 0 mod 3)
- 2n + 1 is odd
- Therefore minFac(2n + 1) = 3, i.e., genSeq n 1 = 3.

This gives a concrete lower bound on the k=1 ensemble average:
every 1-mod-6 squarefree starting point contributes 1/3 to E[1/genSeq(·,1)].

We also prove the factor-3 injection (analogous to squarefree_half for factor 2):
the map n ↦ n/3 injects {odd sf, 3|n} into {odd sf, 3∤n}, so at most half
of odd squarefree numbers are divisible by 3.  Combining with the factor-2
injection gives #{sf} ≤ 4 · #{odd sf coprime to 3}. -/

section K1Infrastructure

/-- For odd n >= 1 with n % 3 = 1, genSeq n 1 = 3. -/
theorem genSeq_one_of_mod6 {n : Nat} (hn : 1 ≤ n) (hodd : ¬ Even n) (hmod3 : n % 3 = 1) :
    genSeq n 1 = 3 := by
  rw [genSeq_def, show genProd n 1 = n * genSeq n 0 from rfl,
    genSeq_zero_of_odd hn hodd]
  set m := n * 2 + 1
  have hm_odd : ¬ Even m := fun ⟨k, hk⟩ => by omega
  have h3_dvd : 3 ∣ m := by
    have : n = 3 * (n / 3) + 1 := by omega
    exact ⟨n / 3 * 2 + 1, by omega⟩
  have hm_ne1 : m ≠ 1 := by omega
  have hm_ge2 := (Nat.minFac_prime hm_ne1).two_le
  have hm_le3 := Nat.minFac_le_of_dvd (by omega : 2 ≤ 3) h3_dvd
  have hm_ne2 : Nat.minFac m ≠ 2 := fun h2 =>
    hm_odd (even_iff_two_dvd.mpr ((Nat.minFac_eq_two_iff m).mp h2))
  omega

/-- Dividing an odd squarefree number divisible by 3 by 3 gives an odd squarefree
    number not divisible by 3. -/
private theorem squarefree_third {m : Nat} (hm : Squarefree m) (hodd : ¬ Even m) (h3 : 3 ∣ m) :
    Squarefree (m / 3) ∧ ¬ Even (m / 3) ∧ ¬ (3 ∣ (m / 3)) := by
  obtain ⟨k, hk⟩ := h3
  have hk3 : m / 3 = k := by omega
  refine ⟨hk3 ▸ hm.squarefree_of_dvd ⟨3, by omega⟩, fun hk_even => ?_, fun h3k => ?_⟩
  · rw [hk3] at hk_even
    obtain ⟨j, hj⟩ := hk_even.two_dvd
    exact hodd ⟨3 * j, by omega⟩
  · rw [hk3] at h3k
    obtain ⟨j, hj⟩ := h3k
    exact absurd (hm 3 ⟨j, by omega⟩) (by simp)

/-- At least half of odd squarefree numbers in [1,X] are coprime to 3:
    #{odd sf in [1,X]} ≤ 2 * #{odd sf coprime to 3 in [1,X]}.
    Proof: the map n ↦ n/3 injects {odd sf, 3|n} into {odd sf, 3∤n},
    so #{odd sf, 3|n} ≤ #{odd sf, 3∤n}, hence total ≤ 2 · #{odd sf, 3∤n}. -/
private theorem odd_coprime3_sf_card_ge_half (X : Nat) :
    ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n)).card ≤
    2 * ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ ¬ (3 ∣ n))).card := by
  set oddS := (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n)
  set copS := (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ ¬ (3 ∣ n))
  set div3S := (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ (3 ∣ n))
  have h_disj : Disjoint copS div3S := by
    rw [Finset.disjoint_filter]
    intro n _ ⟨_, _, hn3⟩ ⟨_, _, h3⟩
    exact hn3 h3
  have h_union : oddS = copS ∪ div3S := by
    ext n
    simp only [oddS, copS, div3S, Finset.mem_filter, Finset.mem_union, Finset.mem_Icc]
    constructor
    · intro ⟨hmem, hsf, hodd⟩
      rcases Decidable.em (3 ∣ n) with h3 | h3
      · exact Or.inr ⟨hmem, hsf, hodd, h3⟩
      · exact Or.inl ⟨hmem, hsf, hodd, h3⟩
    · rintro (⟨hmem, hsf, hodd, _⟩ | ⟨hmem, hsf, hodd, _⟩) <;> exact ⟨hmem, hsf, hodd⟩
  have h_card : oddS.card = copS.card + div3S.card := by
    rw [h_union, Finset.card_union_of_disjoint h_disj]
  have h_inj : div3S.card ≤ copS.card := by
    apply Finset.card_le_card_of_injOn (fun n => n / 3)
    · intro n hn
      rw [Finset.mem_coe, Finset.mem_filter] at hn
      have hmem := Finset.mem_Icc.mp hn.1
      have hsf := hn.2.1
      have hodd := hn.2.2.1
      have h3 := hn.2.2.2
      obtain ⟨hsf', hodd', hcop⟩ := squarefree_third hsf hodd h3
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      have h1 : 1 ≤ n / 3 := by
        have : 3 ≤ n := Nat.le_of_dvd (by omega) h3
        omega
      have h2 : n / 3 ≤ X := le_trans (Nat.div_le_self n 3) hmem.2
      exact ⟨⟨h1, h2⟩, hsf', hodd', hcop⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      linarith [Nat.div_mul_cancel ha.2.2.2, Nat.div_mul_cancel hb.2.2.2]
  linarith [h_card, h_inj]

/-- #{sf in [1,X]} ≤ 4 · #{odd sf coprime to 3 in [1,X]}.
    Combines the factor-2 injection (odd_sf_card_ge_half: #{sf} ≤ 2·#{odd sf})
    with the factor-3 injection (odd_coprime3_sf_card_ge_half: #{odd sf} ≤ 2·#{odd sf ∧ 3∤n}). -/
private theorem sf_le_four_coprime6 (X : Nat) :
    ((Finset.Icc 1 X).filter Squarefree).card ≤
    4 * ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ ¬ (3 ∣ n))).card := by
  calc ((Finset.Icc 1 X).filter Squarefree).card
      ≤ 2 * ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n)).card :=
        odd_sf_card_ge_half X
    _ ≤ 2 * (2 * ((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧ ¬ Even n ∧ ¬ (3 ∣ n))).card) :=
        Nat.mul_le_mul_left 2 (odd_coprime3_sf_card_ge_half X)
    _ = 4 * ((Finset.Icc 1 X).filter
        (fun n => Squarefree n ∧ ¬ Even n ∧ ¬ (3 ∣ n))).card := by ring

/-- The ensemble average of 1/genSeq(n,1) is bounded below by the density of
    1-mod-6 squarefree numbers divided by 3. -/
theorem ensembleAvg_k1_ge_mod6_fraction {X : Nat} (hX : 0 < sqfreeCount X) :
    ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card /
      (3 * sqfreeCount X : ℝ) ≤
    ensembleAvg X (fun n => 1 / (genSeq n 1 : ℝ)) := by
  unfold ensembleAvg sqfreeCount
  set S := (Finset.Icc 1 X).filter Squarefree with hS_def
  set mod6S := (Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)
    with hmod6S_def
  have hS_pos : (0 : ℝ) < S.card := by exact_mod_cast hX
  have h_sub : mod6S ⊆ S := by
    intro n hn
    simp only [hmod6S_def, hS_def, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  have h_mod6_sum : ∑ n ∈ mod6S, (1 : ℝ) / (genSeq n 1 : ℝ) = mod6S.card * (1 / 3) := by
    rw [show mod6S.card * (1 / 3 : ℝ) = ∑ _ ∈ mod6S, (1 : ℝ) / 3 from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_congr rfl fun n hn => by
      simp only [hmod6S_def, Finset.mem_filter, Finset.mem_Icc] at hn
      simp [genSeq_one_of_mod6 hn.1.1 hn.2.2.1 hn.2.2.2]
  have h_sum_lower : (mod6S.card : ℝ) / 3 ≤ ∑ n ∈ S, (1 : ℝ) / (genSeq n 1 : ℝ) := by
    calc ∑ n ∈ S, (1 : ℝ) / (genSeq n 1 : ℝ)
        ≥ ∑ n ∈ mod6S, (1 : ℝ) / (genSeq n 1 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)
      _ = mod6S.card * (1 / 3) := h_mod6_sum
      _ = (mod6S.card : ℝ) / 3 := by ring
  rw [le_div_iff₀ hS_pos]
  calc (mod6S.card : ℝ) / (3 * (S.card : ℝ)) * (S.card : ℝ)
      = (mod6S.card : ℝ) / 3 := by field_simp
    _ ≤ ∑ n ∈ S, (1 : ℝ) / (genSeq n 1 : ℝ) := h_sum_lower

/-- **k=1 lower bound landscape**: witnesses the genSeq_one_of_mod6 theorem,
    the sf_le_four_coprime6 injection bound, and the conditional assembly. -/
theorem k1_lower_bound_landscape :
    -- 1. genSeq n 1 = 3 for n ≡ 1 mod 6 squarefree
    (∀ (n : Nat), 1 ≤ n → ¬ Even n → n % 3 = 1 → genSeq n 1 = 3) ∧
    -- 2. #{sf} ≤ 4 · #{odd sf coprime to 3}
    (∀ X : Nat, ((Finset.Icc 1 X).filter Squarefree).card ≤
      4 * ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ ¬ (3 ∣ n))).card) ∧
    -- 3. Conditional lower bound on E[1/genSeq(·,1)]
    (∀ X : Nat, 0 < sqfreeCount X →
      ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card /
        (3 * sqfreeCount X : ℝ) ≤
      ensembleAvg X (fun n => 1 / (genSeq n 1 : ℝ))) :=
  ⟨fun _ hn hodd hmod3 => genSeq_one_of_mod6 hn hodd hmod3,
   sf_le_four_coprime6,
   fun _ hX => ensembleAvg_k1_ge_mod6_fraction hX⟩

end K1Infrastructure

/-! ## k=2 CRT Structure

For odd squarefree n with n % 3 = 1 (equivalently n ≡ 1 mod 6):
- genSeq(n,0) = 2, genProd(n,1) = 2n
- genSeq(n,1) = 3, genProd(n,2) = 6n
- genSeq(n,2) = minFac(6n+1)

For n additionally with n % 5 = 4 (equivalently n ≡ 19 mod 30 by CRT):
- 6n+1 ≡ 0 mod 5, and 6n+1 is odd and coprime to 3
- So minFac(6n+1) = 5, i.e., genSeq(n,2) = 5 -/

section K2Infrastructure

/-- For odd n >= 1 with n % 3 = 1, genProd n 2 = 6 * n. -/
theorem genProd_two_of_mod6 {n : Nat} (hn : 1 ≤ n) (hodd : ¬ Even n)
    (hmod3 : n % 3 = 1) : genProd n 2 = 6 * n := by
  show genProd n 1 * genSeq n 1 = 6 * n
  rw [show genProd n 1 = n * genSeq n 0 from rfl,
    genSeq_zero_of_odd hn hodd, genSeq_one_of_mod6 hn hodd hmod3]
  ring

/-- For odd n >= 1 with n % 3 = 1 and n % 5 = 4, genSeq n 2 = 5. -/
theorem genSeq_two_of_mod30 {n : Nat} (hn : 1 ≤ n) (hodd : ¬ Even n)
    (hmod3 : n % 3 = 1) (hmod5 : n % 5 = 4) : genSeq n 2 = 5 := by
  rw [genSeq_def, genProd_two_of_mod6 hn hodd hmod3]
  set m := 6 * n + 1
  have hm_ne1 : m ≠ 1 := by omega
  have hm_odd : ¬ Even m := fun ⟨k, hk⟩ => by omega
  have h3_ndvd : ¬ (3 ∣ m) := fun ⟨k, hk⟩ => by omega
  have h5_dvd : 5 ∣ m := by
    have : n = 5 * (n / 5) + 4 := by omega
    exact ⟨6 * (n / 5) + 5, by omega⟩
  have hm_prime := Nat.minFac_prime hm_ne1
  have hm_ge2 := hm_prime.two_le
  have hm_le5 := Nat.minFac_le_of_dvd (by omega : 2 ≤ 5) h5_dvd
  have hm_ne2 : Nat.minFac m ≠ 2 := fun h2 =>
    hm_odd (even_iff_two_dvd.mpr ((Nat.minFac_eq_two_iff m).mp h2))
  have hm_ne3 : Nat.minFac m ≠ 3 := fun h3 =>
    h3_ndvd (h3 ▸ Nat.minFac_dvd m)
  have hm_ne4 : Nat.minFac m ≠ 4 := fun h4 => by
    rw [h4] at hm_prime; exact (by decide : ¬ Nat.Prime 4) hm_prime
  omega

/-- k=2 CRT landscape: for n ≡ 19 mod 30, the first three EM primes are 2, 3, 5. -/
theorem k2_crt_landscape :
    (∀ n : Nat, 1 ≤ n → ¬ Even n → n % 3 = 1 → genProd n 2 = 6 * n) ∧
    (∀ n : Nat, 1 ≤ n → ¬ Even n → n % 3 = 1 → n % 5 = 4 → genSeq n 2 = 5) :=
  ⟨fun _ hn hodd hmod3 => genProd_two_of_mod6 hn hodd hmod3,
   fun _ hn hodd hmod3 hmod5 => genSeq_two_of_mod30 hn hodd hmod3 hmod5⟩

end K2Infrastructure

/-! ## Partial SMLB and Fixed Density Results

PartialSMLB captures "SMLB for finitely many steps", which suffices for
a fixed positive density result (not divergence, but a concrete threshold). -/

section PartialSMLBSection

/-- **Partial SMLB**: the ensemble average of 1/genSeq(n,k) is at least c
    for each k ≤ K₀. This is weaker than SMLB (which requires ALL k). -/
def PartialSMLB (c : ℝ) (K₀ : Nat) : Prop :=
  ∀ k ≤ K₀, ∃ X₀ : Nat, ∀ X ≥ X₀,
    c ≤ ensembleAvg X (fun n => 1 / (genSeq n k : ℝ))

/-- PartialSMLB(c, K₀) implies: for X large enough, E[S_{K₀+1}(n)] ≥ c·(K₀+1).
    By linearity of ensembleAvg, the partial sum average is the sum of step averages.
    Each step average is ≥ c for X large enough. Taking the max threshold gives
    the uniform bound. -/
theorem partial_smlb_implies_mean_lower_bound {c : ℝ} {K₀ : Nat} (_hc : 0 < c)
    (hpsmlb : PartialSMLB c K₀) :
    ∃ X₀ : Nat, ∀ X ≥ X₀,
      c * (K₀ + 1) ≤ ensembleAvg X (fun n => recipPartialSum n (K₀ + 1)) := by
  have hthresh : ∀ k, k ∈ Finset.range (K₀ + 1) →
      ∃ Xk : Nat, ∀ X ≥ Xk,
        c ≤ ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) :=
    fun k hk => hpsmlb k (by rw [Finset.mem_range] at hk; omega)
  let threshold : Nat → Nat := fun k =>
    if hk : k ∈ Finset.range (K₀ + 1) then (hthresh k hk).choose else 0
  refine ⟨(Finset.range (K₀ + 1)).sup threshold, fun X hX => ?_⟩
  simp_rw [show ∀ n, recipPartialSum n (K₀ + 1) =
      ∑ k ∈ Finset.range (K₀ + 1), 1 / (genSeq n k : ℝ) from fun _ => rfl]
  rw [ensembleAvg_sum_range]
  calc c * (↑K₀ + 1) = ∑ _ ∈ Finset.range (K₀ + 1), c := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
    _ ≤ ∑ k ∈ Finset.range (K₀ + 1),
          ensembleAvg X (fun n => 1 / (genSeq n k : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have : threshold k ≤ X :=
          le_trans (Finset.le_sup (f := threshold) hk) hX
        simp only [threshold, dif_pos hk] at this
        exact (hthresh k hk).choose_spec X this

/-- PartialSMLB(1/4, 0) holds unconditionally from the k=0 step. -/
theorem partial_smlb_zero_unconditional : PartialSMLB (1 / 4) 0 := by
  intro k hk
  have : k = 0 := by omega
  subst this
  exact smlb_k0_unconditional

/-- PartialSMLB landscape: PartialSMLB(1/4, 0) unconditional + mean lower bound chain. -/
theorem partial_smlb_landscape :
    PartialSMLB (1 / 4) 0 ∧
    (∀ c : ℝ, 0 < c → ∀ K₀ : Nat, PartialSMLB c K₀ →
      ∃ X₀ : Nat, ∀ X ≥ X₀,
        c * (K₀ + 1) ≤ ensembleAvg X (fun n => recipPartialSum n (K₀ + 1))) :=
  ⟨partial_smlb_zero_unconditional,
   fun _ hc _ hpsmlb => partial_smlb_implies_mean_lower_bound hc hpsmlb⟩

end PartialSMLBSection

/-! ## Squarefree Density in 1 mod 6

The density of squarefree n ≡ 1 mod 6 among all squarefree is 1/3 asymptotically.
We state a weaker lower bound as a hypothesis and connect it to SMLB. -/

section Mod6DensitySection

/-- The density of 1-mod-6 squarefree among all squarefree is bounded below.
    Mathematically: #{n ≤ X : sf, n ≡ 1 mod 6} / #{n ≤ X : sf} → 1/3 as X → ∞.
    We only need: for large X, this ratio ≥ 1/8. -/
def Mod6DensityLB : Prop :=
  ∃ X₀ : Nat, ∀ X ≥ X₀,
    (sqfreeCount X : ℝ) / 8 ≤
    ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card

/-- sqfreeCount X ≤ X: squarefree numbers in [1,X] are a subset of [1,X]. -/
private theorem sqfreeCount_le (X : Nat) : sqfreeCount X ≤ X := by
  unfold sqfreeCount
  calc ((Finset.Icc 1 X).filter Squarefree).card
      ≤ (Finset.Icc 1 X).card := Finset.card_filter_le _ _
    _ = X := by simp [Nat.card_Icc]

/-- Multiples of 4 in [1,X] are not squarefree, giving sqfreeCount X + X/4 ≤ X. -/
private theorem sqfreeCount_le_three_quarter (X : Nat) :
    sqfreeCount X + X / 4 ≤ X := by
  unfold sqfreeCount
  -- The set of non-squarefree in [1,X] has ≥ X/4 elements (multiples of 4)
  suffices h_nonsf : X / 4 ≤ ((Finset.Icc 1 X).filter (fun n => ¬ Squarefree n)).card by
    have h_partition : ((Finset.Icc 1 X).filter Squarefree).card +
        ((Finset.Icc 1 X).filter (fun n => ¬ Squarefree n)).card =
        (Finset.Icc 1 X).card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not _ _ _),
          Finset.filter_union_filter_not_eq]
    have hcard : (Finset.Icc 1 X).card = X := by simp [Nat.card_Icc]
    omega
  -- Build injection from Finset.range (X/4) → non-squarefree in [1,X] via k ↦ 4*(k+1)
  have : (Finset.range (X / 4)).card ≤
      ((Finset.Icc 1 X).filter (fun n => ¬ Squarefree n)).card := by
    apply Finset.card_le_card_of_injOn (fun k => 4 * (k + 1))
    · intro k hk
      have hk_lt : k < X / 4 := Finset.mem_range.mp hk
      have h1 : 1 ≤ 4 * (k + 1) := by omega
      have h2 : 4 * (k + 1) ≤ X := by
        have : 4 * (X / 4) ≤ X := Nat.mul_div_le X 4
        omega
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨h1, h2⟩, fun hsf => absurd (hsf 2 ⟨k + 1, by ring⟩) (by simp)⟩
    · intro a _ b _ (hab : 4 * (a + 1) = 4 * (b + 1)); omega
  simp [Finset.card_range] at this; exact this

/-- Inclusion-exclusion: multiples of 4 and 9 give sqfreeCount X + X/4 + X/9 ≤ X + X/36 + 2.
    Since 1/4 + 1/9 - 1/36 = 1/3, this yields sqfreeCount X ≤ 2X/3 + 2 (approximately). -/
private theorem sqfreeCount_plus_fourth_ninth (X : Nat) :
    sqfreeCount X + X / 4 + X / 9 ≤ X + X / 36 + 2 := by
  unfold sqfreeCount
  -- By inclusion-exclusion: |{4|n}| + |{9|n}| - |{36|n}| ≤ |{non-sf}|
  -- The {4|n} and {9|n} sets (minus their intersection {36|n}) are subsets of non-sf.
  set S := Finset.Icc 1 X
  set nonsf := S.filter (fun n => ¬ Squarefree n)
  set A := S.filter (fun n => 4 ∣ n)
  set B := S.filter (fun n => 9 ∣ n)
  set AB := S.filter (fun n => 36 ∣ n)
  -- A ⊆ nonsf: 4|n → 2²|n → ¬Squarefree
  have hA_nonsf : A ⊆ nonsf := by
    intro n hn
    have hn_mem : n ∈ S := Finset.mem_of_mem_filter n hn
    have h4 : 4 ∣ n := (Finset.mem_filter.mp hn).2
    refine Finset.mem_filter.mpr ⟨hn_mem, fun hsf => ?_⟩
    have h22 : 2 * 2 ∣ n := h4
    exact absurd (hsf 2 h22) (by simp)
  -- B ⊆ nonsf: 9|n → 3²|n → ¬Squarefree
  have hB_nonsf : B ⊆ nonsf := by
    intro n hn
    have hn_mem : n ∈ S := Finset.mem_of_mem_filter n hn
    have h9 : 9 ∣ n := (Finset.mem_filter.mp hn).2
    refine Finset.mem_filter.mpr ⟨hn_mem, fun hsf => ?_⟩
    have h33 : 3 * 3 ∣ n := h9
    exact absurd (hsf 3 h33) (by simp)
  -- AB = A ∩ B: 36|n ↔ 4|n ∧ 9|n (since gcd(4,9)=1)
  have hAB_eq : AB = A ∩ B := by
    ext n; simp only [AB, A, B, S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_inter]
    constructor
    · intro ⟨hmem, h36⟩
      exact ⟨⟨hmem, Dvd.dvd.trans (by norm_num : (4 : ℕ) ∣ 36) h36⟩,
             ⟨hmem, Dvd.dvd.trans (by norm_num : (9 : ℕ) ∣ 36) h36⟩⟩
    · intro ⟨⟨hmem, h4⟩, ⟨_, h9⟩⟩
      exact ⟨hmem, (by decide : Nat.Coprime 4 9).mul_dvd_of_dvd_of_dvd h4 h9⟩
  -- |A ∪ B| = |A| + |B| - |A ∩ B|
  -- |A ∪ B| ≤ |nonsf|
  have hAB_sub : A ∪ B ⊆ nonsf := Finset.union_subset hA_nonsf hB_nonsf
  have hie : A.card + B.card = (A ∪ B).card + AB.card := by
    rw [hAB_eq, Finset.card_union_add_card_inter]
  have hnonsf_ge : (A ∪ B).card ≤ nonsf.card := Finset.card_le_card hAB_sub
  -- |A| ≥ X/4
  have hA_card : X / 4 ≤ A.card := by
    have : (Finset.range (X / 4)).card ≤ A.card := by
      apply Finset.card_le_card_of_injOn (fun k => 4 * (k + 1))
      · intro k hk
        have hk_lt : k < X / 4 := Finset.mem_range.mp hk
        simp only [A, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, by have := Nat.mul_div_le X 4; omega⟩, ⟨k + 1, by ring⟩⟩
      · intro a _ b _ (hab : 4 * (a + 1) = 4 * (b + 1)); omega
    simp [Finset.card_range] at this; exact this
  -- |B| ≥ X/9
  have hB_card : X / 9 ≤ B.card := by
    have : (Finset.range (X / 9)).card ≤ B.card := by
      apply Finset.card_le_card_of_injOn (fun k => 9 * (k + 1))
      · intro k hk
        have hk_lt : k < X / 9 := Finset.mem_range.mp hk
        simp only [B, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, by have := Nat.mul_div_le X 9; omega⟩, ⟨k + 1, by ring⟩⟩
      · intro a _ b _ (hab : 9 * (a + 1) = 9 * (b + 1)); omega
    simp [Finset.card_range] at this; exact this
  -- |AB| ≤ X/36 + 1
  have hAB_card : AB.card ≤ X / 36 + 1 := by
    calc AB.card ≤ (Finset.Icc 0 (X / 36)).card := by
          apply Finset.card_le_card_of_injOn (fun n => n / 36)
          · intro n hn
            simp only [AB, S, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
            exact ⟨Nat.zero_le _, Nat.div_le_div_right hn.1.2⟩
          · intro a ha b hb (hab : a / 36 = b / 36)
            simp only [AB, S, Finset.mem_coe, Finset.mem_filter] at ha hb
            have had := Nat.div_mul_cancel ha.2
            have hbd := Nat.div_mul_cancel hb.2
            nlinarith
      _ = X / 36 + 1 := by rw [← Nat.range_succ_eq_Icc_zero, Finset.card_range]
  -- Partition identity
  have h_partition : (S.filter Squarefree).card + nonsf.card = S.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not _ _ _),
        Finset.filter_union_filter_not_eq]
  have hS_card : S.card = X := by simp [S, Nat.card_Icc]
  -- sf + |A| + |B| ≤ X + |AB| via partition + inclusion-exclusion
  have : (S.filter Squarefree).card + A.card + B.card ≤ X + AB.card := by
    have h1 : A.card + B.card ≤ nonsf.card + AB.card := by linarith
    linarith
  linarith

/-- The sf + non-sf partition of {odd, n % 3 = 1} in [1,X]. -/
private theorem nonsf_one_mod_six_le_sum (X : Nat) :
    ((Finset.Icc 1 X).filter
      (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card +
    ((Finset.Icc 1 X).filter
      (fun n => ¬ Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card =
    ((Finset.Icc 1 X).filter (fun n => ¬ Even n ∧ n % 3 = 1)).card := by
  rw [← Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_filter]; intro n _ ⟨hsf, _, _⟩ ⟨hnsf, _, _⟩; exact hnsf hsf)]
  congr 1; ext n; simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro (⟨hmem, _, hodd, hmod⟩ | ⟨hmem, _, hodd, hmod⟩) <;> exact ⟨hmem, hodd, hmod⟩
  · intro ⟨hmem, hodd, hmod⟩
    rcases Decidable.em (Squarefree n) with hsf | hnsf
    · exact Or.inl ⟨hmem, hsf, hodd, hmod⟩
    · exact Or.inr ⟨hmem, hnsf, hodd, hmod⟩

/-- n ≡ 1 mod 6 ↔ n odd and n % 3 = 1 (for n ≥ 1). -/
private theorem mod6_eq_one_iff {n : Nat} (_hn : 1 ≤ n) :
    n % 6 = 1 ↔ (¬ Even n ∧ n % 3 = 1) := by
  constructor
  · exact fun h => ⟨fun ⟨k, hk⟩ => by omega, by omega⟩
  · exact fun ⟨hodd, hmod3⟩ => by
      have : n % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hodd)
      omega

/-- Count of n ≡ 1 mod 6 in [1,X] is at least X/6. -/
private theorem count_one_mod_six_ge (X : Nat) :
    X / 6 ≤ ((Finset.Icc 1 X).filter (fun n => n % 6 = 1)).card := by
  have : (Finset.range (X / 6)).card ≤
      ((Finset.Icc 1 X).filter (fun n => n % 6 = 1)).card := by
    apply Finset.card_le_card_of_injOn (fun k => 6 * k + 1)
    · intro k hk
      have hk_lt : k < X / 6 := Finset.mem_range.mp hk
      have h1 : 1 ≤ 6 * k + 1 := by omega
      have h2 : 6 * k + 1 ≤ X := by
        have : 6 * (X / 6) ≤ X := Nat.mul_div_le X 6
        omega
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨h1, h2⟩, by omega⟩
    · intro a _ b _ (hab : 6 * a + 1 = 6 * b + 1); omega
  simp [Finset.card_range] at this; exact this

/-- For n coprime to 6 and not squarefree, there exists d ≥ 5 coprime to 6 with d²|n. -/
private theorem exists_sq_factor_of_nonsf_coprime6 {n : Nat} (_hn : 1 ≤ n)
    (hnsf : ¬ Squarefree n) (hodd : ¬ Even n) (hmod3 : n % 3 = 1) :
    ∃ d : Nat, 5 ≤ d ∧ d * d ∣ n := by
  rw [Nat.squarefree_iff_prime_squarefree] at hnsf; push Not at hnsf
  obtain ⟨p, hp, hpdvd⟩ := hnsf
  refine ⟨p, ?_, hpdvd⟩
  have hp2 : p ≠ 2 := by
    intro h; subst h
    obtain ⟨m, hm⟩ := hpdvd
    exact hodd ⟨2 * m, by omega⟩
  have hp3 : p ≠ 3 := by
    intro h; subst h
    obtain ⟨m, hm⟩ := hpdvd
    have : n % 3 = 0 := by omega
    omega
  have h2le := hp.two_le
  have hp4 : p ≠ 4 := by
    intro h; subst h
    exact absurd hp (by decide)
  omega

/-- Non-squarefree n ≡ 1 mod 6 with d²|n: at most X/(d²) + 1 such n in [1,X]. -/
private theorem count_nonsf_with_sq_factor (X d : Nat) (_hd : 2 ≤ d) :
    ((Finset.Icc 1 X).filter (fun n => d * d ∣ n)).card ≤ X / (d * d) + 1 := by
  calc ((Finset.Icc 1 X).filter (fun n => d * d ∣ n)).card
      ≤ (Finset.Icc 0 (X / (d * d))).card := by
        apply Finset.card_le_card_of_injOn (fun n => n / (d * d))
        · intro n hn
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
          rw [Finset.mem_coe, Finset.mem_Icc]
          exact ⟨Nat.zero_le _, Nat.div_le_div_right hn.1.2⟩
        · intro a ha b hb hab
          rw [Finset.mem_coe, Finset.mem_filter] at ha hb
          nlinarith [Nat.div_mul_cancel ha.2, Nat.div_mul_cancel hb.2]
    _ = X / (d * d) + 1 := by rw [← Nat.range_succ_eq_Icc_zero, Finset.card_range]

/-- For d coprime to 6, d² ≡ 1 mod 6. -/
private theorem sq_mod_six_of_coprime {d : Nat} (hd2 : ¬ 2 ∣ d) (hd3 : ¬ 3 ∣ d) :
    d * d % 6 = 1 := by
  have h6 : d % 6 = 1 ∨ d % 6 = 5 := by omega
  rw [Nat.mul_mod]; rcases h6 with h | h <;> simp [h]

/-- For d coprime to 6, #{n ≡ 1 mod 6 in [1,X] : d²|n} ≤ X/(6d²) + 1.
    Key: d coprime to 6 → d² ≡ 1 mod 6, so d²|n and n ≡ 1 mod 6 → n/d² ≡ 1 mod 6.
    The map n ↦ n/d² injects into {m ≡ 1 mod 6 in [1, X/d²]}. -/
private theorem count_mod6_sq_factor (X d : Nat) (hd : 5 ≤ d) (hd2 : ¬ 2 ∣ d) (hd3 : ¬ 3 ∣ d) :
    ((Finset.Icc 1 X).filter (fun n => n % 6 = 1 ∧ d * d ∣ n)).card ≤ X / (6 * (d * d)) + 1 := by
  have hdd_pos : 0 < d * d := by positivity
  calc ((Finset.Icc 1 X).filter (fun n => n % 6 = 1 ∧ d * d ∣ n)).card
      ≤ ((Finset.range (X / (d * d) + 1)).filter (fun m => m % 6 = 1)).card := by
        apply Finset.card_le_card_of_injOn (fun n => n / (d * d))
        · intro n hn
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
          refine ⟨Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.2), ?_⟩
          have h1 : (n / (d * d) * (d * d)) % 6 = n % 6 := by
            rw [Nat.div_mul_cancel hn.2.2]
          rw [Nat.mul_mod] at h1
          simp [sq_mod_six_of_coprime hd2 hd3, hn.2.1] at h1; exact h1
        · intro a ha b hb hab
          simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
          nlinarith [Nat.div_mul_cancel ha.2.2, Nat.div_mul_cancel hb.2.2]
    _ ≤ X / (6 * (d * d)) + 1 := by
        set N := X / (d * d)
        have hcount : ((Finset.range (N + 1)).filter (fun m => m % 6 = 1)).card ≤ N / 6 + 1 := by
          have : ((Finset.range (N + 1)).filter (fun m => m % 6 = 1)).card ≤
              (Finset.range (N / 6 + 1)).card := by
            apply Finset.card_le_card_of_injOn (fun m => m / 6)
            · intro m hm
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm ⊢
              exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.lt_succ_iff.mp hm.1))
            · intro a ha b hb (hab : a / 6 = b / 6)
              simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
              have ha1 := Nat.div_add_mod a 6
              have hb1 := Nat.div_add_mod b 6
              omega
          simpa [Finset.card_range] using this
        have : N / 6 = X / (6 * (d * d)) := by
          show X / (d * d) / 6 = X / (6 * (d * d))
          rw [Nat.div_div_eq_div_mul, mul_comm]
        linarith

/-- Telescoping: ∑_{d=K}^{M} 1/d² ≤ 1/(K-1) for K ≥ 2 and M ≥ K. -/
private theorem sum_inv_sq_le_telescoping (K M : Nat) (hK : 2 ≤ K) (hKM : K ≤ M) :
    ∑ d ∈ Finset.Icc K M, (1 : ℝ) / ((d : ℝ) * d) ≤ 1 / (K - 1 : ℝ) := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) - 1 := by linarith [show (2 : ℝ) ≤ (K : ℝ) from by exact_mod_cast hK]
  calc ∑ d ∈ Finset.Icc K M, (1 : ℝ) / ((d : ℝ) * d)
      ≤ ∑ d ∈ Finset.Icc K M, (1 / ((d : ℝ) - 1) - 1 / d) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd_mem := Finset.mem_Icc.mp hd
        have hd_ge : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 2 ≤ d by omega)
        have hd_pos : (0 : ℝ) < d := by linarith
        have hd1_pos : (0 : ℝ) < (d : ℝ) - 1 := by linarith
        rw [div_sub_div _ _ (ne_of_gt hd1_pos) (ne_of_gt hd_pos)]
        rw [div_le_div_iff₀ (mul_pos hd_pos hd_pos) (mul_pos hd1_pos hd_pos)]
        have : (d : ℝ) - ((d : ℝ) - 1) = 1 := by ring
        nlinarith [mul_self_nonneg ((d : ℝ) - 1)]
    _ ≤ 1 / ((K : ℝ) - 1) := by
        -- Telescoping sum: ∑ (1/(d-1) - 1/d) = 1/(K-1) - 1/M
        have htel : ∑ d ∈ Finset.Icc K M, (1 / ((d : ℝ) - 1) - 1 / d) =
            1 / ((K : ℝ) - 1) - 1 / M := by
          induction M with
          | zero => omega
          | succ n ih =>
            by_cases hle : K ≤ n
            · rw [show Finset.Icc K (n + 1) = Finset.Icc K n ∪ {n + 1} from by
                ext x; simp [Finset.mem_Icc]; omega]
              rw [Finset.sum_union (by
                simp [Finset.disjoint_singleton_right, Finset.mem_Icc])]
              rw [Finset.sum_singleton, ih hle]
              push_cast; ring
            · push Not at hle
              have : K = n + 1 := by omega
              subst this; simp [Finset.Icc_self]
        linarith [htel, div_nonneg (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ (M:ℝ))]

/-- The non-squarefree count among n ≡ 1 mod 6 in [1,X] is ≤ X/24 + Nat.sqrt X.
    Every such n has some d ≥ 5 coprime to 6 with d²|n. By CRT (d²≡1 mod 6),
    the per-d count is X/(6d²)+1, and ∑ X/(6d²) ≤ (X/6)·(1/(K-1)) via telescoping. -/
private theorem nonsf_mod6_count_bound (X : Nat) :
    ((Finset.Icc 1 X).filter (fun n => ¬ Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card ≤
    X / 24 + Nat.sqrt X := by
  set B' := (Finset.Icc 1 X).filter (fun n => ¬ Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)
  set sqrtX := Nat.sqrt X
  set Ds := (Finset.Icc 5 sqrtX).filter (fun d => ¬ 2 ∣ d ∧ ¬ 3 ∣ d)
  have hcontain : B' ⊆ Ds.biUnion (fun d =>
      (Finset.Icc 1 X).filter (fun n => n % 6 = 1 ∧ d * d ∣ n)) := by
    intro n hn
    simp only [B', Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnX⟩, hnsf, hodd, hmod3⟩ := hn
    obtain ⟨d, hd5, hddvd⟩ := exists_sq_factor_of_nonsf_coprime6 hn1 hnsf hodd hmod3
    rw [Finset.mem_biUnion]
    have hd_le_sqrt : d ≤ sqrtX := by
      rw [Nat.le_sqrt]
      exact le_trans (Nat.le_of_dvd (by omega) hddvd) hnX
    have hd2 : ¬ 2 ∣ d := by
      intro h2d
      have h4 : 2 * 2 ∣ d * d := Nat.mul_dvd_mul h2d h2d
      exact hodd ⟨2 * (n / 4), by have := Nat.div_mul_cancel (dvd_trans h4 hddvd); omega⟩
    have hd3 : ¬ 3 ∣ d := by
      intro h3d
      have h9 : 3 * 3 ∣ d * d := Nat.mul_dvd_mul h3d h3d
      have : n % 3 = 0 := by have h9dvd := dvd_trans h9 hddvd; omega
      omega
    have hd_mem : d ∈ Ds := by
      simp only [Ds, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hd5, hd_le_sqrt⟩, hd2, hd3⟩
    have hn_mem : n ∈ (Finset.Icc 1 X).filter (fun n => n % 6 = 1 ∧ d * d ∣ n) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hn1, hnX⟩, (mod6_eq_one_iff hn1).mpr ⟨hodd, hmod3⟩, hddvd⟩
    exact ⟨d, hd_mem, hn_mem⟩
  calc B'.card
      ≤ (Ds.biUnion (fun d => (Finset.Icc 1 X).filter
          (fun n => n % 6 = 1 ∧ d * d ∣ n))).card :=
        Finset.card_le_card hcontain
    _ ≤ ∑ d ∈ Ds, ((Finset.Icc 1 X).filter (fun n => n % 6 = 1 ∧ d * d ∣ n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ d ∈ Ds, (X / (6 * (d * d)) + 1) := by
        apply Finset.sum_le_sum
        intro d hd
        simp only [Ds, Finset.mem_filter, Finset.mem_Icc] at hd
        exact count_mod6_sq_factor X d hd.1.1 hd.2.1 hd.2.2
    _ = ∑ d ∈ Ds, X / (6 * (d * d)) + ∑ _d ∈ Ds, 1 := Finset.sum_add_distrib
    _ = ∑ d ∈ Ds, X / (6 * (d * d)) + Ds.card := by simp
    _ ≤ ∑ d ∈ Ds, X / (6 * (d * d)) + sqrtX := by
        have hDs : Ds.card ≤ (Finset.Icc 5 sqrtX).card := Finset.card_filter_le _ _
        have hIcc : (Finset.Icc 5 sqrtX).card ≤ sqrtX := by
          rw [Nat.card_Icc]; omega
        omega
    _ ≤ X / 24 + sqrtX := by
        suffices h : ∑ d ∈ Ds, X / (6 * (d * d)) ≤ X / 24 by omega
        calc ∑ d ∈ Ds, X / (6 * (d * d))
            ≤ ∑ d ∈ Finset.Icc 5 sqrtX, X / (6 * (d * d)) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              intro _ _ _; exact Nat.zero_le _
          _ ≤ X / 24 := by
              have hR : (↑(∑ d ∈ Finset.Icc 5 sqrtX, X / (6 * (d * d))) : ℝ) ≤
                  (X : ℝ) / 24 := by
                calc (↑(∑ d ∈ Finset.Icc 5 sqrtX, X / (6 * (d * d))) : ℝ)
                    = ∑ d ∈ Finset.Icc 5 sqrtX, (↑(X / (6 * (d * d))) : ℝ) := by
                      push_cast; rfl
                  _ ≤ ∑ d ∈ Finset.Icc 5 sqrtX, ((X : ℝ) / (6 * ((d : ℝ) * d))) := by
                      apply Finset.sum_le_sum
                      intro d _hd
                      have : (↑(X / (6 * (d * d))) : ℝ) ≤ (X : ℝ) / ↑(6 * (d * d)) :=
                        Nat.cast_div_le
                      simp only [Nat.cast_mul] at this
                      exact this
                  _ = (X : ℝ) / 6 * ∑ d ∈ Finset.Icc 5 sqrtX, (1 / ((d : ℝ) * d)) := by
                      rw [Finset.mul_sum]; apply Finset.sum_congr rfl
                      intro d hd
                      have hd5 : 5 ≤ d := (Finset.mem_Icc.mp hd).1
                      have hd_pos : (0 : ℝ) < (d : ℝ) := by positivity
                      field_simp
                  _ ≤ (X : ℝ) / 6 * (1 / ((5 : ℝ) - 1)) := by
                      by_cases h5 : 5 ≤ sqrtX
                      · exact mul_le_mul_of_nonneg_left
                          (sum_inv_sq_le_telescoping 5 sqrtX (by omega) h5)
                          (div_nonneg (Nat.cast_nonneg' X) (by norm_num))
                      · push Not at h5
                        simp only [show Finset.Icc 5 sqrtX = ∅ from by
                          ext x; simp [Finset.mem_Icc]; omega]
                        simp; positivity
                  _ = (X : ℝ) / 24 := by ring
              rw [Nat.le_div_iff_mul_le (by omega : 0 < 24)]
              have h24 : (↑(∑ d ∈ Finset.Icc 5 sqrtX, X / (6 * (d * d))) : ℝ) * 24 ≤ (X : ℝ) := by
                linarith
              exact_mod_cast h24

/-- For X ≥ 10000, Nat.sqrt X ≤ X / 32. -/
private theorem sqrt_le_div_32 {X : Nat} (hX : 10000 ≤ X) : Nat.sqrt X ≤ X / 32 := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have h32 : 32 ≤ Nat.sqrt X := by
    calc 32 ≤ Nat.sqrt 10000 := by native_decide
      _ ≤ Nat.sqrt X := Nat.sqrt_le_sqrt hX
  have hsq : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
  nlinarith

/-- Mod6DensityLB holds unconditionally. Uses inclusion-exclusion (multiples of 4 and 9)
    for a tight sqfreeCount bound, and CRT-factor bound on non-sf 1 mod 6 count. -/
theorem mod6_density_lb_proved : Mod6DensityLB := by
  refine ⟨10000, fun X hX => ?_⟩
  set A := ((Finset.Icc 1 X).filter (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card
  set B' := ((Finset.Icc 1 X).filter (fun n => ¬ Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card
  set C := ((Finset.Icc 1 X).filter (fun n => ¬ Even n ∧ n % 3 = 1)).card
  have hpart : A + B' = C := nonsf_one_mod_six_le_sum X
  have hmod6 : ((Finset.Icc 1 X).filter (fun n => n % 6 = 1)).card = C := by
    congr 1; ext n; simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro ⟨hmem, hmod⟩; exact ⟨hmem, (mod6_eq_one_iff hmem.1).mp hmod⟩
    · intro ⟨hmem, hodd, hmod3⟩; exact ⟨hmem, (mod6_eq_one_iff hmem.1).mpr ⟨hodd, hmod3⟩⟩
  have hC_ge : X / 6 ≤ C := hmod6 ▸ count_one_mod_six_ge X
  have hB'_le : B' ≤ X / 24 + Nat.sqrt X := nonsf_mod6_count_bound X
  have hsqrt : Nat.sqrt X ≤ X / 32 := sqrt_le_div_32 hX
  have hsf_ie : sqfreeCount X + X / 4 + X / 9 ≤ X + X / 36 + 2 :=
    sqfreeCount_plus_fourth_ninth X
  have hA_R : (X : ℝ) / 6 - (X : ℝ) / 24 - (X : ℝ) / 32 - 1 ≤ (A : ℝ) := by
    have h1 : (↑(X / 6) : ℝ) ≤ (A : ℝ) + (B' : ℝ) := by
      exact_mod_cast (show X / 6 ≤ A + B' by omega)
    have h2 : (B' : ℝ) ≤ ↑(X / 24) + ↑(Nat.sqrt X) := by exact_mod_cast hB'_le
    have h3 : (↑(X / 24) : ℝ) ≤ (X : ℝ) / 24 := Nat.cast_div_le
    have h4 : (↑(Nat.sqrt X) : ℝ) ≤ (X : ℝ) / 32 := by
      exact le_trans (by exact_mod_cast hsqrt) Nat.cast_div_le
    have h5 : (X : ℝ) / 6 - 1 ≤ ↑(X / 6) := by
      have : X ≤ X / 6 * 6 + 5 := by omega
      linarith [show (↑X : ℝ) ≤ ↑(X / 6) * 6 + 5 from by exact_mod_cast this]
    linarith
  have hsf_R : (sqfreeCount X : ℝ) ≤ 2 * (X : ℝ) / 3 + 5 := by
    have h1 : (sqfreeCount X : ℝ) + ↑(X/4) + ↑(X/9) ≤ (X : ℝ) + ↑(X/36) + 2 := by
      exact_mod_cast hsf_ie
    have h2 : (X : ℝ) / 4 - 1 ≤ ↑(X / 4) := by
      linarith [show (↑X : ℝ) ≤ ↑(X / 4) * 4 + 3 from by exact_mod_cast (show X ≤ X / 4 * 4 + 3 by omega)]
    have h3 : (X : ℝ) / 9 - 1 ≤ ↑(X / 9) := by
      linarith [show (↑X : ℝ) ≤ ↑(X / 9) * 9 + 8 from by exact_mod_cast (show X ≤ X / 9 * 9 + 8 by omega)]
    linarith [show ↑(X / 36) ≤ (X : ℝ) / 36 from Nat.cast_div_le]
  rw [div_le_iff₀ (show (0:ℝ) < 8 by norm_num)]
  have hX_pos : (10000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  nlinarith

/-- Mod6DensityLB implies SMLB at k=1 with c = 1/24.
    E[1/genSeq(·,1)] ≥ #{1 mod 6 sf}/(3·#{sf}) ≥ (#{sf}/8)/(3·#{sf}) = 1/24. -/
theorem mod6_density_implies_smlb_k1 (hd : Mod6DensityLB) :
    ∃ X₀ : Nat, ∀ X ≥ X₀,
      (1 : ℝ) / 24 ≤ ensembleAvg X (fun n => 1 / (genSeq n 1 : ℝ)) := by
  obtain ⟨X₁, hX₁⟩ := hd
  refine ⟨max X₁ 1, fun X hX => ?_⟩
  have hsc_pos : 0 < sqfreeCount X := sqfreeCount_pos_of_pos (by omega)
  set mod6Card := ((Finset.Icc 1 X).filter
    (fun n => Squarefree n ∧ ¬ Even n ∧ n % 3 = 1)).card
  calc (1 : ℝ) / 24
      ≤ (mod6Card : ℝ) / (3 * sqfreeCount X) := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 24) (by positivity)]
        have : (sqfreeCount X : ℝ) / 8 ≤ (mod6Card : ℝ) := by exact_mod_cast hX₁ X (by omega)
        nlinarith
    _ ≤ ensembleAvg X (fun n => 1 / (genSeq n 1 : ℝ)) :=
        ensembleAvg_k1_ge_mod6_fraction hsc_pos

end Mod6DensitySection

end
