import EM.LargeSieve
import EM.LargeSieveSpectral
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Weak Mullin, Reciprocal Divergence, and Confined Energy

## Main Results

### S87. Missing Primes and Weak Mullin
* `mc_implies_wm` : MC → WM (PROVED)
* `wm_implies_rd` : WM → RD (PROVED) — key theorem
* `mc_implies_rd` : MC → RD (PROVED)

### S88. Product Divergence
* `safe_fraction_exp_bound` : product-exp inequality (PROVED)
* `product_divergence` : thick missing set ⇒ large products (PROVED)

### S89. EMBV and Confined Energy
* `embv_implies_mc` : EMBV → MC (PROVED, conditional on Q₀ ≤ 11)
* `jointSVE_implies_mmcsb` : JointSVE → MMCSB (PROVED)
* `per_prime_confined_energy_lb` : confined energy ≥ N²/(q-2) (PROVED)
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## S87. Missing Primes and Weak Mullin -/

section MissingPrimesAndWeakMullin

/-- **Missing Primes**: primes that never appear in the EM sequence. -/
def MissingPrimes : Set Nat :=
  {p : Nat | Nat.Prime p ∧ ∀ k, seq k ≠ p}

/-- **Weak Mullin**: reciprocal sum over missing primes converges. -/
def WeakMullin : Prop :=
  Summable (Set.indicator MissingPrimes (fun n : Nat => (1 : ℝ) / n))

/-- **Reciprocal Divergence**: ∑_k 1/seq(k) diverges. -/
def ReciprocalDivergence : Prop :=
  ¬ Summable (fun k : Nat => (1 : ℝ) / seq k)

/-- **MissingFinite**: only finitely many primes are missing. -/
def MissingFinite : Prop := Set.Finite MissingPrimes

open Classical in
/-- MC implies MissingPrimes = ∅. -/
theorem mc_implies_missing_empty (hmc : MullinConjecture) : MissingPrimes = ∅ := by
  ext p
  simp only [MissingPrimes, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp; push_neg
  exact hmc p ((isPrime_iff_natPrime p).mpr hp)

/-- MC implies MissingFinite. -/
theorem mc_implies_missing_finite (hmc : MullinConjecture) : MissingFinite := by
  rw [MissingFinite, mc_implies_missing_empty hmc]; exact Set.finite_empty

/-- MC implies WeakMullin. -/
theorem mc_implies_wm (hmc : MullinConjecture) : WeakMullin := by
  unfold WeakMullin; rw [mc_implies_missing_empty hmc, Set.indicator_empty]
  exact summable_zero

/-- MissingFinite implies WeakMullin. -/
theorem missing_finite_implies_wm (hfin : MissingFinite) : WeakMullin := by
  rw [WeakMullin]
  apply summable_of_ne_finset_zero (s := hfin.toFinset)
  intro n hn
  exact Set.indicator_of_notMem (fun h => hn (hfin.mem_toFinset.mpr h)) _

/-! ### Partition of primes -/

private def AppearedPrimes : Set Nat := Set.range seq

private theorem seq_injective' : Function.Injective seq :=
  fun _ _ h => seq_injective _ _ h

open Classical in
private theorem primes_eq_appeared_union_missing :
    {p : Nat | Nat.Prime p} = AppearedPrimes ∪ MissingPrimes := by
  ext p
  simp only [Set.mem_setOf_eq, AppearedPrimes, Set.mem_union, Set.mem_range,
    MissingPrimes, Set.mem_setOf_eq]
  constructor
  · intro hp
    by_cases h : ∃ k, seq k = p
    · left; exact h
    · right; push_neg at h; exact ⟨hp, h⟩
  · rintro (⟨k, hk⟩ | ⟨hp, _⟩)
    · rw [← hk]; exact (isPrime_iff_natPrime _).mp (seq_isPrime k)
    · exact hp

private theorem appeared_missing_disjoint :
    Disjoint AppearedPrimes MissingPrimes := by
  rw [Set.disjoint_iff]
  rintro p ⟨⟨k, hk⟩, _, hne⟩; exact hne k hk

private theorem summable_indicator_appeared_of_summable_seq
    (h : Summable (fun k : Nat => (1 : ℝ) / seq k)) :
    Summable (Set.indicator AppearedPrimes (fun n : Nat => (1 : ℝ) / n)) := by
  show Summable (Set.indicator (Set.range seq) (fun n : Nat => (1 : ℝ) / n))
  rw [← Function.Injective.summable_iff seq_injective'
    (fun n hn => Set.indicator_of_notMem hn _)]
  exact h.congr (fun k => by
    simp only [Function.comp, Set.indicator_of_mem (Set.mem_range_self k)])

open Classical in
/-- **WM → RD**: partition {primes} = appeared ∪ missing. If both indicator
    sums converged, the indicator on all primes would converge, contradicting
    the divergence of ∑ 1/p. -/
theorem wm_implies_rd : WeakMullin → ReciprocalDivergence := by
  intro hwm hseq
  apply not_summable_one_div_on_primes
  rw [primes_eq_appeared_union_missing,
    Set.indicator_union_of_disjoint appeared_missing_disjoint]
  exact (summable_indicator_appeared_of_summable_seq hseq).add hwm

/-- MC → RD. -/
theorem mc_implies_rd (hmc : MullinConjecture) : ReciprocalDivergence :=
  wm_implies_rd (mc_implies_wm hmc)

end MissingPrimesAndWeakMullin

/-! ## S88. Product Divergence -/

section ProductDivergence

open Real Finset

/-- 1 - 1/x ≤ exp(-1/x) for x ≥ 1. -/
theorem one_sub_inv_le_exp_neg {x : ℝ} (_hx : 1 ≤ x) :
    1 - 1 / x ≤ exp (-(1 / x)) := by
  have := add_one_le_exp (-(1 / x))
  linarith

private theorem factor_le_exp {q : ℝ} (hq : 2 ≤ q) :
    (q - 2) / (q - 1) ≤ exp (-(1 / (q - 1))) := by
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  rw [show q - 2 = (q - 1) - 1 from by ring, sub_div, div_self (ne_of_gt hq1)]
  exact one_sub_inv_le_exp_neg (by linarith)

/-- ∏_{q ∈ Q} (q-2)/(q-1) ≤ exp(-∑_{q ∈ Q} 1/(q-1)) for all q ≥ 2. -/
theorem safe_fraction_exp_bound {Q : Finset ℝ} (hQ : ∀ q ∈ Q, 2 ≤ q) :
    ∏ q ∈ Q, ((q - 2) / (q - 1)) ≤ exp (- ∑ q ∈ Q, 1 / (q - 1)) := by
  have h_neg : - ∑ q ∈ Q, 1 / (q - 1) = ∑ q ∈ Q, -(1 / (q - 1)) := by
    rw [← Finset.sum_neg_distrib]
  rw [h_neg, Real.exp_sum]
  exact Finset.prod_le_prod
    (fun q hq => by
      have hq1 : (0 : ℝ) < q - 1 := by linarith [hQ q hq]
      have hq2 : (0 : ℝ) ≤ q - 2 := by linarith [hQ q hq]
      exact div_nonneg hq2 (le_of_lt hq1))
    (fun q hq => factor_le_exp (hQ q hq))

/-- 1/(q-1) ≥ 1/(2q) for q ≥ 2. -/
theorem reciprocal_q_minus_one_lb {q : ℝ} (hq : 2 ≤ q) :
    1 / (2 * q) ≤ 1 / (q - 1) := by
  have hq1 : (0 : ℝ) < q - 1 := by linarith
  have hq2 : (0 : ℝ) < 2 * q := by linarith
  rw [div_le_div_iff₀ hq2 hq1]; nlinarith

/-- For Q ⊆ {q | q ≥ 3} with ∑ 1/q ≥ C: ∏(q-1)/(q-2) ≥ exp(C/2). -/
theorem product_divergence {Q : Finset ℝ} {C : ℝ}
    (hQ : ∀ q ∈ Q, (3 : ℝ) ≤ q)
    (hsum : C ≤ ∑ q ∈ Q, 1 / q) :
    exp (C / 2) ≤ ∏ q ∈ Q, ((q - 1) / (q - 2)) := by
  -- Step 1: ∑ 1/(q-1) ≥ C/2
  have h_lb : C / 2 ≤ ∑ q ∈ Q, 1 / (q - 1) := by
    calc C / 2 ≤ (∑ q ∈ Q, 1 / q) / 2 := by linarith
      _ = ∑ q ∈ Q, 1 / (2 * q) := by rw [Finset.sum_div]; congr 1; ext q; ring
      _ ≤ ∑ q ∈ Q, 1 / (q - 1) :=
          Finset.sum_le_sum fun q hq => reciprocal_q_minus_one_lb (by linarith [hQ q hq])
  -- Step 2: safe_fraction bound
  have h_safe := safe_fraction_exp_bound (fun q hq => by linarith [hQ q hq])
  -- Step 3: product is positive
  have h_pos : 0 < ∏ q ∈ Q, ((q - 2) / (q - 1)) :=
    Finset.prod_pos fun q hq => by
      exact div_pos (by linarith [hQ q hq]) (by linarith [hQ q hq])
  -- Step 4: chain ∏(q-2)/(q-1) ≤ exp(-C/2)
  have h_chain : ∏ q ∈ Q, ((q - 2) / (q - 1)) ≤ exp (-(C / 2)) :=
    h_safe.trans (exp_le_exp_of_le (by linarith))
  -- Step 5: invert both sides (using inv_anti₀)
  have h_inv := inv_anti₀ h_pos h_chain
  -- h_inv : (exp(-(C/2)))⁻¹ ≤ (∏(q-2)/(q-1))⁻¹
  rw [exp_neg, inv_inv] at h_inv
  -- h_inv : exp(C/2) ≤ (∏(q-2)/(q-1))⁻¹
  rwa [show (∏ q ∈ Q, ((q - 2) / (q - 1)))⁻¹ = ∏ q ∈ Q, ((q - 1) / (q - 2)) from by
    rw [← Finset.prod_inv_distrib]; congr 1; ext q; exact inv_div _ _] at h_inv

/-- ¬WM ⇒ products grow without bound. -/
theorem not_wm_product_diverges (hnwm : ¬ WeakMullin) :
    ∀ C : ℝ, ∃ (F : Finset Nat),
      (↑F : Set Nat) ⊆ MissingPrimes ∧
      C ≤ ∏ q ∈ F, ((q : ℝ) - 1) / ((q : ℝ) - 2) := by
  set g := Set.indicator MissingPrimes (fun n : Nat => (1 : ℝ) / n) with hg_def
  have hg_nn : 0 ≤ g := fun n => by
    simp only [g, Set.indicator]; split_ifs
    · exact div_nonneg zero_le_one (Nat.cast_nonneg n)
    · exact le_refl 0
  intro C
  -- Not summable + nonneg ⇒ can find finsets with arbitrarily large sums
  have hns : ¬ Summable g := hnwm
  have ⟨u, hu⟩ : ∃ u : Finset ℕ, 2 * max C 0 < ∑ x ∈ u, g x := by
    by_contra h; push_neg at h
    exact hns (summable_of_sum_le hg_nn h)
  -- Filter to MissingPrimes elements
  classical
  set F := u.filter (fun n => n ∈ MissingPrimes) with hF_def
  have hF_sub : (↑F : Set Nat) ⊆ MissingPrimes := by
    intro n hn; exact (Finset.mem_filter.mp (Finset.mem_coe.mp hn)).2
  -- All elements of MissingPrimes are primes ≥ 3
  have hF_ge3 : ∀ q ∈ F, 3 ≤ q := by
    intro q hq
    have ⟨hqp, hqne⟩ := hF_sub (Finset.mem_coe.mpr hq)
    -- q is prime (≥ 2) and q ≠ 2 (since seq 0 = 2)
    have hge2 := hqp.two_le
    have h2 : q ≠ 2 := by
      intro heq; exact hqne 0 (by rw [seq_zero]; exact heq.symm)
    omega
  -- Sum over u of g = sum over F of 1/q
  have hsum_eq : ∑ x ∈ u, g x = ∑ q ∈ F, 1 / (q : ℝ) := by
    have hrest : ∀ x ∈ u, x ∉ F → g x = 0 := by
      intro x _ hxF
      simp only [g, Set.indicator]
      split_ifs with h
      · exact absurd (Finset.mem_filter.mpr ⟨‹x ∈ u›, h⟩) hxF
      · rfl
    rw [← Finset.sum_filter_add_sum_filter_not u (fun n => n ∈ MissingPrimes)]
    simp only [← hF_def]
    have : ∑ x ∈ u.filter (fun n => n ∉ MissingPrimes), g x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [g, Set.indicator]
      split_ifs with h
      · exact absurd h (Finset.mem_filter.mp hx).2
      · rfl
    rw [this, add_zero]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [g, Set.indicator_of_mem (hF_sub (Finset.mem_coe.mpr hq))]
  -- Get the reciprocal sum bound
  have hsum_lb : 2 * max C 0 < ∑ q ∈ F, 1 / (q : ℝ) := by linarith [hsum_eq]
  -- Now apply product_divergence with the cast to ℝ
  -- We need Q : Finset ℝ with ∑ 1/q ≥ 2 * max C 0
  -- Work with F directly by relating products
  have hF_sum : max C 0 ≤ ∑ q ∈ F, 1 / (q : ℝ) := by
    have : (0 : ℝ) ≤ max C 0 := le_max_right _ _; linarith
  -- exp(max C 0 / 2) ≥ 1 ≥ 0 and exp(x) ≥ x for x ≥ 0... no
  -- For any x ≥ 0, exp(x) ≥ 1 + x ≥ x. So exp(max C 0 / 2) ≥ max C 0 / 2 ≥ C/2... not enough
  -- Better: apply product_divergence with the image in ℝ
  set Q := F.image (fun n : ℕ => (n : ℝ)) with hQ_def
  have hQ_ge3 : ∀ q ∈ Q, (3 : ℝ) ≤ q := by
    intro q hq
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
    exact_mod_cast hF_ge3 n hn
  have hQ_inj : Set.InjOn (fun n : ℕ => (n : ℝ)) ↑F := by
    intro a _ b _ hab
    have : (a : ℝ) = (b : ℝ) := hab
    exact_mod_cast this
  have hQ_sum : ∑ q ∈ Q, 1 / q = ∑ q ∈ F, 1 / (q : ℝ) := by
    rw [hQ_def, Finset.sum_image (fun a ha b hb hab => hQ_inj (Finset.mem_coe.mpr ha)
      (Finset.mem_coe.mpr hb) hab)]
  have hQ_prod : ∏ q ∈ Q, ((q - 1) / (q - 2)) = ∏ q ∈ F, (((q : ℝ) - 1) / ((q : ℝ) - 2)) := by
    rw [hQ_def, Finset.prod_image (fun a ha b hb hab => hQ_inj (Finset.mem_coe.mpr ha)
      (Finset.mem_coe.mpr hb) hab)]
  have hpd := product_divergence hQ_ge3 (by rw [hQ_sum])
  refine ⟨F, hF_sub, ?_⟩
  rw [← hQ_prod]
  calc C ≤ max C 0 := le_max_left _ _
    _ ≤ exp (max C 0) := by linarith [add_one_le_exp (max C 0)]
    _ ≤ exp ((∑ q ∈ F, 1 / (q : ℝ)) / 2) :=
        exp_le_exp_of_le (by linarith [hsum_lb])
    _ ≤ ∏ q ∈ Q, ((q - 1) / (q - 2)) := hpd

end ProductDivergence

/-! ## S89. EMBV and Confined Energy -/

section EMBVAndConfinedEnergy

open Classical

/-- **EMBV**: equivalent to MMCSB as a Prop. -/
def EMBV : Prop := MultiModularCSB

/-- Excess energy at prime q for N steps. -/
noncomputable def excessEnergyAt (q : Nat) [inst : Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (N : Nat) : ℝ :=
  @excessEnergy q inst N (fun (n : Fin N) => emWalkUnit q hq hne n.val)

/-- **JointSVE**: joint subquadratic visit energy over missing primes. -/
def JointSVE : Prop :=
  ∀ (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, Nat.Prime q ∧ ∀ k, seq k ≠ q),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∑ q ∈ Q.attach, (
      @excessEnergyAt q.val ⟨(hQ q.val q.prop).1⟩
        ((isPrime_iff_natPrime q.val).mpr (hQ q.val q.prop).1) (hQ q.val q.prop).2 N
    ) ≤ ε * (N : ℝ) ^ 2 * Q.card

/-- EMBV → MC (conditional on Q₀ ≤ 11). -/
theorem embv_implies_mc (hembv : EMBV)
    (hsmall : hembv.choose ≤ 11) : MullinConjecture :=
  mmcsb_small_threshold_mc hembv hsmall

/-- EMBV → WM (via MC). -/
theorem embv_implies_wm (hembv : EMBV)
    (hsmall : hembv.choose ≤ 11) : WeakMullin :=
  mc_implies_wm (embv_implies_mc hembv hsmall)

/-- JointSVE → MMCSB via per-prime SVE from singleton sets. -/
theorem jointSVE_implies_mmcsb (hjsve : JointSVE) : MultiModularCSB := by
  have hsve : SubquadraticVisitEnergy := by
    use 0
    intro q inst hge hq hne ε hε
    haveI : Fact (Nat.Prime q) := inst
    have hqp : Nat.Prime q := (isPrime_iff_natPrime q).mp hq
    have hQ : ∀ r ∈ ({q} : Finset ℕ), Nat.Prime r ∧ ∀ k, seq k ≠ r := by
      simp only [Finset.mem_singleton]; rintro r rfl; exact ⟨hqp, hne⟩
    obtain ⟨N₀, hN₀⟩ := hjsve {q} hQ ε hε
    use N₀; intro N hN
    have hbound := hN₀ N hN
    simp only [Finset.card_singleton, Nat.cast_one, mul_one] at hbound
    -- Simplify the singleton attach sum
    have hattach : ({q} : Finset ℕ).attach = {⟨q, Finset.mem_singleton.mpr rfl⟩} := by
      ext ⟨x, hx⟩; simp [Finset.mem_singleton.mp hx]
    rw [hattach, Finset.sum_singleton] at hbound
    -- Unfold excessEnergyAt and use proof irrelevance to match
    simp only [excessEnergyAt] at hbound
    exact hbound
  exact sve_implies_mmcsb hsve

/-- Confined energy: N²/(q-2) ≤ (q-1)·∑ V(a)² for missing prime q ≥ 3. -/
theorem per_prime_confined_energy_lb
    {q : Nat} [hp : Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hq3 : 3 ≤ q) (N : Nat) :
    (N : ℝ) ^ 2 / ((q : ℝ) - 2) ≤
    ((q : ℝ) - 1) * ∑ a : (ZMod q)ˣ,
      (@walkVisitCount q hp N (fun (n : Fin N) => emWalkUnit q hq hne n.val) a : ℝ) ^ 2 := by
  set w := fun (n : Fin N) => emWalkUnit q hq hne n.val
  have hq_cast : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hq1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by linarith
  have hq2_pos : (0 : ℝ) < (q : ℝ) - 2 := by linarith
  have h := @visit_energy_lower_bound q hp N w hq1
  -- h : N²/(q-1) ≤ ∑ V(a)², goal : N²/(q-2) ≤ (q-1)·∑ V(a)²
  calc (N : ℝ) ^ 2 / ((q : ℝ) - 2)
      ≤ (N : ℝ) ^ 2 := by
        rw [div_le_iff₀ hq2_pos]
        nlinarith [sq_nonneg (N : ℝ)]
    _ = ((q : ℝ) - 1) * ((N : ℝ) ^ 2 / ((q : ℝ) - 1)) := by
        rw [mul_div_cancel₀]; linarith
    _ ≤ ((q : ℝ) - 1) * ∑ a, (walkVisitCount w a : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left h (by linarith)

/-- Confined/equidistributed energy ratio = (q-1)/(q-2). -/
theorem confined_vs_equidist_ratio {q : ℝ} (hq : 3 ≤ q) {N : ℝ} (hN : N ≠ 0) :
    (N ^ 2 / (q - 2)) / (N ^ 2 / (q - 1)) = (q - 1) / (q - 2) := by
  have hN2 : N ^ 2 ≠ 0 := pow_ne_zero _ hN
  have hq2 : q - 2 ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  field_simp

end EMBVAndConfinedEnergy
