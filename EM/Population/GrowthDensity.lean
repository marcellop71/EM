import EM.Population.SeededGrowth
import EM.Population.HeadDomination
import Mathlib.NumberTheory.PrimeCounting

/-!
# The positive part of the growth factor map is thin, threshold by threshold

`SeededGrowth` shows `MixedDiversity ⟺ {m : C(m) > 0} = ∅`, and
`sgrowth_pos_iff_eventually_prime` shows `C(m) > 0 ⟺ ∃ N, ∀ n ≥ N, T^n m + 1 is prime`.
This file measures the sets on the right.

* **Primes have density zero** (`hasDensityZero_prime`), by the elementary sieve bound
  `Nat.primeCounting'_add_le` with the primorial modulus and `HeadDomination.cfun_tendsto_zero`
  (no PNT).
* **Density-zero sets pull back under `T`** (`hasDensityZero_comp_T`): if `A` is thin then so
  is `{m : A (m · minFac(m+1))}`.  Split by `p = minFac(m+1)`: for each fixed `p ≤ z` the map
  `m ↦ m·p` injects into `A ∩ [0, pX)`, and the tail `minFac(m+1) > z` is the rough count,
  of density `cfun(z+1) → 0`.
* Hence for every stage `N`, `{m : T^N m + 1 prime}` has density zero
  (`hasDensityZero_genProd_prime`) — at every fixed stage almost no seed has a prime Euclid
  number — and so has the **threshold-`N` prime-tower set**
  `{m : ∀ n ≥ N, T^n m + 1 prime}` (`hasDensityZero_perpetual`).

What is *not* concluded, and deliberately not claimed: `{C > 0}` is the countable union over
`N` of these sets (`sgrowth_pos_subset_iUnion`), and natural density is not countably
subadditive, so "`MixedDiversity` holds for almost every seed" does not follow.  The honest
statement is threshold by threshold.  The obstruction to uniformity is real: the preimage
bound `hasDensityZero_comp_T` costs a factor depending on the head cut `z`, and iterating it
`N` times gives no control uniform in `N`.
-/

noncomputable section

open Finset Filter Topology

namespace GrowthDensity

/-! ## Part 1: natural density zero -/

/-- The counting function `#{m < X : A m}`. -/
def cnt (A : ℕ → Prop) [DecidablePred A] (X : ℕ) : ℕ := ((range X).filter A).card

/-- `A` has natural density zero. -/
def HasDensityZero (A : ℕ → Prop) [DecidablePred A] : Prop :=
  Tendsto (fun X : ℕ => (cnt A X : ℝ) / X) atTop (𝓝 0)

theorem cnt_le (A : ℕ → Prop) [DecidablePred A] (X : ℕ) : cnt A X ≤ X := by
  unfold cnt
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem cnt_mono {A B : ℕ → Prop} [DecidablePred A] [DecidablePred B] (h : ∀ m, A m → B m)
    (X : ℕ) : cnt A X ≤ cnt B X :=
  Finset.card_le_card (fun m hm => by
    rw [Finset.mem_filter] at hm ⊢; exact ⟨hm.1, h m hm.2⟩)

theorem cnt_mono_X (A : ℕ → Prop) [DecidablePred A] {X Y : ℕ} (h : X ≤ Y) :
    cnt A X ≤ cnt A Y :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

/-- The `ε`-criterion. -/
theorem hasDensityZero_iff (A : ℕ → Prop) [DecidablePred A] :
    HasDensityZero A ↔ ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X → (cnt A X : ℝ) ≤ ε * X := by
  constructor
  · intro h ε hε
    rw [HasDensityZero, Metric.tendsto_atTop] at h
    obtain ⟨X₀, hX₀⟩ := h ε hε
    refine ⟨max X₀ 1, fun X hX => ?_⟩
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_right _ _) hX
    have := hX₀ X (le_trans (le_max_left _ _) hX)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    rw [div_lt_iff₀ (by linarith)] at this
    linarith
  · intro h
    rw [HasDensityZero, Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨X₀, hX₀⟩ := h (ε / 2) (by linarith)
    refine ⟨max X₀ 1, fun X hX => ?_⟩
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_right _ _) hX
    have := hX₀ X (le_trans (le_max_left _ _) hX)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ (by linarith)]
    nlinarith

theorem hasDensityZero_of_le {A B : ℕ → Prop} [DecidablePred A] [DecidablePred B]
    (h : ∀ m, A m → B m) (hB : HasDensityZero B) : HasDensityZero A := by
  rw [hasDensityZero_iff] at hB ⊢
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := hB ε hε
  exact ⟨X₀, fun X hX => le_trans (by exact_mod_cast cnt_mono h X) (hX₀ X hX)⟩

/-- Shifting the argument by a constant preserves density zero. -/
theorem hasDensityZero_shift {A : ℕ → Prop} [DecidablePred A] (hA : HasDensityZero A) (c : ℕ) :
    HasDensityZero (fun m => A (m + c)) := by
  rw [hasDensityZero_iff] at hA ⊢
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := hA (ε / 2) (by linarith)
  refine ⟨max X₀ c, fun X hX => ?_⟩
  have hcnt : cnt (fun m => A (m + c)) X ≤ cnt A (X + c) := by
    unfold cnt
    calc ((range X).filter (fun m => A (m + c))).card
        = (((range X).filter (fun m => A (m + c))).image (· + c)).card :=
          (Finset.card_image_of_injective _ (add_left_injective c)).symm
      _ ≤ ((range (X + c)).filter A).card := by
          apply Finset.card_le_card
          intro u hu
          obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hu
          rw [Finset.mem_filter, Finset.mem_range] at hm ⊢
          exact ⟨by omega, hm.2⟩
  have h1 := hX₀ (X + c) (by omega)
  have hcX : (c : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_right _ _) hX
  calc (cnt (fun m => A (m + c)) X : ℝ) ≤ cnt A (X + c) := by exact_mod_cast hcnt
    _ ≤ ε / 2 * ((X : ℝ) + c) := by push_cast at h1; exact h1
    _ ≤ ε * X := by nlinarith

/-! ## Part 2: primes have density zero (elementary) -/

/-- `#{m < X : m prime} = π'(X)`. -/
theorem cnt_prime (X : ℕ) : cnt Nat.Prime X = Nat.primeCounting' X := by
  unfold cnt
  rw [Nat.primeCounting', Nat.count_eq_card_filter_range]

/-- **Primes have density zero**, from the elementary sieve bound with the primorial modulus. -/
theorem hasDensityZero_prime : HasDensityZero Nat.Prime := by
  rw [hasDensityZero_iff]
  intro ε hε
  -- choose the head cut `z` with `cfun z < ε/2`
  obtain ⟨z, hz⟩ := (Metric.tendsto_atTop.mp HeadDomination.cfun_tendsto_zero) (ε / 2)
    (by linarith)
  have hz' : HeadDomination.cfun z < ε / 2 := by
    have := hz z le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (HeadDomination.cfun_nonneg z)] at this
    exact this
  set a := HeadDomination.Npr z with ha
  have ha0 : a ≠ 0 := (HeadDomination.Npr_pos z).ne'
  have har : (0 : ℝ) < a := by exact_mod_cast HeadDomination.Npr_pos z
  set k := a + 1 with hk
  -- constant part `π'(k) + φ(a)`
  set K : ℝ := (Nat.primeCounting' k : ℝ) + (Nat.totient a : ℝ) with hK
  obtain ⟨X₁, hX₁⟩ := exists_nat_gt (2 * K / ε)
  refine ⟨max X₁ k, fun X hX => ?_⟩
  have hXk : k ≤ X := le_trans (le_max_right _ _) hX
  have hXX₁ : (X₁ : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_left _ _) hX
  have hKX : 2 * K ≤ ε * X := by
    have : 2 * K / ε < X := lt_of_lt_of_le hX₁ hXX₁
    rw [div_lt_iff₀ hε] at this; linarith
  have hbound := Nat.primeCounting'_add_le ha0 (by omega : a < k) (X - k)
  rw [show k + (X - k) = X by omega] at hbound
  rw [cnt_prime]
  have h1 : (Nat.primeCounting' X : ℝ) ≤ Nat.primeCounting' k +
      (Nat.totient a : ℝ) * (((X - k) / a : ℕ) + 1) := by exact_mod_cast hbound
  have h2 : (((X - k) / a : ℕ) : ℝ) ≤ (X : ℝ) / a := by
    calc (((X - k) / a : ℕ) : ℝ) ≤ ((X - k : ℕ) : ℝ) / a :=
          (HeadDomination.nat_div_bounds (X - k) a (HeadDomination.Npr_pos z)).2
      _ ≤ (X : ℝ) / a := by
          apply div_le_div_of_nonneg_right _ har.le
          exact_mod_cast Nat.sub_le X k
  have hφ : (Nat.totient a : ℝ) / a = HeadDomination.cfun z := by
    rw [ha, HeadDomination.totient_Npr]; rfl
  have h3 : (Nat.totient a : ℝ) * ((X : ℝ) / a) = HeadDomination.cfun z * X := by
    rw [← hφ]; ring
  have hφ0 : (0 : ℝ) ≤ Nat.totient a := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  calc (Nat.primeCounting' X : ℝ)
      ≤ Nat.primeCounting' k + (Nat.totient a : ℝ) * (((X - k) / a : ℕ) + 1) := h1
    _ ≤ Nat.primeCounting' k + (Nat.totient a : ℝ) * ((X : ℝ) / a + 1) := by
        gcongr
    _ = K + HeadDomination.cfun z * X := by rw [hK, ← h3]; ring
    _ ≤ ε / 2 * X + ε / 2 * X :=
        add_le_add (by linarith) (mul_le_mul_of_nonneg_right hz'.le hX0)
    _ = ε * X := by ring

/-- `{m : m + 1 prime}` has density zero. -/
theorem hasDensityZero_succ_prime : HasDensityZero (fun m => Nat.Prime (m + 1)) :=
  hasDensityZero_shift hasDensityZero_prime 1

/-! ## Part 3: density zero pulls back under `T` -/

/-- The head part: for a fixed multiplier `p`, `m ↦ m·p` injects `{m < X : minFac(m+1) = p ∧
A (m p)}` into `{u < pX : A u}`. -/
theorem cnt_head_le (A : ℕ → Prop) [DecidablePred A] (p X : ℕ) (hp : 0 < p) :
    cnt (fun m => Nat.minFac (m + 1) = p ∧ A (m * Nat.minFac (m + 1))) X ≤ cnt A (p * X) := by
  unfold cnt
  calc ((range X).filter (fun m => Nat.minFac (m + 1) = p ∧ A (m * Nat.minFac (m + 1)))).card
      = (((range X).filter (fun m => Nat.minFac (m + 1) = p ∧ A (m * Nat.minFac (m + 1)))).image
          (fun m => m * p)).card :=
        (Finset.card_image_of_injective _ (mul_left_injective₀ hp.ne')).symm
    _ ≤ ((range (p * X)).filter A).card := by
        apply Finset.card_le_card
        intro u hu
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hu
        rw [Finset.mem_filter, Finset.mem_range] at hm ⊢
        obtain ⟨hmX, hmp, hA⟩ := hm
        refine ⟨by nlinarith, ?_⟩
        rw [hmp] at hA; exact hA

/-- The tail: `#{m < X : z < minFac (m+1)} ≤ roughCount z X + 1`. -/
theorem cnt_tail_le (z X : ℕ) :
    cnt (fun m => z < Nat.minFac (m + 1)) X ≤ roughCount z X + 1 := by
  unfold cnt roughCount
  -- `m ↦ m + 1` maps into `Icc 1 X`; the point `m + 1 = 1` contributes at most one
  calc ((range X).filter (fun m => z < Nat.minFac (m + 1))).card
      = (((range X).filter (fun m => z < Nat.minFac (m + 1))).image (· + 1)).card :=
        (Finset.card_image_of_injective _ (add_left_injective 1)).symm
    _ ≤ (insert 1 ((Icc 2 X).filter (fun m => z < Nat.minFac m))).card := by
        apply Finset.card_le_card
        intro u hu
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hu
        rw [Finset.mem_filter, Finset.mem_range] at hm
        rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
        by_cases h1 : m + 1 = 1
        · exact Or.inl h1
        · exact Or.inr ⟨⟨by omega, by omega⟩, hm.2⟩
    _ ≤ ((Icc 2 X).filter (fun m => z < Nat.minFac m)).card + 1 :=
        Finset.card_insert_le _ _

/-- **Density zero pulls back under `T`.** -/
theorem hasDensityZero_comp_T {A : ℕ → Prop} [DecidablePred A] (hA : HasDensityZero A) :
    HasDensityZero (fun m => A (m * Nat.minFac (m + 1))) := by
  rw [hasDensityZero_iff] at hA ⊢
  intro ε hε
  -- head cut `z`: rough density `cfun (z+1) < ε/4`
  obtain ⟨z, hz⟩ := (Metric.tendsto_atTop.mp HeadDomination.cfun_tendsto_zero) (ε / 4)
    (by linarith)
  have hz' : HeadDomination.cfun (z + 1) < ε / 4 := by
    have := hz (z + 1) (by omega)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (HeadDomination.cfun_nonneg _)] at this
    exact this
  -- the rough count is eventually `≤ (ε/4) X + 1 ... ≤ (ε/2) X`
  obtain ⟨X₂, hX₂⟩ := (Metric.tendsto_atTop.mp (HeadDomination.tendsto_roughCount_div z))
    (ε / 4 - HeadDomination.cfun (z + 1)) (by linarith)
  have htail : ∀ X, X₂ ≤ X → 1 ≤ X →
      (roughCount z X : ℝ) ≤ ε / 4 * X := by
    intro X hX hX1
    have := hX₂ X hX
    rw [Real.dist_eq, abs_lt] at this
    have hXr : (0 : ℝ) < X := by exact_mod_cast hX1
    have h' : (roughCount z X : ℝ) / X < ε / 4 := by linarith [this.2]
    rw [div_lt_iff₀ hXr] at h'
    exact h'.le
  -- head: for each `p ≤ z`, `cnt A (p X) ≤ ε/(4 (z+1)^2) · pX` for `X ≥ X₀`
  set δ : ℝ := ε / (4 * ((z : ℝ) + 1) ^ 2) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨X₀, hX₀⟩ := hA δ hδ0
  refine ⟨max (max X₀ X₂) (max 4 (Nat.ceil (4 / ε))), fun X hX => ?_⟩
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXX₂ : X₂ ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hX4 : 4 ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hXε : 4 / ε ≤ X := by
    have : Nat.ceil (4 / ε) ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  have hXr : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have h4 : (4 : ℝ) ≤ ε * X := by rw [div_le_iff₀ hε] at hXε; linarith
  -- decompose the count: head primes `p ≤ z` and tail
  have hsplit : cnt (fun m => A (m * Nat.minFac (m + 1))) X ≤
      (∑ p ∈ (range (z + 1)), cnt (fun m => Nat.minFac (m + 1) = p ∧
        A (m * Nat.minFac (m + 1))) X) + cnt (fun m => z < Nat.minFac (m + 1)) X := by
    unfold cnt
    have hsub : (range X).filter (fun m => A (m * Nat.minFac (m + 1))) ⊆
        ((range (z + 1)).biUnion (fun p => (range X).filter (fun m => Nat.minFac (m + 1) = p ∧
          A (m * Nat.minFac (m + 1))))) ∪ (range X).filter (fun m => z < Nat.minFac (m + 1)) := by
      intro m hm
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_union, Finset.mem_biUnion]
      by_cases hle : Nat.minFac (m + 1) ≤ z
      · left
        exact ⟨Nat.minFac (m + 1), Finset.mem_range.mpr (by omega),
          Finset.mem_filter.mpr ⟨hm.1, rfl, hm.2⟩⟩
      · right
        exact Finset.mem_filter.mpr ⟨hm.1, by omega⟩
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ _ := by gcongr; exact Finset.card_biUnion_le
  -- bound each head term
  have hhead : ∀ p ∈ range (z + 1),
      (cnt (fun m => Nat.minFac (m + 1) = p ∧ A (m * Nat.minFac (m + 1))) X : ℝ) ≤
        δ * ((z : ℝ) + 1) * X := by
    intro p hp
    have hpz : p ≤ z := by have := Finset.mem_range.mp hp; omega
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · -- `minFac (m+1) = 0` never happens
      have : cnt (fun m => Nat.minFac (m + 1) = p ∧ A (m * Nat.minFac (m + 1))) X = 0 := by
        unfold cnt
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro m _ hm
        have := Nat.minFac_pos (m + 1)
        omega
      rw [this]; push_cast; positivity
    · have h1 : (cnt (fun m => Nat.minFac (m + 1) = p ∧ A (m * Nat.minFac (m + 1))) X : ℝ) ≤
          cnt A (p * X) := by exact_mod_cast cnt_head_le A p X h0
      have h2 : (cnt A (p * X) : ℝ) ≤ δ * ((p * X : ℕ) : ℝ) :=
        hX₀ (p * X) (le_trans hXX₀ (Nat.le_mul_of_pos_left X h0))
      have hpr : (p : ℝ) ≤ (z : ℝ) + 1 := by exact_mod_cast (by omega : p ≤ z + 1)
      push_cast at h2
      calc _ ≤ δ * (p * X) := h1.trans h2
        _ ≤ δ * ((z : ℝ) + 1) * X := by
            rw [mul_assoc]; gcongr
  have hsum : ((∑ p ∈ range (z + 1), cnt (fun m => Nat.minFac (m + 1) = p ∧
      A (m * Nat.minFac (m + 1))) X : ℕ) : ℝ) ≤ ε / 4 * X := by
    push_cast
    calc (∑ p ∈ range (z + 1), (cnt (fun m => Nat.minFac (m + 1) = p ∧
          A (m * Nat.minFac (m + 1))) X : ℝ))
        ≤ ∑ p ∈ range (z + 1), δ * ((z : ℝ) + 1) * X := Finset.sum_le_sum hhead
      _ = (z + 1 : ℕ) * (δ * ((z : ℝ) + 1) * X) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ε / 4 * X := by
          rw [hδ]; push_cast; field_simp
  have htail' : (cnt (fun m => z < Nat.minFac (m + 1)) X : ℝ) ≤ ε / 4 * X + 1 := by
    have := cnt_tail_le z X
    have h := htail X hXX₂ (by omega)
    calc (cnt (fun m => z < Nat.minFac (m + 1)) X : ℝ)
        ≤ (roughCount z X : ℝ) + 1 := by exact_mod_cast this
      _ ≤ ε / 4 * X + 1 := by linarith
  calc (cnt (fun m => A (m * Nat.minFac (m + 1))) X : ℝ)
      ≤ ((∑ p ∈ range (z + 1), cnt (fun m => Nat.minFac (m + 1) = p ∧
          A (m * Nat.minFac (m + 1))) X : ℕ) : ℝ) + cnt (fun m => z < Nat.minFac (m + 1)) X := by
        exact_mod_cast hsplit
    _ ≤ ε / 4 * X + (ε / 4 * X + 1) := add_le_add hsum htail'
    _ ≤ ε * X := by linarith

/-- Iterated: density zero pulls back under `T^N`. -/
theorem hasDensityZero_comp_genProd {A : ℕ → Prop} [DecidablePred A] (hA : HasDensityZero A)
    (N : ℕ) : HasDensityZero (fun m => A (genProd m N)) := by
  induction N generalizing A with
  | zero => exact hA
  | succ N ih =>
    have h1 : HasDensityZero (fun m => A (genProd (m * Nat.minFac (m + 1)) N)) :=
      hasDensityZero_comp_T (A := fun u => A (genProd u N)) (ih hA)
    refine hasDensityZero_of_le (fun m hm => ?_) h1
    have e : genProd m (N + 1) = genProd (m * Nat.minFac (m + 1)) N := by
      rw [add_comm, ← genProd_restart]; rfl
    have hm' : A (genProd m (N + 1)) := hm
    rw [e] at hm'; exact hm'

/-! ## Part 4: the prime-tower sets -/

/-- **At every fixed stage `N`, almost no seed has a prime Euclid number.** -/
theorem hasDensityZero_genProd_prime (N : ℕ) :
    HasDensityZero (fun m => Nat.Prime (genProd m N + 1)) :=
  hasDensityZero_comp_genProd hasDensityZero_succ_prime N

/-- The threshold-`N` prime-tower set: seeds whose orbit is a tower of primes from stage `N`. -/
def PerpetualFrom (N : ℕ) (m : ℕ) : Prop := ∀ n, N ≤ n → Nat.Prime (genProd m n + 1)

instance (N : ℕ) : DecidablePred (PerpetualFrom N) := fun _ => Classical.propDecidable _

/-- **For every threshold `N`, the prime-tower set has density zero.** -/
theorem hasDensityZero_perpetual (N : ℕ) : HasDensityZero (PerpetualFrom N) :=
  hasDensityZero_of_le (fun _ hm => hm N le_rfl) (hasDensityZero_genProd_prime N)

/-- `{C > 0}` is the union of the threshold sets — a countable union of density-zero sets.
Natural density is not countably subadditive, so no density statement about `{C > 0}` itself
follows; see the module docstring. -/
theorem sgrowth_pos_subset_iUnion :
    {m : ℕ | 2 ≤ m ∧ 0 < SeededGrowth.sgrowth m} ⊆ ⋃ N : ℕ, {m | PerpetualFrom N m} := by
  intro m ⟨hm2, hpos⟩
  obtain ⟨N, hN⟩ := (SeededGrowth.sgrowth_pos_iff_eventually_prime hm2).mp hpos
  exact Set.mem_iUnion.mpr ⟨N, hN⟩

/-- Conversely each threshold set (with `m ≥ 2`) lies in `{C > 0}`. -/
theorem perpetual_subset_sgrowth_pos (N : ℕ) :
    {m | 2 ≤ m ∧ PerpetualFrom N m} ⊆ {m : ℕ | 2 ≤ m ∧ 0 < SeededGrowth.sgrowth m} := by
  intro m ⟨hm2, hN⟩
  exact ⟨hm2, (SeededGrowth.sgrowth_pos_iff_eventually_prime hm2).mpr ⟨N, hN⟩⟩

/-- **Landscape.**  Threshold by threshold, the positive part of the growth factor map is
null; `MixedDiversity` asks that it be empty. -/
theorem growth_density_landscape :
    (∀ N, HasDensityZero (PerpetualFrom N)) ∧
    ({m : ℕ | 2 ≤ m ∧ 0 < SeededGrowth.sgrowth m} ⊆ ⋃ N : ℕ, {m | PerpetualFrom N m}) ∧
    (MixedDiversity ↔ ∀ m, 2 ≤ m → SeededGrowth.sgrowth m = 0) :=
  ⟨hasDensityZero_perpetual, sgrowth_pos_subset_iUnion,
    SeededGrowth.mixedDiversity_iff_sgrowth_zero⟩

end GrowthDensity

end
