import EM.Equidist.SieveTransfer
import EM.CME.Reduction
import EM.Equidist.SelfCorrecting

/-!
# Walk excursions

An **excursion** at position `c` is a segment of the walk between two visits to `c`
(any two visits: the structure does not require a *first* return). The key structural fact is `excursionMultProd_eq_one`: the product
of multipliers during any excursion is trivial (since the walk returns to its
starting position).

The **Excursion Independence** and **bounded max excursion** hypotheses that this file used
to state (EIP + BME ⇒ CCSB ⇒ MC) were found defective on 2026-11-11 and archived (RED #21):
see Section 3 below and `EM/Meta/HypothesisAudit.lean`.  What remains live is the structural
theory of excursions.

## Main Results

* `Excursion` : structure for a walk segment between two visits to a fixed position
* `excursionMultProd` : product of multipliers during an excursion
* `excursionMultProd_eq_one` : the multiplier product is trivial (PROVED)
* `excursionCharSum_le_len` : triangle inequality bound on excursion char sum (PROVED)
* `walkCharSum_excursion` : walk char sum within excursion = chi(c) * excursionCharSum (PROVED)
* `avoidanceDiscrepancy` : the avoidance bias 1/(q-2) - 1/(q-1) (PROVED positive)
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## Section 1: Definitions -/

/-- An **excursion** at position `c` for the EM walk mod `q` is a walk segment
    from time `start` to time `stop` where the walk equals `c` at both endpoints. -/
structure Excursion (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (c : (ZMod q)ˣ) where
  /-- Starting time of the excursion. -/
  start : ℕ
  /-- Ending time of the excursion. -/
  stop : ℕ
  /-- The excursion is non-degenerate. -/
  h_lt : start < stop
  /-- The walk is at position `c` at the start. -/
  h_start : emWalkUnit q hq hne start = c
  /-- The walk is at position `c` at the stop. -/
  h_stop : emWalkUnit q hq hne stop = c

variable {q : ℕ} [Fact (Nat.Prime q)] {hq : IsPrime q} {hne : ∀ k, seq k ≠ q}
  {c : (ZMod q)ˣ}

/-- The length of an excursion: `stop - start`. -/
noncomputable def Excursion.len (exc : Excursion q hq hne c) : ℕ :=
  exc.stop - exc.start

/-- The length of an excursion is positive. -/
theorem Excursion.len_pos (exc : Excursion q hq hne c) : 0 < exc.len := by
  simp only [Excursion.len]; exact Nat.sub_pos_of_lt exc.h_lt

/-- `start + len = stop` for an excursion. -/
theorem Excursion.start_add_len (exc : Excursion q hq hne c) :
    exc.start + exc.len = exc.stop := by
  simp only [Excursion.len]; have := exc.h_lt; omega

/-- Product of multipliers during an excursion: `∏ i in range(len), m(start + i)`. -/
noncomputable def excursionMultProd (exc : Excursion q hq hne c) : (ZMod q)ˣ :=
  ∏ i ∈ Finset.range exc.len, emMultUnit q hq hne (exc.start + i)

/-- Character sum within an excursion: the sum of partial products of character values.
    For character chi, this is
    `∑ t in range(len), ∏ k in range(t), (chi (m(start + k)) : C)`.
    At t=0, the empty product contributes 1. -/
noncomputable def excursionCharSum (χ : (ZMod q)ˣ →* ℂˣ)
    (exc : Excursion q hq hne c) : ℂ :=
  ∑ t ∈ Finset.range exc.len,
    ∏ k ∈ Finset.range t, (χ (emMultUnit q hq hne (exc.start + k)) : ℂ)

/-- Walk character sum from step `a` to step `b`:
    `∑ n in Ico a b, (chi (emWalkUnit q hq hne n) : C)`. -/
noncomputable def walkCharSumRange (q : ℕ) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (a b : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico a b, (χ (emWalkUnit q hq hne n) : ℂ)

/-! ## Section 2: Proved Basic Properties -/

/-- **Key lemma**: The product of multipliers during an excursion equals 1.
    Since `w(stop) = c = w(start)` and `w(start + len) = w(start) * prod m(start+i)`,
    left cancellation gives `prod m(start + i) = 1`. -/
theorem excursionMultProd_eq_one (exc : Excursion q hq hne c) :
    excursionMultProd exc = 1 := by
  unfold excursionMultProd
  have htelescope := walk_product_telescope
    (emWalkUnit q hq hne) (emMultUnit q hq hne)
    (emWalkUnit_succ q hq hne) exc.start exc.len
  rw [exc.start_add_len] at htelescope
  rw [exc.h_stop, exc.h_start] at htelescope
  -- c = c * prod, so prod = 1 by left cancellation
  exact mul_left_cancel (a := c) (by rw [mul_one]; exact htelescope.symm)

/-- Each term in the excursion character sum has norm at most 1: it is a product
    of character values, each of norm 1. -/
theorem excursionCharSum_term_norm_le_one (χ : (ZMod q)ˣ →* ℂˣ)
    (exc : Excursion q hq hne c) (t : ℕ) :
    ‖∏ k ∈ Finset.range t, (χ (emMultUnit q hq hne (exc.start + k)) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_prod]
  have heq : ∏ k ∈ Finset.range t,
      ‖(χ (emMultUnit q hq hne (exc.start + k)) : ℂ)‖ =
      ∏ _k ∈ Finset.range t, (1 : ℝ) := by
    congr 1; ext k; exact walkTelescope_char_norm_one χ _
  rw [heq, Finset.prod_const_one]

/-- **Triangle inequality bound**: `‖excursionCharSum chi exc‖ ≤ exc.len`. -/
theorem excursionCharSum_le_len (χ : (ZMod q)ˣ →* ℂˣ)
    (exc : Excursion q hq hne c) :
    ‖excursionCharSum χ exc‖ ≤ exc.len := by
  unfold excursionCharSum
  calc ‖∑ t ∈ Finset.range exc.len, ∏ k ∈ Finset.range t,
      (χ (emMultUnit q hq hne (exc.start + k)) : ℂ)‖
      ≤ ∑ t ∈ Finset.range exc.len, ‖∏ k ∈ Finset.range t,
        (χ (emMultUnit q hq hne (exc.start + k)) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ Finset.range exc.len, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro t _
        exact excursionCharSum_term_norm_le_one χ exc t
    _ = exc.len := by simp

/-- **Walk position at an interior point**: for `t ≤ exc.len`,
    `emWalkUnit q hq hne (exc.start + t) = c * prod_{k<t} m(start + k)`. -/
theorem excursion_walk_at (exc : Excursion q hq hne c) (t : ℕ)
    (_ht : t ≤ exc.len) :
    emWalkUnit q hq hne (exc.start + t) =
      c * ∏ k ∈ Finset.range t, emMultUnit q hq hne (exc.start + k) := by
  have htelescope := walk_product_telescope
    (emWalkUnit q hq hne) (emMultUnit q hq hne)
    (emWalkUnit_succ q hq hne) exc.start t
  rw [exc.h_start] at htelescope
  exact htelescope

/-- **Walk character sum within an excursion decomposes as chi(c) times the excursion
    character sum**: `walkCharSumRange q hq hne chi start stop = chi(c) * excursionCharSum chi exc`.

    Proof: At step `start + t`, `w(start + t) = c * prod_{k<t} m(start + k)` by
    `walk_product_telescope`. Applying chi (a monoid hom):
    `chi(w(start+t)) = chi(c) * prod_{k<t} chi(m(start+k))`. Factor out chi(c). -/
theorem walkCharSum_excursion (χ : (ZMod q)ˣ →* ℂˣ)
    (exc : Excursion q hq hne c) :
    walkCharSumRange q hq hne χ exc.start exc.stop =
      (χ c : ℂ) * excursionCharSum χ exc := by
  unfold walkCharSumRange excursionCharSum
  -- Step 1: Reindex Ico start stop as image of range len under (· + start)
  have hIco_eq : Finset.Ico exc.start exc.stop =
      (Finset.range exc.len).image (· + exc.start) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range, Excursion.len]
    constructor
    · intro ⟨hle, hlt⟩
      exact ⟨n - exc.start, by omega, by omega⟩
    · rintro ⟨t, ht, rfl⟩
      constructor <;> omega
  rw [hIco_eq]
  rw [Finset.sum_image (by intro a _ b _ hab; simp only at hab; omega)]
  -- Step 2: Factor out chi(c)
  rw [Finset.mul_sum]
  congr 1; ext t
  -- Step 3: Expand w(start + t) using walk_product_telescope
  rw [show t + exc.start = exc.start + t from by omega]
  have htelescope := walk_product_telescope
    (emWalkUnit q hq hne) (emMultUnit q hq hne)
    (emWalkUnit_succ q hq hne) exc.start t
  rw [exc.h_start] at htelescope
  rw [htelescope]
  -- chi(c * prod) = chi(c) * chi(prod) = chi(c) * prod chi(m_k)
  simp only [map_mul, Units.val_mul, map_prod, Units.coe_prod]

/-- **Sum of squares bounded by max times sum** (version with explicit bound):
    if `∀ i in s, x i ≤ M` and `∀ i in s, 0 ≤ x i`, then `sum x^2 ≤ M * sum x`. -/
theorem sum_sq_le_bound_mul_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ) (M : ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hM : ∀ i ∈ s, x i ≤ M) :
    ∑ i ∈ s, x i ^ 2 ≤ M * ∑ i ∈ s, x i := by
  calc ∑ i ∈ s, x i ^ 2
      = ∑ i ∈ s, x i * x i := by congr 1; ext i; ring
    _ ≤ ∑ i ∈ s, M * x i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hM i hi) (hx i hi)
    _ = M * ∑ i ∈ s, x i := by rw [← Finset.mul_sum]

/-! ## Section 3: Excursion hypotheses (archived 2026-11-11)

The hypotheses `ExcursionIndependence`, `BoundedMaxExcursion` and their universal forms
`UniversalEIP`, `UniversalBoundedMax` were found defective as stated (review
`docs/analysis/review_2026-11-10.md`, row H6): an `Excursion` is *any* pair of visits to `c`,
not a first return, and the lists in `ExcursionIndependence` may repeat an excursion.

* `UniversalBoundedMax` is contradictory at a missing prime — some position is visited
  infinitely often, and the excursion from a fixed visit to a far later one has length
  `> N/2` — hence equivalent to MC by logic alone: `HypothesisAudit.universalBoundedMax_iff_mc`.
* `ExcursionIndependence` forces every excursion character sum to vanish (repeat one excursion
  more than `C` times): `HypothesisAudit.excursionCharSum_eq_zero_of_excursionIndependence`.

The four definitions now live in `EM/Meta/HypothesisAudit.lean` next to these theorems.

-- CMEImpliesEIP archived to EM/Archive/Transfer/ExcursionArchive.lean (RED #21)
-- EIPBoundedImpliesCCSBAt archived to EM/Archive/Transfer/ExcursionArchive.lean (RED #21)
-- UniversalEIPBoundedImpliesCCSB archived to EM/Archive/Transfer/ExcursionArchive.lean (RED #21)
-- eip_bounded_implies_mc archived to EM/Archive/Transfer/ExcursionArchive.lean (RED #21)
-/

/-! ## Section 5: Avoidance Discrepancy -/

/-- The **avoidance discrepancy**: the bias introduced by death-value avoidance.
    When the walk avoids one specific position (the "death value" `-1`), the
    uniform distribution on `q-1` units shifts to a distribution on `q-2` surviving
    units. The discrepancy per step is `1/(q-2) - 1/(q-1) = 1/((q-1)(q-2))`. -/
noncomputable def avoidanceDiscrepancy (q : ℕ) : ℝ :=
  1 / (q - 2 : ℝ) - 1 / (q - 1 : ℝ)

/-- The avoidance discrepancy equals `1/((q-1)(q-2))`. -/
theorem avoidanceDiscrepancy_eq (q : ℕ) (hq : 4 ≤ q) :
    avoidanceDiscrepancy q = 1 / ((q - 1 : ℝ) * (q - 2 : ℝ)) := by
  unfold avoidanceDiscrepancy
  have hq_cast : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h1 : (q : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (q : ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

/-- The avoidance discrepancy is positive for `q >= 4`. -/
theorem avoidanceDiscrepancy_pos (q : ℕ) (hq : 4 ≤ q) :
    0 < avoidanceDiscrepancy q := by
  rw [avoidanceDiscrepancy_eq q hq]
  have hq_cast : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  apply div_pos one_pos
  apply mul_pos <;> linarith

/-- The avoidance discrepancy is at most `1/(q-2)^2` for `q >= 4`.
    Since `1/((q-1)(q-2)) ≤ 1/(q-2)^2` iff `(q-2)^2 ≤ (q-1)(q-2)` iff `q-2 ≤ q-1`. -/
theorem avoidanceDiscrepancy_le (q : ℕ) (hq : 4 ≤ q) :
    avoidanceDiscrepancy q ≤ 1 / (q - 2 : ℝ) ^ 2 := by
  rw [avoidanceDiscrepancy_eq q hq]
  have hq_cast : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h2 : (0 : ℝ) < (q : ℝ) - 2 := by linarith
  -- 1/((q-1)(q-2)) ≤ 1/(q-2)^2 since (q-2)^2 ≤ (q-1)(q-2) since q-2 ≤ q-1
  exact div_le_div_of_nonneg_left (by linarith : (0 : ℝ) ≤ 1)
    (pow_pos h2 2) (by nlinarith)

/-! ## Section 6: Additional Structural Results -/

/-- **Excursion char sum starts at 1**: The t=0 term in `excursionCharSum` is the
    empty product, which equals 1. -/
theorem excursionCharSum_initial_term (χ : (ZMod q)ˣ →* ℂˣ)
    (exc : Excursion q hq hne c) (hlen : 1 ≤ exc.len) :
    (1 : ℂ) ∈ (Finset.range exc.len).image
      (fun t => ∏ k ∈ Finset.range t,
        (χ (emMultUnit q hq hne (exc.start + k)) : ℂ)) := by
  rw [Finset.mem_image]
  exact ⟨0, Finset.mem_range.mpr hlen, by simp⟩

/-- **Excursion multiplier product as character value**: applying a character to the
    excursion multiplier product gives 1, since the product itself is 1. -/
theorem excursion_char_prod_eq_one (χ : (ZMod q)ˣ →* ℂˣ)
    (exc : Excursion q hq hne c) :
    (χ (excursionMultProd exc) : ℂ) = 1 := by
  rw [excursionMultProd_eq_one exc, map_one, Units.val_one]

/-- **Two excursions compose**: if one excursion ends where another starts
    (at the same position `c`), and the second starts at the first's stop,
    then the concatenation is also an excursion. -/
def Excursion.append (exc1 exc2 : Excursion q hq hne c)
    (h : exc1.stop = exc2.start) : Excursion q hq hne c where
  start := exc1.start
  stop := exc2.stop
  h_lt := by have := exc1.h_lt; have := exc2.h_lt; omega
  h_start := exc1.h_start
  h_stop := exc2.h_stop

/-- **Composing excursions adds lengths**:
    `(exc1.append exc2 h).len = exc1.len + exc2.len`. -/
theorem Excursion.append_len (exc1 exc2 : Excursion q hq hne c)
    (h : exc1.stop = exc2.start) :
    (exc1.append exc2 h).len = exc1.len + exc2.len := by
  simp only [Excursion.len, Excursion.append]
  have := exc1.h_lt; have := exc2.h_lt; omega

/-- **Norm squared of a character value is 1**: for any unit `u`, `‖(chi u : C)‖^2 = 1`. -/
theorem char_norm_sq_eq_one (χ : (ZMod q)ˣ →* ℂˣ) (u : (ZMod q)ˣ) :
    ‖(χ u : ℂ)‖ ^ 2 = 1 := by
  rw [walkTelescope_char_norm_one χ u]; norm_num

/-- **Walk char sum norm within excursion is at most len**: using
    `walkCharSum_excursion` and `excursionCharSum_le_len`. -/
theorem walkCharSumRange_le_len (χ : (ZMod q)ˣ →* ℂˣ)
    (exc : Excursion q hq hne c) :
    ‖walkCharSumRange q hq hne χ exc.start exc.stop‖ ≤ exc.len := by
  rw [walkCharSum_excursion χ exc]
  rw [norm_mul, walkTelescope_char_norm_one χ c, one_mul]
  exact excursionCharSum_le_len χ exc

/-! ## Section 7: Excursion Character Sum Norm Squared Identity

The excursion character sum satisfies a useful "return-to-1" identity:
since the total multiplier product over an excursion is 1, the partial
products (which ARE the terms of the excursion character sum) form a
closed path on the unit circle (when viewed through the character chi). -/

/-- **Excursion char sum squared bound via length squared**:
    `‖excursionCharSum chi exc‖^2 ≤ exc.len^2`. -/
theorem excursionCharSum_sq_le_len_sq (χ : (ZMod q)ˣ →* ℂˣ)
    (exc : Excursion q hq hne c) :
    ‖excursionCharSum χ exc‖ ^ 2 ≤ (exc.len : ℝ) ^ 2 := by
  have h := excursionCharSum_le_len χ exc
  nlinarith [norm_nonneg (excursionCharSum χ exc)]

/-- **Excursion sum norm is nonneg**: trivial but useful for API. -/
theorem excursionCharSum_norm_nonneg (χ : (ZMod q)ˣ →* ℂˣ)
    (exc : Excursion q hq hne c) :
    0 ≤ ‖excursionCharSum χ exc‖ := norm_nonneg _

/-! ## Summary

### New definitions:
- `Excursion` : structure for walk segment between returns to position c
- `Excursion.len` : length of excursion (stop - start)
- `excursionMultProd` : product of multipliers during excursion
- `excursionCharSum` : partial-product character sum within excursion
- `walkCharSumRange` : walk character sum from step a to step b
- `avoidanceDiscrepancy` : bias from death-value avoidance
- `Excursion.append` : composition of consecutive excursions

### Proved theorems (zero sorry):
- `excursionMultProd_eq_one` : multiplier product is trivial
- `excursionCharSum_le_len` : triangle inequality bound
- `excursionCharSum_term_norm_le_one` : each term has norm at most 1
- `excursion_walk_at` : walk position at interior point
- `walkCharSum_excursion` : walk char sum = chi(c) * excursion char sum
- `sum_sq_le_bound_mul_sum` : sum x_i^2 ≤ M * sum x_i
- `avoidanceDiscrepancy_eq` : closed form 1/((q-1)(q-2))
- `avoidanceDiscrepancy_pos` : positive for q >= 4
- `avoidanceDiscrepancy_le` : upper bound 1/(q-2)^2
- `excursionCharSum_initial_term` : t=0 term is 1
- `excursion_char_prod_eq_one` : chi(multProd) = 1
- `Excursion.append_len` : concatenation adds lengths
- `char_norm_sq_eq_one` : ‖chi(u)‖^2 = 1
- `walkCharSumRange_le_len` : walk char sum norm at most len
- `excursionCharSum_sq_le_len_sq` : ‖sigma‖^2 ≤ L^2
- `excursionCharSum_norm_nonneg` : ‖sigma‖ >= 0

### Open hypotheses: none
The seven excursion hypotheses formerly listed here (`ExcursionIndependence`,
`BoundedMaxExcursion`, `UniversalEIP`, `UniversalBoundedMax`, `CMEImpliesEIP`,
`EIPBoundedImpliesCCSBAt`, `UniversalEIPBoundedImpliesCCSB`) were archived on 2026-11-11
(RED #21); see Section 3.
-/
