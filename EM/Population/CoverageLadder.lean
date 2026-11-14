import EM.Population.WeakMullin
import Mathlib.NumberTheory.PrimeCounting

/-!
# The coverage ladder: how many primes does the Euclid–Mullin sequence collect?

2026-09-24.  Let `S(x)` be the number of Euclid–Mullin primes `≤ x` (`emCount`) and `M(x)`
the number of missing primes `≤ x` (`missCount`), so `S(x) + M(x) = π(x)`.  The weak forms of
MC on file (`WeakMullin.lean`) are `MissingFinite` (cofinitely many primes appear) and
`WeakMullin` (`∑ 1/q` over missing primes converges).  Two density rungs sit between them and
reciprocal divergence:

* `MissingDensityZero` — `M(x) = o(π(x))`: almost all primes appear;
* `PositiveDensity` — `S(x) ≥ c·π(x)` eventually: the sequence collects a positive proportion
  of the primes.

Proved here: `MC ⟹ MissingFinite ⟹ MissingDensityZero ⟹ PositiveDensity ⟹ RD`.  The last
step is Abel summation (`abel_identity`): `∑_{a∈A, a≤N} 1/a = ∑_{n≤N} A(n)/(n(n+1)) + A(N)/(N+1)`
for any set `A ∌ 0`, so a counting-function inequality `S ≥ c π` transfers to the reciprocal
sums, and `∑_p 1/p = ∞` finishes.  No Chebyshev bound is used.

**Scope.**  Every rung is open.  Not even `PositiveDensity` is known: the only lower
bound on `S(x)` in sight is the doubly-exponential one, `S(x) ≥ log₂ log₃ x`, which follows from
`CompositeFloor.prod_add_one_le_three_pow` and is not stated as a theorem.
The rungs say exactly what "few missing primes" means for the single orbit of `2`.
-/

noncomputable section
open Classical Filter Mullin

namespace CoverageLadder

/-- Number of primes `≤ x`, as a filtered card (equals `Nat.primeCounting x`). -/
def primeCount (x : ℕ) : ℕ := ((Finset.range (x + 1)).filter Nat.Prime).card

theorem primeCount_eq (x : ℕ) : primeCount x = Nat.primeCounting x := by
  rw [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rfl

/-- Number of Euclid–Mullin primes `≤ x`. -/
def emCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p : ℕ => Nat.Prime p ∧ p ∈ Set.range Mullin.seq)).card

/-- Number of missing primes `≤ x`. -/
def missCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p : ℕ => Nat.Prime p ∧ p ∉ Set.range Mullin.seq)).card

theorem mem_missingPrimes_iff {p : ℕ} : p ∈ MissingPrimes ↔ p.Prime ∧ p ∉ Set.range Mullin.seq := by
  simp only [MissingPrimes, Set.mem_ofPred_eq, Set.mem_range, not_exists]

theorem emCount_add_missCount (x : ℕ) : emCount x + missCount x = primeCount x := by
  unfold emCount missCount primeCount
  rw [← Finset.card_filter_add_card_filter_not (s := (Finset.range (x + 1)).filter Nat.Prime)
    (fun p => p ∈ Set.range Mullin.seq)]
  simp only [Finset.filter_filter]

theorem emCount_le_primeCount (x : ℕ) : emCount x ≤ primeCount x := by
  have := emCount_add_missCount x; omega

theorem missCount_le_primeCount (x : ℕ) : missCount x ≤ primeCount x := by
  have := emCount_add_missCount x; omega

/-! ## The rungs -/

/-- **Almost all primes appear**: `M(x) = o(π(x))`. -/
def MissingDensityZero : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, (missCount x : ℝ) ≤ ε * primeCount x

/-- **A positive proportion of the primes appears**: `S(x) ≥ c π(x)` eventually. -/
def PositiveDensity : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop, c * primeCount x ≤ emCount x

theorem tendsto_primeCount : Tendsto (fun x => (primeCount x : ℝ)) atTop atTop := by
  have h : Tendsto (fun x : ℕ => (Nat.primeCounting x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  exact h.congr (fun x => by rw [primeCount_eq])

/-- **MissingFinite ⟹ MissingDensityZero.** -/
theorem missingDensityZero_of_missingFinite (h : MissingFinite) : MissingDensityZero := by
  intro ε hε
  set K : ℕ := h.toFinset.card
  have hbound : ∀ x, missCount x ≤ K := by
    intro x
    unfold missCount
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter] at hp
    exact h.mem_toFinset.mpr (mem_missingPrimes_iff.mpr hp.2)
  have hev : ∀ᶠ x : ℕ in atTop, (K : ℝ) / ε ≤ primeCount x :=
    tendsto_atTop.mp tendsto_primeCount _
  filter_upwards [hev] with x hx
  calc (missCount x : ℝ) ≤ K := by exact_mod_cast hbound x
    _ = ε * (K / ε) := by field_simp
    _ ≤ ε * primeCount x := by gcongr

/-- **MissingDensityZero ⟹ PositiveDensity** (with `c = 1/2`). -/
theorem positiveDensity_of_missingDensityZero (h : MissingDensityZero) : PositiveDensity := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [h (1 / 2) (by norm_num)] with x hx
  have hsum : (emCount x : ℝ) + missCount x = primeCount x := by
    exact_mod_cast emCount_add_missCount x
  linarith

/-! ## Abel summation -/

/-- Counting function of a set: `#{a ∈ A : a ≤ n}`. -/
def cnt (A : Set ℕ) (n : ℕ) : ℕ := ((Finset.range (n + 1)).filter (· ∈ A)).card

theorem cnt_succ (A : Set ℕ) (n : ℕ) :
    cnt A (n + 1) = cnt A n + if n + 1 ∈ A then 1 else 0 := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · simp

theorem cnt_le (A : Set ℕ) (n : ℕ) : cnt A n ≤ n + 1 := by
  unfold cnt
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- **Abel summation.**  For `0 ∉ A`,
`∑_{a ≤ N} 1_A(a)/a = ∑_{n ≤ N} A(n)/(n(n+1)) + A(N)/(N+1)`. -/
theorem abel_identity (A : Set ℕ) (h0 : 0 ∉ A) (N : ℕ) :
    ∑ a ∈ Finset.range (N + 1), Set.indicator A (fun n : ℕ => (1 : ℝ) / n) a
      = ∑ n ∈ Finset.range (N + 1), (cnt A n : ℝ) / (n * (n + 1)) + (cnt A N : ℝ) / (N + 1) := by
  induction N with
  | zero =>
    have h00 : cnt A 0 = 0 := by
      unfold cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx
      simp only [zero_add, Finset.range_one, Finset.mem_singleton] at hx
      rw [hx]; exact h0
    simp [Set.indicator_of_notMem h0, h00]
  | succ N ih =>
    rw [Finset.sum_range_succ _ (N + 1), ih,
      Finset.sum_range_succ (fun n : ℕ => (cnt A n : ℝ) / (n * (n + 1))) (N + 1), cnt_succ]
    generalize (∑ n ∈ Finset.range (N + 1), (cnt A n : ℝ) / (n * (n + 1))) = G
    have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have hN2 : (N : ℝ) + 1 + 1 ≠ 0 := by positivity
    split_ifs with hA
    · rw [Set.indicator_of_mem hA]
      push_cast
      field_simp
      ring
    · rw [Set.indicator_of_notMem hA]
      push_cast
      field_simp
      ring

/-- The Abel sum is bounded by the reciprocal sum (drop the boundary term). -/
theorem abel_sum_le (A : Set ℕ) (h0 : 0 ∉ A) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (cnt A n : ℝ) / (n * (n + 1))
      ≤ ∑ a ∈ Finset.range (N + 1), Set.indicator A (fun n : ℕ => (1 : ℝ) / n) a := by
  rw [abel_identity A h0 N]
  have : (0 : ℝ) ≤ (cnt A N : ℝ) / (N + 1) := by positivity
  linarith

/-- The reciprocal sum is bounded by the Abel sum plus one. -/
theorem le_abel_sum_add_one (A : Set ℕ) (h0 : 0 ∉ A) (N : ℕ) :
    ∑ a ∈ Finset.range (N + 1), Set.indicator A (fun n : ℕ => (1 : ℝ) / n) a
      ≤ ∑ n ∈ Finset.range (N + 1), (cnt A n : ℝ) / (n * (n + 1)) + 1 := by
  rw [abel_identity A h0 N]
  have : (cnt A N : ℝ) / (N + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast cnt_le A N
  linarith

/-! ## PositiveDensity ⟹ ReciprocalDivergence -/

theorem cnt_primes (n : ℕ) : cnt {p | Nat.Prime p} n = primeCount n := by
  unfold cnt primeCount
  congr 1
  ext x
  simp

theorem cnt_appeared (n : ℕ) : cnt (Set.range Mullin.seq) n = emCount n := by
  unfold cnt emCount
  congr 1
  apply Finset.filter_congr
  intro p _
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨hk ▸ ((MullinGroup.isPrime_iff_natPrime _).mp (seq_isPrime k)), ⟨k, hk⟩⟩
  · exact fun h => h.2

theorem zero_not_prime' : (0 : ℕ) ∉ {p : ℕ | p.Prime} := Nat.not_prime_zero

theorem zero_not_appeared : (0 : ℕ) ∉ Set.range Mullin.seq := by
  rintro ⟨k, hk⟩
  exact Nat.not_prime_zero (hk ▸ (MullinGroup.isPrime_iff_natPrime _).mp (seq_isPrime k))

/-- `∑_k 1/seq k` summable ⟹ the indicator sum over the appeared primes is summable. -/
theorem summable_indicator_appeared (h : Summable (fun k : ℕ => (1 : ℝ) / Mullin.seq k)) :
    Summable (Set.indicator (Set.range Mullin.seq) (fun n : ℕ => (1 : ℝ) / n)) := by
  have hinj : Function.Injective Mullin.seq := fun _ _ h => seq_injective _ _ h
  rw [← Function.Injective.summable_iff hinj (fun n hn => Set.indicator_of_notMem hn _)]
  exact h.congr (fun k => by
    simp only [Function.comp, Set.indicator_of_mem (Set.mem_range_self (f := Mullin.seq) k)])

/-- **PositiveDensity ⟹ ReciprocalDivergence.**  If `S(n) ≥ c π(n)` for `n ≥ n₀`, Abel
summation gives `∑_{p ≤ N} 1/p ≤ C + (1/c) ∑_{p ∈ S, p ≤ N} 1/p`, so a convergent EM
reciprocal sum would make `∑_p 1/p` converge. -/
theorem rd_of_positiveDensity (h : PositiveDensity) : ReciprocalDivergence := by
  intro hsum
  have hS := summable_indicator_appeared hsum
  obtain ⟨c, hc, hev⟩ := h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  set fS := Set.indicator (Set.range Mullin.seq) (fun n : ℕ => (1 : ℝ) / n)
  set fP := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n)
  have hfS_nonneg : ∀ n, 0 ≤ fS n := fun n => Set.indicator_nonneg (fun _ _ => by positivity) _
  have hfP_nonneg : ∀ n, 0 ≤ fP n := fun n => Set.indicator_nonneg (fun _ _ => by positivity) _
  -- constant absorbing the first `n₀` terms
  set C₀ : ℝ := ∑ n ∈ Finset.range n₀, (primeCount n : ℝ) / (n * (n + 1))
  apply not_summable_one_div_on_primes
  apply summable_of_sum_range_le hfP_nonneg (c := C₀ + (∑' n, fS n) / c + 1)
  intro N
  -- pass from `range N` to `range (N + 1)`
  have hmono : ∑ i ∈ Finset.range N, fP i ≤ ∑ i ∈ Finset.range (N + 1), fP i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ N))
      (fun i _ _ => hfP_nonneg i)
  refine hmono.trans ?_
  refine (le_abel_sum_add_one {p : ℕ | p.Prime} zero_not_prime' N).trans ?_
  -- termwise bound on the Abel sum for the primes
  have hterm : ∀ n ∈ Finset.range (N + 1),
      (cnt {p : ℕ | p.Prime} n : ℝ) / (n * (n + 1))
        ≤ (if n < n₀ then (primeCount n : ℝ) / (n * (n + 1)) else 0)
          + (cnt (Set.range Mullin.seq) n : ℝ) / (n * (n + 1)) / c := by
    intro n _
    rw [cnt_primes, cnt_appeared]
    have hpos : (0 : ℝ) ≤ (emCount n : ℝ) / (n * (n + 1)) / c := by positivity
    split_ifs with hn
    · linarith
    · push Not at hn
      have := hn₀ n hn
      rw [zero_add]
      rcases Nat.eq_zero_or_pos n with rfl | hn'
      · simp
      · have hD : (0 : ℝ) < n * (n + 1) := by
          have : (0 : ℝ) < n := by exact_mod_cast hn'
          positivity
        rw [div_div, div_le_div_iff₀ hD (mul_pos hD hc)]
        calc (primeCount n : ℝ) * (n * (n + 1) * c) = (c * primeCount n) * (n * (n + 1)) := by ring
          _ ≤ emCount n * (n * (n + 1)) := by gcongr
  calc ∑ n ∈ Finset.range (N + 1), (cnt {p : ℕ | p.Prime} n : ℝ) / (n * (n + 1)) + 1
      ≤ ∑ n ∈ Finset.range (N + 1),
          ((if n < n₀ then (primeCount n : ℝ) / (n * (n + 1)) else 0)
            + (cnt (Set.range Mullin.seq) n : ℝ) / (n * (n + 1)) / c) + 1 := by
        gcongr with n hn
        exact hterm n hn
    _ = ∑ n ∈ Finset.range (N + 1), (if n < n₀ then (primeCount n : ℝ) / (n * (n + 1)) else 0)
          + (∑ n ∈ Finset.range (N + 1), (cnt (Set.range Mullin.seq) n : ℝ) / (n * (n + 1))) / c + 1 := by
        rw [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ C₀ + (∑' n, fS n) / c + 1 := by
        gcongr
        · -- the truncated sum is at most `C₀`
          rw [← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            rw [Finset.mem_filter] at hn
            exact Finset.mem_range.mpr hn.2
          · intro n _ _; positivity
        · exact (abel_sum_le (Set.range Mullin.seq) zero_not_appeared N).trans
            (hS.sum_le_tsum _ (fun n _ => hfS_nonneg n))

/-- **The coverage ladder.**  `MC ⟹ MissingFinite ⟹ MissingDensityZero ⟹ PositiveDensity ⟹ RD`. -/
theorem coverage_ladder :
    (MullinConjecture → MissingFinite) ∧ (MissingFinite → MissingDensityZero) ∧
    (MissingDensityZero → PositiveDensity) ∧ (PositiveDensity → ReciprocalDivergence) :=
  ⟨mc_implies_missing_finite, missingDensityZero_of_missingFinite,
    positiveDensity_of_missingDensityZero, rd_of_positiveDensity⟩

end CoverageLadder

end
