import EM.Population.GrowingRange
import EM.Population.HeadDynamics

/-!
# The head of a seeded orbit: the seed-average law re-indexed by the head

Session 2026-09-02.  `HeadDynamics` introduced the **head** of the Euclid–Mullin sequence, the
least prime not yet selected, and showed MC ⟺ head → ∞.  This file does the same for the seeded
greedy orbits `genProd m` of `EM/Ensemble/GenEM.lean` and re-expresses the seed-average law in
head coordinates.

## 1. The head of a seed

`head m n` is the least prime not dividing `genProd m n` (the bag of seed `m` at stage `n` is
the set of primes dividing the accumulator, so it contains the primes of `m` itself).  It is
nondecreasing in `n`, and

* `GenMullinConjecture m ⟺ head m → ∞` (`genMC_iff_head_tendsto`);
* `head m` is bounded by `Q` iff some prime `q ≤ Q` is missed by the orbit
  (`exists_misses_of_head_le`, `head_le_of_misses`).

## 2. The seed-average law in head coordinates

* `head_stage_density`: for every `Q` and `ε` there is one horizon `n` and one threshold `X₀`
  such that for all `X ≥ X₀` the seeds `m ≤ X` with `head m n ≤ Q` number at most `ε X` —
  *at a fixed late stage the head exceeds `Q` for almost all seeds*.  (From
  `AlmostAllDensity.finite_simultaneous_density`.)
* `head_bounded_density`: the seeds whose head stays `≤ Q` forever have density `0`.
* `head_growing_range`: there is a nondecreasing `Q → ∞` such that the seeds `m` whose head
  stays `≤ Q m` forever have density `0` (from `GrowingRange.seed_range_never_density`).

## 3. §G in head coordinates, and the exact missing input

`HeadEscapesAA` := the seeds whose head does *not* tend to infinity have density `0`; this is
the simultaneous-in-`q` law §G (`headEscapesAA_iff_almostAllGenMC`).  Write

    StallTail := ∀ δ > 0, ∃ Q X₀, ∀ X ≥ X₀,  #{m ≤ X : the head of m stalls at a prime > Q} ≤ δ X,

the head form of the thresholded input "(N2′)" of the §G scoping.  Then

    HeadEscapesAA ⟺ StallTail                         (`headEscapesAA_iff_stallTail`):

the finite part (`head ≤ Q`) is free by `head_bounded_density`, so §G is *exactly* the statement
that a head which has passed `Q` rarely stalls afterwards.  Nothing is gained or lost in the
translation; what is gained is that the missing input is now a statement about one monotone
quantity.

## 4. What an *effective* excursion tail can and cannot give

* `effective_range`: if the per-range thresholds of the seed-average law are bounded by an
  explicit monotone `G` (`X ≥ G K` suffices for the range `K`), then the growing range can be
  taken `Q X ≥ G⁻¹(X)`, i.e. `K ≤ Q X` whenever `G K ≤ X` (`head_effective_range` is the head
  form).  This is the honest output of an effective excursion tail: an *effective growing
  range*, not §G.
* `allScaleTail_cofinite_mc`: a per-prime tail bound `#{m ≤ X : m misses q} ≤ f(q) X` valid
  at **all scales** `X`, with `f` having small tails, implies that the Euclid–Mullin sequence
  contains every sufficiently large prime.  So an effective tail summable in `q` and uniform in
  the scale is at least as strong as cofinite MC for the orbit of `2`: the route "effective
  tails ⟹ Borel–Cantelli ⟹ §G" is closed, not merely hard (this sharpens dead end #176 from
  the (N2) shape to the tail shape).

`scaleUniformTail_without_primality_false` records why the predicate `ScaleUniformTail` must
quantify over *primes*: without primality every composite `q > X` is "missed" by every seed
`m ≤ X`, and the predicate is false outright.

**Scope.**  Population statements only; nothing here constrains any single seed.
-/

noncomputable section
open Classical Filter

namespace SeedHead

open GrowingRange (Misses badSet)

/-! ## 1. The head of a seed -/

/-- A prime divides the accumulator at stage `n` iff it divides the seed or was selected at some
earlier stage. -/
theorem prime_dvd_genProd_iff {m q : ℕ} (hm : 1 ≤ m) (hq : q.Prime) (n : ℕ) :
    q ∣ genProd m n ↔ q ∣ m ∨ ∃ j < n, genSeq m j = q := by
  induction n with
  | zero => simp [show genProd m 0 = m from rfl]
  | succ n ih =>
    rw [genProd_succ, hq.dvd_mul, ih]
    constructor
    · rintro ((h | ⟨j, hj, hjq⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, hjq⟩
      · exact Or.inr ⟨n, Nat.lt_succ_self n,
          ((Nat.prime_dvd_prime_iff_eq hq (genSeq_prime hm n)).mp h).symm⟩
    · rintro (h | ⟨j, hj, hjq⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact Or.inl (Or.inr ⟨j, hj, hjq⟩)
        · exact Or.inr (hjq ▸ dvd_refl _)

theorem genProd_dvd_genProd_of_le (m : ℕ) {a b : ℕ} (h : a ≤ b) :
    genProd m a ∣ genProd m b := by
  induction b, h using Nat.le_induction with
  | base => exact dvd_rfl
  | succ b _ ih => exact ih.trans (dvd_mul_right _ _)

/-- `q` is missing for seed `m` at stage `n`: a prime not dividing the accumulator. -/
def Missing (m n q : ℕ) : Prop := q.Prime ∧ ¬ q ∣ genProd m n

theorem missing_of_le {m n n' q : ℕ} (h : n ≤ n') (hq : Missing m n' q) : Missing m n q :=
  ⟨hq.1, fun hd => hq.2 (hd.trans (genProd_dvd_genProd_of_le m h))⟩

theorem exists_missing {m : ℕ} (hm : 1 ≤ m) (n : ℕ) : ∃ q, Missing m n q := by
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (genProd m n + 1)
  refine ⟨p, hpp, fun h => ?_⟩
  have := Nat.le_of_dvd (genProd_pos hm n) h
  omega

/-- The head of seed `m` at stage `n`: the least prime not dividing `genProd m n`
(`0` for the degenerate seed `0`). -/
def head (m n : ℕ) : ℕ := if h : ∃ q, Missing m n q then Nat.find h else 0

theorem head_missing {m : ℕ} (hm : 1 ≤ m) (n : ℕ) : Missing m n (head m n) := by
  unfold head
  rw [dif_pos (exists_missing hm n)]
  exact Nat.find_spec (exists_missing hm n)

theorem head_prime {m : ℕ} (hm : 1 ≤ m) (n : ℕ) : (head m n).Prime := (head_missing hm n).1

theorem head_le {m n q : ℕ} (h : Missing m n q) : head m n ≤ q := by
  unfold head
  rw [dif_pos ⟨q, h⟩]
  exact Nat.find_min' _ h

theorem head_monotone {m : ℕ} (hm : 1 ≤ m) : Monotone (head m) :=
  fun _ _ hab => head_le (missing_of_le hab (head_missing hm _))

/-- The head exceeds `Q` iff every prime `≤ Q` is in the bag. -/
theorem lt_head_iff {m n Q : ℕ} (hm : 1 ≤ m) :
    Q < head m n ↔ ∀ q, q.Prime → q ≤ Q → q ∣ genProd m n := by
  constructor
  · intro h q hq hqQ
    by_contra hnd
    have := head_le ⟨hq, hnd⟩
    omega
  · intro h
    by_contra hle
    have hmiss := head_missing hm n
    exact hmiss.2 (h _ hmiss.1 (not_lt.mp hle))

theorem head_le_iff {m n Q : ℕ} (hm : 1 ≤ m) :
    head m n ≤ Q ↔ ∃ q, q.Prime ∧ q ≤ Q ∧ ¬ q ∣ genProd m n := by
  constructor
  · intro h
    exact ⟨head m n, (head_missing hm n).1, h, (head_missing hm n).2⟩
  · rintro ⟨q, hq, hqQ, hnd⟩
    exact (head_le ⟨hq, hnd⟩).trans hqQ

/-- A missed prime is missing at every stage, and conversely. -/
theorem misses_iff_forall_missing {m q : ℕ} (hm : 1 ≤ m) (hq : q.Prime) :
    Misses q m ↔ ∀ n, Missing m n q := by
  constructor
  · rintro ⟨hnd, hnever⟩ n
    refine ⟨hq, fun hd => ?_⟩
    rcases (prime_dvd_genProd_iff hm hq n).mp hd with h | ⟨k, _, hk⟩
    · exact hnd h
    · exact hnever k hk
  · intro h
    refine ⟨fun hd => (h 0).2 hd, fun k hk => (h (k + 1)).2 ?_⟩
    exact (prime_dvd_genProd_iff hm hq _).mpr (Or.inr ⟨k, Nat.lt_succ_self k, hk⟩)

theorem head_le_of_misses {m q : ℕ} (hm : 1 ≤ m) (hq : q.Prime) (h : Misses q m) (n : ℕ) :
    head m n ≤ q :=
  head_le ((misses_iff_forall_missing hm hq).mp h n)

/-- **A bounded head is a missed prime.**  If the head of seed `m` never exceeds `Q`, some prime
`q ≤ Q` is missed by the orbit (the eventual value of the head). -/
theorem exists_misses_of_head_le {m Q : ℕ} (hm : 1 ≤ m) (h : ∀ n, head m n ≤ Q) :
    ∃ q, q.Prime ∧ q ≤ Q ∧ Misses q m := by
  have hex : ∃ B, ∀ n, head m n ≤ B := ⟨Q, h⟩
  set B := Nat.find hex with hB
  have hspec : ∀ n, head m n ≤ B := Nat.find_spec hex
  have hBQ : B ≤ Q := Nat.find_min' hex h
  -- the minimal bound is attained at some stage `N`
  have hpos : 1 ≤ B := by
    have := (head_prime hm 0).two_le
    have := hspec 0
    omega
  have hmin : ¬ ∀ n, head m n ≤ B - 1 := Nat.find_min hex (by omega)
  push Not at hmin
  obtain ⟨N, hN⟩ := hmin
  have hNB : head m N = B := by have := hspec N; omega
  refine ⟨B, hNB ▸ head_prime hm N, hBQ, (misses_iff_forall_missing hm (hNB ▸ head_prime hm N)).mpr
    fun n => ?_⟩
  rcases le_or_gt n N with hn | hn
  · exact missing_of_le hn (hNB ▸ head_missing hm N)
  · have h1 := head_monotone hm hn.le
    have h2 := hspec n
    have : head m n = B := by omega
    exact this ▸ head_missing hm n

/-- **`GenMC` in head coordinates**: the generalised conjecture for seed `m` holds iff the head
of `m` tends to infinity. -/
theorem genMC_iff_head_tendsto {m : ℕ} (hm : 1 ≤ m) :
    GenMullinConjecture m ↔ Tendsto (head m) atTop atTop := by
  constructor
  · intro h
    rw [tendsto_atTop_atTop]
    intro B
    have hstage : ∀ q, q.Prime → q ≤ B → ∃ n, q ∣ genProd m n := by
      intro q hq _
      by_cases hd : q ∣ m
      · exact ⟨0, hd⟩
      · obtain ⟨k, hk⟩ := h q hq hd
        exact ⟨k + 1, (prime_dvd_genProd_iff hm hq _).mpr (Or.inr ⟨k, Nat.lt_succ_self k, hk⟩)⟩
    choose! st hst using hstage
    refine ⟨(Finset.range (B + 1)).sup st, fun n hn => ?_⟩
    have : B < head m n := (lt_head_iff hm).mpr fun q hq hqB =>
      (hst q hq hqB).trans (genProd_dvd_genProd_of_le m
        (le_trans (Finset.le_sup (f := st) (Finset.mem_range.mpr (by omega))) hn))
    omega
  · intro h q hq hnd
    by_contra hno
    push Not at hno
    have hmiss : Misses q m := ⟨hnd, hno⟩
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp h (q + 1)
    have := head_le_of_misses hm hq hmiss N
    have := hN N le_rfl
    omega

/-- The failure set of `GenMC` is the set of seeds missing some prime. -/
theorem not_genMC_iff_exists_misses {m : ℕ} :
    ¬ GenMullinConjecture m ↔ ∃ q, q.Prime ∧ Misses q m := by
  unfold GenMullinConjecture Misses
  constructor
  · intro h
    push Not at h
    obtain ⟨q, hq, hnd, hno⟩ := h
    exact ⟨q, hq, hnd, hno⟩
  · rintro ⟨q, hq, hnd, hno⟩ h
    obtain ⟨k, hk⟩ := h q hq hnd
    exact hno k hk

/-! ## 2. The seed-average law in head coordinates -/

/-- A seed whose head at stage `n` is `≤ K` lies in the growing-range bad set. -/
theorem mem_badSet_of_head_le {X K n m : ℕ} (hmX : m ∈ Finset.Icc 1 X) (h : head m n ≤ K) :
    m ∈ badSet X K n := by
  have hm : 1 ≤ m := (Finset.mem_Icc.mp hmX).1
  obtain ⟨q, hq, hqK, hnd⟩ := (head_le_iff hm).mp h
  rw [prime_dvd_genProd_iff hm hq] at hnd
  push Not at hnd
  simp only [badSet, Finset.mem_filter]
  exact ⟨hmX, q, hqK, hq, hnd.1, fun ⟨j, hj, hjq⟩ => hnd.2 j hj hjq⟩

/-- **The head exceeds `Q` at a fixed late stage, for almost all seeds.**  For every `Q` and
`ε > 0` there are one horizon `n` and one threshold `X₀` such that for all `X ≥ X₀` the seeds
`m ≤ X` with `head m n ≤ Q` number at most `ε X`. -/
theorem head_stage_density (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n X₀ : ℕ, ∀ X, X₀ ≤ X →
      (((Finset.Icc 1 X).filter (fun m => head m n ≤ Q)).card : ℝ) ≤ ε * (X : ℝ) := by
  obtain ⟨n, X₀, h⟩ := AlmostAllDensity.finite_simultaneous_density
    ((Finset.range (Q + 1)).filter Nat.Prime) (fun q hq => (Finset.mem_filter.mp hq).2) hε
  refine ⟨n, X₀, fun X hX => le_trans ?_ (h X hX)⟩
  refine (Nat.cast_le.mpr (Finset.card_le_card fun m hm => ?_))
  have hmX := (Finset.mem_filter.mp hm).1
  have hb := mem_badSet_of_head_le hmX (Finset.mem_filter.mp hm).2
  simp only [badSet, Finset.mem_filter, Finset.mem_range] at hb ⊢
  obtain ⟨_, q, hqQ, hq, hnd, hno⟩ := hb
  exact ⟨hmX, q, ⟨by omega, hq⟩, hnd, hno⟩

/-- **A bounded head has density zero.**  The seeds whose head never exceeds `Q` have natural
density `0`. -/
theorem head_bounded_density (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      (((Finset.Icc 1 X).filter (fun m => ∀ n, head m n ≤ Q)).card : ℝ) ≤ ε * (X : ℝ) := by
  obtain ⟨n, X₀, h⟩ := head_stage_density Q hε
  refine ⟨X₀, fun X hX => le_trans ?_ (h X hX)⟩
  exact Nat.cast_le.mpr (Finset.card_le_card fun m hm => by
    simp only [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, hm.2 n⟩)

/-- **The growing range in head coordinates.**  There is a nondecreasing `Q → ∞` such that the
seeds `m` whose head never exceeds `Q m` have natural density `0`. -/
theorem head_growing_range : ∃ Q : ℕ → ℕ, Monotone Q ∧ Tendsto Q atTop atTop ∧
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      (((Finset.Icc 1 X).filter (fun m => ∀ n, head m n ≤ Q m)).card : ℝ) ≤ ε * (X : ℝ) := by
  obtain ⟨Q, hQ, hQt, h⟩ := GrowingRange.seed_range_never_density
  refine ⟨Q, hQ, hQt, fun ε hε => ?_⟩
  obtain ⟨X₀, hX₀⟩ := h ε hε
  refine ⟨X₀, fun X hX => le_trans ?_ (hX₀ X hX)⟩
  refine Nat.cast_le.mpr (Finset.card_le_card fun m hm => ?_)
  simp only [Finset.mem_filter] at hm ⊢
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm.1).1
  obtain ⟨q, hq, hqQ, hnd, hno⟩ := exists_misses_of_head_le hm1 hm.2
  exact ⟨hm.1, q, hqQ, hq, hnd, hno⟩

/-! ## 3. §G in head coordinates -/

/-- **§G in head coordinates**: the seeds whose head does not tend to infinity have density
`0`. -/
def HeadEscapesAA : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
    (((Finset.Icc 1 X).filter (fun m => ¬ Tendsto (head m) atTop atTop)).card : ℝ)
      ≤ ε * (X : ℝ)

/-- The simultaneous-in-`q` seed-average law: the seeds failing `GenMC` have density `0`. -/
def AlmostAllGenMC : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
    (((Finset.Icc 1 X).filter (fun m => ¬ GenMullinConjecture m)).card : ℝ) ≤ ε * (X : ℝ)

/-- The thresholded tail input "(N2′)", in head form: for every `δ` there are `Q` and `X₀` such
that for all `X ≥ X₀` the seeds `m ≤ X` missing some prime `> Q` number at most `δ X`. -/
def StallTail : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ Q X₀ : ℕ, ∀ X, X₀ ≤ X →
    (((Finset.Icc 1 X).filter (fun m => ∃ q, Q < q ∧ q.Prime ∧ Misses q m)).card : ℝ)
      ≤ δ * (X : ℝ)

theorem headEscapesAA_iff_almostAllGenMC : HeadEscapesAA ↔ AlmostAllGenMC := by
  have hset : ∀ X : ℕ, (Finset.Icc 1 X).filter (fun m => ¬ Tendsto (head m) atTop atTop) =
      (Finset.Icc 1 X).filter (fun m => ¬ GenMullinConjecture m) := by
    intro X
    apply Finset.filter_congr
    intro m hm
    rw [genMC_iff_head_tendsto (Finset.mem_Icc.mp hm).1]
  constructor
  · intro h ε hε
    obtain ⟨X₀, hX₀⟩ := h ε hε
    exact ⟨X₀, fun X hX => by rw [← hset]; exact hX₀ X hX⟩
  · intro h ε hε
    obtain ⟨X₀, hX₀⟩ := h ε hε
    exact ⟨X₀, fun X hX => by rw [hset]; exact hX₀ X hX⟩

/-- **§G ⟺ the stall tail.**  The finite part of §G (the head stays `≤ Q`) has density `0`
unconditionally, so §G is exactly the statement that a head which has passed `Q` rarely stalls
afterwards. -/
theorem headEscapesAA_iff_stallTail : HeadEscapesAA ↔ StallTail := by
  constructor
  · intro h δ hδ
    obtain ⟨X₀, hX₀⟩ := h δ hδ
    refine ⟨0, X₀, fun X hX => le_trans ?_ (hX₀ X hX)⟩
    refine Nat.cast_le.mpr (Finset.card_le_card fun m hm => ?_)
    simp only [Finset.mem_filter] at hm ⊢
    obtain ⟨hmX, q, _, hq, hmiss⟩ := hm
    refine ⟨hmX, fun ht => ?_⟩
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmX).1
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp ht (q + 1)
    have := head_le_of_misses hm1 hq hmiss N
    have := hN N le_rfl
    omega
  · intro h ε hε
    have hε2 : (0 : ℝ) < ε / 2 := by positivity
    obtain ⟨Q, X₁, hX₁⟩ := h (ε / 2) hε2
    obtain ⟨X₂, hX₂⟩ := head_bounded_density Q hε2
    refine ⟨max X₁ X₂, fun X hX => ?_⟩
    have h1 := hX₁ X (le_trans (le_max_left _ _) hX)
    have h2 := hX₂ X (le_trans (le_max_right _ _) hX)
    set A := (Finset.Icc 1 X).filter (fun m => ∀ n, head m n ≤ Q)
    set B := (Finset.Icc 1 X).filter (fun m => ∃ q, Q < q ∧ q.Prime ∧ Misses q m)
    have hsub : (Finset.Icc 1 X).filter (fun m => ¬ Tendsto (head m) atTop atTop) ⊆ A ∪ B := by
      intro m hm
      simp only [Finset.mem_filter] at hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm.1).1
      have hnot : ¬ GenMullinConjecture m := fun hg => hm.2 ((genMC_iff_head_tendsto hm1).mp hg)
      obtain ⟨q, hq, hmiss⟩ := not_genMC_iff_exists_misses.mp hnot
      rw [Finset.mem_union]
      rcases le_or_gt q Q with hqQ | hqQ
      · exact Or.inl (Finset.mem_filter.mpr ⟨hm.1, fun n =>
          (head_le_of_misses hm1 hq hmiss n).trans hqQ⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨hm.1, q, hqQ, hq, hmiss⟩)
    calc (((Finset.Icc 1 X).filter (fun m => ¬ Tendsto (head m) atTop atTop)).card : ℝ)
        ≤ ((A ∪ B).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast Finset.card_union_le A B
      _ ≤ ε / 2 * (X : ℝ) + ε / 2 * (X : ℝ) := add_le_add h2 h1
      _ = ε * (X : ℝ) := by ring

/-! ## 4. Effective tails: what they can and cannot give -/

/-- **Effective growing range.**  If the per-range thresholds are bounded by an explicit
nondecreasing `G` with `K ≤ G K`, then the growing range can be taken as (at least) the inverse
of `G`: `K ≤ Q X` whenever `G K ≤ X`. -/
theorem effective_range {G : ℕ → ℕ} (hid : ∀ K, K ≤ G K)
    (hper : ∀ K, ∃ n, ∀ X, G K ≤ X →
      ((badSet X K n).card : ℝ) ≤ (X : ℝ) / ((K : ℝ) + 1)) :
    ∃ Q N : ℕ → ℕ, Monotone Q ∧ (∀ K X, G K ≤ X → K ≤ Q X) ∧
      ∀ X, G 0 ≤ X → ((badSet X (Q X) (N X)).card : ℝ) ≤ (X : ℝ) / ((Q X : ℝ) + 1) := by
  choose n hn using hper
  let S : ℕ → Finset ℕ := fun X => (Finset.range (X + 1)).filter (fun K => G K ≤ X)
  let Q : ℕ → ℕ := fun X => (S X).sup id
  have hmemS : ∀ K X, G K ≤ X → K ∈ S X := by
    intro K X h
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hid K; omega, h⟩
  have hSmono : ∀ {X X'}, X ≤ X' → S X ⊆ S X' := by
    intro X X' h K hK
    simp only [S, Finset.mem_filter, Finset.mem_range] at hK ⊢
    exact ⟨by omega, le_trans hK.2 h⟩
  have hQmono : Monotone Q := fun X X' h => Finset.sup_mono (hSmono h)
  have hQge : ∀ K X, G K ≤ X → K ≤ Q X := fun K X h =>
    Finset.le_sup (f := id) (hmemS K X h)
  have hQadm : ∀ X, G 0 ≤ X → G (Q X) ≤ X := by
    intro X hX
    obtain ⟨K, hKS, hK⟩ := Finset.exists_mem_eq_sup (S X) ⟨0, hmemS 0 X hX⟩ id
    have hK' : Q X = K := hK
    rw [hK']
    exact (Finset.mem_filter.mp hKS).2
  exact ⟨Q, fun X => n (Q X), hQmono, hQge, fun X hX => hn (Q X) X (hQadm X hX)⟩

/-- The head form of `effective_range`: for `X ≥ G 0`, the seeds `m ≤ X` whose head at stage
`N X` is `≤ Q X` number at most `X / (Q X + 1)`, with `Q X ≥ G⁻¹(X)`. -/
theorem head_effective_range {G : ℕ → ℕ} (hid : ∀ K, K ≤ G K)
    (hper : ∀ K, ∃ n, ∀ X, G K ≤ X →
      ((badSet X K n).card : ℝ) ≤ (X : ℝ) / ((K : ℝ) + 1)) :
    ∃ Q N : ℕ → ℕ, Monotone Q ∧ (∀ K X, G K ≤ X → K ≤ Q X) ∧
      ∀ X, G 0 ≤ X →
        (((Finset.Icc 1 X).filter (fun m => head m (N X) ≤ Q X)).card : ℝ)
          ≤ (X : ℝ) / ((Q X : ℝ) + 1) := by
  obtain ⟨Q, N, hQ, hQge, h⟩ := effective_range hid hper
  refine ⟨Q, N, hQ, hQge, fun X hX => le_trans ?_ (h X hX)⟩
  exact Nat.cast_le.mpr (Finset.card_le_card fun m hm =>
    mem_badSet_of_head_le (Finset.mem_filter.mp hm).1 (Finset.mem_filter.mp hm).2)

/-- A per-prime tail bound valid at **all scales**: for every prime `q` and every `X`, the seeds
`m ≤ X` missing `q` number at most `f q · X`. -/
def AllScaleTail (f : ℕ → ℝ) : Prop :=
  ∀ q, q.Prime → ∀ X : ℕ,
    (((Finset.Icc 1 X).filter (fun m => Misses q m)).card : ℝ) ≤ f q * (X : ℝ)

/-- `f` has small tails: for every `δ > 0` there is `Q` with `∑_{q ∈ T} f q ≤ δ` for every finite
`T` of indices `> Q` (for nonnegative `f` this is summability). -/
def TailSmall (f : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ Q : ℕ, ∀ T : Finset ℕ, (∀ q ∈ T, Q < q) → ∑ q ∈ T, f q ≤ δ

/-- An all-scale tail with small tails yields the scale-uniform tail bound (N2). -/
theorem scaleUniformTail_of_allScaleTail {f : ℕ → ℝ} (hT : TailSmall f) (h : AllScaleTail f) :
    GrowingRange.ScaleUniformTail := by
  intro δ hδ
  obtain ⟨Q, hQ⟩ := hT δ hδ
  refine ⟨Q, fun X => ?_⟩
  set U := (Finset.Icc 1 X).filter (fun m => ∃ q, Q < q ∧ q.Prime ∧ Misses q m) with hU
  have hw : ∀ m ∈ U, ∃ q, Q < q ∧ q.Prime ∧ Misses q m := fun m hm => (Finset.mem_filter.mp hm).2
  choose! w hw using hw
  have hcard : U.card = ∑ q ∈ U.image w, (U.filter (fun m => w m = q)).card :=
    Finset.card_eq_sum_card_image w U
  have hfiber : ∀ q ∈ U.image w,
      ((U.filter (fun m => w m = q)).card : ℝ) ≤ f q * (X : ℝ) := by
    intro q hq
    obtain ⟨m₀, hm₀, rfl⟩ := Finset.mem_image.mp hq
    refine le_trans ?_ (h _ (hw m₀ hm₀).2.1 X)
    refine Nat.cast_le.mpr (Finset.card_le_card fun m hm => ?_)
    simp only [Finset.mem_filter] at hm ⊢
    exact ⟨(Finset.mem_filter.mp hm.1).1, hm.2 ▸ (hw m hm.1).2.2⟩
  have hgt : ∀ q ∈ U.image w, Q < q := by
    intro q hq
    obtain ⟨m₀, hm₀, rfl⟩ := Finset.mem_image.mp hq
    exact (hw m₀ hm₀).1
  calc (U.card : ℝ) = ∑ q ∈ U.image w, ((U.filter (fun m => w m = q)).card : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ ≤ ∑ q ∈ U.image w, f q * (X : ℝ) := Finset.sum_le_sum hfiber
    _ = (∑ q ∈ U.image w, f q) * (X : ℝ) := by rw [Finset.sum_mul]
    _ ≤ δ * (X : ℝ) := by
        gcongr
        exact hQ _ hgt

/-- **Effective tails cannot reach §G without MC-strength input.**  A per-prime tail bound
valid at all scales, summable in the prime, implies that the Euclid–Mullin sequence contains
every sufficiently large prime. -/
theorem allScaleTail_cofinite_mc {f : ℕ → ℝ} (hT : TailSmall f) (h : AllScaleTail f) :
    ∃ Q : ℕ, ∀ q, Q < q → q.Prime → ∃ k, Mullin.seq k = q :=
  GrowingRange.scaleUniformTail_cofinite_mc (scaleUniformTail_of_allScaleTail hT h)

/-- Without the primality restriction the scale-uniform tail predicate is false outright: a
composite `q > X` is "missed" by every seed `m ≤ X`. -/
theorem scaleUniformTail_without_primality_false :
    ¬ (∀ δ : ℝ, 0 < δ → ∃ Q : ℕ, ∀ X : ℕ,
      (((Finset.Icc 1 X).filter (fun m => ∃ q, Q < q ∧ Misses q m)).card : ℝ) ≤ δ * (X : ℝ)) := by
  intro h
  obtain ⟨Q, hQ⟩ := h (1 / 2) (by norm_num)
  have h1 := hQ 1
  rw [Nat.cast_one, mul_one] at h1
  -- the seed `1` misses the composite `2 * (Q + 2) > Q`
  have hmiss : Misses (2 * (Q + 2)) 1 := by
    refine ⟨fun hd => ?_, fun k hk => ?_⟩
    · have := Nat.le_of_dvd one_pos hd
      omega
    · have hp := genSeq_prime (le_refl 1) k
      rw [hk] at hp
      exact Nat.not_prime_mul (a := 2) (b := Q + 2) (by norm_num) (by omega) hp
  have hmem : (1 : ℕ) ∈ (Finset.Icc 1 1).filter (fun m => ∃ q, Q < q ∧ Misses q m) :=
    Finset.mem_filter.mpr ⟨by simp, 2 * (Q + 2), by omega, hmiss⟩
  have hcard : (1 : ℝ) ≤ (((Finset.Icc 1 1).filter
      (fun m => ∃ q, Q < q ∧ Misses q m)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, hmem⟩
  linarith

end SeedHead
