import EM.Population.SeedCapture
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Large-step roughness: box bookkeeping, the charge budget, and the brink

This file is the first slice of the deterministic core of the **(LS)** estimate
of the seed-average program (Groups 1-3 of the verified statement list,
`agents/state/findings_ls_verification.md` §4).  Everything here is *pathwise*
and *finitary*: no densities, no limits, no probability.

Throughout we work with the `q`-free greedy dynamics of `EM/Population/SeedCapture.lean`,
writing `p̃(k) = genSeqAvoid q m k` for the multiplier at step `k` and
`c(k) = seedCofactorAvoid q m k` for the cofactor, so that
`genProdAvoid q m k = m * c(k)`.

Fix an auxiliary prime `r ≠ q` (correction **C2** of the verification: the
avoided prime `q` must be excluded from *every* charge, sum and box, because the
brink lemma `brink_forces_small_multiplier` is simply **false** at `r = q` — the
`q`-free dynamics ignores `q` entirely).

## The box process

Step `j` is *`r`-exposed* if `r < p̃(j)`: the prime `r` was available and was
declined.  `visitedAt q m r k` collects the residues `c(j) mod r` over the
`r`-exposed steps `j < k`.  The **box**

```
box q m r k = (ZMod r)ˣ  \  { -v⁻¹ : v ∈ visitedAt q m r k }
```

is the set of unit residues of the seed that are *still compatible* with the
observed history: `m mod r` lies in the box (`seed_mem_box`), because at each
exposed step `j` one has `r ∤ m·c(j) + 1`.

The prime `r` is **charged** at step `k` when it is active (not in the bag),
lands on a genuinely new cofactor residue, and is exposed.  Each charge shrinks
the box by exactly one element (`boxCard_succ_of_charged`), non-charges leave it
alone (`boxCard_of_not_charged`), and the box is never empty
(`boxCard_pos`).  Hence the **harmonic charge budget**

```
∑_{k < n, r charged at k} 1 / |box q m r k|  ≤  1 + 1/2 + ⋯ + 1/(r-1),
```

which is `charge_sum_le_harmonic` (F1e) — the key theorem of this slice.

## Distinctness and the brink

`genSeqAvoid_injOn` (F2b) says the multipliers of a nondegenerate `q`-free orbit
are pairwise distinct, whence `few_small_multipliers` (F2c): at most `π(N)` of
the first `n` steps can have multiplier `< N`.

`brink_forces_small_multiplier` (F3a) is the *brink lemma*: if the box of an
active prime `r ≠ q` has collapsed to a single element and the current cofactor
residue is new, then the seed residue is forced onto the death point, `r`
divides the current Euclid number, and consequently `p̃(k) ≤ r`.  This is what
converts "the box is about to die" into "the multiplier is small", i.e. into a
*non-good* step.
-/

noncomputable section
open Classical

namespace LargeStepRoughness

open SeedCapture SeedTypes

variable {q m r j k n : ℕ}

/-! ## 0.  The unit finset of `ZMod r`

`ZMod r` is a `Fintype` only for `r ≠ 0`, and `r` is a plain natural-number
parameter of all the definitions below, so we spell the unit set as an explicit
image of `Finset.range r` rather than as `Finset.univ.filter IsUnit`. -/

/-- The units of `ZMod r`, as an explicit `Finset` (junk for `r = 0`). -/
def unitFinset (r : ℕ) : Finset (ZMod r) :=
  ((Finset.range r).image (fun i : ℕ => (i : ZMod r))).erase 0

theorem mem_unitFinset (hr : r.Prime) {u : ZMod r} : u ∈ unitFinset r ↔ u ≠ 0 := by
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero r := ⟨hr.ne_zero⟩
  rw [unitFinset, Finset.mem_erase]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact Finset.mem_image.mpr ⟨u.val, Finset.mem_range.mpr (ZMod.val_lt u), by simp⟩

/-- Membership in `unitFinset r` in unit form. -/
theorem mem_unitFinset_isUnit (hr : r.Prime) {u : ZMod r} :
    u ∈ unitFinset r ↔ IsUnit u := by
  have : Fact r.Prime := ⟨hr⟩
  rw [mem_unitFinset hr, isUnit_iff_ne_zero]

/-- There are exactly `r - 1` units modulo a prime `r`. -/
theorem unitFinset_card (hr : r.Prime) : (unitFinset r).card = r - 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have : NeZero r := ⟨hr.ne_zero⟩
  have hset : unitFinset r = Finset.univ.erase (0 : ZMod r) := by
    ext u
    rw [mem_unitFinset hr, Finset.mem_erase]
    simp
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/-! ## 1.  The box process -/

/-- Residues of the cofactor at the `r`-exposed steps `j < k` of the `q`-free
orbit. -/
def visitedAt (q m r k : ℕ) : Finset (ZMod r) :=
  ((Finset.range k).filter (fun j => r < genSeqAvoid q m j)).image
    (fun j => ((seedCofactorAvoid q m j : ℕ) : ZMod r))

/-- `r` is in the bag at time `k`: it divides the seed, or it was already used
as a multiplier. -/
def inBag (q m r k : ℕ) : Prop := r ∣ m ∨ ∃ j < k, genSeqAvoid q m j = r

/-- The current cofactor residue is new modulo `r`. -/
def isNew (q m r k : ℕ) : Prop :=
  ((seedCofactorAvoid q m k : ℕ) : ZMod r) ∉ visitedAt q m r k

/-- The box: unit residues modulo `r` not yet excluded by an exposed step. -/
def box (q m r k : ℕ) : Finset (ZMod r) :=
  unitFinset r \ ((visitedAt q m r k).image (fun v => -v⁻¹))

/-- The size of the box. -/
def boxCard (q m r k : ℕ) : ℕ := (box q m r k).card

/-- `r` is *charged* at step `k`: it is active, the position is new, and the
step is `r`-exposed. -/
def Charged (q m r k : ℕ) : Prop :=
  ¬ inBag q m r k ∧ isNew q m r k ∧ r < genSeqAvoid q m k

/-! ### Structural glue -/

theorem mem_visitedAt {v : ZMod r} (hv : v ∈ visitedAt q m r k) :
    ∃ j, j < k ∧ r < genSeqAvoid q m j ∧
      ((seedCofactorAvoid q m j : ℕ) : ZMod r) = v := by
  rw [visitedAt, Finset.mem_image] at hv
  obtain ⟨j, hj, hveq⟩ := hv
  rw [Finset.mem_filter, Finset.mem_range] at hj
  exact ⟨j, hj.1, hj.2, hveq⟩

@[simp] theorem visitedAt_zero (q m r : ℕ) : visitedAt q m r 0 = ∅ := by
  simp [visitedAt]

/-- One-step growth of the visited set. -/
theorem visitedAt_succ (q m r k : ℕ) :
    visitedAt q m r (k + 1) =
      if r < genSeqAvoid q m k then
        insert ((seedCofactorAvoid q m k : ℕ) : ZMod r) (visitedAt q m r k)
      else visitedAt q m r k := by
  unfold visitedAt
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : r < genSeqAvoid q m k
  · simp [h, Finset.image_insert]
  · simp [h]

/-- The bag only grows. -/
theorem inBag_mono (hjk : j ≤ k) (h : inBag q m r j) : inBag q m r k := by
  rcases h with h | ⟨i, hi, hir⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, lt_of_lt_of_le hi hjk, hir⟩

theorem not_inBag_of_le (hjk : j ≤ k) (h : ¬ inBag q m r k) : ¬ inBag q m r j :=
  fun hj => h (inBag_mono hjk hj)

/-- **Cofactor coprimality.**  While `r` is out of the bag, no cofactor of the
`q`-free orbit is divisible by `r`: the multipliers so far are primes different
from `r`. -/
theorem cofactor_coprime_of_not_inBag (hr : r.Prime) (hbag : ¬ inBag q m r k)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) :
    ∀ j ≤ k, ¬ r ∣ seedCofactorAvoid q m j := by
  intro j hjk hdvd
  rw [seedCofactorAvoid] at hdvd
  obtain ⟨i, hi, hri⟩ := (hr.prime.dvd_finsetProd_iff _).mp hdvd
  have hik : i < k := lt_of_lt_of_le (Finset.mem_range.mp hi) hjk
  have hip : Nat.Prime (genSeqAvoid q m i) := genSeqAvoid_prime (hnd i hik)
  exact hbag (Or.inr ⟨i, hik, ((Nat.prime_dvd_prime_iff_eq hr hip).mp hri).symm⟩)

theorem cofactor_ne_zero_of_not_inBag (hr : r.Prime) (hbag : ¬ inBag q m r k)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) {j : ℕ} (hjk : j ≤ k) :
    ((seedCofactorAvoid q m j : ℕ) : ZMod r) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact cofactor_coprime_of_not_inBag hr hbag hnd j hjk

/-- Every visited residue is a nonzero residue while `r` is out of the bag. -/
theorem visitedAt_ne_zero (hr : r.Prime) (hbag : ¬ inBag q m r k)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) {v : ZMod r} (hv : v ∈ visitedAt q m r k) :
    v ≠ 0 := by
  obtain ⟨j, hj, _, hveq⟩ := mem_visitedAt hv
  rw [← hveq]
  exact cofactor_ne_zero_of_not_inBag hr hbag hnd (le_of_lt hj)

/-- **Lemma A for the `q`-free orbit.**  At an `r`-exposed step the prime
`r ≠ q` was available and declined, so it does not divide the current Euclid
number. -/
theorem not_dvd_succ_of_exposed_avoid (hq : q.Prime) (hm : 1 ≤ m) (hr : r.Prime)
    (hrq : r ≠ q) {j : ℕ} (hexp : r < genSeqAvoid q m j) :
    ¬ r ∣ genProdAvoid q m j + 1 := by
  intro hdvd
  have hN : genProdAvoid q m j + 1 ≠ 0 := by
    have := genProdAvoid_pos q hm j; omega
  have := minFac_qfreePart_least hq hN hr hrq hdvd
  rw [← genSeqAvoid_def] at this
  omega

/-! ### The seed sits in the box -/

/-- **Box positivity, mechanism.**  While `r` is active and does not divide the
seed, the residue `m mod r` lies in the box: it is a unit, and at every exposed
step `j < k` one has `r ∤ m·c(j) + 1`, i.e. `m mod r ≠ -c(j)⁻¹`. -/
theorem seed_mem_box (hq : q.Prime) (hm : 1 ≤ m) (hr : r.Prime) (hrq : r ≠ q)
    (hrm : ¬ r ∣ m) (hbag : ¬ inBag q m r k)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) :
    ((m : ℕ) : ZMod r) ∈ box q m r k := by
  have : Fact r.Prime := ⟨hr⟩
  have hm0 : ((m : ℕ) : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hrm
  refine Finset.mem_sdiff.mpr ⟨(mem_unitFinset hr).mpr hm0, ?_⟩
  intro hmem
  obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hmem
  obtain ⟨j, hj, hexp, hcv⟩ := mem_visitedAt hv
  have hv0 : v ≠ 0 := visitedAt_ne_zero hr hbag hnd hv
  have hhit : ((m : ℕ) : ZMod r) * v = -1 := (hit_iff_eq_neg_inv hr hv0).mpr hveq.symm
  rw [← hcv] at hhit
  have hdvd : r ∣ m * seedCofactorAvoid q m j + 1 := hit_iff_dvd.mp hhit
  rw [← genProdAvoid_eq_seed_mul_cofactor] at hdvd
  exact not_dvd_succ_of_exposed_avoid hq hm hr hrq hexp hdvd

/-! ## 2.  Group 1 — box bookkeeping

Verified statement list, `findings_ls_verification.md` §4, Group 1. -/

/-- **F1c.**  At time `0` nothing has been excluded, so the box is all of
`(ZMod r)ˣ`. -/
theorem boxCard_zero (hr : r.Prime) : boxCard q m r 0 = r - 1 := by
  simp [boxCard, box, unitFinset_card hr]

/-- The map `v ↦ -v⁻¹` is injective on `ZMod r` for `r` prime. -/
theorem neg_inv_injective (hr : r.Prime) :
    Function.Injective (fun v : ZMod r => -v⁻¹) := by
  have : Fact r.Prime := ⟨hr⟩
  intro a b hab
  exact inv_injective (neg_injective hab)

/-- The excluded points are units while `r` is out of the bag. -/
theorem image_visitedAt_subset (hr : r.Prime) (hbag : ¬ inBag q m r k)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) :
    (visitedAt q m r k).image (fun v => -v⁻¹) ⊆ unitFinset r := by
  have : Fact r.Prime := ⟨hr⟩
  intro x hx
  obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hx
  have hv0 : v ≠ 0 := visitedAt_ne_zero hr hbag hnd hv
  refine (mem_unitFinset hr).mpr ?_
  rw [← hveq]
  simpa using hv0

/-- **The bridge.**  While `r` is out of the bag, the box has exactly
`(r - 1) - |visitedAt|` elements: each exposed visit excludes one unit, and
distinct visits exclude distinct units. -/
theorem boxCard_eq (hr : r.Prime) (hbag : ¬ inBag q m r k)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) :
    boxCard q m r k = (r - 1) - (visitedAt q m r k).card := by
  have hsub := image_visitedAt_subset hr hbag hnd
  rw [boxCard, box, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
    unitFinset_card hr,
    Finset.card_image_of_injective _ (neg_inv_injective hr)]

/-- The box never exceeds the unit group. -/
theorem boxCard_le (hr : r.Prime) : boxCard q m r k ≤ r - 1 := by
  rw [boxCard, ← unitFinset_card hr]
  exact Finset.card_le_card (Finset.sdiff_subset)

/-- **F1d.**  Box positivity: an active prime that does not divide the seed
always has a nonempty box. -/
theorem boxCard_pos (hq : q.Prime) (hm : 1 ≤ m) (hr : r.Prime) (hrq : r ≠ q)
    (hrm : ¬ r ∣ m) (hbag : ¬ inBag q m r k)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) :
    0 < boxCard q m r k :=
  Finset.card_pos.mpr ⟨_, seed_mem_box hq hm hr hrq hrm hbag hnd⟩

/-- A charged step keeps `r` out of the bag at the next time. -/
theorem not_inBag_succ_of_charged (hch : Charged q m r k) :
    ¬ inBag q m r (k + 1) := by
  rintro (h | ⟨j, hj, hjr⟩)
  · exact hch.1 (Or.inl h)
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact hch.1 (Or.inr ⟨j, h, hjr⟩)
    · subst h; exact absurd hjr (by have := hch.2.2; omega)

/-- **F1a.**  A charge shrinks the box by exactly one element. -/
theorem boxCard_succ_of_charged (hr : r.Prime) (hch : Charged q m r k)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) :
    boxCard q m r (k + 1) = boxCard q m r k - 1 := by
  have hnd' : ∀ j < k + 1, 2 ≤ genSeqAvoid q m j := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact hnd j h
    · subst h; have := hch.2.2; have := hr.two_le; omega
  rw [boxCard_eq hr (not_inBag_succ_of_charged hch) hnd', boxCard_eq hr hch.1 hnd,
    visitedAt_succ, if_pos hch.2.2, Finset.card_insert_of_notMem hch.2.1]
  omega

/-- The visited set is unchanged at a non-charged step of an active prime. -/
theorem visitedAt_succ_of_not_charged (hnch : ¬ Charged q m r k)
    (hbag : ¬ inBag q m r k) :
    visitedAt q m r (k + 1) = visitedAt q m r k := by
  rw [visitedAt_succ]
  by_cases hexp : r < genSeqAvoid q m k
  · rw [if_pos hexp]
    have hnew : ¬ isNew q m r k := fun hnew => hnch ⟨hbag, hnew, hexp⟩
    exact Finset.insert_eq_self.mpr (not_not.mp hnew)
  · rw [if_neg hexp]

/-- **F1b.**  A non-charged step leaves the box unchanged. -/
theorem boxCard_of_not_charged (hnch : ¬ Charged q m r k)
    (hbag' : ¬ inBag q m r (k + 1)) :
    boxCard q m r (k + 1) = boxCard q m r k := by
  have hbag : ¬ inBag q m r k := not_inBag_of_le (Nat.le_succ k) hbag'
  unfold boxCard box
  rw [visitedAt_succ_of_not_charged hnch hbag]

/-- One-step monotonicity of the box size. -/
theorem boxCard_succ_le (hr : r.Prime) (hbag' : ¬ inBag q m r (k + 1))
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) :
    boxCard q m r (k + 1) ≤ boxCard q m r k := by
  by_cases hch : Charged q m r k
  · rw [boxCard_succ_of_charged hr hch hnd]; omega
  · rw [boxCard_of_not_charged hch hbag']

/-- The box size is non-increasing along any stretch on which `r` stays out of
the bag. -/
theorem boxCard_le_of_le (hr : r.Prime) :
    ∀ {k : ℕ}, ¬ inBag q m r k → (∀ j < k, 2 ≤ genSeqAvoid q m j) →
      ∀ i ≤ k, boxCard q m r k ≤ boxCard q m r i := by
  intro k
  induction k with
  | zero => intro _ _ i hi; rw [Nat.le_zero.mp hi]
  | succ k ih =>
    intro hbag' hnd i hi
    have hbag : ¬ inBag q m r k := not_inBag_of_le (Nat.le_succ k) hbag'
    have hnd' : ∀ j < k, 2 ≤ genSeqAvoid q m j := fun j hj => hnd j (Nat.lt_succ_of_lt hj)
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hi) with h | h
    · exact le_trans (boxCard_succ_le hr hbag' hnd') (ih hbag hnd' i (Nat.lt_succ_iff.mp h))
    · rw [h]

/-- Between two charged steps the box strictly shrinks. -/
theorem boxCard_lt_of_charged (hq : q.Prime) (hm : 1 ≤ m) (hr : r.Prime)
    (hrq : r ≠ q) (hrm : ¬ r ∣ m) {j : ℕ} (hjk : j < k)
    (hnd : ∀ i < k, 2 ≤ genSeqAvoid q m i)
    (hchj : Charged q m r j) (hbagk : ¬ inBag q m r k) :
    boxCard q m r k < boxCard q m r j := by
  have hndj : ∀ i < j, 2 ≤ genSeqAvoid q m i := fun i hi => hnd i (lt_trans hi hjk)
  have hpos : 0 < boxCard q m r j := boxCard_pos hq hm hr hrq hrm hchj.1 hndj
  have hstep : boxCard q m r (j + 1) = boxCard q m r j - 1 :=
    boxCard_succ_of_charged hr hchj hndj
  have hchain : boxCard q m r k ≤ boxCard q m r (j + 1) :=
    boxCard_le_of_le hr hbagk hnd (j + 1) hjk
  omega

/-! ### The harmonic charge budget -/

/-- The real harmonic number `1 + 1/2 + ⋯ + 1/N`. -/
def harmonicR (N : ℕ) : ℝ := ∑ i ∈ Finset.range N, (1 : ℝ) / (i + 1)

/-- `harmonicR` is Mathlib's `harmonic`, cast to `ℝ`. -/
theorem harmonicR_eq_harmonic (N : ℕ) : harmonicR N = (harmonic N : ℝ) := by
  simp only [harmonicR, harmonic, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  rw [one_div]

/-- **F1e — the harmonic charge budget.**  Along any nondegenerate stretch of
the `q`-free orbit, the reciprocal box sizes at the steps where the active prime
`r ≠ q` is charged sum to at most `1 + 1/2 + ⋯ + 1/(r-1)`.

Each charge shrinks the box by one (`boxCard_succ_of_charged`), non-charges
leave it alone (`boxCard_of_not_charged`), and the box stays nonempty
(`boxCard_pos`); so the box sizes at charged steps are *pairwise distinct*
values in `[1, r-1]`, and the sum injects into the harmonic sum.

Verified statement list, `findings_ls_verification.md` §4, Group 1 (F1e). -/
theorem charge_sum_le_harmonic (hq : q.Prime) (hm : 1 ≤ m) (hr : r.Prime)
    (hrq : r ≠ q) (hrm : ¬ r ∣ m) (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m j) :
    ∑ k ∈ (Finset.range n).filter (fun k => Charged q m r k),
        (1 : ℝ) / boxCard q m r k ≤ harmonicR (r - 1) := by
  classical
  set S := (Finset.range n).filter (fun k => Charged q m r k) with hS
  -- Basic facts at a charged step of `S`.
  have hfacts : ∀ i ∈ S, Charged q m r i ∧ (∀ j < i, 2 ≤ genSeqAvoid q m j) ∧
      1 ≤ boxCard q m r i ∧ boxCard q m r i ≤ r - 1 := by
    intro i hi
    rw [hS, Finset.mem_filter, Finset.mem_range] at hi
    have hndi : ∀ j < i, 2 ≤ genSeqAvoid q m j := fun j hj => hnd j (lt_trans hj hi.1)
    exact ⟨hi.2, hndi, boxCard_pos hq hm hr hrq hrm hi.2.1 hndi, boxCard_le hr⟩
  -- Strict decrease of the box size between charged steps.
  have hlt : ∀ i ∈ S, ∀ j ∈ S, i < j → boxCard q m r j < boxCard q m r i := by
    intro i hi j hj hij
    have hjmem := hj
    rw [hS, Finset.mem_filter, Finset.mem_range] at hjmem
    have hndj : ∀ t < j, 2 ≤ genSeqAvoid q m t := fun t ht => hnd t (lt_trans ht hjmem.1)
    exact boxCard_lt_of_charged hq hm hr hrq hrm hij hndj (hfacts i hi).1 hjmem.2.1
  -- The shifted box size, an injection of `S` into `range (r-1)`.
  set f : ℕ → ℕ := fun i => boxCard q m r i - 1 with hf
  have hinj : Set.InjOn f S := by
    intro a ha b hb hab
    have h1 := (hfacts a ha).2.2.1
    have h2 := (hfacts b hb).2.2.1
    rcases lt_trichotomy a b with h | h | h
    · have := hlt a ha b hb h; rw [hf] at hab; simp only at hab; omega
    · exact h
    · have := hlt b hb a ha h; rw [hf] at hab; simp only at hab; omega
  have hmaps : S.image f ⊆ Finset.range (r - 1) := by
    intro v hv
    obtain ⟨i, hi, hveq⟩ := Finset.mem_image.mp hv
    obtain ⟨-, -, hlo, hhi⟩ := hfacts i hi
    rw [Finset.mem_range, ← hveq, hf]
    simp only
    omega
  -- Rewrite the summand through `f`.
  have hterm : ∀ i ∈ S, (1 : ℝ) / boxCard q m r i = (1 : ℝ) / ((f i : ℝ) + 1) := by
    intro i hi
    have hlo := (hfacts i hi).2.2.1
    have : boxCard q m r i = f i + 1 := by rw [hf]; simp only; omega
    rw [this]
    push_cast
    ring
  calc ∑ k ∈ S, (1 : ℝ) / boxCard q m r k
      = ∑ k ∈ S, (1 : ℝ) / ((f k : ℝ) + 1) := Finset.sum_congr rfl hterm
    _ = ∑ v ∈ S.image f, (1 : ℝ) / ((v : ℝ) + 1) := by rw [Finset.sum_image hinj]
    _ ≤ ∑ v ∈ Finset.range (r - 1), (1 : ℝ) / ((v : ℝ) + 1) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hmaps ?_
        intro v _ _
        positivity
    _ = harmonicR (r - 1) := rfl

/-! ## 3.  Group 2 — distinctness of the multipliers

Verified statement list, `findings_ls_verification.md` §4, Group 2. -/

/-- **F2a/F2b, engine.**  An earlier multiplier divides the current cofactor,
hence the current accumulator; it cannot also divide the current Euclid
number. -/
theorem genSeqAvoid_ne_of_lt (hq : q.Prime) (hm : 1 ≤ m) {j : ℕ} (hjk : j < k)
    (h2k : 2 ≤ genSeqAvoid q m k) :
    genSeqAvoid q m j ≠ genSeqAvoid q m k := by
  intro heq
  -- `p = p̃(j)` divides the cofactor at time `k`, hence the accumulator.
  have hdvdc : genSeqAvoid q m j ∣ seedCofactorAvoid q m k :=
    Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hjk)
  have hdvdP : genSeqAvoid q m j ∣ genProdAvoid q m k := by
    rw [genProdAvoid_eq_seed_mul_cofactor]
    exact Dvd.dvd.mul_left hdvdc m
  -- but `p = p̃(k)` divides the Euclid number.
  have hdvdS : genSeqAvoid q m j ∣ genProdAvoid q m k + 1 := by
    rw [heq]; exact genSeqAvoid_dvd_succ hq hm h2k
  have hone : genSeqAvoid q m j ∣ 1 := (Nat.dvd_add_right hdvdP).mp hdvdS
  have hp : Nat.Prime (genSeqAvoid q m j) := genSeqAvoid_prime (heq ▸ h2k)
  exact hp.one_lt.ne' (Nat.dvd_one.mp hone)

/-- **F2b.**  The multipliers of a nondegenerate `q`-free orbit are pairwise
distinct on `[0, n)`. -/
theorem genSeqAvoid_injOn (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m j) :
    Set.InjOn (genSeqAvoid q m) {k | k < n} := by
  intro a ha b hb hab
  have ha : a < n := ha
  have hb : b < n := hb
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (genSeqAvoid_ne_of_lt hq hm h (hnd b hb))
  · exact h
  · exact absurd hab.symm (genSeqAvoid_ne_of_lt hq hm h (hnd a ha))

/-- **F2c.**  At most `π(N)` of the first `n` steps have multiplier `< N`. -/
theorem few_small_multipliers (hq : q.Prime) (hm : 1 ≤ m) (N : ℕ)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m j) :
    ((Finset.range n).filter (fun k => genSeqAvoid q m k < N)).card
      ≤ ((Finset.range N).filter Nat.Prime).card := by
  classical
  refine Finset.card_le_card_of_injOn (genSeqAvoid q m) ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact ⟨ha.2, genSeqAvoid_prime (hnd a ha.1)⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    exact genSeqAvoid_injOn hq hm hnd ha.1 hb.1 hab

/-! ## 4.  Group 3 — the brink lemma

Verified statement list, `findings_ls_verification.md` §4, Group 3.  Note the
hypothesis `r ≠ q` (correction **C2**): the statement is *false* at `r = q`,
because the `q`-free dynamics ignores `q` when selecting its multiplier. -/

/-- **F3a — the brink lemma.**  If the box of an active prime `r ≠ q` has
collapsed to a single element and the current cofactor residue is new, then the
seed residue is forced onto the death point `-c(k)⁻¹`, so `r` divides the
current Euclid number and the multiplier is `≤ r`.

In particular a step at the brink cannot be a *good* (large-multiplier) step. -/
theorem brink_forces_small_multiplier (hq : q.Prime) (hm : 1 ≤ m) (hr : r.Prime)
    (hrq : r ≠ q) (hrm : ¬ r ∣ m) (hbag : ¬ inBag q m r k) (hnew : isNew q m r k)
    (hbox : boxCard q m r k = 1) (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) :
    genSeqAvoid q m k ≤ r := by
  have : Fact r.Prime := ⟨hr⟩
  have hc0 : ((seedCofactorAvoid q m k : ℕ) : ZMod r) ≠ 0 :=
    cofactor_ne_zero_of_not_inBag hr hbag hnd (le_refl k)
  -- The death point of the current step is still in the box.
  have hdeath : (-((seedCofactorAvoid q m k : ℕ) : ZMod r)⁻¹) ∈ box q m r k := by
    refine Finset.mem_sdiff.mpr ⟨(mem_unitFinset hr).mpr ?_, ?_⟩
    · simpa using hc0
    · intro hmem
      obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hmem
      have hvc : v = ((seedCofactorAvoid q m k : ℕ) : ZMod r) := neg_inv_injective hr hveq
      rw [hvc] at hv
      exact hnew hv
  -- So is the seed residue.
  have hseed : ((m : ℕ) : ZMod r) ∈ box q m r k :=
    seed_mem_box hq hm hr hrq hrm hbag hnd
  -- A one-element box forces them to coincide.
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hbox
  have h1 : ((m : ℕ) : ZMod r) = a := Finset.mem_singleton.mp (ha ▸ hseed)
  have h2 : (-((seedCofactorAvoid q m k : ℕ) : ZMod r)⁻¹) = a :=
    Finset.mem_singleton.mp (ha ▸ hdeath)
  have hforced : ((m : ℕ) : ZMod r) = -((seedCofactorAvoid q m k : ℕ) : ZMod r)⁻¹ := by
    rw [h1, h2]
  -- Hence `r` divides the current Euclid number.
  have hhit : ((m : ℕ) : ZMod r) * ((seedCofactorAvoid q m k : ℕ) : ZMod r) = -1 :=
    (hit_iff_eq_neg_inv hr hc0).mpr hforced
  have hdvd : r ∣ m * seedCofactorAvoid q m k + 1 := hit_iff_dvd.mp hhit
  rw [← genProdAvoid_eq_seed_mul_cofactor] at hdvd
  have hN : genProdAvoid q m k + 1 ≠ 0 := by
    have := genProdAvoid_pos q hm k; omega
  have := minFac_qfreePart_least hq hN hr hrq hdvd
  rwa [← genSeqAvoid_def] at this

/-- **F3a, contrapositive form.**  A step whose multiplier exceeds `r` cannot be
at the brink for the active prime `r ≠ q`: its box has at least two elements. -/
theorem two_le_boxCard_of_exposed (hq : q.Prime) (hm : 1 ≤ m) (hr : r.Prime)
    (hrq : r ≠ q) (hrm : ¬ r ∣ m) (hbag : ¬ inBag q m r k) (hnew : isNew q m r k)
    (hexp : r < genSeqAvoid q m k) (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) :
    2 ≤ boxCard q m r k := by
  have hpos := boxCard_pos hq hm hr hrq hrm hbag hnd
  by_contra hcon
  have h1 : boxCard q m r k = 1 := by omega
  have := brink_forces_small_multiplier hq hm hr hrq hrm hbag hnew h1 hnd
  omega

/-! ## 5.  The escape density `ρ`, the two bands and the survival product

Second slice of the deterministic core of **(LS)**: the local escape density,
the near/far band split (correction **C1**: near band `r ≤ 2k+1`, far band
`r ≥ 2k+2`, so that the two bands partition `{r ≤ y}`), the survival product,
the aggregated charge budget (F1f-F1h) and the deterministic Markov count
(M1, M2).  Verified statement list, `findings_ls_verification.md` §4,
Groups 3-5.

Everything continues to carry the hypothesis `r ≠ q` (correction **C2**). -/

/-- **Local escape density.**  `ρ_r(k) = 1/|box|` at an *active, new* position —
the exact conditional probability that the current Euclid number is divisible by
`r`, given the box data — and `0` when `r` is in the bag or the cofactor residue
has already been seen. -/
noncomputable def rho (q m r k : ℕ) : ℝ :=
  if ¬ inBag q m r k ∧ isNew q m r k then 1 / (boxCard q m r k : ℝ) else 0

/-- The **near band** at step `k`: primes `r ≤ 2k+1`, `r ≠ q` (correction C1). -/
def nearBand (q k : ℕ) : Finset ℕ :=
  (Finset.range (2 * k + 2)).filter (fun r => r.Prime ∧ r ≠ q)

/-- The **far band** up to `y` at step `k`: primes `2k+2 ≤ r ≤ y`, `r ≠ q`. -/
def farBand (q y k : ℕ) : Finset ℕ :=
  (Finset.Icc (2 * k + 2) y).filter (fun r => r.Prime ∧ r ≠ q)

/-- All primes `r ≤ y` other than `q`. -/
def bandUpTo (q y : ℕ) : Finset ℕ :=
  (Finset.range (y + 1)).filter (fun r => r.Prime ∧ r ≠ q)

/-- The **roughness survival product** up to `y`, excluding `q` (correction C2):
the conditional probability that the next Euclid number has no prime factor
`≤ y` other than `q`. -/
noncomputable def survival (q m y k : ℕ) : ℝ :=
  ∏ r ∈ bandUpTo q y, (1 - rho q m r k)

/-- Step `k` is **`n`-good**: the multiplier is at least `2n`. -/
def Good (q m n k : ℕ) : Prop := 2 * n ≤ genSeqAvoid q m k

/-- The **near-band escape mass** at step `k`. -/
noncomputable def nearMass (q m k : ℕ) : ℝ := ∑ r ∈ nearBand q k, rho q m r k

/-- The **cumulative charge budget** over the horizon `n`, primes `< N`, `≠ q`. -/
noncomputable def chargeBudget (q m N n : ℕ) : ℝ :=
  ∑ r ∈ (Finset.range N).filter (fun r => r.Prime ∧ r ≠ q),
    ∑ k ∈ (Finset.range n).filter (fun k => Charged q m r k), (1 : ℝ) / boxCard q m r k

/-! ### 5.1  Basic facts about `ρ` -/

theorem rho_of_active (h : ¬ inBag q m r k ∧ isNew q m r k) :
    rho q m r k = 1 / (boxCard q m r k : ℝ) := if_pos h

theorem rho_eq_zero_of_inactive (h : ¬ (¬ inBag q m r k ∧ isNew q m r k)) :
    rho q m r k = 0 := if_neg h

theorem rho_eq_zero_of_inBag (h : inBag q m r k) : rho q m r k = 0 :=
  if_neg (fun hc => hc.1 h)

theorem rho_eq_zero_of_old (h : ¬ isNew q m r k) : rho q m r k = 0 :=
  if_neg (fun hc => h hc.2)

theorem rho_nonneg : 0 ≤ rho q m r k := by
  by_cases h : ¬ inBag q m r k ∧ isNew q m r k
  · rw [rho_of_active h]; positivity
  · rw [rho_eq_zero_of_inactive h]

/-- `ρ_r(k) ≤ 1`: box positivity (F1d) at an active position, and `0` otherwise.
The hypothesis `¬ r ∣ m` is *not* needed: if `r ∣ m` then `r` is in the bag and
`ρ_r(k) = 0`. -/
theorem rho_le_one (hq : q.Prime) (hm : 1 ≤ m) (hr : r.Prime) (hrq : r ≠ q)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) : rho q m r k ≤ 1 := by
  by_cases h : ¬ inBag q m r k ∧ isNew q m r k
  · rw [rho_of_active h]
    have hrm : ¬ r ∣ m := fun hd => h.1 (Or.inl hd)
    have hpos : 0 < boxCard q m r k := boxCard_pos hq hm hr hrq hrm h.1 hnd
    have h1 : (1 : ℕ) ≤ boxCard q m r k := hpos
    have h1' : (1 : ℝ) ≤ (boxCard q m r k : ℝ) := by exact_mod_cast h1
    rw [div_le_one (by linarith)]
    exact h1'
  · rw [rho_eq_zero_of_inactive h]; norm_num

/-! ### 5.2  F3b — the near band at a good step -/

/-- **F3b.**  At a good step, an active near-band prime `r ≤ 2k+1`, `r ≠ q`, is
exposed (`r < 2n ≤ p̃(k)`) and therefore *not* at the brink (F3a), so its box has
at least two elements and `ρ_r(k) ≤ 1/2`. -/
theorem rho_le_half_of_good (hq : q.Prime) (hm : 1 ≤ m) (hr : r.Prime) (hrq : r ≠ q)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) (hkn : k < n) (hgood : Good q m n k)
    (hnear : r ≤ 2 * k + 1) : rho q m r k ≤ 1 / 2 := by
  by_cases h : ¬ inBag q m r k ∧ isNew q m r k
  · rw [rho_of_active h]
    have hrm : ¬ r ∣ m := fun hd => h.1 (Or.inl hd)
    have hg : 2 * n ≤ genSeqAvoid q m k := hgood
    have hexp : r < genSeqAvoid q m k := by omega
    have h2 : 2 ≤ boxCard q m r k :=
      two_le_boxCard_of_exposed hq hm hr hrq hrm h.1 h.2 hexp hnd
    have h2' : (2 : ℝ) ≤ (boxCard q m r k : ℝ) := by exact_mod_cast h2
    exact one_div_le_one_div_of_le (by norm_num) h2'
  · rw [rho_eq_zero_of_inactive h]; norm_num

/-! ### 5.3  B1, B2 — the far band, pointwise -/

/-- The visited set at time `k` has at most `k` elements. -/
theorem card_visitedAt_le (q m r k : ℕ) : (visitedAt q m r k).card ≤ k := by
  refine le_trans Finset.card_image_le (le_trans (Finset.card_filter_le _ _) ?_)
  simp

/-- **B1, natural-number form.**  For a far-band prime the box has kept at least
half of the unit group. -/
theorem two_mul_boxCard_ge_of_far (hr : r.Prime) (hbag : ¬ inBag q m r k)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) (hfar : 2 * k + 2 ≤ r) :
    r ≤ 2 * boxCard q m r k := by
  have hb := boxCard_eq hr hbag hnd
  have hv := card_visitedAt_le q m r k
  omega

/-- **B1.**  `r/2 ≤ |box_k(r)|` for `r ≥ 2k+2`. -/
theorem boxCard_ge_of_far (hr : r.Prime) (hbag : ¬ inBag q m r k)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) (hfar : 2 * k + 2 ≤ r) :
    (r : ℝ) / 2 ≤ (boxCard q m r k : ℝ) := by
  have h := two_mul_boxCard_ge_of_far hr hbag hnd hfar
  have h' : (r : ℝ) ≤ 2 * (boxCard q m r k : ℝ) := by exact_mod_cast h
  linarith

/-- **B2.**  `ρ_r(k) ≤ 2/r` on the far band. -/
theorem rho_le_far (hr : r.Prime) (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j)
    (hfar : 2 * k + 2 ≤ r) : rho q m r k ≤ 2 / r := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  by_cases h : ¬ inBag q m r k ∧ isNew q m r k
  · rw [rho_of_active h]
    have hb := boxCard_ge_of_far hr h.1 hnd hfar
    have hrw : (2 : ℝ) / r = 1 / ((r : ℝ) / 2) := by field_simp
    rw [hrw]
    exact one_div_le_one_div_of_le (by linarith) hb
  · rw [rho_eq_zero_of_inactive h]; positivity

/-- Far-band primes also satisfy `ρ ≤ 1/2` from step `1` on: their box has kept
at least `k+1 ≥ 2` elements. -/
theorem rho_le_half_of_far (hr : r.Prime) (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j)
    (hk : 1 ≤ k) (hfar : 2 * k + 2 ≤ r) : rho q m r k ≤ 1 / 2 := by
  by_cases h : ¬ inBag q m r k ∧ isNew q m r k
  · rw [rho_of_active h]
    have hb := two_mul_boxCard_ge_of_far hr h.1 hnd hfar
    have h2 : 2 ≤ boxCard q m r k := by omega
    have h2' : (2 : ℝ) ≤ (boxCard q m r k : ℝ) := by exact_mod_cast h2
    exact one_div_le_one_div_of_le (by norm_num) h2'
  · rw [rho_eq_zero_of_inactive h]; norm_num

/-! ### 5.4  The survival product -/

theorem survival_nonneg (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) (y : ℕ) : 0 ≤ survival q m y k := by
  refine Finset.prod_nonneg fun t ht => ?_
  rw [bandUpTo, Finset.mem_filter] at ht
  have := rho_le_one hq hm ht.2.1 ht.2.2 hnd
  linarith

/-- **F3c.**  At a good step (from step `1` on) the survival product is
*positive*: every band factor is at least `1/2`.  This is the pathwise form of
bonus §2.9(i): `S_k = 0` forces a non-good step. -/
theorem survival_pos_of_good (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) (hk : 1 ≤ k) (hkn : k < n)
    (hgood : Good q m n k) (y : ℕ) : 0 < survival q m y k := by
  refine Finset.prod_pos fun t ht => ?_
  rw [bandUpTo, Finset.mem_filter] at ht
  have hhalf : rho q m t k ≤ 1 / 2 := by
    by_cases hnear : t ≤ 2 * k + 1
    · exact rho_le_half_of_good hq hm ht.2.1 ht.2.2 hnd hkn hgood hnear
    · exact rho_le_half_of_far ht.2.1 hnd hk (by omega)
  linarith

/-- **F3d.**  Contrapositive of `survival_pos_of_good`. -/
theorem not_good_of_survival_eq_zero (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) (hk : 1 ≤ k) (hkn : k < n) (y : ℕ)
    (hzero : survival q m y k = 0) : ¬ Good q m n k := fun hgood =>
  absurd hzero (survival_pos_of_good hq hm hnd hk hkn hgood y).ne'

/-! ### 5.5  B3 — the elementary exponential inequality -/

/-- **B3.**  `e^{-2x} ≤ 1 - x` on `[0, 1/2]`.

From `1 + 2x ≤ e^{2x}` one gets `e^{-2x} ≤ 1/(1+2x)`, and
`1/(1+2x) ≤ 1 - x ⟺ 1 ≤ (1-x)(1+2x) = 1 + x - 2x² ⟺ 2x² ≤ x ⟺ x ≤ 1/2`. -/
theorem one_sub_ge_exp {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have hE : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add]; simp
  have h1 : (1 : ℝ) + 2 * x ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp (2 * x); linarith
  have hpos : 0 < Real.exp (-(2 * x)) := Real.exp_pos _
  have hE2 : Real.exp (-(2 * x)) * (1 + 2 * x) ≤ 1 := by
    calc Real.exp (-(2 * x)) * (1 + 2 * x)
        ≤ Real.exp (-(2 * x)) * Real.exp (2 * x) := by
          exact mul_le_mul_of_nonneg_left h1 hpos.le
      _ = 1 := hE
  nlinarith [hE2, hx0, hx]

/-! ### 5.6  B7 — the near-band product bound

Recorded constant: the verification's `B6` (`4^{-ρ} ≤ 1 - ρ`) is replaced here
by the weaker but self-contained `B3`, so the near-band product bound reads
`∏ (1 - ρ) ≥ exp (-2T)` instead of `4^{-T}`.  At the verifier's `T = 6` this is
`e^{-12}` in place of `4^{-6} = e^{-8.32}`; downstream the safe margin should be
taken as `c₁ := exp (-36)` rather than `exp (-35)`. -/

/-- **B7.**  If the near-band escape mass at a good step is at most `T`, the
near-band product is at least `e^{-2T}`. -/
theorem near_band_product_ge (T : ℝ) (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) (hkn : k < n) (hgood : Good q m n k)
    (hmass : nearMass q m k ≤ T) :
    Real.exp (-(2 * T)) ≤ ∏ r ∈ nearBand q k, (1 - rho q m r k) := by
  have hstep : ∀ t ∈ nearBand q k, Real.exp (-(2 * rho q m t k)) ≤ 1 - rho q m t k := by
    intro t ht
    rw [nearBand, Finset.mem_filter, Finset.mem_range] at ht
    exact one_sub_ge_exp rho_nonneg
      (rho_le_half_of_good hq hm ht.2.1 ht.2.2 hnd hkn hgood (by omega))
  have hsum : ∑ t ∈ nearBand q k, (-(2 * rho q m t k)) = -(2 * nearMass q m k) := by
    simp [nearMass, Finset.mul_sum]
  calc Real.exp (-(2 * T)) ≤ Real.exp (-(2 * nearMass q m k)) := by
        exact Real.exp_le_exp.mpr (by linarith)
    _ = ∏ t ∈ nearBand q k, Real.exp (-(2 * rho q m t k)) := by
        rw [← hsum, Real.exp_sum]
    _ ≤ ∏ t ∈ nearBand q k, (1 - rho q m t k) :=
        Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) hstep

/-! ### 5.7  B8 — the band partition -/

/-- **B8.**  For `y ≥ 2k+2` the near and far bands are disjoint and partition
`{r ≤ y : r prime, r ≠ q}`, so the survival product factors. -/
theorem survival_eq_near_mul_far (q m k : ℕ) {y : ℕ} (hy : 2 * k + 2 ≤ y) :
    survival q m y k
      = (∏ r ∈ nearBand q k, (1 - rho q m r k))
        * (∏ r ∈ farBand q y k, (1 - rho q m r k)) := by
  have hsplit : Finset.range (y + 1) = Finset.range (2 * k + 2) ∪ Finset.Icc (2 * k + 2) y := by
    ext t
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (nearBand q k) (farBand q y k) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [nearBand, Finset.mem_filter, Finset.mem_range] at ha
    rw [farBand, Finset.mem_filter, Finset.mem_Icc] at hb
    omega
  rw [survival, bandUpTo, hsplit, Finset.filter_union]
  exact Finset.prod_union hdisj

/-! ### 5.8  F1f-F1h — aggregating the charge budget -/

theorem harmonicR_nonneg (N : ℕ) : 0 ≤ harmonicR N :=
  Finset.sum_nonneg fun i _ => by positivity

/-- **F1f.**  `H_N ≤ 1 + log N`, via Mathlib's `harmonic_le_one_add_log`. -/
theorem harmonicR_le (N : ℕ) : harmonicR N ≤ 1 + Real.log N := by
  rw [harmonicR_eq_harmonic]
  exact harmonic_le_one_add_log N

/-- The inner charge sum vanishes for a prime dividing the seed: such a prime is
in the bag from time `0`, hence never charged. -/
theorem charge_sum_eq_zero_of_dvd (hrm : r ∣ m) :
    ∑ k ∈ (Finset.range n).filter (fun k => Charged q m r k),
      (1 : ℝ) / boxCard q m r k = 0 :=
  Finset.sum_eq_zero fun k hk => by
    rw [Finset.mem_filter] at hk
    exact absurd (Or.inl hrm) hk.2.1

/-- **F1g.**  The charge budget is bounded by the sum of the per-prime harmonic
budgets (F1e), the primes dividing the seed contributing nothing. -/
theorem chargeBudget_le_sum_harmonic (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m j) (N : ℕ) :
    chargeBudget q m N n
      ≤ ∑ r ∈ (Finset.range N).filter (fun r => r.Prime ∧ r ≠ q), harmonicR (r - 1) := by
  rw [chargeBudget]
  refine Finset.sum_le_sum fun t ht => ?_
  rw [Finset.mem_filter] at ht
  by_cases htm : t ∣ m
  · rw [charge_sum_eq_zero_of_dvd htm]
    exact harmonicR_nonneg _
  · exact charge_sum_le_harmonic hq hm ht.2.1 ht.2.2 htm hnd

/-- Dropping `r ≠ q` and passing to `1 + log r` (F1f). -/
theorem sum_harmonic_le (q N : ℕ) :
    ∑ r ∈ (Finset.range N).filter (fun r => r.Prime ∧ r ≠ q), harmonicR (r - 1)
      ≤ (((Finset.range N).filter Nat.Prime).card : ℝ)
        + ∑ r ∈ (Finset.range N).filter Nat.Prime, Real.log r := by
  have hsub : (Finset.range N).filter (fun r => r.Prime ∧ r ≠ q)
      ⊆ (Finset.range N).filter Nat.Prime := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.1⟩
  have hterm : ∀ t ∈ (Finset.range N).filter Nat.Prime,
      harmonicR (t - 1) ≤ 1 + Real.log t := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have h2 := ht.2.two_le
    have hlo : (0 : ℝ) < ((t - 1 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ t - 1 := by omega
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hle : ((t - 1 : ℕ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast Nat.sub_le t 1
    calc harmonicR (t - 1) ≤ 1 + Real.log ((t - 1 : ℕ) : ℝ) := harmonicR_le _
      _ ≤ 1 + Real.log t := by linarith [Real.log_le_log hlo hle]
  have hnn : ∀ t ∈ (Finset.range N).filter Nat.Prime,
      t ∉ (Finset.range N).filter (fun r => r.Prime ∧ r ≠ q) → 0 ≤ 1 + Real.log t := by
    intro t ht _
    rw [Finset.mem_filter] at ht
    have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht.2.one_lt.le
    linarith [Real.log_nonneg this]
  calc ∑ r ∈ (Finset.range N).filter (fun r => r.Prime ∧ r ≠ q), harmonicR (r - 1)
      ≤ ∑ r ∈ (Finset.range N).filter (fun r => r.Prime ∧ r ≠ q), (1 + Real.log r) :=
        Finset.sum_le_sum fun t ht => hterm t (hsub ht)
    _ ≤ ∑ r ∈ (Finset.range N).filter Nat.Prime, (1 + Real.log r) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    _ = (((Finset.range N).filter Nat.Prime).card : ℝ)
          + ∑ r ∈ (Finset.range N).filter Nat.Prime, Real.log r := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Chebyshev.**  `θ(N) ≤ N log 4`, from Mathlib's `primorial_le_four_pow`. -/
theorem sum_log_prime_le (N : ℕ) :
    ∑ r ∈ (Finset.range N).filter Nat.Prime, Real.log r ≤ N * Real.log 4 := by
  have hsub : (Finset.range N).filter Nat.Prime
      ⊆ (Finset.range (N + 1)).filter Nat.Prime := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨by omega, hx.2⟩
  have hprim : primorial N = ∏ r ∈ (Finset.range (N + 1)).filter Nat.Prime, r := rfl
  have hdvd : (∏ r ∈ (Finset.range N).filter Nat.Prime, r) ∣ primorial N := by
    rw [hprim]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have hle : (∏ r ∈ (Finset.range N).filter Nat.Prime, r) ≤ 4 ^ N :=
    le_trans (Nat.le_of_dvd (primorial_pos N) hdvd) (primorial_le_four_pow N)
  have hle' : ((∏ r ∈ (Finset.range N).filter Nat.Prime, r : ℕ) : ℝ) ≤ ((4 ^ N : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hppos : (0 : ℝ) < ((∏ r ∈ (Finset.range N).filter Nat.Prime, r : ℕ) : ℝ) := by
    have : 0 < ∏ r ∈ (Finset.range N).filter Nat.Prime, r := by
      refine Finset.prod_pos fun t ht => ?_
      rw [Finset.mem_filter] at ht
      exact ht.2.pos
    exact_mod_cast this
  have hlogprod : ∑ r ∈ (Finset.range N).filter Nat.Prime, Real.log r
      = Real.log ((∏ r ∈ (Finset.range N).filter Nat.Prime, r : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro x hx
    rw [Finset.mem_filter] at hx
    exact_mod_cast hx.2.pos.ne'
  rw [hlogprod]
  calc Real.log ((∏ r ∈ (Finset.range N).filter Nat.Prime, r : ℕ) : ℝ)
      ≤ Real.log ((4 ^ N : ℕ) : ℝ) := Real.log_le_log hppos hle'
    _ = N * Real.log 4 := by
        push_cast
        rw [Real.log_pow]

/-- **F1h.**  The aggregated charge budget: over the horizon `n` and the primes
`r < N`, `r ≠ q`, the total charge is at most `π(N) + N log 4`.

(The `π(N)` term is carried symbolically; Chebyshev's upper bound
`π(N) = o(N)` is what turns this into the verification's `Ch_n ≤ 2.8 n` at
`N = 2n`.)  Verified statement list, `findings_ls_verification.md` §4 (F1f-F1h). -/
theorem chargeBudget_le (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m j) (N : ℕ) :
    chargeBudget q m N n
      ≤ (((Finset.range N).filter Nat.Prime).card : ℝ) + N * Real.log 4 := by
  refine le_trans (chargeBudget_le_sum_harmonic hq hm hnd N) ?_
  refine le_trans (sum_harmonic_le q N) ?_
  linarith [sum_log_prime_le N]

/-! ### 5.9  M1, M2 — the deterministic Markov count -/

/-- **M1.**  At a good step the near-band escape mass is *exactly* the charged
near-band sum: near-band primes are automatically exposed
(`r ≤ 2k+1 < 2n ≤ p̃(k)`), so "active and new" coincides with "charged". -/
theorem nearMass_eq_charge_of_good (hkn : k < n) (hgood : Good q m n k) :
    nearMass q m k
      = ∑ r ∈ (Finset.range (2 * k + 2)).filter
            (fun r => r.Prime ∧ r ≠ q ∧ Charged q m r k),
          (1 : ℝ) / boxCard q m r k := by
  have hg : 2 * n ≤ genSeqAvoid q m k := hgood
  have hBA : (Finset.range (2 * k + 2)).filter (fun r => r.Prime ∧ r ≠ q ∧ Charged q m r k)
      ⊆ nearBand q k := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    rw [nearBand, Finset.mem_filter, Finset.mem_range]
    exact ⟨hx.1, hx.2.1, hx.2.2.1⟩
  have hzero : ∀ x ∈ nearBand q k,
      x ∉ (Finset.range (2 * k + 2)).filter (fun r => r.Prime ∧ r ≠ q ∧ Charged q m r k) →
      rho q m x k = 0 := by
    intro x hxA hxB
    by_cases hact : ¬ inBag q m x k ∧ isNew q m x k
    · exfalso
      rw [nearBand, Finset.mem_filter, Finset.mem_range] at hxA
      refine hxB (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxA.1,
        hxA.2.1, hxA.2.2, hact.1, hact.2, ?_⟩)
      omega
    · exact rho_eq_zero_of_inactive hact
  rw [nearMass, ← Finset.sum_subset hBA hzero]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_filter] at ht
  exact rho_of_active ⟨ht.2.2.2.1, ht.2.2.2.2.1⟩

/-- **M2 — the deterministic Markov count.**  The number of good steps whose
near-band escape mass exceeds `T` is at most `chargeBudget / T`: each such step
consumes more than `T` of the (global, harmonic) budget. -/
theorem markov_count_le (q m n : ℕ) (T : ℝ) :
    T * (((Finset.range n).filter
        (fun k => Good q m n k ∧ T < nearMass q m k)).card : ℝ)
      ≤ chargeBudget q m (2 * n) n := by
  classical
  set R := (Finset.range (2 * n)).filter (fun r => r.Prime ∧ r ≠ q) with hR
  set g : ℕ → ℝ := fun k =>
    ∑ r ∈ R.filter (fun r => Charged q m r k), (1 : ℝ) / boxCard q m r k with hg
  set S := (Finset.range n).filter (fun k => Good q m n k ∧ T < nearMass q m k) with hS
  have hgnn : ∀ t : ℕ, 0 ≤ g t := fun t =>
    Finset.sum_nonneg fun _ _ => by positivity
  have hkey : ∀ t ∈ S, T ≤ g t := by
    intro t ht
    rw [hS, Finset.mem_filter, Finset.mem_range] at ht
    have hM1 := nearMass_eq_charge_of_good ht.1 ht.2.1
    have hsub : (Finset.range (2 * t + 2)).filter
        (fun r => r.Prime ∧ r ≠ q ∧ Charged q m r t)
        ⊆ R.filter (fun r => Charged q m r t) := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_range] at hx
      rw [hR, Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨by omega, hx.2.1, hx.2.2.1⟩, hx.2.2.2⟩
    have hmono := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => by positivity : ∀ i ∈ R.filter (fun r => Charged q m r t),
        i ∉ (Finset.range (2 * t + 2)).filter (fun r => r.Prime ∧ r ≠ q ∧ Charged q m r t) →
        (0 : ℝ) ≤ 1 / boxCard q m i t)
    rw [← hM1] at hmono
    have := ht.2.2
    rw [hg]
    linarith
  calc T * (S.card : ℝ) = ∑ _t ∈ S, T := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ t ∈ S, g t := Finset.sum_le_sum hkey
    _ ≤ ∑ t ∈ Finset.range n, g t :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by rw [hS]; exact Finset.filter_subset _ _) (fun i _ _ => hgnn i)
    _ = chargeBudget q m (2 * n) n := by
        simp only [hg, chargeBudget, Finset.sum_filter, ← hR]
        rw [Finset.sum_comm]

end LargeStepRoughness

end
