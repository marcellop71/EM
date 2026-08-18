import EM.Population.SeedCapture
import Mathlib.NumberTheory.Harmonic.Defs
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

end LargeStepRoughness

end
