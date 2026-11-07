import EM.Population.AdelicShadow

/-!
# Rigidity of the greedy step: nothing acts on the branch

Session 324 (2026-11-07).  Memo: `docs/analysis/equivariance_scoping_2026-11-07.md`.

Question: is there a structure in which the Euclid–Mullin step `T m = m · minFac (m + 1)` is
equivariant, so that the orbit of `2` becomes an orbit of a group acting on seeds (the
"generic object" reading, the Zilber–Pink lower bound of dead end #181)?  This file records
the two theorems that make the negative answer precise on the seed space `ℕ`.

* **Affine rigidity** (`affine_commute_eq_id`): the only map `m ↦ a m + b` with `a ≥ 1`
  commuting with `T` on seeds `m ≥ 1` is the identity.  The proof is two lines of
  arithmetic: `m = 1` forces `b = 0`, and for every prime `r` the seed `m = r − 1` forces
  `r ∣ a − 1`.
* **Itinerary rigidity** (`eq_of_itinerary_eq`): two seeds `m, m' ≥ 1` with the same
  multiplier sequence are equal.  Equal itineraries give `p_k ∣ (m − m') ∏_{j<k} p_j` with
  `p_k` coprime to the product (distinct primes, `AdelicShadow.genSeq_ne_of_lt`), hence
  `p_k ∣ m − m'` for every `k`; the multipliers are unbounded.

Consequences (`eq_id_of_preserves_itinerary`, `genProd_comm_of_step_comm`): a symmetry of the
seed space that preserves the itinerary is the identity, and a symmetry that merely commutes
with `T` maps whole forward orbits to forward orbits.  The itinerary is the finite-horizon
data of #158; the forward orbit is the only symmetry #181 found.  There is nothing between:
a group action on seeds either fixes the branch pointwise or is unconstrained by arithmetic.

`step_two_eq_step_three`: `T` is not injective (`T 2 = T 3 = 6`), so no inverse dynamics
exists and the ambient object of any action is the backward *tree*, not a group orbit.
-/

noncomputable section
open Classical

namespace GreedyRigidity

/-- The greedy step on seeds, `T m = m · minFac (m + 1)`; it is `genProd m 1`. -/
def step (m : ℕ) : ℕ := m * Nat.minFac (m + 1)

theorem step_eq_genProd_one (m : ℕ) : step m = genProd m 1 := rfl

/-- `T` is not injective: `T 2 = T 3 = 6`. -/
theorem step_two_eq_step_three : step 2 = step 3 := by norm_num [step]

/-! ## 1. Affine rigidity -/

/-- **Affine rigidity.**  If `m ↦ a m + b` (`a ≥ 1`) commutes with the greedy step on every
seed `m ≥ 1`, then `a = 1` and `b = 0`. -/
theorem affine_commute_eq_id {a b : ℕ} (ha : 1 ≤ a)
    (h : ∀ m, 1 ≤ m → step (a * m + b) = a * step m + b) : a = 1 ∧ b = 0 := by
  -- `m = 1` forces `b = 0`: `(a + b) · minFac (a + b + 1) = 2a + b` with `minFac ≥ 2`.
  have hb : b = 0 := by
    have h1 := h 1 le_rfl
    have hmf : 2 ≤ Nat.minFac (a * 1 + b + 1) := (Nat.minFac_prime (by omega)).two_le
    have hstep1 : step 1 = 2 := by norm_num [step]
    rw [hstep1] at h1
    unfold step at h1
    nlinarith [Nat.mul_le_mul_left (a * 1 + b) hmf]
  subst hb
  refine ⟨?_, rfl⟩
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  -- for a prime `r = s + 1 ≥ a`, the seed `m = s` forces `r ∣ c`.
  obtain ⟨r, hra, hr⟩ := Nat.exists_infinite_primes (c + 1)
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by have := hr.two_le; omega⟩
  have hs : 1 ≤ s := by have := hr.two_le; omega
  have hm := h s hs
  simp only [step, add_zero] at hm
  rw [hr.minFac_eq] at hm
  -- cancel `(c + 1) s`
  have hcancel : Nat.minFac ((c + 1) * s + 1) = s + 1 := by
    have hpos : 0 < (c + 1) * s := Nat.mul_pos (Nat.succ_pos c) hs
    have : (c + 1) * s * Nat.minFac ((c + 1) * s + 1) = (c + 1) * s * (s + 1) := by
      rw [hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hdvd1 : s + 1 ∣ (c + 1) * s + 1 := hcancel ▸ Nat.minFac_dvd _
  have hdvd2 : s + 1 ∣ (c + 1) * s + (c + 1) := by
    have : (c + 1) * s + (c + 1) = (c + 1) * (s + 1) := by ring
    rw [this]; exact Dvd.intro_left _ rfl
  have hdvdc : s + 1 ∣ c := by
    have := Nat.dvd_sub hdvd2 hdvd1
    rwa [Nat.add_sub_add_left, Nat.add_sub_cancel] at this
  have hc : c = 0 := Nat.eq_zero_of_dvd_of_lt hdvdc (by omega)
  omega

/-! ## 2. Itinerary rigidity -/

/-- The accumulator is the seed times the product of the multipliers so far. -/
theorem genProd_eq_mul_prod (m k : ℕ) :
    genProd m k = m * ∏ j ∈ Finset.range k, genSeq m j := by
  induction k with
  | zero => simp [genProd]
  | succ k ih => rw [genProd_succ, Finset.prod_range_succ, ih, mul_assoc]

/-- A multiplier is coprime to the product of the earlier multipliers (they are distinct
primes). -/
theorem genSeq_coprime_prod_range {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    Nat.Coprime (genSeq m k) (∏ j ∈ Finset.range k, genSeq m j) := by
  have hp : (genSeq m k).Prime := genSeq_prime hm k
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  obtain ⟨j, hj, hjd⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  have hpj : (genSeq m j).Prime := genSeq_prime hm j
  have heq : genSeq m k = genSeq m j := (Nat.prime_dvd_prime_iff_eq hp hpj).mp hjd
  exact AdelicShadow.genSeq_ne_of_lt hm (Finset.mem_range.mp hj) heq

/-- Two seeds with the same itinerary are congruent modulo every multiplier. -/
theorem genSeq_dvd_sub_of_itinerary_eq {m m' : ℕ} (hm : 1 ≤ m)
    (h : ∀ j, genSeq m j = genSeq m' j) (k : ℕ) : genSeq m k ∣ m - m' := by
  have hP : ∏ j ∈ Finset.range k, genSeq m' j = ∏ j ∈ Finset.range k, genSeq m j :=
    Finset.prod_congr rfl (fun j _ => (h j).symm)
  have h1 : genSeq m k ∣ m * ∏ j ∈ Finset.range k, genSeq m j + 1 := by
    rw [← genProd_eq_mul_prod]; exact Nat.minFac_dvd _
  have h2 : genSeq m k ∣ m' * ∏ j ∈ Finset.range k, genSeq m j + 1 := by
    rw [← hP, ← genProd_eq_mul_prod, h k]; exact Nat.minFac_dvd _
  have h3 : genSeq m k ∣ (m - m') * ∏ j ∈ Finset.range k, genSeq m j := by
    have := Nat.dvd_sub h1 h2
    rwa [Nat.add_sub_add_right, ← Nat.sub_mul] at this
  exact (genSeq_coprime_prod_range hm k).dvd_of_dvd_mul_right h3

/-- The multipliers of a seed `m ≥ 1` are pairwise distinct. -/
theorem genSeq_injective_of_pos {m : ℕ} (hm : 1 ≤ m) : Function.Injective (genSeq m) := by
  intro j k hjk
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact AdelicShadow.genSeq_ne_of_lt hm hlt hjk.symm
  · exact AdelicShadow.genSeq_ne_of_lt hm hlt hjk

/-- The multipliers of a seed `m ≥ 1` are unbounded. -/
theorem exists_genSeq_gt {m : ℕ} (hm : 1 ≤ m) (N : ℕ) : ∃ k, N < genSeq m k := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  exact Set.infinite_range_of_injective (genSeq_injective_of_pos hm)
    ((Set.finite_Iic N).subset (by rintro _ ⟨k, rfl⟩; exact Set.mem_Iic.mpr (hcon k)))

/-- **Itinerary rigidity.**  Two seeds `m, m' ≥ 1` with identical multiplier sequences are
equal: the branch determines its seed, so the stabiliser of the branch in any group acting on
seeds and preserving itineraries is trivial. -/
theorem eq_of_itinerary_eq {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m')
    (h : ∀ j, genSeq m j = genSeq m' j) : m = m' := by
  wlog hle : m' ≤ m generalizing m m'
  · exact (this hm' hm (fun j => (h j).symm) (le_of_not_ge hle)).symm
  obtain ⟨k, hk⟩ := exists_genSeq_gt hm (m - m')
  have hdvd := genSeq_dvd_sub_of_itinerary_eq hm h k
  have := Nat.eq_zero_of_dvd_of_lt hdvd hk
  omega

/-! ## 3. Consequences for symmetries of the seed space -/

/-- A map of seeds that preserves the itinerary is the identity on seeds `≥ 1`. -/
theorem eq_id_of_preserves_itinerary (φ : ℕ → ℕ) (hφ : ∀ m, 1 ≤ m → 1 ≤ φ m)
    (h : ∀ m, 1 ≤ m → ∀ j, genSeq (φ m) j = genSeq m j) : ∀ m, 1 ≤ m → φ m = m :=
  fun m hm => eq_of_itinerary_eq (hφ m hm) hm (h m hm)

/-- A map of seeds commuting with the greedy step maps forward orbits to forward orbits. -/
theorem genProd_comm_of_step_comm (φ : ℕ → ℕ) (h : ∀ m, step (φ m) = φ (step m)) (m k : ℕ) :
    genProd (φ m) k = φ (genProd m k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : genProd (φ m) (k + 1) = step (genProd (φ m) k) := rfl
    rw [this, ih, h]; rfl

end GreedyRigidity
