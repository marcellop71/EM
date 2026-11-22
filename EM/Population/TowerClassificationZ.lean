import EM.Population.QuadraticStep
import EM.Population.BackwardOrbit

/-!
# The classification by the tower over `ℤ`

2026-11-22.  The integer counterpart of `FunctionField/TowerClassification.lean`.

Over `𝔽_p[X]` the family is the set of all sequences over a fixed `p`, and

  `FFMullinConjecture p ↔ ¬ Stable p ∧ FFDichotomy p`.

Over `ℤ` the family is the set of all seeds `m ≥ 2` of the greedy rule
`genProd m (k+1) = genProd m k * minFac (genProd m k + 1)`.  The role of `Stable p` is played
by one statement about the single map `x ↦ x² − x + 1`:

* `PrimeTower` — some integer `s` has all its iterates under `x ↦ x² − x + 1` prime.

## Results

* `genProd_add_one_eq_tower` — on a run of prime stages the Euclid numbers of any seed are
  the Sylvester tower.
* `primeTower_iff_exists_sgrowth_pos` — `PrimeTower` iff some seed has positive growth
  constant, i.e. iff some orbit is eventually a tower.
* `not_allSeedsMC_of_primeTower` — a prime tower refutes the all-seeds conjecture.
* **`allSeedsMC_iff_not_primeTower_and_dichotomy`** —
  `AllSeedsMC ↔ ¬ PrimeTower ∧ Dichotomy.DichotomyConjecture`.
* `mc_of_not_primeTower_of_dichotomy` — the orbit of `2` under the two clauses.
* `seed_notMem_preZero_of_primeTower` — the local shadow of a prime tower: its seed avoids
  the backward orbit of `0` under `Φ₆` modulo every smaller prime.

## Reading

Two differences from the function-field statement.

1. Over `𝔽_p[X]` a run of prime stages is a composition of polynomials, so one family of
   level polynomials bounds the runs of every sequence at once, and stability is decided by
   `p`.  Over `ℤ` a run is an orbit of an integer, and whether it stays prime depends on the
   starting integer: `PrimeTower` is an existential over seeds.  For the same reason there is
   no integer analogue of `ffDichotomy_of_stable`: one prime tower does not make every orbit
   a tower.
2. `¬ PrimeTower` is a statement of the same type as "infinitely many Fermat numbers are
   composite": open, with no known method.  Over `𝔽_p[X]` the corresponding clause
   `¬ Stable p` is a theorem for `p = 2, 3` and `p ≡ 1 (mod 3)`.

No prime is captured by anything in this file.  It records which two clauses the all-seeds
conjecture over `ℤ` is equivalent to.
-/

noncomputable section
open Classical Mullin SeededGrowth

namespace TowerClassificationZ

open SylvesterTower

/-- Some integer has all its iterates under `x ↦ x² − x + 1` prime. -/
def PrimeTower : Prop := ∃ s : ℕ, ∀ k, Nat.Prime (tower s k)

/-- The greedy rule captures every prime coprime to the seed, for every seed. -/
def AllSeedsMC : Prop := ∀ m : ℕ, 2 ≤ m → GenMullinConjecture m

/-! ## 1. A run of prime stages is the tower -/

/-- On a run of prime stages from `N`, the Euclid numbers of the seed `m` are the Sylvester
tower seeded at `genProd m N + 1`. -/
theorem genProd_add_one_eq_tower {m N : ℕ}
    (h : ∀ n, N ≤ n → Nat.Prime (genProd m n + 1)) (k : ℕ) :
    genProd m (N + k) + 1 = tower (genProd m N + 1) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep : genProd m (N + k + 1) = genProd m (N + k) * (genProd m (N + k) + 1) := by
        rw [genProd_succ, genSeq_def, (h (N + k) (Nat.le_add_right N k)).minFac_eq]
      rw [tower_succ, ← ih, Nat.add_sub_cancel, show N + (k + 1) = N + k + 1 from rfl,
        hstep, Nat.mul_comm]

/-- Conversely, if the tower seeded at `m + 1` is prime at every level, the orbit of `m` is
that tower from stage `0`. -/
theorem genProd_add_one_eq_tower_of_prime {m : ℕ} (h : ∀ k, Nat.Prime (tower (m + 1) k))
    (k : ℕ) : genProd m k + 1 = tower (m + 1) k := by
  induction k with
  | zero => simp [genProd]
  | succ k ih =>
      have hp : Nat.Prime (genProd m k + 1) := by rw [ih]; exact h k
      have hstep : genProd m (k + 1) = genProd m k * (genProd m k + 1) := by
        rw [genProd_succ, genSeq_def, hp.minFac_eq]
      rw [tower_succ, ← ih, Nat.add_sub_cancel, hstep, Nat.mul_comm]

/-- The tower seeded at `tower s 1` is the tower seeded at `s`, shifted by one level. -/
theorem tower_tower_one (s k : ℕ) : tower (tower s 1) k = tower s (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [tower_succ, ih, ← tower_succ]

/-! ## 2. `PrimeTower` is "some orbit is eventually a tower" -/

/-- A prime tower can be taken with seed at least `3`. -/
theorem exists_three_le_of_primeTower (h : PrimeTower) :
    ∃ s : ℕ, 3 ≤ s ∧ ∀ k, Nat.Prime (tower s k) := by
  obtain ⟨s, hs⟩ := h
  have h2 : 2 ≤ s := by simpa using (hs 0).two_le
  rcases Nat.lt_or_ge s 3 with hlt | hge
  · -- `s = 2`: pass to the next level, which is `3`
    have hs2 : s = 2 := by omega
    subst hs2
    refine ⟨tower 2 1, ?_, fun k => ?_⟩
    · simp [tower]
    · rw [tower_tower_one]; exact hs (k + 1)
  · exact ⟨s, hge, hs⟩

/-- **`PrimeTower` iff some seed has positive growth constant.** -/
theorem primeTower_iff_exists_sgrowth_pos :
    PrimeTower ↔ ∃ m : ℕ, 2 ≤ m ∧ 0 < sgrowth m := by
  constructor
  · intro h
    obtain ⟨s, hs3, hs⟩ := exists_three_le_of_primeTower h
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
    have hm : 2 ≤ m := by omega
    refine ⟨m, hm, (sgrowth_pos_iff_eventually_prime hm).mpr ⟨0, fun n _ => ?_⟩⟩
    rw [genProd_add_one_eq_tower_of_prime hs n]
    exact hs n
  · rintro ⟨m, hm, hpos⟩
    obtain ⟨N, hN⟩ := (sgrowth_pos_iff_eventually_prime hm).mp hpos
    refine ⟨genProd m N + 1, fun k => ?_⟩
    rw [← genProd_add_one_eq_tower hN k]
    exact hN (N + k) (Nat.le_add_right N k)

/-- Without a prime tower every seed has infinitely many composite stages. -/
theorem sgrowth_eq_zero_of_not_primeTower (h : ¬ PrimeTower) {m : ℕ} (hm : 2 ≤ m) :
    sgrowth m = 0 := by
  by_contra hne
  exact h (primeTower_iff_exists_sgrowth_pos.mpr
    ⟨m, hm, lt_of_le_of_ne (sgrowth_nonneg hm) (Ne.symm hne)⟩)

/-- `¬ PrimeTower` iff every seed has infinitely many composite Euclid numbers. -/
theorem not_primeTower_iff_all_seeds_composite :
    ¬ PrimeTower ↔ ∀ m : ℕ, 2 ≤ m → SeedInfinitelyManyComposite m := by
  constructor
  · intro h m hm
    exact (seedInfinitelyManyComposite_iff_sgrowth_eq_zero hm).mpr
      (sgrowth_eq_zero_of_not_primeTower h hm)
  · intro h hT
    obtain ⟨m, hm, hpos⟩ := primeTower_iff_exists_sgrowth_pos.mp hT
    have := (seedInfinitelyManyComposite_iff_sgrowth_eq_zero hm).mp (h m hm)
    linarith

/-! ## 3. The classification -/

/-- A prime tower refutes the all-seeds conjecture. -/
theorem not_allSeedsMC_of_primeTower (h : PrimeTower) : ¬ AllSeedsMC := by
  intro hall
  obtain ⟨m, hm, hpos⟩ := primeTower_iff_exists_sgrowth_pos.mp h
  have := QuadraticStep.sgrowth_eq_zero_of_genMC hm (hall m hm)
  linarith

/-- Without a prime tower, the all-seeds conjecture is the dichotomy conjecture. -/
theorem allSeedsMC_iff_dichotomy_of_not_primeTower (h : ¬ PrimeTower) :
    AllSeedsMC ↔ Dichotomy.DichotomyConjecture := by
  constructor
  · intro hall m hm
    exact ⟨fun _ => sgrowth_eq_zero_of_not_primeTower h hm, fun _ => hall m hm⟩
  · intro hd m hm
    exact (hd m hm).mpr (sgrowth_eq_zero_of_not_primeTower h hm)

/-- **The classification over `ℤ`.**  The greedy rule captures every prime from every seed
iff no integer has all its iterates under `x ↦ x² − x + 1` prime, and every orbit that
misses a prime is eventually a tower. -/
theorem allSeedsMC_iff_not_primeTower_and_dichotomy :
    AllSeedsMC ↔ ¬ PrimeTower ∧ Dichotomy.DichotomyConjecture := by
  constructor
  · intro hall
    have hT : ¬ PrimeTower := fun hT => not_allSeedsMC_of_primeTower hT hall
    exact ⟨hT, (allSeedsMC_iff_dichotomy_of_not_primeTower hT).mp hall⟩
  · rintro ⟨hT, hd⟩
    exact (allSeedsMC_iff_dichotomy_of_not_primeTower hT).mpr hd

/-- The orbit of `2` under the two clauses. -/
theorem mc_of_not_primeTower_of_dichotomy (hT : ¬ PrimeTower)
    (hd : Dichotomy.DichotomyConjecture) : MullinConjecture :=
  gen_mc_two_iff_mc.mp ((allSeedsMC_iff_not_primeTower_and_dichotomy.mpr ⟨hT, hd⟩) 2 le_rfl)

/-! ## 4. The local shadow of a prime tower -/

open BackwardOrbit in
/-- **A prime tower is locally invisible below its seed.**  If every level of the tower
seeded at `s` is prime, then for every prime `ℓ < s` the residue of `s` modulo `ℓ` is not in
the backward orbit of `0` under `Φ₆`.  This is the integer counterpart of "every level
polynomial is irreducible": a condition at each prime, imposed on one integer. -/
theorem seed_notMem_preZero_of_primeTower {s : ℕ} (hs : ∀ k, Nat.Prime (tower s k))
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ) (hlt : ℓ < s) : ((s : ℕ) : ZMod ℓ) ∉ PreZero ℓ := by
  rintro ⟨k, hk⟩
  have h2 : 2 ≤ s := by simpa using (hs 0).two_le
  have hdvd : ℓ ∣ tower s k := (dvd_tower_iff h2 ℓ k).mpr hk
  have heq : ℓ = tower s k := (Nat.prime_dvd_prime_iff_eq hℓ (hs k)).mp hdvd
  have := self_le_tower h2 k
  omega

end TowerClassificationZ

end
