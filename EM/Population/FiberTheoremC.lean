import EM.Population.TheoremC

/-!
# Theorem C, fibre form

`TheoremC.theorem_C` bounds the number of **good uncaptured seeds** in one period of the
`q`-free dynamics.  Two of the four clauses of `TheoremC.GoodSeed` — namely `¬ q ∣ m` and
`¬ ∃ j < n, genSeq m j = q` — depend on the seed `m` itself and *not* only on the residue
`m mod (modulus q Y)`; the modulus deliberately omits `q`.  Consequently `GoodSeed` is not a
`modulus`-periodic predicate and a bound on its density *inside one period* cannot be turned
into a natural-density statement.

This file removes that obstruction.  The observation is that the capture readoff
`SeedCapture.captured_of_mem_visited` is already stated for a **general fibre seed**
`m' ≡ m [MOD M]`: a full exposed visited set of the (seed-blind) `q`-free reference orbit of
`m` forces capture for *every* seed of the fibre that is coprime to `q`.  The Theorem C
argument therefore never needs `m` itself to be coprime to `q` and uncaptured; it suffices
that **some** seed of the residue fibre of `m` is.  That is `FiberGood`, whose dependence on
`m` runs entirely through `m mod (modulus q Y)`.

## Main results

* `FiberGood` — the fibre-relaxed goodness predicate.
* `goodSeed_fiberGood` — `GoodSeed → FiberGood`, so this is a genuine strengthening.
* `captured_of_visited_full_fiber`, `guard_of_exposed_fiber`, `compensator_lower_fiber` —
  the fibre versions of the three deterministic ingredients.
* `theorem_C_fiber` — the headline, and `theorem_C_of_fiber` re-deriving `TheoremC.theorem_C`.

Session 312, WP-N Part A.
-/

noncomputable section
open Classical

namespace FiberTheoremC

open SeedCapture SeedTypes LargeStepRoughness SelectionLaw LSPlus TheoremC

/-! ## 1. The fibre-relaxed goodness predicate -/

/-- **Fibre-good seeds.**  The prefix of the `q`-free orbit is nondegenerate and `Y`-bounded,
the divisor mass in the exclusion window `(Cc², Y]` is small, and **some** seed of the
residue fibre of `m` modulo `modulus q Y` is coprime to `q` and uncaptured before depth `n`.

Unlike `TheoremC.GoodSeed`, every clause depends on `m` only through data determined by
`m mod (modulus q Y)`: the `q`-free orbit is fibre-measurable, the divisor mass is over
primes `≤ Y` other than `q` (all of which divide the modulus), and the last clause is a
property of the fibre itself. -/
def FiberGood (q Y Cc n m : ℕ) : Prop :=
  (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y) ∧
    (∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m), (1 : ℝ) / r ≤ 1 / Cc) ∧
    (∃ m', 1 ≤ m' ∧ ¬ q ∣ m' ∧ m ≡ m' [MOD SelectionLaw.modulus q Y] ∧
      ¬ ∃ j < n, genSeq m' j = q)

instance decidableFiberGood (q Y Cc n m : ℕ) : Decidable (FiberGood q Y Cc n m) :=
  Classical.propDecidable _

/-- **`FiberGood` is weaker than `GoodSeed`**: take `m' = m`. -/
theorem goodSeed_fiberGood {q Y Cc n m : ℕ} (hm : 1 ≤ m) (h : GoodSeed q Y Cc n m) :
    FiberGood q Y Cc n m := by
  obtain ⟨hqm, hnc, hnd, hdiv⟩ := h
  exact ⟨hnd, hdiv, m, hm, hqm, Nat.ModEq.refl m, hnc⟩

/-! ## 2. The capture readoff, on the fibre -/

/-- **The fibre capture readoff.**  If the exposed visited set of the `q`-free reference
orbit of `m` at depth `n` contains every nonzero residue, then *every* seed `m'` of the
residue fibre of `m` modulo `modulus q Y` which is coprime to `q` has its genuine orbit
select `q` before depth `n`.

This is `TheoremC.captured_of_visited_full` with the fibre seed put back in: the underlying
`SeedCapture.captured_of_mem_visited` was always stated at that generality. -/
theorem captured_of_visited_full_fiber {q Y n m m' : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hm' : 1 ≤ m') (hqm' : ¬ q ∣ m') (hmod : m ≡ m' [MOD SelectionLaw.modulus q Y])
    (hy : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)
    (hfull : ∀ x : ZMod q, x ≠ 0 → x ∈ visitedSetAvoid q m n) :
    ∃ j < n, genSeq m' j = q := by
  have : Fact q.Prime := ⟨hq⟩
  have hmne : ((m' : ℕ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqm'
  set v : ZMod q := -((m' : ℕ) : ZMod q)⁻¹ with hv
  have hvne : v ≠ 0 := by
    rw [hv, neg_ne_zero]
    exact inv_ne_zero hmne
  have hvval : ((m' : ℕ) : ZMod q) = -v⁻¹ := by
    rw [hv, inv_neg, inv_inv, neg_neg]
  exact captured_of_mem_visited hq hm hm' hqm'
    (fun r hr hrY hrq => dvd_modulus hr hrY hrq) hmod hy
    ⟨v, hfull v hvne, hvval⟩

/-! ## 3. The guard at exposed steps of a fibre-good seed -/

/-- **The guard holds at every exposed step of a fibre-good seed.**  A guard failure at an
exposed step fills the visited set with all nonzero residues, and then the fibre capture
readoff forces the witness seed `m'` to be captured — contradicting fibre-goodness. -/
theorem guard_of_exposed_fiber {q Y Cc k₀ n m k : ℕ} (hq : q.Prime) (hm : m ∈ sampleSpace q Y)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)
    (hfib : ∃ m', 1 ≤ m' ∧ ¬ q ∣ m' ∧ m ≡ m' [MOD SelectionLaw.modulus q Y] ∧
      ¬ ∃ j < n, genSeq m' j = q)
    (hdiv : ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m), (1 : ℝ) / r
      ≤ 1 / Cc)
    (hthr : ∀ k < n, (bigThreshold q m Cc k) ^ 2 ≤ Y)
    (hk1 : 1 ≤ k) (hCck : Cc ≤ k) (hk₀ : k₀ ≤ k) (hkn : k < n)
    (hexp : q < genSeqAvoid q m k) :
    guardC q Y Cc (Cc ^ 2) k₀ k (typeData q Y k m) := by
  obtain ⟨m', hm'1, hqm', hmod, hnc⟩ := hfib
  have hm1 : 1 ≤ m := (mem_sampleSpace.mp hm).1
  have hnd' : ∀ j < k, 2 ≤ genSeqAvoid q m j := fun j hj => (hnd j (by omega)).1
  have hzy : Cc ^ 2 ≤ bigThreshold q m Cc k := by
    have hL : k ≤ Nat.log 2 (seedCofactorAvoid q m k) := le_log_cofactor hnd'
    have hLpos : 0 < Nat.log 2 (seedCofactorAvoid q m k) := by omega
    show Cc ^ 2 ≤ Cc * k * Nat.log 2 (seedCofactorAvoid q m k)
    calc Cc ^ 2 = Cc * Cc := by ring
      _ ≤ Cc * k := Nat.mul_le_mul le_rfl hCck
      _ ≤ Cc * k * Nat.log 2 (seedCofactorAvoid q m k) :=
          Nat.le_mul_of_pos_right _ hLpos
  refine ⟨?_, hk₀, m, hm, rfl, fun j hj => hnd j (by omega), hzy, hthr k hkn, hdiv⟩
  -- the prescription clause
  by_contra hemp
  have hc : cellCofactor q Y k (typeData q Y k m) ≠ 0 := by
    rw [cellCofactor_eq hm]
    exact seedCofactorAvoid_ne_zero_zmod hq hm1 hnd'
  have hfull : ∀ x : ZMod q, x ≠ 0 → x ∈ visitedSetAvoid q m (k + 1) := by
    intro x hx
    have := mem_insert_of_goodNatClasses_empty hq hc hemp hx
    rw [cellCofactor_eq hm, cellVisited_eq hm] at this
    rw [visitedSetAvoid_succ_of_exposed hexp]
    exact this
  exact hnc (captured_of_visited_full_fiber hq hm1 hm'1 hqm' hmod hnd
    (fun x hx => visitedSetAvoid_mono (by omega) (hfull x hx)))

/-! ## 4. The compensator lower bound, fibre form -/

/-- **The compensator of a fibre-good seed is large.**  Identical to
`TheoremC.compensator_lower` except that the capture clause is taken on the fibre. -/
theorem compensator_lower_fiber {κ : ℝ} {q Y Cc k₀ n m : ℕ} (hq : q.Prime) (hκ : 0 ≤ κ)
    (hCc : 1 ≤ Cc)
    (hcore : c₁ / 2 * (n : ℝ) ≤ ∑ k ∈ Finset.range n, stepSurvival q m Cc k)
    (hm : m ∈ sampleSpace q Y) (hgood : FiberGood q Y Cc n m)
    (hthr : ∀ k < n, (bigThreshold q m Cc k) ^ 2 ≤ Y) (hCck₀ : Cc ≤ k₀) :
    κ * (c₁ / 2 * (n : ℝ) - ((k₀ + q : ℕ) : ℝ))
      ≤ TreeChernoff.compensator (typeData q Y) (predC κ q Y Cc (Cc ^ 2) k₀) n m := by
  obtain ⟨hnd, hdiv, hfib⟩ := hgood
  have hm1 : 1 ≤ m := (mem_sampleSpace.mp hm).1
  have hndn : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y :=
    fun j hj => hnd j (by omega)
  -- on the good path the predicted survival is the pathwise step survival
  have hcell : ∀ k < n, cellSurvival q Y Cc k (typeData q Y k m) = stepSurvival q m Cc k := by
    intro k hk
    refine cellSurvival_eq hm (fun j hj => hnd j (by omega)) ?_
    exact le_trans (Nat.le_self_pow (by norm_num) _) (hthr k hk)
  have hs1 : ∀ k < n, stepSurvival q m Cc k ≤ 1 := fun k _ =>
    survival_le_one hq hm1 (fun j hj => (hnd j (by omega)).1)
  -- the bad set of depths
  set B := (Finset.range n).filter
    (fun k => ¬ guardC q Y Cc (Cc ^ 2) k₀ k (typeData q Y k m)) with hB
  have hBsub : B ⊆ Finset.range k₀ ∪
      (Finset.range n).filter (fun k => ¬ q < genSeqAvoid q m k) := by
    intro k hk
    rw [hB, Finset.mem_filter, Finset.mem_range] at hk
    by_cases hk₀ : k < k₀
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hk₀)
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk.1, ?_⟩)
      intro hexp
      have hk₀k : k₀ ≤ k := by omega
      exact hk.2 (guard_of_exposed_fiber hq hm hndn hfib hdiv hthr
        (by omega) (le_trans hCck₀ hk₀k) hk₀k hk.1 hexp)
  have hBcard : B.card ≤ k₀ + q := by
    have h1 := Finset.card_le_card hBsub
    have h2 := Finset.card_union_le (Finset.range k₀)
      ((Finset.range n).filter (fun k => ¬ q < genSeqAvoid q m k))
    have h3 := card_unexposed_le (q := q) (m := m) (N := n) hq hm1
      (fun j hj => (hnd j (by omega)).1)
    rw [Finset.card_range] at h2
    omega
  -- split the compensator sum
  rw [TreeChernoff.compensator]
  have hrw : ∀ k ∈ Finset.range n, predC κ q Y Cc (Cc ^ 2) k₀ k (typeData q Y k m)
      = if guardC q Y Cc (Cc ^ 2) k₀ k (typeData q Y k m)
        then κ * stepSurvival q m Cc k else 0 := by
    intro k hk
    rw [predC, hcell k (Finset.mem_range.mp hk)]
  rw [Finset.sum_congr rfl hrw]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range n)
    (fun k => guardC q Y Cc (Cc ^ 2) k₀ k (typeData q Y k m))
    (fun k => κ * stepSurvival q m Cc k)
  have hite : ∑ k ∈ Finset.range n,
      (if guardC q Y Cc (Cc ^ 2) k₀ k (typeData q Y k m)
        then κ * stepSurvival q m Cc k else 0)
      = ∑ k ∈ (Finset.range n).filter
          (fun k => guardC q Y Cc (Cc ^ 2) k₀ k (typeData q Y k m)),
          κ * stepSurvival q m Cc k := (Finset.sum_filter _ _).symm
  rw [hite]
  -- the bad depths cost at most `κ · #B`
  have hbad : ∑ k ∈ B, κ * stepSurvival q m Cc k ≤ κ * ((k₀ + q : ℕ) : ℝ) := by
    have hle : ∑ k ∈ B, κ * stepSurvival q m Cc k ≤ ∑ _k ∈ B, κ := by
      refine Finset.sum_le_sum fun k hk => ?_
      rw [hB, Finset.mem_filter, Finset.mem_range] at hk
      calc κ * stepSurvival q m Cc k ≤ κ * 1 :=
            mul_le_mul_of_nonneg_left (hs1 k hk.1) hκ
        _ = κ := mul_one κ
    rw [Finset.sum_const, nsmul_eq_mul] at hle
    have hcast : (B.card : ℝ) ≤ ((k₀ + q : ℕ) : ℝ) := by exact_mod_cast hBcard
    refine le_trans hle ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hcast hκ
  have htotal : κ * (c₁ / 2 * (n : ℝ)) ≤ ∑ k ∈ Finset.range n, κ * stepSurvival q m Cc k := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hcore hκ
  have := hsplit
  rw [hB] at hbad
  nlinarith [hbad, htotal, this]

/-! ## 5. Theorem C, fibre form -/

/-- **Theorem C, fibre form.**  Identical to `TheoremC.theorem_C` with `GoodSeed` replaced
by the weaker `FiberGood`: the seeds counted need only lie in a residue fibre containing
*some* seed coprime to `q` whose genuine orbit misses `q` before depth `n`.

The point of the relaxation is periodicity: every clause of `FiberGood` is determined by
`m mod (modulus q Y)`, so this bound on one period does transfer to natural density —
which the `GoodSeed` form does not.

Session 312, WP-N Part A. -/
theorem theorem_C_fiber (q Cc : ℕ) (hq : q.Prime) (hCc : 48 * q ≤ Cc) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ K₀ n₁ : ℕ, ∀ Y n : ℕ,
      n₁ ≤ n → (Cc : ℝ) ≤ (n : ℝ) → Real.log Y ≤ (n : ℝ) ^ 2 →
      (∀ m ∈ sampleSpace q Y, FiberGood q Y Cc n m →
        ∀ k < n, (bigThreshold q m Cc k) ^ 2 ≤ Y) →
      (((sampleSpace q Y).filter (fun m => FiberGood q Y Cc n m)).card : ℝ)
        ≤ ((sampleSpace q Y).card : ℝ)
            * Real.exp (-(3 / 8) * (κ * (c₁ / 2 * (n : ℝ) - (K₀ : ℝ)))) := by
  classical
  obtain ⟨κ, hκpos, k₀, hD⟩ := lemmaD_statement q hq Cc hCc (Cc ^ 2)
  obtain ⟨n₀, hpc⟩ := pathwise_compensator
  have hq2 := hq.two_le
  have hCc1 : 1 ≤ Cc := by omega
  set κ' : ℝ := min κ 1 with hκ'
  have hκ'pos : 0 < κ' := lt_min hκpos one_pos
  have hκ'0 : 0 ≤ κ' := hκ'pos.le
  have hκ'1 : κ' ≤ 1 := min_le_right _ _
  have hκ'κ : κ' ≤ κ := min_le_left _ _
  set k₀' : ℕ := max (max 1 k₀) Cc with hk₀'
  set K₀ : ℕ := k₀' + q with hK₀
  have hD' : LemmaDStatement κ' q Cc (Cc ^ 2) k₀' :=
    hD.mono hκ'κ (le_trans (le_max_right 1 k₀) (le_max_left _ _))
  -- the size threshold
  set R : ℝ := 2 * ((K₀ : ℝ) + (8 * (q : ℝ) + 1) / κ') / c₁ with hR
  refine ⟨κ', hκ'pos, K₀, max n₀ ⌈R⌉₊, ?_⟩
  intro Y n hn hCcn hpol hthr
  have hn₀ : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hnR : R ≤ (n : ℝ) := by
    have h1 : ⌈R⌉₊ ≤ n := le_trans (le_max_right _ _) hn
    exact le_trans (Nat.le_ceil R) (by exact_mod_cast h1)
  -- the key numeric consequence: `v ≥ 8q + 1`
  have hc₁ := c₁_pos
  have hvge : 8 * (q : ℝ) + 1 ≤ κ' * (c₁ / 2 * (n : ℝ) - (K₀ : ℝ)) := by
    have h1 : 2 * ((K₀ : ℝ) + (8 * (q : ℝ) + 1) / κ') ≤ c₁ * (n : ℝ) := by
      rw [hR, div_le_iff₀ hc₁] at hnR
      linarith
    have h2 : (8 * (q : ℝ) + 1) / κ' * κ' = 8 * (q : ℝ) + 1 :=
      div_mul_cancel₀ _ hκ'pos.ne'
    nlinarith [hκ'pos, h1, h2]
  set v : ℝ := κ' * (c₁ / 2 * (n : ℝ) - (K₀ : ℝ)) with hv
  have hqR : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hv0 : 0 ≤ v := by linarith
  -- the Chernoff hypotheses
  have hrefine : ∀ k, ∀ ω ∈ sampleSpace q Y, ∀ ω' ∈ sampleSpace q Y,
      typeData q Y (k + 1) ω = typeData q Y (k + 1) ω' →
      typeData q Y k ω = typeData q Y k ω' :=
    fun _ _ _ _ _ h => typeData_refine h
  have hdet : ∀ k, ∀ ω ∈ sampleSpace q Y, ∀ ω' ∈ sampleSpace q Y,
      typeData q Y (k + 1) ω = typeData q Y (k + 1) ω' →
      (successC q Y Cc (Cc ^ 2) k₀' k ω ↔ successC q Y Cc (Cc ^ 2) k₀' k ω') := by
    intro k ω _ ω' _ h
    have hk := (typeData_eq_iff.mp h).1 k (by omega)
    have htyp := typeData_refine h
    have hb := bigThreshold_congr htyp Cc
    rw [successC, successC, htyp, bigStep, bigStep, hk, hb]
  have hS0 : ∀ k ω, ω ∈ sampleSpace q Y →
      0 ≤ predC κ' q Y Cc (Cc ^ 2) k₀' k (typeData q Y k ω) :=
    fun _ _ _ => predC_nonneg hκ'0 hq _
  have hS1 : ∀ k ω, ω ∈ sampleSpace q Y →
      predC κ' q Y Cc (Cc ^ 2) k₀' k (typeData q Y k ω) ≤ 1 :=
    fun _ _ _ => predC_le_one hκ'0 hκ'1 hq _
  have hcher := TreeChernoff.chernoff_quarter_local
    (Ω := sampleSpace q Y) (F := typeData q Y)
    (A := successC q Y Cc (Cc ^ 2) k₀') (S := predC κ' q Y Cc (Cc ^ 2) k₀') (v := v)
    hrefine hdet hS0 hS1 (fun k b => hcondC hq hκ'0 hD' k b) n hv0
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hcher
  -- every fibre-good seed is Chernoff-bad
  intro m hm
  rw [Finset.mem_filter] at hm
  obtain ⟨hmΩ, hgood⟩ := hm
  have hm1 : 1 ≤ m := (mem_sampleSpace.mp hmΩ).1
  obtain ⟨hnd, hdiv, hfib⟩ := hgood
  refine Finset.mem_filter.mpr ⟨hmΩ, ?_, ?_⟩
  · -- hit count is at most `2q < v/4`
    have hcount : (TreeChernoff.hitCount (successC q Y Cc (Cc ^ 2) k₀') n m : ℕ) ≤ 2 * q :=
      success_count_le hq hCc (le_trans (le_max_left 1 k₀) (le_max_left _ _)) hmΩ
        (fun j hj => (hnd j hj).1)
    have hcR : ((TreeChernoff.hitCount (successC q Y Cc (Cc ^ 2) k₀') n m : ℕ) : ℝ)
        ≤ 2 * (q : ℝ) := by exact_mod_cast hcount
    have : 2 * (q : ℝ) < v / 4 := by linarith
    linarith
  · -- compensator is at least `v`
    have hcore := hpc q m Y Cc n hq hm1 hCc1 hCcn (fun j hj => (hnd j (by omega)).1)
      (fun j hj => (hnd j (by omega)).2) hpol hn₀
    have := compensator_lower_fiber (κ := κ') hq hκ'0 hCc1 hcore hmΩ
      ⟨hnd, hdiv, hfib⟩
      (fun k hk => hthr m hmΩ ⟨hnd, hdiv, hfib⟩ k hk)
      (le_trans (le_max_right (max 1 k₀) Cc) le_rfl)
    rw [hv, hK₀]
    exact this

/-- `TheoremC.theorem_C` re-derived from the fibre form: `GoodSeed` seeds are `FiberGood`
seeds (`goodSeed_fiberGood`), so their count is smaller. -/
theorem theorem_C_of_fiber (q Cc : ℕ) (hq : q.Prime) (hCc : 48 * q ≤ Cc) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ K₀ n₁ : ℕ, ∀ Y n : ℕ,
      n₁ ≤ n → (Cc : ℝ) ≤ (n : ℝ) → Real.log Y ≤ (n : ℝ) ^ 2 →
      (∀ m ∈ sampleSpace q Y, FiberGood q Y Cc n m →
        ∀ k < n, (bigThreshold q m Cc k) ^ 2 ≤ Y) →
      (((sampleSpace q Y).filter (fun m => GoodSeed q Y Cc n m)).card : ℝ)
        ≤ ((sampleSpace q Y).card : ℝ)
            * Real.exp (-(3 / 8) * (κ * (c₁ / 2 * (n : ℝ) - (K₀ : ℝ)))) := by
  obtain ⟨κ, hκ, K₀, n₁, h⟩ := theorem_C_fiber q Cc hq hCc
  refine ⟨κ, hκ, K₀, n₁, fun Y n hn hCcn hpol hthr => ?_⟩
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (h Y n hn hCcn hpol hthr)
  intro m hm
  rw [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, goodSeed_fiberGood (mem_sampleSpace.mp hm.1).1 hm.2⟩

end FiberTheoremC

end
