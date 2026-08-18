import EM.Population.LSPlus
import EM.Population.LemmaDBox

/-!
# Theorem C — exponentially few uncaptured seeds

This file assembles the seed-average programme's **Theorem C**: on one full period of the
`q`-free dynamics, the seeds whose genuine orbit fails to select `q` in its first `n` steps
(and which are otherwise *good*: nondegenerate `Y`-bounded prefix, small divisor mass in the
exclusion window) form an **exponentially small** fraction of the period.

## The mechanism, in one paragraph

Fix a type cell `b` at depth `k`.  The cell determines the visited set
`V_k = visitedSetAvoid q · k` and the cofactor class `c_k = seedCofactorAvoid q · k mod q`
(`cellVisited`, `cellCofactor`).  Whenever `V_k ∪ {c_k}` misses a nonzero residue, we may
*prescribe* a multiplier class `w` mod `q` with `c_k · w ∉ V_k ∪ {c_k}` (`goodNatClasses`,
`prescribed`); a seed of the cell **succeeds** at depth `k` if it takes a large step *and*
its `k`-th multiplier lies in the prescribed class (`successC`).  Lemma D (box side,
`LemmaD.lemma_D_z`) says a fixed proportion `κ` of the large-stepping seeds of the cell do
succeed — that is the conditional counting inequality `hcondC` consumed by the abstract tree
Chernoff bound `TreeChernoff.chernoff_quarter_local`.

Two deterministic facts then close the argument:

* **Successes are rare on every path** (`success_count_le`): a success at depth `k` puts the
  *next* cofactor class outside `V_{k+1}`, so the visited set strictly grows two steps later
  — unless the next step is `q`-unexposed, and unexposed steps are `≤ q - 1` by multiplier
  distinctness.  Hence at most `2q` successes, **always**.
* **Uncaptured good paths have a large compensator** (`compensator_lower`): the guard can
  only fail at a `q`-unexposed step, because a failure at an exposed step would make the
  visited set contain *every* nonzero residue, and then the capture identity
  `SeedCapture.captured_iff_mem_visited` would force the genuine orbit to select `q`.

So an uncaptured good seed has hit count `≤ 2q` while its compensator is `≳ κ c₁ n / 2`:
for `n` large this is exactly the Chernoff-bad event.

## Main results

* `cellVisited`, `cellCofactor`, `goodNatClasses`, `prescribed` — the cell-measurable
  prescription, with congruence lemmas (`cellVisited_eq`, `cellCofactor_eq`).
* `guardC`, `successC`, `predC` — the guard, the success event and the predicted probability.
* `hcondC` — the conditional counting inequality (Lemma D in Chernoff shape).
* `success_count_le` — the deterministic bound `#successes ≤ 2q` on **every** path.
* `guard_of_exposed`, `compensator_lower` — the compensator lower bound on uncaptured good
  seeds.
* `theorem_C` — the headline.

`agents/state/findings.md` §"Session 311 — coordinator design"; Session 311, WP-C.
-/

noncomputable section
open Classical

namespace TheoremC

open SeedCapture SeedTypes LargeStepRoughness SelectionLaw LSPlus

/-! ## 1. Cell-measurable visited set and cofactor class -/

/-- The exposed visited set at depth `k` is a function of the type at depth `k`. -/
theorem visitedSetAvoid_congr {q Y k m m' : ℕ} (h : typeData q Y k m = typeData q Y k m') :
    visitedSetAvoid q m k = visitedSetAvoid q m' k := by
  obtain ⟨h1, _⟩ := typeData_eq_iff.mp h
  rw [visitedSetAvoid, visitedSetAvoid]
  have hfil : (Finset.range k).filter (fun j => q < genSeqAvoid q m j)
      = (Finset.range k).filter (fun j => q < genSeqAvoid q m' j) :=
    Finset.filter_congr fun j hj => by rw [h1 j (Finset.mem_range.mp hj)]
  rw [hfil]
  refine Finset.image_congr ?_
  intro j hj
  rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
  show ((seedCofactorAvoid q m j : ℕ) : ZMod q) = ((seedCofactorAvoid q m' j : ℕ) : ZMod q)
  rw [cofactor_congr h (le_of_lt hj.1)]

/-- A type at depth `k` is *realized* when some seed of the period has it. -/
def cellReal (q Y k : ℕ) (b : List ℕ × Finset ℕ) : Prop :=
  ∃ m₀ ∈ sampleSpace q Y, typeData q Y k m₀ = b

/-- **The visited set of a type.**  Well defined: two seeds of the same type have the same
exposed visited set (`visitedSetAvoid_congr`). -/
def cellVisited (q Y k : ℕ) (b : List ℕ × Finset ℕ) : Finset (ZMod q) :=
  if h : cellReal q Y k b then visitedSetAvoid q h.choose k else ∅

/-- **The cofactor class of a type.**  Well defined by `cofactor_congr`. -/
def cellCofactor (q Y k : ℕ) (b : List ℕ × Finset ℕ) : ZMod q :=
  if h : cellReal q Y k b then ((seedCofactorAvoid q h.choose k : ℕ) : ZMod q) else 0

theorem cellVisited_eq {q Y k m : ℕ} (hm : m ∈ sampleSpace q Y) :
    cellVisited q Y k (typeData q Y k m) = visitedSetAvoid q m k := by
  have hr : cellReal q Y k (typeData q Y k m) := ⟨m, hm, rfl⟩
  rw [cellVisited, dif_pos hr]
  exact visitedSetAvoid_congr hr.choose_spec.2

theorem cellCofactor_eq {q Y k m : ℕ} (hm : m ∈ sampleSpace q Y) :
    cellCofactor q Y k (typeData q Y k m) = ((seedCofactorAvoid q m k : ℕ) : ZMod q) := by
  have hr : cellReal q Y k (typeData q Y k m) := ⟨m, hm, rfl⟩
  rw [cellCofactor, dif_pos hr, cofactor_congr hr.choose_spec.2 le_rfl]

/-! ## 2. The prescription -/

/-- **The admissible multiplier classes of a type**: the residues `w` mod `q` (represented by
naturals `< q`) that are nonzero and move the cofactor class *out* of the visited set. -/
def goodNatClasses (q Y k : ℕ) (b : List ℕ × Finset ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun t => ((t : ℕ) : ZMod q) ≠ 0 ∧
    cellCofactor q Y k b * ((t : ℕ) : ZMod q) ∉
      insert (cellCofactor q Y k b) (cellVisited q Y k b))

/-- **The prescribed multiplier class of a type** (`1` when there is none). -/
def prescribed (q Y k : ℕ) (b : List ℕ × Finset ℕ) : ℕ :=
  if h : (goodNatClasses q Y k b).Nonempty then h.choose else 1

theorem prescribed_mem {q Y k : ℕ} {b : List ℕ × Finset ℕ}
    (h : (goodNatClasses q Y k b).Nonempty) : prescribed q Y k b ∈ goodNatClasses q Y k b := by
  rw [prescribed, dif_pos h]; exact h.choose_spec

/-- The prescribed class is coprime to `q` — trivially in the degenerate case (`1`), and by
nonvanishing mod `q` otherwise. -/
theorem prescribed_coprime {q Y k : ℕ} (hq : q.Prime) (b : List ℕ × Finset ℕ) :
    Nat.Coprime (prescribed q Y k b) q := by
  by_cases h : (goodNatClasses q Y k b).Nonempty
  · have hmem := prescribed_mem h
    rw [goodNatClasses, Finset.mem_filter] at hmem
    have hne : ((prescribed q Y k b : ℕ) : ZMod q) ≠ 0 := hmem.2.1
    have hnd : ¬ q ∣ prescribed q Y k b := by
      intro hd; exact hne ((ZMod.natCast_eq_zero_iff _ _).mpr hd)
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr hnd |>.symm
  · rw [prescribed, dif_neg h]; exact Nat.coprime_one_left q

/-- **Surjectivity of the prescription mechanism.**  If no class is admissible, then the
visited set together with the cofactor class already covers *every* nonzero residue. -/
theorem mem_insert_of_goodNatClasses_empty {q Y k : ℕ} {b : List ℕ × Finset ℕ} (hq : q.Prime)
    (hc : cellCofactor q Y k b ≠ 0) (hemp : ¬ (goodNatClasses q Y k b).Nonempty)
    {x : ZMod q} (hx : x ≠ 0) :
    x ∈ insert (cellCofactor q Y k b) (cellVisited q Y k b) := by
  have : Fact q.Prime := ⟨hq⟩
  have : NeZero q := ⟨hq.pos.ne'⟩
  set c := cellCofactor q Y k b with hcdef
  obtain ⟨t, ht⟩ := ZMod.natCast_zmod_surjective (n := q) (c⁻¹ * x)
  have hmod : ((t % q : ℕ) : ZMod q) = c⁻¹ * x := by
    rw [ZMod.natCast_mod]; exact ht
  have hlt : t % q < q := Nat.mod_lt _ hq.pos
  have hne0 : ((t % q : ℕ) : ZMod q) ≠ 0 := by
    rw [hmod]
    exact mul_ne_zero (inv_ne_zero hc) hx
  have hcx : c * ((t % q : ℕ) : ZMod q) = x := by
    rw [hmod, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  by_contra hcon
  refine hemp ⟨t % q, ?_⟩
  rw [goodNatClasses, Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr hlt, hne0, by rw [hcx]; exact hcon⟩

/-! ## 3. Guard, success event, predicted probability -/

/-- **The guard of a type.**  A prescription exists, the depth is past the Lemma-D threshold,
and the type is realized by a seed whose prefix is nondegenerate and `Y`-bounded, whose moving
threshold sits inside the exclusion window `(z, √Y]`, and whose divisor mass in that window is
small. -/
def guardC (q Y Cc z k₀ k : ℕ) (b : List ℕ × Finset ℕ) : Prop :=
  (goodNatClasses q Y k b).Nonempty ∧ k₀ ≤ k ∧
    ∃ m₀ ∈ sampleSpace q Y, typeData q Y k m₀ = b ∧
      (∀ j < k, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y) ∧
      z ≤ bigThreshold q m₀ Cc k ∧ (bigThreshold q m₀ Cc k) ^ 2 ≤ Y ∧
      (∑ r ∈ (Finset.Ioc z Y).filter (fun r => r.Prime ∧ r ∣ m₀), (1 : ℝ) / r ≤ 1 / Cc)

instance decidableGuardC (q Y Cc z k₀ k : ℕ) (b : List ℕ × Finset ℕ) :
    Decidable (guardC q Y Cc z k₀ k b) := Classical.propDecidable _

/-- **The success event at depth `k`**: the guard holds, the step is large, and the multiplier
falls into the prescribed class. -/
def successC (q Y Cc z k₀ k m : ℕ) : Prop :=
  guardC q Y Cc z k₀ k (typeData q Y k m) ∧ bigStep q Cc k m ∧
    genSeqAvoid q m k % q = prescribed q Y k (typeData q Y k m) % q

instance decidableSuccessC (q Y Cc z k₀ k m : ℕ) :
    Decidable (successC q Y Cc z k₀ k m) := Classical.propDecidable _

/-- **The predicted conditional success probability of a type.** -/
def predC (κ : ℝ) (q Y Cc z k₀ k : ℕ) (b : List ℕ × Finset ℕ) : ℝ :=
  if guardC q Y Cc z k₀ k b then κ * cellSurvival q Y Cc k b else 0

theorem predC_nonneg {κ : ℝ} (hκ : 0 ≤ κ) {q Y Cc z k₀ k : ℕ} (hq : q.Prime)
    (b : List ℕ × Finset ℕ) : 0 ≤ predC κ q Y Cc z k₀ k b := by
  rw [predC]
  split
  · exact mul_nonneg hκ (cellSurvival_nonneg hq b)
  · exact le_rfl

theorem predC_le_one {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) {q Y Cc z k₀ k : ℕ} (hq : q.Prime)
    (b : List ℕ × Finset ℕ) : predC κ q Y Cc z k₀ k b ≤ 1 := by
  rw [predC]
  split
  · calc κ * cellSurvival q Y Cc k b ≤ κ * 1 :=
          mul_le_mul_of_nonneg_left (cellSurvival_le_one hq b) hκ0
      _ = κ := mul_one κ
      _ ≤ 1 := hκ1
  · exact zero_le_one

/-! ## 4. Lemma D, packaged -/

/-- The conclusion of `LemmaD.lemma_D_z`, as a named property of the constants. -/
def LemmaDStatement (κ : ℝ) (q Cc z k₀ : ℕ) : Prop :=
  ∀ Y k m₀ a : ℕ, 1 ≤ m₀ →
    (∀ j < k, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y) → k₀ ≤ k →
    z ≤ bigThreshold q m₀ Cc k → (bigThreshold q m₀ Cc k) ^ 2 ≤ Y →
    (∑ r ∈ (Finset.Ioc z Y).filter (fun r => r.Prime ∧ r ∣ m₀), (1 : ℝ) / r ≤ 1 / Cc) →
    Nat.Coprime a q →
    κ * (((stepCell q Y k m₀).filter
           (fun m => SurvivesUpTo q (bigThreshold q m₀ Cc k) k m)).card : ℝ)
      ≤ (((stepCell q Y k m₀).filter
           (fun m => SurvivesUpTo q (bigThreshold q m₀ Cc k) k m
             ∧ genSeqAvoid q m k % q = a % q)).card : ℝ)

theorem lemmaD_statement (q : ℕ) (hq : q.Prime) (Cc : ℕ) (hCc : 48 * q ≤ Cc) (z : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ k₀ : ℕ, LemmaDStatement κ q Cc z k₀ :=
  LemmaD.lemma_D_z q hq Cc hCc z

theorem LemmaDStatement.mono {κ κ' : ℝ} {q Cc z k₀ k₀' : ℕ} (h : LemmaDStatement κ q Cc z k₀)
    (hκ : κ' ≤ κ) (hk : k₀ ≤ k₀') : LemmaDStatement κ' q Cc z k₀' := by
  intro Y k m₀ a hm hnd hk₀ hz hyY hdiv hcop
  refine le_trans ?_ (h Y k m₀ a hm hnd (le_trans hk hk₀) hz hyY hdiv hcop)
  exact mul_le_mul_of_nonneg_right hκ (Nat.cast_nonneg _)

/-! ## 5. `hcond`: Lemma D in the shape the tree Chernoff bound consumes -/

/-- **The conditional counting inequality.**  Inside a guarded type cell, the fraction of
seeds that both take a large step and land in the prescribed class is at least `κ` times the
predicted survival — that is Lemma D (box side). -/
theorem hcondC {κ : ℝ} {q Y Cc z k₀ : ℕ} (hq : q.Prime) (hκ : 0 ≤ κ)
    (hD : LemmaDStatement κ q Cc z k₀) (k : ℕ) (b : List ℕ × Finset ℕ) :
    predC κ q Y Cc z k₀ k b
        * (((sampleSpace q Y).filter (fun m => typeData q Y k m = b)).card : ℝ)
      ≤ (((sampleSpace q Y).filter
          (fun m => typeData q Y k m = b ∧ successC q Y Cc z k₀ k m)).card : ℝ) := by
  by_cases hg : guardC q Y Cc z k₀ k b
  · obtain ⟨hne, hk₀, m₀, hm₀mem, hm₀typ, hm₀nd, hz, hyY, hdiv⟩ := hg
    have hgfull : guardC q Y Cc z k₀ k b := ⟨hne, hk₀, m₀, hm₀mem, hm₀typ, hm₀nd, hz, hyY, hdiv⟩
    subst hm₀typ
    have hthr : bigThreshold q m₀ Cc k ≤ Y :=
      le_trans (Nat.le_self_pow (by norm_num) _) hyY
    -- the success set inside the cell
    have hand : (sampleSpace q Y).filter
          (fun m => typeData q Y k m = typeData q Y k m₀ ∧ successC q Y Cc z k₀ k m)
        = (stepCell q Y k m₀).filter
          (fun m => SurvivesUpTo q (bigThreshold q m₀ Cc k) k m
            ∧ genSeqAvoid q m k % q = prescribed q Y k (typeData q Y k m₀) % q) := by
      ext m
      rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro ⟨hmem, htyp, _, hbs, hcls⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [← fiber_eq_stepCell q Y k m₀]
          exact Finset.mem_filter.mpr ⟨hmem, htyp⟩
        · have hsv := (bigStep_iff_survives hq).mp hbs
          rwa [bigThreshold_congr htyp Cc] at hsv
        · rwa [htyp] at hcls
      · rintro ⟨hcell, hsurv, hcls⟩
        have hmemf : m ∈ (sampleSpace q Y).filter
            (fun m => typeData q Y k m = typeData q Y k m₀) := by
          rw [fiber_eq_stepCell]; exact hcell
        obtain ⟨hmem, htyp⟩ := Finset.mem_filter.mp hmemf
        refine ⟨hmem, htyp, ?_, (bigStep_iff_survives hq).mpr ?_, ?_⟩
        · rwa [htyp]
        · rwa [bigThreshold_congr htyp Cc]
        · rwa [htyp]
    rw [hand, predC, if_pos hgfull, fiber_eq_stepCell,
      cellSurvival_eq hm₀mem hm₀nd hthr, stepSurvival, mul_assoc]
    have hsel := selection_law_ge hq (mem_sampleSpace.mp hm₀mem).1 hm₀nd hthr
    have hkey := hD Y k m₀ (prescribed q Y k (typeData q Y k m₀))
      (mem_sampleSpace.mp hm₀mem).1 hm₀nd hk₀ hz hyY hdiv (prescribed_coprime hq _)
    exact le_trans (mul_le_mul_of_nonneg_left hsel hκ) hkey
  · rw [predC, if_neg hg, zero_mul]
    exact Nat.cast_nonneg _

/-! ## 6. Structure of the exposed visited set -/

theorem visitedSetAvoid_succ_of_exposed {q m k : ℕ} (h : q < genSeqAvoid q m k) :
    visitedSetAvoid q m (k + 1)
      = insert ((seedCofactorAvoid q m k : ℕ) : ZMod q) (visitedSetAvoid q m k) := by
  rw [visitedSetAvoid, visitedSetAvoid, Finset.range_add_one, Finset.filter_insert, if_pos h,
    Finset.image_insert]

theorem visitedSetAvoid_mono {q m j k : ℕ} (h : j ≤ k) :
    visitedSetAvoid q m j ⊆ visitedSetAvoid q m k := by
  have hsub : Finset.range j ⊆ Finset.range k := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)
  rw [visitedSetAvoid, visitedSetAvoid]
  exact Finset.image_subset_image (Finset.filter_subset_filter _ hsub)

/-- The visited set consists of nonzero residues, hence has at most `q - 1` elements. -/
theorem visitedSetAvoid_card_le_pred {q m k : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < k, 2 ≤ genSeqAvoid q m j) : (visitedSetAvoid q m k).card ≤ q - 1 := by
  have : NeZero q := ⟨hq.pos.ne'⟩
  have hsub : visitedSetAvoid q m k ⊆ (Finset.univ : Finset (ZMod q)).erase 0 := by
    intro v hv
    obtain ⟨j, hj, _, hveq⟩ := mem_visitedSetAvoid hv
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    rw [← hveq]
    exact seedCofactorAvoid_ne_zero_zmod hq hm (fun i hi => hnd i (lt_trans hi hj))
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/-- Counting strict increases of a monotone integer sequence. -/
theorem count_strict_increase (c : ℕ → ℕ) (hmono : ∀ j, c j ≤ c (j + 1)) (N : ℕ) :
    ((Finset.range N).filter (fun j => c j < c (j + 1))).card + c 0 ≤ c N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    have hm := hmono N
    by_cases h : c N < c (N + 1)
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
      omega
    · rw [if_neg h]
      omega

/-! ## 7. Multiplier distinctness and the unexposed steps -/

theorem genSeqAvoid_dvd_cofactor {q m i j : ℕ} (h : i < j) :
    genSeqAvoid q m i ∣ seedCofactorAvoid q m j :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr h)

/-- Distinct depths carry distinct multipliers. -/
theorem genSeqAvoid_inj {q m N : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < N, 2 ≤ genSeqAvoid q m j) {i j : ℕ} (hi : i < N) (hj : j < N)
    (h : genSeqAvoid q m i = genSeqAvoid q m j) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd (by rw [← h]; exact genSeqAvoid_dvd_cofactor (q := q) (m := m) hlt)
      (multiplier_not_dvd_cofactor hq hm (hnd j hj))
  · exact heq
  · exact absurd (by rw [h]; exact genSeqAvoid_dvd_cofactor (q := q) (m := m) hgt)
      (multiplier_not_dvd_cofactor hq hm (hnd i hi))

/-- At most `q - 1` of the first `N` steps are `q`-unexposed. -/
theorem card_unexposed_le {q m N : ℕ} (hq : q.Prime) (hm : 1 ≤ m)
    (hnd : ∀ j < N, 2 ≤ genSeqAvoid q m j) :
    ((Finset.range N).filter (fun j => ¬ q < genSeqAvoid q m j)).card ≤ q - 1 := by
  have hcard : ((Finset.range N).filter (fun j => ¬ q < genSeqAvoid q m j)).card
      ≤ (Finset.Icc 2 q).card := by
    refine Finset.card_le_card_of_injOn (fun j => genSeqAvoid q m j) ?_ ?_
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
      simp only [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨hnd j hj.1, by omega⟩
    · intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hj
      exact genSeqAvoid_inj hq hm hnd hi.1 hj.1 hij
  rw [Nat.card_Icc] at hcard
  omega

/-! ## 8. The deterministic success-count bound -/

/-- A success is `q`-exposed: the large step exceeds the moving threshold, which itself
exceeds `Cc ≥ 48 q`. -/
theorem exposed_of_success {q Y Cc z k₀ k m : ℕ} (hq : q.Prime) (hCc : 48 * q ≤ Cc)
    (hk₀ : 1 ≤ k₀) (hnd : ∀ j < k + 1, 2 ≤ genSeqAvoid q m j)
    (hs : successC q Y Cc z k₀ k m) : q < genSeqAvoid q m k := by
  obtain ⟨⟨_, hk₀k, _⟩, hbs, _⟩ := hs
  have hk1 : 1 ≤ k := le_trans hk₀ hk₀k
  have hL : 1 ≤ Nat.log 2 (seedCofactorAvoid q m k) :=
    le_trans hk1 (le_log_cofactor (fun j hj => hnd j (by omega)))
  have hy : Cc ≤ bigThreshold q m Cc k := by
    show Cc ≤ Cc * k * Nat.log 2 (seedCofactorAvoid q m k)
    calc Cc = Cc * 1 * 1 := by ring
      _ ≤ Cc * k * Nat.log 2 (seedCofactorAvoid q m k) :=
          Nat.mul_le_mul (Nat.mul_le_mul le_rfl hk1) hL
  have h2 := hnd k (by omega)
  have hq2 := hq.two_le
  rcases hbs with h1 | hgt
  · omega
  · omega

/-- **The success mechanism.**  A success at depth `k` puts the *next* cofactor class outside
the visited set at depth `k + 1`. -/
theorem cofactor_notMem_of_success {q Y Cc z k₀ k m : ℕ} (hq : q.Prime) (hCc : 48 * q ≤ Cc)
    (hk₀ : 1 ≤ k₀) (hm : m ∈ sampleSpace q Y) (hnd : ∀ j < k + 1, 2 ≤ genSeqAvoid q m j)
    (hs : successC q Y Cc z k₀ k m) :
    ((seedCofactorAvoid q m (k + 1) : ℕ) : ZMod q) ∉ visitedSetAvoid q m (k + 1) := by
  have hexp : q < genSeqAvoid q m k := exposed_of_success hq hCc hk₀ hnd hs
  obtain ⟨⟨hne, _, _⟩, _, hcls⟩ := hs
  have hmem := prescribed_mem hne
  rw [goodNatClasses, Finset.mem_filter, cellCofactor_eq hm, cellVisited_eq hm] at hmem
  have hcast : ((genSeqAvoid q m k : ℕ) : ZMod q)
      = ((prescribed q Y k (typeData q Y k m) : ℕ) : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hcls
  rw [visitedSetAvoid_succ_of_exposed hexp]
  have hval : ((seedCofactorAvoid q m (k + 1) : ℕ) : ZMod q)
      = ((seedCofactorAvoid q m k : ℕ) : ZMod q)
        * ((prescribed q Y k (typeData q Y k m) : ℕ) : ZMod q) := by
    rw [seedCofactorAvoid_succ, Nat.cast_mul, hcast]
  rw [hval]
  exact hmem.2.2

/-- **Successes are rare on every path.**  At most `2q` of the first `n` depths are
successes — a purely deterministic fact, with no probability involved. -/
theorem success_count_le {q Y Cc z k₀ n m : ℕ} (hq : q.Prime) (hCc : 48 * q ≤ Cc)
    (hk₀ : 1 ≤ k₀) (hm : m ∈ sampleSpace q Y) (hnd : ∀ j < n + 1, 2 ≤ genSeqAvoid q m j) :
    ((Finset.range n).filter (fun k => successC q Y Cc z k₀ k m)).card ≤ 2 * q := by
  have hm1 : 1 ≤ m := (mem_sampleSpace.mp hm).1
  set S := (Finset.range n).filter (fun k => successC q Y Cc z k₀ k m) with hS
  set S₁ := S.filter (fun k => q < genSeqAvoid q m (k + 1)) with hS₁
  set S₂ := S.filter (fun k => ¬ q < genSeqAvoid q m (k + 1)) with hS₂
  have hsplit : S ⊆ S₁ ∪ S₂ := by
    intro k hk
    by_cases hp : q < genSeqAvoid q m (k + 1)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hp⟩)
  -- (a) successes followed by an exposed step give strict growth of the visited set
  have hS₁card : S₁.card ≤ q - 1 := by
    set G := (Finset.range (n + 1)).filter
      (fun j => (visitedSetAvoid q m j).card < (visitedSetAvoid q m (j + 1)).card) with hG
    have hGcard : G.card ≤ q - 1 := by
      have hmono : ∀ j, (visitedSetAvoid q m j).card ≤ (visitedSetAvoid q m (j + 1)).card :=
        fun j => Finset.card_le_card (visitedSetAvoid_mono (Nat.le_succ j))
      have hcs : G.card + (visitedSetAvoid q m 0).card
          ≤ (visitedSetAvoid q m (n + 1)).card :=
        count_strict_increase (fun j => (visitedSetAvoid q m j).card) hmono (n + 1)
      have hz : (visitedSetAvoid q m 0).card = 0 := by simp [visitedSetAvoid]
      have hle : (visitedSetAvoid q m (n + 1)).card ≤ q - 1 :=
        visitedSetAvoid_card_le_pred hq hm1 (fun j hj => hnd j hj)
      omega
    refine le_trans (Finset.card_le_card_of_injOn (fun k => k + 1) ?_ ?_) hGcard
    · intro k hk
      simp only [hS₁, hS, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨⟨hkn, hsucc⟩, hexp1⟩ := hk
      have hnot : ((seedCofactorAvoid q m (k + 1) : ℕ) : ZMod q)
          ∉ visitedSetAvoid q m (k + 1) :=
        cofactor_notMem_of_success hq hCc hk₀ hm (fun j hj => hnd j (by omega)) hsucc
      simp only [hG, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [visitedSetAvoid_succ_of_exposed hexp1, Finset.card_insert_of_notMem hnot]
      omega
    · intro a _ b _ hab
      exact Nat.succ_injective hab
  -- (b) successes followed by an unexposed step inject into the unexposed steps
  have hS₂card : S₂.card ≤ q - 1 := by
    have hcard : S₂.card ≤ (Finset.Icc 2 q).card := by
      refine Finset.card_le_card_of_injOn (fun k => genSeqAvoid q m (k + 1)) ?_ ?_
      · intro k hk
        simp only [hS₂, hS, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
        simp only [Finset.mem_coe, Finset.mem_Icc]
        exact ⟨hnd (k + 1) (by omega), by omega⟩
      · intro a ha b hb hab
        simp only [hS₂, hS, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
        have := genSeqAvoid_inj hq hm1 hnd (i := a + 1) (j := b + 1)
          (by omega) (by omega) hab
        omega
    rw [Nat.card_Icc] at hcard
    have := hq.two_le
    omega
  have := Finset.card_le_card hsplit
  have hunion := Finset.card_union_le S₁ S₂
  have hq2 := hq.two_le
  omega

/-! ## 9. The guard holds at exposed steps of uncaptured good seeds -/

/-- **The capture readoff.**  If the visited set at depth `n` contains every nonzero residue,
then the genuine orbit of the seed selects `q` before depth `n`. -/
theorem captured_of_visited_full {q Y n m : ℕ} (hq : q.Prime) (hm : 1 ≤ m) (hqm : ¬ q ∣ m)
    (hy : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)
    (hfull : ∀ x : ZMod q, x ≠ 0 → x ∈ visitedSetAvoid q m n) :
    ∃ j < n, genSeq m j = q := by
  have : Fact q.Prime := ⟨hq⟩
  have hmne : ((m : ℕ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqm
  set v : ZMod q := -((m : ℕ) : ZMod q)⁻¹ with hv
  have hvne : v ≠ 0 := by
    rw [hv, neg_ne_zero]
    exact inv_ne_zero hmne
  have hvval : ((m : ℕ) : ZMod q) = -v⁻¹ := by
    rw [hv, inv_neg, inv_inv, neg_neg]
  exact captured_of_mem_visited hq hm hm hqm
    (fun r hr hrY hrq => dvd_modulus hr hrY hrq) (Nat.ModEq.refl m) hy
    ⟨v, hfull v hvne, hvval⟩

/-- **The guard holds at every exposed step of an uncaptured good seed.**  A guard failure at
an exposed step would fill the visited set with all nonzero residues, hence force capture. -/
theorem guard_of_exposed {q Y Cc k₀ n m k : ℕ} (hq : q.Prime) (hm : m ∈ sampleSpace q Y)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)
    (hnc : ¬ ∃ j < n, genSeq m j = q) (hqm : ¬ q ∣ m)
    (hdiv : ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m), (1 : ℝ) / r
      ≤ 1 / Cc)
    (hthr : ∀ k < n, (bigThreshold q m Cc k) ^ 2 ≤ Y)
    (hk1 : 1 ≤ k) (hCck : Cc ≤ k) (hk₀ : k₀ ≤ k) (hkn : k < n)
    (hexp : q < genSeqAvoid q m k) :
    guardC q Y Cc (Cc ^ 2) k₀ k (typeData q Y k m) := by
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
  exact hnc (captured_of_visited_full hq hm1 hqm hnd
    (fun x hx => visitedSetAvoid_mono (by omega) (hfull x hx)))

/-! ## 10. The compensator lower bound -/

/-- **Good seeds.**  Coprime to `q`, uncaptured before depth `n`, with a nondegenerate
`Y`-bounded prefix and a small divisor mass in the exclusion window `(Cc², Y]`. -/
def GoodSeed (q Y Cc n m : ℕ) : Prop :=
  ¬ q ∣ m ∧ (¬ ∃ j < n, genSeq m j = q) ∧
    (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y) ∧
    (∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m), (1 : ℝ) / r ≤ 1 / Cc)

instance decidableGoodSeed (q Y Cc n m : ℕ) : Decidable (GoodSeed q Y Cc n m) :=
  Classical.propDecidable _

/-- **The compensator of an uncaptured good seed is large.**  The guard can only fail before
depth `k₀` or at a `q`-unexposed step, and there are at most `q - 1` of the latter; on the
remaining depths the predicted probability is `κ` times the pathwise step survival, whose sum
is bounded below by the deterministic core (`pathwise_compensator`). -/
theorem compensator_lower {κ : ℝ} {q Y Cc k₀ n m : ℕ} (hq : q.Prime) (hκ : 0 ≤ κ)
    (hCc : 1 ≤ Cc)
    (hcore : c₁ / 2 * (n : ℝ) ≤ ∑ k ∈ Finset.range n, stepSurvival q m Cc k)
    (hm : m ∈ sampleSpace q Y) (hgood : GoodSeed q Y Cc n m)
    (hthr : ∀ k < n, (bigThreshold q m Cc k) ^ 2 ≤ Y) (hCck₀ : Cc ≤ k₀) :
    κ * (c₁ / 2 * (n : ℝ) - ((k₀ + q : ℕ) : ℝ))
      ≤ TreeChernoff.compensator (typeData q Y) (predC κ q Y Cc (Cc ^ 2) k₀) n m := by
  obtain ⟨hqm, hnc, hnd, hdiv⟩ := hgood
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
      exact hk.2 (guard_of_exposed hq hm hndn hnc hqm hdiv hthr
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

/-! ## 11. Theorem C -/

/-- **Theorem C.**  For every prime `q` and every constant `Cc ≥ 48 q` there are constants
`κ > 0`, `K₀`, `n₁` such that, on one full period of the `q`-free dynamics and for every
`n ≥ n₁` obeying the policy `Cc ≤ n`, `log Y ≤ n²` (and the localization hypothesis that the
moving thresholds of good seeds stay inside the band), the **good uncaptured seeds** — those
coprime to `q`, with a nondegenerate `Y`-bounded prefix and a small divisor mass in
`(Cc², Y]`, whose genuine orbit does *not* select `q` before depth `n` — form a fraction at
most `exp(-(3/8)·κ·(c₁ n/2 - K₀))` of the period.

The proof is the composition of

* `hcondC` — Lemma D (box side) in the shape of the conditional counting inequality;
* `success_count_le` — the deterministic bound `#successes ≤ 2q` on **every** path;
* `compensator_lower` — the compensator lower bound on uncaptured good seeds, whose only
  input beyond the deterministic core is the capture identity of `EM/Population/SeedCapture`;
* `TreeChernoff.chernoff_quarter_local` — the localized exponential supermartingale.

`agents/state/findings.md` §"Session 311 — coordinator design"; Session 311, WP-C. -/
theorem theorem_C (q Cc : ℕ) (hq : q.Prime) (hCc : 48 * q ≤ Cc) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ K₀ n₁ : ℕ, ∀ Y n : ℕ,
      n₁ ≤ n → (Cc : ℝ) ≤ (n : ℝ) → Real.log Y ≤ (n : ℝ) ^ 2 →
      (∀ m ∈ sampleSpace q Y, GoodSeed q Y Cc n m →
        ∀ k < n, (bigThreshold q m Cc k) ^ 2 ≤ Y) →
      (((sampleSpace q Y).filter (fun m => GoodSeed q Y Cc n m)).card : ℝ)
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
  -- every good uncaptured seed is Chernoff-bad
  intro m hm
  rw [Finset.mem_filter] at hm
  obtain ⟨hmΩ, hgood⟩ := hm
  have hm1 : 1 ≤ m := (mem_sampleSpace.mp hmΩ).1
  obtain ⟨hqm, hnc, hnd, hdiv⟩ := hgood
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
    have := compensator_lower (κ := κ') hq hκ'0 hCc1 hcore hmΩ
      ⟨hqm, hnc, hnd, hdiv⟩
      (fun k hk => hthr m hmΩ ⟨hqm, hnc, hnd, hdiv⟩ k hk)
      (le_trans (le_max_right (max 1 k₀) Cc) le_rfl)
    rw [hv, hK₀]
    exact this

end TheoremC

end
