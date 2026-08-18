import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# Periodic sets have small density (Mathlib-only)

A completely generic block-counting lemma: if a predicate `P` on the positive naturals can only
hold on finitely many residue classes modulo a period `M`, then the number of `m ∈ [1, X]` with
`P m` is at most `(X / M + 1)` times the number of admissible classes.  Consequently, if the
admissible classes are a small fraction of all classes, then `{m : P m}` has small upper density.

The bookkeeping is done through `PeriodicDensity.periodRep M m`, the representative of `m` mod `M`
taken in `[1, M]` rather than `[0, M)`; this is the convention that matches "the type of `m`" in
sieve-style arguments, where index `0` is unnatural.

Main statements:

* `PeriodicDensity.card_fiber_le`   — a single residue class meets `[1, X]` at most `X/M + 1` times;
* `PeriodicDensity.card_filter_le_of_type_bad` — the block bound `#≤ (X/M + 1) · #T`;
* `PeriodicDensity.eventually_density_le` — the density form, with `M` eliminated from the
  conclusion;
* `PeriodicDensity.limsup_density_le` — the `limsup` restatement.

Nothing here is specific to any particular sequence: it is pure counting.
-/

open Finset

namespace PeriodicDensity

/-! ## Part 1: the representative in `[1, M]` -/

/-- The representative of `m` modulo `M` chosen in the range `[1, M]` (rather than `[0, M)`). -/
def periodRep (M m : ℕ) : ℕ := if m % M = 0 then M else m % M

theorem periodRep_mem_Ico {M m : ℕ} (hM : 1 ≤ M) :
    periodRep M m ∈ Finset.Ico 1 (M + 1) := by
  rw [Finset.mem_Ico]
  unfold periodRep
  split_ifs with h
  · omega
  · have := Nat.mod_lt m (show 0 < M by omega)
    omega

theorem periodRep_pos {M m : ℕ} (hM : 1 ≤ M) : 1 ≤ periodRep M m := by
  have := periodRep_mem_Ico (M := M) (m := m) hM
  rw [Finset.mem_Ico] at this
  exact this.1

theorem periodRep_le {M m : ℕ} (hM : 1 ≤ M) : periodRep M m ≤ M := by
  have := periodRep_mem_Ico (M := M) (m := m) hM
  rw [Finset.mem_Ico] at this
  omega

theorem periodRep_modEq (M m : ℕ) : m ≡ periodRep M m [MOD M] := by
  show m % M = periodRep M m % M
  unfold periodRep
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact (Nat.mod_mod_of_dvd m dvd_rfl).symm

theorem periodRep_eq_self {M m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ M) : periodRep M m = m := by
  rcases eq_or_lt_of_le h2 with h | h
  · subst h
    simp [periodRep, Nat.mod_self]
  · unfold periodRep
    rw [Nat.mod_eq_of_lt h, if_neg (by omega)]

/-! ## Part 2: the fiber bound -/

set_option linter.unusedVariables false in
/-- A single residue class modulo `M` meets `[1, X]` at most `X / M + 1` times.

(The hypothesis `1 ≤ M` is kept for uniformity with the rest of the file; the counting argument
happens to survive `M = 0`, where the bound degenerates to `1`.) -/
theorem card_fiber_le {M : ℕ} (hM : 1 ≤ M) (t X : ℕ) :
    (((Finset.Icc 1 X).filter (fun m => periodRep M m = t)).card : ℝ) ≤ (X : ℝ) / M + 1 := by
  have hcard : ((Finset.Icc 1 X).filter (fun m => periodRep M m = t)).card ≤ X / M + 1 := by
    have hle : ((Finset.Icc 1 X).filter (fun m => periodRep M m = t)).card
        ≤ (Finset.range (X / M + 1)).card := by
      refine Finset.card_le_card_of_injOn (fun m => m / M) ?_ ?_
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm
        have : m / M ≤ X / M := Nat.div_le_div_right hm.1.2
        simp only [Finset.mem_coe, Finset.mem_range]
        omega
      · intro m hm m' hm' h
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm hm'
        have e1 : m % M = periodRep M m % M := periodRep_modEq M m
        have e2 : m' % M = periodRep M m' % M := periodRep_modEq M m'
        have hmod : m % M = m' % M := by rw [e1, e2, hm.2, hm'.2]
        have hq : m / M = m' / M := h
        calc m = M * (m / M) + m % M := (Nat.div_add_mod m M).symm
          _ = M * (m' / M) + m' % M := by rw [hq, hmod]
          _ = m' := Nat.div_add_mod m' M
    simpa using hle
  calc (((Finset.Icc 1 X).filter (fun m => periodRep M m = t)).card : ℝ)
      ≤ ((X / M + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = ((X / M : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (X : ℝ) / M + 1 := by
        have := Nat.cast_div_le (α := ℝ) (m := X) (n := M)
        linarith

/-! ## Part 3: the block bound -/

/-- If `P` forces the representative of `m` modulo `M` to lie in a finite set `T` of classes,
then `P` holds at most `(X/M + 1) · #T` times in `[1, X]`. -/
theorem card_filter_le_of_type_bad {M : ℕ} (hM : 1 ≤ M)
    (T : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ m, 1 ≤ m → P m → periodRep M m ∈ T) (X : ℕ) :
    (((Finset.Icc 1 X).filter P).card : ℝ) ≤ ((X : ℝ) / M + 1) * (T.card : ℝ) := by
  have hsub : (Finset.Icc 1 X).filter P ⊆
      T.biUnion (fun t => (Finset.Icc 1 X).filter (fun m => periodRep M m = t)) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    exact Finset.mem_biUnion.mpr ⟨periodRep M m, hP m hm.1.1 hm.2,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hm.1, rfl⟩⟩
  have h1 : ((Finset.Icc 1 X).filter P).card
      ≤ ∑ t ∈ T, ((Finset.Icc 1 X).filter (fun m => periodRep M m = t)).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
  calc (((Finset.Icc 1 X).filter P).card : ℝ)
      ≤ ((∑ t ∈ T, ((Finset.Icc 1 X).filter (fun m => periodRep M m = t)).card : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = ∑ t ∈ T, ((((Finset.Icc 1 X).filter (fun m => periodRep M m = t)).card : ℝ)) := by
        push_cast; ring
    _ ≤ ∑ _t ∈ T, ((X : ℝ) / M + 1) :=
        Finset.sum_le_sum (fun t _ => card_fiber_le hM t X)
    _ = ((X : ℝ) / M + 1) * (T.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ## Part 4: the density form -/

/-- If the admissible classes are at most an `ε/2` fraction of all `M` classes, then eventually
`#{m ≤ X : P m} ≤ ε · X`.  The period `M` has disappeared from the conclusion. -/
theorem eventually_density_le {M : ℕ} (hM : 1 ≤ M) (T : Finset ℕ) (P : ℕ → Prop)
    [DecidablePred P] (hP : ∀ m, 1 ≤ m → P m → periodRep M m ∈ T)
    {ε : ℝ} (hε : 0 < ε) (hT : (T.card : ℝ) ≤ ε / 2 * (M : ℝ)) :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, (((Finset.Icc 1 X).filter P).card : ℝ) ≤ ε * (X : ℝ) := by
  refine ⟨M, fun X hX => ?_⟩
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hXM : (M : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hfac : (0 : ℝ) ≤ (X : ℝ) / M + 1 := by positivity
  have h1 := card_filter_le_of_type_bad hM T P hP X
  have h2 : ((X : ℝ) / M + 1) * (T.card : ℝ) ≤ ((X : ℝ) / M + 1) * (ε / 2 * (M : ℝ)) :=
    mul_le_mul_of_nonneg_left hT hfac
  have h3 : ((X : ℝ) / M + 1) * (ε / 2 * (M : ℝ)) = ε / 2 * (X : ℝ) + ε / 2 * (M : ℝ) := by
    field_simp
  have h4 : ε / 2 * (M : ℝ) ≤ ε / 2 * (X : ℝ) :=
    mul_le_mul_of_nonneg_left hXM (by linarith)
  linarith

/-- `limsup` restatement of `eventually_density_le`. -/
theorem limsup_density_le {M : ℕ} (hM : 1 ≤ M) (T : Finset ℕ) (P : ℕ → Prop)
    [DecidablePred P] (hP : ∀ m, 1 ≤ m → P m → periodRep M m ∈ T)
    {ε : ℝ} (hε : 0 < ε) (hT : (T.card : ℝ) ≤ ε / 2 * (M : ℝ)) :
    Filter.limsup (fun X : ℕ => (((Finset.Icc 1 X).filter P).card : ℝ) / (X : ℝ))
      Filter.atTop ≤ ε := by
  obtain ⟨X₀, hX₀⟩ := eventually_density_le hM T P hP hε hT
  refine Filter.limsup_le_of_le ?_ ?_
  · refine ⟨0, fun a ha => ?_⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ha
    have h1 : (0 : ℝ) ≤ ((((Finset.Icc 1 (N + 1)).filter P).card : ℝ) / ((N + 1 : ℕ) : ℝ)) := by
      positivity
    exact le_trans h1 (hN (N + 1) (Nat.le_succ N))
  · filter_upwards [Filter.eventually_ge_atTop (max X₀ 1)] with X hX
    have hX1 : (0 : ℝ) < (X : ℝ) := by
      have : 1 ≤ X := le_trans (le_max_right X₀ 1) hX
      exact_mod_cast this
    rw [div_le_iff₀ hX1]
    exact hX₀ X (le_trans (le_max_left X₀ 1) hX)

end PeriodicDensity
