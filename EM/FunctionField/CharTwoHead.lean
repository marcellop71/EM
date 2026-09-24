import EM.FunctionField.CharTwo
import EM.FunctionField.Bootstrap

/-!
# Over `𝔽_2[t]` the cubics are the head, and capture is a bare hit

2026-09-24.  Companion to `docs/analysis/euclid_systems_theory_2026-09-23.md` §10.

The monic irreducibles of degree `≤ 2` over `𝔽_2` are `X`, `X + 1`, `X² + X + 1`
(`monic_irreducible_natDegree_le_two`), and every `FFEMData 2` collects exactly these in its
first three terms (`CharTwo.ff_two_first_terms`).  Hence `FFMCBelow d 3` holds for every
sequence (`ffMCBelow_three`), and for `n ≥ 2` a cubic dividing the Euclid polynomial
`ffProd n + 1` forces the next multiplier to be a cubic (`cubic_capture`): at the head, capture
needs no sieve condition — it is the hit `P_n ≡ 1 (mod Q)` itself.
-/

noncomputable section
open Polynomial Classical

namespace FunctionFieldAnalog

namespace CharTwoHead

/-- Every element of `ZMod 2` is `0` or `1`. -/
theorem zmod_two_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

/-- A monic polynomial of `natDegree 2` is `X² + C a X + C b`. -/
theorem monic_natDegree_two_eq {R : Type*} [CommRing R] [Nontrivial R] {Q : R[X]}
    (hm : Q.Monic) (h2 : Q.natDegree = 2) :
    Q = X ^ 2 + C (Q.coeff 1) * X + C (Q.coeff 0) := by
  ext n
  simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · have : Q.coeff 2 = 1 := by
      have := Polynomial.Monic.leadingCoeff hm
      rwa [leadingCoeff, h2] at this
    simp [this]
  · have : Q.coeff (n + 3) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [this]

/-- **Classification.**  The monic irreducibles of degree `≤ 2` over `𝔽_2` are `X`, `X + 1`
and `X² + X + 1`. -/
theorem monic_irreducible_natDegree_le_two {Q : (ZMod 2)[X]} (hm : Q.Monic) (hi : Irreducible Q)
    (hd : Q.natDegree ≤ 2) :
    Q = X ∨ Q = X + 1 ∨ Q = X ^ 2 + X + 1 := by
  have hpos : 0 < Q.natDegree := by
    rcases Nat.eq_zero_or_pos Q.natDegree with h0 | h0
    · exfalso
      have : Q = 1 := (Polynomial.Monic.natDegree_eq_zero hm).mp h0
      exact hi.not_isUnit (this ▸ isUnit_one)
    · exact h0
  rcases (show Q.natDegree = 1 ∨ Q.natDegree = 2 by omega) with h1 | h2
  · -- linear: `X + C c`
    have := Polynomial.Monic.eq_X_add_C hm h1
    rcases zmod_two_cases (Q.coeff 0) with hc | hc
    · left; rw [this, hc, C_0, add_zero]
    · right; left; rw [this, hc, C_1]
  · -- quadratic: no roots, so constant term `1` and middle coefficient `1`
    right; right
    have hQ := monic_natDegree_two_eq hm h2
    -- no linear factor
    have hnolin : ∀ c : ZMod 2, ¬ (X - C c ∣ Q) := by
      intro c hdvd
      obtain ⟨r, hr⟩ := hdvd
      rcases hi.isUnit_or_isUnit hr with hu | hu
      · have := natDegree_eq_zero_of_isUnit hu
        rw [natDegree_X_sub_C] at this
        exact one_ne_zero this
      · have hdeg := natDegree_eq_zero_of_isUnit hu
        have : Q.natDegree = 1 := by
          rw [hr, natDegree_mul (X_sub_C_ne_zero c) (fun h => by simp [h] at hu),
            natDegree_X_sub_C, hdeg]
        omega
    have h0 : Q.coeff 0 = 1 := by
      rcases zmod_two_cases (Q.coeff 0) with hc | hc
      · exfalso
        apply hnolin 0
        rw [C_0, sub_zero, X_dvd_iff]; exact hc
      · exact hc
    have h1 : Q.coeff 1 = 1 := by
      rcases zmod_two_cases (Q.coeff 1) with hc | hc
      · exfalso
        apply hnolin 1
        rw [dvd_iff_isRoot, IsRoot, hQ, hc, h0]
        simp
        decide
      · exact hc
    rw [hQ, h0, h1, C_1, one_mul]

/-- **Every `FFEMData 2` has collected everything below degree 3.** -/
theorem ffMCBelow_three (d : FFEMData 2) : FFMCBelow d 3 := by
  intro Q hm hi hd
  obtain ⟨h0, h1, h2, -⟩ := CharTwo.ff_two_first_terms d
  rcases monic_irreducible_natDegree_le_two hm hi (by omega) with rfl | rfl | rfl
  · exact ⟨0, h0⟩
  · exact ⟨1, h1⟩
  · exact ⟨2, h2⟩

/-- Everything below degree 3 has appeared by stage `2`. -/
theorem sieve_three (d : FFEMData 2) {n : ℕ} (hn : 2 ≤ n) :
    ∀ P : (ZMod 2)[X], P.Monic → Irreducible P → P.natDegree < 3 →
      ∃ j, j ≤ n ∧ d.ffSeq j = P := by
  intro P hm hi hd
  obtain ⟨h0, h1, h2, -⟩ := CharTwo.ff_two_first_terms d
  rcases monic_irreducible_natDegree_le_two hm hi (by omega) with rfl | rfl | rfl
  · exact ⟨0, by omega, h0⟩
  · exact ⟨1, by omega, h1⟩
  · exact ⟨2, by omega, h2⟩

/-- **Cubic capture is a bare hit.**  For `n ≥ 2`, if a monic irreducible cubic divides
`ffProd n + 1`, the next multiplier is a cubic. -/
theorem cubic_capture (d : FFEMData 2) {n : ℕ} (hn : 2 ≤ n) {Q : (ZMod 2)[X]}
    (hm : Q.Monic) (hi : Irreducible Q) (h3 : Q.natDegree = 3) (hdvd : Q ∣ d.ffProd n + 1) :
    (d.ffSeq (n + 1)).natDegree = 3 := by
  rw [← h3]
  exact ff_captures_degree d Q hm hi hdvd (fun P hPm hPi hPd => sieve_three d hn P hPm hPi (by omega))

end CharTwoHead

end FunctionFieldAnalog

end
