import EM.Population.Confinement
import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# Confined stages in `ℤ[√−3]`: the tower and the shifted tower as factorizations

2026-09-24.  Companion to `docs/analysis/euclid_systems_theory_2026-09-23.md` §13.

On a confined stage `4c_n = 3s_n² + 1`, and the norm identity `E_{n+1} = c_n p² − p + 1` becomes

    4 E_{n+1} = (p − 2)² + 3 (s p)² = N( (p − 2) + s p √−3 )        (`four_euclid_succ_eq_norm`)

with `p = p_{n+1}`.  Writing `δ_n = (1 + s_n√−3)/2 ∈ ℤ[ω]` (norm `c_n`), this is
`E_{n+1} = N(p δ_n − 1)`.  The next stage is confined iff `N(p δ_n − 1) = p' N(δ_{n+1})`; a
*polynomial* family of confined pairs is a factorization `p δ − 1 = ε π' δ'^{±}` in the unique
factorization domain `ℤ[ω][p]`, with `N(π') = p'(p)` and `δ'` again of real part `1/2`.  Two
such factorizations are on file, and they differ by the conjugation of the `δ`-factor:

* the **tower**, `s = 1`, `δ = ω` a unit: `2α = (1 + √−3)(2p − 1 + √−3)`
  (`tower_factorization`), i.e. `p ω − 1 = ω (p − ω̄)`, `p' = p² − p + 1 = Φ₃(p − 1)`;
* the **shifted tower**, `s = (4p+5)/3`: `2√−3 · 3α = −3 (2p + 3 − √−3)(4p − 1 + √−3)`
  (`shifted_tower_factorization`), i.e. `p δ − 1 = −π' δ̄'` with `π' = (p+1) + ω̄`,
  `p' = p² + 3p + 3 = Φ₃(p + 1)`, `δ' = (1 + s'√−3)/2`, `s' = (4p − 1)/3`.

The classification of *linear* families (memo §13.3) reduces to the factorization
`36 v m³ + 12 w m² + 3 v w² m + w³ = (3 v m + w)(12 m² + w²)` (`linear_family_cubic`), whose
only real root is `m = −w/(3v)`; integrality then leaves exactly the tower and the shifted
tower.  Nothing here is numerical: these are ring identities and their dynamical reading.
-/

noncomputable section
open Classical Mullin QuadraticStep Confinement

namespace EisensteinFamilies

/-- `4 E_{n+1}` is the norm of `(p − 2) + s p √−3` on a confined stage. -/
theorem four_euclid_succ_eq_norm {n : ℕ} {s : ℤ} (hs : disc n = -3 * s ^ 2) :
    4 * ((prod (n + 1) + 1 : ℕ) : ℤ)
      = Zsqrtd.norm (⟨(Mullin.seq (n + 1) : ℤ) - 2, s * (Mullin.seq (n + 1) : ℤ)⟩ : ℤ√(-3)) := by
  have h := euclid_succ_eq_norm n
  have hc : 4 * (cofactor n : ℤ) = 3 * s ^ 2 + 1 := by unfold disc at hs; linarith
  rw [Zsqrtd.norm_def]
  simp only
  rw [h]
  linear_combination (Mullin.seq (n + 1) : ℤ) ^ 2 * hc

/-- **The tower factorization**: `2((p−2) + p√−3) = (1 + √−3)(2p − 1 + √−3)`. -/
theorem tower_factorization (p : ℤ) :
    (2 : ℤ√(-3)) * ⟨p - 2, p⟩ = ⟨1, 1⟩ * ⟨2 * p - 1, 1⟩ := by
  ext <;> simp <;> ring

/-- **The shifted-tower factorization**:
`2√−3 · ((3p−6) + (4p²+5p)√−3) = −3 (2p + 3 − √−3)(4p − 1 + √−3)`.  Here `(3p−6) + (4p²+5p)√−3`
is `3α` for `α = (p−2) + s p √−3`, `s = (4p+5)/3`. -/
theorem shifted_tower_factorization (p : ℤ) :
    (2 : ℤ√(-3)) * Zsqrtd.sqrtd * ⟨3 * p - 6, 4 * p ^ 2 + 5 * p⟩
      = -3 * (⟨2 * p + 3, -1⟩ * ⟨4 * p - 1, 1⟩) := by
  ext <;> simp <;> ring

/-- The two factors of the shifted tower have norms `4 p'` and `12 c'` with
`p' = p² + 3p + 3` and `c' = (4p² − 2p + 1)/3`. -/
theorem shifted_tower_norms (p : ℤ) :
    Zsqrtd.norm (⟨2 * p + 3, -1⟩ : ℤ√(-3)) = 4 * (p ^ 2 + 3 * p + 3) ∧
    Zsqrtd.norm (⟨4 * p - 1, 1⟩ : ℤ√(-3)) = 4 * (4 * p ^ 2 - 2 * p + 1) := by
  constructor <;> rw [Zsqrtd.norm_def] <;> ring

/-- **The cubic of linear families.**  Matching coefficients in a length-2 family with linear
conductors `s = m p + r`, `s' = m p + v` and monic `p' = p² + α p + β` forces
`36 v m³ + 12 w m² + 3 v w² m + w³ = 0` with `w = 3v² + 1`; this factors, and `12m² + w² > 0`
leaves `m = −w/(3v)`. -/
theorem linear_family_cubic (v m w : ℚ) :
    36 * v * m ^ 3 + 12 * w * m ^ 2 + 3 * v * w ^ 2 * m + w ^ 3
      = (3 * v * m + w) * (12 * m ^ 2 + w ^ 2) := by
  ring

theorem linear_family_root {v m w : ℚ} (hw : w = 3 * v ^ 2 + 1)
    (h : 36 * v * m ^ 3 + 12 * w * m ^ 2 + 3 * v * w ^ 2 * m + w ^ 3 = 0) :
    3 * v * m + w = 0 := by
  rw [linear_family_cubic] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact h1
  · exfalso
    have : 0 < 12 * m ^ 2 + w ^ 2 := by
      have : (0 : ℚ) < w := by rw [hw]; positivity
      positivity
    linarith

end EisensteinFamilies

end
