import EM.CME.Reduction
import EM.LargeSieve.WalkDecomposition

/-!
# Walk Analysis: Energy Increment Dynamics

Content extracted from the flat LargeSieveSpectral.lean (now EM/LargeSieve/Spectral.lean) for modularity.

## Sections

* **EnergyIncrementDynamics** (§75): energy increment identity, self-correcting criterion

Moved elsewhere:

* §S71 (EH conjecture, EH → BV → MC chain) now lives in `EM.LargeSieve.Basic`.
* §84-§86 (VCB, CME fiber decomposition, transition matrix) now live in
  `EM.CME.FiberAnalysis`.
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## §75. Energy Increment Dynamics

The energy increment `Delta E` when the walk takes one step to position `a` equals
`2(p-1) V_N(a) - 2N + (p-2)`, where `V_N(a)` is the visit count.

This identity connects the excess energy (a spectral quantity equal to
`sum_{chi != 1} |S_chi|^2`) to the walk's single-step visit pattern.

**Key insight**: energy increases when the walk visits an above-average position
(`V_N(a) > N/(p-1)`) and decreases when visiting a below-average position.
SubquadraticVisitEnergy (SVE) is equivalent to the walk "typically" visiting
below-average positions.

**Self-correcting criterion**: SVE holds iff the average energy increment per
step converges to (p-2), which happens iff V_N(w(N)) is approximately N/(p-1) on average.
This reformulates SVE as a single-step visit-count condition. -/

section EnergyIncrementDynamics

open Finset DirichletCharacter
open Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP75 : NeZero p := ⟨hp.out.ne_zero⟩

/-- **Nontrivial character orthogonality for walk sums**:
    `sum_{chi != 1} conj(chi(a)) * S_chi(N) = (p-1) * V_N(a) - N`.

    This is the key identity connecting nontrivial character sums to visit counts.
    It follows from full character orthogonality by separating the trivial character. -/
theorem nontrivial_char_walk_sum {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (hp1 : (1 : ℝ) < p) :
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p)) =
    ((p : ℂ) - 1) * (walkVisitCount w a : ℂ) - (N : ℂ) := by
  have hp1c : (p : ℂ) - 1 ≠ 0 := by
    exact_mod_cast ne_of_gt (by linarith : (0 : ℝ) < (p : ℝ) - 1)
  -- Full sum: ∑_χ χ(a⁻¹) · S_χ = (p-1) · V_N(a)
  have hfull : ∑ χ : DirichletCharacter ℂ p, χ (↑a⁻¹ : ZMod p) *
      ∑ n : Fin N, χ (↑(w n) : ZMod p) =
    ((p : ℂ) - 1) * (walkVisitCount w a : ℂ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [char_indicator_expansion a]
    rw [← Finset.sum_filter]
    simp only [walkVisitCount, Finset.sum_const, nsmul_eq_mul]
    ring
  -- Split: full = trivial + nontrivial
  have hsplit : ∑ χ : DirichletCharacter ℂ p, χ (↑a⁻¹ : ZMod p) *
      ∑ n : Fin N, χ (↑(w n) : ZMod p) =
    (1 : DirichletCharacter ℂ p) (↑a⁻¹ : ZMod p) *
      (∑ n : Fin N, (1 : DirichletCharacter ℂ p) (↑(w n) : ZMod p)) +
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ _)]
  -- Trivial part: 1(a⁻¹) · ∑ 1(w(n)) = N
  have h_triv : (1 : DirichletCharacter ℂ p) (↑a⁻¹ : ZMod p) *
      (∑ n : Fin N, (1 : DirichletCharacter ℂ p) (↑(w n) : ZMod p)) = (N : ℂ) := by
    simp only [MulChar.one_apply_coe, one_mul, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- Combine: nontrivial = full - trivial = (p-1)*V - N
  -- hsplit: full = triv + nontrivial, hfull: full = (p-1)*V, h_triv: triv = N
  -- => nontrivial = (p-1)*V - N
  rw [hfull, h_triv] at hsplit
  -- hsplit : (p-1) * V = N + nontrivial_sum => nontrivial = (p-1)*V - N
  have hsplit' := hsplit  -- (p-1)*V = N + nontrivial
  -- Goal: nontrivial = (p-1)*V - N
  -- From hsplit': nontrivial = (p-1)*V - N
  exact eq_sub_of_add_eq' hsplit'.symm

/-- **Energy increment identity (character-sum form)**:
    The total "energy change" from adding one step at position `a` is
    `2(p-1) V_N(a) - 2N + (p-2)`.

    Formally, `sum_{chi != 1} (2 Re(S_chi * conj(chi(a))) + 1) = 2(p-1) V_N(a) - 2N + (p-2)`.

    This identity follows from `nontrivial_char_walk_sum` (which gives the sum of
    `conj(chi(a)) * S_chi` over nontrivial characters) plus the count of nontrivial
    characters (which is `p-2`). -/
theorem energy_increment_identity {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (hp1 : (1 : ℝ) < p) :
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => 2 * ((χ (↑a⁻¹ : ZMod p) *
        ∑ n : Fin N, χ (↑(w n) : ZMod p)).re) + 1) =
    2 * ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) - 2 * (N : ℝ) + ((p : ℝ) - 2) := by
  -- Step 1: Split sum of (f + 1) into (sum f) + card * 1
  have hsplit_sum : (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => 2 * ((χ (↑a⁻¹ : ZMod p) *
        ∑ n : Fin N, χ (↑(w n) : ZMod p)).re) + 1) =
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => 2 * ((χ (↑a⁻¹ : ZMod p) *
        ∑ n : Fin N, χ (↑(w n) : ZMod p)).re)) +
    ((Finset.univ.erase (1 : DirichletCharacter ℂ p)).card : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsplit_sum]
  -- Step 2: Compute ∑_χ (χ(a⁻¹) * S_χ).re via Complex.re_sum + nontrivial_char_walk_sum
  have hre_key : (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => (χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p)).re) =
    ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) - (N : ℝ) := by
    rw [← Complex.re_sum, nontrivial_char_walk_sum w a hp1]
    simp only [Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.one_re, mul_zero, sub_zero]
  -- Step 3: Factor 2 out: ∑ (2 * f) = 2 * ∑ f
  have hfactor : (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => 2 * ((χ (↑a⁻¹ : ZMod p) *
        ∑ n : Fin N, χ (↑(w n) : ZMod p)).re)) =
    2 * ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) - 2 * (N : ℝ) := by
    rw [← Finset.mul_sum, hre_key]; ring
  rw [hfactor]
  -- Step 4: Count of nontrivial characters = p - 2
  have hcard_real : ((Finset.univ.erase (1 : DirichletCharacter ℂ p)).card : ℝ) =
      (p : ℝ) - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p,
      Nat.totient_prime hp.out]
    have h2le : 2 ≤ p := hp.out.two_le
    push_cast [Nat.sub_sub, Nat.cast_sub h2le]; ring
  rw [hcard_real]

/-- **Energy decreases for below-average positions**: if `V_N(a) < N/(p-1)` then the
    energy increment is strictly less than `p - 2` (the "neutral" increment value).

    This means visiting an underrepresented position results in slower-than-average
    energy growth. SVE is equivalent to the walk typically visiting such positions. -/
theorem energy_below_average_decreases {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (hp1 : (1 : ℝ) < p)
    (hbelow : (walkVisitCount w a : ℝ) < (N : ℝ) / ((p : ℝ) - 1)) :
    2 * ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) - 2 * (N : ℝ) + ((p : ℝ) - 2) <
    (p : ℝ) - 2 := by
  have hp1r : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  -- V < N/(p-1) implies (p-1)*V < N
  have h1 : ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) < (N : ℝ) := by
    have := (lt_div_iff₀ hp1r).mp hbelow
    linarith [mul_comm (walkVisitCount w a : ℝ) ((p : ℝ) - 1)]
  nlinarith

/-- **Energy increases for above-average positions**: if `V_N(a) > N/(p-1)` then the
    energy increment is strictly greater than `p - 2`. -/
theorem energy_above_average_increases {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (hp1 : (1 : ℝ) < p)
    (habove : (N : ℝ) / ((p : ℝ) - 1) < (walkVisitCount w a : ℝ)) :
    (p : ℝ) - 2 <
    2 * ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) - 2 * (N : ℝ) + ((p : ℝ) - 2) := by
  have hp1r : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  -- N/(p-1) < V implies N < (p-1)*V
  have h1 : (N : ℝ) < ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) := by
    have := (div_lt_iff₀ hp1r).mp habove
    linarith [mul_comm (walkVisitCount w a : ℝ) ((p : ℝ) - 1)]
  nlinarith

/-- **Average energy increment equals `p - 2`**: the expected energy increment,
    averaged uniformly over all positions `a`, equals `p - 2`.

    Proof: the average of `2(p-1) V_N(a) - 2N + (p-2)` over all `a` in `(ZMod p)ˣ`
    equals `(1/(p-1)) * (2(p-1) * sum_a V(a) - 2N(p-1) + (p-2)(p-1))`
    = `(1/(p-1)) * (2(p-1)N - 2N(p-1) + (p-2)(p-1))` = `p - 2`. -/
theorem average_energy_increment {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (hp1 : (1 : ℝ) < p) :
    (1 / ((p : ℝ) - 1)) *
      ∑ a : (ZMod p)ˣ, (2 * ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) -
        2 * (N : ℝ) + ((p : ℝ) - 2)) = (p : ℝ) - 2 := by
  have hp1r : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp1ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1r
  -- Compute the full sum directly
  -- ∑_a (2(p-1)V(a) - 2N + (p-2))
  -- = 2(p-1) * ∑V(a) - (p-1)*2N + (p-1)*(p-2)
  -- = 2(p-1)*N - 2N(p-1) + (p-1)(p-2)
  -- = (p-1)(p-2)
  -- Card of units = p - 1
  have hcard : (Finset.univ : Finset (ZMod p)ˣ).card = p - 1 := by
    rw [Finset.card_univ, ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  -- ∑_a V(a) = N
  have hv_sum : ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) = (N : ℝ) := by
    have h := walkVisitCount_sum w
    exact_mod_cast h
  -- Compute the sum by distributing
  have hfull : ∑ a : (ZMod p)ˣ, (2 * ((p : ℝ) - 1) * (walkVisitCount w a : ℝ) -
      2 * (N : ℝ) + ((p : ℝ) - 2)) =
    ((p : ℝ) - 1) * ((p : ℝ) - 2) := by
    simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hv_sum,
      Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast [Nat.cast_sub hp.out.one_le]
    ring
  rw [hfull]
  field_simp

end EnergyIncrementDynamics

