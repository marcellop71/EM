import EM.IK.Ch7AdditiveLS

/-!
# Chapter 7 (Part 3): Multiplicative Large Sieve (Iwaniec-Kowalski)

§7.5 of Iwaniec-Kowalski: Multiplicative large sieve inequality,
Gauss sum bridge, Parseval chain, ALS ⇒ MLS for prime modulus.

## References
- [IK] H. Iwaniec, E. Kowalski, *Analytic Number Theory*, 2004
-/

noncomputable section

open Classical

namespace IK

open Complex Finset BigOperators

/-!
## §7.5 Multiplicative large sieve inequality

Theorem 7.13 (Bombieri-Davenport): Large sieve for primitive Dirichlet characters.
∑_{q≤Q} (q/φ(q)) ∑*_χ |∑_n a_n χ(n)|² ≤ (Q² + N − 1) ‖a‖².

### Strategy (Gauss sum bridge)

The derivation from the additive large sieve proceeds in three steps:

1. **Gauss inversion**: For primitive χ mod q, write χ(n) = τ(χ̄)⁻¹ ∑_a χ̄(a) e(an/q).
2. **Parseval orthogonality**: Sum |character sum|² over primitive χ, use character
   orthogonality to collapse to a sum of exponential sums at Farey fractions a/q.
3. **ALS application**: The Farey fractions {a/q : 1 ≤ a ≤ q, (a,q)=1, q ≤ Q}
   are Q⁻²-spaced, so the ALS gives the bound (Q² + N − 1) ‖a‖².

For a single prime modulus p, steps 1–2 are formalized below using
`char_parseval_units` and `gaussSum_norm_sq_eq_prime` from LargeSieveAnalytic/Harmonic.
-/

section MultiplicativeLargeSieve

open DirichletCharacter

/-- **Theorem 7.13** (Bombieri-Davenport): Multiplicative large sieve — IK (7.31).
    ∑_{q≤Q} (q/φ(q)) ∑*_{χ mod q} |∑_n a_n χ(n)|² ≤ (Q² + N − 1) ‖a‖².

    This is the full multi-modulus version. It requires:
    - Farey spacing: the fractions a/q with (a,q)=1, q ≤ Q are (1/Q²)-spaced
    - Additive large sieve at Farey fractions
    - Parseval orthogonality summed over conductors with Mobius inversion

    This is stated as an open Prop because the Farey spacing argument and
    the conductor-level Mobius inversion are not yet formalized. -/
def MultiplicativeLargeSieve : Prop :=
  ∀ (N Q : ℕ), 1 ≤ N → 1 ≤ Q →
    ∀ (a : Fin N → ℂ),
      ∑ q ∈ (Finset.range (Q + 1)).filter (0 < ·),
        ((q : ℝ) / (q : ℕ).totient) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun χ => χ.IsPrimitive),
          ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 ≤
        ((Q : ℝ) ^ 2 + ↑N - 1) * l2NormSq a

/-- **Multiplicative large sieve for a single prime modulus** (Parseval form).

    For a prime p and sequence `a : Fin N → ℂ`, the weighted sum of
    nontrivial character sum norms is bounded:

    `(p/(p-1)) · ∑_{χ ≠ 1 mod p} |∑_n a_n χ(↑n)|² ≤ (N - 1 + p) · ‖a‖²`

    Equivalently (without the weight):

    `∑_{χ ≠ 1 mod p} |∑_n a_n χ(↑n)|² ≤ ((p-1)/p) · (N - 1 + p) · ‖a‖²`

    This is strictly sharper than the bound `(p-1) · (N-1+p) · ‖a‖²`
    from `PrimeArithmeticLargeSieve` (which uses Cauchy-Schwarz instead of Parseval).

    **Proved** from the additive large sieve via Gauss sums + Parseval. -/
def MultiplicativeLargeSievePrime : Prop :=
  ∀ (p : ℕ) (_ : Nat.Prime p) (N : ℕ) (_ : 0 < N) (a : Fin N → ℂ),
    ((p : ℝ) / ((p : ℝ) - 1)) *
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 ≤
    ((N : ℝ) - 1 + (p : ℝ)) * l2NormSq a

/-- The strengthened form — IK (7.32):
    ∑_{rs≤Q,(r,s)=1} (s/φ(rs)) ∑*_χ |∑_n a_n χ̄(n) c_r(n)|² ≤ (Q²+N−1) ‖a‖².
    Open: requires Ramanujan sum infrastructure. -/
def MultiplicativeLargeSieveStrengthened : Prop :=
  ∀ (N Q : ℕ), 1 ≤ N → 1 ≤ Q →
    ∀ (_ : Fin N → ℂ),
      -- Strengthened form with Ramanujan sums; precise statement requires
      -- additional infrastructure (Ramanujan sum c_r(n), coprimality conditions)
      True

/-!
### §7.5a Parseval bridge: character sums to exponential sums

The key intermediate step for the MLS. By Gauss inversion and multiplicative
Parseval, the weighted sum of nontrivial character sum norms is bounded by
the sum of exponential sum norms over ZMod p. This is sharper than applying
Cauchy-Schwarz to each character individually.

**Key results** (all proved):
- `nontrivial_char_parseval_le`: ∑_{χ≠1} |∑ g(b)χ(b)|² ≤ (p-1)·∑|g(b)|² (from Parseval)
- `sum_filter_inv_eq`: χ ↦ χ⁻¹ bijection on nontrivial characters
- `als_implies_mls_prime`: ALS → MLSPrime (open Prop, depends on ALS)
-/

section ParsBridge

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP75 : NeZero p := ⟨hp.out.ne_zero⟩

/-- **Nontrivial Parseval bound** (dropping trivial character from full Parseval):
    `∑_{χ ≠ 1} |∑_b g(b) χ(↑b)|² ≤ (p-1) · ∑_b |g(b)|²`.

    This follows from `char_parseval_units` (which gives equality for the sum
    over ALL χ) by observing the trivial character contributes a nonneg term. -/
theorem nontrivial_char_parseval_le (g : (ZMod p)ˣ → ℂ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ a : (ZMod p)ˣ, g a * χ (↑a)‖ ^ 2 ≤
    ((p : ℝ) - 1) * ∑ a : (ZMod p)ˣ, ‖g a‖ ^ 2 := by
  -- Full Parseval: ∑_χ ‖...‖² = (p-1) · ∑_a ‖g(a)‖²
  have hfull := char_parseval_units g
  -- Split: ∑_χ = (χ = 1 term) + (χ ≠ 1 terms)
  have hsplit : ∑ χ : DirichletCharacter ℂ p, ‖∑ a : (ZMod p)ˣ, g a * χ (↑a)‖ ^ 2 =
      ‖∑ a : (ZMod p)ˣ, g a * (1 : DirichletCharacter ℂ p) (↑a)‖ ^ 2 +
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
        ‖∑ a : (ZMod p)ˣ, g a * χ (↑a)‖ ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ p))]
    congr 1
    apply Finset.sum_congr
    · ext χ; simp [Finset.mem_erase, Finset.mem_filter, ne_eq, and_iff_left]
    · intros; rfl
  rw [hsplit] at hfull
  -- The trivial character term is nonneg
  have htriv_nonneg : (0 : ℝ) ≤ ‖∑ a : (ZMod p)ˣ, g a *
      (1 : DirichletCharacter ℂ p) (↑a)‖ ^ 2 := by positivity
  linarith

omit hp in
/-- **Filtered inversion bijection**: summing `f(χ⁻¹)` over nontrivial χ
    equals summing `f(χ)`, using the inversion bijection on the character group. -/
theorem sum_filter_inv_eq {α : Type*} [AddCommMonoid α]
    (f : DirichletCharacter ℂ p → α) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      f χ⁻¹ =
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      f χ := by
  apply Finset.sum_nbij (fun χ => χ⁻¹)
  · intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    exact inv_ne_one.mpr hχ
  · intro χ₁ _ χ₂ _ h
    have : χ₁⁻¹ = χ₂⁻¹ := h
    exact inv_injective this
  · intro χ hχ
    have hχ' : χ ≠ 1 := (Finset.mem_filter.mp hχ).2
    refine ⟨χ⁻¹, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, inv_ne_one.mpr hχ'⟩
    · exact inv_inv χ
  · intros; rfl

end ParsBridge

/-!
### §7.5b ALS implies MLS for prime modulus

The reduction ALS → MLS_prime. The proof uses Gauss sum inversion,
Parseval orthogonality (`nontrivial_char_parseval_le`), and the inversion
bijection (`sum_filter_inv_eq`) to establish the Parseval-optimal bound.

The proof requires connecting the Gauss expansion (which writes character
sums as weighted exponential sums) with the units-to-ZMod-p reindexing.
This connection uses `char_sum_gauss_expansion` (from LargeSieveAnalytic),
`gaussSum_norm_sq_eq_prime`, and the fact that MulChar vanishes on non-units.

This is stated as an open Prop because the complete proof requires
infrastructure for splitting sums over ZMod p into sums over units
that is not yet fully formalized. The Parseval helpers above
(`nontrivial_char_parseval_le`, `sum_filter_inv_eq`) are proved and
constitute the main algebraic content.
-/

section MLSPrimeProof

open DirichletCharacter

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP75b : NeZero p := ⟨hp.out.ne_zero⟩

/-- For any MulChar χ on ZMod p (p prime), the sum `∑_{b : ZMod p} χ(b) * f(b)`
    equals `∑_{b : (ZMod p)ˣ} χ(↑b) * f(↑b)` because χ vanishes on non-units. -/
private theorem mulchar_sum_eq_units_sum
    (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) :
    ∑ b : ZMod p, χ b * f b =
    ∑ b : (ZMod p)ˣ, χ (↑b) * f (↑b) := by
  -- Non-units contribute 0, so restrict to units
  have h0 : ∀ b : ZMod p, ¬IsUnit b → χ b * f b = 0 :=
    fun b hb => by simp [MulChar.map_nonunit χ hb]
  -- Write units sum as a mapped sum
  set g : ZMod p → ℂ := fun b => χ b * f b
  -- ∑ b : (ZMod p)ˣ, g(↑b) = ∑ b ∈ image_of_units, g(b)
  -- ∑ b : ZMod p, g(b) = ∑ b ∈ univ, g(b)
  -- Since g(b) = 0 for non-units, both equal the same thing
  have hRHS : ∑ b : (ZMod p)ˣ, g (↑b) =
      ∑ b ∈ (Finset.univ : Finset (ZMod p)ˣ).map
        ⟨((↑) : (ZMod p)ˣ → ZMod p), Units.val_injective⟩, g b := by
    rw [Finset.sum_map]; rfl
  show ∑ b : ZMod p, g b = ∑ b : (ZMod p)ˣ, g (↑b)
  rw [hRHS]
  -- Now show: ∑_{b ∈ univ} g(b) = ∑_{b ∈ map} g(b)
  -- The map is a subset of univ
  symm
  apply Finset.sum_subset
  · intro x _; exact Finset.mem_univ _
  · intro b _ hb
    apply h0
    intro hbu
    obtain ⟨u, hu⟩ := hbu
    apply hb
    rw [Finset.mem_map]
    refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [Function.Embedding.coeFn_mk]
    exact hu

/-- **Gauss expansion + norm squared bound for nontrivial characters**.
    For nontrivial χ mod p:
    `‖∑_n a_n χ(n)‖² = (1/p) · ‖∑_{b:units} χ⁻¹(↑b) · S(b)‖²`
    where S(b) = ∑_n a_n · eAN(n · val(b)/p). -/
private theorem char_sum_norm_sq_eq_parseval_form
    (N : ℕ) (a : Fin N → ℂ) (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    let S : (ZMod p)ˣ → ℂ := fun b =>
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ))
    ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 =
    (p : ℝ)⁻¹ * ‖∑ b : (ZMod p)ˣ, χ⁻¹ (↑b) * S b‖ ^ 2 := by
  intro S
  set ψ := ZMod.stdAddChar (N := p)
  set τ := gaussSum χ⁻¹ ψ
  have hne : τ ≠ 0 := gaussSum_stdAddChar_ne_zero χ⁻¹ (inv_ne_one.mpr hχ)
  -- Step 1: Apply Gauss expansion
  have hgauss := char_sum_gauss_expansion N a χ hχ
  -- ∑_n a(n)χ(n) = τ⁻¹ · ∑_{b:ZMod p} χ⁻¹(b) · ∑_n a(n)·ψ(b·n)
  -- Step 2: Use bridge to replace ψ(b·n) by eAN(n·val(b)/p)
  have hbridge : ∀ b : ZMod p,
      ∑ n : Fin N, a n * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ) =
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val b : ℝ) / (p : ℝ)) := by
    intro b; congr 1; ext n; congr 1
    exact stdAddChar_mul_intCast_eq_eAN b (↑n : ℤ)
  -- Step 3: Rewrite the gauss expansion using bridge
  have hinner_eq : ∑ b : ZMod p, χ⁻¹ b *
      ∑ n : Fin N, a n * (ψ (b * (↑(↑n : ℤ) : ZMod p)) : ℂ) =
    ∑ b : ZMod p, χ⁻¹ b *
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val b : ℝ) / (p : ℝ)) := by
    congr 1; ext b; congr 1; exact hbridge b
  -- Step 4: Replace sum over ZMod p by sum over units (χ⁻¹(0) = 0)
  have hunits_eq : ∑ b : ZMod p, χ⁻¹ b *
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val b : ℝ) / (p : ℝ)) =
    ∑ b : (ZMod p)ˣ, χ⁻¹ (↑b) * S b :=
    mulchar_sum_eq_units_sum _ χ⁻¹
  -- Combine: ∑_n a(n) χ(n) = τ⁻¹ * ∑_{b:units} χ⁻¹(↑b) S(b)
  have hfull : ∑ n : Fin N, a n * χ (↑(↑n : ℤ)) =
      τ⁻¹ * ∑ b : (ZMod p)ˣ, χ⁻¹ (↑b) * S b := by
    rw [hgauss, hinner_eq, hunits_eq]
  rw [hfull, norm_mul, mul_pow]
  -- ‖τ⁻¹‖² = 1/p
  have hτ_norm : ‖τ‖ ^ 2 = (p : ℝ) :=
    gaussSum_norm_sq_eq_prime χ⁻¹ (inv_ne_one.mpr hχ)
  rw [norm_inv, inv_pow, hτ_norm]

/-- The Gauss expansion for a single nontrivial character, linking the
    character sum norm to exponential sums over units. -/
theorem charsum_gauss_bound (N : ℕ) (a : Fin N → ℂ)
    (S : (ZMod p)ˣ → ℂ)
    (hS : S = fun (b : (ZMod p)ˣ) =>
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ)))
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 =
    (p : ℝ)⁻¹ * ‖∑ b : (ZMod p)ˣ, χ⁻¹ (↑b) * S b‖ ^ 2 := by
  subst hS
  exact char_sum_norm_sq_eq_parseval_form N a χ hχ

/-- **Sum rewriting**: Rewrite the sum over nontrivial chi using Gauss expansion. -/
theorem charsum_sum_eq_inv_parseval (N : ℕ) (a : Fin N → ℂ)
    (S : (ZMod p)ˣ → ℂ)
    (hS : S = fun (b : (ZMod p)ˣ) =>
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ))) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 =
    (p : ℝ)⁻¹ *
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ b : (ZMod p)ˣ, χ⁻¹ (↑b) * S b‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  exact charsum_gauss_bound N a S hS χ (Finset.mem_filter.mp hχ).2

/-- Commuting factors in the character-weighted sum. -/
theorem charsum_comm_factors (S : (ZMod p)ˣ → ℂ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ b : (ZMod p)ˣ, χ (↑b) * S b‖ ^ 2 =
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ b : (ZMod p)ˣ, S b * χ (↑b)‖ ^ 2 := by
  congr 1; ext χ; congr 2; congr 1; ext b; ring

/-- The unweighted bound: character sums bounded by (p-1)/p times exponential sum norms. -/
theorem charsum_le_inv_parseval (N : ℕ) (a : Fin N → ℂ)
    (S : (ZMod p)ˣ → ℂ)
    (hS : S = fun (b : (ZMod p)ˣ) =>
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ))) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 ≤
    (p : ℝ)⁻¹ * ((p : ℝ) - 1) * ∑ b : (ZMod p)ˣ, ‖S b‖ ^ 2 := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.out.pos
  rw [charsum_sum_eq_inv_parseval N a S hS,
      sum_filter_inv_eq (p := p) (fun χ => ‖∑ b : (ZMod p)ˣ, χ (↑b) * S b‖ ^ 2),
      charsum_comm_factors S, mul_assoc]
  exact mul_le_mul_of_nonneg_left (nontrivial_char_parseval_le S)
    (le_of_lt (inv_pos.mpr hp_pos))

/-- **Parseval chain**: The weighted sum of nontrivial character sum norms squared
    is bounded by the sum of exponential sum norms squared over units. -/
theorem parseval_chain (N : ℕ) (a : Fin N → ℂ)
    (S : (ZMod p)ˣ → ℂ)
    (hS : S = fun (b : (ZMod p)ˣ) =>
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ))) :
    (p : ℝ) / ((p : ℝ) - 1) *
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
      ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2 ≤
    ∑ b : (ZMod p)ˣ, ‖S b‖ ^ 2 := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.out.pos
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp_pos
  have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.two_le
    linarith
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1_pos
  have h_le := charsum_le_inv_parseval N a S hS
  calc (p : ℝ) / ((p : ℝ) - 1) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ p)).filter (· ≠ 1),
        ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2
      ≤ (p : ℝ) / ((p : ℝ) - 1) *
        ((p : ℝ)⁻¹ * ((p : ℝ) - 1) * ∑ b : (ZMod p)ˣ, ‖S b‖ ^ 2) := by gcongr
    _ = ∑ b : (ZMod p)ˣ, ‖S b‖ ^ 2 := by field_simp

set_option maxHeartbeats 400000 in
/-- **Unit evaluation points are spaced**: the points `val(↑b)/p` for `b : (ZMod p)ˣ`
    reindexed through `Fin (card units)` are `(1/p)`-spaced. -/
theorem unit_points_spaced (hp_prime : Nat.Prime p)
    (e : Fin (Fintype.card (ZMod p)ˣ) ≃ (ZMod p)ˣ)
    (α : Fin (Fintype.card (ZMod p)ˣ) → ℝ)
    (hα : α = fun r => (ZMod.val (↑(e r) : ZMod p) : ℝ) / (p : ℝ)) :
    IsSpaced α (1 / (p : ℝ)) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
  intro r s hrs
  rw [hα]
  have hne : e r ≠ e s := fun h => hrs (e.injective h)
  have hval_ne : (↑(e r) : ZMod p) ≠ (↑(e s) : ZMod p) := by
    intro h; exact hne (Units.val_injective h)
  have hv_ne : ZMod.val (↑(e r) : ZMod p) ≠ ZMod.val (↑(e s) : ZMod p) := by
    intro h; exact hval_ne (ZMod.val_injective p h)
  have hval_lt_r : ZMod.val (↑(e r) : ZMod p) < p := ZMod.val_lt _
  have hval_lt_s : ZMod.val (↑(e s) : ZMod p) < p := ZMod.val_lt _
  have hfr : Int.fract ((ZMod.val (↑(e r) : ZMod p) : ℝ) / (p : ℝ)) =
      (ZMod.val (↑(e r) : ZMod p) : ℝ) / (p : ℝ) := by
    rw [Int.fract_eq_self]
    exact ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hp_pos),
      by rw [div_lt_one hp_pos]; exact_mod_cast hval_lt_r⟩
  have hfs : Int.fract ((ZMod.val (↑(e s) : ZMod p) : ℝ) / (p : ℝ)) =
      (ZMod.val (↑(e s) : ZMod p) : ℝ) / (p : ℝ) := by
    rw [Int.fract_eq_self]
    exact ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hp_pos),
      by rw [div_lt_one hp_pos]; exact_mod_cast hval_lt_s⟩
  rw [hfr, hfs]
  rw [show (ZMod.val (↑(e r) : ZMod p) : ℝ) / (p : ℝ) -
      (ZMod.val (↑(e s) : ZMod p) : ℝ) / (p : ℝ) =
      ((ZMod.val (↑(e r) : ZMod p) : ℝ) - (ZMod.val (↑(e s) : ZMod p) : ℝ)) / (p : ℝ)
    from div_sub_div_same _ _ _]
  rw [abs_div, abs_of_pos hp_pos, le_div_iff₀ hp_pos]
  rw [show 1 / (p : ℝ) * (p : ℝ) = 1 from by field_simp]
  -- Distinct naturals differ by ≥ 1 as reals
  have hint_ne : (ZMod.val (↑(e r) : ZMod p) : ℤ) ≠ (ZMod.val (↑(e s) : ZMod p) : ℤ) := by
    exact_mod_cast hv_ne
  have hint_abs := Int.one_le_abs (sub_ne_zero.mpr hint_ne)
  -- Transfer from ℤ to ℝ
  have h_real : (1 : ℝ) ≤ |(ZMod.val (↑(e r) : ZMod p) : ℝ) -
      (ZMod.val (↑(e s) : ZMod p) : ℝ)| := by
    have key : ((|↑(ZMod.val (↑(e r) : ZMod p)) - ↑(ZMod.val (↑(e s) : ZMod p))| : ℤ) : ℝ) ≥ 1 := by
      exact_mod_cast hint_abs
    calc (1 : ℝ) ≤ |(↑(ZMod.val (↑(e r) : ZMod p) : ℤ) : ℝ) -
        (↑(ZMod.val (↑(e s) : ZMod p) : ℤ) : ℝ)| := by
          rw [← Int.cast_sub, ← Int.cast_abs]; exact_mod_cast hint_abs
      _ = |(ZMod.val (↑(e r) : ZMod p) : ℝ) - (ZMod.val (↑(e s) : ZMod p) : ℝ)| := by
          push_cast; ring_nf
  exact h_real

set_option maxHeartbeats 400000 in
/-- **ALS LHS reindexing**: The ALS sum over `Fin R` at evaluation points `val(b)/p`
    equals the sum over `(ZMod p)ˣ` of the exponential sums `S(b)`. -/
theorem als_reindex (N : ℕ) (a : Fin N → ℂ)
    (S : (ZMod p)ˣ → ℂ)
    (hS : S = fun (b : (ZMod p)ˣ) =>
      ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ)))
    (e : Fin (Fintype.card (ZMod p)ˣ) ≃ (ZMod p)ˣ)
    (α : Fin (Fintype.card (ZMod p)ˣ) → ℝ)
    (hα : α = fun r => (ZMod.val (↑(e r) : ZMod p) : ℝ) / (p : ℝ)) :
    ∑ r : Fin (Fintype.card (ZMod p)ˣ),
      ‖∑ n : Fin N, a n * eAN (α r * ↑(n : ℕ))‖ ^ 2 =
    ∑ b : (ZMod p)ˣ, ‖S b‖ ^ 2 := by
  -- Reindex via e
  apply Fintype.sum_equiv e
  intro r
  -- Goal: ‖∑ n, a n * eAN(α r * n)‖² = ‖S (e r)‖²
  rw [hS, hα]
  congr 1; congr 1
  apply Finset.sum_congr rfl; intro n _
  congr 1
  rw [eAN_eq_root_eAN]
  congr 1; push_cast; ring

set_option maxHeartbeats 800000 in
/-- **ALS implies MLS for prime modulus**: the reduction from the additive
    large sieve to the multiplicative large sieve for a single prime modulus.

    Proof: Gauss expansion + Parseval orthogonality + ALS at evaluation points b/p. -/
theorem als_implies_mls_prime : AdditiveLargeSieve → MultiplicativeLargeSievePrime := by
  intro hals p hp_prime N hN a
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
  -- Define exponential sums
  set S : (ZMod p)ˣ → ℂ := fun (b : (ZMod p)ˣ) =>
    ∑ n : Fin N, a n * _root_.eAN ((↑(↑n : ℤ) : ℝ) * (ZMod.val (↑b : ZMod p) : ℝ) / (p : ℝ))
  -- Step 1-3: Parseval chain
  have h_weighted := parseval_chain N a S rfl
  -- Step 4: Apply ALS
  set R := Fintype.card (ZMod p)ˣ
  set e : Fin R ≃ (ZMod p)ˣ := (Fintype.equivFin (ZMod p)ˣ).symm
  set α : Fin R → ℝ := fun r => (ZMod.val (↑(e r) : ZMod p) : ℝ) / (p : ℝ)
  have hδ : (0 : ℝ) < 1 / (p : ℝ) := div_pos one_pos hp_pos
  have hδ_le : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp_pos (by norm_num : (0 : ℝ) < 2)]
    simp only [one_mul]
    exact_mod_cast hp_prime.two_le
  have hspaced := unit_points_spaced hp_prime e α rfl
  have hals_bound := hals R N α a (1 / (p : ℝ)) hδ hδ_le hN hspaced
  have hals_lhs_eq := als_reindex N a S rfl e α rfl
  rw [hals_lhs_eq] at hals_bound
  -- Simplify the ALS bound: 1/(1/p) = p
  have hsimp : (1 / (1 / (p : ℝ)) + ↑N - 1) = ((N : ℝ) - 1 + (p : ℝ)) := by
    rw [one_div_one_div]; ring
  rw [hsimp] at hals_bound
  exact le_trans h_weighted hals_bound

end MLSPrimeProof

end MultiplicativeLargeSieve

end IK
