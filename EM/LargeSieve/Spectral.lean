import EM.LargeSieve.Analytic
import EM.ForMathlib.VanDerCorput

/-!
# Walk Energy and Higher-Order Decorrelation

Walk energy Parseval identity (§66), subquadratic visit energy bridge (§67),
finite Weyl criterion (§68), and higher-order decorrelation / van der Corput
(§69) with the HOD-simplified chain theorems.

Material extracted elsewhere: CME reductions, fiber energy bounds, and
hierarchy connectors to `EM/CME/Reduction.lean`; the Elliott–Halberstam
chain (§71) to `EM/LargeSieve/Basic.lean`; energy increment dynamics (§75)
to `EM/LargeSieve/WalkAnalysis.lean`.

## Main Results

* `walk_energy_parseval` : Parseval identity for walk character sums (PROVED)
* `sve_implies_mmcsb` : SubquadraticVisitEnergy ⟹ MMCSB (PROVED)
* `van_der_corput_bound` : van der Corput inequality for character sums (PROVED)
* `hod_implies_ccsb` : HOD ⟹ CCSB (PROVED)
* `sve_implies_mc` : SVE ⟹ MC (PROVED)
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## §66. Walk Energy Parseval Identity

For any function `w : Fin N → (ZMod p)ˣ` (e.g., the Euclid-Mullin walk), the
**Walk Energy Parseval Identity** relates the total character sum energy

    ∑_χ ‖∑_{n<N} χ(w(n))‖²

to the occupation measure (visit counts) `V_N(a) := #{n < N : w(n) = a}`:

    ∑_χ ‖∑_{n<N} χ(w(n))‖² = (p-1) · ∑_{a : (ZMod p)ˣ} V_N(a)²

This follows from two ingredients:
1. **Rearrangement**: ∑_n χ(w(n)) = ∑_a V_N(a) · χ(a) (sum over fibers)
2. **`char_parseval_units`** (§60): Parseval for multiplicative characters on (ZMod p)ˣ

We also prove the **energy lower bound** ∑_a V_N(a)² ≥ N²/(p-1) by Cauchy-Schwarz,
which gives a lower bound on the total character sum energy. -/

section WalkEnergyParseval

open Finset DirichletCharacter

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP66 : NeZero p := ⟨hp.out.ne_zero⟩

/-- Walk occupation measure: count of visits to unit `a` in `N` steps. -/
noncomputable def walkVisitCount {N : ℕ} (w : Fin N → (ZMod p)ˣ) (a : (ZMod p)ˣ) : ℕ :=
  (Finset.univ.filter (fun n => w n = a)).card

/-- Visit counts sum to N: ∑_a V_N(a) = N. -/
theorem walkVisitCount_sum {N : ℕ} (w : Fin N → (ZMod p)ˣ) :
    ∑ a : (ZMod p)ˣ, walkVisitCount w a = N := by
  simp only [walkVisitCount]
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
      (f := w) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

/-- Rearrangement: walk character sum equals occupation-weighted character sum.
    ∑_{n < N} χ(w(n)) = ∑_{a : (ZMod p)ˣ} V_N(a) · χ(↑a) -/
theorem walk_char_sum_eq_occupation {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (χ : DirichletCharacter ℂ p) :
    ∑ n : Fin N, χ (↑(w n) : ZMod p) =
    ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℂ) * χ (↑a : ZMod p) := by
  -- Regroup the LHS by the value of w(n) using Finset.sum_fiberwise
  have : ∑ n : Fin N, χ (↑(w n) : ZMod p) =
      ∑ n ∈ Finset.univ, χ (↑(w n) : ZMod p) := by simp
  rw [this, ← Finset.sum_fiberwise Finset.univ w (fun n => χ (↑(w n) : ZMod p))]
  congr 1; ext a
  -- In the fiber {n | w n = a}, χ(w(n)) = χ(a)
  simp only [walkVisitCount]
  rw [Finset.sum_filter]
  conv_lhs =>
    arg 2; ext n; rw [show (if w n = a then χ (↑(w n) : ZMod p) else 0) =
      (if w n = a then χ (↑a : ZMod p) else 0) from by
        split_ifs with h
        · rw [h]
        · rfl]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- **Walk Energy Parseval**: ∑_χ ‖∑_{n<N} χ(w(n))‖² = (p-1) · ∑_a V_N(a)².
    This is the composition of the rearrangement lemma with `char_parseval_units`. -/
theorem walk_energy_parseval {N : ℕ} (w : Fin N → (ZMod p)ˣ) :
    ∑ χ : DirichletCharacter ℂ p,
      ‖∑ n : Fin N, χ (↑(w n) : ZMod p)‖ ^ 2 =
    ((p : ℝ) - 1) * ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) ^ 2 := by
  -- Step 1: Rewrite walk character sums as occupation-weighted sums
  conv_lhs =>
    arg 2; ext χ; rw [walk_char_sum_eq_occupation w χ]
  -- Step 2: Apply char_parseval_units with g(a) := (V_N(a) : ℂ)
  have h := char_parseval_units (fun a => (walkVisitCount w a : ℂ))
  -- Step 3: Simplify ‖(V_N(a) : ℂ)‖² = (V_N(a))²
  simp only [Complex.norm_natCast] at h
  exact h

/-- Visit counts satisfy ∑_a V_N(a)² ≥ N²/(p-1) by Cauchy-Schwarz.
    This gives a lower bound on the character sum energy. -/
theorem visit_energy_lower_bound {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (hp1 : (1 : ℝ) ≤ (p : ℝ) - 1) :
    (N : ℝ) ^ 2 / ((p : ℝ) - 1) ≤
    ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) ^ 2 := by
  -- Cauchy-Schwarz: (∑ a, 1 * V(a))² ≤ (∑ a, 1²) · (∑ a, V(a)²)
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun (_ : (ZMod p)ˣ) => (1 : ℝ)) (fun a => (walkVisitCount w a : ℝ))
  simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at cs
  -- cs : (∑ 1 * V(a))² ≤ card * ∑ V(a)²
  -- card = p - 1 (number of units)
  have hcard : (Finset.univ : Finset (ZMod p)ˣ).card = p - 1 := by
    rw [Finset.card_univ, ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  -- ∑ V(a) = N as ℕ, then cast to ℝ
  have hsum_eq : ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) = (N : ℝ) := by
    have h := walkVisitCount_sum w
    exact_mod_cast h
  -- Simplify (∑ 1 * V(a)) to (∑ V(a))
  simp only [one_mul] at cs
  rw [hsum_eq, hcard] at cs
  -- cs : N² ≤ ↑(p-1) * ∑ V(a)²
  -- Convert ↑(p-1 : ℕ) to (↑p - 1 : ℝ) using Nat.cast_sub
  rw [Nat.cast_sub hp.out.one_le, Nat.cast_one] at cs
  -- cs : N² ≤ (↑p - 1) * ∑ V(a)²
  -- Goal: N² / (↑p - 1) ≤ ∑ V(a)²
  rw [mul_comm] at cs
  rwa [div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)]

end WalkEnergyParseval

/-! ## §67. SubquadraticVisitEnergy → MMCSB Markov Bridge

If the visit energy of the EM walk is subquadratic — i.e., the excess energy
`(p-1) · ∑_a V_N(a)² - N²` is `o(N²)` — then every nontrivial character sum
is `o(N)`, yielding `MultiModularCSB`.

**Proof sketch** (no Markov needed):
1. Walk Energy Parseval (§66): `∑_χ ‖S_χ‖² = (p-1) · ∑_a V_N(a)²`
2. Trivial character contributes `N²`, so `∑_{χ≠1} ‖S_χ‖² = excessEnergy`
3. SubquadraticVisitEnergy: `excessEnergy ≤ ε · N²`
4. Each nontrivial term: `‖S_χ‖² ≤ ∑_{χ≠1} ‖S_χ‖² ≤ ε · N²`
5. Hence `‖S_χ‖ ≤ √ε · N`
6. Since `ε` is arbitrary, walk sums are `o(N)` → MMCSB → MC -/

section SubquadraticVisitEnergyBridge

open Finset DirichletCharacter
open Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP67 : NeZero p := ⟨hp.out.ne_zero⟩

/-- Excess energy: the nontrivial part of the character sum energy.
    Equals `(p-1) · ∑_a V_N(a)² - N²`, i.e., the total walk energy minus
    the trivial character's contribution. -/
noncomputable def excessEnergy {N : ℕ} (w : Fin N → (ZMod p)ˣ) : ℝ :=
  ((p : ℝ) - 1) * (∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) ^ 2) - (N : ℝ) ^ 2

/-- The excess energy equals the sum of ‖S_χ‖² over nontrivial characters.

    From Walk Energy Parseval: `∑_χ ‖S_χ‖² = (p-1) · ∑_a V_N(a)²`.
    The trivial character contributes `‖∑ 1‖² = N²`.
    Hence `∑_{χ≠1} ‖S_χ‖² = (p-1) · ∑_a V_N(a)² - N² = excessEnergy`. -/
theorem excess_energy_eq_nontrivial_sum {N : ℕ} (w : Fin N → (ZMod p)ˣ) :
    excessEnergy w =
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => ‖∑ n : Fin N, χ (↑(w n) : ZMod p)‖ ^ 2) := by
  unfold excessEnergy
  -- From walk_energy_parseval: total = (p-1) * ∑ V(a)²
  have hparseval := walk_energy_parseval w
  -- Split the total sum into trivial + nontrivial
  set g : DirichletCharacter ℂ p → ℝ :=
    fun χ => ‖∑ n : Fin N, χ (↑(w n) : ZMod p)‖ ^ 2
  have hsplit : ∑ χ : DirichletCharacter ℂ p, g χ =
    g 1 + (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum g := by
    rw [← Finset.add_sum_erase Finset.univ g (Finset.mem_univ _)]
  -- Trivial character: ‖∑ 1‖² = N²
  have h_triv : g 1 = (N : ℝ) ^ 2 := by
    show ‖∑ n : Fin N, (1 : DirichletCharacter ℂ p) (↑(w n) : ZMod p)‖ ^ 2 = _
    simp only [MulChar.one_apply_coe, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Complex.norm_natCast]
  -- Combine: excessEnergy = total - N² = ∑_{χ≠1} g(χ)
  -- Goal: (p-1)*∑V² - N² = (univ.erase 1).sum g
  -- From hsplit: univ.sum g = g 1 + (univ.erase 1).sum g
  -- From hparseval: univ.sum g = (p-1)*∑V²
  -- From h_triv: g 1 = N²
  -- Use sub_eq_iff to transform the goal
  have hee : (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum g =
      ((p : ℝ) - 1) * ∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) ^ 2 - (N : ℝ) ^ 2 := by
    linarith [hsplit]
  exact hee.symm

/-- The excess energy is nonneg. -/
theorem excessEnergy_nonneg {N : ℕ} (w : Fin N → (ZMod p)ˣ) :
    0 ≤ excessEnergy w := by
  rw [excess_energy_eq_nontrivial_sum]
  apply Finset.sum_nonneg
  intro χ _
  positivity

/-- Each nontrivial character's ‖S_χ‖² is bounded by the excess energy. -/
theorem nontrivial_char_sq_le_excess {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (ψ : DirichletCharacter ℂ p) (hψ : ψ ≠ 1) :
    ‖∑ n : Fin N, ψ (↑(w n) : ZMod p)‖ ^ 2 ≤ excessEnergy w := by
  rw [excess_energy_eq_nontrivial_sum]
  have hmem : ψ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p) :=
    Finset.mem_erase.mpr ⟨hψ, Finset.mem_univ ψ⟩
  exact Finset.single_le_sum (f := fun χ => ‖∑ n : Fin N, χ (↑(w n) : ZMod p)‖ ^ 2)
    (fun χ _ => sq_nonneg _) hmem

/-- **SubquadraticVisitEnergy**: the excess energy of the EM walk mod q
    is subquadratic — `o(N²)`. This is the spectral gap hypothesis:
    the EM walk visits all residue classes with approximately equal frequency.

    Formally: there exists Q₀ such that for all primes q ≥ Q₀ not in the
    sequence, and for every ε > 0, there exists N₀ such that for all N ≥ N₀:

        excessEnergy(emWalk mod q restricted to [0,N)) ≤ ε · N²

    Here `emWalkFin` restricts the EM walk `emWalkUnit q : ℕ → (ZMod q)ˣ`
    to `Fin N → (ZMod q)ˣ`. -/
def SubquadraticVisitEnergy : Prop :=
  ∃ Q₀ : ℕ, ∀ (q : Nat) [Fact (Nat.Prime q)], q ≥ Q₀ →
  ∀ (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    excessEnergy (fun (n : Fin N) => emWalkUnit q hq hne n.val) ≤ ε * (N : ℝ) ^ 2

/-- **SVE → MMCSB**: SubquadraticVisitEnergy implies MultiModularCSB.

    Proof: For each nontrivial character χ and ε > 0, pick ε' = ε².
    SVE gives excessEnergy ≤ ε'·N² = ε²·N² for large N.
    Then ‖S_χ‖² ≤ excessEnergy ≤ ε²·N², so ‖S_χ‖ ≤ ε·N.
    This gives MMCSB. -/
theorem sve_implies_mmcsb (hsve : SubquadraticVisitEnergy) : MultiModularCSB := by
  obtain ⟨Q₀, hQ₀⟩ := hsve
  use Q₀
  intro q _inst hge hq hne χ _hχ ε hε
  -- Choose ε' = ε² > 0 for SVE
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  obtain ⟨N₀, hN₀⟩ := @hQ₀ q inferInstance hge hq hne (ε ^ 2) hε2
  refine ⟨N₀, fun N hN => ?_⟩
  -- Step 1: Convert Finset.range N sum to Fin N sum
  set w : Fin N → (ZMod q)ˣ := fun n => emWalkUnit q hq hne n.val
  have hsum_eq : ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
      ∑ n : Fin N, (χ (w n) : ℂ) := by
    rw [← Fin.sum_univ_eq_sum_range]
  rw [hsum_eq]
  -- Step 2: Excess energy bound from SVE
  have hexcess : excessEnergy w ≤ ε ^ 2 * (N : ℝ) ^ 2 := hN₀ N hN
  -- Step 3: Lift χ : (ZMod q)ˣ →* ℂˣ to a DirichletCharacter via equivToUnitHom
  have : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  -- MulChar.equivToUnitHom : DirichletCharacter ℂ q ≃ ((ZMod q)ˣ →* ℂˣ)
  set ψ : DirichletCharacter ℂ q := MulChar.equivToUnitHom.symm χ
  have hψ : ψ.toUnitHom = χ := by
    rw [MulChar.toUnitHom_eq]; exact MulChar.equivToUnitHom.apply_symm_apply χ
  -- ψ ≠ 1 since χ ≠ 1
  have hψne : ψ ≠ 1 := by
    intro h; apply _hχ; rw [h] at hψ
    have h1 : (1 : DirichletCharacter ℂ q).toUnitHom = 1 := by
      ext a; simp [MulChar.one_apply_coe]
    rw [h1] at hψ; exact hψ.symm
  -- Step 4: The DirichletCharacter sum equals the unit-hom sum
  have hsum_dc : ∑ n : Fin N, ψ (↑(w n) : ZMod q) =
      ∑ n : Fin N, (χ (w n) : ℂ) := by
    congr 1; ext n; rw [← hψ]
    exact (MulChar.coe_toUnitHom ψ (w n)).symm
  -- Step 5: ‖S_χ‖² ≤ excessEnergy ≤ ε²·N²
  have hle_excess : ‖∑ n : Fin N, (χ (w n) : ℂ)‖ ^ 2 ≤ excessEnergy w := by
    rw [← hsum_dc]; exact nontrivial_char_sq_le_excess w ψ hψne
  have hle_eps : ‖∑ n : Fin N, (χ (w n) : ℂ)‖ ^ 2 ≤ ε ^ 2 * (N : ℝ) ^ 2 :=
    le_trans hle_excess hexcess
  -- Step 6: Take square root: ‖S_χ‖ ≤ ε · N
  -- From ‖S‖² ≤ (ε·N)² with both sides nonneg, derive ‖S‖ ≤ ε·N
  set S := ‖∑ n : Fin N, (χ (w n) : ℂ)‖
  have hS_nonneg : (0 : ℝ) ≤ S := norm_nonneg _
  have hεN : (0 : ℝ) ≤ ε * (N : ℝ) := by positivity
  -- hle_eps : S ^ 2 ≤ ε ^ 2 * N ^ 2 = (ε * N) ^ 2
  have hle' : S ^ 2 ≤ (ε * (N : ℝ)) ^ 2 := by rw [mul_pow]; exact hle_eps
  -- S ≤ ε * N by monotonicity of sqrt on nonneg reals
  exact le_of_sq_le_sq hle' hεN

/-- **SVE → MC with finite verification**: SubquadraticVisitEnergy plus finite
    verification for primes below the threshold implies Mullin's Conjecture. -/
theorem sve_implies_mc
    (hsve : SubquadraticVisitEnergy)
    (hfin : FiniteMCBelow (sve_implies_mmcsb hsve).choose) :
    MullinConjecture :=
  mmcsb_implies_mc (sve_implies_mmcsb hsve) hfin

/-- **SVE with small threshold → MC unconditionally**: if SubquadraticVisitEnergy
    yields a threshold Q₀ ≤ 11, then MC follows from the already-verified
    FiniteMCBelow 11. -/
theorem sve_small_threshold_mc
    (hsve : SubquadraticVisitEnergy)
    (hsmall : (sve_implies_mmcsb hsve).choose ≤ 11) :
    MullinConjecture :=
  mmcsb_small_threshold_mc (sve_implies_mmcsb hsve) hsmall

end SubquadraticVisitEnergyBridge

/-! ### Shared helpers for telescoping identity and boundary norm -/

section TelescopingHelpers

open Finset

/-- The walk character sum equals the product sum minus the boundary term. -/
theorem walk_sum_eq_product_sub_boundary (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
    ∑ n ∈ Finset.range N, ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))
    - ((χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)) := by
  have hsub : ∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))
    - ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
      (χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ) := by
    rw [← Finset.sum_sub_distrib]
    convert walk_telescope_identity q hq hne χ N using 1
    congr 1; ext n; ring
  linear_combination -hsub

/-- The boundary term `χ(w(N)) - χ(w(0))` has norm at most 2. -/
theorem walk_boundary_norm_le_two (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖ ≤ 2 :=
  calc ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖
      ≤ ‖(χ (emWalkUnit q hq hne N) : ℂ)‖ + ‖(χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
        norm_sub_le _ _
    _ = 2 := by rw [walkTelescope_char_norm_one χ _, walkTelescope_char_norm_one χ _]; ring

end TelescopingHelpers

/-! ## §68. Finite Weyl Criterion for Walk Equidistribution

The **finite Weyl criterion** on a finite abelian group: a sequence is
equidistributed iff all nontrivial character sums are o(N).

Concretely, if every nontrivial Dirichlet character χ mod p satisfies
‖∑_{n<N} χ(w(n))‖ ≤ ε·N, then the walk's occupation measure satisfies
|V_N(a) − N/(p−1)| ≤ ε·N for every unit a.

The proof uses character orthogonality to expand the indicator function
1_a as a character sum, then applies triangle inequality + |χ(a⁻¹)| = 1. -/

section FiniteWeylCriterion

open Finset DirichletCharacter
open Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP68 : NeZero p := ⟨hp.out.ne_zero⟩

/-- **Walk equidistribution condition**: every nontrivial Dirichlet character sum
    along the walk is bounded by ε·N. -/
def WalkEquidistCondition {N : ℕ} (w : Fin N → (ZMod p)ˣ) (ε : ℝ) : Prop :=
  ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
    ‖∑ n : Fin N, χ (↑(w n) : ZMod p)‖ ≤ ε * (N : ℝ)

/-- Character orthogonality on units: ∑_χ χ(a⁻¹) · χ(x) = (p-1) · [x = a].
    This is the indicator function expansion for units of (ZMod p).
    Uses `DirichletCharacter.sum_char_inv_mul_char_eq` from Mathlib. -/
theorem char_indicator_expansion (a x : (ZMod p)ˣ) :
    ∑ χ : DirichletCharacter ℂ p, χ (↑a⁻¹ : ZMod p) * χ (↑x : ZMod p) =
    if x = a then ((p : ℂ) - 1) else 0 := by
  have ha : IsUnit (↑a : ZMod p) := Units.isUnit a
  have hmathlib := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (↑x : ZMod p)
  have hinv : (↑a : ZMod p)⁻¹ = ↑a⁻¹ := (Units.val_inv_eq_inv_val a).symm
  simp_rw [hinv] at hmathlib
  rw [hmathlib]
  simp only [Units.val_injective.eq_iff, eq_comm (a := a) (b := x)]
  split_ifs
  · rw [Nat.totient_prime hp.out, Nat.cast_sub hp.out.one_le]; norm_cast
  · rfl

/-- The occupation measure V_N(a) can be recovered from character sums via
    the orthogonality expansion:
    V_N(a) = (1/(p-1)) · ∑_χ χ(a⁻¹) · (∑_n χ(w(n))). -/
private theorem visit_count_char_expansion {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (hp1 : (1 : ℝ) < p) :
    (walkVisitCount w a : ℂ) =
    (1 / ((p : ℂ) - 1)) *
      ∑ χ : DirichletCharacter ℂ p, χ (↑a⁻¹ : ZMod p) *
        ∑ n : Fin N, χ (↑(w n) : ZMod p) := by
  have hp1c : (p : ℂ) - 1 ≠ 0 := by
    exact_mod_cast ne_of_gt (by linarith : (0 : ℝ) < (p : ℝ) - 1)
  -- RHS = (1/(p-1)) · ∑_χ ∑_n χ(a⁻¹) · χ(w(n))
  -- = (1/(p-1)) · ∑_n ∑_χ χ(a⁻¹) · χ(w(n))  [by sum_comm]
  -- = (1/(p-1)) · ∑_n (if w(n)=a then (p-1) else 0)  [by orthogonality]
  -- = (1/(p-1)) · (p-1) · V_N(a) = V_N(a)
  -- Key: swap sums and apply orthogonality
  have hkey : ∑ χ : DirichletCharacter ℂ p, χ (↑a⁻¹ : ZMod p) *
      ∑ n : Fin N, χ (↑(w n) : ZMod p) =
    ((p : ℂ) - 1) * (walkVisitCount w a : ℂ) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [char_indicator_expansion a]
    rw [← Finset.sum_filter]
    simp only [walkVisitCount, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hkey, one_div, ← mul_assoc, inv_mul_cancel₀ hp1c, one_mul]

/-- **Weyl criterion separating trivial character**: the occupation measure decomposes as
    V_N(a) = N/(p-1) + (1/(p-1)) · ∑_{χ≠1} χ(a⁻¹) · S_χ. -/
private theorem visit_count_nontrivial_decomposition {N : ℕ} (w : Fin N → (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (hp1 : (1 : ℝ) < p) :
    (walkVisitCount w a : ℂ) - (N : ℂ) / ((p : ℂ) - 1) =
    (1 / ((p : ℂ) - 1)) *
      (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
        (fun χ => χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p)) := by
  have hp1c : (p : ℂ) - 1 ≠ 0 := by
    exact_mod_cast ne_of_gt (by linarith : (0 : ℝ) < (p : ℝ) - 1)
  rw [visit_count_char_expansion w a hp1]
  -- Split ∑_χ = trivial + nontrivial
  have hsplit : ∑ χ : DirichletCharacter ℂ p,
      χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p) =
    (1 : DirichletCharacter ℂ p) (↑a⁻¹ : ZMod p) *
      (∑ n : Fin N, (1 : DirichletCharacter ℂ p) (↑(w n) : ZMod p)) +
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ _)]
  rw [hsplit]
  -- Trivial character: 1(a⁻¹) = 1, ∑_n 1(w(n)) = N
  have h_triv_inv : (1 : DirichletCharacter ℂ p) (↑a⁻¹ : ZMod p) = 1 :=
    MulChar.one_apply_coe a⁻¹
  simp only [h_triv_inv, one_mul, MulChar.one_apply_coe, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- Goal: (1/(p-1)) * (↑N + nontrivial) - ↑N/(p-1) = (1/(p-1)) * nontrivial
  field_simp
  ring

/-- **Finite Weyl criterion**: if all nontrivial character sums are bounded by ε·N,
    then the walk visits each unit approximately N/(p-1) times.

    Precisely: ‖V_N(a) − N/(p−1)‖ ≤ ε · N for every unit a ∈ (ZMod p)ˣ. -/
theorem weyl_criterion_finite_group {N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (w : Fin N → (ZMod p)ˣ) (hp1 : (1 : ℝ) < p)
    (hchar : WalkEquidistCondition w ε) (a : (ZMod p)ˣ) :
    ‖(walkVisitCount w a : ℂ) - (N : ℂ) / ((p : ℂ) - 1)‖ ≤ ε * (N : ℝ) := by
  have hp1r : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp1c : (p : ℂ) - 1 ≠ 0 := by
    exact_mod_cast ne_of_gt hp1r
  -- Step 1: Decompose via nontrivial characters
  rw [visit_count_nontrivial_decomposition w a hp1]
  -- Step 2: ‖(1/(p-1)) · ∑_{χ≠1} ...‖ ≤ (1/(p-1)) · ∑_{χ≠1} ‖...‖
  -- Rewrite the factor as a real-valued complex number to simplify norm
  have hfactor : (1 : ℂ) / ((p : ℂ) - 1) = ((1 / ((p : ℝ) - 1) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hfactor, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((p:ℝ) - 1))]
  -- Now goal: 1/((p:ℝ)-1) * ‖∑...‖ ≤ ε * N
  -- Bound ‖∑_{χ≠1} ...‖ ≤ ∑_{χ≠1} ‖...‖ by triangle inequality
  have htri : ‖(Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p))‖ ≤
    (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => ‖χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p)‖) :=
    norm_sum_le _ _
  -- Each term: ‖χ(a⁻¹) · S_χ‖ = ‖χ(a⁻¹)‖ · ‖S_χ‖ ≤ 1 · ε·N
  have hterm : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ p),
      ‖χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p)‖ ≤ ε * (N : ℝ) := by
    intro χ hχ
    rw [Finset.mem_erase] at hχ
    rw [norm_mul]
    have hle1 : ‖χ (↑a⁻¹ : ZMod p)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hSχ := hchar χ hχ.1
    calc ‖χ (↑a⁻¹ : ZMod p)‖ * ‖∑ n : Fin N, χ (↑(w n) : ZMod p)‖
        ≤ 1 * (ε * (N : ℝ)) :=
          mul_le_mul hle1 hSχ (norm_nonneg _) zero_le_one
      _ = ε * (N : ℝ) := one_mul _
  -- Sum bound: ∑ ‖...‖ ≤ card · (ε·N)
  have hsum_le : (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
      (fun χ => ‖χ (↑a⁻¹ : ZMod p) * ∑ n : Fin N, χ (↑(w n) : ZMod p)‖) ≤
    ((Finset.univ.erase (1 : DirichletCharacter ℂ p)).card : ℝ) * (ε * (N : ℝ)) := by
    have h := Finset.sum_le_card_nsmul _ _ _ hterm
    rwa [nsmul_eq_mul] at h
  -- Card of nontrivial characters = p - 1 - 1
  have hcard_val : (Finset.univ.erase (1 : DirichletCharacter ℂ p)).card = p - 1 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p,
      Nat.totient_prime hp.out]
  have hcard_le : ((Finset.univ.erase (1 : DirichletCharacter ℂ p)).card : ℝ) ≤ (p : ℝ) - 1 := by
    rw [hcard_val]
    have h2 : p - 1 - 1 ≤ p - 1 := Nat.sub_le _ _
    have : ((p - 1 - 1 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := Nat.cast_le.mpr h2
    calc ((p - 1 - 1 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := this
      _ = (p : ℝ) - 1 := by push_cast [Nat.cast_sub hp.out.one_le]; ring
  -- Combine: (1/(p-1)) · sum ≤ (1/(p-1)) · (p-1) · ε · N = ε · N
  calc 1 / ((p : ℝ) - 1) * ‖(Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum _‖
      ≤ 1 / ((p : ℝ) - 1) * ((Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
          (fun χ => ‖χ (↑a⁻¹ : ZMod p) * ∑ n, χ (↑(w n) : ZMod p)‖)) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ ≤ 1 / ((p : ℝ) - 1) * (((p : ℝ) - 1) * (ε * (N : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc (Finset.univ.erase (1 : DirichletCharacter ℂ p)).sum
              (fun χ => ‖χ (↑a⁻¹ : ZMod p) * ∑ n, χ (↑(w n) : ZMod p)‖)
            ≤ ((Finset.univ.erase (1 : DirichletCharacter ℂ p)).card : ℝ) * (ε * ↑N) :=
              hsum_le
          _ ≤ ((p : ℝ) - 1) * (ε * ↑N) :=
              mul_le_mul_of_nonneg_right hcard_le (by positivity)
    _ = ε * (N : ℝ) := by
        field_simp

end FiniteWeylCriterion

/-! ## S69. Higher-Order Decorrelation and Van der Corput

The **Van der Corput method** bounds character sums via autocorrelation estimates.
If the walk autocorrelations `R_h(N) = sum_{n<N-h} chi(w(n)) * conj(chi(w(n+h)))`
are o(N) for all lags h = 1, ..., H, then the character sum itself is o(N).

This section introduces:
- `HigherOrderDecorrelation`: open Prop saying all walk autocorrelations are o(N)
- `VanDerCorputBound`: open Prop encoding the standard VdC corollary for
  bounded sequences with small autocorrelations (a known result, not in Mathlib)
- `hod_vdc_implies_ccsb`: **PROVED** -- HOD + VdC -> ComplexCharSumBound
- Chain theorems to MullinConjecture

### Mathematical background

The finite Van der Corput inequality (Iwaniec-Kowalski, Lemma 8.3) gives:
for f : {0,...,N-1} -> C with |f(n)| <= 1, and H >= 1 with H <= N,

  |sum f(n)|^2 <= ((N+H)/(H+1)) * (N + 2 * sum_{h=1}^{H} |R_h|)

As a corollary: if |R_h| <= delta * N for all 1 <= h <= H, then
  |sum f(n)|^2 <= ((N+H)/(H+1)) * N * (1 + 2*H*delta)

For fixed H and delta, the RHS is O(N^2/(H+1) + delta*N^2). By choosing H large
(to make 1/(H+1) small) and delta small (via HOD), we get |sum f(n)| = o(N). -/

section HigherOrderDecorrelation

/-- **Higher-Order Decorrelation**: all walk autocorrelations `R_h(N)` are `o(N)`
    for every prime q not in the EM sequence and every nontrivial character.
    For `h = 1` this reduces to `EMMultCharSumBound`; for `h >= 2` it captures
    multi-step independence of consecutive multiplier character values. -/
def HigherOrderDecorrelation : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (chi : (ZMod q)ˣ →* ℂˣ) (_hchi : chi ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ H₀ : ℕ, ∀ H ≥ H₀,
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
  ∀ h : ℕ, 1 ≤ h → h ≤ H →
    ‖walkAutocorrelation q hq hne chi N h‖ ≤ ε * (N : ℝ)

/-! The van der Corput inequality (`VanDerCorputBound`, `van_der_corput_bound`) now lives in
`EM/ForMathlib/VanDerCorput.lean` (Mathlib-only imports; extracted 2026-08-18). -/

/-- **HOD + VdC implies ComplexCharSumBound**: combining the decorrelation
    hypothesis (autocorrelations are o(N)) with the Van der Corput bound
    gives that each character sum is o(N).

    **Proof**: Given chi nontrivial and eps > 0, we want ||S_chi|| <= eps * N
    for large N.

    Step 1: Call HOD with parameter eps^2/4. Get H_0.
    Step 2: Choose H = max(H_0, ceil(8/eps^2)). This ensures:
            - H >= H_0 (so HOD applies)
            - 2/(H+1) <= eps^2/4 (so the first VdC error term is small)
    Step 3: Get N_0 from HOD for this H.
    Step 4: For N >= N_0, VdC gives:
            ||S||^2 <= 2*N^2/(H+1) + 2*(eps^2/4)*N^2
                    <= (eps^2/4)*N^2 + (eps^2/2)*N^2
                    = (3/4)*eps^2*N^2
                    <= eps^2*N^2
    Step 5: Therefore ||S|| <= eps*N. -/
theorem hod_vdc_implies_ccsb
    (hhod : HigherOrderDecorrelation)
    (hvdc : VanDerCorputBound) :
    ComplexCharSumBound := by
  intro q _inst hq hne chi hchi ε hε
  -- Step 1: Call HOD with eps^2/4
  have hε2 : (0 : ℝ) < ε ^ 2 / 4 := by positivity
  obtain ⟨H₀, hH₀⟩ := hhod q hq hne chi hchi (ε ^ 2 / 4) hε2
  -- Step 2: Choose H = max(H_0, ceil(8/eps^2))
  set H : ℕ := max H₀ (Nat.ceil (8 / ε ^ 2) + 1) with hH_def
  have hH_ge_H0 : H ≥ H₀ := le_max_left _ _
  have hH_ge_1 : 1 ≤ H := le_trans (by omega : 1 ≤ Nat.ceil (8 / ε ^ 2) + 1) (le_max_right _ _)
  -- Step 3: Get N_0 from HOD
  obtain ⟨N₀, hN₀⟩ := hH₀ H hH_ge_H0
  -- We need N >= N_0 and N >= H
  refine ⟨max N₀ H, fun N hN => ?_⟩
  have hN_ge_N0 : N ≥ N₀ := le_trans (le_max_left _ _) hN
  have hN_ge_H : H ≤ N := le_trans (le_max_right _ _) hN
  -- Define f(n) = chi(w(n)) as a function on Nat
  set f : ℕ → ℂ := fun n => if h : n < N then
    (chi (emWalkUnit q hq hne n) : ℂ) else 0 with hf_def
  -- f has norm <= 1
  have hf_norm : ∀ n, ‖f n‖ ≤ 1 := by
    intro n
    simp only [hf_def]
    split_ifs with h
    · exact le_of_eq (walkTelescope_char_norm_one chi (emWalkUnit q hq hne n))
    · exact le_trans (le_of_eq norm_zero) zero_le_one
  -- The Finset.range N sum of f equals the original character sum
  have hsum_eq : ∑ n ∈ Finset.range N, f n =
      ∑ n ∈ Finset.range N, (chi (emWalkUnit q hq hne n) : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [hf_def, Finset.mem_range.mp hn, dite_true]
  -- The autocorrelation of f over range(N-h) matches walkAutocorrelation
  have hautocorr_eq : ∀ h : ℕ, 1 ≤ h → h ≤ H →
      ∑ n ∈ Finset.range (N - h), f n * starRingEnd ℂ (f (n + h)) =
      walkAutocorrelation q hq hne chi N h := by
    intro h hh1 hhH
    unfold walkAutocorrelation
    apply Finset.sum_congr rfl
    intro n hn
    have hn_range := Finset.mem_range.mp hn
    have hn_lt : n < N := by omega
    have hnh_lt : n + h < N := by omega
    simp only [hf_def, hn_lt, hnh_lt, dite_true]
  -- HOD gives autocorrelation bounds
  have hautocorr_bound : ∀ h : ℕ, 1 ≤ h → h ≤ H →
      ‖∑ n ∈ Finset.range (N - h), f n * starRingEnd ℂ (f (n + h))‖ ≤
      (ε ^ 2 / 4) * (N : ℝ) := by
    intro h hh1 hhH
    rw [hautocorr_eq h hh1 hhH]
    exact hN₀ N hN_ge_N0 h hh1 hhH
  -- Step 4: Apply VdC
  have hvdc_bound := hvdc N f hf_norm H hH_ge_1 hN_ge_H (ε ^ 2 / 4) hε2 hautocorr_bound
  -- hvdc_bound : ||sum f||^2 <= 2*N^2/(H+1) + 2*(eps^2/4)*N^2
  -- = 2*N^2/(H+1) + eps^2*N^2/2
  rw [hsum_eq] at hvdc_bound
  -- Key: 2/(H+1) <= eps^2/4 from our choice of H
  have hH_large : (H : ℝ) + 1 ≥ 8 / ε ^ 2 := by
    have h1 : Nat.ceil (8 / ε ^ 2) + 1 ≤ H := le_max_right H₀ (Nat.ceil (8 / ε ^ 2) + 1)
    have h2 : (Nat.ceil (8 / ε ^ 2) : ℝ) ≥ 8 / ε ^ 2 := Nat.le_ceil _
    have h3 : (H : ℝ) ≥ (Nat.ceil (8 / ε ^ 2) : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have hH1_pos : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  -- 2/(H+1) <= 2/(8/eps^2) = eps^2/4
  have h_first_term : 2 * (N : ℝ) ^ 2 / ((H : ℝ) + 1) ≤ ε ^ 2 / 4 * (N : ℝ) ^ 2 := by
    rw [div_le_iff₀ hH1_pos]
    -- Need: 2 * N^2 ≤ (eps^2/4) * N^2 * (H+1)
    -- From hH_large: 8/eps^2 ≤ H+1, so eps^2 * (H+1) >= 8, so (eps^2/4)*(H+1) >= 2
    have h8 : 8 / ε ^ 2 ≤ (H : ℝ) + 1 := hH_large
    have hε2_pos : (0 : ℝ) < ε ^ 2 := by positivity
    have h_key : 8 ≤ ε ^ 2 * ((H : ℝ) + 1) := by
      have := (div_le_iff₀ hε2_pos).mp h8
      linarith
    nlinarith [sq_nonneg (N : ℝ)]
  -- Combine: ||S||^2 <= eps^2/4 * N^2 + 2*(eps^2/4)*N^2 = 3*eps^2/4 * N^2
  have hsq_le : ‖∑ n ∈ Finset.range N, (chi (emWalkUnit q hq hne n) : ℂ)‖ ^ 2 ≤
      ε ^ 2 * (N : ℝ) ^ 2 := by
    calc ‖∑ n ∈ Finset.range N, (chi (emWalkUnit q hq hne n) : ℂ)‖ ^ 2
        ≤ 2 * (N : ℝ) ^ 2 / ((H : ℝ) + 1) + 2 * (ε ^ 2 / 4) * (N : ℝ) ^ 2 :=
          hvdc_bound
      _ ≤ ε ^ 2 / 4 * (N : ℝ) ^ 2 + ε ^ 2 / 2 * (N : ℝ) ^ 2 := by linarith
      _ = 3 * ε ^ 2 / 4 * (N : ℝ) ^ 2 := by ring
      _ ≤ ε ^ 2 * (N : ℝ) ^ 2 := by nlinarith [sq_nonneg (N : ℝ), sq_nonneg ε]
  -- Step 5: Take square root
  have hεN_sq : ε ^ 2 * (N : ℝ) ^ 2 = (ε * (N : ℝ)) ^ 2 := by ring
  rw [hεN_sq] at hsq_le
  have hεN_nonneg : 0 ≤ ε * (N : ℝ) := by positivity
  exact le_of_sq_le_sq hsq_le hεN_nonneg

/-- **HOD + VdC → MC** (full chain): Higher-Order Decorrelation combined with
    the Van der Corput bound implies Mullin's Conjecture, via the chain
    HOD + VdC -> CCSB -> MC. -/
theorem hod_vdc_chain_mc
    (hhod : HigherOrderDecorrelation)
    (hvdc : VanDerCorputBound) :
    MullinConjecture :=
  complex_csb_mc' (hod_vdc_implies_ccsb hhod hvdc)

/-- **HOD + VdC → SVE**: Higher-Order Decorrelation and Van der Corput also
    imply SubquadraticVisitEnergy, since CCSB -> MMCSB -> SVE (visit energy
    is controlled by character sums via Parseval). This gives an alternative
    route through the occupation-measure framework. -/
theorem hod_vdc_implies_mmcsb
    (hhod : HigherOrderDecorrelation)
    (hvdc : VanDerCorputBound) :
    MultiModularCSB := by
  -- CCSB implies MMCSB with Q_0 = 0 (the universal bound)
  have hcsb := hod_vdc_implies_ccsb hhod hvdc
  exact ⟨0, fun q _inst _ hq hne chi hchi ε hε => hcsb q hq hne chi hchi ε hε⟩

end HigherOrderDecorrelation

/-! ## HOD-Simplified Chain Theorems

Since `VanDerCorputBound` is now proved as a theorem (not an open hypothesis),
we can provide simplified versions of the HOD chain theorems that take only
`HigherOrderDecorrelation` as a parameter. -/

section HODSimplified

/-- **HOD → CCSB** (simplified): Since VanDerCorputBound is proved,
    HigherOrderDecorrelation alone implies ComplexCharSumBound. -/
theorem hod_implies_ccsb (h : HigherOrderDecorrelation) : ComplexCharSumBound :=
  hod_vdc_implies_ccsb h van_der_corput_bound

/-- **HOD → MC** (simplified): HigherOrderDecorrelation alone implies
    Mullin's Conjecture, via the chain HOD → CCSB → MC. -/
theorem hod_chain_mc (h : HigherOrderDecorrelation) : MullinConjecture :=
  hod_vdc_chain_mc h van_der_corput_bound

/-- **HOD → MMCSB** (simplified): HigherOrderDecorrelation alone implies
    MultiModularCSB with Q₀ = 0. -/
theorem hod_implies_mmcsb (h : HigherOrderDecorrelation) : MultiModularCSB :=
  hod_vdc_implies_mmcsb h van_der_corput_bound

end HODSimplified
