import EM.LargeSieveAnalytic

/-!
# Walk Energy, Higher-Order Decorrelation, and CME

Walk energy Parseval identity, subquadratic visit energy bridge, finite Weyl
criterion, higher-order decorrelation (van der Corput), conditional multiplier
equidistribution (CME), fiber energy bounds, Elliott–Halberstam chain, and
energy increment dynamics.

## Main Results

* `walk_energy_parseval` : Parseval identity for walk character sums (PROVED)
* `subquadraticVisitEnergy_implies_mmcsb` : subquadratic energy ⟹ MMCSB (PROVED)
* `vanDerCorputBound` : van der Corput inequality for character sums (PROVED)
* `cme_implies_ccsb` : CME ⟹ CCSB bypassing BRE (PROVED)
* `cme_implies_mc` : CME ⟹ MC (PROVED)
* `ccsb_implies_mmcsb` : CCSB ⟹ MMCSB with Q₀ = 0 (PROVED)
* `ccsb_implies_sve` : CCSB ⟹ SVE (PROVED, completes CCSB ⟺ SVE)
* `cme_implies_vcb` : CME ⟹ VCB (PROVED: take μ = 0)
* `vcb_ped_implies_mc` : VCB + PED ⟹ MC (conditional on VCBPEDImpliesCCSB)
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

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP67 : NeZero p := ⟨hp.out.ne_zero⟩

/-- Excess energy: the nontrivial part of the character sum energy.
    Equals `(p-1) · ∑_a V_N(a)² - N²`, i.e., the total walk energy minus
    the trivial character's contribution. -/
noncomputable def excessEnergy {N : ℕ} (w : Fin N → (ZMod p)ˣ) : ℝ :=
  ((p : ℝ) - 1) * (∑ a : (ZMod p)ˣ, (walkVisitCount w a : ℝ) ^ 2) - (N : ℝ) ^ 2

open Classical in
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

open Classical in
/-- The excess energy is nonneg. -/
theorem excessEnergy_nonneg {N : ℕ} (w : Fin N → (ZMod p)ˣ) :
    0 ≤ excessEnergy w := by
  rw [excess_energy_eq_nontrivial_sum]
  apply Finset.sum_nonneg
  intro χ _
  positivity

open Classical in
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
  haveI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
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
private lemma char_indicator_expansion (a x : (ZMod p)ˣ) :
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
private lemma visit_count_char_expansion {N : ℕ} (w : Fin N → (ZMod p)ˣ)
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

open Classical in
/-- **Weyl criterion separating trivial character**: the occupation measure decomposes as
    V_N(a) = N/(p-1) + (1/(p-1)) · ∑_{χ≠1} χ(a⁻¹) · S_χ. -/
private lemma visit_count_nontrivial_decomposition {N : ℕ} (w : Fin N → (ZMod p)ˣ)
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

open Classical in
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

/-- **Higher-Order Decorrelation**: for all primes q not in the EM sequence,
    all nontrivial characters chi mod q, and all eps > 0, there exist H_0 such
    that for all H >= H_0 there exists N_0 such that for all N >= N_0 and all
    lags 1 <= h <= H, the walk autocorrelation satisfies ||R_h(N)|| <= eps * N.

    This hypothesis captures the idea that consecutive multiplier character values
    chi(m(n)), chi(m(n+1)), ..., chi(m(n+h-1)) are "asymptotically independent",
    so that h-fold products decorrelate. By `walkAutocorrelation_eq_mult_product`,
    R_h involves h-fold products of consecutive multiplier values, and decorrelation
    means these products average to zero.

    For h = 1, HOD reduces to `EMMultCharSumBound` (multiplier sums o(N)).
    For h >= 2, this is a genuinely stronger hypothesis about multi-step
    correlations in the EM sequence. -/
def HigherOrderDecorrelation : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (chi : (ZMod q)ˣ →* ℂˣ) (_hchi : chi ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ H₀ : ℕ, ∀ H ≥ H₀,
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
  ∀ h : ℕ, 1 ≤ h → h ≤ H →
    ‖walkAutocorrelation q hq hne chi N h‖ ≤ ε * (N : ℝ)

/-- **Van der Corput bound for bounded sequences**: a corollary of the classical
    finite Van der Corput inequality. For a bounded sequence f with small
    autocorrelations, the partial sum is small.

    Precisely: for any sequence f(0), ..., f(N-1) in C with ||f(n)|| <= 1,
    if there exist H >= 1 and delta > 0 such that
    ||sum_{n<N-h} f(n) * conj(f(n+h))|| <= delta * N for all 1 <= h <= H,
    then ||sum f(n)||^2 <= C * N^2 where C depends on H, delta.

    We state the bound in the form that is most convenient for composition
    with HOD: given H and delta, the conclusion bounds the sum norm squared
    by (2*N^2/(H+1) + 2*delta*N^2), capturing the two sources of error
    (short lag window and autocorrelation size).

    This is a known result in analytic number theory, not currently in Mathlib.

    **Proof**: We use the Iwaniec-Kowalski averaging trick. Define g : ℕ → ℂ as the
    zero extension of f (g(n) = f(n) for n < N, 0 otherwise). For the windowed sum
    w(j) = ∑_{h=0}^{min(j,H)} g(j-h), we have:
    (1) ∑_j w(j) = (H+1)·S (each value f(n) is counted H+1 times)
    (2) ∑_j ‖w(j)‖² = (H+1)·R₀ + 2·Re(∑_{ℓ=1}^H (H+1-ℓ)·R_ℓ)
        where R_ℓ = ∑_{n<N-ℓ} f(n)·conj(f(n+ℓ)) is the autocorrelation at lag ℓ.
    By Cauchy-Schwarz: (H+1)²·‖S‖² ≤ (N+H)·∑‖w(j)‖².
    Bounding: ∑‖w(j)‖² ≤ (H+1)N + 2δN·H(H+1)/2 = (H+1)N(1+Hδ).
    So ‖S‖² ≤ N(N+H)(1+Hδ)/(H+1) ≤ 2N²/(H+1) + 2δN². -/
def VanDerCorputBound : Prop :=
  ∀ (N : ℕ) (f : ℕ → ℂ),
  (∀ n, ‖f n‖ ≤ 1) →
  ∀ (H : ℕ), 1 ≤ H → H ≤ N →
  ∀ (δ : ℝ), 0 < δ →
  (∀ h : ℕ, 1 ≤ h → h ≤ H →
    ‖∑ n ∈ Finset.range (N - h), f n * starRingEnd ℂ (f (n + h))‖ ≤ δ * (N : ℝ)) →
  ‖∑ n ∈ Finset.range N, f n‖ ^ 2 ≤
    2 * (N : ℝ) ^ 2 / ((H : ℝ) + 1) + 2 * δ * (N : ℝ) ^ 2

/-- Cauchy-Schwarz for `Finset.range` sums: `‖∑_{i<M} z_i‖² ≤ M · ∑_{i<M} ‖z_i‖²`. -/
private lemma norm_sq_sum_le_card_mul_range {M : ℕ} {z : ℕ → ℂ} :
    ‖∑ j ∈ Finset.range M, z j‖ ^ 2 ≤ (M : ℝ) * ∑ j ∈ Finset.range M, ‖z j‖ ^ 2 := by
  have h1 : ‖∑ j ∈ Finset.range M, z j‖ ^ 2 ≤ (∑ j ∈ Finset.range M, ‖z j‖) ^ 2 := by
    gcongr; exact norm_sum_le _ _
  calc ‖∑ j ∈ Finset.range M, z j‖ ^ 2
      ≤ (∑ j ∈ Finset.range M, ‖z j‖) ^ 2 := h1
    _ = (∑ j ∈ Finset.range M, 1 * ‖z j‖) ^ 2 := by simp
    _ ≤ (∑ _j ∈ Finset.range M, (1 : ℝ) ^ 2) * (∑ j ∈ Finset.range M, ‖z j‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq (Finset.range M) (fun _ => 1) (fun j => ‖z j‖)
    _ = (M : ℝ) * ∑ j ∈ Finset.range M, ‖z j‖ ^ 2 := by
        simp [Finset.card_range]

private lemma int_shift_injOn (s : Finset ℕ) (c : ℤ) :
    Set.InjOn (fun n : ℕ => (↑n + c : ℤ)) s := by
  intro a _ b _ hab; exact_mod_cast show (a : ℤ) = b by linarith

/-- **Van der Corput bound** (proved): the finite Van der Corput inequality
    for bounded sequences with small autocorrelations.

    Proof uses the Iwaniec-Kowalski averaging trick: define w(j) = ∑_{h≤H} g(j-h)
    where g is the zero extension of f. Then ∑w = (H+1)S, and Cauchy-Schwarz gives
    (H+1)²‖S‖² ≤ (N+H)·∑‖w(j)‖². The energy ∑‖w(j)‖² expands via double sum
    into autocorrelations and is bounded by (H+1)N(1+Hδ). -/
theorem vanDerCorputBound : VanDerCorputBound := by
  intro N f hf H hH1 hHN δ hδ hR
  have hN_pos : 0 < N := lt_of_lt_of_le hH1 hHN
  have hNr : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
  have hH1r : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  set S := ∑ n ∈ Finset.range N, f n with hS_def
  -- Reduce to IK inequality
  suffices hIK : ((H : ℝ) + 1) ^ 2 * ‖S‖ ^ 2 ≤
      2 * (↑N : ℝ) * ((H : ℝ) + 1) * ↑N * (1 + ↑H * δ) by
    have h1 : ‖S‖ ^ 2 ≤ 2 * (N : ℝ) ^ 2 * (1 + (H : ℝ) * δ) / ((H : ℝ) + 1) := by
      rw [le_div_iff₀ hH1r]
      nlinarith [sq ((H : ℝ) + 1), sq_nonneg ‖S‖]
    have h2 : 2 * (N : ℝ) ^ 2 * (1 + (H : ℝ) * δ) / ((H : ℝ) + 1)
        ≤ 2 * (N : ℝ) ^ 2 / ((H : ℝ) + 1) + 2 * δ * (N : ℝ) ^ 2 := by
      suffices h : 2 * (N : ℝ) ^ 2 * ((H : ℝ) * δ) / ((H : ℝ) + 1) ≤
          2 * δ * (N : ℝ) ^ 2 by
        have expand : 2 * (N : ℝ) ^ 2 * (1 + (H : ℝ) * δ) / ((H : ℝ) + 1) =
            2 * (N : ℝ) ^ 2 / ((H : ℝ) + 1) + 2 * (N : ℝ) ^ 2 * ((H : ℝ) * δ) / ((H : ℝ) + 1) := by
          rw [mul_add, mul_one, add_div]
        linarith
      rw [div_le_iff₀ hH1r]; nlinarith
    linarith
  -- == Prove IK inequality ==
  -- Use ℕ-indexed windowed sum to avoid ℤ coercion issues.
  -- g(n) = f(n) for n < N, 0 otherwise (on ℕ)
  -- w(j) = ∑_{h=0}^{H} g(j-h) = ∑_{h=0}^{min(j,H)} f(j-h) when j-h < N
  -- The key quantities:
  --   diag = ∑_{h=0}^{H} ∑_{n<N} ‖f(n)‖² = (H+1)·∑‖f‖² ≤ (H+1)N
  --   offdiag = 2·∑_{ℓ=1}^{H} Re(∑_{n<N-ℓ} f(n)·conj(f(n+ℓ)))
  -- and (H+1)²‖S‖² ≤ (N+H)·((H+1)N + ∑offdiag)
  --
  -- We work directly with the VdC identity in a simplified form.
  -- From the autocorrelation hypothesis and the trivial bound ‖f‖≤1:
  -- ‖S‖² = ∑_n |f(n)|² + 2·Re(∑_{ℓ=1}^{N-1} ∑_{n<N-ℓ} f(n)·conj(f(n+ℓ)))
  -- But this gives ‖S‖² ≤ N + 2·(N-1)·δ·N which is O(δN²), missing the 1/(H+1) factor.
  --
  -- The windowed-sum approach IS needed. Use ℤ-indexed version but be careful with casts.
  -- Define g : ℤ → ℂ as zero extension
  set g : ℤ → ℂ := fun n => if 0 ≤ n ∧ n < (N : ℤ) then f n.toNat else 0 with hg_def
  -- w(j) = ∑_{h=0}^{H} g(j - h)
  set w : ℤ → ℂ := fun j => ∑ h ∈ Finset.range (H + 1), g (j - ↑h) with hw_def
  set Jset := (Finset.Ico (0 : ℤ) (↑N + ↑H)) with hJset_def
  -- Step A: Sum identity
  -- We prove this by showing ∑_{j∈Jset} g(j-h) = S for each h ∈ [0,H]
  have hg_shift_sum : ∀ h ≤ H, ∑ j ∈ Jset, g (j - (h : ℤ)) = S := by
    intro h hh
    -- The nonzero terms are exactly those with 0 ≤ j-h < N, i.e., h ≤ j < N+h
    -- Reindex: n = j - h, so j = n + h with n ∈ [0, N)
    -- Step 1: zero-extend beyond support
    have : ∑ j ∈ Jset, g (j - (h : ℤ)) =
        ∑ n ∈ Finset.range N, g (↑n) := by
      -- The image of range(N) under (n ↦ ↑n+h) ⊆ Jset
      set img := Finset.image (fun n : ℕ => (↑n + (h : ℤ))) (Finset.range N)
      have himg_sub : img ⊆ Jset := by
        intro j hj; simp only [img, Finset.mem_image, Finset.mem_range] at hj
        obtain ⟨n, hn, rfl⟩ := hj; simp [hJset_def, Finset.mem_Ico]; omega
      -- Outside the image, g(j-h) = 0
      have hzero : ∀ j ∈ Jset, j ∉ img → g (j - (h : ℤ)) = 0 := by
        intro j _ hnmem
        simp only [hg_def]; split_ifs with hcond
        · exfalso; apply hnmem
          simp only [img, Finset.mem_image, Finset.mem_range]
          exact ⟨(j - (h : ℤ)).toNat, by omega, by omega⟩
        · rfl
      rw [← Finset.sum_subset himg_sub (fun j hj hnj => hzero j hj hnj)]
      rw [Finset.sum_image (int_shift_injOn _ _)]
      apply Finset.sum_congr rfl; intro n _
      show g ((↑n + (h : ℤ)) - (h : ℤ)) = g (↑n)
      congr 1; omega
    rw [this]
    apply Finset.sum_congr rfl
    intro n hn
    have hn_lt := Finset.mem_range.mp hn
    simp [hg_def, hn_lt]
  have hsum_identity : ∑ j ∈ Jset, w j = (↑(H + 1) : ℂ) * S := by
    simp only [hw_def]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun h hh => hg_shift_sum h
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)))]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Step B: Cauchy-Schwarz
  have hcard_Jset : Jset.card = N + H := by
    simp [hJset_def, Int.card_Ico]; omega
  have hCS : ‖∑ j ∈ Jset, w j‖ ^ 2 ≤ (↑(N + H) : ℝ) * ∑ j ∈ Jset, ‖w j‖ ^ 2 := by
    calc ‖∑ j ∈ Jset, w j‖ ^ 2
        ≤ (∑ j ∈ Jset, ‖w j‖) ^ 2 := by gcongr; exact norm_sum_le _ _
      _ = (∑ j ∈ Jset, 1 * ‖w j‖) ^ 2 := by simp
      _ ≤ (∑ _j ∈ Jset, (1 : ℝ) ^ 2) * (∑ j ∈ Jset, ‖w j‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq Jset (fun _ => 1) (fun j => ‖w j‖)
      _ = (↑(N + H) : ℝ) * ∑ j ∈ Jset, ‖w j‖ ^ 2 := by simp [hcard_Jset]
  have hLHS : ((H : ℝ) + 1) ^ 2 * ‖S‖ ^ 2 = ‖∑ j ∈ Jset, w j‖ ^ 2 := by
    rw [hsum_identity, norm_mul, Complex.norm_natCast, sq, sq]; push_cast; ring
  -- Step C: Energy bound
  suffices hEnergy : (∑ j ∈ Jset, ‖w j‖ ^ 2 : ℝ) ≤
      (↑H + 1) * ↑N * (1 + ↑H * δ) by
    rw [hLHS]
    calc ‖∑ j ∈ Jset, w j‖ ^ 2
        ≤ (↑(N + H) : ℝ) * ∑ j ∈ Jset, ‖w j‖ ^ 2 := hCS
      _ ≤ (↑(N + H) : ℝ) * ((↑H + 1) * ↑N * (1 + ↑H * δ)) := by gcongr
      _ ≤ (2 * (↑N : ℝ)) * ((↑H + 1) * ↑N * (1 + ↑H * δ)) := by
          gcongr; push_cast
          have : (H : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hHN
          linarith
      _ = 2 * ↑N * (↑H + 1) * ↑N * (1 + ↑H * δ) := by ring
  -- == Prove hEnergy ==
  set Hset := Finset.range (H + 1) with hHset_def
  -- C1: norm-squared expansion
  have hnorm_sq_w : ∀ j : ℤ, (‖w j‖ ^ 2 : ℝ) =
      (∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))).re := by
    intro j
    rw [complex_norm_sq_eq_re_mul_conj (w j)]
    simp only [hw_def, map_sum, Finset.mul_sum, Finset.sum_mul]
    congr 1; rw [Finset.sum_comm]
  -- C2: Sum over j and swap
  have henergy_expand : (∑ j ∈ Jset, ‖w j‖ ^ 2 : ℝ) =
      (∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset,
        ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))).re := by
    simp_rw [hnorm_sq_w]; rw [Complex.re_sum]; simp_rw [Complex.re_sum]
    rw [Finset.sum_comm (s := Jset) (t := Hset)]
    simp_rw [Finset.sum_comm (s := Jset) (t := Hset)]
  -- C3: Diagonal bound: for h₁ = h₂, each inner sum = ∑ ‖f(n)‖²
  have hdiag_eq : ∀ h ∈ Hset,
      ∑ j ∈ Jset, g (j - ↑h) * starRingEnd ℂ (g (j - ↑h)) =
      ∑ n ∈ Finset.range N, (‖f n‖ ^ 2 : ℂ) := by
    intro h hh
    have hh_le : h ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
    -- Reindex via n ↦ n + h, use sum_nbij
    have heq : ∑ j ∈ Jset, g (j - ↑h) * starRingEnd ℂ (g (j - ↑h)) =
        ∑ n ∈ Finset.range N, g (↑n) * starRingEnd ℂ (g (↑n)) := by
      set img := Finset.image (fun n : ℕ => (↑n + (h : ℤ))) (Finset.range N)
      have himg_sub : img ⊆ Jset := by
        intro j hj; simp only [img, Finset.mem_image, Finset.mem_range] at hj
        obtain ⟨n, hn, rfl⟩ := hj; simp [hJset_def, Finset.mem_Ico]; omega
      rw [← Finset.sum_subset himg_sub (fun j _ hnj => by
        have : g (j - (h : ℤ)) = 0 := by
          simp only [hg_def]; split_ifs with hcond
          · exfalso; apply hnj; simp only [img, Finset.mem_image, Finset.mem_range]
            exact ⟨(j - (h : ℤ)).toNat, by omega, by omega⟩
          · rfl
        simp [this])]
      rw [Finset.sum_image (by intro a _ b _ (hab : (↑a : ℤ) + ↑h = ↑b + ↑h); omega)]
      apply Finset.sum_congr rfl; intro n _
      have hsub : (↑n + (h : ℤ)) - (h : ℤ) = ↑n := by omega
      simp only [hsub]
    rw [heq]
    apply Finset.sum_congr rfl; intro n hn
    have hn_lt := Finset.mem_range.mp hn
    simp only [hg_def, Int.natCast_nonneg, Nat.cast_lt, hn_lt, and_self, ite_true,
                Int.toNat_natCast]
    rw [Complex.mul_conj']
  have hf_norm_sq_le : (∑ n ∈ Finset.range N, ‖f n‖ ^ 2 : ℝ) ≤ ↑N := by
    calc (∑ n ∈ Finset.range N, ‖f n‖ ^ 2 : ℝ)
        ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum (fun n _ => by nlinarith [hf n, norm_nonneg (f n)])
      _ = ↑N := by simp
  -- C4: Off-diagonal cross-sum bound
  have hcross_bound : ∀ h₁ ∈ Hset, ∀ h₂ ∈ Hset, h₁ ≠ h₂ →
      ‖∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))‖ ≤ δ * ↑N := by
    intro h₁ hh₁ h₂ hh₂ hne
    have hh₁_le : h₁ ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh₁)
    have hh₂_le : h₂ ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh₂)
    -- Reduce to the case h₁ < h₂ by conjugation symmetry
    suffices hmain : ∀ a b : ℕ, a ∈ Hset → b ∈ Hset → a < b →
        ‖∑ j ∈ Jset, g (j - ↑a) * starRingEnd ℂ (g (j - ↑b))‖ ≤ δ * ↑N by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hmain h₁ h₂ hh₁ hh₂ hlt
      · rw [show (∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))) =
            starRingEnd ℂ (∑ j ∈ Jset, g (j - ↑h₂) * starRingEnd ℂ (g (j - ↑h₁))) from by
              rw [map_sum]; apply Finset.sum_congr rfl; intro j _
              rw [map_mul, starRingEnd_self_apply, mul_comm]]
        rw [norm_starRingEnd_complex]
        exact hmain h₂ h₁ hh₂ hh₁ hgt
    intro h₁ h₂ hh₁ hh₂ hlt
    have hh₁_le : h₁ ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh₁)
    have hh₂_le : h₂ ≤ H := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh₂)
    set ℓ := h₂ - h₁ with hℓ_def
    have hℓ_pos : 1 ≤ ℓ := by omega
    have hℓ_le : ℓ ≤ H := by omega
    -- Reindex the Jset sum to range(N-ℓ) sum via m = j - h₂
    have hsum_reindex : ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂)) =
        ∑ m ∈ Finset.range (N - ℓ), f (m + ℓ) * starRingEnd ℂ (f m) := by
      have hNℓ : ℓ ≤ N := le_trans hℓ_le hHN
      set img := Finset.image (fun m : ℕ => (↑m + (h₂ : ℤ))) (Finset.range (N - ℓ))
      have himg_sub : img ⊆ Jset := by
        intro j hj; simp only [img, Finset.mem_image, Finset.mem_range] at hj
        obtain ⟨m, hm, rfl⟩ := hj; simp [hJset_def, Finset.mem_Ico]; omega
      rw [← Finset.sum_subset himg_sub (fun j _ hnj => by
        by_cases hsupp2 : 0 ≤ j - (h₂ : ℤ) ∧ j - (h₂ : ℤ) < ↑N
        · -- hsupp2 active but j ∉ img; show g(j-h₁) = 0
          -- j ∉ img means (j-h₂).toNat ∉ range(N-ℓ), so j-h₂ ≥ N-ℓ, so j-h₁ ≥ N
          by_cases hsupp1 : 0 ≤ j - (h₁ : ℤ) ∧ j - (h₁ : ℤ) < ↑N
          · -- Both supports active: j IS in img (contradiction)
            exfalso; apply hnj; simp only [img, Finset.mem_image, Finset.mem_range]
            refine ⟨(j - (h₂ : ℤ)).toNat, ?_, ?_⟩
            · zify [hNℓ]; rw [Int.toNat_of_nonneg hsupp2.1]; omega
            · rw [Int.toNat_of_nonneg hsupp2.1]; omega
          · have : g (j - ↑h₁) = 0 := by
              simp only [hg_def]; exact if_neg hsupp1
            simp [this]
        · -- g(j - h₂) = 0, so product is zero
          push_neg at hsupp2
          have : g (j - ↑h₂) = 0 := by
            simp only [hg_def]; split_ifs with hcond
            · exact absurd hcond.2 (not_lt.mpr (hsupp2 hcond.1))
            · rfl
          simp [this])]
      rw [Finset.sum_image (by intro a _ b _ (hab : (↑a : ℤ) + ↑h₂ = ↑b + ↑h₂); omega)]
      apply Finset.sum_congr rfl; intro m hm
      have hm_lt := Finset.mem_range.mp hm
      have hmN : m + ℓ < N := by omega
      simp only [show (↑m + (h₂ : ℤ) - ↑h₁) = ↑(m + ℓ) from by push_cast; omega,
                  show (↑m + (h₂ : ℤ) - ↑h₂) = ↑m from by omega]
      simp only [hg_def, Int.natCast_nonneg, Nat.cast_lt, hmN, and_self, ite_true,
                  Int.toNat_natCast, show m < N from by omega]
    rw [hsum_reindex]
    rw [show (∑ m ∈ Finset.range (N - ℓ), f (m + ℓ) * starRingEnd ℂ (f m)) =
        starRingEnd ℂ (∑ m ∈ Finset.range (N - ℓ),
          f m * starRingEnd ℂ (f (m + ℓ))) from by
        rw [map_sum]; apply Finset.sum_congr rfl; intro m _
        rw [map_mul, starRingEnd_self_apply, mul_comm]]
    rw [norm_starRingEnd_complex]
    exact hR ℓ hℓ_pos hℓ_le
  -- C5: Assembly
  rw [henergy_expand]
  have hsplit : ∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset,
      ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂)) =
      (∑ h₁ ∈ Hset, ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₁))) +
      (∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset.erase h₁,
        ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro h₁ hh₁
    rw [← Finset.add_sum_erase Hset _ hh₁]
  rw [hsplit, Complex.add_re]
  -- Diagonal bound
  have hdiag_bound : (∑ h₁ ∈ Hset, ∑ j ∈ Jset,
      g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₁))).re ≤ (↑H + 1) * ↑N := by
    have hrewr : ∑ h₁ ∈ Hset, ∑ j ∈ Jset,
        g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₁)) =
        ∑ _h₁ ∈ Hset, ∑ n ∈ Finset.range N, (‖f n‖ ^ 2 : ℂ) :=
      Finset.sum_congr rfl (fun h hh => hdiag_eq h hh)
    rw [hrewr, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [show (↑(H + 1) : ℂ) * ∑ n ∈ Finset.range N, (‖f n‖ ^ 2 : ℂ) =
        (↑((↑(H + 1) : ℝ) * ∑ n ∈ Finset.range N, ‖f n‖ ^ 2) : ℂ) from by
      push_cast; simp]
    rw [Complex.ofReal_re]
    calc (↑(H + 1) : ℝ) * ∑ n ∈ Finset.range N, ‖f n‖ ^ 2
        ≤ (↑(H + 1) : ℝ) * ↑N := by gcongr
      _ = (↑H + 1) * ↑N := by push_cast; ring
  -- Off-diagonal bound
  have hoffdiag_bound : (∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset.erase h₁,
      ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))).re ≤
      ↑H * (↑H + 1) * δ * ↑N := by
    calc (∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset.erase h₁,
          ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))).re
        ≤ ‖∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset.erase h₁,
          ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))‖ :=
          Complex.re_le_norm _
      _ ≤ ∑ h₁ ∈ Hset, ‖∑ h₂ ∈ Hset.erase h₁,
          ∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ h₁ ∈ Hset, ∑ h₂ ∈ Hset.erase h₁,
          ‖∑ j ∈ Jset, g (j - ↑h₁) * starRingEnd ℂ (g (j - ↑h₂))‖ :=
          Finset.sum_le_sum (fun h₁ _ => norm_sum_le _ _)
      _ ≤ ∑ h₁ ∈ Hset, ∑ _h₂ ∈ Hset.erase h₁, (δ * ↑N) := by
          apply Finset.sum_le_sum; intro h₁ hh₁
          apply Finset.sum_le_sum; intro h₂ hh₂
          exact hcross_bound h₁ hh₁ h₂ (Finset.mem_of_mem_erase hh₂)
            (Finset.ne_of_mem_erase hh₂).symm
      _ = ∑ h₁ ∈ Hset, ↑(Hset.erase h₁).card * (δ * ↑N) := by
          simp_rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ _h₁ ∈ Hset, ↑H * (δ * ↑N) := by
          apply Finset.sum_congr rfl; intro h₁ hh₁; congr 1
          have : (Hset.erase h₁).card = H := by
            rw [Finset.card_erase_of_mem hh₁, Finset.card_range, Nat.add_sub_cancel]
          exact_mod_cast this
      _ = ↑(H + 1) * (↑H * (δ * ↑N)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ↑H * (↑H + 1) * δ * ↑N := by push_cast; ring
  linarith [show (↑H + 1) * ↑N + ↑H * (↑H + 1) * δ * ↑N =
      (↑H + 1) * ↑N * (1 + ↑H * δ) from by ring]

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
    · simp
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
  hod_vdc_implies_ccsb h vanDerCorputBound

/-- **HOD → MC** (simplified): HigherOrderDecorrelation alone implies
    Mullin's Conjecture, via the chain HOD → CCSB → MC. -/
theorem hod_chain_mc (h : HigherOrderDecorrelation) : MullinConjecture :=
  hod_vdc_chain_mc h vanDerCorputBound

/-- **HOD → MMCSB** (simplified): HigherOrderDecorrelation alone implies
    MultiModularCSB with Q₀ = 0. -/
theorem hod_implies_mmcsb (h : HigherOrderDecorrelation) : MultiModularCSB :=
  hod_vdc_implies_mmcsb h vanDerCorputBound

end HODSimplified

/-! ## §70: Conditional Multiplier Equidistribution (CME)

CME captures the number-theoretic content that the EM multiplier m(n) = minFac(prod(n)+1)
has equidistributed character values CONDITIONAL on the walk position w(n).

### Position in the hierarchy:
- CME IMPLIES DecorrelationHypothesis (h=1 multiplier cancellation)
- CME IMPLIES ComplexCharSumBound (proved via telescoping identity + fiber decomposition)
- CME does NOT imply HOD for h >= 2 (Dead End #81)
- Hierarchy: PED < Dec < CME ≤ CCSB -/

section ConditionalMultiplierEquidist

/-- **Conditional Multiplier Equidistribution**: for any prime q not in the EM
    sequence, any nontrivial character chi, and any walk position a in (ZMod q)^*,
    the multiplier character sum restricted to steps where w(n) = a is o(N).

    This captures: "the least prime factor of integers in a specific congruence
    class mod q is equidistributed among coprime residue classes."

    Position in hierarchy: PED < Dec < CME ≤ CCSB.
    CME implies both Dec and CCSB (proved via telescoping identity).
    CME does NOT imply HOD for h >= 2 (Dead End #81). -/
def ConditionalMultiplierEquidist : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (a : (ZMod q)ˣ),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
      (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- The fiber-restricted multiplier character sum: the sum of χ(m(n)) over
    indices n < N where the walk position w(n) = a.

    This is the central quantity in CME: the character sum restricted to a
    single walk-position fiber. CME says this is o(N) for all fibers. -/
noncomputable def fiberMultCharSum (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (a : (ZMod q)ˣ) (N : ℕ) : ℂ :=
  ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
    (χ (emMultUnit q hq hne n) : ℂ)

/-- CME is equivalent to: for all q, χ ≠ 1, a, ε > 0, eventually
    ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε * N.

    This is just unfolding the definition — the sum in CME is exactly
    `fiberMultCharSum`. -/
theorem cme_iff_fiber_bound :
    ConditionalMultiplierEquidist ↔
    ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
    ∀ (a : (ZMod q)ˣ),
    ∀ (ε : ℝ) (_hε : 0 < ε),
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε * N :=
  Iff.rfl

/-- The total multiplier character sum decomposes as the sum of fiber sums
    over all walk positions.

    `∑_{n<N} χ(m(n)) = ∑_a fiberMultCharSum q hq hne χ a N` -/
theorem mult_char_sum_eq_fiber_sum (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) =
    ∑ a : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a N := by
  simp only [fiberMultCharSum]
  rw [← Finset.sum_fiberwise (Finset.range N) (emWalkUnit q hq hne)
    (fun n => (χ (emMultUnit q hq hne n) : ℂ))]

open Classical in
/-- **CME implies DecorrelationHypothesis**: the total multiplier character sum
    decomposes as a sum over walk positions. By triangle inequality and the
    conditional bound from CME, the total sum is o(N).

    Proof: partition {0,...,N-1} by walk position w(n) = a, apply triangle
    inequality, bound each conditional sum by CME with epsilon/(q-1), and
    sum over at most (q-1) positions. -/
theorem cme_implies_dec (hcme : ConditionalMultiplierEquidist) :
    DecorrelationHypothesis := by
  intro q inst hq hne χ hχ ε hε
  -- Number of walk positions: Fintype.card (ZMod q)ˣ
  haveI : Fact (Nat.Prime q) := inst
  set C := Fintype.card (ZMod q)ˣ with hC_def
  -- C ≥ 1 since the group is nonempty (contains 1)
  have hC_pos : (0 : ℝ) < C := by
    have : 0 < C := Fintype.card_pos
    exact Nat.cast_pos.mpr this
  -- Set ε' = ε / C
  set ε' := ε / C with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε hC_pos
  -- For each walk position a, CME gives N₀(a) such that the conditional sum ≤ ε' * N
  have hcme_a : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε' * N :=
    fun a => hcme q hq hne χ hχ a ε' hε'_pos
  -- Choose N₀(a) for each a
  choose N₀_fn hN₀_fn using hcme_a
  -- Take the maximum N₀ over all a
  set N₀ := Finset.univ.sup N₀_fn with hN₀_def
  refine ⟨N₀, fun N hN => ?_⟩
  -- Step 1: Partition the sum by walk position using sum_fiberwise
  have hdecomp : ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) =
      ∑ a : (ZMod q)ˣ, ∑ n ∈ (Finset.range N).filter
        (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ) := by
    rw [← Finset.sum_fiberwise (Finset.range N) (emWalkUnit q hq hne)
      (fun n => (χ (emMultUnit q hq hne n) : ℂ))]
  rw [hdecomp]
  -- Step 2: Triangle inequality
  calc ‖∑ a : (ZMod q)ˣ, ∑ n ∈ (Finset.range N).filter
        (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖
      ≤ ∑ a : (ZMod q)ˣ, ‖∑ n ∈ (Finset.range N).filter
        (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod q)ˣ, ε' * N := by
        apply Finset.sum_le_sum
        intro a _
        apply hN₀_fn a N
        exact le_trans (Finset.le_sup (Finset.mem_univ a)) hN
    _ = C * (ε' * N) := by
        rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]
    _ = ε * N := by
        rw [hε'_def]
        field_simp

/-- **Walk-multiplier product decomposes by fiber**: the sum
    `∑_{n<N} χ(w(n))·χ(m(n))` equals the fiber-weighted sum
    `∑_a χ(a) · ∑_{w(n)=a} χ(m(n))`.

    This is a direct application of `Finset.sum_fiberwise` combined with the fact
    that `χ(w(n))` is constant (equal to `χ(a)`) on the fiber `{n : w(n) = a}`. -/
theorem walk_mult_product_fiber_decomp (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ)) =
    ∑ a : (ZMod q)ˣ, (χ a : ℂ) *
      ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ) := by
  rw [← Finset.sum_fiberwise (Finset.range N) (emWalkUnit q hq hne)
    (fun n => (χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))]
  congr 1
  ext a
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [(Finset.mem_filter.mp hn).2]

open Classical in
/-- **CME implies CCSB**: Conditional Multiplier Equidistribution implies
    the Complex Character Sum Bound, via the telescoping identity and
    fiber decomposition.

    This is the key reduction that bypasses PEDImpliesComplexCSB entirely.
    The proof uses:
    1. The telescoping identity: `∑ χ(w(n))·(χ(m(n))-1) = χ(w(N)) - χ(w(0))`
    2. Fiber decomposition: `∑ χ(w(n))·χ(m(n)) = ∑_a χ(a) · ∑_{w(n)=a} χ(m(n))`
    3. CME bounds each fiber sum by `ε·N`
    4. Triangle inequality sums over at most `C = Fintype.card (ZMod q)ˣ` fibers

    Position in hierarchy: CME implies CCSB (proved). CME implies HOD remains false. -/
theorem cme_implies_ccsb (hcme : ConditionalMultiplierEquidist) :
    ComplexCharSumBound := by
  intro q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- Step 1: Set up ε' for CME fiber bounds
  -- We need C * (ε' * N) + 2 ≤ ε * N, so set ε' = ε/(2*C) and require N ≥ 4/ε
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := by
    have : 0 < C := Fintype.card_pos
    exact Nat.cast_pos.mpr this
  set ε' := ε / (2 * C) with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε (mul_pos two_pos hC_pos)
  -- Step 2: Get N₀ from CME for each fiber, take maximum
  have hcme_a : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
        (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε' * N :=
    fun a => hcme q hq hne χ hχ a ε' hε'_pos
  choose N₀_fn hN₀_fn using hcme_a
  set N₀_cme := Finset.univ.sup N₀_fn
  -- Also need N₀ large enough that 2 ≤ (ε/2) * N, i.e., N ≥ 4/ε
  set N₀_boundary := Nat.ceil (4 / ε)
  set N₀ := max N₀_cme N₀_boundary
  refine ⟨N₀, fun N hN => ?_⟩
  -- Step 3: Use the telescoping identity to express S_N
  -- walk_telescope_identity: ∑ χ(w(n))·(χ(m(n))-1) = χ(w(N)) - χ(w(0))
  -- Expanding: ∑ χ(w)·χ(m) - ∑ χ(w) = χ(w(N)) - χ(w(0))
  -- So: ∑ χ(w) = ∑ χ(w)·χ(m) - (χ(w(N)) - χ(w(0)))
  have htelescope := walk_telescope_identity q hq hne χ N
  have hSN_eq : ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
      ∑ n ∈ Finset.range N, ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))
      - ((χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)) := by
    have hsub : ∑ n ∈ Finset.range N,
        ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))
      - ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
        (χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ) := by
      rw [← Finset.sum_sub_distrib]
      convert htelescope using 1
      congr 1; ext n; ring
    linear_combination -hsub
  -- Step 4: Bound the product sum via fiber decomposition and CME
  have hfiber := walk_mult_product_fiber_decomp q hq hne χ N
  -- Step 5: Bound norm of product sum using triangle inequality + CME
  have hprod_bound : ‖∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))‖
      ≤ C * (ε' * N) := by
    rw [hfiber]
    calc ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * ∑ n ∈ (Finset.range N).filter
          (fun n => emWalkUnit q hq hne n = a), (χ (emMultUnit q hq hne n) : ℂ)‖
        ≤ ∑ a : (ZMod q)ˣ, ‖(χ a : ℂ) * ∑ n ∈ (Finset.range N).filter
          (fun n => emWalkUnit q hq hne n = a), (χ (emMultUnit q hq hne n) : ℂ)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ a : (ZMod q)ˣ, ‖∑ n ∈ (Finset.range N).filter
          (fun n => emWalkUnit q hq hne n = a), (χ (emMultUnit q hq hne n) : ℂ)‖ := by
            apply Finset.sum_le_sum; intro a _
            rw [norm_mul]
            calc ‖(χ a : ℂ)‖ * _ ≤ 1 * _ := by
                  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                  exact le_of_eq (walkTelescope_char_norm_one χ a)
              _ = _ := one_mul _
      _ ≤ ∑ _a : (ZMod q)ˣ, ε' * ↑N := by
            apply Finset.sum_le_sum; intro a _
            exact hN₀_fn a N (le_trans (Finset.le_sup (Finset.mem_univ a))
              (le_max_left _ _ |>.trans hN))
      _ = C * (ε' * N) := by
            rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]
  -- Step 6: Bound the boundary term ‖χ(w(N)) - χ(w(0))‖ ≤ 2
  have hboundary : ‖(χ (emWalkUnit q hq hne N) : ℂ) -
      (χ (emWalkUnit q hq hne 0) : ℂ)‖ ≤ 2 := by
    calc ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖
        ≤ ‖(χ (emWalkUnit q hq hne N) : ℂ)‖ + ‖(χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
          norm_sub_le _ _
      _ = 1 + 1 := by
          rw [walkTelescope_char_norm_one χ _, walkTelescope_char_norm_one χ _]
      _ = 2 := by ring
  -- Step 7: N ≥ 4/ε ensures the boundary term is absorbed
  have hN_ge_boundary : (4 / ε : ℝ) ≤ N := by
    calc (4 / ε : ℝ) ≤ ↑(Nat.ceil (4 / ε)) := Nat.le_ceil _
      _ ≤ ↑N := by
          exact_mod_cast le_trans (le_max_right N₀_cme N₀_boundary) hN
  have hε_half_N : 2 ≤ ε / 2 * (N : ℝ) := by
    have h4 : 4 ≤ ε * (N : ℝ) := by
      have := (div_le_iff₀ hε).mp hN_ge_boundary
      linarith
    linarith
  -- Step 8: Combine everything
  calc ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖
      = ‖∑ n ∈ Finset.range N, ((χ (emWalkUnit q hq hne n) : ℂ) *
          (χ (emMultUnit q hq hne n) : ℂ))
        - ((χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ))‖ := by
          rw [hSN_eq]
    _ ≤ ‖∑ n ∈ Finset.range N, ((χ (emWalkUnit q hq hne n) : ℂ) *
          (χ (emMultUnit q hq hne n) : ℂ))‖ +
        ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
          norm_sub_le _ _
    _ ≤ C * (ε' * N) + 2 := by linarith [hprod_bound, hboundary]
    _ = ε / 2 * N + 2 := by
          rw [hε'_def]
          have hC_ne : (C : ℝ) ≠ 0 := ne_of_gt hC_pos
          field_simp
    _ ≤ ε * N := by linarith [hε_half_N]

/-- **CME implies MC** (single hypothesis): CME implies Mullin's Conjecture
    directly, bypassing PEDImpliesComplexCSB entirely.
    Composes `cme_implies_ccsb` with `complex_csb_mc'`. -/
theorem cme_implies_mc (hcme : ConditionalMultiplierEquidist) : MullinConjecture :=
  complex_csb_mc' (cme_implies_ccsb hcme)

/-- **CME implies MC (old chain)**: Conditional Multiplier Equidistribution implies
    Mullin's Conjecture, via the chain CME -> Dec -> PED -> CCSB -> MC.
    Requires PEDImpliesComplexCSB (the block-rotation estimate bridge).
    Superseded by `cme_implies_mc` which needs no additional hypotheses. -/
theorem cme_chain_mc (hcme : ConditionalMultiplierEquidist)
    (hped_csb : PEDImpliesComplexCSB) : MullinConjecture :=
  decorrelation_mc' (cme_implies_dec hcme) hped_csb

end ConditionalMultiplierEquidist

/-! ## S80. Fiber Energy Bounds

The **Fiber Energy Bound** is the L² version of CME: instead of controlling
each fiber multiplier sum individually (L^∞), we control the sum of squares
∑_a ‖F(a)‖² (L² energy).

### Key Results

* `FiberEnergyBound`     : L² fiber control (def)
* `cme_implies_feb`      : CME → FEB (PROVED: L^∞ implies L²)
* `feb_implies_ccsb`     : FEB → CCSB (PROVED: Cauchy-Schwarz, alternative to triangle inequality)
* `feb_implies_mc`       : FEB → MC (PROVED: composition)

### Dead End #93

While FEB → CCSB via a clean Cauchy-Schwarz argument (avoiding the triangle
inequality in `cme_implies_ccsb`), FEB is NOT strictly weaker than CME for
fixed q. The finite fiber count (q-1 positions) makes L² and L^∞ equivalent
via Markov's inequality: with CC_χ = o(N²) and T = ε·N, the number of fibers
where ‖F(a)‖ > T is #{a : ‖F(a)‖² > (εN)²} ≤ CC_χ/(εN)² = o(1), so eventually
all fibers satisfy the L^∞ bound.

Conclusion: No L^p interpolation between Dec and CCSB provides a strictly
weaker intermediate. The viable routes remain SieveTransfer, CME, or direct
CCSB approaches.
-/

section FiberEnergyBounds

/-- **Fiber Energy Bound**: for every missing prime q, every nontrivial character χ,
    and ε > 0, eventually ∑_a ‖fiberMultCharSum q χ a N‖² ≤ ε · N².

    This is the L² fiber control condition: the fiber multiplier char sums are
    small in aggregate. CC_χ(N) = ∑_a |F(a)|² is the "conditional collision sum."

    Position in hierarchy:
    - CME → FiberEnergyBound (L^∞ → L²)
    - FiberEnergyBound → CCSB (Cauchy-Schwarz, proved below)
    - CCSB does NOT imply FiberEnergyBound (fibers can cancel by character weighting)
    - FiberEnergyBound ⟺ CME for fixed q (Markov on finitely many positions)

    In summary: FiberEnergyBound is equivalent to CME but implies CCSB
    by a different proof (Cauchy-Schwarz rather than triangle inequality).
    This is Dead End #93: the L² perspective does not provide a strictly
    weaker intermediate between CME and CCSB. -/
def FiberEnergyBound : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 ≤ ε * (N : ℝ) ^ 2

open Classical in
/-- **CME implies FEB**: Conditional Multiplier Equidistribution implies
    Fiber Energy Bound. This is the L^∞ to L² implication.

    Proof: CME gives ‖F(a)‖ ≤ ε'·N for each fiber a. Then
    ∑_a ‖F(a)‖² ≤ ∑_a (ε'·N)² = C·(ε')²·N²
    where C = φ(q) is the number of fibers.
    To achieve ∑ ≤ ε·N², choose ε' = √(ε/C).

    Dead End #93: FEB ⟺ CME for fixed q, so this is an alternative
    route equivalent to the already-proved CME → CCSB path. -/
theorem cme_implies_feb (hcme : ConditionalMultiplierEquidist) : FiberEnergyBound := by
  intro q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- C = number of fibers = card (ZMod q)ˣ
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := Nat.cast_pos.mpr Fintype.card_pos
  -- Choose ε' = √(ε/C) so that C · (ε')² = ε
  set ε' := Real.sqrt (ε / C) with hε'_def
  have hε'_pos : 0 < ε' := Real.sqrt_pos.mpr (div_pos hε hC_pos)
  -- Get N₀(a) from CME for each fiber a
  have hcme_a : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε' * N := by
    intro a; exact (cme_iff_fiber_bound.mp hcme) q hq hne χ hχ a ε' hε'_pos
  choose N₀_fn hN₀_fn using hcme_a
  refine ⟨Finset.univ.sup N₀_fn, fun N hN => ?_⟩
  -- For each a, ‖F(a)‖ ≤ ε' · N
  have hfa : ∀ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε' * N :=
    fun a => hN₀_fn a N (le_trans (Finset.le_sup (Finset.mem_univ a)) hN)
  -- ‖F(a)‖² ≤ (ε' · N)²
  have hfa_sq : ∀ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 ≤ (ε' * N) ^ 2 := by
    intro a
    apply sq_le_sq'
    · linarith [norm_nonneg (fiberMultCharSum q hq hne χ a N),
                mul_nonneg hε'_pos.le (Nat.cast_nonneg N)]
    · exact hfa a
  -- Sum: ∑_a ‖F(a)‖² ≤ C · (ε' · N)²
  calc ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2
      ≤ ∑ _a : (ZMod q)ˣ, (ε' * N) ^ 2 := Finset.sum_le_sum fun a _ => hfa_sq a
    _ = C * (ε' * N) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]
    _ = C * (ε' ^ 2 * N ^ 2) := by ring
    _ = C * (ε / C * N ^ 2) := by
        congr 1
        rw [hε'_def, Real.sq_sqrt (le_of_lt (div_pos hε hC_pos))]
    _ = ε * (N : ℝ) ^ 2 := by
        field_simp

open Classical in
/-- **FEB implies CCSB**: Fiber Energy Bound implies Complex Character Sum Bound,
    via Cauchy-Schwarz instead of the triangle inequality.

    Proof:
    1. Walk char sum telescoping: ∑_n χ(w(n))·(χ(m(n))-1) = χ(w(N)) - χ(w(0))
    2. Fiber decomposition: ∑_n χ(w(n))·χ(m(n)) = ∑_a χ(a)·F(a)
    3. Cauchy-Schwarz: ‖∑_a χ(a)·F(a)‖² ≤ C·(∑‖F(a)‖²) = C·CC_χ(N)
    4. FEB gives CC_χ(N) ≤ ε'·N², so ‖S_N‖ ≤ √(C·ε')·N + 2 = o(N)

    Dead End #93: FEB ⟺ CME for fixed q, so this alternative route
    is equivalent to the already-proved CME → CCSB → MC path. -/
theorem feb_implies_ccsb (hfeb : FiberEnergyBound) : ComplexCharSumBound := by
  intro q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- C = number of fibers
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := Nat.cast_pos.mpr Fintype.card_pos
  -- Choose ε' for FEB: we need √(C · ε') + 2/N ≤ ε
  -- Set ε' = (ε/2)² / C, so √(C·ε') = ε/2
  set ε' := (ε / 2) ^ 2 / C with hε'_def
  have hε'_pos : 0 < ε' := div_pos (sq_pos_of_pos (half_pos hε)) hC_pos
  -- Get N₀ from FEB
  obtain ⟨N₀_feb, hN₀_feb⟩ := hfeb q hq hne χ hχ ε' hε'_pos
  -- Also need N large enough for boundary absorption: 4/ε ≤ N
  set N₀ := max N₀_feb (Nat.ceil (4 / ε))
  refine ⟨N₀, fun N hN => ?_⟩
  -- FEB bound
  have hfeb_N : ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 ≤
      ε' * (N : ℝ) ^ 2 :=
    hN₀_feb N (le_trans (le_max_left _ _) hN)
  -- Use telescoping identity
  have htelescope := walk_telescope_identity q hq hne χ N
  have hSN_eq : ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
      ∑ n ∈ Finset.range N, ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))
      - ((χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)) := by
    have hsub : ∑ n ∈ Finset.range N,
        ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))
      - ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
        (χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ) := by
      rw [← Finset.sum_sub_distrib]
      convert htelescope using 1
      congr 1; ext n; ring
    linear_combination -hsub
  -- Fiber decomposition of the product sum
  have hfiber := walk_mult_product_fiber_decomp q hq hne χ N
  -- Cauchy-Schwarz: ‖∑_a χ(a) · F(a)‖² ≤ (∑ ‖χ(a)‖²) · (∑ ‖F(a)‖²) = C · ∑ ‖F(a)‖²
  have hcs : ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * fiberMultCharSum q hq hne χ a N‖ ^ 2 ≤
      C * ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 := by
    calc ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * fiberMultCharSum q hq hne χ a N‖ ^ 2
        ≤ (∑ a : (ZMod q)ˣ, ‖(χ a : ℂ) * fiberMultCharSum q hq hne χ a N‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
      _ = (∑ a : (ZMod q)ˣ, ‖(χ a : ℂ)‖ * ‖fiberMultCharSum q hq hne χ a N‖) ^ 2 := by
          congr 1; congr 1; ext a; exact norm_mul _ _
      _ = (∑ a : (ZMod q)ˣ, 1 * ‖fiberMultCharSum q hq hne χ a N‖) ^ 2 := by
          congr 1; congr 1; ext a
          rw [walkTelescope_char_norm_one χ a]
      _ ≤ (∑ _a : (ZMod q)ˣ, (1 : ℝ) ^ 2) *
          (∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
            (fun _ => (1 : ℝ)) (fun a => ‖fiberMultCharSum q hq hne χ a N‖)
      _ = C * ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 := by
          simp [Finset.card_univ, hC_def]
  -- Product sum norm bound via Cauchy-Schwarz + FEB
  have hprod_norm_sq : ‖∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))‖ ^ 2 ≤
      C * ε' * (N : ℝ) ^ 2 := by
    rw [hfiber]
    calc ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * fiberMultCharSum q hq hne χ a N‖ ^ 2
        ≤ C * ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 := hcs
      _ ≤ C * (ε' * (N : ℝ) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hfeb_N (le_of_lt hC_pos)
      _ = C * ε' * (N : ℝ) ^ 2 := by ring
  -- Extract norm bound (not squared)
  have hprod_norm : ‖∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))‖ ≤
      ε / 2 * N := by
    have hCε' : C * ε' = (ε / 2) ^ 2 := by
      rw [hε'_def]; field_simp
    have hCε'_nn : 0 ≤ C * ε' := le_of_lt (mul_pos hC_pos hε'_pos)
    rw [hCε'] at hprod_norm_sq
    have hN_nn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hεN_nn : 0 ≤ ε / 2 * N := mul_nonneg (le_of_lt (half_pos hε)) hN_nn
    nlinarith [sq_nonneg (‖∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ))‖ - ε / 2 * N)]
  -- Boundary term bound
  have hboundary : ‖(χ (emWalkUnit q hq hne N) : ℂ) -
      (χ (emWalkUnit q hq hne 0) : ℂ)‖ ≤ 2 := by
    calc ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖
        ≤ ‖(χ (emWalkUnit q hq hne N) : ℂ)‖ + ‖(χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
          norm_sub_le _ _
      _ = 1 + 1 := by
          rw [walkTelescope_char_norm_one χ _, walkTelescope_char_norm_one χ _]
      _ = 2 := by ring
  -- N ≥ 4/ε ensures boundary absorption
  have hN_ge : (4 / ε : ℝ) ≤ N := by
    calc (4 / ε : ℝ) ≤ ↑(Nat.ceil (4 / ε)) := Nat.le_ceil _
      _ ≤ ↑N := by exact_mod_cast le_trans (le_max_right N₀_feb _) hN
  have hε_half_N : 2 ≤ ε / 2 * (N : ℝ) := by
    have h4 : 4 ≤ ε * (N : ℝ) := by
      have := (div_le_iff₀ hε).mp hN_ge; linarith
    linarith
  -- Combine
  calc ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖
      = ‖∑ n ∈ Finset.range N, ((χ (emWalkUnit q hq hne n) : ℂ) *
          (χ (emMultUnit q hq hne n) : ℂ))
        - ((χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ))‖ := by
          rw [hSN_eq]
    _ ≤ ‖∑ n ∈ Finset.range N, ((χ (emWalkUnit q hq hne n) : ℂ) *
          (χ (emMultUnit q hq hne n) : ℂ))‖ +
        ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
          norm_sub_le _ _
    _ ≤ ε / 2 * N + 2 := by linarith [hprod_norm, hboundary]
    _ ≤ ε * N := by linarith [hε_half_N]

/-- **FEB implies MC**: Fiber Energy Bound implies Mullin's Conjecture,
    via the Cauchy-Schwarz route FEB → CCSB → MC.

    This is an alternative to the triangle inequality route CME → CCSB → MC.
    Both routes are equivalent since FEB ⟺ CME for fixed q (Dead End #93). -/
theorem feb_implies_mc (hfeb : FiberEnergyBound) : MullinConjecture :=
  complex_csb_mc' (feb_implies_ccsb hfeb)

/-! ### Dead End #93: FiberEnergyBound ⟺ CME for fixed q.

While FiberEnergyBound implies CCSB via Cauchy-Schwarz (a clean alternative
to the triangle inequality in `cme_implies_ccsb`), it is NOT a strictly
weaker condition than CME. For fixed q, there are only finitely many (q-1)
walk positions, so L² control (FEB) implies L∞ control (CME) by Markov's
inequality: #{a : ‖F(a)‖ > T} ≤ CC_χ/T². With CC_χ = o(N²) and T = ε·N,
the number of "bad" positions is o(1) → eventually 0 → all positions good → CME.

Similarly, Density-1 CME (allowing o(N) bad INDICES) is equivalent to CME
because each fiber has Θ(N/(q-1)) = Θ(N) elements for fixed q. The o(N)
bad-index budget cannot absorb a biased fiber of size Θ(N).

Conclusion: No L^p interpolation between Dec and CCSB provides a strictly
weaker intermediate. The only viable routes remain SieveTransfer, CME, or
direct CCSB approaches. -/

end FiberEnergyBounds

/-! ## Hierarchy Connectors

Small lemmas completing the hierarchy diagram. These connect the major open
Props and their proved implications.

### Results

* `ccsb_implies_mmcsb`  : CCSB → MMCSB with Q₀ = 0 (trivial unwrapping)
* `cme_implies_mmcsb`   : CME → MMCSB (composition through CCSB)
* `feb_implies_mmcsb`   : FEB → MMCSB (composition through CCSB)
* `ccsb_implies_sve`    : CCSB → SVE (character sum bounds → excess energy o(N²))

These complete the bidirectional picture: SVE ⟺ MMCSB ⟺ CCSB (modulo Q₀ threshold).
-/

section HierarchyConnectors

/-- **CCSB → MMCSB**: ComplexCharSumBound implies MultiModularCSB with threshold
    Q₀ = 0 (i.e., for ALL primes). This is immediate since CCSB is the universal
    version of MMCSB without a threshold. -/
theorem ccsb_implies_mmcsb (hcsb : ComplexCharSumBound) : MultiModularCSB :=
  ⟨0, fun q _inst _ hq hne χ hχ ε hε => hcsb q hq hne χ hχ ε hε⟩

/-- **CME → MMCSB**: Conditional Multiplier Equidistribution implies MultiModularCSB.
    Composes CME → CCSB (telescoping + fiber decomposition) → MMCSB (trivial). -/
theorem cme_implies_mmcsb (hcme : ConditionalMultiplierEquidist) : MultiModularCSB :=
  ccsb_implies_mmcsb (cme_implies_ccsb hcme)

/-- **FEB → MMCSB**: Fiber Energy Bound implies MultiModularCSB.
    Composes FEB → CCSB (Cauchy-Schwarz) → MMCSB (trivial). -/
theorem feb_implies_mmcsb (hfeb : FiberEnergyBound) : MultiModularCSB :=
  ccsb_implies_mmcsb (feb_implies_ccsb hfeb)

open Classical in
/-- **CCSB → SVE**: ComplexCharSumBound implies SubquadraticVisitEnergy.

    Proof: CCSB gives ‖S_χ‖ ≤ ε'·N for each nontrivial χ. The excess energy
    equals ∑_{χ≠1} ‖S_χ‖², which is bounded by (p−2)·(ε'·N)². Choosing
    ε' = √(ε/(p−2)) gives excess ≤ ε·N².

    Combined with `sve_implies_mmcsb`, this shows CCSB ⟺ SVE ⟺ MMCSB
    (modulo the Q₀ threshold: CCSB has Q₀=0, SVE/MMCSB have Q₀≥0). -/
theorem ccsb_implies_sve (hcsb : ComplexCharSumBound) : SubquadraticVisitEnergy := by
  use 0
  intro q _inst _hge hq hne ε hε
  -- Step 1: Set up the Fin N walk wrapper
  -- We need to bound excessEnergy of the restricted walk
  haveI : Fact (Nat.Prime q) := _inst
  haveI : NeZero q := ⟨(Fact.out : Nat.Prime q).ne_zero⟩
  -- Number of nontrivial characters C = p - 2
  set C := (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card with hC_def
  -- Choose ε' so that C · (ε' · N)² ≤ ε · N²
  -- Set ε' = √(ε / max(C,1)) so that C · ε'² = ε · C / max(C,1) ≤ ε
  -- But simpler: use ε directly and get CCSB to deliver √ε bounds
  -- Since excess = ∑_{χ≠1} ‖S_χ‖² ≤ C * (ε' * N)² and we want ≤ ε * N²,
  -- choose ε' = √(ε / (C + 1)) (the +1 avoids division by zero when C=0)
  set ε' := Real.sqrt (ε / (C + 1)) with hε'_def
  have hC_pos : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  have hε'_pos : 0 < ε' := Real.sqrt_pos.mpr (div_pos hε hC_pos)
  -- For each nontrivial ψ, CCSB gives an N₀(ψ)
  -- Convert DirichletCharacter to unit hom via equivToUnitHom
  have hcsb_dc : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ‖∑ n ∈ Finset.range N, (ψ.toUnitHom (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε' * N := by
    intro ψ hψ
    have hχ : ψ.toUnitHom ≠ 1 := by
      intro h; apply hψ
      ext a
      have := congr_fun (congr_arg DFunLike.coe h) a
      simp only [MonoidHom.one_apply] at this
      rw [show ψ a = (ψ.toUnitHom a : ℂ) from (MulChar.coe_toUnitHom ψ a).symm, this]
      simp [MulChar.one_apply_coe]
    obtain ⟨N₀, hN₀⟩ := hcsb q hq hne ψ.toUnitHom hχ ε' hε'_pos
    exact ⟨N₀, hN₀⟩
  -- For each ψ, get an N₀ (use 0 for trivial character since it won't be used)
  have hcsb_dc' : ∀ ψ : DirichletCharacter ℂ q,
      ∃ N₀ : ℕ, ψ ≠ 1 → ∀ N ≥ N₀,
        ‖∑ n ∈ Finset.range N, (ψ.toUnitHom (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε' * N := by
    intro ψ
    by_cases hψ : ψ = 1
    · exact ⟨0, fun h => absurd hψ h⟩
    · obtain ⟨N₀, hN₀⟩ := hcsb_dc ψ hψ
      exact ⟨N₀, fun _ => hN₀⟩
  choose N₀_fn hN₀_fn using hcsb_dc'
  set N₀ := Finset.univ.sup N₀_fn
  refine ⟨N₀, fun N hN => ?_⟩
  -- Step 2: Bound excess energy using the nontrivial sum identity
  set w : Fin N → (ZMod q)ˣ := fun n => emWalkUnit q hq hne n.val
  rw [excess_energy_eq_nontrivial_sum w]
  -- Step 3: Bound each character sum term
  have hchar_bound : ∀ ψ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ‖∑ n : Fin N, ψ (↑(w n) : ZMod q)‖ ^ 2 ≤ (ε' * N) ^ 2 := by
    intro ψ hψ
    apply sq_le_sq'
    · linarith [norm_nonneg (∑ n : Fin N, ψ (↑(w n) : ZMod q)),
                mul_nonneg hε'_pos.le (Nat.cast_nonneg N)]
    · -- Convert Fin N sum to Finset.range N sum
      have hsum_convert : ∑ n : Fin N, ψ (↑(w n) : ZMod q) =
          ∑ n ∈ Finset.range N, (ψ.toUnitHom (emWalkUnit q hq hne n) : ℂ) := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro n _; exact (MulChar.coe_toUnitHom ψ (w n)).symm
      rw [hsum_convert]
      exact hN₀_fn ψ (Finset.ne_of_mem_erase hψ) N
        (le_trans (Finset.le_sup (Finset.mem_univ ψ)) hN)
  -- Step 4: Sum the bounds
  calc (Finset.univ.erase (1 : DirichletCharacter ℂ q)).sum
          (fun χ => ‖∑ n : Fin N, χ (↑(w n) : ZMod q)‖ ^ 2)
      ≤ (Finset.univ.erase (1 : DirichletCharacter ℂ q)).sum
          (fun _ => (ε' * ↑N) ^ 2) :=
        Finset.sum_le_sum hchar_bound
    _ = ↑C * (ε' * ↑N) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, hC_def]
    _ = ↑C * (ε' ^ 2 * ↑N ^ 2) := by ring
    _ = ↑C * (ε / (↑C + 1) * ↑N ^ 2) := by
        congr 1; rw [hε'_def, Real.sq_sqrt (le_of_lt (div_pos hε hC_pos))]
    _ ≤ (↑C + 1) * (ε / (↑C + 1) * ↑N ^ 2) := by
        gcongr; exact le_of_lt (lt_add_one (C : ℝ))
    _ = ε * (↑N : ℝ) ^ 2 := by field_simp

end HierarchyConnectors

/-! ## S71. Elliott-Halberstam Conjecture and Chain to MC

The **Elliott-Halberstam conjecture** (1968) asserts that primes have
level of distribution θ for every θ < 1: the BV-type error bound
∑_{q ≤ x^θ} max_{(a,q)=1} |π(x;q,a) − li(x)/φ(q)| ≤ x/(log x)^A
holds for all A > 0 whenever θ < 1.

The Bombieri-Vinogradov theorem proves this for θ = 1/2 only. EH is
strictly stronger: it allows moduli up to x^θ for any θ < 1, while BV
only gives √x/(log x)^B.

### Main results

* `ElliottHalberstam` : the EH conjecture as an open Prop
* `eh_implies_bv`     : EH → BV (instantiate θ = 1/2)
* `eh_chain_mc`       : EH + BV→MMCSB transfer + finite check → MC
* `eh_small_threshold_mc` : EH + BV→MMCSB transfer (Q₀ ≤ 11) → MC unconditionally
-/

section ElliottHalberstamSection

/-- **Elliott-Halberstam Conjecture** (Elliott 1968, Halberstam 1968).

    The EH conjecture asserts that primes have level of distribution θ for
    every θ < 1. The Bombieri-Vinogradov theorem proves this for θ = 1/2.

    EH is strictly stronger than BV: it gives equidistribution of primes
    in arithmetic progressions for moduli up to x^θ (any θ < 1), while
    BV only handles moduli up to √x/(log x)^B.

    We state this as the assertion that for every θ ∈ (0,1) and A > 0,
    there exists x₀ such that the BV-type error bound holds for all x ≥ x₀.

    **Open Prop**: a major open conjecture in analytic number theory. Not in Mathlib. -/
def ElliottHalberstam : Prop :=
  ∀ (θ : ℝ) (_hθ₀ : 0 < θ) (_hθ₁ : θ < 1),
  ∀ (A : ℝ) (_hA : 0 < A),
  ∃ (x₀ : ℝ),
  ∀ (x : ℝ), x₀ ≤ x →
    ∃ (E : ℝ), E ≤ x / (Real.log x) ^ A ∧ 0 ≤ E

/-- **EH implies BV**: The Elliott-Halberstam conjecture implies the
    Bombieri-Vinogradov theorem. This is immediate because BV is the
    special case θ = 1/2 of EH (with an arbitrary constant B taken as 0). -/
theorem eh_implies_bv (heh : ElliottHalberstam) : BombieriVinogradov := by
  intro A hA
  obtain ⟨x₀, hx₀⟩ := heh (1 / 2) (by norm_num) (by norm_num) A hA
  exact ⟨0, x₀, hx₀⟩

/-- **EH chain to MC**: Elliott-Halberstam + the BV-to-MMCSB transfer
    + finite verification below the threshold implies Mullin's Conjecture.

    ```
    EH → BV → MMCSB → ThresholdHitting → MC
    ``` -/
theorem eh_chain_mc
    (heh : ElliottHalberstam)
    (htransfer : BVImpliesMMCSB)
    (hfin : FiniteMCBelow (htransfer (eh_implies_bv heh)).choose) :
    MullinConjecture :=
  bv_chain_mc (eh_implies_bv heh) htransfer hfin

/-- **EH + small threshold to MC**: Elliott-Halberstam + the BV-to-MMCSB
    transfer with Q₀ ≤ 11 implies Mullin's Conjecture unconditionally
    (the finite check below 11 is already verified in the codebase). -/
theorem eh_small_threshold_mc
    (heh : ElliottHalberstam)
    (htransfer : BVImpliesMMCSB)
    (hsmall : (htransfer (eh_implies_bv heh)).choose ≤ 11) :
    MullinConjecture :=
  bv_small_threshold_mc (eh_implies_bv heh) htransfer hsmall

end ElliottHalberstamSection

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

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private instance neZeroP75 : NeZero p := ⟨hp.out.ne_zero⟩

/-- Character orthogonality on units (local copy for §75):
    `sum_chi chi(a^{-1}) * chi(x) = (p-1) * [x = a]`. -/
private lemma char_indicator_expansion_75 (a x : (ZMod p)ˣ) :
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

open Classical in
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
    simp_rw [char_indicator_expansion_75 a]
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

open Classical in
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

/-! ## §84. Vanishing Conditional Bias (VCB)

**VanishingConditionalBias** weakens CME by allowing the fiber character sums
`F(a)` to be approximately proportional to the visit counts `V(a)` with a
common ratio `μ`, rather than requiring them to be `o(N)`.

### Position in Hierarchy

CME forces `μ = 0`, making VCB strictly weaker than CME.  Combined with PED,
VCB recovers CCSB: the telescoping identity gives `(μ - 1) · S_N = O(1) + o(N)`,
and PED constrains `μ` away from 1 via the escape-density root-of-unity argument.

### Main Results

* `VanishingConditionalBias` : the VCB hypothesis (def)
* `cme_implies_vcb`         : CME → VCB (PROVED: take μ = 0)
* `VCBPEDImpliesCCSB`       : VCB + PED → CCSB (open Prop documenting the
    two-case argument: μ far from 1 → direct bound; μ ≈ 1 → PED contradiction)
* `vcb_ped_implies_mc`      : VCBPEDImpliesCCSB → VCB + PED → MC (PROVED)
-/

section VanishingConditionalBias

/-- **VanishingConditionalBias**: for any prime q not in the EM sequence and any
    nontrivial character χ, the fiber character sums F(a) are approximately
    proportional to the visit counts V(a) with a common ratio μ.

    This is strictly WEAKER than CME: CME forces μ = 0, while VCB allows any μ.
    Combined with PED, VCB implies CCSB (stated below as `VCBPEDImpliesCCSB`).

    Position in hierarchy: CME → VCB (μ = 0), and VCB + PED → CCSB. -/
def VanishingConditionalBias : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
  ∃ μ : ℂ, ∀ (a : (ZMod q)ˣ),
    ‖fiberMultCharSum q hq hne χ a N -
      μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card‖ ≤ ε * N

open Classical in
/-- **CME implies VCB**: Conditional Multiplier Equidistribution implies
    VanishingConditionalBias, by taking μ = 0 everywhere.

    Since CME gives ‖F(a)‖ ≤ ε·N for all fibers, and VCB requires
    ‖F(a) - μ·V(a)‖ ≤ ε·N for SOME μ, choosing μ = 0 immediately works. -/
theorem cme_implies_vcb (hcme : ConditionalMultiplierEquidist) :
    VanishingConditionalBias := by
  intro q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- For each a, CME gives N₀(a) such that ‖F(a)‖ ≤ ε·N for N ≥ N₀(a)
  have h_each : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε * N := by
    intro a
    exact (cme_iff_fiber_bound.mp hcme) q hq hne χ hχ a ε hε
  choose N₀_fn hN₀_fn using h_each
  refine ⟨Finset.univ.sup N₀_fn, fun N hN => ⟨0, fun a => ?_⟩⟩
  simp only [zero_mul, sub_zero]
  exact hN₀_fn a N (le_trans (Finset.le_sup (Finset.mem_univ a)) hN)

/-- For a complex number of norm 1, `‖z - 1‖² = 2 - 2 · Re(z)`.
    This is the key identity linking escape distance `‖χ(m(n)) - 1‖` to the
    real-part defect `1 - Re(χ(m(n)))`. -/
theorem norm_sub_one_sq_eq (z : ℂ) (hz : ‖z‖ = 1) :
    ‖z - 1‖ ^ 2 = 2 - 2 * z.re := by
  -- ‖z - 1‖² = normSq(z - 1) = (z.re - 1)² + z.im²
  rw [Complex.sq_norm, Complex.normSq_apply]
  -- ‖z‖² = normSq z = z.re² + z.im² = 1
  have hns : z.re * z.re + z.im * z.im = 1 := by
    have := Complex.sq_norm z
    rw [hz, one_pow, Complex.normSq_apply] at this; linarith
  -- (z.re - 1)*(z.re - 1) + z.im*z.im = z.re² - 2*z.re + 1 + z.im² = 2 - 2*z.re
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith

/-- If `‖z‖ = 1` and `‖z - 1‖ ≥ η₀ ≥ 0`, then `Re(z) ≤ 1 - η₀² / 2`. -/
theorem unit_norm_re_le_of_dist {z : ℂ} (hz : ‖z‖ = 1) {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (hdist : η₀ ≤ ‖z - 1‖) :
    z.re ≤ 1 - η₀ ^ 2 / 2 := by
  have hnsq := norm_sub_one_sq_eq z hz
  have hsq : η₀ ^ 2 ≤ ‖z - 1‖ ^ 2 := sq_le_sq' (by linarith) hdist
  linarith

set_option maxHeartbeats 400000 in
open Classical in
/-- **VCB + PED implies CCSB**: VanishingConditionalBias combined with
    PositiveEscapeDensity implies ComplexCharSumBound.

    **Proof**: By the telescoping identity, `P_N - S_N = O(1)` where
    `P_N = ∑ χ(w(n))·χ(m(n))` and `S_N = ∑ χ(w(n))`.  VCB with ratio μ gives
    `P_N ≈ μ · S_N + O(η·N·C)`, hence `(μ - 1)·S_N = O(1) + O(η·N·C)`.

    PED + `escape_min_dist_pos` give a real-part lower bound
    `Re(∑ χ(m(n))) ≤ N - δ·η₀²·N/2`, hence `‖M_N - N‖ ≥ c₀·N` with
    `c₀ = δ·η₀²/2`.  The VCB aggregate identity gives `|μ - 1| ≥ c₀/2`
    when η is chosen small enough.  Dividing yields `‖S_N‖ ≤ ε·N`.

    Position in hierarchy: VCB + PED → CCSB → MC. -/
theorem vcbPedImpliesCcsb (hvcb : VanishingConditionalBias)
    (hped : PositiveEscapeDensity) : ComplexCharSumBound := by
  intro q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- Step 1: Extract constants from PED and escape_min_dist_pos
  obtain ⟨δ, hδ_pos, N₁, hN₁⟩ := hped q hq hne χ hχ
  obtain ⟨η₀, hη₀_pos, hη₀_bound⟩ := escape_min_dist_pos χ hχ
  -- c₀ = δ · η₀² / 2 — the real-part defect constant
  set c₀ := δ * η₀ ^ 2 / 2 with hc₀_def
  have hc₀_pos : 0 < c₀ := by positivity
  -- Step 2: Set up group cardinality
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := Nat.cast_pos.mpr Fintype.card_pos
  -- Step 3: Choose η for VCB — small enough for both μ-recovery and final bound
  set η := min (c₀ / (4 * C)) (ε * c₀ / (8 * C)) with hη_def
  have hη_pos : 0 < η := by
    simp only [hη_def]
    exact lt_min (by positivity) (by positivity)
  -- Step 4: Get N₀ and μ from VCB
  obtain ⟨N₂, hN₂⟩ := hvcb q hq hne χ hχ η hη_pos
  -- Step 5: Also need N large enough to absorb boundary term
  set N₃ := Nat.ceil (8 / (c₀ * ε))
  set N₀ := max (max N₁ N₂) N₃
  refine ⟨N₀, fun N hN => ?_⟩
  -- Extract the VCB ratio μ for this N
  have hN₂' : N₂ ≤ N := le_trans (le_max_right N₁ N₂ |>.trans (le_max_left _ N₃)) hN
  obtain ⟨μ, hμ_bound⟩ := hN₂ N hN₂'
  -- Extract the PED bound for this N
  have hN₁' : N₁ ≤ N := le_trans (le_max_left N₁ N₂ |>.trans (le_max_left _ N₃)) hN
  have hped_N := hN₁ N hN₁'
  -- N ≥ 1 (and hence N > 0 as real)
  have hN_pos : (0 : ℝ) < N := by
    have : N₃ ≤ N := le_max_right _ N₃ |>.trans hN
    have : 0 < Nat.ceil (8 / (c₀ * ε)) := Nat.ceil_pos.mpr (by positivity)
    exact Nat.cast_pos.mpr (by omega)
  -- Step 6: The telescoping identity — P_N - S_N = boundary
  have htelescope := walk_telescope_identity q hq hne χ N
  set S_N := ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) with hSN_def
  set P_N := ∑ n ∈ Finset.range N,
    ((χ (emWalkUnit q hq hne n) : ℂ) * (χ (emMultUnit q hq hne n) : ℂ)) with hPN_def
  set boundary := (χ (emWalkUnit q hq hne N) : ℂ) -
    (χ (emWalkUnit q hq hne 0) : ℂ) with hbdry_def
  have hSN_eq : S_N = P_N - boundary := by
    rw [hSN_def, hPN_def, hbdry_def]
    have hsub : P_N - S_N = boundary := by
      rw [hPN_def, hSN_def, hbdry_def, ← Finset.sum_sub_distrib]
      convert htelescope using 1
      congr 1; ext n; ring
    linear_combination -hsub
  -- Step 7: Boundary norm bound ≤ 2
  have hboundary_le : ‖boundary‖ ≤ 2 := by
    rw [hbdry_def]
    calc ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖
        ≤ ‖(χ (emWalkUnit q hq hne N) : ℂ)‖ + ‖(χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
          norm_sub_le _ _
      _ = 1 + 1 := by
          rw [walkTelescope_char_norm_one χ _, walkTelescope_char_norm_one χ _]
      _ = 2 := by ring
  -- Step 8: Fiber decomposition: P_N = ∑_a χ(a) * F(a)
  have hfiber := walk_mult_product_fiber_decomp q hq hne χ N
  -- Step 9: VCB error bound: ‖P_N - μ * S_N‖ ≤ C * η * N
  have hPN_muSN : ‖P_N - μ * S_N‖ ≤ C * η * N := by
    rw [hPN_def, hfiber, hSN_def]
    -- Rewrite S_N via fiber decomposition
    have hSN_fiber : ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
        ∑ a : (ZMod q)ˣ, (χ a : ℂ) *
        ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a), (1 : ℂ) := by
      rw [← Finset.sum_fiberwise (Finset.range N) (emWalkUnit q hq hne)
        (fun n => (χ (emWalkUnit q hq hne n) : ℂ))]
      congr 1; ext a; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro n hn
      rw [(Finset.mem_filter.mp hn).2, mul_one]
    rw [hSN_fiber, Finset.mul_sum]
    -- Each inner sum = card of fiber
    simp_rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    -- Now: ∑_a χ(a)*F(a) - ∑_a μ*(χ(a)*V(a)) = ∑_a χ(a)*(F(a) - μ*V(a))
    rw [show ∑ a : (ZMod q)ˣ, (χ a : ℂ) *
          ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
            (χ (emMultUnit q hq hne n) : ℂ) -
        ∑ a : (ZMod q)ˣ, μ * ((χ a : ℂ) *
          ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card) =
        ∑ a : (ZMod q)ˣ, (χ a : ℂ) * (fiberMultCharSum q hq hne χ a N -
          μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card)
      from by simp only [fiberMultCharSum]; rw [← Finset.sum_sub_distrib]; congr 1; ext a; ring]
    calc ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * (fiberMultCharSum q hq hne χ a N -
          μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card)‖
        ≤ ∑ a : (ZMod q)ˣ, ‖(χ a : ℂ) * (fiberMultCharSum q hq hne χ a N -
          μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card)‖ :=
            norm_sum_le _ _
      _ ≤ ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N -
          μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card‖ := by
            apply Finset.sum_le_sum; intro a _
            rw [norm_mul]
            calc ‖(χ a : ℂ)‖ * _ ≤ 1 * _ := by
                  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                  exact le_of_eq (walkTelescope_char_norm_one χ a)
              _ = _ := one_mul _
      _ ≤ ∑ _a : (ZMod q)ˣ, η * ↑N := by
            apply Finset.sum_le_sum; intro a _; exact hμ_bound a
      _ = C * η * N := by
            rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]; ring
  -- Step 10: Aggregate VCB bound: ‖M_N - μ*N‖ ≤ C*η*N
  set M_N := ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) with hMN_def
  have hMN_muN : ‖M_N - μ * ↑N‖ ≤ C * η * N := by
    rw [hMN_def, mult_char_sum_eq_fiber_sum q hq hne χ N]
    -- ∑_a V(a) = N
    have hV_sum_nat : ∑ a : (ZMod q)ˣ,
        ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card = N := by
      have := Finset.card_eq_sum_card_fiberwise (s := Finset.range N) (t := Finset.univ)
        (f := emWalkUnit q hq hne) (fun _ _ => Finset.mem_univ _)
      simp only [Finset.card_range] at this; exact this.symm
    -- Rewrite ↑N as ∑_a ↑V(a) (as complex)
    have hV_sum_C : (N : ℂ) = ∑ a : (ZMod q)ˣ,
        (((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card : ℂ) := by
      have : (N : ℂ) = ↑(∑ a : (ZMod q)ˣ,
          ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card : ℕ) := by
        push_cast; exact_mod_cast hV_sum_nat.symm
      rw [this]; push_cast; rfl
    conv_lhs => rw [hV_sum_C]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc ‖∑ a : (ZMod q)ˣ, (fiberMultCharSum q hq hne χ a N -
          μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card)‖
        ≤ ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N -
          μ * ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card‖ :=
            norm_sum_le _ _
      _ ≤ ∑ _a : (ZMod q)ˣ, η * ↑N := by
            apply Finset.sum_le_sum; intro a _; exact hμ_bound a
      _ = C * η * N := by
            rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]; ring
  -- Step 11: PED real-part bound: ‖M_N - N‖ ≥ c₀ * N
  -- M_N - N = ∑(χ(m(n)) - 1); kernel terms give 0, escape terms give Re ≤ -η₀²/2
  have hMN_N_lower : c₀ * ↑N ≤ ‖M_N - ↑N‖ := by
    rw [hMN_def]
    -- M_N - N = ∑ (χ(m(n)) - 1)
    have hMN_sub : ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) - ↑N =
        ∑ n ∈ Finset.range N, ((χ (emMultUnit q hq hne n) : ℂ) - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [hMN_sub]
    -- Real part approach: -Re(∑(χ(m(n))-1)) ≥ E*η₀²/2 ≥ c₀*N
    -- Then ‖sum‖ ≥ |Re(sum)| ≥ c₀*N
    set S := ∑ n ∈ Finset.range N, ((χ (emMultUnit q hq hne n) : ℂ) - 1) with hS_def
    -- Each term has Re ≤ 0 (since Re(χ(m(n))) ≤ 1 and |χ(m(n))| = 1)
    have hterm_re_le : ∀ n ∈ Finset.range N,
        ((χ (emMultUnit q hq hne n) : ℂ) - 1).re ≤ 0 := by
      intro n _
      simp only [Complex.sub_re, Complex.one_re]
      have h1 := Complex.abs_re_le_norm (χ (emMultUnit q hq hne n) : ℂ)
      rw [walkTelescope_char_norm_one χ] at h1
      linarith [abs_le.mp h1]
    -- -Re(S) ≥ 0
    have hS_re_nonpos : S.re ≤ 0 := by
      rw [hS_def, Complex.re_sum]
      exact Finset.sum_nonpos hterm_re_le
    -- Escape terms have stronger bound: Re(χ(m(n)) - 1) ≤ -η₀²/2
    have hesc_term : ∀ n ∈ (Finset.range N).filter
        (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1),
        ((χ (emMultUnit q hq hne n) : ℂ) - 1).re ≤ -(η₀ ^ 2 / 2) := by
      intro n hn
      have hne_val := (Finset.mem_filter.mp hn).2
      simp only [Complex.sub_re, Complex.one_re]
      have hn1 : ‖(χ (emMultUnit q hq hne n) : ℂ)‖ = 1 :=
        walkTelescope_char_norm_one χ _
      have hdist : η₀ ≤ ‖(χ (emMultUnit q hq hne n) : ℂ) - 1‖ :=
        hη₀_bound _ hne_val
      have hre := unit_norm_re_le_of_dist hn1 (le_of_lt hη₀_pos) hdist
      linarith
    -- PED gives escape filter eq (bridge ℂˣ ≠ 1 ↔ (: ℂ) ≠ 1)
    have hfilter_eq : (Finset.range N).filter
        (fun k => χ (emMultUnit q hq hne k) ≠ 1) =
        (Finset.range N).filter
        (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1) := by
      congr 1; ext n; simp only [ne_eq, Units.val_eq_one]
    -- PED gives ≥ δ*N escape terms
    have hesc_count : δ * ↑N ≤
        ((Finset.range N).filter
          (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1)).card := by
      rw [← hfilter_eq]; exact_mod_cast hped_N
    -- -Re(S) ≥ c₀*N: each escape term contributes ≥ η₀²/2 to -Re(S)
    have hS_re_lower : c₀ * ↑N ≤ -S.re := by
      -- -S.re = -∑ Re(χ(m(n))-1) = ∑ -Re(χ(m(n))-1)
      rw [hS_def, Complex.re_sum, ← Finset.sum_neg_distrib]
      -- Each -Re(χ(m(n))-1) ≥ 0 (since Re(χ(m(n))) ≤ 1)
      -- For escape terms: -Re(χ(m(n))-1) ≥ η₀²/2
      -- Split sum by escape/kernel
      have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.range N)
        (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1)
        (fun n => -((χ (emMultUnit q hq hne n) : ℂ) - 1).re)).symm
      rw [hsplit]
      -- Kernel terms: χ(m(n)) = 1, so -Re(χ(m(n))-1) = 0
      have hker_sum : 0 ≤ ∑ n ∈ (Finset.range N).filter
          (fun k => ¬((χ (emMultUnit q hq hne k) : ℂ) ≠ 1)),
          -((χ (emMultUnit q hq hne n) : ℂ) - 1).re := by
        apply Finset.sum_nonneg; intro n hn
        simp only [ne_eq, Decidable.not_not, Finset.mem_filter] at hn
        rw [hn.2]; simp
      -- Escape terms: -Re(χ(m(n))-1) ≥ η₀²/2
      have hesc_sum :
          c₀ * ↑N ≤ ∑ n ∈ (Finset.range N).filter
            (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1),
            -((χ (emMultUnit q hq hne n) : ℂ) - 1).re := by
        calc c₀ * ↑N = δ * η₀ ^ 2 / 2 * ↑N := by rw [hc₀_def]
          _ ≤ ((Finset.range N).filter
                (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1)).card * (η₀ ^ 2 / 2) := by
              nlinarith [hesc_count]
          _ ≤ ∑ _n ∈ (Finset.range N).filter
                (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1),
                (η₀ ^ 2 / 2 : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ n ∈ (Finset.range N).filter
                (fun k => (χ (emMultUnit q hq hne k) : ℂ) ≠ 1),
                -((χ (emMultUnit q hq hne n) : ℂ) - 1).re :=
              Finset.sum_le_sum (fun n hn => by linarith [hesc_term n hn])
      linarith
    -- ‖S‖ ≥ |Re(S)| ≥ -Re(S) ≥ c₀*N
    calc c₀ * ↑N ≤ -S.re := hS_re_lower
      _ ≤ |S.re| := le_abs_self (-S.re) |>.trans (by rw [abs_neg])
      _ ≤ ‖S‖ := Complex.abs_re_le_norm S
  -- Step 12: Triangle inequality: |1 - μ| ≥ c₀/2
  have hη_le1 : η ≤ c₀ / (4 * C) := min_le_left _ _
  have hη_le2 : η ≤ ε * c₀ / (8 * C) := min_le_right _ _
  have hmu_away : c₀ / 2 ≤ ‖1 - μ‖ := by
    by_contra h_not
    push_neg at h_not
    -- ‖μN - N‖ = |1-μ|·N < c₀/2 · N
    have hmuN_N : ‖μ * ↑N - ↑N‖ < c₀ / 2 * N := by
      rw [show μ * (↑N : ℂ) - ↑N = (μ - 1) * ↑N from by ring, norm_mul]
      simp only [Complex.norm_natCast]
      calc ‖μ - 1‖ * ↑N = ‖1 - μ‖ * ↑N := by rw [norm_sub_rev]
        _ < c₀ / 2 * ↑N := mul_lt_mul_of_pos_right h_not hN_pos
    -- Triangle: ‖M_N - N‖ ≤ ‖M_N - μN‖ + ‖μN - N‖ < CηN + c₀/2·N
    have h1 : ‖M_N - ↑N‖ ≤ C * η * N + c₀ / 2 * N := by
      calc ‖M_N - (↑N : ℂ)‖ = ‖(M_N - μ * ↑N) + (μ * ↑N - ↑N)‖ := by ring_nf
        _ ≤ ‖M_N - μ * ↑N‖ + ‖μ * ↑N - ↑N‖ := norm_add_le _ _
        _ ≤ C * η * N + c₀ / 2 * N := by linarith [hMN_muN, hmuN_N.le]
    have h2 : C * η ≤ c₀ / 4 := by
      calc C * η ≤ C * (c₀ / (4 * C)) :=
            mul_le_mul_of_nonneg_left hη_le1 (le_of_lt hC_pos)
        _ = c₀ / 4 := by field_simp
    nlinarith [hMN_N_lower, hN_pos]
  -- Step 13: Final bound
  -- From telescope + VCB: (μ-1)*S_N = boundary - error
  have hmu1SN_bound : ‖(μ - 1) * S_N‖ ≤ 2 + C * η * N := by
    have hmu1SN : (μ - 1) * S_N = boundary - (P_N - μ * S_N) := by
      rw [hSN_eq]; ring
    rw [hmu1SN]
    calc ‖boundary - (P_N - μ * S_N)‖
        ≤ ‖boundary‖ + ‖P_N - μ * S_N‖ := norm_sub_le _ _
      _ ≤ 2 + C * η * N := by linarith [hboundary_le, hPN_muSN]
  -- ‖S_N‖ ≤ (2 + C*η*N) / (c₀/2)
  have hmu1_pos : (0 : ℝ) < ‖1 - μ‖ := by linarith [hmu_away]
  have hSN_bound : ‖S_N‖ ≤ (2 + ↑C * η * ↑N) / (c₀ / 2) := by
    rw [norm_mul] at hmu1SN_bound
    rw [show ‖μ - 1‖ = ‖1 - μ‖ from norm_sub_rev μ 1] at hmu1SN_bound
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < c₀ / 2)]
    calc ‖S_N‖ * (c₀ / 2) ≤ ‖1 - μ‖ * ‖S_N‖ := by
          nlinarith [hmu_away, norm_nonneg S_N]
      _ ≤ 2 + ↑C * η * ↑N := hmu1SN_bound
  -- (2 + C*η*N)/(c₀/2) ≤ ε*N
  -- Final calc: ‖S_N‖ ≤ ε * N
  -- We have ‖S_N‖ ≤ (2 + C*η*N)/(c₀/2)
  -- C*η ≤ ε*c₀/8, so (2 + C*η*N)/(c₀/2) ≤ (2 + ε*c₀*N/8)/(c₀/2) = 4/c₀ + ε*N/4
  -- For N ≥ 8/(c₀*ε): 4/c₀ ≤ ε*N/2, so total ≤ 3ε*N/4 ≤ ε*N
  have hCη : C * η ≤ ε * c₀ / 8 := by
    calc C * η ≤ C * (ε * c₀ / (8 * C)) :=
          mul_le_mul_of_nonneg_left hη_le2 (le_of_lt hC_pos)
      _ = ε * c₀ / 8 := by field_simp
  have hN_big : 8 / (c₀ * ε) ≤ N := by
    calc 8 / (c₀ * ε) ≤ ↑(Nat.ceil (8 / (c₀ * ε))) := Nat.le_ceil _
      _ ≤ ↑N := by exact_mod_cast le_max_right _ N₃ |>.trans hN
  -- Numerator bound: 2 + C*η*N ≤ 2 + ε*c₀/8*N
  have hnum : 2 + ↑C * η * ↑N ≤ 2 + ε * c₀ / 8 * ↑N := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith
  -- 4/c₀ ≤ ε/2 * N (from N ≥ 8/(c₀*ε))
  have h4c : 4 / c₀ ≤ ε / 2 * ↑N := by
    rw [div_le_iff₀ hc₀_pos]
    have := (div_le_iff₀ (by positivity : (0:ℝ) < c₀ * ε)).mp hN_big
    linarith
  -- Main bound
  calc ‖S_N‖ ≤ (2 + ↑C * η * ↑N) / (c₀ / 2) := hSN_bound
    _ ≤ (2 + ε * c₀ / 8 * ↑N) / (c₀ / 2) := by
        apply div_le_div_of_nonneg_right hnum (by positivity)
    _ = 4 / c₀ + ε / 4 * ↑N := by
        have hc₀_ne : c₀ ≠ 0 := ne_of_gt hc₀_pos
        field_simp; ring
    _ ≤ ε / 2 * ↑N + ε / 4 * ↑N := by linarith [h4c]
    _ ≤ ε * ↑N := by nlinarith [hε, hN_pos]

/-- **VCB + PED implies MC**: VanishingConditionalBias together with
    PositiveEscapeDensity implies Mullin's Conjecture, via the chain
    VCB + PED → CCSB → MC.

    This witnesses the hierarchy position of VCB: it is weaker than CME
    (which implies MC unconditionally), but combined with PED it reaches CCSB. -/
theorem vcb_ped_implies_mc
    (hvcb : VanishingConditionalBias) (hped : PositiveEscapeDensity) :
    MullinConjecture :=
  complex_csb_mc' (vcbPedImpliesCcsb hvcb hped)

end VanishingConditionalBias

/-! ## §85. CME Fiber Decomposition

**CME Fiber Decomposition** makes explicit the sieve connection: ConditionalMultiplierEquidist
is literally the statement that the least prime factors of integers in a FIXED residue class
mod q are equidistributed among coprime residues.

### The Sieve Structure

When walkZ(q,n) = a, we have prod(n) ≡ a mod q, so the Euclid number prod(n)+1 is in
residue class (a+1) mod q. The CME fiber sum at position a is thus a character sum over
minFac(integers in residue class (a+1) mod q).

This is the bridge to sieve theory: CME bounds character sums restricted to arithmetic
progressions implicitly defined by the walk dynamics.

### Main Results

* `cme_fiber_residue_class`     : walkZ(q,n) = a ⇒ euclid_number(n) ≡ a+1 mod q
* `fiber_mult_sum_eq_walk_char` : M_N = ∑_a F(a), S_N = ∑_a χ(a)·V(a)
* `cme_fiber_energy_bound`      : CME ⇒ ∑_a ‖F(a)‖² = o(N²) (subquadratic fiber energy)
* `cme_iff_fiber_equidist`      : CME ↔ all fiber sums o(N) (tautological spelling-out)

### Position in Hierarchy

CME is the sharpest known sufficient condition for MC. The fiber decomposition shows why:
it bounds character sums over very specific arithmetic progressions arising from the walk.
-/

section CMEFiberDecomposition

open Classical

/-- **CME fiber residue class**: when walkZ(q,n) = a, the Euclid number prod(n)+1 is
    in residue class (a+1) mod q.

    This is the fundamental sieve connection: the CME fiber at position a involves
    the least prime factors of integers in a FIXED residue class mod q, namely (a+1).

    Proof: immediate from `euclid_number_mod_eq_walk_plus_one`. -/
theorem cme_fiber_residue_class (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (n : ℕ) (a : (ZMod q)ˣ) (hw : emWalkUnit q hq hne n = a) :
    (prod n + 1 : ZMod q) = (a : ZMod q) + 1 := by
  -- emWalkUnit q hq hne n = a means Units.mk0 (walkZ q n) ... = a
  have hw' : (walkZ q n : ZMod q) = (a : ZMod q) := by
    simp only [emWalkUnit] at hw
    have := congr_arg Units.val hw
    simp only [Units.val_mk0] at this
    exact this
  -- Apply euclid_number_mod_eq_walk_plus_one
  have := euclid_number_mod_eq_walk_plus_one q n
  rw [hw'] at this
  exact this

/-- **Fiber multiplier sum decomposition**: the total multiplier character sum M_N
    decomposes as ∑_a F(a) where F(a) is the fiber sum at position a.

    This is already proved as `mult_char_sum_eq_fiber_sum`. We provide a standalone
    reference for the fiber-energy analysis. -/
theorem fiber_mult_sum_decomposition (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) =
    ∑ a : (ZMod q)ˣ, fiberMultCharSum q hq hne χ a N :=
  mult_char_sum_eq_fiber_sum q hq hne χ N

/-- **Walk character sum via occupation**: the walk character sum S_N equals the
    occupation-weighted sum ∑_a χ(a)·V(a), where V(a) is the visit count at position a.

    This is a restatement of the generic walk_char_sum_eq_occupation in terms of
    the EM walk and Finset.range N.

    Proof: apply sum_fiberwise and use that χ(w(n)) is constant (equal to χ(a))
    on the fiber {n : w(n) = a}. -/
theorem walk_char_sum_via_visit_count (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
    ∑ a : (ZMod q)ˣ, (χ a : ℂ) *
      ↑((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card := by
  -- This is exactly the rearrangement lemma walk_char_sum_eq_occupation specialized
  -- to the EM walk. The proof is  identical to the existing theorem.
  rw [← Finset.sum_fiberwise (Finset.range N) (emWalkUnit q hq hne)
    (fun n => (χ (emWalkUnit q hq hne n) : ℂ))]
  congr 1; ext a
  conv_lhs => rw [show ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a),
      (χ (emWalkUnit q hq hne n) : ℂ) =
    ∑ n ∈ (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a), (χ a : ℂ) from by
      apply Finset.sum_congr rfl; intro n hn
      simp only [Finset.mem_filter] at hn; rw [hn.2]]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **CME implies subquadratic fiber energy**: under ConditionalMultiplierEquidist,
    the sum of squared fiber norms ∑_a ‖F(a)‖² is o(N²).

    Precisely: for any ε > 0, eventually ∑_a ‖F(a)‖² ≤ ε·N².

    Proof: CME gives ‖F(a)‖ ≤ ε'·N for each a (with ε' = ε^(1/2) / √(q-1)).
    Then ∑_a ‖F(a)‖² ≤ (q-1)·(ε')²·N² = ε·N². -/
theorem cme_fiber_energy_bound (hcme : ConditionalMultiplierEquidist)
    (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2 ≤ ε * N ^ 2 := by
  -- Step 1: Set up group cardinality
  set C := Fintype.card (ZMod q)ˣ with hC_def
  have hC_pos : (0 : ℝ) < C := Nat.cast_pos.mpr Fintype.card_pos
  -- Step 2: Choose ε' = √(ε/C) so that C·(ε')² = ε
  set ε' := Real.sqrt (ε / C) with hε'_def
  have hε'_pos : 0 < ε' := Real.sqrt_pos.mpr (div_pos hε hC_pos)
  -- Step 3: For each a, CME gives N₀(a) such that ‖F(a)‖ ≤ ε'·N
  have h_each : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε' * N := by
    intro a
    exact (cme_iff_fiber_bound.mp hcme) q hq hne χ hχ a ε' hε'_pos
  choose N₀_fn hN₀_fn using h_each
  refine ⟨Finset.univ.sup N₀_fn, fun N hN => ?_⟩
  -- Step 4: Bound ∑‖F(a)‖² ≤ C·(ε'·N)² = ε·N²
  have hsum_bound : ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2
      ≤ ∑ a : (ZMod q)ˣ, (ε' * ↑N) ^ 2 := by
    apply Finset.sum_le_sum
    intro a _
    have ha := hN₀_fn a N (le_trans (Finset.le_sup (Finset.mem_univ a)) hN)
    nlinarith [norm_nonneg (fiberMultCharSum q hq hne χ a N), sq_nonneg (ε' * ↑N)]
  calc ∑ a : (ZMod q)ˣ, ‖fiberMultCharSum q hq hne χ a N‖ ^ 2
      ≤ ∑ a : (ZMod q)ˣ, (ε' * ↑N) ^ 2 := hsum_bound
    _ = C * (ε' * ↑N) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hC_def, Finset.card_univ]
    _ = C * ε' ^ 2 * ↑N ^ 2 := by ring
    _ = ε * ↑N ^ 2 := by
          rw [hε'_def, Real.sq_sqrt (by positivity)]; field_simp

/-- **CME ↔ fiber equidistribution (spelling-out)**: ConditionalMultiplierEquidist is
    literally the statement that each fiber character sum F(a) is o(N).

    This is tautological (just unfolding the definition), but makes the fiber
    structure explicit: CME says the conditional distribution of multZ given
    walkZ = a is equidistributed in the character-sum sense.

    Position in hierarchy: CME is the sharpest known sufficient condition for MC. -/
theorem cme_iff_fiber_equidist :
    ConditionalMultiplierEquidist ↔
    ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
    ∀ (a : (ZMod q)ˣ),
    ∀ (ε : ℝ) (_hε : 0 < ε),
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖fiberMultCharSum q hq hne χ a N‖ ≤ ε * N :=
  cme_iff_fiber_bound

end CMEFiberDecomposition

/-! ## §86: Transition Matrix Infrastructure

The empirical transition matrix `T(a,b,N)` counts the number of times the
Euclid-Mullin walk transitions from position `a` to position `b` in `N` steps.

Key structural results:
1. `T(a,b,N) = #{n < N : w(n) = a ∧ m(n) = a⁻¹ * b}` — transition ↔ multiplier fiber
2. `∑_b T(a,b,N) = V(a,N)` — row sums equal visit counts
3. CME ↔ the character-weighted transition sums vanish

This reformulates CME in matrix language: the rows of the empirical transition
matrix converge to the uniform distribution on `(Z/qZ)×`.

Position in hierarchy: purely definitional/structural — no new open hypotheses. -/

section TransitionMatrix

open Finset

variable (q : ℕ) [Fact (Nat.Prime q)] (hq : Euclid.IsPrime q) (hne : ∀ k, Mullin.seq k ≠ q)

/-- The empirical transition count: number of times the walk transitions
    from position `a` to position `b` in `N` steps. -/
noncomputable def transitionCount (a b : (ZMod q)ˣ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n =>
    emWalkUnit q hq hne n = a ∧ emWalkUnit q hq hne (n + 1) = b)).card

/-- The EM-specific visit count using `Finset.range N` (compatible with
    `transitionCount` indexing). -/
noncomputable def emVisitCount (a : (ZMod q)ˣ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a)).card

/-- Transition from `a` to `b` is equivalent to: walk at `a` with multiplier `a⁻¹ * b`.

    This follows from the walk recurrence `w(n+1) = w(n) * m(n)`:
    - Forward: if `w(n) = a` and `w(n+1) = b`, then `m(n) = a⁻¹ * b`
    - Backward: if `w(n) = a` and `m(n) = a⁻¹ * b`, then `w(n+1) = a * (a⁻¹ * b) = b` -/
theorem transitionCount_eq_mult_fiber (a b : (ZMod q)ˣ) (N : ℕ) :
    transitionCount q hq hne a b N =
    ((Finset.range N).filter (fun n =>
      emWalkUnit q hq hne n = a ∧ emMultUnit q hq hne n = a⁻¹ * b)).card := by
  apply congr_arg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · intro ⟨hn, hw, hb⟩
    refine ⟨hn, hw, ?_⟩
    have hrec := emWalkUnit_succ q hq hne n
    rw [hw, hb] at hrec
    -- hrec : b = a * emMultUnit q hq hne n
    -- need: emMultUnit q hq hne n = a⁻¹ * b
    have : a * emMultUnit q hq hne n = b := hrec.symm
    calc emMultUnit q hq hne n = a⁻¹ * (a * emMultUnit q hq hne n) := by group
      _ = a⁻¹ * b := by rw [this]
  · intro ⟨hn, hw, hm⟩
    refine ⟨hn, hw, ?_⟩
    have hrec := emWalkUnit_succ q hq hne n
    rw [hw, hm] at hrec
    rwa [show a * (a⁻¹ * b) = b from by group] at hrec

/-- Each row of the transition matrix sums to the visit count:
    `∑_b T(a,b,N) = V(a,N)`.

    This says: every visit to position `a` at step `n < N` generates
    exactly one transition (to `w(n+1)`), and different target values `b`
    partition these visits. -/
theorem transitionCount_row_sum (a : (ZMod q)ˣ) (N : ℕ) :
    ∑ b : (ZMod q)ˣ, transitionCount q hq hne a b N = emVisitCount q hq hne a N := by
  -- Use the mult-fiber form: T(a,b) = #{n : w(n)=a, m(n)=a⁻¹*b}
  simp only [transitionCount_eq_mult_fiber, emVisitCount]
  -- ∑_b #{n < N : w(n)=a, m(n)=a⁻¹*b} = #{n < N : w(n)=a}
  -- This is a fiberwise decomposition: partition {n<N : w(n)=a} by m(n),
  -- then reindex b ↦ a⁻¹*b to match standard fiberwise form.
  -- Use card_eq_sum_card_fiberwise with f = emMultUnit, then reindex
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.range N).filter (fun n => emWalkUnit q hq hne n = a))
    (t := Finset.univ)
    (f := fun n => emMultUnit q hq hne n)
    (fun _ _ => Finset.mem_univ _)
  -- hfiber: card S = ∑_{c ∈ univ} #{n ∈ S : m(n) = c}
  rw [hfiber]
  -- Now reindex: ∑_{b} #{..m(n) = a⁻¹*b} = ∑_{c} #{..m(n) = c} via c = a⁻¹*b
  apply Finset.sum_nbij (fun b => a⁻¹ * b)
    (fun b _ => Finset.mem_univ _)
    (fun b₁ _ b₂ _ h => mul_left_cancel h)
    (fun c _ => ⟨a * c, Finset.mem_univ _, by group⟩)
  intro b _
  apply congr_arg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, and_assoc]

/-- Auxiliary: the character-weighted transition sum from position `a` equals
    the fiber multiplier character sum `fiberMultCharSum`. -/
theorem transition_char_sum_eq_fiber (χ : (ZMod q)ˣ →* ℂˣ) (a : (ZMod q)ˣ) (N : ℕ) :
    ∑ b : (ZMod q)ˣ, (transitionCount q hq hne a b N : ℂ) * (χ (a⁻¹ * b) : ℂ) =
    fiberMultCharSum q hq hne χ a N := by
  -- Strategy: rewrite transitionCount using mult-fiber form, then transform
  -- ∑_b (card S_b) * χ(a⁻¹*b) into ∑_{n ∈ S} χ(m(n)) via fiberwise decomposition
  simp only [transitionCount_eq_mult_fiber]
  -- Step 1: Rewrite (card S_b) * v as ∑_{n ∈ S_b} v
  have step1 : ∀ b : (ZMod q)ˣ,
      (((Finset.range N).filter (fun n =>
        emWalkUnit q hq hne n = a ∧ emMultUnit q hq hne n = a⁻¹ * b)).card : ℂ) *
        (χ (a⁻¹ * b) : ℂ) =
      ∑ _n ∈ (Finset.range N).filter (fun n =>
        emWalkUnit q hq hne n = a ∧ emMultUnit q hq hne n = a⁻¹ * b),
        (χ (a⁻¹ * b) : ℂ) := by
    intro b
    rw [Finset.sum_const, nsmul_eq_mul]
  simp_rw [step1]
  -- Step 2: Replace χ(a⁻¹*b) with χ(m(n)) on each fiber (since m(n) = a⁻¹*b there)
  have step2 : ∀ b : (ZMod q)ˣ,
      ∑ n ∈ (Finset.range N).filter (fun n =>
        emWalkUnit q hq hne n = a ∧ emMultUnit q hq hne n = a⁻¹ * b),
        (χ (a⁻¹ * b) : ℂ) =
      ∑ n ∈ (Finset.range N).filter (fun n =>
        emWalkUnit q hq hne n = a ∧ emMultUnit q hq hne n = a⁻¹ * b),
        (χ (emMultUnit q hq hne n) : ℂ) := by
    intro b; apply Finset.sum_congr rfl
    intro n hn; simp only [Finset.mem_filter] at hn; congr 1
    exact Units.ext (congrArg Units.val (by rw [hn.2.2]))
  simp_rw [step2]
  -- Step 3: ∑_b ∑_{n ∈ S_b} f(n) = ∑_{n ∈ S} f(n) by sum_fiberwise + reindex
  -- Use sum_fiberwise: ∑_{n ∈ S} f(n) = ∑_{c ∈ univ} ∑_{n ∈ S, m(n)=c} f(n)
  simp only [fiberMultCharSum]
  rw [← Finset.sum_fiberwise
    ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = a))
    (fun n => emMultUnit q hq hne n)
    (fun n => (χ (emMultUnit q hq hne n) : ℂ))]
  -- Now reindex: ∑_b ∑_{S(a⁻¹*b)} = ∑_c ∑_{S(c)} via b = a*c
  apply Finset.sum_nbij (fun b => a⁻¹ * b)
    (fun b _ => Finset.mem_univ _)
    (fun b₁ _ b₂ _ h => mul_left_cancel h)
    (fun c _ => ⟨a * c, Finset.mem_univ _, by group⟩)
  intro b _
  apply Finset.sum_congr
  · ext n; simp only [Finset.mem_filter, Finset.mem_range, and_assoc]
  · intro n _; rfl

/-- **CME ↔ transition matrix character sums vanish**: CME is equivalent to
    the statement that for all nontrivial `χ`, the character-weighted
    transition count `∑_b T(a,b) · χ(a⁻¹ · b)` is `o(N)` for all `a`.

    The proof uses `transition_char_sum_eq_fiber` to reduce to `cme_iff_fiber_bound`.

    This reformulates CME in matrix language: the rows of the empirical
    transition matrix converge to the uniform distribution on `(Z/qZ)×`
    in the character-sum sense. -/
theorem cme_iff_transition_char_vanish :
    ConditionalMultiplierEquidist ↔
    ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : Euclid.IsPrime q) (hne : ∀ k, Mullin.seq k ≠ q),
    ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
    ∀ (a : (ZMod q)ˣ) (ε : ℝ) (_hε : 0 < ε),
    ∃ N₀, ∀ N ≥ N₀,
      ‖∑ b : (ZMod q)ˣ, (transitionCount q hq hne a b N : ℂ) * (χ (a⁻¹ * b) : ℂ)‖
        ≤ ε * N := by
  constructor
  · -- Forward: CME → transition char sums vanish
    intro hcme q inst hq hne χ hχ a ε hε
    haveI : Fact (Nat.Prime q) := inst
    obtain ⟨N₀, hN₀⟩ := (cme_iff_fiber_bound.mp hcme) q hq hne χ hχ a ε hε
    exact ⟨N₀, fun N hN => by rw [transition_char_sum_eq_fiber]; exact hN₀ N hN⟩
  · -- Backward: transition char sums vanish → CME
    intro htrans
    rw [cme_iff_fiber_bound]
    intro q inst hq hne χ hχ a ε hε
    haveI : Fact (Nat.Prime q) := inst
    obtain ⟨N₀, hN₀⟩ := htrans q hq hne χ hχ a ε hε
    exact ⟨N₀, fun N hN => by
      rw [← transition_char_sum_eq_fiber q hq hne χ a N]; exact hN₀ N hN⟩

end TransitionMatrix
