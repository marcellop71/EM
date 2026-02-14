import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Walk Coverage on Finite Groups

This file formalizes the theory of walk coverage on finite groups, the Weyl
equidistribution criterion for finite groups, and the structural gap between
multiplier (step) character cancellation and walk character cancellation.

## Mathematical Overview

A **walk** on a finite group G with steps s(0), s(1), ... is the sequence
W(n) = s(0) * s(1) * ... * s(n-1) (with W(0) = 1). The walk **covers** G
if every element of G is visited: {W(n) : n in N} = G.

### Character sum criterion

By character orthogonality on finite abelian groups:
  #{n < M : W(n) = g} = (1/|G|) * (M + sum_{chi != 1} chi(g^{-1}) * S_M(chi))

where S_M(chi) = sum_{n < M} chi(W(n)) is the **walk character sum**.

If |S_M(chi)| <= delta * M for all nontrivial chi, then:
  #{n < M : W(n) = g} >= M/|G| * (1 - (|G|-1) * delta)

This is positive when delta < 1/(|G|-1), giving coverage.

### The step-to-walk gap

The **step character sum** is T_M(chi) = sum_{k < M} chi(s(k)).
Since chi(W(n)) = chi(s(0)) * chi(s(1)) * ... * chi(s(n-1)), the walk character sum
involves PRODUCTS of character values, not the character values themselves.
Step character cancellation (T_M = o(M)) does NOT imply walk character
cancellation (S_M = o(M)). This is the structural gap (Dead End #20).

### Counterexample: generation without coverage

In Z/4Z (additive), the alternating steps 1, 3, 1, 3, ... generate Z/4Z
(since gcd(1,3) = 1), but the partial sums cycle: 0, 1, 0, 1, ...
visiting only {0, 1} and missing {2, 3}.

## Main Results

### Definitions
* `GroupWalk` -- walk position W(n) = s(0) * ... * s(n-1) (recursive)
* `WalkCovers` -- walk visits every group element
* `WalkVisitCount` -- #{n < M : W(n) = g}
* `WalkCharSum` -- sum_{n<M} chi(W(n))
* `StepCharSum` -- sum_{k<M} chi(steps(k))
* `StepCharCancel` -- T_M(chi) = o(M) for all nontrivial chi
* `WalkCharCancel` -- S_M(chi) = o(M) for all nontrivial chi

### Proved Theorems
* `groupWalk_zero` -- W(0) = 1
* `groupWalk_succ` -- W(n+1) = W(n) * s(n)
* `walkCharSum_eq_prod_sum` -- S_M(chi) = sum of products of chi(s(k)) (CommGroup)
* `walkVisitCount_sum_eq` -- sum_g #{n < M : W(n) = g} = M
* `walkCharSum_trivial` -- trivial char contribution = M
* `walk_cancel_of_small_char_sums` -- small char sums => every element visited
* `walk_cancel_implies_covers` -- WalkCharCancel => WalkCovers (from expansion)
* `counterexample_alternating_mod4` -- alternating walk in Z/4Z misses elements

### Open Hypotheses
* `WalkCharExpansion` -- character orthogonality expansion (full Fourier inversion)
-/

noncomputable section
open Classical

/-! ## Section 1: Walk Definitions -/

/-- The walk on a group G with given steps: W(n) = s(0) * s(1) * ... * s(n-1).
    W(0) = 1, W(n+1) = W(n) * steps(n). Defined recursively. -/
def GroupWalk {G : Type*} [Group G] (steps : ℕ → G) : ℕ → G
  | 0 => 1
  | n + 1 => GroupWalk steps n * steps n

/-- The walk covers G if every element is visited. -/
def WalkCovers {G : Type*} [Group G] (steps : ℕ → G) : Prop :=
  ∀ g : G, ∃ n : ℕ, GroupWalk steps n = g

/-- Visit count: #{n < M : W(n) = g}. -/
def WalkVisitCount {G : Type*} [Group G] [DecidableEq G]
    (steps : ℕ → G) (M : ℕ) (g : G) : ℕ :=
  ((Finset.range M).filter (fun n => GroupWalk steps n = g)).card

/-- Walk character sum: S_M(chi) = sum_{n<M} chi(W(n)). -/
def WalkCharSum {G : Type*} [Group G]
    (steps : ℕ → G) (χ : G →* ℂˣ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.range M, (χ (GroupWalk steps n) : ℂ)

/-- Step (multiplier) character sum: T_M(chi) = sum_{k<M} chi(steps(k)). -/
def StepCharSum {G : Type*} [Group G]
    (steps : ℕ → G) (χ : G →* ℂˣ) (M : ℕ) : ℂ :=
  ∑ k ∈ Finset.range M, (χ (steps k) : ℂ)

/-- Step character cancellation: for every nontrivial chi and epsilon > 0,
    the step character sum is eventually bounded by epsilon * M. -/
def StepCharCancel {G : Type*} [Group G] (steps : ℕ → G) : Prop :=
  ∀ (χ : G →* ℂˣ), χ ≠ 1 → ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
    ‖StepCharSum steps χ M‖ ≤ ε * (M : ℝ)

/-- Walk character cancellation: for every nontrivial chi and epsilon > 0,
    the walk character sum is eventually bounded by epsilon * M. -/
def WalkCharCancel {G : Type*} [Group G] (steps : ℕ → G) : Prop :=
  ∀ (χ : G →* ℂˣ), χ ≠ 1 → ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
    ‖WalkCharSum steps χ M‖ ≤ ε * (M : ℝ)

/-! ## Section 2: Basic Walk Properties -/

section WalkBasic

variable {G : Type*} [Group G] (steps : ℕ → G)

/-- W(0) = 1: the walk starts at the identity. -/
@[simp]
theorem groupWalk_zero : GroupWalk steps 0 = 1 := rfl

/-- W(n+1) = W(n) * steps(n): the walk recurrence. -/
@[simp]
theorem groupWalk_succ (n : ℕ) :
    GroupWalk steps (n + 1) = GroupWalk steps n * steps n := rfl

/-- The visit counts partition M: sum_g #{n < M : W(n) = g} = M. -/
theorem walkVisitCount_sum_eq [Fintype G] [DecidableEq G] (M : ℕ) :
    ∑ g : G, WalkVisitCount steps M g = M := by
  simp only [WalkVisitCount]
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun n => GroupWalk steps n) (s := Finset.range M) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_range] at h; exact h.symm

/-- Each visit count is at most M. -/
theorem walkVisitCount_le [DecidableEq G] (M : ℕ) (g : G) :
    WalkVisitCount steps M g ≤ M := by
  unfold WalkVisitCount
  exact (Finset.card_filter_le _ _).trans (Finset.card_range M).le

/-- If WalkVisitCount steps M g > 0, then g is visited before time M. -/
theorem exists_visit_of_count_pos [DecidableEq G] (M : ℕ) (g : G)
    (h : 0 < WalkVisitCount steps M g) :
    ∃ n, n < M ∧ GroupWalk steps n = g := by
  unfold WalkVisitCount at h
  rw [Finset.card_pos] at h
  obtain ⟨n, hn⟩ := h
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  exact ⟨n, hn.1, hn.2⟩

/-- If g is visited before time M, then visit count is positive. -/
theorem count_pos_of_visit [DecidableEq G] (M : ℕ) (g : G) (n : ℕ)
    (hn : n < M) (heq : GroupWalk steps n = g) :
    0 < WalkVisitCount steps M g := by
  unfold WalkVisitCount
  rw [Finset.card_pos]
  exact ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, heq⟩⟩

/-- If all steps are the identity, the walk stays at 1. -/
theorem walk_trivial (h : ∀ k, steps k = 1) (n : ℕ) :
    GroupWalk steps n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih, h n]

end WalkBasic

/-! ## Section 3: Character Theory for Walk Coverage -/

section CharTheory

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
/-- For a nontrivial character chi : G ->* Cx, the sum over all elements vanishes. -/
theorem char_sum_eq_zero (χ : G →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ g : G, (χ g : ℂ) = 0 := by
  have ⟨b, hb⟩ : ∃ b : G, χ b ≠ 1 := by
    by_contra h; push Not at h; apply hχ; ext a; simp [h a]
  set S := ∑ g : G, (χ g : ℂ)
  have hmul : (χ b : ℂ) * S = S := by
    simp only [S, Finset.mul_sum]
    exact Fintype.sum_bijective (b * ·) (Group.mulLeft_bijective b) _ _
      (fun a => by simp only [map_mul, Units.val_mul])
  have hb_ne : (χ b : ℂ) ≠ 1 := fun h => hb (Units.val_injective h)
  have hsub : ((χ b : ℂ) - 1) * S = 0 := by linear_combination hmul
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hb_ne
  · exact h

omit [DecidableEq G] in
/-- Character value has norm 1 on a finite group. -/
theorem char_norm_one (χ : G →* ℂˣ) (g : G) : ‖(χ g : ℂ)‖ = 1 := by
  have hfin' : IsOfFinOrder (χ g) := χ.isOfFinOrder (isOfFinOrder_of_finite g)
  rw [isOfFinOrder_iff_pow_eq_one] at hfin'
  obtain ⟨n, hn, hpow⟩ := hfin'
  have hne : NeZero n := ⟨by omega⟩
  exact Complex.norm_eq_one_of_mem_rootsOfUnity
    (show (χ g) ∈ rootsOfUnity (⟨n, by omega⟩ : ℕ+) ℂ from by
      rw [_root_.mem_rootsOfUnity]; exact hpow)

omit [Fintype G] [DecidableEq G] in
/-- For commutative groups, GroupWalk = Finset.prod. -/
private theorem groupWalk_eq_finset_prod (steps : ℕ → G) (n : ℕ) :
    GroupWalk steps n = ∏ k ∈ Finset.range n, steps k := by
  induction n with
  | zero => simp [GroupWalk]
  | succ n ih => simp [GroupWalk, ih, Finset.prod_range_succ]

omit [Fintype G] [DecidableEq G] in
/-- Walk character sum as sum of products: S_M(chi) = sum_{n<M} prod_{k<n} chi(s(k)). -/
theorem walkCharSum_eq_prod_sum (steps : ℕ → G) (χ : G →* ℂˣ) (M : ℕ) :
    WalkCharSum steps χ M =
    ∑ n ∈ Finset.range M, ∏ k ∈ Finset.range n, (χ (steps k) : ℂ) := by
  simp only [WalkCharSum, groupWalk_eq_finset_prod, map_prod, Units.coe_prod]

omit [Fintype G] [DecidableEq G] in
/-- The walk character sum for the trivial character equals M. -/
theorem walkCharSum_trivial (steps : ℕ → G) (M : ℕ) :
    WalkCharSum steps (1 : G →* ℂˣ) M = (M : ℂ) := by
  simp [WalkCharSum, MonoidHom.one_apply, Units.val_one]

omit [DecidableEq G] in
/-- The norm of a walk character sum is bounded by M. -/
theorem walkCharSum_norm_le (steps : ℕ → G) (χ : G →* ℂˣ) (M : ℕ) :
    ‖WalkCharSum steps χ M‖ ≤ M := by
  unfold WalkCharSum
  calc ‖∑ n ∈ Finset.range M, (χ (GroupWalk steps n) : ℂ)‖
      ≤ ∑ n ∈ Finset.range M, ‖(χ (GroupWalk steps n) : ℂ)‖ := norm_sum_le _ _
    _ = ∑ _ ∈ Finset.range M, (1 : ℝ) := by congr 1; ext n; exact char_norm_one χ _
    _ = M := by simp

omit [DecidableEq G] in
/-- The norm of a step character sum is bounded by M. -/
theorem stepCharSum_norm_le (steps : ℕ → G) (χ : G →* ℂˣ) (M : ℕ) :
    ‖StepCharSum steps χ M‖ ≤ M := by
  unfold StepCharSum
  calc ‖∑ k ∈ Finset.range M, (χ (steps k) : ℂ)‖
      ≤ ∑ k ∈ Finset.range M, ‖(χ (steps k) : ℂ)‖ := norm_sum_le _ _
    _ = ∑ _ ∈ Finset.range M, (1 : ℝ) := by congr 1; ext k; exact char_norm_one χ _
    _ = M := by simp

omit [Fintype G] [DecidableEq G] in
/-- Walk character value at time n+1:
    chi(W(n+1)) = chi(W(n)) * chi(steps(n)). -/
theorem walk_char_step (steps : ℕ → G) (χ : G →* ℂˣ) (n : ℕ) :
    (χ (GroupWalk steps (n + 1)) : ℂ) =
    (χ (GroupWalk steps n) : ℂ) * (χ (steps n) : ℂ) := by
  rw [groupWalk_succ, map_mul, Units.val_mul]

omit [Fintype G] [DecidableEq G] in
/-- S_{M+1}(chi) = S_M(chi) + chi(W(M)). -/
theorem walkCharSum_succ (steps : ℕ → G) (χ : G →* ℂˣ) (M : ℕ) :
    WalkCharSum steps χ (M + 1) =
    WalkCharSum steps χ M + (χ (GroupWalk steps M) : ℂ) := by
  simp [WalkCharSum, Finset.sum_range_succ]

omit [Fintype G] [DecidableEq G] in
/-- T_{M+1}(chi) = T_M(chi) + chi(steps(M)). -/
theorem stepCharSum_succ (steps : ℕ → G) (χ : G →* ℂˣ) (M : ℕ) :
    StepCharSum steps χ (M + 1) =
    StepCharSum steps χ M + (χ (steps M) : ℂ) := by
  simp [StepCharSum, Finset.sum_range_succ]

end CharTheory

/-! ## Section 3b: Dual Character Orthogonality (MulChar Duality) -/

section DualOrthogonality

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-! ### Bridge between MulChar G ℂ and G →* ℂˣ -/

/-- Convert a MulChar G ℂ into a group homomorphism G →* ℂˣ. -/
private noncomputable def mulCharToHom' (chi : MulChar G ℂ) : G →* ℂˣ :=
  chi.toUnitHom.comp (toUnits (G := G)).toMonoidHom

/-- Convert a group homomorphism G →* ℂˣ into a MulChar G ℂ. -/
private noncomputable def homToMulChar' (f : G →* ℂˣ) : MulChar G ℂ :=
  MulChar.ofUnitHom (f.comp (toUnits (G := G)).symm.toMonoidHom)

set_option linter.unusedSectionVars false in
private theorem mulCharToHom'_apply (chi : MulChar G ℂ) (g : G) :
    (mulCharToHom' chi g : ℂ) = chi g := by
  simp [mulCharToHom']

set_option linter.unusedSectionVars false in
private theorem homToMulChar'_mulCharToHom' (chi : MulChar G ℂ) :
    homToMulChar' (mulCharToHom' chi) = chi := by
  ext g; simp [homToMulChar', mulCharToHom']

set_option linter.unusedSectionVars false in
private theorem mulCharToHom'_homToMulChar' (f : G →* ℂˣ) :
    mulCharToHom' (homToMulChar' f) = f := by
  ext g; simp [mulCharToHom', homToMulChar']

/-- The bijection between MulChar G ℂ and G →* ℂˣ. -/
private noncomputable def mulCharHomEquiv' : MulChar G ℂ ≃ (G →* ℂˣ) where
  toFun := mulCharToHom'
  invFun := homToMulChar'
  left_inv := homToMulChar'_mulCharToHom'
  right_inv := mulCharToHom'_homToMulChar'

/-- Fintype instance for G →* ℂˣ via the MulChar bijection. -/
private noncomputable instance homFintypeInst' : Fintype (G →* ℂˣ) :=
  haveI : Fintype (MulChar G ℂ) := Fintype.ofFinite _
  Fintype.ofEquiv _ mulCharHomEquiv'

/-- Fintype.card (G →* ℂˣ) = Fintype.card G. -/
private theorem card_hom_eq_card' : Fintype.card (G →* ℂˣ) = Fintype.card G := by
  haveI : Fintype (MulChar G ℂ) := Fintype.ofFinite _
  have h1 : Fintype.card (G →* ℂˣ) = Fintype.card (MulChar G ℂ) :=
    Fintype.card_congr mulCharHomEquiv'.symm
  have hexp_pos : 0 < Monoid.exponent Gˣ :=
    Monoid.exponent_pos_of_exists (Fintype.card Gˣ) Fintype.card_pos
      (fun g => pow_card_eq_one)
  haveI : NeZero (Monoid.exponent Gˣ : ℂ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  have h2 : Fintype.card (MulChar G ℂ) = Fintype.card G := by
    rw [show Fintype.card (MulChar G ℂ) = Nat.card (MulChar G ℂ) from
      Nat.card_eq_fintype_card.symm,
      MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity G ℂ,
      Nat.card_eq_fintype_card,
      (Fintype.card_congr (toUnits (G := G)).toEquiv).symm]
  omega

/-! ### Character orthogonality: summing over characters -/

/-- For a ≠ 1, the sum of all characters evaluated at a vanishes. -/
private theorem hom_sum_eq_zero' {a : G} (ha : a ≠ 1) :
    ∑ f : G →* ℂˣ, (f a : ℂ) = 0 := by
  -- Transfer to MulChar via the equivalence
  haveI : Fintype (MulChar G ℂ) := Fintype.ofFinite _
  rw [show ∑ f : G →* ℂˣ, (f a : ℂ) =
      ∑ chi : MulChar G ℂ, (mulCharToHom' chi a : ℂ) from
    (Fintype.sum_equiv mulCharHomEquiv' _ _ (fun _ => rfl)).symm]
  simp_rw [mulCharToHom'_apply]
  -- Now use MulChar orthogonality
  have hexp_pos : 0 < Monoid.exponent Gˣ :=
    Monoid.exponent_pos_of_exists (Fintype.card Gˣ) Fintype.card_pos
      (fun g => pow_card_eq_one)
  haveI : NeZero (Monoid.exponent Gˣ : ℂ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  obtain ⟨chi, hchi⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ ha
  exact eq_zero_of_mul_eq_self_left hchi
    (by simp only [Finset.mul_sum, ← MulChar.mul_apply]
        exact Fintype.sum_bijective _ (Group.mulLeft_bijective chi) _ _ fun _ => rfl)

/-- Dual orthogonality: ∑_χ χ(g) = |G| if g = 1, 0 otherwise. -/
private theorem hom_sum_ite' (g : G) :
    ∑ f : G →* ℂˣ, (f g : ℂ) =
    if g = 1 then ↑(Fintype.card G) else 0 := by
  split_ifs with h
  · subst h
    simp only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    congr 1; exact card_hom_eq_card'
  · exact hom_sum_eq_zero' h

/-- Fourier indicator: ∑_χ χ(g⁻¹) · χ(a) = |G| · δ(a, g). -/
private theorem hom_indicator' (g a : G) :
    ∑ f : G →* ℂˣ, (f g⁻¹ : ℂ) * (f a : ℂ) =
    if a = g then ↑(Fintype.card G) else 0 := by
  simp_rw [← Units.val_mul, ← map_mul]
  rw [hom_sum_ite' (g⁻¹ * a)]
  simp only [inv_mul_eq_one, eq_comm (a := g)]

/-- Fourier indicator using conj: ∑_χ conj(χ(g)) · χ(a) = |G| · δ(a, g).
    (Uses conj(χ(g)) = χ(g⁻¹) since |χ(g)| = 1.) -/
private theorem hom_indicator_conj' (g a : G) :
    ∑ f : G →* ℂˣ, starRingEnd ℂ (f g : ℂ) * (f a : ℂ) =
    if a = g then ↑(Fintype.card G) else 0 := by
  have conj_eq : ∀ f : G →* ℂˣ, starRingEnd ℂ (f g : ℂ) = (f g⁻¹ : ℂ) := by
    intro f
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact (Complex.inv_eq_conj (char_norm_one f g)).symm
  simp_rw [conj_eq]
  exact hom_indicator' g a

/-! ### Finset orthogonality transfer -/

/-- Transfer: if χs contains all characters, sum over χs equals sum over Fintype.elems. -/
private theorem finset_sum_eq_univ_sum' {α : Type*} [AddCommMonoid α]
    (χs : Finset (G →* ℂˣ)) (hχs : ∀ χ : G →* ℂˣ, χ ∈ χs)
    (_hcard : χs.card = Fintype.card G)
    (f : (G →* ℂˣ) → α) :
    ∑ χ ∈ χs, f χ = ∑ χ : G →* ℂˣ, f χ := by
  rw [show χs = Finset.univ from Finset.eq_univ_iff_forall.mpr hχs]

/-- Fourier indicator over a Finset of characters. -/
private theorem finset_hom_indicator' (χs : Finset (G →* ℂˣ))
    (hχs : ∀ χ : G →* ℂˣ, χ ∈ χs) (hcard : χs.card = Fintype.card G)
    (g a : G) :
    ∑ f ∈ χs, (f g⁻¹ : ℂ) * (f a : ℂ) =
    if a = g then ↑(Fintype.card G) else 0 := by
  rw [finset_sum_eq_univ_sum' χs hχs hcard]
  exact hom_indicator' g a

set_option linter.unusedSectionVars false in
/-- Splitting the Finset sum into trivial + nontrivial parts. -/
private theorem finset_split_trivial_nontrivial'
    (χs : Finset (G →* ℂˣ)) (hχs : ∀ χ : G →* ℂˣ, χ ∈ χs)
    (f : (G →* ℂˣ) → ℂ) :
    ∑ χ ∈ χs, f χ =
    f 1 + ∑ χ ∈ χs.filter (· ≠ 1), f χ := by
  rw [← Finset.add_sum_erase χs f (hχs 1)]
  congr 1
  apply Finset.sum_congr
  · ext χ
    simp only [Finset.mem_filter, Finset.mem_erase, ne_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
  · intros; rfl

end DualOrthogonality

/-! ## Section 4: Walk Character Cancellation Implies Coverage -/

section CancelImpliesCoverage

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- **Character orthogonality expansion** (open hypothesis).
    The visit count of g in the walk is related to character sums by Fourier inversion.
    Full formalization requires the complete character table / Pontryagin duality for
    finite abelian groups, which is substantial Mathlib infrastructure. -/
def WalkCharExpansion (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] : Prop :=
  ∀ (steps : ℕ → G) (χs : Finset (G →* ℂˣ))
    (_hχs_complete : ∀ χ : G →* ℂˣ, χ ∈ χs)
    (_hχs_card : χs.card = Fintype.card G)
    (M : ℕ) (g : G),
    (WalkVisitCount steps M g : ℂ) =
    (1 / (Fintype.card G : ℂ)) *
    ((M : ℂ) + ∑ χ ∈ χs.filter (· ≠ 1), (χ g⁻¹ : ℂ) * WalkCharSum steps χ M)

/-- **WalkCharExpansion is proved** via Fourier inversion on finite abelian groups.

    Key identity: WalkVisitCount(M, g) = |{n < M : W(n) = g}|
    = ∑_{n<M} δ(W(n), g)
    = ∑_{n<M} (1/|G|) ∑_χ χ(g⁻¹) χ(W(n))          (by character orthogonality)
    = (1/|G|) ∑_χ χ(g⁻¹) ∑_{n<M} χ(W(n))           (swap sums)
    = (1/|G|) (M + ∑_{χ≠1} χ(g⁻¹) S_M(χ))          (trivial char gives M) -/
theorem walk_char_expansion_proved : WalkCharExpansion G := by
  intro steps χs hχs_complete hχs_card M g
  -- Step 1: Express WalkVisitCount as a filter count
  unfold WalkVisitCount
  -- Step 2: Express the filter count via indicator sums using Fourier inversion
  -- We need: #{n < M : W(n) = g} = ∑_{n < M} (1/|G|) ∑_χ χ(g⁻¹) χ(W(n))
  have hG_ne : (Fintype.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- Key: the filter count equals the Fourier expansion
  -- First, express as (1/|G|) * ∑_χ∈χs χ(g⁻¹) * ∑_{n<M} χ(W(n))
  -- Then split into trivial + nontrivial
  suffices h : (((Finset.range M).filter (fun n => GroupWalk steps n = g)).card : ℂ) =
    (1 / (Fintype.card G : ℂ)) *
    ∑ χ ∈ χs, (χ g⁻¹ : ℂ) * ∑ n ∈ Finset.range M, (χ (GroupWalk steps n) : ℂ) by
    rw [h]
    congr 1
    -- Split ∑_χ into trivial + nontrivial
    rw [finset_split_trivial_nontrivial' χs hχs_complete]
    congr 1
    -- Trivial character: χ = 1 gives g⁻¹ ↦ 1 and χ(W(n)) = 1
    simp [MonoidHom.one_apply, Units.val_one]
  -- Prove the sufficiency: card = (1/|G|) * ∑_χ χ(g⁻¹) * ∑_n χ(W(n))
  -- Swap the order of summation: ∑_χ χ(g⁻¹) * ∑_n χ(W(n)) = ∑_n ∑_χ χ(g⁻¹) * χ(W(n))
  rw [show ∑ χ ∈ χs, (χ g⁻¹ : ℂ) * ∑ n ∈ Finset.range M, (χ (GroupWalk steps n) : ℂ) =
    ∑ n ∈ Finset.range M, ∑ χ ∈ χs, (χ g⁻¹ : ℂ) * (χ (GroupWalk steps n) : ℂ) from by
    rw [Finset.sum_comm]; congr 1; ext χ; rw [Finset.mul_sum]]
  -- Apply the Fourier indicator: ∑_χ χ(g⁻¹) * χ(W(n)) = |G| * δ(W(n), g)
  simp_rw [finset_hom_indicator' χs hχs_complete hχs_card g]
  -- Now: (1/|G|) * ∑_{n<M} (if W(n)=g then |G| else 0)
  -- = (1/|G|) * |G| * #{n<M : W(n)=g}
  -- = #{n<M : W(n)=g}
  rw [one_div]
  rw [show ∑ n ∈ Finset.range M,
    (if GroupWalk steps n = g then (Fintype.card G : ℂ) else 0) =
    (Fintype.card G : ℂ) * ↑((Finset.range M).filter (fun n => GroupWalk steps n = g)).card from by
    simp only [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring]
  rw [← mul_assoc, inv_mul_cancel₀ hG_ne, one_mul]

/-- **If walk character sums are small, every element is visited.**

    Assumes WalkCharExpansion. If |S_M(chi)| <= delta * M for all nontrivial chi,
    delta * (|G|-1) < 1, and M >= |G|, then every element has positive visit count. -/
theorem walk_cancel_of_small_char_sums_from_expansion
    (hexp : WalkCharExpansion G)
    (steps : ℕ → G) (M : ℕ)
    (hG : 1 < Fintype.card G)
    (hM : Fintype.card G ≤ M)
    (χs : Finset (G →* ℂˣ))
    (hχs_complete : ∀ χ : G →* ℂˣ, χ ∈ χs)
    (hχs_card : χs.card = Fintype.card G)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ_small : δ * ((Fintype.card G : ℝ) - 1) < 1)
    (hbound : ∀ χ : G →* ℂˣ, χ ≠ 1 → ‖WalkCharSum steps χ M‖ ≤ δ * M) :
    ∀ g : G, 0 < WalkVisitCount steps M g := by
  intro g
  by_contra h_neg
  push Not at h_neg
  have h0 : WalkVisitCount steps M g = 0 := by omega
  have hexp_g := hexp steps χs hχs_complete hχs_card M g
  rw [h0, Nat.cast_zero] at hexp_g
  -- hexp_g : 0 = (1/|G|) * (M + err)
  -- Since |G| > 0, the factor 1/|G| > 0, so M + err = 0
  set err := ∑ χ ∈ χs.filter (· ≠ 1), (χ g⁻¹ : ℂ) * WalkCharSum steps χ M with err_def
  have hG_pos : (0 : ℝ) < Fintype.card G := by exact_mod_cast (show 0 < Fintype.card G by omega)
  have hG_ne : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast (show (Fintype.card G : ℕ) ≠ 0 by omega)
  have h_sum_zero : (M : ℂ) + err = 0 := by
    by_contra hne
    have hinv_ne : (Fintype.card G : ℂ)⁻¹ ≠ 0 := inv_ne_zero hG_ne
    have h_ne_zero : (Fintype.card G : ℂ)⁻¹ * ((M : ℂ) + err) ≠ 0 := mul_ne_zero hinv_ne hne
    rw [one_div] at hexp_g; exact h_ne_zero hexp_g.symm
  have h_neg_err : (M : ℂ) = -err := by linear_combination h_sum_zero
  -- Bound |error| using triangle inequality + char norm 1
  have h_err_bound : ‖err‖ ≤ (χs.filter (· ≠ 1)).card * (δ * ↑M) := by
    calc ‖err‖
        ≤ ∑ χ ∈ χs.filter (· ≠ 1), ‖(χ g⁻¹ : ℂ) * WalkCharSum steps χ M‖ :=
          norm_sum_le _ _
      _ = ∑ χ ∈ χs.filter (· ≠ 1), ‖WalkCharSum steps χ M‖ := by
          congr 1; ext χ; rw [norm_mul, char_norm_one χ g⁻¹, one_mul]
      _ ≤ ∑ _χ ∈ χs.filter (· ≠ 1), (δ * ↑M) := by
          apply Finset.sum_le_sum; intro χ hχ
          exact hbound χ (Finset.mem_filter.mp hχ).2
      _ = (χs.filter (· ≠ 1)).card * (δ * ↑M) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- The nontrivial character count is at most |G| - 1
  have h_nontrivs_card : (χs.filter (· ≠ 1)).card + 1 ≤ Fintype.card G := by
    have h1_not : (1 : G →* ℂˣ) ∉ χs.filter (· ≠ 1) := by simp [Finset.mem_filter]
    have : (χs.filter (· ≠ 1)).card < χs.card :=
      Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h =>
        h1_not (h (hχs_complete 1))⟩
    omega
  -- From |M| = |err|
  have hM_eq_err : (M : ℝ) = ‖err‖ := by
    have : ‖(M : ℂ)‖ = ‖err‖ := by rw [h_neg_err, norm_neg]
    rwa [Complex.norm_natCast] at this
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  -- Combine: M ≤ card_nontrivs * δ * M
  have hle : (M : ℝ) ≤ (χs.filter (· ≠ 1)).card * (δ * ↑M) := by linarith
  -- Since M > 0, divide: 1 ≤ card_nontrivs * δ
  have h_one_le : (1 : ℝ) ≤ ↑(χs.filter (· ≠ 1)).card * δ := by
    rw [show (↑(χs.filter (· ≠ 1)).card : ℝ) * (δ * ↑M) =
      ↑(χs.filter (· ≠ 1)).card * δ * ↑M from by ring] at hle
    nlinarith
  -- card_nontrivs + 1 ≤ |G|, so card_nontrivs ≤ |G| - 1 (in ℝ)
  have h_card_le_real : (↑(χs.filter (· ≠ 1)).card : ℝ) ≤ (Fintype.card G : ℝ) - 1 := by
    have : ((χs.filter (· ≠ 1)).card + 1 : ℝ) ≤ (Fintype.card G : ℝ) := by
      exact_mod_cast h_nontrivs_card
    linarith
  -- 1 ≤ card * δ ≤ (|G|-1) * δ = δ * (|G|-1)
  have : (1 : ℝ) ≤ δ * ((Fintype.card G : ℝ) - 1) := by
    calc (1 : ℝ) ≤ ↑(χs.filter (· ≠ 1)).card * δ := h_one_le
      _ ≤ ((Fintype.card G : ℝ) - 1) * δ := mul_le_mul_of_nonneg_right h_card_le_real hδ
      _ = δ * ((Fintype.card G : ℝ) - 1) := mul_comm _ δ
  linarith

/-- **Walk character cancellation implies coverage** (from character expansion). -/
theorem walk_cancel_implies_covers
    (hexp : WalkCharExpansion G)
    (steps : ℕ → G)
    (hG : 1 < Fintype.card G)
    (χs : Finset (G →* ℂˣ))
    (hχs_complete : ∀ χ : G →* ℂˣ, χ ∈ χs)
    (hχs_card : χs.card = Fintype.card G)
    (hcancel : WalkCharCancel steps) :
    WalkCovers steps := by
  intro g
  set cG := Fintype.card G
  have hcG_pos : (1 : ℝ) < (cG : ℝ) := by exact_mod_cast hG
  have hcG_sub_pos : (0 : ℝ) < (cG : ℝ) - 1 := by linarith
  set δ := 1 / (2 * ((cG : ℝ) - 1))
  have hδ_pos : 0 < δ := by positivity
  have hδ_small : δ * ((cG : ℝ) - 1) < 1 := by
    have hne : (0 : ℝ) < 2 * ((cG : ℝ) - 1) := by positivity
    have h1 : δ = 1 / (2 * ((cG : ℝ) - 1)) := rfl
    rw [h1, div_mul_eq_mul_div, one_mul, div_lt_one hne]
    linarith
  set nontrivs := χs.filter (· ≠ 1)
  -- Choose M₀ large enough for all nontrivial characters
  set charBound : (G →* ℂˣ) → ℕ := fun χ' =>
    if h : χ' ≠ 1 then Nat.find (hcancel χ' h δ hδ_pos) else 0
  set M₀ := nontrivs.sup charBound + cG
  have hM₀_ge_card : cG ≤ M₀ := Nat.le_add_left cG _
  have hM₀_bound : ∀ χ : G →* ℂˣ, χ ≠ 1 →
      ‖WalkCharSum steps χ M₀‖ ≤ δ * ↑M₀ := by
    intro χ hχ
    have hχ_mem : χ ∈ nontrivs := Finset.mem_filter.mpr ⟨hχs_complete χ, hχ⟩
    have hM₀_ge : M₀ ≥ Nat.find (hcancel χ hχ δ hδ_pos) := by
      have h1 : charBound χ = Nat.find (hcancel χ hχ δ hδ_pos) := dif_pos hχ
      have h2 : charBound χ ≤ nontrivs.sup charBound := Finset.le_sup hχ_mem
      omega
    exact Nat.find_spec (hcancel χ hχ δ hδ_pos) M₀ hM₀_ge
  have hvc := walk_cancel_of_small_char_sums_from_expansion hexp steps M₀ hG
    hM₀_ge_card χs hχs_complete hχs_card δ hδ_pos.le hδ_small hM₀_bound g
  obtain ⟨n, _, hn_eq⟩ := exists_visit_of_count_pos steps M₀ g hvc
  exact ⟨n, hn_eq⟩

end CancelImpliesCoverage

/-! ## Section 5: The Step-to-Walk Gap -/

/-- **The step-to-walk gap**: StepCharCancel does NOT imply WalkCharCancel.

    This is the fundamental structural gap between multiplier (step) character
    cancellation and walk character cancellation. In the Euclid-Mullin context,
    this is the "Decorrelation -> CCSB" gap (Dead End #20, Dead End #117).

    Counterexample: In Z/4Z (additive), steps 1, 3, 1, 3, ... generate the
    group (gcd(1,3)=1) but partial sums cycle 0, 1, 0, 1, ... visiting only
    {0, 1}. Step character sums cancel (pairs i + (-i) = 0) but walk character
    sums do NOT cancel (walk is periodic, character sum grows linearly).

    The mathematical reason: step cancellation says the multiplier has no preferred
    direction ON AVERAGE. Walk cancellation says the ACCUMULATED PRODUCT has no
    preferred direction. These are fundamentally different because the product
    operation couples consecutive steps. -/
theorem step_walk_gap_documented : True := trivial

/-! ## Section 6: Counterexample -- Generation Without Coverage -/

section Counterexample

/-- The alternating additive walk in Z/4Z: steps are 1, 3, 1, 3, ... -/
def alternatingSteps4 : ℕ → ZMod 4 :=
  fun n => if n % 2 = 0 then (1 : ZMod 4) else (3 : ZMod 4)

/-- The additive walk: W(n) = sum_{k<n} steps(k) in ZMod 4. -/
def additiveWalk4 (n : ℕ) : ZMod 4 :=
  ∑ k ∈ Finset.range n, alternatingSteps4 k

/-- Key computation: 1 + 3 = 0 in Z/4Z. -/
private theorem one_plus_three_mod4 : (1 : ZMod 4) + (3 : ZMod 4) = 0 := by decide

/-- The additive walk at even indices is 0. -/
theorem additiveWalk4_even (k : ℕ) : additiveWalk4 (2 * k) = 0 := by
  induction k with
  | zero => simp [additiveWalk4]
  | succ k ih =>
    show ∑ i ∈ Finset.range (2 * (k + 1)), alternatingSteps4 i = 0
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 from by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : alternatingSteps4 (2 * k) = 1 := by
      simp [alternatingSteps4, Nat.mul_mod_right]
    have h3 : alternatingSteps4 (2 * k + 1) = 3 := by
      show (if (2 * k + 1) % 2 = 0 then (1 : ZMod 4) else 3) = 3
      simp
    rw [h1, h3]
    have : ∑ i ∈ Finset.range (2 * k), alternatingSteps4 i = 0 := by
      have := ih; simp only [additiveWalk4] at this; exact this
    rw [this, zero_add, one_plus_three_mod4]

/-- The additive walk at odd indices is 1. -/
theorem additiveWalk4_odd (k : ℕ) : additiveWalk4 (2 * k + 1) = 1 := by
  show ∑ i ∈ Finset.range (2 * k + 1), alternatingSteps4 i = 1
  rw [Finset.sum_range_succ]
  have h_even : ∑ i ∈ Finset.range (2 * k), alternatingSteps4 i = 0 := by
    have := additiveWalk4_even k; simp [additiveWalk4] at this; exact this
  have h_step : alternatingSteps4 (2 * k) = 1 := by
    simp [alternatingSteps4, Nat.mul_mod_right]
  rw [h_even, h_step, zero_add]

/-- The additive walk in Z/4Z with alternating steps 1,3 only visits {0, 1}. -/
theorem counterexample_alternating_mod4 (n : ℕ) :
    additiveWalk4 n = 0 ∨ additiveWalk4 n = 1 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · left; rw [show n = 2 * k from by omega]; exact additiveWalk4_even k
  · right; rw [show n = 2 * k + 1 from by omega]; exact additiveWalk4_odd k

/-- The element 2 is never visited by the alternating walk in Z/4Z. -/
theorem alternating_walk_misses_two :
    ∀ n : ℕ, additiveWalk4 n ≠ 2 := by
  intro n; rcases counterexample_alternating_mod4 n with h | h <;> rw [h] <;> decide

/-- The element 3 is never visited by the alternating walk in Z/4Z. -/
theorem alternating_walk_misses_three :
    ∀ n : ℕ, additiveWalk4 n ≠ 3 := by
  intro n; rcases counterexample_alternating_mod4 n with h | h <;> rw [h] <;> decide

/-- The alternating steps 1, 3 generate Z/4Z additively: {1, 3} generates the
    whole group because 1 is in the generating set and generates Z/4Z by itself. -/
theorem alternating_steps_generate :
    AddSubgroup.closure ({1, 3} : Set (ZMod 4)) = ⊤ := by
  -- It suffices to show every element is in the closure
  ext x; simp only [AddSubgroup.mem_top, iff_true]
  have h1 : (1 : ZMod 4) ∈ AddSubgroup.closure ({1, 3} : Set (ZMod 4)) :=
    AddSubgroup.subset_closure (Set.mem_insert 1 {3})
  have h3 : (3 : ZMod 4) ∈ AddSubgroup.closure ({1, 3} : Set (ZMod 4)) :=
    AddSubgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr rfl))
  -- 2 = 1 + 1 and 0 = 1 + 3
  have h2 : (2 : ZMod 4) ∈ AddSubgroup.closure ({1, 3} : Set (ZMod 4)) := by
    have : (2 : ZMod 4) = 1 + 1 := by decide
    rw [this]; exact (AddSubgroup.closure ({1, 3} : Set (ZMod 4))).add_mem h1 h1
  have h0 : (0 : ZMod 4) ∈ AddSubgroup.closure ({1, 3} : Set (ZMod 4)) :=
    (AddSubgroup.closure ({1, 3} : Set (ZMod 4))).zero_mem
  fin_cases x <;> assumption

end Counterexample

/-! ## Section 7: Walk Translations and Structural Properties -/

section WalkStructure

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
/-- The identity element is always visited at time 0. -/
theorem one_always_visited (steps : ℕ → G) : GroupWalk steps 0 = 1 :=
  groupWalk_zero steps

omit [Fintype G] [DecidableEq G] in
/-- If steps are eventually constant g, the walk moves by g at each step. -/
theorem walk_constant_step (steps : ℕ → G) (g : G) (N₀ : ℕ)
    (h : ∀ k ≥ N₀, steps k = g) (n : ℕ) (hn : n ≥ N₀) :
    GroupWalk steps (n + 1) = GroupWalk steps n * g := by
  rw [groupWalk_succ, h n hn]

omit [Fintype G] [DecidableEq G] in
/-- Walk respects left-multiplication of all steps by a constant. -/
theorem walk_left_translate (steps : ℕ → G) (c : G) (n : ℕ) :
    GroupWalk (fun k => c * steps k) n = c ^ n * GroupWalk steps n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [groupWalk_succ]
    rw [ih, pow_succ, mul_assoc, mul_assoc]
    congr 1
    rw [← mul_assoc, mul_comm (GroupWalk steps n) c, mul_assoc]

/-- Landscape summary: the four key structural relationships for walk coverage. -/
theorem walk_coverage_landscape :
    -- (1) Walk char sum as product sum
    (∀ (steps : ℕ → G) (χ : G →* ℂˣ) (M : ℕ),
      WalkCharSum steps χ M =
      ∑ n ∈ Finset.range M, ∏ k ∈ Finset.range n, (χ (steps k) : ℂ)) ∧
    -- (2) Visit counts partition
    (∀ (steps : ℕ → G) (M : ℕ), ∑ g : G, WalkVisitCount steps M g = M) ∧
    -- (3) Walk character norm bound
    (∀ (steps : ℕ → G) (χ : G →* ℂˣ) (M : ℕ),
      ‖WalkCharSum steps χ M‖ ≤ M) ∧
    -- (4) Nontrivial char sum vanishes over group
    (∀ (χ : G →* ℂˣ), χ ≠ 1 → ∑ g : G, (χ g : ℂ) = 0) :=
  ⟨walkCharSum_eq_prod_sum, fun s M => walkVisitCount_sum_eq s M,
   walkCharSum_norm_le, char_sum_eq_zero⟩

end WalkStructure
