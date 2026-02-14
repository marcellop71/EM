import EM.Advanced.VanishingNoise
import Mathlib.NumberTheory.MulChar.Duality

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter



/-! ## Part 9: Mean Character Value and Averaged Character Product

We define the **mean character value** over a Finset and prove basic norm bounds.
The **averaged character product** telescopes these over multiple steps. -/

section MeanCharValue

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- The mean character value over a Finset: (1/|S|) * sum_{s in S} chi(s). -/
def meanCharValue (chi : G →* ℂˣ) (S : Finset G) : ℂ :=
  (∑ s ∈ S, (chi s : ℂ)) / ↑S.card

omit [DecidableEq G] in
/-- The mean character value has norm at most 1 for any nonempty Finset.
    Proof: triangle inequality gives |sum chi(s)| <= sum |chi(s)| = |S|, divide by |S|. -/
theorem meanCharValue_norm_le_one (chi : G →* ℂˣ) (S : Finset G)
    (hne : S.Nonempty) :
    ‖meanCharValue chi S‖ ≤ 1 := by
  simp only [meanCharValue]
  have hcard_pos : (0 : ℝ) < ↑S.card := by positivity
  rw [Complex.norm_div, Complex.norm_natCast, div_le_one hcard_pos]
  calc ‖∑ s ∈ S, (chi s : ℂ)‖
      ≤ ∑ s ∈ S, ‖(chi s : ℂ)‖ := norm_sum_le S _
    _ = ∑ s ∈ S, (1 : ℝ) := by congr 1; ext s; exact char_norm_one_of_hom chi s
    _ = ↑S.card := by simp

/-- If there exist s, t in S with chi(s) != chi(t), the mean character value
    has norm strictly less than 1.
    Proof: spectral_gap_of_distinct_values gives |sum| < |S|, divide by |S|. -/
theorem meanCharValue_norm_lt_one_of_distinct (chi : G →* ℂˣ) (S : Finset G)
    (hcard : 2 ≤ S.card)
    (hdist : ∃ s ∈ S, ∃ t ∈ S, (chi s : ℂ) ≠ (chi t : ℂ)) :
    ‖meanCharValue chi S‖ < 1 := by
  simp only [meanCharValue]
  have hcard_pos : (0 : ℝ) < ↑S.card := by positivity
  rw [Complex.norm_div, Complex.norm_natCast, div_lt_one hcard_pos]
  exact spectral_gap_of_distinct_values chi S hcard hdist

end MeanCharValue


/-! ## Part 10: Averaged Character Product -/

section AvgCharProduct

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- The product of mean character values over N steps. -/
def avgCharProduct (chi : G →* ℂˣ) (S : ℕ → Finset G) (N : ℕ) : ℂ :=
  ∏ k ∈ Finset.range N, meanCharValue chi (S k)

omit [Fintype G] [DecidableEq G] in
/-- Norm of the averaged character product is bounded by the product of norms.
    Uses the fact that C is a normed field, so |prod z_k| = prod |z_k|. -/
theorem avgCharProduct_norm_eq (chi : G →* ℂˣ) (S : ℕ → Finset G) (N : ℕ) :
    ‖avgCharProduct chi S N‖ = ∏ k ∈ Finset.range N, ‖meanCharValue chi (S k)‖ := by
  simp only [avgCharProduct]
  exact norm_prod (Finset.range N) _

omit [DecidableEq G] in
/-- If all S(k) are nonempty, the averaged character product has norm at most 1. -/
theorem avgCharProduct_norm_le_one (chi : G →* ℂˣ) (S : ℕ → Finset G)
    (hne : ∀ k, (S k).Nonempty) (N : ℕ) :
    ‖avgCharProduct chi S N‖ ≤ 1 := by
  rw [avgCharProduct_norm_eq]
  apply Finset.prod_le_one
  · intro k _; exact norm_nonneg _
  · intro k hk
    exact meanCharValue_norm_le_one chi (S k) (hne k)

end AvgCharProduct


/-! ## Part 11: Product Contraction Implies Averaged Sums Vanish -/

section AvgContraction

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
/-- If the spectral gaps gamma_k = 1 - |meanCharValue chi (S k)| are all positive
    and their sum diverges, then the averaged character product tends to 0 in norm.

    Proof: |avgCharProduct| = prod |meanCharValue| = prod (1 - gamma_k) -> 0
    by product_contraction_tendsto. -/
theorem avgCharProduct_tendsto_zero (chi : G →* ℂˣ) (S : ℕ → Finset G)
    (hgap_pos : ∀ k, 0 < 1 - ‖meanCharValue chi (S k)‖)
    (hgap_le : ∀ k, 1 - ‖meanCharValue chi (S k)‖ ≤ 1)
    (hdiv : ¬Summable (fun k => 1 - ‖meanCharValue chi (S k)‖)) :
    Filter.Tendsto (fun N => ‖avgCharProduct chi S N‖) Filter.atTop (nhds 0) := by
  -- Rewrite |avgCharProduct| = prod (1 - gamma_k)
  have heq : ∀ N, ‖avgCharProduct chi S N‖ =
      ∏ k ∈ Finset.range N, (1 - (1 - ‖meanCharValue chi (S k)‖)) := by
    intro N
    rw [avgCharProduct_norm_eq]
    congr 1; ext k; ring
  simp_rw [heq]
  simp_rw [show ∀ k, 1 - (1 - ‖meanCharValue chi (S k)‖) = ‖meanCharValue chi (S k)‖
    from fun k => by ring]
  -- Now we need: prod ‖meanCharValue‖ -> 0
  -- This is prod (1 - gamma) -> 0 with gamma = 1 - ‖meanCharValue‖
  -- Rewrite back
  have heq2 : ∀ N, ∏ k ∈ Finset.range N, ‖meanCharValue chi (S k)‖ =
      ∏ k ∈ Finset.range N, (1 - (1 - ‖meanCharValue chi (S k)‖)) := by
    intro N; congr 1; ext k; ring
  simp_rw [heq2]
  exact product_contraction_tendsto _ hgap_pos hgap_le hdiv

end AvgContraction


/-! ## Part 12: Proper InfinitelyManyLargeFactorSets and Product Multiset -/

section IMLFS

variable {q : ℕ} [Fact (Nat.Prime q)]

/-- **InfinitelyManyLargeFactorSets'**: For each prime q, infinitely many steps n
    have at least 2 distinct factor set residues mod q.
    This ensures the spectral gap gives strict contraction infinitely often. -/
def InfinitelyManyLargeFactorSets' (q : ℕ) [Fact (Nat.Prime q)] : Prop :=
  ∀ N : ℕ, ∃ n, N ≤ n ∧ 2 ≤ (factorSetResidues (q := q) n).card

end IMLFS


/-! ## Part 13: Product Multiset and Character Sum Identity

We define the multiset of all achievable products from selecting one element
from each of S(0), ..., S(N-1), and prove the key character sum factorization
identity by induction. -/

section ProductMultiset

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- The multiset of all achievable products from selecting one element
    from each of S(0), ..., S(N-1).
    - N = 0: the multiset is {1}
    - N + 1: for each g in the N-step multiset and each s in S(N), form g * s -/
def productMultiset (S : ℕ → Finset G) : ℕ → Multiset G
  | 0 => {1}
  | n + 1 => (productMultiset S n).bind (fun g => (S n).val.map (fun s => g * s))

omit [Fintype G] [DecidableEq G] in
/-- The cardinality of the product multiset equals the product of set sizes. -/
theorem productMultiset_card (S : ℕ → Finset G) :
    ∀ N, Multiset.card (productMultiset S N) =
      ∏ k ∈ Finset.range N, (S k).card := by
  intro N
  induction N with
  | zero => simp [productMultiset]
  | succ n ih =>
    simp only [productMultiset, Finset.prod_range_succ]
    rw [Multiset.card_bind]
    -- card o f = const (S n).card since f maps each g to (S n).val.map (g * ·)
    have hconst : Multiset.map (Multiset.card ∘ fun g => Multiset.map (fun s => g * s) (S n).val)
        (productMultiset S n) =
        Multiset.map (fun _ => (S n).card) (productMultiset S n) := by
      congr 1; ext g
      simp only [Function.comp, Multiset.card_map, Finset.card_val]
    rw [hconst, Multiset.map_const', Multiset.sum_replicate, ih, smul_eq_mul, mul_comm]

omit [Fintype G] [DecidableEq G] in
/-- **Character sum factorization**: The sum of chi over the product multiset
    equals the product of per-step character sums.

    This is the key identity: sum_{sigma} chi(prod sigma) = prod_k (sum_{s in S_k} chi(s)).

    Proof by induction on N:
    - N = 0: both sides are 1 (chi(1) = 1 and empty product = 1)
    - N + 1: expand the bind, use multiplicativity of chi and factor out -/
theorem char_sum_productMultiset (chi : G →* ℂˣ) (S : ℕ → Finset G) :
    ∀ N, ((productMultiset S N).map (fun g => (chi g : ℂ))).sum =
      ∏ k ∈ Finset.range N, (∑ s ∈ S k, (chi s : ℂ)) := by
  intro N
  induction N with
  | zero =>
    simp [productMultiset, map_one chi, Units.val_one]
  | succ n ih =>
    simp only [productMultiset, Finset.prod_range_succ]
    -- Expand: multiset = bind of (product n) over (fun g => S(n).val.map (g * ·))
    rw [Multiset.map_bind]
    -- sum of bind = sum of sums
    simp only [Multiset.sum_bind]
    -- Each inner sum: for fixed g, sum over s in S(n) of chi(g * s)
    -- = chi(g) * sum chi(s)
    have inner_eq : (productMultiset S n).map
        (fun g => ((S n).val.map (fun s => g * s)).map (fun x => (chi x : ℂ)) |>.sum) =
        (productMultiset S n).map
        (fun g => (chi g : ℂ) * ∑ s ∈ S n, (chi s : ℂ)) := by
      congr 1; ext g
      simp only [Multiset.map_map, Function.comp, map_mul, Units.val_mul]
      rw [Multiset.sum_map_mul_left]
      rfl
    rw [inner_eq, Multiset.sum_map_mul_right, ih]

omit [Fintype G] [DecidableEq G] in
/-- The product multiset at step 0 is {1}. -/
theorem productMultiset_zero (S : ℕ → Finset G) :
    productMultiset S 0 = {1} := rfl

end ProductMultiset


/-! ## Part 14: Path Existence via Character Products (PROVED)

The **path existence** theorem: if for all nontrivial characters chi,
the averaged character products tend to 0, then every element of G appears
in the product multiset for large enough N.

The proof uses:
1. char_sum_productMultiset (PROVED): character sum over paths = product of per-step sums
2. Character orthogonality for MulChar G C (from Mathlib)
3. Bridge from MulChar G C to G ->* C* via toUnits
4. The Fourier counting identity: |G| * count(a, M) = sum_f conj(f(a)) * sum_{g in M} f(g)
5. When avgCharProduct -> 0, the count is eventually positive -/

section PathExistence

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-! ### Bridge between MulChar G C and G ->* C* -/

/-- Convert a MulChar G C into a group homomorphism G ->* C*. -/
noncomputable def mulCharToHom (chi : MulChar G ℂ) : G →* ℂˣ :=
  chi.toUnitHom.comp toUnits.toMonoidHom

/-- Convert a group homomorphism G ->* C* into a MulChar G C. -/
noncomputable def homToMulChar (f : G →* ℂˣ) : MulChar G ℂ :=
  MulChar.ofUnitHom (f.comp toUnits.symm.toMonoidHom)

set_option linter.unusedSectionVars false in
/-- The value of mulCharToHom at g equals the MulChar value. -/
theorem mulCharToHom_apply (chi : MulChar G ℂ) (g : G) :
    (mulCharToHom chi g : ℂ) = chi g := by
  simp [mulCharToHom]

set_option linter.unusedSectionVars false in
/-- homToMulChar is a left inverse of mulCharToHom. -/
theorem homToMulChar_mulCharToHom (chi : MulChar G ℂ) :
    homToMulChar (mulCharToHom chi) = chi := by
  ext g
  simp [homToMulChar, mulCharToHom]

set_option linter.unusedSectionVars false in
/-- mulCharToHom is a left inverse of homToMulChar. -/
theorem mulCharToHom_homToMulChar (f : G →* ℂˣ) :
    mulCharToHom (homToMulChar f) = f := by
  ext g
  simp [mulCharToHom, homToMulChar]

/-- The bijection between MulChar G C and G ->* C*. -/
noncomputable def mulCharHomEquiv : MulChar G ℂ ≃ (G →* ℂˣ) where
  toFun := mulCharToHom
  invFun := homToMulChar
  left_inv := homToMulChar_mulCharToHom
  right_inv := mulCharToHom_homToMulChar

set_option linter.unusedSectionVars false in
/-- mulCharToHom maps the trivial MulChar to the trivial hom. -/
theorem mulCharToHom_one : mulCharToHom (1 : MulChar G ℂ) = 1 := by
  have h : ∀ g : G, (mulCharToHom (1 : MulChar G ℂ) g : ℂ) = ((1 : G →* ℂˣ) g : ℂ) := by
    intro g
    rw [mulCharToHom_apply, MulChar.one_apply (Group.isUnit g)]
    simp [MonoidHom.one_apply, Units.val_one]
  ext g
  exact h g

/-- mulCharToHom preserves nontriviality. -/
theorem mulCharToHom_ne_one {chi : MulChar G ℂ} (hne : chi ≠ 1) :
    mulCharToHom chi ≠ 1 := by
  intro h
  apply hne
  have := congr_arg homToMulChar h
  rw [homToMulChar_mulCharToHom] at this
  rw [this]; rw [← mulCharToHom_one]; exact homToMulChar_mulCharToHom 1

/-- homToMulChar preserves nontriviality. -/
theorem homToMulChar_ne_one {f : G →* ℂˣ} (hne : f ≠ 1) :
    homToMulChar f ≠ 1 := by
  intro h
  apply hne
  have := congr_arg mulCharToHom h
  rw [mulCharToHom_homToMulChar] at this
  rw [this, mulCharToHom_one]

/-! ### Character Orthogonality -/

/-- Fintype instance for MulChar G C. -/
noncomputable instance mulCharFintypeInst : Fintype (MulChar G ℂ) :=
  Fintype.ofFinite _

/-- Fintype instance for G ->* C* via the bijection. -/
private noncomputable instance homFintypeInst : Fintype (G →* ℂˣ) :=
  Fintype.ofEquiv _ mulCharHomEquiv

/-- Fintype.card Gˣ = Fintype.card G for groups (every element is a unit). -/
private theorem card_units_eq_card : Fintype.card Gˣ = Fintype.card G :=
  (Fintype.card_congr (toUnits (G := G)).toEquiv).symm

/-- Fintype.card (G →* ℂˣ) = Fintype.card G via MulChar bridge. -/
private theorem card_hom_eq_card : Fintype.card (G →* ℂˣ) = Fintype.card G := by
  have h1 : Fintype.card (G →* ℂˣ) = Fintype.card (MulChar G ℂ) :=
    Fintype.card_congr mulCharHomEquiv.symm
  have hexp_pos : 0 < Monoid.exponent Gˣ :=
    Monoid.exponent_pos_of_exists (Fintype.card Gˣ) Fintype.card_pos
      (fun g => pow_card_eq_one)
  haveI : NeZero (Monoid.exponent Gˣ : ℂ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  have h2 : Fintype.card (MulChar G ℂ) = Fintype.card G := by
    rw [show Fintype.card (MulChar G ℂ) = Nat.card (MulChar G ℂ) from
      Nat.card_eq_fintype_card.symm,
      MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity G ℂ,
      Nat.card_eq_fintype_card, card_units_eq_card]
  omega

/-- NeZero instance for the exponent of Gˣ in C. -/
private theorem neZero_exponent_units :
    NeZero (Monoid.exponent Gˣ : ℂ) := by
  constructor
  have hexp_pos : 0 < Monoid.exponent Gˣ :=
    Monoid.exponent_pos_of_exists (Fintype.card Gˣ) Fintype.card_pos
      (fun g => pow_card_eq_one)
  exact Nat.cast_ne_zero.mpr (by omega)

/-- Character orthogonality for MulChar: for a != 1, sum chi(a) = 0. -/
private theorem mulChar_sum_eq_zero {a : G} (ha : a ≠ 1) :
    ∑ chi : MulChar G ℂ, chi a = 0 := by
  haveI := neZero_exponent_units (G := G)
  obtain ⟨chi, hchi⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ ha
  exact eq_zero_of_mul_eq_self_left hchi
    (by simp only [Finset.mul_sum, ← MulChar.mul_apply]
        exact Fintype.sum_bijective _ (Group.mulLeft_bijective chi) _ _ fun _ => rfl)

/-- Character orthogonality for G ->* C*: for a != 1, sum f(a) = 0. -/
private theorem hom_sum_eq_zero {a : G} (ha : a ≠ 1) :
    ∑ f : G →* ℂˣ, (f a : ℂ) = 0 := by
  rw [show ∑ f : G →* ℂˣ, (f a : ℂ) =
      ∑ chi : MulChar G ℂ, (mulCharToHom chi a : ℂ) from
    (Fintype.sum_equiv mulCharHomEquiv _ _ (fun _ => rfl)).symm]
  simp_rw [mulCharToHom_apply]
  exact mulChar_sum_eq_zero ha

/-- Combined orthogonality: sum_f f(g) = |G| if g = 1, 0 otherwise. -/
private theorem hom_sum_eq (g : G) :
    ∑ f : G →* ℂˣ, (f g : ℂ) = if g = 1 then ↑(Fintype.card G) else 0 := by
  split_ifs with h
  · subst h
    simp only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    congr 1
    exact card_hom_eq_card
  · exact hom_sum_eq_zero h

/-! ### Fourier Counting Identity -/

/-- For g, a in G, sum_f conj(f(a)) * f(g) = |G| if g = a, 0 otherwise. -/
private theorem hom_indicator_sum (a g : G) :
    ∑ f : G →* ℂˣ, starRingEnd ℂ (f a : ℂ) * (f g : ℂ) =
    if g = a then ↑(Fintype.card G) else 0 := by
  -- conj(f(a)) = f(a^{-1}) since |f(a)| = 1 implies conj = inv
  have conj_eq : ∀ f : G →* ℂˣ, starRingEnd ℂ (f a : ℂ) = (f a⁻¹ : ℂ) := by
    intro f
    rw [map_inv, Units.val_inv_eq_inv_val]
    exact (Complex.inv_eq_conj (char_norm_one_of_hom f a)).symm
  simp_rw [conj_eq, ← Units.val_mul, ← map_mul, show a⁻¹ * g = g * a⁻¹ from mul_comm _ _]
  rw [hom_sum_eq (g * a⁻¹)]
  simp only [mul_inv_eq_one]

/-- **Fourier counting identity**: for a in G and a multiset M,
    |G| * count(a, M) = sum_f conj(f(a)) * (sum_{g in M} f(g)). -/
private theorem char_count_formula (a : G) (M : Multiset G) :
    (↑(Fintype.card G) : ℂ) * ↑(Multiset.count a M) =
    ∑ f : G →* ℂˣ, starRingEnd ℂ (f a : ℂ) *
      (M.map (fun g => (f g : ℂ))).sum := by
  -- Swap sums and apply Fourier identity, by induction on M
  induction M using Multiset.induction_on with
  | empty => simp
  | cons x M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.count_cons]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← ih]
    -- LHS: |G| * ↑(count + if_indicator), RHS: (if x=a then |G| else 0) + |G| * ↑count
    -- Handle by cases on a = x
    by_cases hax : a = x
    · subst hax; simp [hom_indicator_sum]; ring
    · have hxa : ¬(x = a) := fun h => hax h.symm
      simp only [hom_indicator_sum, if_neg hxa, if_neg hax]
      ring_nf

set_option linter.unusedSectionVars false in
/-- The character sum over the product multiset equals |M_N| * avgCharProduct. -/
private theorem char_sum_eq_card_mul_avg
    (f : G →* ℂˣ) (S : ℕ → Finset G) (hne : ∀ k, (S k).Nonempty) (N : ℕ) :
    ((productMultiset S N).map (fun g => (f g : ℂ))).sum =
    ↑(Multiset.card (productMultiset S N)) * avgCharProduct f S N := by
  rw [char_sum_productMultiset, avgCharProduct, productMultiset_card]
  simp only [meanCharValue]
  -- Goal: ∏ (∑ f(s)) = ↑(∏ card) * ∏ ((∑ f(s)) / ↑card)
  have hne_card : ∀ k, (↑((S k).card) : ℂ) ≠ 0 :=
    fun k => Nat.cast_ne_zero.mpr (Finset.card_pos.mpr (hne k) |>.ne')
  induction N with
  | zero => simp
  | succ n ih =>
    simp only [Finset.prod_range_succ, Nat.cast_mul]
    rw [ih]
    -- LHS: A * B, RHS: (A₁ * card_n) * (A₂ * (B / card_n))
    -- where A = A₁ * A₂ (from ih). Just use field_simp to clear denominators.
    field_simp [hne_card n]

/-! ### Path Existence Theorem -/

/-- The original definition is now proved below. -/
def PathExistenceFromVanishing (G : Type*) [CommGroup G] [Fintype G]
    [DecidableEq G] : Prop :=
  ∀ (S : ℕ → Finset G),
    (∀ k, (S k).Nonempty) →
    (∀ k, 2 ≤ (S k).card) →
    (∀ (chi : G →* ℂˣ), chi ≠ 1 →
      Filter.Tendsto (fun N => ‖avgCharProduct chi S N‖) Filter.atTop (nhds 0)) →
    ∀ a : G, ∃ N, a ∈ (productMultiset S N).toFinset

/-- Uniform bound extraction: for finitely many tendsto-zero sequences, find N₀ such that
    all are below epsilon for N >= N₀. -/
private theorem uniform_bound_of_tendsto
    {ι : Type*} (T : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ T, Filter.Tendsto (f i) Filter.atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀, ∀ i ∈ T, ∀ N, N₀ ≤ N → f i N < ε := by
  induction T using Finset.induction_on with
  | empty => exact ⟨0, fun _ h => absurd h (by simp)⟩
  | @insert a s hna ih_ind =>
    obtain ⟨N₁, hN₁⟩ := ih_ind (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have ha_tends := hf a (Finset.mem_insert_self a s)
    rw [Metric.tendsto_atTop] at ha_tends
    obtain ⟨N₂, hN₂⟩ := ha_tends ε hε
    refine ⟨max N₁ N₂, fun i hi N hN => ?_⟩
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · have h := hN₂ N (le_of_max_le_right hN)
      rw [Real.dist_eq, sub_zero, abs_lt] at h
      exact h.2
    · exact hN₁ i hi N (le_of_max_le_left hN)

/-- **PathExistenceFromVanishing PROVED**: If the averaged character products
    tend to 0 for all nontrivial characters, then every element of G appears
    in the product multiset for sufficiently large N. -/
theorem pathExistenceFromVanishing_proved :
    PathExistenceFromVanishing G := by
  intro S hne _hcard hvanish a
  -- It suffices to show count(a, M_N) > 0 for some N
  suffices ∃ N, 0 < Multiset.count a (productMultiset S N) by
    obtain ⟨N, hN⟩ := this
    exact ⟨N, Multiset.mem_toFinset.mpr (Multiset.count_pos.mp hN)⟩
  -- Handle |G| = 1 separately
  by_cases hG1 : Fintype.card G = 1
  · -- G is trivial, so a = 1
    have ⟨d, hd⟩ := Fintype.card_eq_one_iff.mp hG1
    have ha : a = d := hd a
    have h1 : (1 : G) = d := hd 1
    use 0
    rw [productMultiset_zero]
    rw [show a = 1 from ha.trans h1.symm]
    simp
  · -- |G| >= 2
    have hcG_pos : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
    -- Collect nontrivial homs
    set nontrivHoms := (Finset.univ : Finset (G →* ℂˣ)).filter (· ≠ 1)
    -- Get uniform bound: for epsilon = 1/(2*|G|), find N₀ such that all
    -- nontrivial avgCharProduct norms are below epsilon for N >= N₀
    have heps : (0 : ℝ) < 1 / (2 * Fintype.card G) := by positivity
    -- Extract tendsto for the norms of avgCharProducts on nontrivHoms
    have htends : ∀ f ∈ nontrivHoms, Filter.Tendsto
        (fun N => ‖avgCharProduct f S N‖) Filter.atTop (nhds 0) := by
      intro f hf
      exact hvanish f (by simp [nontrivHoms] at hf; exact hf)
    obtain ⟨N₀, hN₀⟩ := uniform_bound_of_tendsto (ι := G →* ℂˣ)
      nontrivHoms (fun f N => ‖avgCharProduct f S N‖) htends
      (1 / (2 * Fintype.card G)) heps
    -- Show count(a, M_{N₀}) > 0 by contradiction
    use N₀
    -- The product multiset always has positive cardinality
    have hM_pos : 0 < Multiset.card (productMultiset S N₀) := by
      rw [productMultiset_card]
      exact Finset.prod_pos (fun k _ => Finset.card_pos.mpr (hne k))
    -- Use the Fourier identity
    by_contra hcount
    push Not at hcount
    have hcount0 : Multiset.count a (productMultiset S N₀) = 0 := by omega
    -- From char_count_formula: |G| * 0 = sum, so sum = 0
    have hident := char_count_formula (G := G) a (productMultiset S N₀)
    rw [hcount0, Nat.cast_zero, mul_zero] at hident
    -- Split the sum: trivial character + nontrivial characters
    have hsplit : ∑ f : G →* ℂˣ, starRingEnd ℂ (f a : ℂ) *
        ((productMultiset S N₀).map (fun g => (f g : ℂ))).sum =
        (↑(Multiset.card (productMultiset S N₀)) : ℂ) +
        ∑ f ∈ nontrivHoms,
          starRingEnd ℂ (f a : ℂ) *
          ((productMultiset S N₀).map (fun g => (f g : ℂ))).sum := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : G →* ℂˣ))]
      congr 1
      · -- trivial character contribution = |M|
        simp [map_one, Units.val_one, Multiset.map_const', Multiset.sum_replicate,
          nsmul_eq_mul, mul_one]
      · apply Finset.sum_congr
        · ext f; simp [nontrivHoms, Finset.mem_erase]
        · intros; rfl
    rw [hsplit] at hident
    -- So |M| = -(error term)
    set errTerm := ∑ f ∈ nontrivHoms,
      starRingEnd ℂ (f a : ℂ) *
      ((productMultiset S N₀).map (fun g => (f g : ℂ))).sum
    have hM_eq : (↑(Multiset.card (productMultiset S N₀)) : ℂ) = -errTerm := by
      -- hident : 0 = ↑card + errTerm, so card = -errTerm
      have h := hident.symm  -- ↑card + errTerm = 0
      linear_combination h
    -- Take norms: |M| = |errTerm|
    have hnorm_eq : (↑(Multiset.card (productMultiset S N₀)) : ℝ) = ‖errTerm‖ := by
      have h1 : ‖(↑(Multiset.card (productMultiset S N₀)) : ℂ)‖ = ‖errTerm‖ := by
        rw [hM_eq, norm_neg]
      rwa [Complex.norm_natCast] at h1
    -- Bound |errTerm|
    have herr_bound : ‖errTerm‖ <
        ↑(Multiset.card (productMultiset S N₀)) := by
      calc ‖errTerm‖
          ≤ ∑ f ∈ nontrivHoms,
            ‖starRingEnd ℂ (f a : ℂ) *
              ((productMultiset S N₀).map (fun g => (f g : ℂ))).sum‖ := norm_sum_le _ _
        _ = ∑ f ∈ nontrivHoms,
            ‖((productMultiset S N₀).map (fun g => (f g : ℂ))).sum‖ := by
            congr 1; ext f
            rw [norm_mul, RCLike.norm_conj, char_norm_one_of_hom f a, one_mul]
        _ = ∑ f ∈ nontrivHoms,
            ‖↑(Multiset.card (productMultiset S N₀)) * avgCharProduct f S N₀‖ := by
            congr 1; ext f
            rw [char_sum_eq_card_mul_avg f S hne N₀]
        _ = ∑ f ∈ nontrivHoms,
            (↑(Multiset.card (productMultiset S N₀)) *
              ‖avgCharProduct f S N₀‖) := by
            congr 1; ext f
            rw [Complex.norm_mul, Complex.norm_natCast]
        _ < ∑ _f ∈ nontrivHoms,
            (↑(Multiset.card (productMultiset S N₀)) *
              (1 / (2 * ↑(Fintype.card G)))) := by
            apply Finset.sum_lt_sum
            · intro f hf
              apply mul_le_mul_of_nonneg_left (le_of_lt (hN₀ f hf N₀ le_rfl))
              exact Nat.cast_nonneg _
            · -- need at least one nontrivial hom (since |G| >= 2)
              -- the character that separates a from 1 (or any nontrivial one)
              have : ∃ f ∈ nontrivHoms, True := by
                -- Need at least 2 homs, hence at least 1 nontrivial
                have hcG_ge2 : 2 ≤ Fintype.card G := by
                  have := Fintype.card_pos (α := G)
                  by_contra h; push Not at h
                  exact hG1 (show Fintype.card G = 1 by linarith)
                have h2 : 2 ≤ Fintype.card (G →* ℂˣ) := by
                  rw [card_hom_eq_card]; exact hcG_ge2
                haveI : Nontrivial (G →* ℂˣ) :=
                  Fintype.one_lt_card_iff_nontrivial.mp (by linarith)
                obtain ⟨f, hf⟩ := exists_ne (1 : G →* ℂˣ)
                exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩, trivial⟩
              obtain ⟨f₀, hf₀, _⟩ := this
              have hM_pos' : (0 : ℝ) < ↑(Multiset.card (productMultiset S N₀)) :=
                Nat.cast_pos.mpr hM_pos
              have hsmall := hN₀ f₀ hf₀ N₀ le_rfl
              exact ⟨f₀, hf₀, by nlinarith⟩
        _ = ↑nontrivHoms.card *
            (↑(Multiset.card (productMultiset S N₀)) *
              (1 / (2 * ↑(Fintype.card G)))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (↑(Fintype.card G) - 1) *
            (↑(Multiset.card (productMultiset S N₀)) *
              (1 / (2 * ↑(Fintype.card G)))) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hntcard : (nontrivHoms.card : ℝ) ≤ ↑(Fintype.card G) - 1 := by
              have heq : nontrivHoms = Finset.univ.erase (1 : G →* ℂˣ) := by
                ext f; simp [nontrivHoms, Finset.mem_erase]
              rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
                card_hom_eq_card]
              have : 1 ≤ Fintype.card G := Fintype.card_pos
              push_cast [Nat.cast_sub this]
              linarith
            exact hntcard
        _ = ↑(Multiset.card (productMultiset S N₀)) *
            ((↑(Fintype.card G) - 1) / (2 * ↑(Fintype.card G))) := by ring
        _ < ↑(Multiset.card (productMultiset S N₀)) * 1 := by
            have hM_pos' : (0 : ℝ) < ↑(Multiset.card (productMultiset S N₀)) :=
              Nat.cast_pos.mpr hM_pos
            have hcG2 : 2 ≤ Fintype.card G := by
              have := Fintype.card_pos (α := G)
              by_contra h; push Not at h
              exact hG1 (show Fintype.card G = 1 by linarith)
            have hcG : (1 : ℝ) < ↑(Fintype.card G) := by exact_mod_cast hcG2
            have hfrac : (↑(Fintype.card G) - 1) / (2 * ↑(Fintype.card G)) < (1 : ℝ) := by
              rw [div_lt_one (by positivity : (0 : ℝ) < 2 * ↑(Fintype.card G))]
              linarith
            nlinarith
        _ = ↑(Multiset.card (productMultiset S N₀)) := mul_one _
    -- Contradiction: |M| = |errTerm| and |errTerm| < |M|
    linarith

end PathExistence


/-! ## Part 15: Stochastic MC Landscape -/

section StochasticMCLandscape

/-- **Stochastic MC Landscape**: Summary of the Tier 1 framework.

    ALL PROVED (Parts 9-14):
    1. meanCharValue_norm_le_one: |mean chi S| <= 1 for nonempty S
    2. meanCharValue_norm_lt_one_of_distinct: strict when distinct chi-values exist
    3. avgCharProduct_norm_eq: |avgCharProduct| = prod |meanCharValue|
    4. avgCharProduct_norm_le_one: bounded by 1
    5. avgCharProduct_tendsto_zero: vanishes when spectral gaps diverge
    6. char_sum_productMultiset: character sum = product of per-step sums (KEY IDENTITY)
    7. productMultiset_card: |paths| = prod |S_k|
    8. PathExistenceFromVanishing: PROVED (character orthogonality + Fourier counting)

    The chain for Stochastic MC:
    IMLFS' -> spectral gap at infinitely many steps -> avgCharProduct -> 0
    -> PathExistenceFromVanishing -> exists selection to -1 -/
theorem stochastic_mc_landscape :
    -- 1. Mean char value bounded by 1
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ) (S : Finset G), S.Nonempty →
       ‖meanCharValue chi S‖ ≤ 1)
    ∧
    -- 2. Strict bound when distinct values exist
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ) (S : Finset G), 2 ≤ S.card →
       (∃ s ∈ S, ∃ t ∈ S, (chi s : ℂ) ≠ (chi t : ℂ)) →
       ‖meanCharValue chi S‖ < 1)
    ∧
    -- 3. Product norm factorization
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ) (S : ℕ → Finset G) (N : ℕ),
       ‖avgCharProduct chi S N‖ = ∏ k ∈ Finset.range N, ‖meanCharValue chi (S k)‖)
    ∧
    -- 4. Character sum factorization over product multiset
    (∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
       (chi : G →* ℂˣ) (S : ℕ → Finset G) (N : ℕ),
       ((productMultiset S N).map (fun g => (chi g : ℂ))).sum =
         ∏ k ∈ Finset.range N, (∑ s ∈ S k, (chi s : ℂ))) := by
  exact ⟨fun G _ _ _ chi S hne => meanCharValue_norm_le_one chi S hne,
         fun G _ _ _ chi S hcard hdist => meanCharValue_norm_lt_one_of_distinct chi S hcard hdist,
         fun G _ _ _ chi S N => avgCharProduct_norm_eq chi S N,
         fun G _ _ _ chi S N => char_sum_productMultiset chi S N⟩

end StochasticMCLandscape
