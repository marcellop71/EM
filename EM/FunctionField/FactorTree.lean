import EM.FunctionField.Bootstrap
import EM.FunctionField.WeakMC

/-!
# Factor Tree and Mixed MC for the Function Field EM Sequence

This file defines the factor tree, mixed selection, and GenMixedMC over F_p[t],
mirroring the integer mixed walk infrastructure in `EM/Advanced/EpsilonRandomMC.lean`.

Over F_p[t], monic irreducible polynomials play the role of primes. At each step
of the standard FF-EM walk, the smallest-degree monic irreducible factor is selected.
The mixed variant allows ANY monic irreducible factor to be selected, defining a
branching tree of possible walks.

## Main definitions

* `FFMixedSelection` -- a selection sequence choosing monic irreducible factors
* `ffMixedWalkProd` -- accumulated product under a mixed selection
* `FFMixedSelectionValid` -- validity: each selection is a monic irred factor of acc+1
* `ffMixedCaptures` -- a selection captures a target polynomial
* `FFMixedMC` -- mixed MC: every monic irreducible is capturable from every valid start
* `FFGenMixedMC` -- generalized mixed MC for all monic irreducibles
* `ffTreeReachable` -- a target is reachable in the factor tree (root or selected)

## Main results

* `ffMixedWalkProd_monic` -- accumulated product is monic under valid selection
* `ffMixedWalkProd_natDegree_pos` -- accumulated product has positive degree
* `ffMixedWalkProd_natDegree_strictMono` -- degree of acc product strictly increases
* `ffMixedSel_injective` -- valid selection is injective (no irreducible twice)
* `ff_standard_valid` -- the standard FF-EM sequence gives a valid mixed selection
* `ffmc_implies_tree_reachable_from_X` -- FFMC implies every irred is reachable from X
* `ffMixedWalkProd_coprime_succ` -- acc product and acc+1 share no irreducible factor
* `start_not_capturable` -- the starting polynomial can never be captured
-/

namespace FunctionFieldAnalog

open Polynomial Classical

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Section 1: Mixed Selection Definitions -/

/-- A mixed selection for FF-EM: at each step, choose any monic irreducible
    factor of the accumulated product + 1. -/
structure FFMixedSelection where
  /-- The selected factor at each step. -/
  sel : ℕ → Polynomial (ZMod p)

/-- The accumulated product after n steps under a mixed selection,
    starting from a given monic polynomial. -/
noncomputable def ffMixedWalkProd (start : Polynomial (ZMod p))
    (σ : FFMixedSelection p) : ℕ → Polynomial (ZMod p)
  | 0 => start
  | n + 1 => ffMixedWalkProd start σ n * σ.sel n

/-- A mixed selection is valid from a given starting point if:
    (1) start is monic with positive degree, and
    (2) at each step n, sigma.sel(n) is a monic irreducible factor of
        ffMixedWalkProd(n) + 1. -/
def FFMixedSelectionValid (start : Polynomial (ZMod p))
    (σ : FFMixedSelection p) : Prop :=
  start.Monic ∧ 0 < start.natDegree ∧
  ∀ n, IsMonicIrredFactor p (σ.sel n) (ffMixedWalkProd p start σ n + 1)

/-- A mixed selection captures a target polynomial Q if Q appears as
    a selected factor at some step. -/
def ffMixedCaptures (_start : Polynomial (ZMod p))
    (σ : FFMixedSelection p) (Q : Polynomial (ZMod p)) : Prop :=
  ∃ n, σ.sel n = Q

/-- Mixed MC at target Q: for every valid starting point,
    there exists a valid selection capturing Q. -/
def FFMixedMC (Q : Polynomial (ZMod p)) : Prop :=
  ∀ start : Polynomial (ZMod p), start.Monic → 0 < start.natDegree →
  ∃ σ : FFMixedSelection p, FFMixedSelectionValid p start σ ∧
    ffMixedCaptures p start σ Q

/-- Generalized Mixed MC: for all monic irreducible Q, FFMixedMC holds. -/
def FFGenMixedMC : Prop :=
  ∀ Q : Polynomial (ZMod p), Q.Monic → Irreducible Q → FFMixedMC p Q

/-- Q is reachable in the factor tree from start: either Q = start (root),
    or Q is captured by some valid selection from start.
    This is broader than `ffMixedCaptures` which requires Q to appear as
    a selected factor (excluding the root). -/
def ffTreeReachable (start : Polynomial (ZMod p))
    (Q : Polynomial (ZMod p)) : Prop :=
  Q = start ∨
  ∃ σ : FFMixedSelection p, FFMixedSelectionValid p start σ ∧
    ffMixedCaptures p start σ Q

/-! ## Section 2: Basic Recurrence Properties -/

variable {p}

@[simp]
theorem ffMixedWalkProd_zero (start : Polynomial (ZMod p))
    (σ : FFMixedSelection p) :
    ffMixedWalkProd p start σ 0 = start := rfl

@[simp]
theorem ffMixedWalkProd_succ (start : Polynomial (ZMod p))
    (σ : FFMixedSelection p) (n : ℕ) :
    ffMixedWalkProd p start σ (n + 1) =
      ffMixedWalkProd p start σ n * σ.sel n := rfl

/-- The root is always reachable. -/
theorem ffTreeReachable_root (start : Polynomial (ZMod p)) :
    ffTreeReachable p start start :=
  Or.inl rfl

/-! ## Section 3: Monic and Degree Properties -/

/-- The selection at each step is monic when the selection is valid. -/
theorem ffMixedSel_monic {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) (n : ℕ) :
    (σ.sel n).Monic :=
  (hv.2.2 n).1

/-- The selection at each step is irreducible when the selection is valid. -/
theorem ffMixedSel_irreducible {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) (n : ℕ) :
    Irreducible (σ.sel n) :=
  (hv.2.2 n).2.1

/-- The selection at each step divides the accumulated product + 1. -/
theorem ffMixedSel_dvd {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) (n : ℕ) :
    σ.sel n ∣ ffMixedWalkProd p start σ n + 1 :=
  (hv.2.2 n).2.2

/-- The accumulated product is monic at all steps under a valid selection. -/
theorem ffMixedWalkProd_monic {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) :
    ∀ n, (ffMixedWalkProd p start σ n).Monic := by
  intro n
  induction n with
  | zero => exact hv.1
  | succ n ih =>
    simp only [ffMixedWalkProd_succ]
    exact ih.mul (ffMixedSel_monic hv n)

/-- The selection at each step has positive degree (since it is irreducible). -/
theorem ffMixedSel_natDegree_pos {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) (n : ℕ) :
    0 < (σ.sel n).natDegree :=
  Irreducible.natDegree_pos (ffMixedSel_irreducible hv n)

/-- The accumulated product has positive degree at all steps. -/
theorem ffMixedWalkProd_natDegree_pos {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) :
    ∀ n, 0 < (ffMixedWalkProd p start σ n).natDegree := by
  intro n
  induction n with
  | zero => exact hv.2.1
  | succ n ih =>
    simp only [ffMixedWalkProd_succ]
    rw [Polynomial.Monic.natDegree_mul (ffMixedWalkProd_monic hv n)
      (ffMixedSel_monic hv n)]
    have := ffMixedSel_natDegree_pos hv n
    omega

/-- The degree of the accumulated product at step n+1 equals the degree at
    step n plus the degree of the selected factor. -/
theorem ffMixedWalkProd_natDegree_succ {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) (n : ℕ) :
    (ffMixedWalkProd p start σ (n + 1)).natDegree =
      (ffMixedWalkProd p start σ n).natDegree + (σ.sel n).natDegree := by
  simp only [ffMixedWalkProd_succ]
  exact Polynomial.Monic.natDegree_mul (ffMixedWalkProd_monic hv n)
    (ffMixedSel_monic hv n)

/-- The degree of the accumulated product is strictly increasing. -/
theorem ffMixedWalkProd_natDegree_strictMono {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) :
    StrictMono (fun n => (ffMixedWalkProd p start σ n).natDegree) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [ffMixedWalkProd_natDegree_succ hv n]
  have := ffMixedSel_natDegree_pos hv n
  omega

/-! ## Section 4: Coprimality and Injectivity -/

/-- Coprimality cascade for mixed walks: no irreducible of positive degree
    can divide both the accumulated product and the accumulated product + 1.
    This follows from the same argument as `coprimality_cascade`. -/
theorem ffMixedWalkProd_coprime_succ {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p}
    (Q : Polynomial (ZMod p)) (hQ : Irreducible Q) (n : ℕ)
    (hdvd_prod : Q ∣ ffMixedWalkProd p start σ n)
    (hdvd_succ : Q ∣ ffMixedWalkProd p start σ n + 1) : False := by
  have hdvd_one : Q ∣ 1 := by
    have h := dvd_sub hdvd_succ hdvd_prod
    simp [add_sub_cancel_left] at h
    exact h
  exact hQ.not_dvd_one hdvd_one

/-- The selection at step k divides the accumulated product at step k+1+j
    (it appears as a factor in the product). -/
theorem ffMixedSel_dvd_later_prod {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (k : ℕ) (j : ℕ) :
    σ.sel k ∣ ffMixedWalkProd p start σ (k + 1 + j) := by
  induction j with
  | zero =>
    simp only [Nat.add_zero, ffMixedWalkProd_succ]
    exact dvd_mul_left _ _
  | succ j ih =>
    have heq : k + 1 + (j + 1) = (k + 1 + j) + 1 := by omega
    rw [heq, ffMixedWalkProd_succ]
    exact dvd_mul_of_dvd_left ih _

/-- The selection at step k divides the accumulated product at any later step. -/
theorem ffMixedSel_dvd_prod_of_lt {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} {k m : ℕ} (hkm : k < m) :
    σ.sel k ∣ ffMixedWalkProd p start σ m := by
  have heq : m = k + 1 + (m - k - 1) := by omega
  rw [heq]
  exact ffMixedSel_dvd_later_prod k (m - k - 1)

/-- A valid mixed selection is injective: no monic irreducible appears twice.

    Proof: if sigma.sel(j) = sigma.sel(k) with j < k, then sigma.sel(j) divides
    ffMixedWalkProd(k) (since it appears as a factor in the product at step j+1),
    and sigma.sel(k) divides ffMixedWalkProd(k) + 1 (by validity). Since
    sigma.sel(j) = sigma.sel(k) and irreducible, it divides both, contradicting
    the coprimality cascade. -/
theorem ffMixedSel_injective {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) :
    Function.Injective σ.sel := by
  intro j k hjk
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hjlt | hklt
  · -- j < k: sigma.sel(j) | prod(k) and sigma.sel(k) | prod(k)+1
    have hdvd_prod : σ.sel j ∣ ffMixedWalkProd p start σ k :=
      ffMixedSel_dvd_prod_of_lt hjlt
    have hdvd_succ := ffMixedSel_dvd hv k
    rw [hjk] at hdvd_prod
    exact ffMixedWalkProd_coprime_succ (σ.sel k)
      (ffMixedSel_irreducible hv k) k hdvd_prod hdvd_succ
  · -- k < j: symmetric
    have hdvd_prod : σ.sel k ∣ ffMixedWalkProd p start σ j :=
      ffMixedSel_dvd_prod_of_lt hklt
    have hdvd_succ := ffMixedSel_dvd hv j
    rw [← hjk] at hdvd_prod
    exact ffMixedWalkProd_coprime_succ (σ.sel j)
      (ffMixedSel_irreducible hv j) j hdvd_prod hdvd_succ

/-! ## Section 5: Start Not Capturable -/

/-- The starting polynomial divides the accumulated product at every step.
    Proof by induction: start | start, and start | prod(n) implies
    start | prod(n) * sel(n) = prod(n+1). -/
theorem start_dvd_ffMixedWalkProd {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (n : ℕ) :
    start ∣ ffMixedWalkProd p start σ n := by
  induction n with
  | zero => exact dvd_refl _
  | succ n ih =>
    simp only [ffMixedWalkProd_succ]
    exact dvd_mul_of_dvd_left ih _

/-- The starting polynomial can NEVER be captured by any valid selection.

    Proof: start divides the accumulated product at every step (by induction).
    If start were also a selected factor, it would divide acc(n) + 1 as well.
    By the coprimality cascade, no irreducible can divide both acc(n) and
    acc(n) + 1, giving a contradiction.

    This is why `ffTreeReachable` (which includes the root) is the correct
    notion of containment for the factor tree, rather than `ffMixedCaptures`. -/
theorem start_not_capturable {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ)
    (hsi : Irreducible start) :
    ¬ ffMixedCaptures p start σ start := by
  intro ⟨n, hn⟩
  have hdvd_prod : start ∣ ffMixedWalkProd p start σ n := start_dvd_ffMixedWalkProd n
  have hdvd_succ : σ.sel n ∣ ffMixedWalkProd p start σ n + 1 := ffMixedSel_dvd hv n
  rw [hn] at hdvd_succ
  exact ffMixedWalkProd_coprime_succ start hsi n hdvd_prod hdvd_succ

/-! ## Section 6: Bridge to Standard FF-EM Sequence -/

/-- Convert an FFEMData sequence to a mixed selection by choosing
    ffSeq(n+1) at each step n. -/
def ffEMToMixed (d : FFEMData p) : FFMixedSelection p :=
  ⟨fun n => d.ffSeq (n + 1)⟩

/-- The mixed walk product from X with the standard EM selection equals
    the standard FF-EM product.

    Key identity: ffMixedWalkProd(X, sigma_EM, n) = ffProd(n). -/
theorem ffEMToMixed_walkProd_eq (d : FFEMData p) (n : ℕ) :
    ffMixedWalkProd p (X : Polynomial (ZMod p)) (ffEMToMixed d) n =
      d.ffProd n := by
  induction n with
  | zero => simp [d.ffProd_zero]
  | succ n ih =>
    rw [ffMixedWalkProd_succ, ih, d.ffProd_succ n]
    rfl

/-- The standard FF-EM sequence gives a valid mixed selection from X. -/
theorem ff_standard_valid (d : FFEMData p) :
    FFMixedSelectionValid p (X : Polynomial (ZMod p)) (ffEMToMixed d) := by
  refine ⟨monic_X, ?_, ?_⟩
  · simp [natDegree_X (R := ZMod p)]
  · intro n
    rw [ffEMToMixed_walkProd_eq]
    exact ⟨(d.ffSeq_succ n).1, (d.ffSeq_succ n).2.1, (d.ffSeq_succ n).2.2⟩

/-- If Q appears in the standard FF-EM sequence at step n+1,
    then the standard mixed selection captures Q. -/
theorem ff_standard_captures_of_seq (d : FFEMData p)
    (Q : Polynomial (ZMod p)) {n : ℕ} (hseq : d.ffSeq (n + 1) = Q) :
    ffMixedCaptures p (X : Polynomial (ZMod p)) (ffEMToMixed d) Q :=
  ⟨n, hseq⟩

/-- FFMullinConjecture implies every monic irreducible is reachable from X.

    Proof: FFMullinConjecture gives d.ffSeq(n) = Q for some n.
    - If n = 0, then Q = ffSeq(0) = X = start, so Q is reachable as the root.
    - If n = k+1, then Q is captured by the standard mixed selection at step k. -/
theorem ffmc_implies_tree_reachable_from_X (d : FFEMData p)
    (hmc : FFMullinConjecture p)
    (Q : Polynomial (ZMod p)) (hQm : Q.Monic) (hQi : Irreducible Q) :
    ffTreeReachable p (X : Polynomial (ZMod p)) Q := by
  obtain ⟨n, hn⟩ := hmc d Q hQm hQi
  cases n with
  | zero =>
    -- Q = ffSeq(0) = X = start, reachable as root
    exact Or.inl (hn ▸ d.ffSeq_zero)
  | succ k =>
    -- Q = ffSeq(k+1), captured by standard mixed selection at step k
    exact Or.inr ⟨ffEMToMixed d, ff_standard_valid d, k, hn⟩

/-- The standard EM mixed selection captures every Q that appears at
    a step >= 1 in the FF-EM sequence. Combined with start_not_capturable,
    this shows ffSeq(0) = X is the unique polynomial that is reachable
    but not capturable. -/
theorem ff_standard_captures_all_later (d : FFEMData p)
    (hmc : FFMullinConjecture p)
    (Q : Polynomial (ZMod p)) (hQm : Q.Monic) (hQi : Irreducible Q)
    (hne : Q ≠ X) :
    ffMixedCaptures p (X : Polynomial (ZMod p)) (ffEMToMixed d) Q := by
  obtain ⟨n, hn⟩ := hmc d Q hQm hQi
  cases n with
  | zero =>
    -- Q = ffSeq(0) = X contradicts hne
    exfalso
    exact hne (hn ▸ d.ffSeq_zero)
  | succ k =>
    exact ⟨k, hn⟩

/-! ## Section 7: Coprimality of Accumulated Products -/

/-- The selected factor at step n does not divide the accumulated product
    at step n. This is a direct consequence of the coprimality cascade:
    sel(n) | acc(n)+1 and sel(n) irreducible, so sel(n) cannot also
    divide acc(n). -/
theorem ffMixedWalkProd_sel_not_dvd_prod {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) (n : ℕ) :
    ¬ (σ.sel n ∣ ffMixedWalkProd p start σ n) := by
  intro hdvd
  exact ffMixedWalkProd_coprime_succ (σ.sel n)
    (ffMixedSel_irreducible hv n) n hdvd (ffMixedSel_dvd hv n)

/-! ## Section 8: Degree of accumulated product + 1 -/

/-- The degree of ffMixedWalkProd(n) + 1 equals the degree of ffMixedWalkProd(n),
    since adding 1 to a monic polynomial of positive degree does not change the
    leading term. -/
theorem ffMixedWalkProd_succ_natDegree {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) (n : ℕ) :
    (ffMixedWalkProd p start σ n + 1).natDegree =
      (ffMixedWalkProd p start σ n).natDegree := by
  apply Polynomial.natDegree_add_eq_left_of_degree_lt
  calc degree 1 = 0 := degree_one
    _ < ↑(ffMixedWalkProd p start σ n).natDegree := by
        exact_mod_cast ffMixedWalkProd_natDegree_pos hv n
    _ = degree (ffMixedWalkProd p start σ n) := by
        rw [Polynomial.degree_eq_natDegree (ffMixedWalkProd_monic hv n).ne_zero]

/-! ## Section 9: Additional Tree Properties -/

/-- The degree of the accumulated product at step n is at least
    the starting degree plus n. This follows from each step adding
    at least 1 to the degree. -/
theorem ffMixedWalkProd_natDegree_ge {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) (n : ℕ) :
    start.natDegree + n ≤ (ffMixedWalkProd p start σ n).natDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ffMixedWalkProd_natDegree_succ hv n]
    have := ffMixedSel_natDegree_pos hv n
    omega

/-- The accumulated products at distinct steps are distinct polynomials.
    This follows from strict monotonicity of degrees. -/
theorem ffMixedWalkProd_injective {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) :
    Function.Injective (ffMixedWalkProd p start σ) := by
  intro j k hjk
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hjlt | hklt
  · have := (ffMixedWalkProd_natDegree_strictMono hv).lt_iff_lt.mpr hjlt
    simp [hjk] at this
  · have := (ffMixedWalkProd_natDegree_strictMono hv).lt_iff_lt.mpr hklt
    simp [hjk] at this

/-- A captured polynomial cannot also be the starting polynomial
    (for irreducible starts). This strengthens start_not_capturable
    to show the dichotomy: reachable = root OR captured, never both. -/
theorem ffTreeReachable_dichotomy {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ)
    (hsi : Irreducible start)
    (Q : Polynomial (ZMod p)) (hr : ffTreeReachable p start Q) :
    Q = start ∨ (Q ≠ start ∧ ∃ σ' : FFMixedSelection p,
      FFMixedSelectionValid p start σ' ∧ ffMixedCaptures p start σ' Q) := by
  rcases hr with rfl | ⟨σ', hv', hc⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨fun heq => by subst heq; exact start_not_capturable hv' hsi hc,
      σ', hv', hc⟩

/-! ## Section 10: Landscape -/

/-- The factor tree landscape: summary of structural properties. -/
theorem ff_factor_tree_landscape
    {start : Polynomial (ZMod p)}
    {σ : FFMixedSelection p} (hv : FFMixedSelectionValid p start σ) :
    -- (1) Accumulated product is monic at all steps
    (∀ n, (ffMixedWalkProd p start σ n).Monic) ∧
    -- (2) Accumulated product has positive degree at all steps
    (∀ n, 0 < (ffMixedWalkProd p start σ n).natDegree) ∧
    -- (3) Degree is strictly increasing
    StrictMono (fun n => (ffMixedWalkProd p start σ n).natDegree) ∧
    -- (4) Selection is injective (no irreducible appears twice)
    Function.Injective σ.sel ∧
    -- (5) Accumulated product is injective
    Function.Injective (ffMixedWalkProd p start σ) ∧
    -- (6) Selection does not divide the accumulated product
    (∀ n, ¬ (σ.sel n ∣ ffMixedWalkProd p start σ n)) ∧
    -- (7) Start divides the accumulated product at every step
    (∀ n, start ∣ ffMixedWalkProd p start σ n) :=
  ⟨ffMixedWalkProd_monic hv,
   ffMixedWalkProd_natDegree_pos hv,
   ffMixedWalkProd_natDegree_strictMono hv,
   ffMixedSel_injective hv,
   ffMixedWalkProd_injective hv,
   ffMixedWalkProd_sel_not_dvd_prod hv,
   fun n => start_dvd_ffMixedWalkProd n⟩

end FunctionFieldAnalog
