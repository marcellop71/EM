import EM.Advanced.EpsilonWalk
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Constructions

/-!
# Dense Capture: Topological Density of Capturing Selection Sequences

## Overview

This file studies the **captureSet** -- the set of binary selection sequences sigma : N -> Bool
for which the epsilon-walk from accumulator `acc` captures a given prime q (i.e., q appears
as the chosen factor at some step). The main result is that captureSet is **open** in the
product topology (Cantor space N -> Bool), unconditionally.

Combined with density (which requires hypotheses), this gives a Baire category argument:
the intersection of captureSet(q, acc) over all primes q is comeager (residual), meaning
a "generic" selection sequence captures every prime.

## Key Results

### Proved Theorems
* `epsWalkProdFrom_depends_on_prefix` -- accumulator at step k depends only on sigma(0),...,sigma(k-1)
* `epsWalkFactorFrom_depends_on_prefix` -- factor at step k depends only on sigma(0),...,sigma(k)
* `captureSet_level_isOpen` -- each level set {sigma | factor(k) = q} is open
* `captureSet_isOpen` -- captureSet is open (unconditional)
* `epsWalkProdFrom_tail_restart` -- walk from step K onward is a fresh walk
* `fullCapture_residual` -- open + dense => intersection over countably many primes is residual
* `fullCapture_exists_residual` -- existential form: open + dense => exists comeager G
* `dense_capture_landscape` -- summary conjunction

### Open Hypotheses
* `DenseCaptureHypothesis` -- captureSet is dense for acc >= 2

## Mathematical Content

The product topology on N -> Bool (Cantor space) is compact Hausdorff, hence Baire.
A function depending on finitely many coordinates is continuous, so its level sets
are clopen. The captureSet is a countable union of such level sets, hence open.
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 1: Definitions -/

section Definitions

/-- The space of binary selection sequences. -/
abbrev SelectionSeq := ℕ → Bool

/-- The set of selection sequences that capture prime q starting from accumulator acc.
    sigma captures q if q appears as the chosen factor at some step k. -/
def captureSet (q acc : ℕ) : Set SelectionSeq :=
  {σ | ∃ k, epsWalkFactorFrom acc σ k = q}

/-- The all-false selection sequence (always choose minFac = standard EM walk). -/
def minFacSeq : SelectionSeq := fun _ => false

/-- MC at (q, acc) means the minFac walk from acc captures q. -/
def MC_at (q acc : ℕ) : Prop := minFacSeq ∈ captureSet q acc

/-- MC_at is definitionally equivalent to membership in captureSet. -/
theorem MC_at_iff (q acc : ℕ) : MC_at q acc ↔ minFacSeq ∈ captureSet q acc := by
  rfl

end Definitions

/-! ## Part 2: Finitary Dependence -/

section FinitaryDependence

/-- The walk accumulator at step k depends only on sigma(0),...,sigma(k-1).
    If two decision sequences agree on the first k bits, the accumulators agree at step k. -/
theorem epsWalkProdFrom_depends_on_prefix (acc : ℕ) (σ τ : SelectionSeq)
    (k : ℕ) (h : ∀ i, i < k → σ i = τ i) :
    epsWalkProdFrom acc σ k = epsWalkProdFrom acc τ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [epsWalkProdFrom]
    have hpref : ∀ i, i < k → σ i = τ i := fun i hi => h i (by omega)
    rw [ih hpref, h k (by omega)]

/-- The factor at step k depends only on sigma(0),...,sigma(k).
    If two decision sequences agree on the first k+1 bits, the factors agree at step k. -/
theorem epsWalkFactorFrom_depends_on_prefix (acc : ℕ) (σ τ : SelectionSeq)
    (k : ℕ) (h : ∀ i, i ≤ k → σ i = τ i) :
    epsWalkFactorFrom acc σ k = epsWalkFactorFrom acc τ k := by
  simp only [epsWalkFactorFrom]
  have hpref : ∀ i, i < k → σ i = τ i := fun i hi => h i (by omega)
  rw [epsWalkProdFrom_depends_on_prefix acc σ τ k hpref, h k (le_refl k)]

end FinitaryDependence

/-! ## Part 3: captureSet is Open -/

section OpenCapture

/-- The cylinder set of sequences agreeing with sigma on indices 0,...,k is open
    in the product topology on N -> Bool. Uses `isOpen_set_pi` with finite index set. -/
private theorem cylinder_isOpen (σ : SelectionSeq) (k : ℕ) :
    IsOpen {τ : SelectionSeq | ∀ i, i ≤ k → τ i = σ i} := by
  have heq : {τ : SelectionSeq | ∀ i, i ≤ k → τ i = σ i} =
      Set.pi (Finset.Icc 0 k : Set ℕ) (fun i => {σ i}) := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_Icc, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · intro h i ⟨_, hi2⟩; exact h i (by omega)
    · intro h i hi; exact h i ⟨by omega, hi⟩
  rw [heq]
  exact isOpen_set_pi (Finset.Icc 0 k).finite_toSet (fun _ _ => isOpen_discrete _)

/-- Each level set {sigma | epsWalkFactorFrom acc sigma k = q} is open in the product topology.
    This is because the factor at step k depends only on sigma(0),...,sigma(k),
    so the level set is a union of cylinder sets. -/
theorem captureSet_level_isOpen (q acc : ℕ) (k : ℕ) :
    IsOpen {σ : SelectionSeq | epsWalkFactorFrom acc σ k = q} := by
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨{τ | ∀ i, i ≤ k → τ i = σ i}, ?_, cylinder_isOpen σ k, ?_⟩
  · intro τ hτ
    simp only [Set.mem_setOf_eq] at hτ hσ ⊢
    rw [epsWalkFactorFrom_depends_on_prefix acc τ σ k hτ]
    exact hσ
  · simp only [Set.mem_setOf_eq]
    tauto

/-- **captureSet is open**: The set of selection sequences that capture prime q from
    accumulator acc is open in the product topology on N -> Bool.

    Proof: captureSet = Union_k {sigma | factor(k) = q}, and each level set is open. -/
theorem captureSet_isOpen (q acc : ℕ) :
    IsOpen (captureSet q acc) := by
  have heq : captureSet q acc = ⋃ k, {σ | epsWalkFactorFrom acc σ k = q} := by
    ext σ; simp only [captureSet, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [heq]
  exact isOpen_iUnion (fun k => captureSet_level_isOpen q acc k)

end OpenCapture

/-! ## Part 4: Tail Restart -/

section TailRestart

/-- Walk from step K onward is a fresh walk starting from the accumulator at step K.
    The shifted decision sequence is `fun i => sigma (K + i)`. -/
theorem epsWalkProdFrom_tail_restart (acc : ℕ) (σ : SelectionSeq) (K j : ℕ) :
    epsWalkProdFrom acc σ (K + j) =
    epsWalkProdFrom (epsWalkProdFrom acc σ K) (fun i => σ (K + i)) j := by
  induction j with
  | zero => simp [epsWalkProdFrom]
  | succ j ih =>
    have hkj : K + (j + 1) = K + j + 1 := by omega
    rw [hkj]
    simp only [epsWalkProdFrom]
    rw [ih]

/-- The factor at step K+j in the original walk equals the factor at step j
    in the shifted walk starting from the accumulator at step K. -/
theorem epsWalkFactorFrom_tail_restart (acc : ℕ) (σ : SelectionSeq) (K j : ℕ) :
    epsWalkFactorFrom acc σ (K + j) =
    epsWalkFactorFrom (epsWalkProdFrom acc σ K) (fun i => σ (K + i)) j := by
  simp only [epsWalkFactorFrom]
  rw [epsWalkProdFrom_tail_restart acc σ K j]

/-- Capture at any step K+j in the original walk implies capture at step j
    in the shifted walk, and vice versa. -/
theorem captureSet_tail_iff (q acc : ℕ) (K : ℕ) (σ : SelectionSeq) :
    (∃ j, epsWalkFactorFrom acc σ (K + j) = q) ↔
    (∃ j, epsWalkFactorFrom (epsWalkProdFrom acc σ K) (fun i => σ (K + i)) j = q) := by
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, by rwa [← epsWalkFactorFrom_tail_restart]⟩
  · rintro ⟨j, hj⟩; exact ⟨j, by rwa [epsWalkFactorFrom_tail_restart]⟩

end TailRestart

/-! ## Part 5: Conditional Density + Baire Category -/

section BaireCapture

/-- Dense capture hypothesis: for acc >= 2, captureSet(q, acc) is dense.
    This is the key hypothesis connecting the topological framework to number theory.
    It asserts that the set of decision sequences capturing q is dense in Cantor space,
    meaning every cylinder (finite prefix) can be extended to capture q.

    **Status**: open hypothesis. -/
def DenseCaptureHypothesis (q : ℕ) : Prop :=
  ∀ (acc : ℕ), 2 ≤ acc →
    Dense (captureSet q acc)

/-- Cantor space N -> Bool is compact Hausdorff, hence a Baire space.
    This is an instance witness for the Baire category theorem application.

    Bool has discrete topology, so N -> Bool has the product topology (Tychonoff).
    Compact T2 implies locally compact T2, which implies Baire. -/
instance : BaireSpace SelectionSeq :=
  BaireSpace.of_t2Space_locallyCompactSpace

/-- The set of primes is countable (subset of the countable set N). -/
private theorem primes_countable : ({q : ℕ | q.Prime}).Countable :=
  Set.Countable.mono (Set.subset_univ _) Set.countable_univ

/-- If captureSet(q, acc) is open AND dense for every prime q, then the intersection
    over all primes is residual (comeager), meaning a generic selection sequence
    captures every prime.

    Uses Baire category theorem: countable intersection of open dense sets is dense
    in a Baire space (Cantor space = compact Hausdorff = Baire).

    The result is stated using the `residual` filter (= comeager sets). A set belongs
    to `residual X` iff it contains a countable intersection of open dense sets. -/
theorem fullCapture_residual (acc : ℕ)
    (h_dense : ∀ q, Nat.Prime q → Dense (captureSet q acc)) :
    (⋂ q ∈ {q : ℕ | q.Prime}, captureSet q acc) ∈ residual SelectionSeq := by
  -- Build the set of open dense sets
  have h_open : ∀ s ∈ (captureSet · acc) '' {q : ℕ | q.Prime}, IsOpen s := by
    intro s hs
    obtain ⟨q, _, rfl⟩ := hs
    exact captureSet_isOpen q acc
  have h_dense' : ∀ s ∈ (captureSet · acc) '' {q : ℕ | q.Prime}, Dense s := by
    intro s hs
    obtain ⟨q, hq, rfl⟩ := hs
    exact h_dense q hq
  have h_count : ((captureSet · acc) '' {q : ℕ | q.Prime}).Countable :=
    primes_countable.image _
  -- Apply dense_sInter_of_isOpen and then residual_of_dense_Gδ
  have h_isGδ : IsGδ (⋂₀ ((captureSet · acc) '' {q : ℕ | q.Prime})) :=
    IsGδ.sInter (fun s hs => by
      simp only [Set.mem_image, Set.mem_setOf_eq] at hs
      obtain ⟨q, _, rfl⟩ := hs
      exact (captureSet_isOpen q acc).isGδ) h_count
  have h_dense_inter := dense_sInter_of_isOpen h_open h_count h_dense'
  -- Convert sInter of images to biInter
  have h_eq : ⋂₀ ((captureSet · acc) '' {q : ℕ | q.Prime}) =
      ⋂ q ∈ {q : ℕ | q.Prime}, captureSet q acc := by
    ext σ
    simp only [Set.mem_sInter, Set.mem_image, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h q hq; exact h _ ⟨q, hq, rfl⟩
    · rintro h _ ⟨q, hq, rfl⟩; exact h q hq
  rw [← h_eq]
  exact residual_of_dense_Gδ h_isGδ h_dense_inter

/-- If captureSet(q, acc) is open AND dense for every prime q, then there exists
    a residual (comeager) set G such that every sigma in G captures every prime.
    This is the existential form of the Baire argument. -/
theorem fullCapture_exists_residual (acc : ℕ)
    (h_dense : ∀ q, Nat.Prime q → Dense (captureSet q acc)) :
    ∃ G : Set SelectionSeq,
      G ∈ residual SelectionSeq ∧ ∀ σ ∈ G, ∀ q, q.Prime → σ ∈ captureSet q acc := by
  refine ⟨⋂ q ∈ {q : ℕ | q.Prime}, captureSet q acc,
    fullCapture_residual acc h_dense, ?_⟩
  intro σ hσ q hq
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hσ
  exact hσ q hq

/-- The Baire intersection is nonempty: under density, there exists a selection sequence
    that captures every prime. Uses that residual sets in nonempty Baire spaces are nonempty
    (via density of the intersection). -/
theorem fullCapture_nonempty (acc : ℕ)
    (h_dense : ∀ q, Nat.Prime q → Dense (captureSet q acc)) :
    ∃ σ : SelectionSeq, ∀ q, q.Prime → σ ∈ captureSet q acc := by
  obtain ⟨G, hG, hGprop⟩ := fullCapture_exists_residual acc h_dense
  have hd := dense_of_mem_residual hG
  obtain ⟨σ, hσ⟩ := hd.nonempty
  exact ⟨σ, hGprop σ hσ⟩

end BaireCapture

/-! ## Part 6: Landscape -/

section Landscape

/-- **Dense capture landscape**: summary of all results in this file.

    PROVED results:
    1. captureSet_isOpen -- captureSet is open (unconditional)
    2. MC_at_iff -- MC_at q acc iff minFacSeq in captureSet q acc
    3. epsWalkProdFrom_depends_on_prefix -- finitary dependence of accumulator
    4. epsWalkFactorFrom_depends_on_prefix -- finitary dependence of factor
    5. epsWalkProdFrom_tail_restart -- tail restart identity
    6. fullCapture_residual -- open + dense => residual (conditional on density)
    7. fullCapture_nonempty -- density => existence of full-capturing sequence -/
theorem dense_capture_landscape (q : ℕ) (_hq : Nat.Prime q) (acc : ℕ) (_hacc : 2 ≤ acc) :
    -- 1. captureSet is open (unconditional)
    IsOpen (captureSet q acc)
    ∧
    -- 2. MC_at iff minFacSeq in captureSet (definitional)
    (MC_at q acc ↔ minFacSeq ∈ captureSet q acc)
    ∧
    -- 3. Comeager full capture from open + dense (conditional)
    ((∀ q', q'.Prime → Dense (captureSet q' acc)) →
      ∃ G : Set SelectionSeq, G ∈ residual SelectionSeq ∧
        ∀ σ ∈ G, ∀ q', q'.Prime → σ ∈ captureSet q' acc) :=
  ⟨captureSet_isOpen q acc,
   MC_at_iff q acc,
   fun h_dense => fullCapture_exists_residual acc h_dense⟩

end Landscape
