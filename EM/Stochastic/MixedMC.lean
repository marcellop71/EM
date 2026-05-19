import EM.Stochastic.MixedWalk

/-!
# Mixed MC: MixedMC Framework, Hitting Formulation, and Bridges

## Overview

This file (Parts 12-20b of the original epsilon-random MC development) defines the
MixedMC conjecture family for the mixed walk of `MixedWalk.lean` and proves the
main reduction: `MixedDiversityWeak` implies MixedMC for all primes, by strong
induction. It also gives the cleaner hitting formulation `MixedHitting` and the
bridges from the two-point walk and from `UFDStrong`.

## Contents

* Part 12: Mixed MC framework -- `MixedMC`, `MixedMCBelow`, `MixedMullinConjecture`
* Part 13: q=2 and q=3 base cases -- `mixed_mc_two`, `mixed_mc_three`
* Part 14: MixedDiversityWeak hypothesis -- `MixedDiversityWeak`
* Part 15: Main theorem, strong induction -- `mixed_diversity_weak_implies_mixed_mc`,
  `mixed_diversity_weak_is_sole_gap`
* Part 16: MixedMCBelow from induction -- `mixed_diversity_weak_implies_mc_below`
* Part 17: Mixed MC landscape -- `mixed_mc_landscape`
* Part 18: Walk-mod-q structural lemmas -- `prime_factor_ne_not_dvd`,
  `walk_coprime_until_capture`, `hit_implies_capture'`
* Part 19: MixedHitting, cleaner hitting formulation -- `MixedHitting`,
  `mixed_hitting_implies_diversity_weak`, `mixed_hitting_diversity_implies_mc`,
  `mixed_hitting_is_sufficient`
* Part 20: Bridge from two-point walk to MixedMC -- `embedBoolToMixed`,
  `embed_walk_agreement`, `embed_factor_agreement`, `embed_valid`,
  `two_point_capture_implies_mixed_capture`, `two_point_capture_implies_mixed_mc`,
  `embed_all_true_eq_minFac`
* Part 20b: UFDStrong to MixedMC bridge -- `UFDStrongImpliesMixedMC`,
  `ufd_strong_implies_mixed_mc_chain`, `two_point_mixed_mc_landscape`
-/

noncomputable section
open Classical

open Mullin Euclid MullinGroup RotorRouter

/-! ## Part 12: Mixed MC Framework

We define the Mixed Mullin Conjecture: every prime is "captured" by the mixed walk.
Since all accumulators starting from acc=2 are even, P(n)+1 is always odd, so
q=2 can never appear as a factor. We handle q=2 separately via disjunction. -/

section MixedMCDefs

/-- Mixed MC for a single prime: either q=2 (trivially in the initial accumulator)
    or there exists a valid selection that captures q from acc=2. -/
def MixedMC (q : ℕ) : Prop :=
  q.Prime → q = 2 ∨ ∃ σ : MixedSelection, ValidMixedSelection 2 σ ∧ mixedCaptures q 2 σ

/-- Mixed MC below: all primes less than q have MixedMC. -/
def MixedMCBelow (q : ℕ) : Prop :=
  ∀ r, r.Prime → r < q → MixedMC r

/-- Full Mixed Mullin Conjecture: every prime has MixedMC. -/
def MixedMullinConjecture : Prop :=
  ∀ q, q.Prime → MixedMC q

end MixedMCDefs

/-! ## Part 13: q=2 and q=3 Base Cases -/

section BaseCases

/-- q=2 is trivially captured since 2 divides the initial accumulator acc=2. -/
theorem mixed_mc_two : MixedMC 2 := by
  intro _
  left
  rfl

/-- q=3 is captured at step 0 for any valid selection from acc=2.
    This follows from `mixed_capture_three` and `minFacMixed_valid`. -/
theorem mixed_mc_three : MixedMC 3 := by
  intro _
  right
  exact ⟨minFacMixed, minFacMixed_valid 2, 0, mixed_capture_three minFacMixed (minFacMixed_valid 2)⟩

end BaseCases

/-! ## Part 14: MixedDiversityWeak Hypothesis

The weak steering hypothesis: for every prime q >= 5 and accumulator acc >= 2
with q not dividing acc, if the minFac walk from acc produces composite P+1 at
cofinally many steps (diversity), then some valid selection captures q.

This is genuinely weaker than DynamicalHitting: the mixed walk has freedom to
choose non-minFac factors, providing more paths to hit any given prime. -/

section DiversityWeak

/-- Weak diversity-implies-capture hypothesis for the mixed walk.
    Given diversity (cofinally many composite P+1), we can steer the walk
    to capture any target prime q >= 5.

    **Status**: open hypothesis. This is the sole gap for MixedMullinConjecture. -/
def MixedDiversityWeak : Prop :=
  ∀ (q : ℕ), q.Prime → 5 ≤ q →
    ∀ (acc : ℕ), 2 ≤ acc → ¬(q ∣ acc) →
    (∀ N, ∃ n, N ≤ n ∧ ¬(mixedWalkProd acc minFacMixed n + 1).Prime) →
    ∃ σ : MixedSelection, ValidMixedSelection acc σ ∧ mixedCaptures q acc σ

end DiversityWeak

/-! ## Part 15: Main Theorem — Strong Induction

The core reduction: MixedDiversityWeak + MixedDiversity implies MixedMullinConjecture.
The proof uses strong induction on the prime q. For q=2 and q=3, we use the base
cases. For q >= 5, we apply MixedDiversityWeak with acc=2. -/

section MainReduction

/-- For q >= 5, q does not divide 2. -/
private theorem not_dvd_two_of_ge_five {q : ℕ} (h5 : 5 ≤ q) :
    ¬(q ∣ 2) := by
  intro hdvd
  have := Nat.le_of_dvd (by omega : 0 < 2) hdvd
  omega

/-- For q prime and q not equal to 2 or 3, we have q >= 5. -/
private theorem prime_ge_five_of_ne {q : ℕ} (hq : q.Prime) (hne2 : q ≠ 2) (hne3 : q ≠ 3) :
    5 ≤ q := by
  by_contra h
  push Not at h
  have h2 := hq.two_le
  -- q ∈ {2, 3, 4}; only 2 and 3 are prime
  interval_cases q <;> first | omega | exact absurd hq (by decide)

/-- **Main theorem**: MixedDiversityWeak + MixedDiversity implies MixedMullinConjecture.

    Proof by strong induction on q:
    - q = 2: trivial (2 | acc = 2)
    - q = 3: unconditional from mixed_capture_three
    - q >= 5: apply MixedDiversityWeak with acc = 2, using MixedDiversity for the
      cofinality hypothesis and the inductive hypothesis for MixedMCBelow. -/
theorem mixed_diversity_weak_implies_mixed_mc
    (hdw : MixedDiversityWeak) (hdiv : MixedDiversity) :
    MixedMullinConjecture := by
  -- Strong induction: suffices to show MixedMC q for all q <= k
  suffices ∀ k q, q ≤ k → q.Prime → MixedMC q by
    intro q hq; exact this q q le_rfl hq
  intro k
  induction k with
  | zero =>
    intro q hle hq
    exact absurd hq.one_lt (by omega)
  | succ k ih =>
    intro q hle hq
    -- If q < k+1, use the inductive hypothesis
    match Nat.lt_or_ge q (k + 1) with
    | .inl hlt => exact ih q (by omega) hq
    | .inr _ =>
      -- q = k + 1 case (since q <= k+1 and q >= k+1)
      intro _hprime
      -- Handle small primes directly
      by_cases hq2 : q = 2
      · left; exact hq2
      by_cases hq3 : q = 3
      · right
        subst hq3
        exact ⟨minFacMixed, minFacMixed_valid 2, 0,
               mixed_capture_three minFacMixed (minFacMixed_valid 2)⟩
      -- q >= 5: apply MixedDiversityWeak
      right
      have hq5 : 5 ≤ q := prime_ge_five_of_ne hq hq2 hq3
      have hndvd : ¬(q ∣ 2) := not_dvd_two_of_ge_five hq5
      have hdiv2 : ∀ N, ∃ n, N ≤ n ∧ ¬(mixedWalkProd 2 minFacMixed n + 1).Prime :=
        hdiv 2 (by omega)
      exact hdw q hq hq5 2 (by omega) hndvd hdiv2

/-- MixedDiversity alone is insufficient: we also need MixedDiversityWeak to steer.
    But MixedDiversityWeak is the SOLE hypothesis beyond MixedDiversity. -/
theorem mixed_diversity_weak_is_sole_gap :
    (MixedDiversityWeak → MixedDiversity → MixedMullinConjecture) :=
  mixed_diversity_weak_implies_mixed_mc

end MainReduction

/-! ## Part 16: MixedMCBelow from Induction

The strong induction gives MixedMCBelow at each step. We extract this as
a standalone theorem for use in downstream proofs. -/

section MCBelowExtraction

/-- MixedDiversityWeak + MixedDiversity implies MixedMCBelow for all q. -/
theorem mixed_diversity_weak_implies_mc_below
    (hdw : MixedDiversityWeak) (hdiv : MixedDiversity) (q : ℕ) :
    MixedMCBelow q := by
  intro r hr hrq
  exact mixed_diversity_weak_implies_mixed_mc hdw hdiv r hr

end MCBelowExtraction

/-! ## Part 17: Mixed MC Landscape

Summary of the entire mixed MC framework: base cases, main reduction, and
the single open hypothesis. -/

section MixedMCLandscape

/-- **Mixed MC landscape**: summary of the complete framework.

    1. MixedMC 2 -- q=2 is trivial
    2. MixedMC 3 -- q=3 is unconditional
    3. MixedDiversityWeak + MixedDiversity implies MixedMullinConjecture
    4. MixedDiversityWeak is the sole open hypothesis for q >= 5 -/
theorem mixed_mc_landscape
    (hdw : MixedDiversityWeak) (hdiv : MixedDiversity) :
    -- 1. q=2 is trivial
    MixedMC 2
    ∧
    -- 2. q=3 is unconditional
    MixedMC 3
    ∧
    -- 3. Full Mixed MC holds
    MixedMullinConjecture
    ∧
    -- 4. Sole gap is MixedDiversityWeak
    (MixedDiversityWeak → MixedDiversity → MixedMullinConjecture) :=
  ⟨mixed_mc_two,
   mixed_mc_three,
   mixed_diversity_weak_implies_mixed_mc hdw hdiv,
   mixed_diversity_weak_implies_mixed_mc⟩

end MixedMCLandscape

/-! ## Part 18: Walk-mod-q Structural Lemmas

The walk modulo a prime q stays coprime to q until the walk captures q.
These lemmas formalize the structural fact that if no factor chosen along
the walk equals q, then q cannot divide the accumulator product at any step.
This is because each factor is prime and distinct from q (hence coprime to q),
and the product of terms coprime to q remains coprime to q. -/

section WalkModQ

/-- For any prime factor f different from prime q, q does not divide f.
    This is because f is prime, so its only divisors are 1 and f.
    If q | f, then q = 1 or q = f; but q is prime so q ≠ 1, hence q = f,
    contradicting f ≠ q. -/
theorem prime_factor_ne_not_dvd {q : ℕ} (hq : Nat.Prime q)
    (f : ℕ) (hf : f.Prime) (hfq : f ≠ q) :
    ¬(q ∣ f) := by
  intro hdvd
  exact hfq ((hf.eq_one_or_self_of_dvd q hdvd).resolve_left (Nat.Prime.ne_one hq)).symm

/-- The walk stays coprime to q until capture: if q does not divide the initial
    accumulator and no factor chosen at steps 0, ..., n-1 equals q, then q does
    not divide the accumulator at step n.

    Proof by induction on n. At n=0 this is the hypothesis q ∤ acc. At n+1,
    the product P_{n+1} = P_n * f_n. By IH, q ∤ P_n. The factor f_n is prime
    (from validity + acc ≥ 2) and f_n ≠ q (from hnocap), so q ∤ f_n by
    `prime_factor_ne_not_dvd`. Therefore q ∤ P_n * f_n. -/
theorem walk_coprime_until_capture {q : ℕ} (hq : Nat.Prime q)
    (acc : ℕ) (hacc : 2 ≤ acc)
    (σ : MixedSelection) (hv : ValidMixedSelection acc σ)
    (hndvd : ¬(q ∣ acc))
    (n : ℕ) (hnocap : ∀ k, k < n → mixedWalkFactor acc σ k ≠ q) :
    ¬(q ∣ mixedWalkProd acc σ n) := by
  induction n with
  | zero => simp [mixedWalkProd]; exact hndvd
  | succ n ih =>
    rw [mixedWalkProd_succ]
    have hih : ¬(q ∣ mixedWalkProd acc σ n) :=
      ih (fun k hk => hnocap k (by omega))
    have hge := mixedWalkProd_ge_two acc hacc σ hv n
    have hfac_prime := mixedWalkFactor_prime acc σ hv n hge
    have hfac_neq : mixedWalkFactor acc σ n ≠ q := hnocap n (by omega)
    have hfac_ndvd : ¬(q ∣ mixedWalkFactor acc σ n) :=
      prime_factor_ne_not_dvd hq _ hfac_prime hfac_neq
    exact Nat.Prime.not_dvd_mul hq hih hfac_ndvd

/-- If q divides P_σ(n)+1 for some valid σ and q does not divide acc, we can
    construct a new valid selection σ' that captures q. The selection σ' agrees
    with σ on steps [0, n) and sets σ'(n) = some q, σ'(k) = none for k > n.

    Key facts:
    1. σ' agrees with σ on [0, n), so mixedWalkProd acc σ' n = mixedWalkProd acc σ n
    2. At step n: σ'(n) = some q, validity requires q prime (from hq) and q | P(n)+1
    3. For k > n: σ'(k) = none, validity is trivially True
    4. Capture: mixedWalkFactor acc σ' n = q -/
theorem hit_implies_capture' {q : ℕ} (hq : Nat.Prime q)
    (acc : ℕ)
    (σ : MixedSelection) (hv : ValidMixedSelection acc σ) (n : ℕ)
    (hdvd : q ∣ mixedWalkProd acc σ n + 1) :
    ∃ σ' : MixedSelection, ValidMixedSelection acc σ' ∧ mixedCaptures q acc σ' := by
  -- Define σ': agree with σ on [0,n), use some q at n, none after
  let σ' : MixedSelection := fun k =>
    if k < n then σ k
    else if k = n then some q
    else none
  have hpref : ∀ i, i < n → σ' i = σ i :=
    fun i hi => by simp only [σ', if_pos hi]
  have hwalk_eq : mixedWalkProd acc σ' n = mixedWalkProd acc σ n :=
    mixedWalkProd_depends_on_prefix acc σ' σ n hpref
  -- σ' at step n
  have hsn : σ' n = some q := by
    simp only [σ', show ¬(n < n) from lt_irrefl n, ite_false, ite_true]
  -- σ' at step k > n
  have hsk : ∀ k, ¬(k < n) → k ≠ n → σ' k = none := by
    intro k hlt hne
    simp only [σ', if_neg hlt, if_neg hne]
  -- Validity of σ'
  have hv' : ValidMixedSelection acc σ' := by
    intro k
    by_cases hlt : k < n
    · -- k < n: σ'(k) = σ(k), walk agrees
      rw [hpref k hlt]
      have hwk : mixedWalkProd acc σ' k = mixedWalkProd acc σ k :=
        mixedWalkProd_depends_on_prefix acc σ' σ k
          (fun i hi => hpref i (by omega))
      have hspec := hv k
      cases hσk : σ k with
      | none => trivial
      | some p =>
        simp only [hσk] at hspec ⊢
        exact ⟨hspec.1, by rw [hwk]; exact hspec.2⟩
    · by_cases heq : k = n
      · subst heq; rw [hsn]; exact ⟨hq, by rw [hwalk_eq]; exact hdvd⟩
      · rw [hsk k hlt heq]; trivial
  -- Capture: factor at step n equals q
  have hcap : mixedWalkFactor acc σ' n = q :=
    mixedWalkFactor_some_eq acc σ' n q hsn
  exact ⟨σ', hv', n, hcap⟩

end WalkModQ

/-! ## Part 19: MixedHitting -- Cleaner Hitting Formulation

MixedHitting is a cleaner formulation of the steering hypothesis: for any
target prime q >= 5, if the standard minFac walk produces composite P+1 at
cofinally many steps, then there exists SOME valid walk (not necessarily the
minFac walk) where q divides P+1 at some step. This immediately implies
capture via `hit_implies_capture'`.

MixedHitting + MixedDiversity together imply MixedMullinConjecture. -/

section MixedHitting

/-- MixedHitting: for any prime q >= 5 and acc >= 2 with q not dividing acc,
    if the minFac walk from acc produces composite P+1 at cofinally many steps,
    then there exists some valid walk from acc where q divides P+1 at some step.

    This is a sufficient condition for capture: once q | P+1, we can select
    factor = q to complete the capture.

    **Status**: open hypothesis. Strictly weaker than DynamicalHitting because
    the mixed walk has freedom to choose non-minFac factors. -/
def MixedHitting : Prop :=
  ∀ (q : ℕ), q.Prime → 5 ≤ q →
    ∀ (acc : ℕ), 2 ≤ acc → ¬(q ∣ acc) →
    (∀ N, ∃ n, N ≤ n ∧ ¬(mixedWalkProd acc minFacMixed n + 1).Prime) →
    ∃ (σ : MixedSelection) (n : ℕ),
      ValidMixedSelection acc σ ∧ q ∣ (mixedWalkProd acc σ n + 1)

/-- MixedHitting implies MixedDiversityWeak: a hit gives a walk with q | P+1,
    then `hit_implies_capture'` converts this to a valid capturing walk. -/
theorem mixed_hitting_implies_diversity_weak :
    MixedHitting → MixedDiversityWeak := by
  intro hmh q hq h5 acc hacc hndvd hdiv
  obtain ⟨σ, n, hv, hdvd⟩ := hmh q hq h5 acc hacc hndvd hdiv
  exact hit_implies_capture' hq acc σ hv n hdvd

/-- MixedHitting + MixedDiversity implies MixedMullinConjecture.
    Composition of mixed_hitting_implies_diversity_weak with the main
    reduction mixed_diversity_weak_implies_mixed_mc. -/
theorem mixed_hitting_diversity_implies_mc
    (hmh : MixedHitting) (hdiv : MixedDiversity) :
    MixedMullinConjecture :=
  mixed_diversity_weak_implies_mixed_mc (mixed_hitting_implies_diversity_weak hmh) hdiv

/-- MixedHitting is sufficient: with MixedDiversity, it closes the entire
    MixedMullinConjecture. This makes MixedHitting an alternative to
    MixedDiversityWeak as the sole open hypothesis. -/
theorem mixed_hitting_is_sufficient :
    (MixedHitting → MixedDiversity → MixedMullinConjecture) :=
  mixed_hitting_diversity_implies_mc

end MixedHitting

/-! ## Part 20: Bridge from Two-Point Walk to MixedMC

The two-point walk (`epsWalkProdFrom` from `RandomTwoPointMC.lean`) uses `ℕ → Bool`
with `true = minFac`, `false = secondMinFac`. The mixed walk uses `MixedSelection`
with `none = minFac`, `some p = specific prime`.

We embed any two-point decision sequence `σ : ℕ → Bool` into a mixed selection
`embedBoolToMixed acc σ` by mapping:
- `true` at step k → `none` (= choose minFac)
- `false` at step k → `some (secondMinFac(P+1))` where P is the TWO-POINT walk's
  accumulator at step k

The key theorem `embed_walk_agreement` shows that under this embedding, the mixed walk
produces exactly the same accumulator sequence as the two-point walk. This is proved
by induction: at each step, both walks use the same factor (either minFac or
secondMinFac of the same value P+1), because the accumulators agree by the IH.

From this, we derive:
1. The embedded selection is valid (factors are prime and divide P+1).
2. If the two-point walk captures q (some factor = q), the mixed walk does too.
3. Composition: any two-point capture gives MixedMC.

This bridges the two-point spectral analysis (UFDStrong → path existence) to the
mixed walk framework, reducing MixedMC to two-point capture from acc = 2. -/

section TwoPointBridge

/-- Embed a Bool decision sequence into a MixedSelection.
    `true` → `none` (choose minFac), `false` → `some (secondMinFac(P+1))`
    where P is the two-point walk's accumulator at that step. -/
def embedBoolToMixed (acc : ℕ) (σ : ℕ → Bool) : MixedSelection :=
  fun k =>
    if σ k then none
    else some (secondMinFac (epsWalkProdFrom acc σ k + 1))

/-- Under the embedding, the mixed walk factor at step n agrees with the
    two-point walk factor, given that the accumulators agree at step n. -/
private theorem embed_factor_eq_aux (acc : ℕ) (σ : ℕ → Bool) (n : ℕ)
    (hwalk : mixedWalkProd acc (embedBoolToMixed acc σ) n = epsWalkProdFrom acc σ n) :
    mixedWalkFactor acc (embedBoolToMixed acc σ) n = epsWalkFactorFrom acc σ n := by
  simp only [mixedWalkFactor, epsWalkFactorFrom, embedBoolToMixed]
  cases σ n with
  | true => simp [hwalk]
  | false => simp

/-- **Walk agreement**: the mixed walk under the Bool embedding produces
    exactly the same accumulator sequence as the two-point walk.

    Proof by induction on n. Base case: both start at acc. Inductive step:
    by IH the accumulators agree at step n, so the factors agree
    (via `embed_factor_eq_aux`), hence the products at step n+1 agree. -/
theorem embed_walk_agreement (acc : ℕ) (σ : ℕ → Bool) (n : ℕ) :
    mixedWalkProd acc (embedBoolToMixed acc σ) n = epsWalkProdFrom acc σ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [mixedWalkProd_succ, epsWalkProdFrom_succ, ih,
        embed_factor_eq_aux acc σ n ih]

/-- **Factor agreement**: the mixed walk factor under the Bool embedding
    agrees with the two-point walk factor. -/
theorem embed_factor_agreement (acc : ℕ) (σ : ℕ → Bool) (n : ℕ) :
    mixedWalkFactor acc (embedBoolToMixed acc σ) n = epsWalkFactorFrom acc σ n :=
  embed_factor_eq_aux acc σ n (embed_walk_agreement acc σ n)

/-- **Validity**: the Bool embedding produces a valid mixed selection
    for acc >= 2. At `true` steps: `none`, trivially valid. At `false` steps:
    `some (secondMinFac(P+1))`, which is prime and divides P+1. -/
theorem embed_valid (acc : ℕ) (hacc : 2 ≤ acc) (σ : ℕ → Bool) :
    ValidMixedSelection acc (embedBoolToMixed acc σ) := by
  intro k
  simp only [embedBoolToMixed]
  cases σ k with
  | true =>
    simp
  | false =>
    simp
    constructor
    · exact secondMinFac_prime (by
        have := epsWalkProdFrom_ge_two acc hacc σ k
        omega)
    · rw [embed_walk_agreement]
      exact secondMinFac_dvd (by
        have := epsWalkProdFrom_ge_two acc hacc σ k
        omega)

/-- If the two-point walk from acc captures q at step n (factor = q), then
    there exists a valid mixed selection from acc that also captures q. -/
theorem two_point_capture_implies_mixed_capture (q acc : ℕ) (hacc : 2 ≤ acc)
    (σ : ℕ → Bool) (n : ℕ) (hcap : epsWalkFactorFrom acc σ n = q) :
    ∃ σ' : MixedSelection, ValidMixedSelection acc σ' ∧ mixedCaptures q acc σ' :=
  ⟨embedBoolToMixed acc σ, embed_valid acc hacc σ, n,
   by rw [embed_factor_agreement]; exact hcap⟩

/-- If ANY two-point walk from acc=2 captures q, then MixedMC q.
    This converts the two-point reachability framework into MixedMC. -/
theorem two_point_capture_implies_mixed_mc (q : ℕ)
    (σ : ℕ → Bool) (n : ℕ) (hcap : epsWalkFactorFrom 2 σ n = q) :
    MixedMC q := by
  intro _
  right
  exact two_point_capture_implies_mixed_capture q 2 (by omega) σ n hcap

/-- The embedding commutes with the `mixedWalkProd_minFac_eq` bridge:
    embedding the all-true sequence gives the all-minFac mixed selection. -/
theorem embed_all_true_eq_minFac (acc : ℕ) :
    embedBoolToMixed acc (fun _ => true) = minFacMixed := by
  ext k
  simp [embedBoolToMixed, minFacMixed]

end TwoPointBridge

/-! ## Part 20b: UFDStrong to MixedMC Bridge

The UFDStrong → path existence chain operates in the abstract group (ZMod q)ˣ
via `paddedUnitSet` (which uses the STANDARD EM sequence's factors from `prod(n)+1`).
The mixed walk is self-consistent: factors depend on the walk's own accumulator,
not the standard sequence's.

This creates a gap: `ufdStrong_implies_path_existence` proves that every element
of (ZMod q)ˣ appears in the abstract product multiset, but the product multiset
models selections from FIXED factor sets (the standard EM orbit), not the
path-dependent factor sets of a mixed walk.

We define `UFDStrongImpliesMixedMC` as an open Prop capturing this gap, and prove
that if it holds, the full chain from UFDStrong to MixedMC is closed. -/

section UFDBridge

/-- **UFDStrongImpliesMixedMC**: bridge from UFDStrong's abstract path existence
    (over padded unit sets of the standard EM orbit) to concrete MixedMC.

    The gap: `ufdStrong_implies_path_existence` shows every unit mod q is reachable
    in the product multiset of `paddedUnitSet` (the standard orbit's factor sets).
    But MixedMC requires constructing a valid `MixedSelection` that achieves this
    reachability through a self-consistent walk (where each step's factor set depends
    on the walk's own accumulator, not the standard orbit's).

    This is the "self-consistent vs non-self-consistent" gap (Session 217).

    **Status**: open hypothesis. -/
def UFDStrongImpliesMixedMC : Prop :=
  ∀ (q : ℕ), q.Prime → 5 ≤ q →
    (∀ (hqp : Fact (Nat.Prime q)), @UFDStrong q hqp) →
    MixedMC q

/-- If UFDStrongImpliesMixedMC holds and UFDStrong holds at every prime q >= 5,
    then MixedMC holds for all primes. -/
theorem ufd_strong_implies_mixed_mc_chain
    (hbridge : UFDStrongImpliesMixedMC)
    (hufd : ∀ (q : ℕ) (hqp : Fact (Nat.Prime q)), 5 ≤ q → @UFDStrong q hqp) :
    MixedMullinConjecture := by
  intro q hq_prime
  by_cases hq2 : q = 2
  · subst hq2; exact mixed_mc_two
  by_cases hq3 : q = 3
  · subst hq3; exact mixed_mc_three
  · have h5 : 5 ≤ q := prime_ge_five_of_ne hq_prime hq2 hq3
    exact hbridge q hq_prime h5 (fun hqp => hufd q hqp h5)

/-- **Two-Point to MixedMC landscape**: summary of the bridge framework.

    1. embed_walk_agreement -- mixed walk = two-point walk under embedding (PROVED)
    2. embed_valid -- embedded selection is valid (PROVED)
    3. embed_factor_agreement -- factors agree (PROVED)
    4. two_point_capture_implies_mixed_capture -- two-point capture gives mixed capture (PROVED)
    5. embed_all_true_eq_minFac -- all-true embedding = all-minFac (PROVED)
    6. UFDStrongImpliesMixedMC is the open bridge from abstract to concrete (OPEN)
    7. ufd_strong_implies_mixed_mc_chain -- UFDStrongImpliesMixedMC closes everything (PROVED) -/
theorem two_point_mixed_mc_landscape (acc : ℕ) (hacc : 2 ≤ acc) (σ : ℕ → Bool) :
    -- 1. Walk agreement
    (∀ n, mixedWalkProd acc (embedBoolToMixed acc σ) n = epsWalkProdFrom acc σ n)
    ∧
    -- 2. Embedding is valid
    ValidMixedSelection acc (embedBoolToMixed acc σ)
    ∧
    -- 3. Factor agreement
    (∀ n, mixedWalkFactor acc (embedBoolToMixed acc σ) n = epsWalkFactorFrom acc σ n)
    ∧
    -- 4. All-true embedding = all-minFac
    (embedBoolToMixed acc (fun _ => true) = minFacMixed)
    ∧
    -- 5. Bridge chain exists
    (UFDStrongImpliesMixedMC →
      (∀ (q : ℕ) (hqp : Fact (Nat.Prime q)), 5 ≤ q → @UFDStrong q hqp) →
      MixedMullinConjecture) :=
  ⟨embed_walk_agreement acc σ,
   embed_valid acc hacc σ,
   embed_factor_agreement acc σ,
   embed_all_true_eq_minFac acc,
   ufd_strong_implies_mixed_mc_chain⟩

end UFDBridge
