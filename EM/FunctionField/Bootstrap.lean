import EM.FunctionField.Analog

/-!
# Inductive Bootstrap for FF-MC

This file formalizes the inductive bootstrap reducing the Function Field Mullin
Conjecture (FF-MC) to a single open hypothesis (FFDynamicalHitting), mirroring
the integer bootstrap in `EquidistBootstrap.lean`.

## Key differences from the integer case

Over Z, `captures_target` shows `seq(n+1) = q` because primes are totally ordered
and `minFac` selects the unique smallest. Over F_p[t], irreducible polynomials of
the SAME degree can both divide ffProd(n)+1, so `ffSeq_minimal` only gives
degree minimality. We need an additional argument using:

1. **Injectivity** of ffSeq (proved from coprimality_cascade)
2. **Finiteness** of monic irreducibles of each degree over F_p
3. **Cofinal hitting**: FFDynamicalHitting provides hits at arbitrarily late steps

The combination: at each cofinal hit of Q on ffProd(n)+1, either Q is selected
or another irreducible of the same degree is selected (and consumed). Since there
are finitely many competitors and ffSeq is injective, eventually Q must be selected.

## Main results

- `ffProd_dvd_of_le` : product divisibility monotonicity
- `ffSeq_dvd_prod` : ffSeq(j) | ffProd(m) for j ≤ m
- `ffSeq_injective_proved` : Function.Injective d.ffSeq
- `ff_appeared_not_dvd_succ` : appeared irreducibles cannot divide ffProd(n)+1
- `ff_captures_degree` : degree-level capture (analog of captures_target)
- `ff_dh_implies_ffmc` : FFDynamicalHitting + FFFiniteIrreduciblesPerDegree → FFMullinConjecture
-/

namespace FunctionFieldAnalog

open Polynomial Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ## Section 1: Product Divisibility and Injectivity -/

/-- The running product at step j divides the running product at step k
    when j ≤ k. Proof by induction: ffProd(k+1) = ffProd(k) * ffSeq(k+1). -/
theorem ffProd_dvd_of_le (d : FFEMData p) {j k : ℕ} (hjk : j ≤ k) :
    d.ffProd j ∣ d.ffProd k := by
  induction k with
  | zero => simp [Nat.le_zero.mp hjk]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
    · exact dvd_refl _
    · rw [d.ffProd_succ k]
      exact dvd_mul_of_dvd_left (ih (by omega)) _

/-- ffSeq(j) divides ffProd(j): each sequence term is a factor of the
    running product at its own index. -/
theorem ffSeq_dvd_own_prod (d : FFEMData p) (j : ℕ) :
    d.ffSeq j ∣ d.ffProd j := by
  cases j with
  | zero => rw [d.ffSeq_zero, d.ffProd_zero]
  | succ n =>
    rw [d.ffProd_succ n]
    exact dvd_mul_left _ _

/-- ffSeq(j) divides ffProd(m) whenever j ≤ m.
    Proof: ffSeq(j) | ffProd(j) and ffProd(j) | ffProd(m). -/
theorem ffSeq_dvd_prod (d : FFEMData p) {j m : ℕ} (hjm : j ≤ m) :
    d.ffSeq j ∣ d.ffProd m :=
  dvd_trans (ffSeq_dvd_own_prod d j) (ffProd_dvd_of_le d hjm)

/-- ffSeq(0) = X is irreducible. Helper for the irreducibility proof. -/
private theorem ffSeq_zero_irreducible (d : FFEMData p) :
    Irreducible (d.ffSeq 0) := by
  rw [d.ffSeq_zero]; exact irreducible_X

/-- Every term of the FF-EM sequence is irreducible. -/
theorem ffSeq_irreducible' (d : FFEMData p) (n : ℕ) :
    Irreducible (d.ffSeq n) := by
  cases n with
  | zero => exact ffSeq_zero_irreducible d
  | succ n => exact (d.ffSeq_succ n).2.1

/-- If ffSeq(j) has appeared (j ≤ n), then ffSeq(j) cannot divide ffProd(n)+1
    because ffSeq(j) | ffProd(n) and the coprimality cascade forbids both. -/
theorem ff_appeared_not_dvd_succ (d : FFEMData p) {j n : ℕ} (hjn : j ≤ n) :
    ¬ (d.ffSeq j ∣ d.ffProd n + 1) := by
  intro hdvd_succ
  have hdvd_prod : d.ffSeq j ∣ d.ffProd n := ffSeq_dvd_prod d hjn
  exact coprimality_cascade p d (d.ffSeq j) (ffSeq_irreducible' d j) hdvd_prod hdvd_succ

/-- **Injectivity of ffSeq**: no monic irreducible appears twice.

    Proof: if ffSeq(j) = ffSeq(k) with j < k, then ffSeq(j) | ffProd(k-1)
    (since j < k implies j ≤ k-1) and ffSeq(k) | ffProd(k-1)+1 (by definition).
    Since ffSeq(j) = ffSeq(k), this polynomial divides both ffProd(k-1) and
    ffProd(k-1)+1, contradicting the coprimality cascade. -/
theorem ffSeq_injective_proved (d : FFEMData p) : Function.Injective d.ffSeq := by
  intro j k hjk
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hjlt | hklt
  · -- j < k: ffSeq(j) | ffProd(k-1) and ffSeq(k) | ffProd(k-1)+1
    have hdvd_prod : d.ffSeq j ∣ d.ffProd (k - 1) := ffSeq_dvd_prod d (by omega)
    have hdvd_succ : d.ffSeq k ∣ d.ffProd (k - 1) + 1 := by
      cases k with
      | zero => omega
      | succ n => exact (d.ffSeq_succ n).2.2
    rw [hjk] at hdvd_prod
    exact coprimality_cascade p d (d.ffSeq k) (ffSeq_irreducible' d k) hdvd_prod hdvd_succ
  · -- k < j: symmetric
    have hdvd_prod : d.ffSeq k ∣ d.ffProd (j - 1) := ffSeq_dvd_prod d (by omega)
    have hdvd_succ : d.ffSeq j ∣ d.ffProd (j - 1) + 1 := by
      cases j with
      | zero => omega
      | succ n => exact (d.ffSeq_succ n).2.2
    rw [← hjk] at hdvd_prod
    exact coprimality_cascade p d (d.ffSeq j) (ffSeq_irreducible' d j) hdvd_prod hdvd_succ

/-! ## Section 2: Bootstrap Definitions -/

/-- FF-MC holds below degree d0: all monic irreducible polynomials of degree
    strictly less than d0 appear in the FF-EM sequence. -/
def FFMCBelow (d : FFEMData p) (d0 : ℕ) : Prop :=
  ∀ Q : Polynomial (ZMod p), Q.Monic → Irreducible Q →
    Q.natDegree < d0 → ∃ n, d.ffSeq n = Q

/-- **FF Dynamical Hitting**: for every FFEMData and every monic irreducible Q,
    there exist cofinal indices n at which Q divides ffProd(n)+1.

    This is the function field analog of `DynamicalHitting` in EquidistBootstrap.lean.
    The cofinal property is essential: a single hit might be "stolen" by a
    competing irreducible of the same degree (unlike the integer case where
    primes are totally ordered). -/
def FFDynamicalHitting : Prop :=
  ∀ (d : FFEMData p),
  ∀ Q : Polynomial (ZMod p), Q.Monic → Irreducible Q →
    (∀ n, d.ffSeq n ≠ Q) →
    ∀ N, ∃ n, N ≤ n ∧ Q ∣ (d.ffProd n + 1)

/-- The set of monic irreducible polynomials of a given degree over F_p
    is finite. This is standard: there are at most p^d monic polynomials
    of degree d, and the irreducible ones form a subset.

    Stated as a Prop because the full formalization would require
    `Fintype` for bounded-degree polynomials, which needs substantial
    Mathlib infrastructure. -/
def FFFiniteIrreduciblesPerDegree : Prop :=
  ∀ (d : ℕ), Set.Finite {Q : Polynomial (ZMod p) | Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d}

/-! ## Section 3: Degree-Level Capture -/

/-- If Q divides ffProd(n)+1, then ffSeq(n+1) has degree at most deg(Q).
    This follows immediately from ffSeq_minimal. -/
theorem ff_degree_upper_bound (d : FFEMData p) (Q : Polynomial (ZMod p))
    (hQm : Q.Monic) (hQi : Irreducible Q) {n : ℕ}
    (hdvd : Q ∣ d.ffProd n + 1) :
    (d.ffSeq (n + 1)).natDegree ≤ Q.natDegree :=
  d.ffSeq_minimal n Q hQm hQi hdvd

/-- Sieve exclusion: if an irreducible P appeared at step j ≤ n, then
    P cannot divide ffProd(n)+1 (by the coprimality cascade). -/
theorem ff_sieve_exclusion (d : FFEMData p) {n : ℕ}
    (P : Polynomial (ZMod p)) (hPi : Irreducible P) {j : ℕ}
    (hj : j ≤ n) (hseq : d.ffSeq j = P) :
    ¬ (P ∣ d.ffProd n + 1) := by
  intro hdvd
  have hdvd_prod : P ∣ d.ffProd n := hseq ▸ ffSeq_dvd_prod d hj
  exact coprimality_cascade p d P hPi hdvd_prod hdvd

/-- Degree lower bound: if all monic irreducibles of degree < d0 have appeared
    by step n, then any monic irreducible factor of ffProd(n)+1 has degree ≥ d0. -/
theorem ff_degree_lower_bound (d : FFEMData p) {n d0 : ℕ}
    (hsieve : ∀ P : Polynomial (ZMod p), P.Monic → Irreducible P →
      P.natDegree < d0 → ∃ j, j ≤ n ∧ d.ffSeq j = P)
    (f : Polynomial (ZMod p)) (hfm : f.Monic) (hfi : Irreducible f)
    (hf_dvd : f ∣ d.ffProd n + 1) :
    d0 ≤ f.natDegree := by
  by_contra hlt
  push Not at hlt
  obtain ⟨j, hjn, hj⟩ := hsieve f hfm hfi hlt
  exact ff_sieve_exclusion d f hfi hjn hj hf_dvd

/-- **Degree-level capture**: if Q | ffProd(n)+1 and all irreds of degree < deg(Q)
    have appeared by step n, then deg(ffSeq(n+1)) = deg(Q). -/
theorem ff_captures_degree (d : FFEMData p) {n : ℕ}
    (Q : Polynomial (ZMod p)) (hQm : Q.Monic) (hQi : Irreducible Q)
    (hdvd : Q ∣ d.ffProd n + 1)
    (hsieve : ∀ P : Polynomial (ZMod p), P.Monic → Irreducible P →
      P.natDegree < Q.natDegree → ∃ j, j ≤ n ∧ d.ffSeq j = P) :
    (d.ffSeq (n + 1)).natDegree = Q.natDegree := by
  apply Nat.le_antisymm
  · exact ff_degree_upper_bound d Q hQm hQi hdvd
  · exact ff_degree_lower_bound d hsieve (d.ffSeq (n + 1))
      (d.ffSeq_succ n).1 (d.ffSeq_succ n).2.1 (d.ffSeq_succ n).2.2

/-! ## Section 4: The Sieve Gap -/

/-- **Sieve gap lemma**: if FFMCBelow d d0 holds, then for every n, all monic
    irreducibles of degree < d0 that appear do so at some definite index.
    Since ffSeq is injective, the set of indices where degree-< d0 irreds appear
    is finite, so there is a uniform upper bound N0.

    However, to COMPUTE this N0 requires knowing the set of monic irreducibles
    of degree < d0, which is where FFFiniteIrreduciblesPerDegree enters.

    We formalize this as: FFMCBelow + FFFiniteIrreduciblesPerDegree together
    give a uniform sieve gap. -/
theorem ff_sieve_gap (d : FFEMData p)
    (hfin : FFFiniteIrreduciblesPerDegree (p := p))
    {d0 : ℕ} (hbelow : FFMCBelow d d0) :
    ∃ N0, ∀ n, N0 ≤ n →
      ∀ P : Polynomial (ZMod p), P.Monic → Irreducible P →
        P.natDegree < d0 → ∃ j, j ≤ n ∧ d.ffSeq j = P := by
  -- The set of all monic irreducibles of degree < d0
  set S := {Q : Polynomial (ZMod p) | Q.Monic ∧ Irreducible Q ∧ Q.natDegree < d0}
  -- S is finite: it's contained in the union of finite sets for each degree < d0
  have hS_fin : Set.Finite S := by
    apply Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iio d0)
      (fun e _ => hfin e))
    intro Q ⟨hm, hi, hd⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨Q.natDegree, Set.mem_Iio.mpr hd, hm, hi, rfl⟩
  -- For each Q in S, get its appearance index
  have happ : ∀ Q ∈ S, ∃ k, d.ffSeq k = Q := by
    intro Q ⟨hm, hi, hd⟩
    exact hbelow Q hm hi hd
  -- Use the axiom of choice to pick indices, then take the max
  -- Since S is finite, we can take the supremum of appearance indices
  by_cases hS_empty : S = ∅
  · -- No irreducibles of degree < d0: N0 = 0 works vacuously
    exact ⟨0, fun n _ P hPm hPi hPd => absurd (show P ∈ S from ⟨hPm, hPi, hPd⟩)
      (by simp [hS_empty])⟩
  · -- S is nonempty and finite: take N0 = max of appearance indices
    -- For each Q in S, choose its index
    have hchoice : ∀ Q ∈ S, ∃ k, d.ffSeq k = Q := happ
    -- Build a function from S to ℕ (appearance indices)
    set f : S → ℕ := fun ⟨Q, hQ⟩ => (hchoice Q hQ).choose
    have hf_spec : ∀ (x : S), d.ffSeq (f x) = (x : Polynomial (ZMod p)) :=
      fun ⟨Q, hQ⟩ => (hchoice Q hQ).choose_spec
    -- S is finite, so f has a finite range; take N0 = sup of range
    haveI : Fintype S := hS_fin.fintype
    set N0 := Finset.sup Finset.univ f with hN0_def
    refine ⟨N0, fun n hn P hPm hPi hPd => ?_⟩
    have hPS : P ∈ S := ⟨hPm, hPi, hPd⟩
    have hP_sub : ⟨P, hPS⟩ ∈ (Finset.univ : Finset S) := Finset.mem_univ _
    have hfP_le : f ⟨P, hPS⟩ ≤ N0 := by
      rw [hN0_def]
      exact Finset.le_sup hP_sub
    exact ⟨f ⟨P, hPS⟩, by omega, hf_spec ⟨P, hPS⟩⟩

/-! ## Section 5: Element Capture via Exhaustion of Competitors

Over integers, `captures_target` gives `seq(n+1) = q` directly because primes
are totally ordered by size. Over F_p[t], multiple irreducibles of the same
degree can divide ffProd(n)+1. The exhaustion argument uses:

1. There are finitely many monic irreducibles of each degree (FFFiniteIrreduciblesPerDegree).
2. ffSeq is injective (ffSeq_injective_proved).
3. At each cofinal hit, a distinct irreducible of the target degree is consumed.
4. After exhausting all competitors, Q itself must be selected.

The key Set.Infinite / Set.Finite contradiction: the set of hitting times maps
injectively (via ffSeq) into a finite set of competitors, but cofinality gives
infinitely many hitting times. -/

/-- Helper: the set of hitting indices past a bound is infinite when
    cofinal hitting holds. -/
private theorem ff_hitting_set_infinite
    (d_data : FFEMData p) (Q : Polynomial (ZMod p))
    (hcofinal : ∀ N, ∃ n, N ≤ n ∧ Q ∣ (d_data.ffProd n + 1))
    (N0 : ℕ) :
    Set.Infinite {m : ℕ | N0 ≤ m ∧ Q ∣ d_data.ffProd m + 1} := by
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨m, hm_ge, hm_dvd⟩ := hcofinal (max (n + 1) N0)
  exact ⟨m, ⟨by omega, hm_dvd⟩, by omega⟩

/-- **Element capture via competitor exhaustion**: if Q has cofinal hits and
    the set of same-degree competitors is finite, then Q eventually appears.

    This is the function field version of the integer `captures_target`, adapted
    for the degree-only minimality setting. The proof shows the set of consumed
    competitors is infinite (from cofinal hitting + injectivity), contradicting
    finiteness of the competitor set. -/
theorem ff_element_capture
    (hfin : FFFiniteIrreduciblesPerDegree (p := p))
    (d_data : FFEMData p)
    (Q : Polynomial (ZMod p)) (hQm : Q.Monic) (hQi : Irreducible Q)
    (hcofinal : ∀ N, ∃ n, N ≤ n ∧ Q ∣ (d_data.ffProd n + 1))
    (hsieve_gap : ∃ N0, ∀ n, N0 ≤ n →
      ∀ P : Polynomial (ZMod p), P.Monic → Irreducible P →
        P.natDegree < Q.natDegree → ∃ j, j ≤ n ∧ d_data.ffSeq j = P) :
    ∃ n, d_data.ffSeq n = Q := by
  by_contra hQ_not_appear
  push Not at hQ_not_appear
  obtain ⟨N0, hN0⟩ := hsieve_gap
  -- Define the competitor set: monic irreducibles of degree = deg(Q), excluding Q
  set S' := {R : Polynomial (ZMod p) | R.Monic ∧ Irreducible R ∧
    R.natDegree = Q.natDegree ∧ R ≠ Q}
  have hS'_fin : Set.Finite S' := by
    apply Set.Finite.subset (hfin Q.natDegree)
    intro R ⟨hm, hi, hd, _⟩
    exact ⟨hm, hi, hd⟩
  -- The hitting set is infinite
  have hH_inf := ff_hitting_set_infinite d_data Q hcofinal N0
  -- Define the map: hitting indices → S' via m ↦ ffSeq(m+1)
  -- At each hitting time m ≥ N0, ffSeq(m+1) has degree = deg(Q) and ≠ Q
  have hval_in_S' : ∀ m, N0 ≤ m → Q ∣ d_data.ffProd m + 1 →
      d_data.ffSeq (m + 1) ∈ S' := by
    intro m hm hdvd
    refine ⟨(d_data.ffSeq_succ m).1, (d_data.ffSeq_succ m).2.1,
      ff_captures_degree d_data Q hQm hQi hdvd (hN0 m hm), ?_⟩
    exact fun h => hQ_not_appear (m + 1) h
  -- The image of the hitting set under m ↦ ffSeq(m+1) is contained in S'
  -- Build the image set
  set T := d_data.ffSeq '' (Nat.succ '' {m : ℕ | N0 ≤ m ∧ Q ∣ d_data.ffProd m + 1})
  -- T ⊆ S'
  have hT_sub : T ⊆ S' := by
    intro x hx
    obtain ⟨k, ⟨m, ⟨hm_ge, hm_dvd⟩, rfl⟩, rfl⟩ := hx
    exact hval_in_S' m hm_ge hm_dvd
  -- T is infinite: the preimage set is infinite and the composition is injective
  have hT_inf : Set.Infinite T := by
    have hsucc_inf : Set.Infinite (Nat.succ '' {m : ℕ | N0 ≤ m ∧ Q ∣ d_data.ffProd m + 1}) :=
      hH_inf.image (fun _ _ h => by omega)
    exact hsucc_inf.image (ffSeq_injective_proved d_data).injOn
  -- But T ⊆ S' and S' is finite: contradiction
  exact hS'_fin.not_infinite (hT_inf.mono hT_sub)

/-! ## Section 6: The Main Bootstrap -/

/-- **Sieve gap from FFMCBelow**: if all irreds of degree < d0 have appeared,
    then past a uniform bound, no irred of degree < d0 divides ffProd(n)+1.

    This combines FFMCBelow (existence of appearance indices) with
    FFFiniteIrreduciblesPerDegree (finiteness, to get a uniform bound). -/
theorem ff_mcbelow_implies_sieve_gap (d : FFEMData p)
    (hfin : FFFiniteIrreduciblesPerDegree (p := p))
    {d0 : ℕ} (hbelow : FFMCBelow d d0) :
    ∃ N0, ∀ n, N0 ≤ n →
      ∀ P : Polynomial (ZMod p), P.Monic → Irreducible P →
        P.natDegree < d0 → ∃ j, j ≤ n ∧ d.ffSeq j = P :=
  ff_sieve_gap d hfin hbelow

/-- **Exists bound for FF**: given FFMCBelow d d0, there exists a uniform
    bound N such that all irreds of degree < d0 have appeared by step N.
    This is the FF analog of `exists_bound` from MullinConjectures.lean. -/
theorem ff_exists_bound (d : FFEMData p)
    (hfin : FFFiniteIrreduciblesPerDegree (p := p))
    {d0 : ℕ} (hbelow : FFMCBelow d d0) :
    ∃ N, ∀ Q : Polynomial (ZMod p), Q.Monic → Irreducible Q →
      Q.natDegree < d0 → ∃ j, j ≤ N ∧ d.ffSeq j = Q := by
  obtain ⟨N0, hN0⟩ := ff_sieve_gap d hfin hbelow
  exact ⟨N0, fun Q hQm hQi hQd => hN0 N0 le_rfl Q hQm hQi hQd⟩

/-- **FFMCBelow is monotone**: if FFMCBelow d d0 and d1 ≤ d0, then FFMCBelow d d1. -/
theorem ffMCBelow_mono (d : FFEMData p) {d0 d1 : ℕ} (h : d1 ≤ d0)
    (hbelow : FFMCBelow d d0) : FFMCBelow d d1 :=
  fun Q hQm hQi hQd => hbelow Q hQm hQi (lt_of_lt_of_le hQd h)

/-- **FF-MC below degree 1 is vacuous**: there are no monic irreducible
    polynomials of degree 0 (since irreducible polynomials have degree ≥ 1). -/
theorem ffMCBelow_zero (d : FFEMData p) : FFMCBelow d 0 :=
  fun _ _ hQi hQd => absurd (Irreducible.natDegree_pos hQi) (by omega)

/-- **FF-MC below degree 1**: the only monic irreducible of degree 0... actually
    there are none (degree 0 means constant, and constants are units, not
    irreducible). So FFMCBelow d 1 is equivalent to FFMCBelow d 0. -/
theorem ffMCBelow_one (d : FFEMData p) : FFMCBelow d 1 :=
  fun _ _ hQi hQd => absurd (Irreducible.natDegree_pos hQi) (by omega)

/-- **The one-hypothesis reduction for FF-MC**: FFDynamicalHitting together with
    finiteness of irreducibles per degree implies FFMullinConjecture.

    The proof uses strong induction on degree. At degree d0:
    - The induction hypothesis gives FFMCBelow d d0.
    - The sieve gap lemma gives a uniform bound past which all degree-< d0
      irreds have appeared.
    - FFDynamicalHitting provides cofinal hits.
    - Element capture (via competitor exhaustion) gives the appearance of Q. -/
theorem ff_dh_implies_ffmc
    (hdh : FFDynamicalHitting (p := p))
    (hfin : FFFiniteIrreduciblesPerDegree (p := p)) :
    FFMullinConjecture p := by
  intro d Q hQm hQi
  -- Induction on degree: suffices to prove for all degrees d0, all irreds
  -- of degree ≤ d0 appear.
  suffices h : ∀ d0, FFMCBelow d d0 by
    exact h (Q.natDegree + 1) Q hQm hQi (by omega)
  intro d0
  induction d0 with
  | zero => exact ffMCBelow_zero d
  | succ d0 ih =>
    -- Need to show: all irreds of degree < d0 + 1, i.e., degree ≤ d0, appear.
    intro R hRm hRi hRd
    -- If deg(R) < d0, use IH
    rcases Nat.lt_or_ge R.natDegree d0 with hlt | hge
    · exact ih R hRm hRi hlt
    · -- deg(R) = d0 (since deg(R) < d0 + 1 and deg(R) ≥ d0)
      have hRd0 : R.natDegree = d0 := by omega
      -- By contradiction: assume R never appears
      by_contra hR_not_exist
      have hR_not_appear : ∀ n, d.ffSeq n ≠ R := by
        intro n hn; exact hR_not_exist ⟨n, hn⟩
      -- FFDynamicalHitting gives cofinal hits
      have hcofinal : ∀ N, ∃ n, N ≤ n ∧ R ∣ d.ffProd n + 1 :=
        hdh d R hRm hRi hR_not_appear
      -- IH gives FFMCBelow d d0, which covers all irreds of degree < d0 = deg(R)
      have hbelow : FFMCBelow d d0 := ih
      -- Sieve gap from IH
      have hsieve := ff_mcbelow_implies_sieve_gap d hfin hbelow
      -- Rewrite sieve gap in terms of R's degree
      have hsieve' : ∃ N0, ∀ n, N0 ≤ n →
          ∀ P : Polynomial (ZMod p), P.Monic → Irreducible P →
            P.natDegree < R.natDegree → ∃ j, j ≤ n ∧ d.ffSeq j = P := by
        obtain ⟨N0, hN0⟩ := hsieve
        exact ⟨N0, fun n hn P hPm hPi hPd => hN0 n hn P hPm hPi (hRd0 ▸ hPd)⟩
      -- Element capture gives R appearing, contradiction
      exact hR_not_exist (ff_element_capture hfin d R hRm hRi hcofinal hsieve')

/-! ## Section 7: Landscape and Summary -/

/-- FFDynamicalHitting implies that all irreducibles eventually appear,
    conditional on finiteness of irreducibles per degree.

    This is the function field analog of `dynamical_hitting_implies_mullin`. -/
theorem ff_dh_finiteness_landscape :
    -- (1) Injectivity of ffSeq (PROVED)
    (∀ (d : FFEMData p), Function.Injective d.ffSeq) ∧
    -- (2) Degree-level capture (PROVED)
    True ∧
    -- (3) Main reduction: FFDH + finiteness → FF-MC (PROVED)
    (FFDynamicalHitting (p := p) → FFFiniteIrreduciblesPerDegree (p := p) →
      FFMullinConjecture p) :=
  ⟨fun d => ffSeq_injective_proved d,
   trivial,
   fun hdh hfin => ff_dh_implies_ffmc hdh hfin⟩

end FunctionFieldAnalog
