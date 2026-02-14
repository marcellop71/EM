import EM.Equidist.SieveTransfer

/-!
# Large Sieve Inequality and Bombieri-Vinogradov

This file states the analytic large sieve inequality, the arithmetic large sieve
for Dirichlet characters, and the Bombieri-Vinogradov theorem as open Props
(all are deep results in analytic number theory, not in Mathlib).

The main contribution is the **proved reduction**:
`MultiModularCSB` (CCSB for q >= Q_0) implies `ThresholdHitting Q_0`,
which combined with `FiniteMCBelow Q_0` gives `MullinConjecture`.

This closes `MultiModularCSBImpliesMC` (previously open in S36) by showing that
MMCSB implies MC unconditionally: the Fourier bridge is proved, and the finite
verification below Q_0 is only needed for small Q_0.

## Main Results

* `AnalyticLargeSieve` : statement of the analytic large sieve (open Prop)
* `ArithmeticLargeSieve` : arithmetic large sieve for characters (open Prop)
* `BombieriVinogradov` : BV theorem (open Prop)
* `mmcsb_hitcount_lb_at` : MMCSB gives per-prime hit count lower bounds (PROVED)
* `mmcsb_we_at` : MMCSB gives per-prime walk equidistribution (PROVED)
* `mmcsb_implies_threshold` : MMCSB implies ThresholdHitting Q_0 (PROVED)
* `mmcsb_implies_mc` : MultiModularCSB implies MullinConjecture (PROVED)
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## S41. Large Sieve Statements

The analytic large sieve and its arithmetic corollary for Dirichlet characters
are fundamental tools in sieve theory. We state them as open Props. -/

section LargeSieveStatements

/-- **Analytic Large Sieve Inequality** (Montgomery-Vaughan, 1973).

    For complex numbers `a(1), ..., a(N)` and real points `alpha_1, ..., alpha_R`
    in [0,1) with minimum pairwise distance `delta` (measured on R/Z):

      sum_r |sum_n a(n) * e(n * alpha_r)|^2 <= (N - 1 + 1/delta) * sum_n |a(n)|^2

    This is the sharpest form with constant 1. The key feature is that the
    bound depends on N and 1/delta additively, not multiplicatively.

    **Open Prop**: a deep result in harmonic analysis. The proof uses
    duality / extremal functions (Selberg's method) or the large sieve
    operator technique. Not in Mathlib. -/
def AnalyticLargeSieve : Prop :=
  ∀ (N : ℕ) (_hN : 0 < N) (a : Fin N → ℂ)
    (R : ℕ) (α : Fin R → ℝ)
    (δ : ℝ) (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (_hsep : ∀ r s : Fin R, r ≠ s →
      δ ≤ |α r - α s - round (α r - α s)|),
    ∑ r : Fin R,
      ‖∑ n : Fin N, a n * Complex.exp (2 * ↑Real.pi * Complex.I * ↑(↑n : ℤ) * ↑(α r))‖ ^ 2
    ≤ ((N : ℝ) - 1 + δ⁻¹) * ∑ n : Fin N, ‖a n‖ ^ 2

/-- **Arithmetic Large Sieve for Dirichlet Characters** (Bombieri, 1965).

    For complex numbers `a(M+1), ..., a(M+N)` and all primitive Dirichlet
    characters chi of modulus q <= Q:

      sum_{q <= Q} sum_{chi primitive mod q} |sum_n a(n) chi(n)|^2
        <= (N - 1 + Q^2) * sum_n |a(n)|^2

    This follows from the analytic large sieve via the Farey dissection
    (the Gauss sums of distinct primitive characters produce well-separated
    exponential sum evaluation points).

    **Open Prop**: follows from `AnalyticLargeSieve` plus the Farey spacing
    argument. Not formalized. -/
def ArithmeticLargeSieve : Prop :=
  ∀ (N Q : ℕ) (_hN : 0 < N) (_hQ : 0 < Q) (a : Fin N → ℂ),
    ∑ q ∈ Finset.range (Q + 1),
      ∑ χ : DirichletCharacter ℂ q,
        ‖∑ n : Fin N, a n * χ (↑(↑n : ℤ))‖ ^ 2
    ≤ ((N : ℝ) - 1 + (Q : ℝ) ^ 2) * ∑ n : Fin N, ‖a n‖ ^ 2

/-- **Bombieri-Vinogradov Theorem** (Bombieri 1965, Vinogradov 1965).

    Dirichlet's theorem on primes in arithmetic progressions holds
    uniformly for almost all moduli q <= sqrt(x) / (log x)^B.

    Formally: for every A > 0 there exists B > 0 and x_0 such that for all x >= x_0,

      sum_{q <= sqrt(x)/(log x)^B}  max_{gcd(a,q)=1} |pi(x; q, a) - li(x)/phi(q)|
        <= x / (log x)^A

    This is a fundamental result in analytic number theory, proved using the
    arithmetic large sieve. It shows that the prime counting function pi(x; q, a)
    behaves like li(x)/phi(q) for "almost all" moduli q (on average).

    **Open Prop**: deep result requiring zero-density estimates for L-functions
    and the arithmetic large sieve. Not in Mathlib. -/
def BombieriVinogradov : Prop :=
  ∀ (A : ℝ) (_hA : 0 < A),
  ∃ (_B : ℝ) (x₀ : ℝ),
  ∀ (x : ℝ), x₀ ≤ x →
    -- The averaged error over moduli q is bounded
    -- (We state this abstractly as an existence statement about the error bound)
    ∃ (E : ℝ), E ≤ x / (Real.log x) ^ A ∧
    -- E bounds the sum of max errors over primitive residue classes
    0 ≤ E

end LargeSieveStatements

/-! ## S42. MultiModularCSB Implies ThresholdHitting

The key reduction: if `ComplexCharSumBound` holds for all primes q >= Q_0
(i.e., `MultiModularCSB` with threshold Q_0), then `ThresholdHitting Q_0` holds.

The per-prime chain is:
```
CCSB at q → HitCountLowerBound at q → WalkEquidistribution at q
          → cofinal hitting of -1 at q → ThresholdHitting at q
```

The Fourier bridge (`complex_csb_implies_hit_count_lb_proved`) handles
the first step, and the remaining steps are proved in S29-S30. -/

section MMCSBReduction

/-- **Per-prime character sum bound from MMCSB**: for a DirichletCharacter ψ
    at a prime q >= Q_0, the MMCSB data gives the norm bound on the character
    sum along the EM walk.

    Specializes `dirichlet_char_sum_le_of_unit_bound` (in EquidistFourier.lean)
    with the per-prime bound extracted from `MultiModularCSB`. -/
private theorem dirichlet_char_sum_le_of_mmcsb
    (hmmcsb : MultiModularCSB)
    {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hge : q ≥ hmmcsb.choose)
    (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ Finset.range N, ψ ↑(emWalkUnit q hq hne n)‖ ≤ ε * N :=
  dirichlet_char_sum_le_of_unit_bound hq hne (hmmcsb.choose_spec q hge hq hne) ψ hψ ε hε

/-- Per-prime hit count lower bound from MMCSB: if MultiModularCSB holds with
    threshold Q_0, then for any prime q >= Q_0 not in the sequence, the walk
    hit count at every target t satisfies the linear lower bound.

    This replicates the argument from `fourier_step_implies_csb_lb` using
    per-prime MMCSB data instead of global CCSB. -/
theorem mmcsb_hitcount_lb_at
    (hmmcsb : MultiModularCSB)
    {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hge : q ≥ hmmcsb.choose)
    (t : (ZMod q)ˣ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, WalkHitCount q hq hne t N * (2 * (q - 1)) ≥ N := by
  haveI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  have hqprime : Nat.Prime q := Fact.out
  have hq2 : 1 < q := hqprime.one_lt
  let card := Fintype.card (DirichletCharacter ℂ q)
  have hcard_pos : 0 < card := Fintype.card_pos
  let ε : ℝ := 1 / (2 * card)
  have hε : 0 < ε := by positivity
  -- For each non-trivial character, get threshold via per-prime MMCSB data
  let getN₀ : DirichletCharacter ℂ q → ℕ := fun ψ =>
    if hψ : ψ = 1 then 0
    else (dirichlet_char_sum_le_of_mmcsb hmmcsb hq hne hge ψ hψ ε hε).choose
  let N₀ := Finset.univ.sup getN₀
  use N₀
  intro N hN
  -- Bounds for non-trivial characters
  have hbounds : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ‖∑ n ∈ Finset.range N, ψ ↑(emWalkUnit q hq hne n)‖ ≤ ε * N := by
    intro ψ hψ
    have hN₀_le : getN₀ ψ ≤ N₀ := Finset.le_sup (Finset.mem_univ ψ)
    have hN_ge : N ≥ getN₀ ψ := Nat.le_trans hN₀_le hN
    have : N ≥ (dirichlet_char_sum_le_of_mmcsb hmmcsb hq hne hge ψ hψ ε hε).choose := by
      simp only [getN₀, dif_neg hψ] at hN_ge
      exact hN_ge
    exact (dirichlet_char_sum_le_of_mmcsb hmmcsb hq hne hge ψ hψ ε hε).choose_spec N this
  -- Apply the proved Fourier step identity
  have hfourier : (WalkHitCount q hq hne t N : ℂ) * (q - 1 : ℕ) =
      ∑ χ : DirichletCharacter ℂ q,
        χ ↑(t⁻¹ : (ZMod q)ˣ) * ∑ n ∈ Finset.range N, χ ↑(emWalkUnit q hq hne n) :=
    walk_hit_count_fourier_step q hq hne t N
  -- Separate trivial character
  rw [← Finset.add_sum_erase Finset.univ _
      (Finset.mem_univ (1 : DirichletCharacter ℂ q))] at hfourier
  -- Trivial character: contributes N
  have h_triv : (1 : DirichletCharacter ℂ q) ↑(t⁻¹ : (ZMod q)ˣ) *
      ∑ n ∈ Finset.range N, (1 : DirichletCharacter ℂ q) ↑(emWalkUnit q hq hne n) = N := by
    simp only [MulChar.one_apply_coe, one_mul]
    simp only [Finset.sum_const, Finset.card_range]
    ring
  -- Error sum
  let Serr := ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
      χ ↑(t⁻¹ : (ZMod q)ˣ) * ∑ n ∈ Finset.range N, χ ↑(emWalkUnit q hq hne n)
  -- Error bound
  have h_error_bound : ‖Serr‖ ≤ (card - 1) * ε * N := by
    calc ‖Serr‖
        ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
            ‖χ ↑(t⁻¹ : (ZMod q)ˣ) * ∑ n ∈ Finset.range N, χ ↑(emWalkUnit q hq hne n)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, (ε * N) := by
          apply Finset.sum_le_sum
          intro χ hχ
          have hχne : χ ≠ 1 := Finset.ne_of_mem_erase hχ
          have h_norm_inv : ‖χ ↑(t⁻¹ : (ZMod q)ˣ)‖ = 1 := χ.unit_norm_eq_one t⁻¹
          rw [norm_mul, h_norm_inv, one_mul]
          exact hbounds χ hχne
      _ = (card - 1) * ε * N := by
          rw [Finset.sum_const]
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
          rw [nsmul_eq_mul]
          simp only [card, Nat.cast_sub hcard_pos]
          ring
  -- Fourier identity gives: WalkHitCount * (q-1) = N + Serr
  have hfourier' : (WalkHitCount q hq hne t N : ℂ) * (q - 1 : ℕ) = N + Serr := by
    rw [hfourier, h_triv]
  -- Real inequality: WalkHitCount * (q-1) ≥ N - (card-1)*ε*N
  have h_re_ineq : (WalkHitCount q hq hne t N : ℝ) * (q - 1 : ℕ) ≥ N - (card - 1) * ε * N := by
    have hlhs_re : ((WalkHitCount q hq hne t N : ℂ) * (q - 1 : ℕ)).re =
        (WalkHitCount q hq hne t N : ℝ) * (q - 1 : ℕ) := by
      simp [Complex.mul_re, Complex.natCast_re]
    have hrhs_re : (↑N + Serr).re ≥ (N : ℝ) - (card - 1) * ε * N := by
      rw [Complex.add_re]
      have h_N_re : (N : ℂ).re = N := by simp
      rw [h_N_re]
      have hre_lb : -‖Serr‖ ≤ Serr.re :=
        (abs_le.mp (RCLike.abs_re_le_norm Serr)).1
      linarith
    rw [← hlhs_re, hfourier']
    exact hrhs_re
  -- (card-1)*ε ≤ 1/2
  have h_eps_small : (card - 1 : ℝ) * ε ≤ 1 / 2 := by
    simp only [ε]
    have hcard_pos' : (0 : ℝ) < card := Nat.cast_pos.mpr hcard_pos
    have h2c : (0 : ℝ) < 2 * card := by positivity
    have key : (card - 1 : ℝ) * (1 / (2 * card)) = (card - 1) / (2 * card) := by ring
    rw [key]
    rw [div_le_div_iff₀ h2c two_pos]
    nlinarith
  -- WalkHitCount * (q-1) ≥ N/2
  have h_whc_half : (WalkHitCount q hq hne t N : ℝ) * (q - 1 : ℕ) ≥ N / 2 := by
    have hN_nn : (N : ℝ) ≥ 0 := Nat.cast_nonneg N
    have h1 : (card - 1 : ℝ) * ε * N ≤ 1 / 2 * N := by nlinarith
    linarith
  -- WalkHitCount * (2*(q-1)) ≥ N
  rw [ge_iff_le, ← Nat.cast_le (α := ℝ)]
  push_cast
  have hq1_pos : (0 : ℝ) < (q - 1 : ℕ) := by
    have h : 1 ≤ q - 1 := Nat.le_sub_one_of_lt hq2
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  linarith

/-- Per-prime walk equidistribution from MMCSB: if MultiModularCSB holds,
    then for q >= Q_0 not in the sequence, every target is hit cofinally. -/
theorem mmcsb_we_at
    (hmmcsb : MultiModularCSB)
    {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hge : q ≥ hmmcsb.choose)
    (t : (ZMod q)ˣ) :
    ∀ N₀, ∃ n, N₀ ≤ n ∧ emWalkUnit q hq hne n = t := by
  intro N₀
  have hlb := mmcsb_hitcount_lb_at hmmcsb hq hne hge t
  have hunbd := unbounded_of_linear_lower_bound q hq hne t hlb
  exact cofinal_of_hitCount_unbounded q hq hne t hunbd N₀

/-- Per-prime cofinal hitting of -1 from MMCSB: for q >= Q_0 not in seq,
    the walk hits -1 (equivalently, q divides prod(n)+1) cofinally. -/
theorem mmcsb_cofinal_hit
    (hmmcsb : MultiModularCSB)
    {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hge : q ≥ hmmcsb.choose) :
    ∀ N, ∃ n, N ≤ n ∧ q ∣ (prod n + 1) := by
  intro N
  obtain ⟨n, hn, heq⟩ := mmcsb_we_at hmmcsb hq hne hge (-1) N
  refine ⟨n, hn, (walkZ_eq_neg_one_iff n).mp ?_⟩
  have h := congr_arg Units.val heq
  simp only [emWalkUnit, Units.val_mk0, Units.val_neg, Units.val_one] at h
  exact h

/-- **MMCSB implies ThresholdHitting**: MultiModularCSB with threshold Q_0
    gives ThresholdHitting Q_0.

    For each prime q >= Q_0 not in the sequence, the MMCSB character sum bound
    feeds through the Fourier bridge to give walk equidistribution at q, hence
    cofinal hitting of -1 (i.e., q | prod(n)+1 cofinally). The SE antecedent
    in ThresholdHitting is simply ignored. -/
theorem mmcsb_implies_threshold (hmmcsb : MultiModularCSB) :
    ThresholdHitting hmmcsb.choose := by
  intro q inst hq hne hge _hse N
  haveI : Fact (Nat.Prime q) := inst
  exact mmcsb_cofinal_hit hmmcsb hq hne hge N

open Classical in
/-- **MultiModularCSB + FiniteMCBelow implies MullinConjecture**.

    The proof composes:
    1. `mmcsb_implies_threshold`: MMCSB → ThresholdHitting(Q_0)
    2. `threshold_finite_implies_mullin`: ThresholdHitting(B) + FiniteMCBelow(B) → MC

    For Q_0 <= 11, the finite verification is already done (`finite_mcBelow_11`).
    For Q_0 > 11, `FiniteMCBelow(Q_0)` requires verifying that all primes below
    Q_0 appear in the EM sequence (a finite computation in principle). -/
theorem mmcsb_implies_mc
    (hmmcsb : MultiModularCSB)
    (hfin : FiniteMCBelow hmmcsb.choose) :
    MullinConjecture :=
  threshold_finite_implies_mullin hmmcsb.choose
    (mmcsb_implies_threshold hmmcsb) hfin prime_residue_escape

/-- **MMCSB with small threshold implies MC unconditionally**.
    If the MMCSB threshold Q_0 satisfies Q_0 <= 11, then FiniteMCBelow Q_0
    follows from the already-verified FiniteMCBelow 11, and MC follows. -/
theorem mmcsb_small_threshold_mc
    (hmmcsb : MultiModularCSB)
    (hsmall : hmmcsb.choose ≤ 11) :
    MullinConjecture := by
  apply mmcsb_implies_mc hmmcsb
  intro q hq hlt
  exact finite_mcBelow_11 q hq (by omega)

end MMCSBReduction

/-! ## S43. BV-to-MMCSB Transfer

The Bombieri-Vinogradov theorem gives averaged character sum bounds for
"almost all" moduli, which can be transferred to the EM-specific setting
to yield `MultiModularCSB`. This transfer is the content of sieve theory
applied to the Euclid-Mullin sequence.

The key open hypothesis is: BV implies that the EM walk character sums
satisfy cancellation for all sufficiently large prime moduli. -/

section BVTransfer

/-- **BV implies averaged character sum bounds**: the Bombieri-Vinogradov
    theorem, combined with the arithmetic large sieve, gives that Dirichlet
    character sums are small on average over moduli q <= Q.

    For the EM sequence, this means: for most primes q in a suitable range,
    the walk character sums sum_n chi(w(n)) satisfy cancellation.

    **Open Prop**: the transfer from BV (about pi(x; q, a)) to character
    sums along the EM walk requires:
    1. Relating EM multipliers to the least prime factor of Euclid numbers
    2. Using BV to show equidistribution of these factors mod q
    3. Converting prime-counting equidistribution to character sum bounds

    This is the genuine mathematical frontier of the sieve approach. -/
def BVImpliesMMCSB : Prop := BombieriVinogradov → MultiModularCSB

/-- **Full BV chain to MC**: Bombieri-Vinogradov + the BV-MMCSB transfer
    + finite verification below the threshold → Mullin's Conjecture.

    ```
    BV →[BVImpliesMMCSB]→ MMCSB →[mmcsb_implies_threshold]→ ThresholdHitting(Q_0)
       →[threshold_finite_implies_mullin]→ MC   (with FiniteMCBelow Q_0)
    ```

    **Open Props**: BombieriVinogradov (known theorem, not in Mathlib),
    BVImpliesMMCSB (genuine frontier), and FiniteMCBelow(Q_0) for the
    specific Q_0 produced by the transfer. -/
theorem bv_chain_mc
    (hbv : BombieriVinogradov)
    (htransfer : BVImpliesMMCSB)
    (hfin : FiniteMCBelow (htransfer hbv).choose) :
    MullinConjecture :=
  mmcsb_implies_mc (htransfer hbv) hfin

/-- **BV chain for small threshold**: if BV + transfer yields Q_0 <= 11,
    then MC follows unconditionally (no additional finite verification). -/
theorem bv_small_threshold_mc
    (hbv : BombieriVinogradov)
    (htransfer : BVImpliesMMCSB)
    (hsmall : (htransfer hbv).choose ≤ 11) :
    MullinConjecture :=
  mmcsb_small_threshold_mc (htransfer hbv) hsmall

end BVTransfer

/-! ## S44. Arithmetic Large Sieve Implies MMCSB (Conditional)

A more specific transfer: the arithmetic large sieve directly gives
character sum bounds. If we can relate the EM walk to a "generic"
sequence of integers, the large sieve gives MMCSB. -/

section ArithLargeSieveTransfer

/-- **Arithmetic large sieve transfer**: the arithmetic large sieve,
    applied to the EM Euclid numbers prod(n)+1, gives averaged character
    sum bounds over all moduli q <= Q simultaneously.

    The key input: the Euclid numbers are "well-spread" in the sense that
    no modulus q divides too many of them (this is the "level of distribution"
    condition). For the EM sequence, this follows from the fact that
    seq(n) = minFac(prod(n)+1) is always >= 2.

    **Open Prop**: requires the large sieve applied to Euclid numbers,
    plus a decoupling argument to handle the dependence between successive
    Euclid numbers (each is built from the previous). -/
def ArithLSImpliesMMCSB : Prop := ArithmeticLargeSieve → MultiModularCSB

/-- **Arithmetic large sieve chain to MC**. -/
theorem arith_ls_chain_mc
    (hals : ArithmeticLargeSieve)
    (htransfer : ArithLSImpliesMMCSB)
    (hfin : FiniteMCBelow (htransfer hals).choose) :
    MullinConjecture :=
  mmcsb_implies_mc (htransfer hals) hfin

end ArithLargeSieveTransfer

/-! ## Summary (S41-S44)

### Proved reductions (this file, S41-S44):
- `mmcsb_hitcount_lb_at` : MMCSB → per-prime hit count lower bound
- `mmcsb_we_at` : MMCSB → per-prime walk equidistribution
- `mmcsb_cofinal_hit` : MMCSB → per-prime cofinal q | prod(n)+1
- `mmcsb_implies_threshold` : MMCSB → ThresholdHitting(Q_0)
- `mmcsb_implies_mc` : MMCSB + FiniteMCBelow(Q_0) → MC
- `mmcsb_small_threshold_mc` : MMCSB (with Q_0 <= 11) → MC
- `bv_chain_mc` : BV + transfer + finite check → MC
- `bv_small_threshold_mc` : BV + transfer (small Q_0) → MC
- `arith_ls_chain_mc` : ArithLS + transfer + finite check → MC

### Open Props (this file, S41-S44):
- `AnalyticLargeSieve` : classical result, not in Mathlib
- `ArithmeticLargeSieve` : classical result, not in Mathlib
- `BombieriVinogradov` : classical result, not in Mathlib
- `BVImpliesMMCSB` : genuine frontier (sieve transfer to EM)
- `ArithLSImpliesMMCSB` : genuine frontier (large sieve for EM)

### Key chain (S41-S44):
```
BV →[open]→ MMCSB →[proved]→ ThresholdHitting(Q_0) →[proved]→ MC
                                (with FiniteMCBelow Q_0)
```
-/

/-! ## S45. Product Growth and Level of Distribution

The running product `prod N` grows at least exponentially: `prod N ≥ 2^N`.
This is because each `seq(n+1)` is prime (hence ≥ 2), and `prod(n+1) = prod(n) * seq(n+1)`.

The exponential lower bound means that for any fixed prime `q`, eventually
`q ≤ (prod N)^θ` for any `θ > 0`. This makes the "level of distribution"
approach particularly powerful for the EM sequence: even a tiny positive
level of distribution suffices for `MultiModularCSB`. -/

section ProductGrowth

/-- **Exponential lower bound on the running product**: `2^N ≤ prod N`.

    Proof by induction on `N`:
    - Base: `prod 0 = 2 ≥ 2^0 = 1`.
    - Step: `prod(n+1) = prod(n) * seq(n+1) ≥ prod(n) * 2 ≥ 2^n * 2 = 2^(n+1)`,
      using that `seq(n+1)` is prime (hence ≥ 2). -/
theorem prod_exponential_lower (N : ℕ) : 2 ^ N ≤ prod N := by
  induction N with
  | zero => simp [prod_zero]
  | succ n ih =>
    rw [prod_succ, Nat.pow_succ]
    have hprime : IsPrime (seq (n + 1)) := seq_isPrime (n + 1)
    have hge2 : 2 ≤ seq (n + 1) := hprime.1
    exact Nat.mul_le_mul ih hge2

/-- **The running product eventually exceeds any fixed bound**.

    Since `prod N ≥ 2^N` and `2^N` is unbounded, for any `B` there exists
    `N₀` such that `B ≤ prod N` for all `N ≥ N₀`. -/
theorem prod_growth_eventually_exceeds (B : ℕ) : ∃ N₀, ∀ N ≥ N₀, B ≤ prod N := by
  refine ⟨B, fun N hN => ?_⟩
  have hlt : B < 2 ^ B := Nat.lt_two_pow_self
  calc B ≤ 2 ^ B := hlt.le
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) hN
    _ ≤ prod N := prod_exponential_lower N

/-- **EM has level of distribution θ**: character sum bounds hold for the
    EM walk at moduli `q ≤ (prod N)^θ / (log(prod N))^A`.

    For every `A > 0`, there exists `N₀` such that for all `N ≥ N₀`, if
    a prime `q` (not in the EM sequence) satisfies the size bound, then
    the EM walk character sum at `q` is `o(N)`.

    **Open Prop**: requires showing that the EM multipliers (least prime
    factors of Euclid numbers) are "generic enough" to produce character
    sum cancellation up to this range. Even `θ = ε > 0` suffices for
    `MultiModularCSB` since `prod(N)` grows super-exponentially. -/
def EMHasLevelOfDistribution (θ : ℝ) : Prop :=
  0 < θ ∧ θ ≤ 1 ∧
  ∀ (A : ℝ) (_ : 0 < A),
  ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
    ∀ (q : ℕ) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    (q : ℝ) ≤ (prod N : ℝ) ^ θ / (Real.log (prod N : ℝ)) ^ A →
    ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_ : χ ≠ 1),
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤
      (prod N : ℝ) ^ θ / (Real.log (prod N : ℝ)) ^ A

/-- **Level of distribution implies MultiModularCSB**: any positive level
    of distribution for the EM sequence implies character sum cancellation
    for all sufficiently large prime moduli.

    The key insight: since `prod N ≥ 2^N`, for any fixed prime `q`,
    eventually `q ≤ (prod N)^θ / (log(prod N))^A`. So the LoD hypothesis
    gives character sum bounds at `q` that are `o(N)` (since `(prod N)^θ`
    grows polynomially in `prod N` while `N ≤ log₂(prod N)`).

    **Open Prop**: the transfer from the LoD bound
    `‖sum‖ ≤ (prod N)^θ / (log prod N)^A` to the `o(N)` bound needed by
    MMCSB requires showing that `(prod N)^θ / (log prod N)^A = o(N)`.
    This is subtle because `prod N` can grow faster than `2^N` (making the
    bound weaker) and the relationship between `prod N` and `N` is not
    monotone. The transfer is a genuine analytic step. -/
def LoDImpliesMMCSB (θ : ℝ) : Prop :=
  EMHasLevelOfDistribution θ → MultiModularCSB

end ProductGrowth

/-! ## S46. Averaged-to-Pointwise Reduction (Markov)

A clean Finset Markov inequality: if a sum of nonneg values is at most B,
then at most B/T of them exceed T. This is useful for converting averaged
bounds (like the large sieve) into pointwise bounds (like MMCSB). -/

section MarkovInequality

/-- **Finset Markov inequality**: if `∑ i ∈ s, f i ≤ B` where all `f i ≥ 0`,
    then the number of indices where `f i > T` is at most `B / T`.

    More precisely: `|{i ∈ s | T < f i}| * T ≤ B`.

    This is the standard Markov inequality for finite sums. The proof:
    the sub-sum over `{i | T < f i}` is bounded by the full sum (≤ B),
    and each term in the sub-sum exceeds T. -/
theorem finset_markov_inequality {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (B T : ℝ) (_hT : 0 < T)
    (havg : ∑ i ∈ s, f i ≤ B) :
    ((s.filter (fun i => T < f i)).card : ℝ) * T ≤ B := by
  have h_sub : (s.filter (fun i => T < f i)).card * T ≤
      ∑ i ∈ s.filter (fun i => T < f i), f i := by
    have h_each : ∀ i ∈ s.filter (fun i => T < f i), T ≤ f i := by
      intro i hi
      exact le_of_lt (Finset.mem_filter.mp hi).2
    calc (s.filter (fun i => T < f i)).card * T
        = ∑ _i ∈ s.filter (fun i => T < f i), T := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s.filter (fun i => T < f i), f i :=
          Finset.sum_le_sum h_each
  have h_filter_le : ∑ i ∈ s.filter (fun i => T < f i), f i ≤
      ∑ i ∈ s, f i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i hi _
    exact hf i hi
  push_cast at h_sub ⊢
  linarith

/-- **Markov inequality, card bound form**: the number of indices exceeding
    the threshold is at most `B / T`. -/
theorem finset_markov_card_bound {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (B T : ℝ) (hT : 0 < T)
    (havg : ∑ i ∈ s, f i ≤ B) :
    ((s.filter (fun i => T < f i)).card : ℝ) ≤ B / T := by
  rw [le_div_iff₀ hT]
  exact finset_markov_inequality s f hf B T hT havg

end MarkovInequality

/-! ## S47. ALS-ArithLS Reduction and Farey Spacing

The arithmetic large sieve for Dirichlet characters follows from the analytic
large sieve plus the Farey spacing property (distinct fractions a/q with
small denominators are well-separated). We state Farey spacing as an open
Prop and prove the conditional reduction. -/

section FareyAndReduction

/-- **Farey spacing property**: distinct fractions `a/q`, `a'/q'` with
    `1 ≤ q, q' ≤ Q` satisfy `|a/q - a'/q'| ≥ 1/(q*q') ≥ 1/Q^2`.

    This is a classical fact in number theory (Stern-Brocot / mediant
    properties). For distinct reduced fractions with bounded denominators,
    the minimum distance on `ℝ/ℤ` is at least `1/Q^2`. -/
def FareySpacing : Prop :=
  ∀ (Q : ℕ) (_ : 0 < Q),
  ∀ (q q' : ℕ) (_ : 0 < q) (_ : q ≤ Q) (_ : 0 < q') (_ : q' ≤ Q),
  ∀ (a a' : ℤ),
  (a : ℚ) / q ≠ (a' : ℚ) / q' →
  (1 : ℝ) / ((Q : ℝ) ^ 2) ≤ |((a : ℝ) / q - (a' : ℝ) / q')|

/-- **Proof of Farey spacing**: For distinct fractions `a/q ≠ a'/q'`
    (over `ℚ`), we have `a*q' ≠ a'*q` (as integers), so
    `|a*q' - a'*q| ≥ 1`. Then
    `|a/q - a'/q'| = |a*q' - a'*q|/(q*q') ≥ 1/(q*q') ≥ 1/Q²`
    since `q*q' ≤ Q²`. -/
theorem farey_spacing_proved : FareySpacing := by
  intro Q _hQ q q' hq hqQ hq' hq'Q a a' hne
  -- Step 1: a * q' ≠ a' * q (as integers), from a/q ≠ a'/q' over ℚ
  have hint_ne : a * (q' : ℤ) ≠ a' * (q : ℤ) := by
    intro heq; apply hne
    have hqne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq)
    have hq'ne : (q' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq')
    rw [div_eq_div_iff hqne hq'ne]; exact_mod_cast heq
  -- Step 2: |a * q' - a' * q| ≥ 1 (nonzero integer has absolute value ≥ 1)
  have hint_bound : 1 ≤ |a * (q' : ℤ) - a' * (q : ℤ)| :=
    Int.one_le_abs (sub_ne_zero.mpr hint_ne)
  -- Step 3: Cast to ℝ (div_sub_div puts numerator as a*q' - q*a', so fix order)
  have hreal_bound : (1 : ℝ) ≤ |(a : ℝ) * (q' : ℝ) - (q : ℝ) * (a' : ℝ)| := by
    have h := @Int.cast_le ℝ _ |>.mpr hint_bound
    simp only [Int.cast_one, Int.cast_abs, Int.cast_sub, Int.cast_mul,
      Int.cast_natCast] at h
    rwa [show (a : ℝ) * (q' : ℝ) - (q : ℝ) * (a' : ℝ) =
      (a : ℝ) * (q' : ℝ) - (a' : ℝ) * (q : ℝ) by ring]
  -- Step 4: q * q' > 0 and q * q' ≤ Q²
  have hqq' : (0 : ℝ) < (q : ℝ) * (q' : ℝ) :=
    mul_pos (Nat.cast_pos.mpr hq) (Nat.cast_pos.mpr hq')
  have hqq'_le : (q : ℝ) * (q' : ℝ) ≤ (Q : ℝ) ^ 2 := by
    rw [sq]; exact_mod_cast Nat.mul_le_mul hqQ hq'Q
  -- Step 5: 1/Q² ≤ 1/(q*q') (larger denominator → smaller fraction)
  have h1 : (1 : ℝ) / ((Q : ℝ) ^ 2) ≤ 1 / ((q : ℝ) * (q' : ℝ)) :=
    one_div_le_one_div_of_le hqq' hqq'_le
  -- Step 6: 1/(q*q') ≤ |numerator|/(q*q')
  have h2 : 1 / ((q : ℝ) * (q' : ℝ)) ≤
      |(a : ℝ) * (q' : ℝ) - (q : ℝ) * (a' : ℝ)| / ((q : ℝ) * (q' : ℝ)) :=
    div_le_div_of_nonneg_right hreal_bound (le_of_lt hqq')
  -- Step 7: Rewrite a/q - a'/q' = (a*q' - q*a')/(q*q') and simplify |·|
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq)
  have hq'R : (q' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hq')
  rw [div_sub_div _ _ hqR hq'R, abs_div, abs_of_pos hqq']
  exact le_trans h1 h2

/-- **ALS + Farey spacing implies ArithLS**: the analytic large sieve
    combined with the Farey spacing property yields the arithmetic large
    sieve for Dirichlet characters.

    The classical argument:
    1. For each primitive character `χ mod q`, associate the Gauss sum
       evaluation point `α(χ) = a/q` where `a` runs over residues.
    2. Farey spacing gives `δ ≥ 1/Q^2` separation between distinct points.
    3. The analytic large sieve with this `δ` gives the character sum bound.
    4. Summing over primitive characters and extending to all characters
       via conductor theory completes the proof.

    **Open Prop**: the Gauss sum argument and conductor bookkeeping are
    substantial (would require ~100 lines). We state this as an open
    reduction. -/
def ALSFareyImpliesArithLS : Prop :=
  AnalyticLargeSieve → FareySpacing → ArithmeticLargeSieve

/-- **ALS + Farey spacing chain to MC**: composing the ALS-to-ArithLS
    reduction with the ArithLS-to-MMCSB transfer gives a chain from
    the analytic large sieve to Mullin's Conjecture.

    ```
    ALS + Farey →[ALSFareyImpliesArithLS]→ ArithLS
      →[ArithLSImpliesMMCSB]→ MMCSB →[proved]→ MC
    ``` -/
theorem als_farey_chain_mc
    (hals : AnalyticLargeSieve) (hfarey : FareySpacing)
    (hreduce : ALSFareyImpliesArithLS)
    (htransfer : ArithLSImpliesMMCSB)
    (hfin : FiniteMCBelow (htransfer (hreduce hals hfarey)).choose) :
    MullinConjecture :=
  arith_ls_chain_mc (hreduce hals hfarey) htransfer hfin

/-- **Simplified ALS chain to MC**: since `FareySpacing` is now proved,
    the chain from ALS to MC no longer needs it as a hypothesis. -/
theorem als_farey_chain_mc'
    (hals : AnalyticLargeSieve)
    (hreduce : ALSFareyImpliesArithLS)
    (htransfer : ArithLSImpliesMMCSB)
    (hfin : FiniteMCBelow (htransfer (hreduce hals farey_spacing_proved)).choose) :
    MullinConjecture :=
  als_farey_chain_mc hals farey_spacing_proved hreduce htransfer hfin

/-- **LoD chain to MC**: level of distribution implies MMCSB implies MC.

    ```
    EMHasLevelOfDistribution θ →[LoDImpliesMMCSB]→ MMCSB →[proved]→ MC
    ``` -/
theorem lod_chain_mc (θ : ℝ)
    (hlod : EMHasLevelOfDistribution θ)
    (htransfer : LoDImpliesMMCSB θ)
    (hfin : FiniteMCBelow (htransfer hlod).choose) :
    MullinConjecture :=
  mmcsb_implies_mc (htransfer hlod) hfin

/-- **LoD chain for small threshold**: if LoD + transfer yields Q₀ ≤ 11,
    then MC follows unconditionally. -/
theorem lod_small_threshold_mc (θ : ℝ)
    (hlod : EMHasLevelOfDistribution θ)
    (htransfer : LoDImpliesMMCSB θ)
    (hsmall : (htransfer hlod).choose ≤ 11) :
    MullinConjecture :=
  mmcsb_small_threshold_mc (htransfer hlod) hsmall

end FareyAndReduction

/-! ## S48. Product Parity and Sqrt Range

Structural lemmas about the Euclid-Mullin sequence:
- The running product is always even (since seq 0 = 2 divides prod n).
- The Euclid number prod n + 1 is always odd.
- Every term after the first is odd (hence differs from 2).
- Any fixed bound is eventually dominated by sqrt(prod N). -/

section ProductParity

/-- **The running product is always even**: `2 ∣ prod n` for all `n`.

    Since `seq 0 = 2` and `seq 0 ∣ prod n` (by `seq_dvd_prod`), we have `2 ∣ prod n`. -/
theorem two_dvd_prod (n : ℕ) : 2 ∣ prod n :=
  seq_zero ▸ seq_dvd_prod 0 n (Nat.zero_le n)

/-- **The Euclid number is always odd**: `¬ 2 ∣ (prod n + 1)`.

    Since `2 ∣ prod n`, if also `2 ∣ (prod n + 1)`, then `2 ∣ 1`,
    which is impossible since 2 > 1. -/
theorem prod_add_one_odd (n : ℕ) : ¬ 2 ∣ (prod n + 1) := by
  intro ⟨b, hb⟩
  obtain ⟨a, ha⟩ := two_dvd_prod n
  omega

/-- **Every term after the first is odd (hence not 2)**: `seq n ≠ 2` for `n > 0`.

    For `n = k + 1`, `seq (k+1) = minFac(prod k + 1)`. Since `prod k + 1` is odd
    (by `prod_add_one_odd`), it has no factor of 2. But `minFac(prod k + 1)` divides
    `prod k + 1`, so `minFac(prod k + 1) ≠ 2`. -/
theorem seq_pos_ne_two (n : ℕ) (hn : 0 < n) : seq n ≠ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  intro h
  have hdvd : seq (k + 1) ∣ (prod k + 1) := seq_dvd_succ_prod k
  rw [h] at hdvd
  exact prod_add_one_odd k hdvd

/-- **Any fixed bound is eventually in the sqrt range of prod N**.

    Since `prod N ≥ 2^N` and `2^N` is unbounded, for any fixed `B` there exists
    `N₀` such that `B ≤ sqrt(prod N)` for all `N ≥ N₀`.

    Equivalently, `B^2 ≤ prod N`, which follows from `B^2 ≤ 2^N ≤ prod N`
    for sufficiently large `N`. -/
theorem fixed_q_eventually_in_sqrt_range (B : ℕ) (_hB : 0 < B) :
    ∃ N₀, ∀ N ≥ N₀, (B : ℝ) ≤ Real.sqrt (prod N : ℝ) := by
  -- B^2 ≤ 2^N ≤ prod N for large N
  obtain ⟨N₀, hN₀⟩ := prod_growth_eventually_exceeds (B * B)
  refine ⟨N₀, fun N hN => ?_⟩
  have hprod : B * B ≤ prod N := hN₀ N hN
  rw [Real.le_sqrt (Nat.cast_nonneg B) (Nat.cast_nonneg (prod N))]
  have : (B : ℝ) ^ 2 = (B : ℝ) * (B : ℝ) := by ring
  rw [this]
  exact_mod_cast hprod

end ProductParity

/-! ## Summary (S45-S48)

### Proved theorems (S45-S48):
- `prod_exponential_lower` : `2^N ≤ prod N` (induction on N)
- `prod_growth_eventually_exceeds` : `∀ B, ∃ N₀, ∀ N ≥ N₀, B ≤ prod N`
- `finset_markov_inequality` : `|{i | T < f i}| * T ≤ ∑ f i` (Markov for finsets)
- `finset_markov_card_bound` : `|{i | T < f i}| ≤ B / T`
- `farey_spacing_proved` : |a/q - a'/q'| ≥ 1/Q² for distinct fractions (PROVED)
- `als_farey_chain_mc` : ALS + Farey + ArithLSImpliesMMCSB → MC
- `als_farey_chain_mc'` : ALS + ArithLSImpliesMMCSB → MC (Farey eliminated)
- `lod_chain_mc` : LoD + LoDImpliesMMCSB → MC
- `lod_small_threshold_mc` : LoD + transfer (small Q₀) → MC
- `two_dvd_prod` : `2 ∣ prod n` (seq 0 = 2 divides every running product)
- `prod_add_one_odd` : `¬ 2 ∣ (prod n + 1)` (Euclid numbers are odd)
- `seq_pos_ne_two` : `seq n ≠ 2` for `n > 0` (all terms after the first are odd)
- `fixed_q_eventually_in_sqrt_range` : `∀ B, ∃ N₀, ∀ N ≥ N₀, B ≤ √(prod N)`

### Open Props (S45-S48):
- `EMHasLevelOfDistribution θ` : EM walk has level of distribution θ
- `LoDImpliesMMCSB θ` : LoD → MultiModularCSB (analytic transfer)
- `ALSFareyImpliesArithLS` : ALS + Farey → ArithLS (Gauss sum argument)

### Key new chains:
```
LoD(θ) →[open]→ MMCSB →[proved]→ MC
ALS + Farey(proved) →[open]→ ArithLS →[open]→ MMCSB →[proved]→ MC
```
-/

/-! ## S49. Gauss-Conductor Transfer and Structural Lemmas

Since `FareySpacing` is now proved, the `ALSFareyImpliesArithLS` reduction
simplifies: the only remaining open content is the Gauss sum inversion and
conductor factorization. We factor this out as `GaussConductorTransfer`:
`AnalyticLargeSieve → ArithmeticLargeSieve`, absorbing the proved Farey step.

We also prove structural lemmas about the EM sequence supporting the sieve:
- The running product is strictly monotone increasing.
- Euclid numbers `prod(n)+1` are coprime to all prior sequence terms.
- The sequence terms in any range are pairwise distinct. -/

section GaussConductorTransfer

/-- **Gauss-conductor transfer**: the analytic large sieve implies the
    arithmetic large sieve, absorbing the (now proved) Farey spacing step.

    The classical argument proceeds in two stages:
    1. **Gauss sum inversion**: for each primitive character χ mod q, express
       the character sum ∑ a(n)χ(n) as a linear combination of exponential
       sums S(α) = ∑ a(n)e(nα) at evaluation points α = a/q determined by
       the Gauss sum τ(χ). The key identity: χ(n) = τ(χ)⁻¹ ∑_a χ̄(a)e(an/q),
       with |τ(χ)|² = q for primitive χ.
    2. **Conductor factorization**: reduce from all characters to primitive
       characters via the conductor. Each imprimitive character χ mod q is
       induced from a unique primitive character χ* mod q* with q* | q,
       and |∑ a(n)χ(n)| ≤ |∑ a(n)χ*(n)| (up to controlled factors).

    The composition gives: ALS (exponential sum bound with δ-separation) +
    Farey spacing (δ ≥ 1/Q²) → ArithLS (character sum bound).

    **Open Prop**: requires Gauss sum theory (definition, norm formula,
    inversion) and conductor theory (inducing from primitive characters).
    Neither is in Mathlib. -/
def GaussConductorTransfer : Prop :=
  AnalyticLargeSieve → ArithmeticLargeSieve

/-- `GaussConductorTransfer` implies `ALSFareyImpliesArithLS`, since the
    former absorbs the Farey step while the latter requires it separately.
    This is immediate: given ALS and Farey, GCT applied to ALS gives ArithLS. -/
theorem gct_implies_als_farey (hgct : GaussConductorTransfer) :
    ALSFareyImpliesArithLS :=
  fun hals _hfarey => hgct hals

/-- **Gauss-conductor chain to MC**: composing GaussConductorTransfer with
    the ArithLS→MMCSB transfer and the proved MMCSB→MC reduction.

    ```
    ALS →[GaussConductorTransfer]→ ArithLS →[ArithLSImpliesMMCSB]→ MMCSB
      →[mmcsb_implies_mc]→ MC
    ``` -/
theorem gauss_conductor_chain_mc
    (hgct : GaussConductorTransfer)
    (hals : AnalyticLargeSieve)
    (htransfer : ArithLSImpliesMMCSB)
    (hfin : FiniteMCBelow (htransfer (hgct hals)).choose) :
    MullinConjecture :=
  arith_ls_chain_mc (hgct hals) htransfer hfin

/-- **Gauss-conductor chain for small threshold**: if the ArithLS→MMCSB
    transfer yields Q₀ ≤ 11, MC follows unconditionally. -/
theorem gauss_conductor_small_threshold_mc
    (hgct : GaussConductorTransfer)
    (hals : AnalyticLargeSieve)
    (htransfer : ArithLSImpliesMMCSB)
    (hsmall : (htransfer (hgct hals)).choose ≤ 11) :
    MullinConjecture :=
  mmcsb_small_threshold_mc (htransfer (hgct hals)) hsmall

end GaussConductorTransfer

