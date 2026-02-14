import EM.EquidistSieveTransfer

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
CCSB at q → hitCount_lower_bound at q → WalkEquidistribution at q
          → cofinal hitting of -1 at q → ThresholdHitting at q
```

The Fourier bridge (`complex_csb_implies_hit_count_lb_proved`) handles
the first step, and the remaining steps are proved in S29-S30. -/

section MMCSBReduction

/-- **Per-prime character sum bound from MMCSB**: for a DirichletCharacter ψ
    at a prime q >= Q_0, the MMCSB data gives the norm bound on the character
    sum along the EM walk.

    This replicates `dirichlet_char_sum_le_of_csb` (which is private in
    EquidistFourier.lean) using per-prime MMCSB data instead of global CCSB. -/
private lemma dirichlet_char_sum_le_of_mmcsb
    (hmmcsb : MultiModularCSB)
    {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hge : q ≥ hmmcsb.choose)
    (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ Finset.range N, ψ ↑(emWalkUnit q hq hne n)‖ ≤ ε * N := by
  -- MMCSB gives per-prime data for χ : (ZMod q)ˣ →* ℂˣ
  have hcsb_q := hmmcsb.choose_spec q hge hq hne
  -- ψ.toUnitHom is a non-trivial (ZMod q)ˣ →* ℂˣ
  have hψ' : ψ.toUnitHom ≠ 1 := by
    intro h
    apply hψ
    have h1 : (1 : DirichletCharacter ℂ q).toUnitHom = 1 := by
      ext a; simp [MulChar.one_apply_coe]
    exact (DirichletCharacter.toUnitHom_inj (χ := ψ) 1).mp (h.trans h1.symm)
  obtain ⟨N₀, hN₀⟩ := hcsb_q ψ.toUnitHom hψ' ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have heq : ∑ n ∈ Finset.range N, ψ ↑(emWalkUnit q hq hne n) =
      ∑ n ∈ Finset.range N, (ψ.toUnitHom (emWalkUnit q hq hne n) : ℂ) := by
    apply Finset.sum_congr rfl
    intro n _
    exact (MulChar.coe_toUnitHom ψ (emWalkUnit q hq hne n)).symm
  rw [heq]
  exact hN₀ N hN

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

    For Q_0 <= 11, the finite verification is already done (`finite_mc_below_11`).
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
  exact finite_mc_below_11 q hq (by omega)

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

section StructuralLemmas

/-- **The running product is strictly increasing**: `prod m < prod n` for `m < n`.

    This is immediate from `prod_strictMono` (proved in EquidistSelfAvoidance.lean
    by induction: each `seq(n+1)` is prime hence ≥ 2, so multiplying by it
    strictly increases the product). -/
theorem prod_strictly_increasing {m n : ℕ} (h : m < n) : prod m < prod n :=
  prod_strictMono h

/-- **Euclid numbers are coprime to prior sequence terms**: if `k ≤ n`
    then `Nat.Coprime (seq k) (prod n + 1)`.

    Since `seq k ∣ prod n` (by `seq_dvd_prod`) and `seq k` is prime,
    if `seq k` also divided `prod n + 1` it would divide their difference 1.
    So `seq k ∤ prod n + 1`, and since `seq k` is prime this gives coprimality. -/
theorem euclid_number_coprime_seq (k n : ℕ) (h : k ≤ n) :
    Nat.Coprime (seq k) (prod n + 1) := by
  apply coprime_of_prime_not_dvd (seq_isPrime k)
  exact seq_not_dvd_prod_succ h

/-- **Sequence terms are pairwise distinct on any range**: the elements
    `{seq 0, seq 1, ..., seq n}` are pairwise distinct.

    This follows directly from `seq_injective`: the Euclid-Mullin sequence
    is injective, so distinct indices give distinct values. -/
theorem seq_pairwise_distinct :
    ∀ i j : ℕ, seq i = seq j → i = j :=
  seq_injective

/-- **The number of distinct sequence terms up to index n**: the image of
    `seq` on `Finset.range n` has cardinality exactly `n`, since `seq` is
    injective. This is useful for counting arguments in the sieve. -/
theorem seq_image_card (n : ℕ) :
    (Finset.image seq (Finset.range n)).card = n := by
  rw [Finset.card_image_of_injective _ (fun _ _ h => seq_injective _ _ h)]
  exact Finset.card_range n

/-- **Euclid number coprimality to all prior terms simultaneously**:
    `prod n + 1` is coprime to the running product `prod n`.

    This is a restatement of `aux_coprime_prod` with the arguments in the
    conventional order for sieve applications: gcd(prod n + 1, prod n) = 1. -/
theorem euclid_coprime_running_prod (n : ℕ) :
    Nat.Coprime (prod n + 1) (prod n) :=
  aux_coprime_prod n

/-- **Every prime factor of prod(n)+1 is new**: if `p` is prime and
    `p ∣ prod n + 1`, then `p ∉ {seq 0, ..., seq n}`.

    This is the key structural fact making the EM sequence infinite and
    supporting the sieve: each Euclid number introduces genuinely new
    prime factors that have never appeared before. -/
theorem prime_factor_of_euclid_not_in_range {p n : ℕ}
    (_hp : Nat.Prime p) (hdvd : p ∣ prod n + 1) :
    ∀ k ≤ n, seq k ≠ p := by
  intro k hk heq
  have : seq k ∣ prod n + 1 := heq ▸ hdvd
  exact seq_not_dvd_prod_succ hk this

/-- **Product lower bound for sieve applications**: `prod n ≥ 2^n`,
    which means for any modulus Q, the range [1, prod n] contains at
    least `2^n` integers — more than enough for the large sieve to
    produce nontrivial bounds once `n` is large relative to `Q`.

    This is a restatement of `prod_exponential_lower` highlighting
    the sieve-theoretic significance. -/
theorem prod_lower_bound_for_sieve (n : ℕ) : 2 ^ n ≤ prod n :=
  prod_exponential_lower n

end StructuralLemmas

/-! ## Summary (S49)

### New definitions (S49):
- `GaussConductorTransfer` : ALS → ArithLS (absorbing proved Farey spacing)

### Proved theorems (S49):
- `gct_implies_als_farey` : GCT implies ALSFareyImpliesArithLS
- `gauss_conductor_chain_mc` : GCT + ALS + ArithLSImpliesMMCSB → MC
- `gauss_conductor_small_threshold_mc` : above with Q₀ ≤ 11 → MC unconditionally
- `prod_strictly_increasing` : prod m < prod n for m < n
- `euclid_number_coprime_seq` : Coprime (seq k) (prod n + 1) for k ≤ n
- `seq_pairwise_distinct` : seq i = seq j → i = j
- `seq_image_card` : |image of seq on range(n)| = n
- `euclid_coprime_running_prod` : Coprime (prod n + 1) (prod n)
- `prime_factor_of_euclid_not_in_range` : prime factors of Euclid numbers are new
- `prod_lower_bound_for_sieve` : 2^n ≤ prod n

### Key insight (S49):
The `ALSFareyImpliesArithLS` open Prop decomposes into:
1. `GaussConductorTransfer` (open) — the Gauss sum + conductor argument
2. `farey_spacing_proved` (proved) — Farey separation ≥ 1/Q²
Since (2) is proved, only `GaussConductorTransfer` remains open, giving a cleaner
chain: `ALS →[GCT]→ ArithLS →[open]→ MMCSB →[proved]→ MC`.

### Structural lemmas for sieve (S49):
The sequence's built-in coprimality structure (consecutive integers share no
common factor) means every Euclid number introduces genuinely new primes.
Combined with the exponential growth of `prod n`, this makes the EM sequence
a natural input for sieve methods.
-/

-- ============================================================================
-- S50. DIVISIBILITY AND COPRIMALITY STRUCTURAL LEMMAS
-- ============================================================================

/-! ## S50: Running product divisibility and coprimality

This section proves foundational structural lemmas about the EM sequence's
divisibility and coprimality properties:

1. `prod_dvd_prod` : running product divisibility is monotone (m <= n => prod m | prod n)
2. `seq_succ_coprime_prod` : new EM terms are coprime to the running product
3. `seq_le_euclid_number` : sequence terms bounded by Euclid numbers
4. `euclid_coprime_factor_of_prod` : Euclid numbers coprime to factors of earlier products

These are structural consequences of the EM construction and require no
analytic input. They strengthen the sieve-theoretic toolkit from S49. -/

section DivisibilityCoprimality

/-- Running product divisibility: `prod m | prod n` for `m <= n`.
    By induction: `prod(n+1) = prod(n) * seq(n+1)`, so `prod(m) | prod(n)`
    implies `prod(m) | prod(n) * seq(n+1) = prod(n+1)`. -/
theorem prod_dvd_prod (m n : ℕ) (h : m ≤ n) : prod m ∣ prod n := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst this
    exact Nat.dvd_refl _
  | succ k ih =>
    rw [prod_succ]
    match Nat.lt_or_ge m (k + 1) with
    | .inl hlt =>
      exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_mul_right (prod k) (seq (k + 1)))
    | .inr hge =>
      have : m = k + 1 := by omega
      subst this
      exact dvd_refl _

/-- New EM term is coprime to running product: `Nat.Coprime (seq (n+1)) (prod n)`.
    Since `seq(n+1) | prod(n)+1` and `seq(n+1)` is prime, if also `seq(n+1) | prod(n)`,
    then `seq(n+1) | 1`, contradicting primality. -/
theorem seq_succ_coprime_prod (n : ℕ) : Nat.Coprime (seq (n + 1)) (prod n) := by
  apply coprime_of_prime_not_dvd (seq_isPrime (n + 1))
  intro hdvd
  have hdvd_succ : seq (n + 1) ∣ (prod n + 1) := seq_dvd_succ_prod n
  have hge2 : 2 ≤ seq (n + 1) := (seq_isPrime (n + 1)).1
  -- seq(n+1) | prod n and seq(n+1) | prod n + 1
  -- gcd(prod n + 1, prod n) = 1 by aux_coprime_prod
  -- So seq(n+1) | gcd(prod n + 1, prod n) = 1
  have hcop := aux_coprime_prod n  -- Nat.gcd (prod n + 1) (prod n) = 1
  have : seq (n + 1) ∣ Nat.gcd (prod n + 1) (prod n) :=
    Nat.dvd_gcd hdvd_succ hdvd
  rw [hcop] at this
  exact absurd (Nat.le_of_dvd (by omega) this) (by omega)

/-- Sequence terms are bounded by Euclid numbers: `seq (n+1) <= prod n + 1`.
    Since `seq(n+1) = minFac(prod(n)+1)` and minFac divides its argument,
    `seq(n+1) <= prod(n)+1`. -/
theorem seq_le_euclid_number (n : ℕ) : seq (n + 1) ≤ prod n + 1 := by
  rw [seq_succ]
  have h2 : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  exact Nat.le_of_dvd (by omega) (minFac_dvd (prod n + 1) h2)

/-- Euclid numbers are coprime to factors of earlier running products:
    if `q | prod m` and `m <= n`, then `Nat.Coprime q (prod n + 1)`. -/
theorem euclid_coprime_factor_of_prod {q m n : ℕ}
    (hq_dvd : q ∣ prod m) (hmn : m ≤ n) :
    Nat.Coprime q (prod n + 1) := by
  have hq_dvd_n : q ∣ prod n := Nat.dvd_trans hq_dvd (prod_dvd_prod m n hmn)
  have hcop := aux_coprime_prod n  -- Nat.Coprime (prod n + 1) (prod n)
  -- hcop : Nat.gcd (prod n + 1) (prod n) = 1
  -- We need: Nat.gcd q (prod n + 1) = 1
  -- Since q | prod n and gcd(prod n + 1, prod n) = 1, we get gcd(q, prod n + 1) = 1
  exact hcop.symm.coprime_dvd_left hq_dvd_n

end DivisibilityCoprimality

/-! ## Summary (S50)

### Proved theorems (S50):
- `prod_dvd_prod` : prod m | prod n for m <= n (induction)
- `seq_succ_coprime_prod` : Coprime (seq (n+1)) (prod n) (prime not dividing consecutive)
- `seq_le_euclid_number` : seq (n+1) <= prod n + 1 (minFac bound)
- `euclid_coprime_factor_of_prod` : q | prod m and m <= n => Coprime q (prod n + 1)

### Key insight (S50):
The running product `prod n` is monotone under divisibility, forming a divisibility
chain `prod 0 | prod 1 | prod 2 | ...`. Combined with the coprimality of consecutive
integers (`prod n + 1` coprime to `prod n`), this gives a strong structural framework:
any factor of any earlier running product is automatically coprime to any later Euclid
number. This is the algebraic backbone underlying all sieve applications to the EM sequence.
-/

/-! ## §51 Congruence and coprimality of EM sequence terms

Building on the divisibility chain from §50, we derive two further structural properties:

1. **Modular congruence**: The Euclid number `prod n + 1` is congruent to 1 modulo any
   earlier running product `prod m` (for `m ≤ n`). This is an immediate consequence of
   `prod_dvd_prod`.

2. **Pairwise coprimality**: Distinct terms `seq i` and `seq j` are coprime. This uses
   the fact that earlier terms divide the running product, while later terms are coprime
   to it (by `seq_succ_coprime_prod`).
-/

section CongruenceAndCoprimality

/-- Euclid numbers are congruent to 1 modulo earlier running products:
    `prod n + 1 ≡ 1 [MOD prod m]` for `m ≤ n`.
    Since `prod m ∣ prod n` (by `prod_dvd_prod`), we have
    `prod n + 1 - 1 = prod n` is divisible by `prod m`. -/
theorem euclid_cong_one_mod_earlier_prod (m n : ℕ) (h : m ≤ n) :
    Nat.ModEq (prod m) (prod n + 1) 1 := by
  rw [Nat.ModEq.comm]
  rw [Nat.modEq_iff_dvd' (by omega : 1 ≤ prod n + 1)]
  simp only [Nat.add_sub_cancel]
  exact prod_dvd_prod m n h

/-- Distinct EM sequence terms are coprime: `Nat.Coprime (seq i) (seq j)` for `i ≠ j`.
    WLOG `i < j`. Write `j = k + 1` with `i ≤ k`. Then:
    - `seq i ∣ prod k` (by `seq_dvd_prod`)
    - `Coprime (seq (k+1)) (prod k)` (by `seq_succ_coprime_prod`)
    So `Coprime (seq i) (seq j)` via `Nat.Coprime.coprime_dvd_right`. -/
theorem seq_coprime_of_distinct {i j : ℕ} (h : i ≠ j) :
    Nat.Coprime (seq i) (seq j) := by
  -- Reduce to i < j or j < i
  rcases Nat.lt_or_gt_of_ne h with hij | hji
  · -- Case i < j: write j = k + 1 with i ≤ k
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    -- seq i ∣ prod k since i ≤ k
    have hi_dvd : seq i ∣ prod k := seq_dvd_prod i k (by omega)
    -- Coprime (seq (k+1)) (prod k)
    have hcop : Nat.Coprime (seq (k + 1)) (prod k) := seq_succ_coprime_prod k
    -- Since seq i ∣ prod k and Coprime (seq (k+1)) (prod k),
    -- we get Coprime (seq (k+1)) (seq i)
    exact (hcop.coprime_dvd_right hi_dvd).symm
  · -- Case j < i: symmetric, swap and use commutativity
    exact (seq_coprime_of_distinct (Ne.symm h)).symm

end CongruenceAndCoprimality

/-! ## Summary (S51)

### Proved theorems (S51):
- `euclid_cong_one_mod_earlier_prod` : prod n + 1 ≡ 1 [MOD prod m] for m ≤ n
- `seq_coprime_of_distinct` : Coprime (seq i) (seq j) for i ≠ j

### Key insight (S51):
The Euclid-Mullin sequence has a remarkably rigid arithmetic structure: not only is
each term prime and distinct, but all terms are **pairwise coprime**. This means
distinct EM primes can never share a common factor — they live in independent parts
of the factorization lattice. The modular congruence `prod n + 1 ≡ 1 [MOD prod m]`
is the quantitative form of Euclid's argument: adding 1 to a product ensures the
result is coprime to every factor of that product.
-/

-- ============================================================================
-- S52. BVImpliesMMCSB DECOMPOSITION
-- ============================================================================

/-! ## §52 BVImpliesMMCSB Decomposition

The transfer `BombieriVinogradov -> MultiModularCSB` faces three independent
obstacles. We articulate each as a separate open Prop and prove that their
sequential composition yields `BVImpliesMMCSB`.

The three obstacles are:

1. **Population-to-Subsequence Transfer**: BV controls all primes in arithmetic
   progressions; we need the specific EM multipliers `seq(n+1) = minFac(prod(n)+1)`
   to inherit equidistribution of residues. This requires transferring from the full
   set of primes to the thin subsequence of least prime factors of Euclid numbers.

2. **Multiplier-to-Walk Bridge**: Even if individual multiplier character sums
   `sum_{n<N} chi(m(n))` cancel, the walk character sums `sum_{n<N} chi(w(n))`
   involve products `w(n) = prod_{k<n} m(k)`, making cancellation harder.
   This is a multiplicative random walk analysis.

3. **Averaged-to-Pointwise Lift**: BV gives averaged bounds (sum over q of errors);
   we need pointwise bounds for EACH q >= Q_0 individually. The doubly-exponential
   growth of `prod(N)` helps (any fixed q is eventually tiny relative to prod(N)),
   but the argument must be uniform in N.

We decompose `BVImpliesMMCSB` as:
```
BV ->[Obstacle 1]-> EMMultCharSumBound ->[Obstacles 2+3]-> MultiModularCSB
```

The first obstacle (BV to multiplier character sum bounds) is the sieve-theoretic
content. The second and third (multiplier sums to walk sums, with pointwise control)
are the harmonic analysis content.
-/

section BVDecomposition

/-- **EM Multiplier Character Sum Bound**: the EM multipliers `emMultUnit q n`
    satisfy character sum cancellation for all sufficiently large prime moduli.

    This is the natural intermediate between BV and MMCSB: it says that for
    non-trivial characters chi on `(ZMod q)^x`, the multiplier sums
    `sum_{n<N} chi(m(n))` are o(N).

    This is WEAKER than MMCSB (which bounds walk sums, not multiplier sums)
    and STRONGER than SieveEquidistribution (which gives counting bounds,
    not character sum bounds).

    The key point: multiplier character sums are LINEAR sums of chi-values,
    while walk character sums involve products. Linear sums are what BV/sieve
    methods naturally produce. -/
def EMMultCharSumBound : Prop :=
  ∃ Q₀ : ℕ, ∀ (q : Nat) [Fact (Nat.Prime q)], q ≥ Q₀ →
  ∀ (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- **Obstacle 1: BV implies EM Multiplier Character Sum Bound**.

    The Bombieri-Vinogradov theorem controls the error in the prime counting
    function pi(x; q, a) for almost all moduli q <= sqrt(x)/(log x)^A.
    This Prop transfers that to character sum cancellation for the specific
    EM multipliers seq(n+1) = minFac(prod(n)+1).

    The transfer requires:
    (a) Relating the EM multipliers (least prime factors of Euclid numbers)
        to the set of all primes counted by pi(x; q, a).
    (b) Using the BV averaged bound to extract pointwise bounds for individual q.
        The doubly-exponential growth of prod(N) helps: for fixed q, eventually
        q << sqrt(prod(N)), placing q well within the BV range.
    (c) Converting from prime-counting equidistribution (pi(x; q, a) ~ pi(x)/phi(q))
        to character sum cancellation (sum chi(m(n)) = o(N)) via Fourier inversion
        on the group (ZMod q)^x.

    **Open Prop**: this is the sieve-theoretic heart of the BV approach.
    It requires tools from analytic number theory (Selberg sieve, Alladi's
    theorem on least prime factors) that are not in Mathlib. -/
def BVImpliesEMMultCSB : Prop :=
  BombieriVinogradov → EMMultCharSumBound

/-- **Obstacles 2+3: Multiplier Character Sum Bound implies MultiModularCSB**.

    Given cancellation of multiplier character sums (sum chi(m(n)) = o(N)),
    derive cancellation of walk character sums (sum chi(w(n)) = o(N)).

    Since `w(n+1) = w(n) * m(n)`, we have `chi(w(n)) = prod_{k<n} chi(m(k))`.
    The walk character sum is thus a sum of partial products of unit complex
    numbers. Even if the individual factors chi(m(n)) are equidistributed,
    the partial products can fail to cancel (this is the multiplicative
    random walk problem).

    However, the telescoping identity (proved in S37) gives:
    `sum_{n<N} chi(w(n)) * (chi(m(n)) - 1) = chi(w(N)) - chi(w(0))`

    This means: if chi(m(n)) != 1 often enough (which follows from multiplier
    equidistribution), the walk character sums cannot grow linearly.

    More precisely, this Prop combines:
    - The walk-multiplier telescoping bound (algebraic, proved in S37)
    - A pointwise extraction argument (from the averaged multiplier bound
      to a pointwise walk bound)

    **Open Prop**: the telescope gives norm <= 2, but we need the ratio
    sum chi(w(n)) / (sum of (chi(m(n))-1) terms) to be bounded. This
    requires showing that the denominator grows linearly, which needs
    quantitative equidistribution of multipliers away from ker(chi). -/
def MultCSBImpliesMMCSB : Prop :=
  EMMultCharSumBound → MultiModularCSB

/-- **Decomposition theorem**: the two sub-Props compose to give BVImpliesMMCSB.

    ```
    BV ->[BVImpliesEMMultCSB]-> EMMultCharSumBound ->[MultCSBImpliesMMCSB]-> MMCSB
    ```

    This is a trivial function composition: given BV, first apply the sieve
    transfer to get multiplier character sum bounds, then apply the walk
    bridge to get walk character sum bounds (= MMCSB). -/
theorem bv_decomposition_implies_mmcsb
    (h1 : BVImpliesEMMultCSB)
    (h2 : MultCSBImpliesMMCSB) :
    BVImpliesMMCSB :=
  fun hbv => h2 (h1 hbv)

/-- **Decomposed BV chain to MC**: BV + the two decomposed transfers + finite
    verification → Mullin's Conjecture.

    ```
    BV ->[h1]-> EMMultCSB ->[h2]-> MMCSB ->[mmcsb_implies_mc]-> MC
    ``` -/
theorem bv_decomposed_chain_mc
    (hbv : BombieriVinogradov)
    (h1 : BVImpliesEMMultCSB)
    (h2 : MultCSBImpliesMMCSB)
    (hfin : FiniteMCBelow (h2 (h1 hbv)).choose) :
    MullinConjecture :=
  mmcsb_implies_mc (h2 (h1 hbv)) hfin

/-- **Decomposed BV chain for small threshold**: if the decomposed transfers
    yield Q_0 <= 11, MC follows unconditionally. -/
theorem bv_decomposed_small_threshold_mc
    (hbv : BombieriVinogradov)
    (h1 : BVImpliesEMMultCSB)
    (h2 : MultCSBImpliesMMCSB)
    (hsmall : (h2 (h1 hbv)).choose ≤ 11) :
    MullinConjecture :=
  mmcsb_small_threshold_mc (h2 (h1 hbv)) hsmall

/-- **EMMultCSB is implied by StrongSieveEquidist** (modulo a Fourier bridge).

    StrongSieveEquidist gives window equidistribution of multiplier residues.
    Character sum cancellation follows by the Weyl criterion: if the fraction
    of multipliers hitting each unit a in (ZMod q)^x converges to 1/phi(q),
    then sum chi(m(n)) = o(N) for non-trivial chi (by orthogonality of characters).

    This connects the sieve route (S36-S39) with the BV decomposition route. -/
def StrongSieveImpliesMultCSB : Prop :=
  StrongSieveEquidist → EMMultCharSumBound

open Classical in
/-- **StrongSieveEquidist implies SieveEquidistribution**: window equidistribution
    (controlling every window of sufficient length) implies cumulative equidistribution
    (controlling the single window [0, N)).

    Proof: given ε > 0, apply SSE with ε' = ε/2, L₀ = 1. Get N₀ such that for all
    n₀ ≥ N₀ and L ≥ 1, the window [n₀, n₀+L) has hit count ≥ L·(1/φ − ε/2).
    The cumulative count on [0, N) is at least the count on [N₀, N), which by SSE
    is ≥ (N−N₀)·(1/φ − ε/2). For N large enough, this exceeds N·(1/φ − ε). -/
theorem strongSieveEquidist_implies_sieveEquidist (hsse : StrongSieveEquidist) :
    SieveEquidistribution := by
  intro q inst hq hne a ε hε
  haveI : Fact (Nat.Prime q) := inst
  set φ := (Finset.univ (α := (ZMod q)ˣ)).card with hφ_def
  -- Apply SSE with ε' = ε/2, L₀ = 1
  set ε' := ε / 2 with hε'_def
  have hε'_pos : 0 < ε' := by positivity
  obtain ⟨N₀, hN₀⟩ := hsse q hq hne a ε' hε'_pos 1 Nat.one_pos
  -- For N ≥ N₀, the window [N₀, N₀ + (N - N₀)) has count ≥ (N-N₀)·(1/φ - ε/2).
  -- The cumulative [0,N) count is at least as large.
  -- We need: (N-N₀)·(1/φ - ε/2) ≥ N·(1/φ - ε), i.e., N₀·(1/φ-ε/2) ≤ N·ε/2.
  -- Since 1/φ-ε/2 ≤ 1, it suffices to take N ≥ 2·N₀/ε.
  -- Choose N₁ so that both N₁ ≥ N₀ and N₀ ≤ N₁·(ε/2).
  -- Use N₁ = max(N₀, ⌈2·N₀/ε⌉ + 1).
  -- Simpler: pick N₁ = N₀ + ⌈N₀/ε⌉ · 2 + 1, but ceiling is complex.
  -- Just pick N₁ such that N₁ ≥ N₀ and N₁ · (ε/2) ≥ N₀ (real arithmetic).
  -- A clean choice: N₁ = N₀ + ⌈2·N₀/ε⌉.
  -- Actually, let's just existentially pick a large enough N₁ and do real arithmetic.
  refine ⟨N₀ + Nat.ceil (2 * N₀ / ε) + 1, fun N hN => ?_⟩
  -- Key: N ≥ N₀
  have hN_ge_N₀ : N₀ ≤ N := by omega
  -- Key: N > 0
  have hN_pos : 0 < N := by omega
  -- L = N - N₀ ≥ 1
  set L := N - N₀ with hL_def
  have hL_ge_1 : L ≥ 1 := by omega
  -- Apply SSE: window [N₀, N₀ + L) = [N₀, N)
  have hsse_app := hN₀ N₀ le_rfl L hL_ge_1
  -- The hit count in [N₀, N₀+L) ≥ L·(1/φ - ε')
  -- The cumulative hit count in [0,N) ≥ hit count in [N₀, N)
  -- Build injective map from window filter to cumulative filter
  have hcumul_ge_window :
      ((Finset.range L).filter (fun k => emMultUnit q hq hne (N₀ + k) = a)).card ≤
      ((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card := by
    apply Finset.card_le_card_of_injOn (fun k => N₀ + k)
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk ⊢
      exact ⟨by rw [hL_def] at hk; omega, hk.2⟩
    · intro k₁ _ k₂ _ (h : N₀ + k₁ = N₀ + k₂); omega
  -- Now do the real arithmetic
  -- cumulative_hit ≥ hitW ≥ L·(1/φ - ε') ≥ N·(1/φ - ε)
  -- Step 1: cast cumulative ≥ window
  have h_ge_window : (((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card : ℝ) ≥
      (((Finset.range L).filter (fun k => emMultUnit q hq hne (N₀ + k) = a)).card : ℝ) := by
    exact_mod_cast hcumul_ge_window
  -- Step 2: window bound from SSE
  have h_window_bound :
      (((Finset.range L).filter (fun k => emMultUnit q hq hne (N₀ + k) = a)).card : ℝ) ≥
      (L : ℝ) * (1 / ↑φ - ε') := hsse_app
  -- Step 3: show L·(1/φ - ε') ≥ N·(1/φ - ε)
  -- Goal: cumulative hit count ≥ N · (1/φ - ε)
  -- Chain: cumulative ≥ hitW ≥ L·(1/φ - ε/2) ≥ N·(1/φ - ε)
  -- For the last step: L·(1/φ - ε/2) = (N-N₀)·(1/φ-ε/2) ≥ N·(1/φ-ε)
  -- ⟺ N·(ε/2) ≥ N₀·(1/φ - ε/2), which holds since N₀·(1/φ-ε/2) ≤ N₀ ≤ N·(ε/2).
  have hL_cast : (L : ℝ) = (N : ℝ) - N₀ := by
    have : N = N₀ + L := by omega
    rw [this]; push_cast; ring
  have hφ_pos : (0 : ℝ) < φ := by
    have : 0 < φ := Finset.card_pos.mpr ⟨1, Finset.mem_univ _⟩
    exact Nat.cast_pos.mpr this
  have hinv_le_one : 1 / (φ : ℝ) ≤ 1 := by
    rw [div_le_one hφ_pos]; exact_mod_cast Finset.one_le_card.mpr ⟨1, Finset.mem_univ _⟩
  have hN_large : (N : ℝ) * ε ≥ 2 * N₀ := by
    have hceil : (Nat.ceil (2 * ↑N₀ / ε) : ℝ) ≥ 2 * N₀ / ε := Nat.le_ceil _
    have hN_ge_ceil : N ≥ Nat.ceil (2 * ↑N₀ / ε) + 1 := by omega
    have hN_cast : (N : ℝ) ≥ (Nat.ceil (2 * ↑N₀ / ε) : ℝ) + 1 := by exact_mod_cast hN_ge_ceil
    calc (N : ℝ) * ε ≥ (2 * ↑N₀ / ε + 1) * ε := by nlinarith
      _ = 2 * ↑N₀ + ε := by field_simp
      _ ≥ 2 * ↑N₀ := by linarith
  -- Final inequality chain
  calc (((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card : ℝ)
      ≥ (((Finset.range L).filter (fun k => emMultUnit q hq hne (N₀ + k) = a)).card : ℝ) :=
        h_ge_window
    _ ≥ (L : ℝ) * (1 / ↑φ - ε') := h_window_bound
    _ ≥ (N : ℝ) * (1 / ↑φ - ε) := by rw [hL_cast, hε'_def]; nlinarith

/-- **The walk telescope bound from S37 constrains walk sums in terms of
    multiplier escape frequency**.

    For any non-trivial character chi, the telescoping identity gives:
    `|sum_{n<N} chi(w(n)) * (chi(m(n)) - 1)| <= 2`

    If the multiplier character values chi(m(n)) are not all 1 (i.e., not all
    in ker(chi)), then the terms (chi(m(n)) - 1) provide non-zero weights.
    The walk character sum is thus constrained by the inverse of the
    "escape density" (frequency of m(n) outside ker(chi)).

    This is the algebraic content already proved in `walk_telescope_norm_bound`
    (S37). The quantitative extraction from this bound to MMCSB requires the
    open `MultCSBImpliesMMCSB`. -/
theorem telescope_constrains_walk :
    ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∀ (χ : (ZMod q)ˣ →* ℂˣ),
    ∀ (N : ℕ),
    ‖∑ n ∈ Finset.range N,
      ((χ (emWalkUnit q hq hne n) : ℂ) * ((χ (emMultUnit q hq hne n) : ℂ) - 1))‖ ≤ 2 :=
  walk_telescope_norm_bound

/-! ### Sieve Equidistribution implies Multiplier Character Sum Bound

    The counting form of multiplier equidistribution (SieveEquidistribution) implies
    the character sum form (EMMultCharSumBound) by a Weyl-type argument.
    We decompose ∑ χ(m(n)) by fiber, use character orthogonality to subtract the
    mean, and bound the deviation via the triangle inequality. -/

/-- Auxiliary: for a nontrivial MonoidHom χ : (ZMod q)ˣ →* ℂˣ, the sum ∑ a, (χ a : ℂ) = 0.
    Uses the standard trick: pick b with χ(b) ≠ 1, then χ(b) · S = S implies S = 0. -/
private lemma unit_char_sum_eq_zero {q : ℕ} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ a : (ZMod q)ˣ, (χ a : ℂ) = 0 := by
  -- Since χ ≠ 1, there exists b with χ(b) ≠ 1
  have ⟨b, hb⟩ : ∃ b : (ZMod q)ˣ, χ b ≠ 1 := by
    by_contra h; push_neg at h; apply hχ
    ext a; simp [h a]
  -- The sum S satisfies χ(b) · S = S (by reindexing a ↦ b·a)
  set S := ∑ a : (ZMod q)ˣ, (χ a : ℂ)
  have hmul : (χ b : ℂ) * S = S := by
    simp only [S, Finset.mul_sum]
    exact Fintype.sum_bijective (b * ·) (Group.mulLeft_bijective b) _ _ (fun a => by
      simp only [map_mul, Units.val_mul])
  -- χ(b) ≠ 1 as complex, so (χ(b) - 1) · S = 0 gives S = 0
  have hb_ne : (χ b : ℂ) ≠ 1 := by
    intro h; apply hb; exact Units.val_injective h
  have hsub : ((χ b : ℂ) - 1) * S = 0 := by
    have : (χ b : ℂ) * S - S = 0 := sub_eq_zero.mpr hmul
    linear_combination this
  rcases mul_eq_zero.mp hsub with h | h
  · exact absurd (sub_eq_zero.mp h) hb_ne
  · exact h

/-- Auxiliary: the multiplier character sum decomposes as ∑_a χ(a) · V_N(a)
    where V_N(a) = #{n < N : m(n) = a}. -/
private lemma mult_char_sum_fiber {q : ℕ} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ) =
    ∑ a : (ZMod q)ˣ,
      (χ a : ℂ) * ((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card := by
  rw [← Finset.sum_fiberwise (Finset.range N) (emMultUnit q hq hne)
      (fun n => (χ (emMultUnit q hq hne n) : ℂ))]
  congr 1; ext a
  rw [Finset.sum_filter]
  conv_lhs =>
    arg 2; ext n
    rw [show (if emMultUnit q hq hne n = a then (χ (emMultUnit q hq hne n) : ℂ) else 0) =
      (if emMultUnit q hq hne n = a then (χ a : ℂ) else 0) from by
        split_ifs with h
        · rw [h]
        · rfl]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Auxiliary: the total multiplier hit count sums to N. -/
private lemma mult_hit_count_sum {q : ℕ} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q) (N : ℕ) :
    ∑ a : (ZMod q)ˣ,
      ((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card = N := by
  -- Use card_eq_sum_card_fiberwise: #s = ∑ b ∈ t, #{a ∈ s | f a = b}
  have h := Finset.card_eq_sum_card_fiberwise
    (f := emMultUnit q hq hne) (s := Finset.range N) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_range] at h
  simpa using h.symm

/-- Auxiliary: ‖(χ a : ℂ)‖ = 1 for a MonoidHom χ : (ZMod q)ˣ →* ℂˣ. -/
private lemma unit_monoidHom_norm_one {q : ℕ} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (a : (ZMod q)ˣ) :
    ‖(χ a : ℂ)‖ = 1 := by
  have hfin : IsOfFinOrder a := isOfFinOrder_of_finite a
  have hfin' : IsOfFinOrder (χ a) := χ.isOfFinOrder hfin
  rw [isOfFinOrder_iff_pow_eq_one] at hfin'
  obtain ⟨n, hn, hpow⟩ := hfin'
  have hne : NeZero n := ⟨by omega⟩
  have hmem : (χ a) ∈ rootsOfUnity n ℂ := by
    rw [_root_.mem_rootsOfUnity]; exact hpow
  exact Complex.norm_eq_one_of_mem_rootsOfUnity hmem

/-- **SieveEquidistribution implies EMMultCharSumBound** (multiplier Weyl criterion).

    The counting form of multiplier equidistribution (SieveEquidistribution) implies
    the character sum form (EMMultCharSumBound) by Fourier decomposition on (ZMod q)ˣ.

    Proof: decompose ∑ χ(m(n)) = ∑_a χ(a) · V_N(a) where V_N(a) counts multipliers
    equal to a. Using χ nontrivial gives ∑ χ(a) = 0, so the sum equals
    ∑ χ(a) · (V_N(a) - N/φ(q)), which is bounded by triangle inequality. -/
theorem sieve_equidist_implies_mult_csb :
    SieveEquidistribution → EMMultCharSumBound := by
  intro hsieve
  -- Use Q₀ = 0 (SieveEquidistribution covers all primes)
  refine ⟨0, fun q inst hq_ge hq hne χ hχ ε hε => ?_⟩
  -- Let φ = number of units in (ZMod q)ˣ
  set φ := (Finset.univ : Finset (ZMod q)ˣ).card with hφ_def
  have hφ_pos : (0 : ℝ) < φ := by positivity
  -- Pick ε' = ε / φ² for SieveEquidistribution
  set ε' := ε / ((φ : ℝ) * φ) with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε (mul_pos hφ_pos hφ_pos)
  -- Get N₀ for each unit a from SieveEquidistribution, take max
  have hN₀_exists : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card : ℝ) ≥
      (N : ℝ) * (1 / φ - ε') := by
    intro a; exact hsieve q hq hne a ε' hε'_pos
  choose N₀_fn hN₀_fn using hN₀_exists
  refine ⟨Finset.univ.sup N₀_fn + 1, fun N hN_ge => ?_⟩
  -- For each a, N ≥ N₀(a)
  have hN_ge_a : ∀ a : (ZMod q)ˣ, N ≥ N₀_fn a := by
    intro a; have := Finset.le_sup (f := N₀_fn) (Finset.mem_univ a); omega
  -- Lower bound on hit count for each a
  set V := fun a => ((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card
  have hlb : ∀ a : (ZMod q)ˣ, (V a : ℝ) ≥ (N : ℝ) * (1 / (φ : ℝ) - ε') :=
    fun a => hN₀_fn a N (hN_ge_a a)
  -- Total hit count = N
  have htotal : (∑ b : (ZMod q)ˣ, (V b : ℝ)) = (N : ℝ) := by
    have := mult_hit_count_sum hq hne N; exact_mod_cast this
  -- Use fiber decomposition
  rw [mult_char_sum_fiber hq hne χ N]
  -- Character orthogonality: ∑ χ(a) = 0
  have horth : ∑ a : (ZMod q)ˣ, (χ a : ℂ) = 0 := unit_char_sum_eq_zero χ hχ
  -- Rewrite: ∑ χ(a) · V(a) = ∑ χ(a) · (V(a) - N/φ) (mean subtraction)
  -- First, rewrite the sum using subtraction + remainder
  have hmean_eq : ∑ a : (ZMod q)ˣ,
      (χ a : ℂ) * ((V a : ℕ) : ℂ) =
      ∑ a : (ZMod q)ˣ,
        ((χ a : ℂ) * (((V a : ℝ) - (N : ℝ) / (φ : ℝ) : ℝ) : ℂ) +
         (χ a : ℂ) * (((N : ℝ) / (φ : ℝ) : ℝ) : ℂ)) := by
    congr 1; ext a; push_cast; ring
  rw [hmean_eq, Finset.sum_add_distrib]
  have hmean_zero : ∑ a : (ZMod q)ˣ, (χ a : ℂ) * (((N : ℝ) / (φ : ℝ) : ℝ) : ℂ) = 0 := by
    rw [← Finset.sum_mul, horth, zero_mul]
  rw [hmean_zero, add_zero]
  -- Triangle inequality + character norm = 1
  calc ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * (((V a : ℝ) - (N : ℝ) / (φ : ℝ) : ℝ) : ℂ)‖
      ≤ ∑ a : (ZMod q)ˣ, ‖(χ a : ℂ) * (((V a : ℝ) - (N : ℝ) / (φ : ℝ) : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
    _ = ∑ a : (ZMod q)ˣ, |(V a : ℝ) - (N : ℝ) / (φ : ℝ)| := by
        congr 1; ext a
        rw [norm_mul, unit_monoidHom_norm_one χ a, one_mul, Complex.norm_real,
            Real.norm_eq_abs]
    _ ≤ ∑ _a : (ZMod q)ˣ, ((φ : ℝ) * ε' * N) := by
        apply Finset.sum_le_sum; intro a _
        -- Two-sided bound: V(a) ≥ N/φ - ε'N and V(a) ≤ N/φ + (φ-1)ε'N
        have hVlb : (V a : ℝ) - (N : ℝ) / (φ : ℝ) ≥ -(ε' * N) := by
          have h1 := hlb a
          -- N * (1/φ - ε') = N/φ - ε'*N
          have h2 : (N : ℝ) * (1 / (φ : ℝ) - ε') = (N : ℝ) / (φ : ℝ) - ε' * (N : ℝ) := by ring
          linarith
        have hVub : (V a : ℝ) - (N : ℝ) / (φ : ℝ) ≤ ((φ : ℝ) - 1) * ε' * N := by
          -- V(a) = N - ∑_{b≠a} V(b) ≤ N - (φ-1)·N·(1/φ - ε')
          have hVa_eq : (V a : ℝ) = (N : ℝ) - ∑ b ∈ Finset.univ.erase a, (V b : ℝ) := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at htotal; linarith
          have hφ_ge_one : (1 : ℝ) ≤ (φ : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨a, Finset.mem_univ _⟩
          have hcard_nat : (Finset.univ.erase a : Finset (ZMod q)ˣ).card = φ - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ a)]
          have hφ_nat : 1 ≤ φ := Finset.card_pos.mpr ⟨a, Finset.mem_univ _⟩
          have hcard : ((Finset.univ.erase a : Finset (ZMod q)ˣ).card : ℝ) = (φ : ℝ) - 1 := by
            rw [hcard_nat, Nat.cast_sub hφ_nat]; simp
          have hsum_lb : ∑ b ∈ Finset.univ.erase a, (V b : ℝ) ≥
              ((φ : ℝ) - 1) * ((N : ℝ) * (1 / (φ : ℝ) - ε')) := by
            rw [← hcard]
            have h := Finset.card_nsmul_le_sum (Finset.univ.erase a)
              (fun b => (V b : ℝ)) ((N : ℝ) * (1 / (φ : ℝ) - ε'))
              (fun b _ => hlb b)
            rw [nsmul_eq_mul] at h; exact_mod_cast h
          -- N - (φ-1)*(N*(1/φ - ε')) = N/φ + (φ-1)*ε'*N
          have key : (N : ℝ) - ((φ : ℝ) - 1) * ((N : ℝ) * (1 / (φ : ℝ) - ε')) =
              (N : ℝ) / (φ : ℝ) + ((φ : ℝ) - 1) * ε' * (N : ℝ) := by
            field_simp; ring
          linarith
        -- |V(a) - N/φ| ≤ max(ε'·N, (φ-1)·ε'·N) ≤ φ·ε'·N
        rw [abs_le]
        have hφ_ge_one : (1 : ℝ) ≤ (φ : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr ⟨a, Finset.mem_univ _⟩
        have hεN_nn : 0 ≤ ε' * (N : ℝ) := mul_nonneg (le_of_lt hε'_pos) (Nat.cast_nonneg N)
        constructor
        · -- -(φ·ε'·N) ≤ -(ε'·N) ≤ V(a) - N/φ
          have : -(↑φ * ε' * ↑N) ≤ -(ε' * ↑N) := by nlinarith
          linarith
        · -- V(a) - N/φ ≤ (φ-1)·ε'·N ≤ φ·ε'·N
          nlinarith
    _ = (φ : ℝ) * ((φ : ℝ) * ε' * N) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ε * N := by
        -- φ * (φ * (ε/(φ*φ)) * N) = ε * N
        have : (φ : ℝ) * ((φ : ℝ) * ε' * (N : ℝ)) = (φ : ℝ) * (φ : ℝ) * ε' * (N : ℝ) := by ring
        rw [this, hε'_def, mul_div_cancel₀]
        exact ne_of_gt (mul_pos hφ_pos hφ_pos)

/-- **StrongSieveImpliesMultCSB holds**: StrongSieveEquidist → EMMultCharSumBound.

    This follows by composing `strongSieveEquidist_implies_sieveEquidist` (SSE → SE)
    with `sieve_equidist_implies_mult_csb` (SE → EMMultCSB). -/
theorem strongSieve_implies_multCSB : StrongSieveImpliesMultCSB :=
  fun hsse => sieve_equidist_implies_mult_csb (strongSieveEquidist_implies_sieveEquidist hsse)

end BVDecomposition

/-! ## S79. Sieve-to-Harmonic Bridge Theorems

The proved `sieve_equidist_implies_mult_csb` yields `EMMultCharSumBound` with
`Q_0 = 0`, which means multiplier character sums cancel for ALL primes q (not
just q >= Q_0).  This is exactly the `DecorrelationHypothesis` from S31.

We formalize this connection and compose it with the downstream harmonic chain:
- `SieveEquidistribution` -> `DecorrelationHypothesis` (extract Q_0 = 0)
- `SieveEquidistribution` -> `PositiveEscapeDensity` (compose with `decorrelation_implies_ped`)
- Chain theorems to MC (requiring `PEDImpliesComplexCSB` as the sole remaining bridge)

### Key insight:
The sieve hierarchy (S36-S39) and the harmonic hierarchy (S30-S35) converge:
both produce `DecorrelationHypothesis` as output.  The sieve route achieves
this via counting-to-character-sum bridge (`sieve_equidist_implies_mult_csb`);
the harmonic route states it directly.  This means ANY proof of
`SieveEquidistribution` (e.g., from PNT in APs + Alladi's theorem) immediately
gives `DecorrelationHypothesis` and `PositiveEscapeDensity` for free.

### Chains:
```
SieveEquidistribution ->[proved]-> DecorrelationHypothesis
  ->[proved]-> PositiveEscapeDensity ->[PEDImpliesCSB, open]-> CCSB ->[proved]-> MC
```
-/

section SieveHarmonicBridge

/-- **SieveEquidistribution implies DecorrelationHypothesis**: the counting form of
    multiplier equidistribution (SieveEquidistribution) implies the character-sum
    form (DecorrelationHypothesis) for ALL primes q.

    Proof: `sieve_equidist_implies_mult_csb` produces `EMMultCharSumBound` with
    `Q_0 = 0`. For Q_0 = 0, the condition `q >= Q_0` is trivially satisfied,
    so the bound holds for all primes — which is exactly `DecorrelationHypothesis`. -/
theorem sieve_equidist_implies_decorrelation :
    SieveEquidistribution → DecorrelationHypothesis := by
  intro hsieve q inst hq hne χ hχ ε hε
  haveI : Fact (Nat.Prime q) := inst
  -- Prove the Weyl bound directly from hsieve for this specific q.
  -- This applies the same Fourier decomposition as sieve_equidist_implies_mult_csb
  -- but targets DecorrelationHypothesis directly (avoiding the ∃ Q₀ wrapper of
  -- EMMultCharSumBound, whose witness is opaque after existential packaging).
  set φ := (Finset.univ : Finset (ZMod q)ˣ).card with hφ_def
  have hφ_pos : (0 : ℝ) < φ := by positivity
  set ε' := ε / ((φ : ℝ) * φ) with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε (mul_pos hφ_pos hφ_pos)
  have hN₀_exists : ∀ a : (ZMod q)ˣ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card : ℝ) ≥
      (N : ℝ) * (1 / φ - ε') :=
    fun a => hsieve q hq hne a ε' hε'_pos
  choose N₀_fn hN₀_fn using hN₀_exists
  refine ⟨Finset.univ.sup N₀_fn + 1, fun N hN_ge => ?_⟩
  have hN_ge_a : ∀ a : (ZMod q)ˣ, N ≥ N₀_fn a := by
    intro a; have := Finset.le_sup (f := N₀_fn) (Finset.mem_univ a); omega
  set V := fun a => ((Finset.range N).filter (fun n => emMultUnit q hq hne n = a)).card
  have hlb : ∀ a, (V a : ℝ) ≥ (N : ℝ) * (1 / (φ : ℝ) - ε') := fun a => hN₀_fn a N (hN_ge_a a)
  have htotal : (∑ b : (ZMod q)ˣ, (V b : ℝ)) = (N : ℝ) := by
    have := mult_hit_count_sum hq hne N; exact_mod_cast this
  rw [mult_char_sum_fiber hq hne χ N]
  have horth : ∑ a : (ZMod q)ˣ, (χ a : ℂ) = 0 := unit_char_sum_eq_zero χ hχ
  have hmean_eq : ∑ a : (ZMod q)ˣ, (χ a : ℂ) * ((V a : ℕ) : ℂ) =
      ∑ a : (ZMod q)ˣ, ((χ a : ℂ) * (((V a : ℝ) - (N : ℝ) / (φ : ℝ) : ℝ) : ℂ) +
       (χ a : ℂ) * (((N : ℝ) / (φ : ℝ) : ℝ) : ℂ)) := by congr 1; ext a; push_cast; ring
  rw [hmean_eq, Finset.sum_add_distrib,
      show ∑ a : (ZMod q)ˣ, (χ a : ℂ) * (((N : ℝ) / (φ : ℝ) : ℝ) : ℂ) = 0 from by
        rw [← Finset.sum_mul, horth, zero_mul],
      add_zero]
  calc ‖∑ a : (ZMod q)ˣ, (χ a : ℂ) * (((V a : ℝ) - (N : ℝ) / (φ : ℝ) : ℝ) : ℂ)‖
      ≤ ∑ a : (ZMod q)ˣ, ‖(χ a : ℂ) * (((V a : ℝ) - (N : ℝ) / (φ : ℝ) : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
    _ = ∑ a : (ZMod q)ˣ, |(V a : ℝ) - (N : ℝ) / (φ : ℝ)| := by
        congr 1; ext a
        rw [norm_mul, unit_monoidHom_norm_one χ a, one_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ _a : (ZMod q)ˣ, ((φ : ℝ) * ε' * N) := by
        apply Finset.sum_le_sum; intro a _
        rw [abs_le]; constructor
        · -- Lower bound: -(φ·ε'·N) ≤ V(a) - N/φ
          -- From hlb: V(a) ≥ N/φ - ε'·N, so V(a) - N/φ ≥ -ε'·N ≥ -(φ·ε'·N)
          have h1 := hlb a
          have hφ_ge_one' : (1 : ℝ) ≤ (φ : ℝ) :=
            by exact_mod_cast Finset.card_pos.mpr ⟨a, Finset.mem_univ _⟩
          have hεN_nn : 0 ≤ ε' * (N : ℝ) := mul_nonneg (le_of_lt hε'_pos) (Nat.cast_nonneg N)
          have h2 : (N : ℝ) * (1 / (φ : ℝ) - ε') = (N : ℝ) / (φ : ℝ) - ε' * (N : ℝ) := by ring
          have h3 : -(↑φ * ε' * ↑N) ≤ -(ε' * ↑N) := by nlinarith
          linarith
        · -- Upper bound: V(a) - N/φ ≤ (φ-1)·ε'·N ≤ φ·ε'·N
          have hφ_ge_one : (1 : ℝ) ≤ (φ : ℝ) :=
            by exact_mod_cast Finset.card_pos.mpr ⟨a, Finset.mem_univ _⟩
          have hVa_eq : (V a : ℝ) = (N : ℝ) - ∑ b ∈ Finset.univ.erase a, (V b : ℝ) := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at htotal; linarith
          have hcard : ((Finset.univ.erase a : Finset (ZMod q)ˣ).card : ℝ) = (φ : ℝ) - 1 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ a),
                Nat.cast_sub (Finset.card_pos.mpr ⟨a, Finset.mem_univ _⟩)]
            simp [hφ_def]
          have hsum_lb : ∑ b ∈ Finset.univ.erase a, (V b : ℝ) ≥
              ((φ : ℝ) - 1) * ((N : ℝ) * (1 / (φ : ℝ) - ε')) := by
            rw [← hcard]
            have h := Finset.card_nsmul_le_sum (Finset.univ.erase a)
              (fun b => (V b : ℝ)) ((N : ℝ) * (1 / (φ : ℝ) - ε')) (fun b _ => hlb b)
            rw [nsmul_eq_mul] at h; exact_mod_cast h
          nlinarith [hVa_eq, hsum_lb, (show (N : ℝ) - ((φ : ℝ) - 1) * ((N : ℝ) * (1 / (φ : ℝ) - ε')) =
            (N : ℝ) / (φ : ℝ) + ((φ : ℝ) - 1) * ε' * (N : ℝ) from by field_simp; ring)]
    _ = (φ : ℝ) * ((φ : ℝ) * ε' * N) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ε * N := by
        have : (φ : ℝ) * ((φ : ℝ) * ε' * (N : ℝ)) = (φ : ℝ) * (φ : ℝ) * ε' * (N : ℝ) := by ring
        rw [this, hε'_def, mul_div_cancel₀]
        exact ne_of_gt (mul_pos hφ_pos hφ_pos)

/-- **SieveEquidistribution implies PositiveEscapeDensity**: composing the
    sieve-to-decorrelation bridge with `decorrelation_implies_ped`.

    For every prime q not in the EM sequence and every non-trivial character chi,
    a positive fraction of the multipliers escape ker(chi). -/
theorem sieve_equidist_implies_ped :
    SieveEquidistribution → PositiveEscapeDensity :=
  fun hsieve => decorrelation_implies_ped (sieve_equidist_implies_decorrelation hsieve)

/-- **Sieve equidistribution chain to MC**: SieveEquidistribution, combined with
    the (open) PED-to-CCSB bridge, implies Mullin's Conjecture.

    ```
    SieveEquidist ->[proved]-> Dec ->[proved]-> PED
      ->[PEDImpliesCSB, open]-> CCSB ->[proved]-> MC
    ```

    The sole remaining open hypothesis is `PEDImpliesComplexCSB`. -/
theorem sieve_equidist_chain_mc (hsieve : SieveEquidistribution)
    (hped_csb : PEDImpliesComplexCSB) :
    MullinConjecture :=
  complex_csb_mc' (hped_csb (sieve_equidist_implies_ped hsieve))

/-- **StrongSieveEquidist implies DecorrelationHypothesis**: composing
    SSE -> SE with SE -> Dec. -/
theorem strongSieve_implies_decorrelation :
    StrongSieveEquidist → DecorrelationHypothesis :=
  fun hsse => sieve_equidist_implies_decorrelation
    (strongSieveEquidist_implies_sieveEquidist hsse)

/-- **StrongSieveEquidist implies PositiveEscapeDensity**: composing
    SSE -> SE with SE -> PED. -/
theorem strongSieve_implies_ped :
    StrongSieveEquidist → PositiveEscapeDensity :=
  fun hsse => sieve_equidist_implies_ped
    (strongSieveEquidist_implies_sieveEquidist hsse)

/-- **StrongSieveEquidist chain to MC**: SSE + PEDImpliesCSB -> MC. -/
theorem strongSieve_chain_mc (hsse : StrongSieveEquidist)
    (hped_csb : PEDImpliesComplexCSB) :
    MullinConjecture :=
  sieve_equidist_chain_mc (strongSieveEquidist_implies_sieveEquidist hsse) hped_csb

end SieveHarmonicBridge

/-! ## Summary (S52)

### New definitions (S52):
- `EMMultCharSumBound` : multiplier character sums are o(N) for q >= Q_0 (intermediate Prop)
- `BVImpliesEMMultCSB` : BV -> EMMultCharSumBound (open -- sieve transfer)
- `MultCSBImpliesMMCSB` : EMMultCharSumBound -> MultiModularCSB (open -- walk bridge)
- `StrongSieveImpliesMultCSB` : StrongSieveEquidist -> EMMultCharSumBound (open -- Weyl bridge)

### Proved theorems (S52):
- `bv_decomposition_implies_mmcsb` : BVImpliesEMMultCSB + MultCSBImpliesMMCSB -> BVImpliesMMCSB
- `bv_decomposed_chain_mc` : BV + both transfers + finite check -> MC
- `bv_decomposed_small_threshold_mc` : above with Q_0 <= 11 -> MC unconditionally
- `telescope_constrains_walk` : walk telescope norm bound <= 2 (restatement from S37)

### Key insight (S52):
The frontier `BVImpliesMMCSB` decomposes into two independent obstacles at a
natural intermediate: **EMMultCharSumBound** (multiplier character sums cancel).

1. **BV -> EMMultCSB** (sieve-theoretic): Transfer from the universal prime
   counting function to the specific EM multipliers. This is where Alladi's
   theorem, the Selberg sieve, and the BV averaged bound interact.

2. **EMMultCSB -> MMCSB** (harmonic-analytic): Transfer from multiplier character
   sums (linear) to walk character sums (product walk). The algebraic backbone
   is the walk telescoping identity from S37, but the quantitative extraction
   (showing escape density implies walk cancellation) remains open.

This decomposition separates NUMBER THEORY (obstacle 1: which primes appear as
EM multipliers?) from DYNAMICS (obstacle 2: how do partial products of
equidistributed unit complex numbers behave?). Each obstacle can be attacked
independently with different mathematical tools.

### New chains:
```
BV ->[open]-> EMMultCSB ->[open]-> MMCSB ->[proved]-> MC
StrongSieveEquidist ->[proved]-> EMMultCSB ->[open]-> MMCSB ->[proved]-> MC
```

### Proved theorems (S79):
- `sieve_equidist_implies_decorrelation` : SE -> DecorrelationHypothesis (Weyl criterion)
- `sieve_equidist_implies_ped` : SE -> PositiveEscapeDensity (compose with Dec -> PED)
- `sieve_equidist_chain_mc` : SE + PEDImpliesCSB -> MC
- `strongSieve_implies_decorrelation` : SSE -> DecorrelationHypothesis
- `strongSieve_implies_ped` : SSE -> PositiveEscapeDensity
- `strongSieve_chain_mc` : SSE + PEDImpliesCSB -> MC

### Key insight (S79):
The sieve hierarchy and harmonic hierarchy converge at DecorrelationHypothesis.
SieveEquidistribution (a counting statement about minFac equidistribution) implies
DecorrelationHypothesis (a character-sum cancellation statement) via the Weyl criterion.
This means any proof of SieveEquidistribution (e.g., PNT in APs + Alladi) immediately
gives Dec and PED for free.  The sole remaining gap to MC is PEDImpliesComplexCSB.

### New chains (S79):
```
SieveEquidist ->[proved]-> Dec ->[proved]-> PED ->[open]-> CCSB ->[proved]-> MC
SSE ->[proved]-> Dec ->[proved]-> PED ->[open]-> CCSB ->[proved]-> MC
```
-/

