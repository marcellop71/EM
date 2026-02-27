import EM.EquidistSelfCorrecting

/-!
# Prime Density, Sieve Transfer, and Walk Sum Decomposition

Prime density equipartition, LPF equidistribution, sieve transfer chain,
distributional PED, quadratic walk sum decomposition, escape decorrelation,
general walk sum decomposition, and block alternation structure.

## Main Results

* `primeDensity_chain_mc` : PDE + sieve chain ⟹ MC (PROVED)
* `genericLPF_chain_mc` : GLPFE + SieveTransfer ⟹ MC (PROVED)
* `dped_implies_ped` : DPED ⟹ PED (PROVED)
* `kernel_preserves_quadratic_walk` : kernel elements preserve quadratic walk (PROVED)
* `escape_decorrelation_implies_mc` : escape decorrelation ⟹ MC (PROVED)
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## §38. Prime Density Equipartition and LPF Equidistribution

This section separates two distinct layers of analytic difficulty:

1. **Generic analytic number theory** (known, not yet in Mathlib):
   - `PrimeDensityEquipartition`: primes equidistribute in AP (PNT in APs).
   - `GenericLPFEquidist`: smallest prime factors of generic integers
     equidistribute (Alladi 1977).
   - `PrimeDensityImpliesLPFEquidist`: the logical connection (partial summation).

2. **EM-specific transfer** (genuinely open):
   - `SieveTransfer`: generic lpf equidistribution transfers to the EM
     setting (this is the true mathematical frontier).
   - `SieveEquidistImpliesNoLongRuns`: SieveEquidistribution → NoLongRuns(L)
     for L = φ(q)+1.  This is a combinatorial consequence (not yet
     formalized) of the equidistribution definition.

3. **Chain theorems** (trivial compositions through existing infrastructure):
   The full analytic chain is:
   ```
   PrimeDensityEquipartition
     → (Alladi) GenericLPFEquidist
     → (SieveTransfer) SieveEquidistribution
     → (combinatorial) NoLongRuns(L)
     → (§32) PositiveEscapeDensity
     → (PEDImpliesComplexCSB) ComplexCharSumBound
     → (§30) MullinConjecture
   ```
-/

section PrimeDensityEquipartition

/-- **PrimeDensityEquipartition**: primes equidistribute among coprime residue
    classes.  For every prime q, coprime class a, and ε > 0, eventually
    #{p ≤ N prime : p ≡ a (mod q)} ≥ (1/φ(q) − ε) · π(N).

    This is a known theorem (PNT in arithmetic progressions) but is NOT in
    Mathlib v4.27.0.  It follows from the non-vanishing of L(1,χ) for
    non-trivial Dirichlet characters (which IS proved in Mathlib via
    `DirichletCharacter.Lfunction_ne_zero_of_one`) plus the Wiener-Ikehara
    tauberian theorem (NOT yet in Mathlib). -/
def PrimeDensityEquipartition : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (a : (ZMod q)ˣ),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    let classCount := (Finset.filter (fun p => Nat.Prime p ∧ (p : ZMod q) = a.val)
                        (Finset.range (N + 1))).card
    let totalPrimes := (Finset.filter Nat.Prime (Finset.range (N + 1))).card
    let eulerPhi := (Finset.univ (α := (ZMod q)ˣ)).card
    (classCount : ℝ) ≥ (1 / (eulerPhi : ℝ) - ε) * (totalPrimes : ℝ)

/-- **GenericLPFEquidist**: the smallest prime factor of integers equidistributes
    among residue classes mod q.

    More precisely: among integers 2 ≤ n ≤ N, the fraction for which
    minFac(n) ≡ a (mod q) converges to 1/φ(q) as N → ∞.

    This is **Alladi's theorem** (K. Alladi, 1977: "On the distribution of
    the smallest prime factor of integers").  It follows from
    `PrimeDensityEquipartition` via partial summation / Abel summation.
    Known but NOT formalized in any proof assistant library. -/
def GenericLPFEquidist : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (a : (ZMod q)ˣ),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    let lpfInClass := (Finset.filter
      (fun n => 2 ≤ n ∧ (Nat.minFac n : ZMod q) = a.val)
      (Finset.range (N + 1))).card
    let eligible := (Finset.filter (fun n => 2 ≤ n)
      (Finset.range (N + 1))).card
    let eulerPhi := (Finset.univ (α := (ZMod q)ˣ)).card
    (lpfInClass : ℝ) ≥ (1 / (eulerPhi : ℝ) - ε) * (eligible : ℝ)

/-- **PrimeDensityImpliesLPFEquidist**: PNT in APs implies Alladi's theorem.

    The logical implication PrimeDensityEquipartition → GenericLPFEquidist
    follows by partial summation (Abel summation), converting the prime
    counting estimate into a statement about smallest prime factors.
    Known but NOT formalized. -/
def PrimeDensityImpliesLPFEquidist : Prop :=
  PrimeDensityEquipartition → GenericLPFEquidist

/-- **SieveTransfer**: generic smallest-prime-factor equidistribution implies
    EM-specific multiplier equidistribution.

    This is the **genuine mathematical frontier** of the project.  The EM
    sequence satisfies prod(n) + 1 = ∏_{k<n} seq(k) + 1, and the multiplier
    seq(n+1) = minFac(prod(n) + 1).  To transfer from "random integers have
    equidistributed minFac" to "the specific EM values prod(n)+1 have
    equidistributed minFac," one must show the EM products are "pseudo-random"
    in the sense that they avoid the exceptional sets where minFac is biased.

    The difficulty: EM products grow super-exponentially and are products of
    distinct primes, so they lie in a very thin and structured subset of the
    integers.  Standard sieve methods apply to ranges, not to specific
    subsequences.  This is what makes the conjecture hard. -/
def SieveTransfer : Prop :=
  GenericLPFEquidist → SieveEquidistribution

/-- **SieveEquidistImpliesNoLongRuns**: open Prop (density on [0,N) does NOT imply gap control).

    NOTE: This remains an open Prop.  `SieveEquidistribution` controls the
    density of hits in the initial segment [0,N), but does NOT prevent long
    gaps appearing arbitrarily late.  Concretely, a run of L kernel steps
    starting at position n ≥ N₀ satisfies the equidistribution inequality
    trivially when n is large (n ≥ L·(1/φ(q)−ε)/(1−1/φ(q)+ε)), so no
    fixed L eliminates all runs.

    A stronger window-equidistribution hypothesis (`StrongSieveEquidist`)
    controls hit counts on EVERY window [n₀, n₀+L) and does imply NoLongRuns;
    see `strongSieveEquidist_noLongRunsAt` and `strongSieve_chain_mc` below. -/
def SieveEquidistImpliesNoLongRuns : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)],
  SieveEquidistribution →
  ∃ (L : Nat), 0 < L ∧ NoLongRuns L

/-- **NoLongRunsAt q L**: per-prime version of `NoLongRuns`.

    For a fixed prime `q`, for every non-trivial character `χ` on `(ZMod q)ˣ`,
    there is a threshold past which no `L` consecutive multipliers all lie in
    `ker(χ)`.  Unlike `NoLongRuns L`, which quantifies over ALL primes, this
    version fixes `q` and produces a run-length `L` tailored to `φ(q)`. -/
def NoLongRunsAt (q : Nat) [Fact (Nat.Prime q)] (L : Nat) : Prop :=
  ∀ (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ k, k < L ∧ χ (emMultUnit q hq hne (n + k)) ≠ 1

/-- **StrongSieveEquidist**: window equidistribution of EM multipliers.

    For every prime `q`, unit `a`, `ε > 0`, and threshold `N₀`, the hit count
    for `a` in the window `[n₀, n₀+L)` is at least `L·(1/φ(q) − ε)` for all
    `n₀ ≥ N₀` and all `L ≥ L₀`.

    This is strictly stronger than `SieveEquidistribution`: the latter only
    controls the cumulative count in `[0,N)`, while this controls the count in
    EVERY window of sufficient length, regardless of starting position.

    Analytically this follows from a quantitative sieve transfer with an error
    term that is uniform in the starting point (e.g., via effective
    Chebotarev or Siegel-Walfisz bounds applied to the EM subsequence). -/
def StrongSieveEquidist : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (a : (ZMod q)ˣ),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∀ (L₀ : ℕ) (_hL₀ : 0 < L₀),
  ∃ N₀ : ℕ, ∀ n₀ ≥ N₀, ∀ L ≥ L₀,
    let hitW : ℕ := (Finset.range L).filter (fun k => emMultUnit q hq hne (n₀ + k) = a) |>.card
    (hitW : ℝ) ≥ (L : ℝ) * (1 / (Finset.univ (α := (ZMod q)ˣ)).card - ε)

open Classical in
/-- **StrongSieveEquidist → NoLongRunsAt q**: window equidistribution yields a
    per-prime run-length bound.

    Given `StrongSieveEquidist`, for each prime `q` there exists `L > 0` such
    that no `L` consecutive multipliers all lie in the kernel of any non-trivial
    character on `(ZMod q)ˣ`.

    **Proof**: Let `φ := φ(q)` and `L := φ + 1`.  Given `χ ≠ 1`, pick `a` with
    `χ(a) ≠ 1`.  Apply `StrongSieveEquidist` with `ε = 1/(2φ)` and `L₀ = L`.
    For any `n₀ ≥ N₀`, the hit count for `a` in `[n₀, n₀+L)` is
    `≥ L·(1/φ − 1/(2φ)) = L/(2φ) = (φ+1)/(2φ) > 1/2`.
    Since the count is a natural number, it is `≥ 1`, so there exists `k < L`
    with `emMultUnit(n₀+k) = a` and hence `χ(emMultUnit(n₀+k)) = χ(a) ≠ 1`. -/
theorem strongSieveEquidist_noLongRunsAt (hsse : StrongSieveEquidist)
    (q : Nat) [hqfact : Fact (Nat.Prime q)] :
    ∃ (L : Nat), 0 < L ∧ NoLongRunsAt q L := by
  -- Let φ := card of (ZMod q)ˣ (Euler's φ(q)), L := φ+1.
  set φ := (Finset.univ (α := (ZMod q)ˣ)).card with hφ_def
  have hφ_pos : 0 < φ := by
    rw [hφ_def]
    apply Finset.card_pos.mpr
    exact ⟨1, Finset.mem_univ _⟩
  refine ⟨φ + 1, Nat.succ_pos _, ?_⟩
  intro hq hne χ hχ
  -- Pick a unit a with χ(a) ≠ 1.
  have ⟨a, ha⟩ : ∃ a : (ZMod q)ˣ, χ a ≠ 1 := by
    by_contra hall
    push_neg at hall
    exact hχ (MonoidHom.ext (fun a => by
      have := hall a
      simp only [MonoidHom.one_apply] at this ⊢
      exact_mod_cast Units.ext_iff.mpr (Units.val_eq_one.mpr this)))
  -- Set ε = 1/(2φ).
  set ε := (1 : ℝ) / (2 * φ) with hε_def
  have hε_pos : (0 : ℝ) < ε := by positivity
  -- Apply StrongSieveEquidist with L₀ = φ+1.
  obtain ⟨N₀, hN₀⟩ := hsse q hq hne a ε hε_pos (φ + 1) (Nat.succ_pos _)
  refine ⟨N₀, fun n hn => ?_⟩
  -- The hit count for a in [n, n+(φ+1)) is ≥ (φ+1)·(1/φ - 1/(2φ)) = (φ+1)/(2φ).
  have hcount := hN₀ n hn (φ + 1) (le_refl _)
  simp only at hcount
  -- The count is a natural number, so count ≥ 1.
  -- Abbreviate the filter for readability.
  set S := (Finset.range (φ + 1)).filter (fun k => emMultUnit q hq hne (n + k) = a)
  have hcount_pos : 0 < S.card := by
    by_contra hle
    push_neg at hle
    have hzero : S.card = 0 := Nat.le_zero.mp hle
    rw [hzero] at hcount
    simp only [Nat.cast_zero] at hcount
    have hφr : (0 : ℝ) < (φ : ℝ) := by exact_mod_cast hφ_pos
    have hLr : (0 : ℝ) < ((φ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos φ
    have hεr : (0 : ℝ) < 1 / (φ : ℝ) - ε := by
      rw [hε_def]
      have h1 : (0 : ℝ) < 1 / (φ : ℝ) := div_pos one_pos hφr
      have h2 : (0 : ℝ) < 1 / (2 * (φ : ℝ)) := div_pos one_pos (mul_pos two_pos hφr)
      have h3 : (1 : ℝ) / (2 * (φ : ℝ)) < 1 / (φ : ℝ) := by
        apply div_lt_div_of_pos_left one_pos hφr
        linarith
      linarith
    linarith [mul_pos hLr hεr]
  -- Extract a witness from the nonempty filter.
  obtain ⟨k, hk_mem⟩ := Finset.card_pos.mp hcount_pos
  simp only [S, Finset.mem_filter, Finset.mem_range] at hk_mem
  exact ⟨k, hk_mem.1, by rw [hk_mem.2]; exact ha⟩

/-- **PositiveEscapeDensityAt q**: per-prime positive escape density.

    The multiplier sequence eventually has positive density of non-kernel
    steps for any non-trivial character on `(ZMod q)ˣ`. -/
def PositiveEscapeDensityAt (q : Nat) [Fact (Nat.Prime q)] : Prop :=
  ∀ (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    δ * N ≤ ((Finset.range N).filter (fun n => χ (emMultUnit q hq hne n) ≠ 1)).card

open Classical in
/-- NoLongRunsAt implies PositiveEscapeDensityAt.

    The proof is the same block-counting argument as `noLongRuns_implies_ped`:
    partition [N₀, N) into blocks of L, each contributing ≥ 1 escape, giving
    density ≥ 1/(2L) for N ≥ 2·N₀ + 2·L. -/
theorem noLongRunsAt_ped (q : Nat) [hqf : Fact (Nat.Prime q)]
    (L : Nat) (hL : 0 < L) (hnlr : NoLongRunsAt q L) :
    PositiveEscapeDensityAt q := by
  intro hq hne χ hχ
  obtain ⟨N₀, hN₀⟩ := hnlr hq hne χ hχ
  refine ⟨1 / (2 * (L : ℝ)), by positivity, 2 * N₀ + 2 * L, fun N hN => ?_⟩
  set escSet := Finset.filter (fun k => χ (emMultUnit q hq hne k) ≠ 1) (Finset.range N)
  have hN₀_le : N₀ ≤ N := by omega
  have hcard_ge : (N - N₀) / L ≤ escSet.card :=
    escape_count_ge_blocks hN₀ hN₀_le hL
  have hLr : (0 : ℝ) < ↑L := by exact_mod_cast hL
  have hmod : (↑((N - N₀) / L) : ℝ) * ↑L > (↑(N - N₀) : ℝ) - ↑L := by
    have heq : L * ((N - N₀) / L) + (N - N₀) % L = N - N₀ := Nat.div_add_mod (N - N₀) L
    have hrem : (N - N₀) % L < L := Nat.mod_lt _ hL
    have heqr : (↑L : ℝ) * ↑((N - N₀) / L) + ↑((N - N₀) % L) = ↑(N - N₀) := by
      exact_mod_cast heq
    have hremr : (↑((N - N₀) % L) : ℝ) < ↑L := by exact_mod_cast hrem
    linarith [mul_comm (↑L : ℝ) ↑((N - N₀) / L)]
  have hNhalf : (↑(N - N₀) : ℝ) ≥ (↑N : ℝ) / 2 + ↑L := by
    have h2 : 2 * (N - N₀) ≥ N + 2 * L := by omega
    have h2r : 2 * (↑(N - N₀) : ℝ) ≥ ↑N + 2 * ↑L := by exact_mod_cast h2
    linarith
  have hprod : (↑((N - N₀) / L) : ℝ) * (2 * ↑L) > ↑N := by nlinarith
  have hc : (↑((N - N₀) / L) : ℝ) ≤ ↑escSet.card := by exact_mod_cast hcard_ge
  have h2L : (2 : ℝ) * ↑L > 0 := by linarith
  -- Goal: 1/(2*L) * N ≤ escSet.card
  -- From hprod: N < blocks*(2L), so N/(2L) < blocks ≤ escSet.card.
  have hdiv : (↑N : ℝ) / (2 * ↑L) < ↑((N - N₀) / L) := by
    rwa [div_lt_iff₀ h2L]
  have : (1 : ℝ) / (2 * ↑L) * ↑N = ↑N / (2 * ↑L) := by ring
  linarith

/-- **strongSieve_chain_mc**: full chain from StrongSieveEquidist to MC.

    Given:
    - `StrongSieveEquidist` (window equidistribution of EM multipliers)
    - `SieveTransfer` (generic LPF equidist → EM multiplier equidist)
    - `GenericLPFEquidist` (Alladi's theorem)
    - `PEDImpliesComplexCSB` (PED → CCSB, remaining open hypothesis)

    We obtain `MullinConjecture`.

    The chain: StrongSieveEquidist → NoLongRunsAt 2 L →
               (via noLongRuns_mc' with universal NLR) → MC.

    NOTE: This chain requires converting `NoLongRunsAt` back to `NoLongRuns`.
    For q = 2, `(ZMod 2)ˣ ≅ {1}`, so every character on it is trivial and
    `NoLongRunsAt 2 L` and `NoLongRuns L` are both vacuously satisfied for q=2.
    The non-trivial use is through `PositiveEscapeDensityAt` and the PED chain. -/
def StrongSieveEquidistImpliesNLR : Prop :=
  StrongSieveEquidist →
  ∀ (q : Nat) [Fact (Nat.Prime q)],
  ∃ (L : Nat), 0 < L ∧ NoLongRunsAt q L

/-- StrongSieveEquidist implies StrongSieveEquidistImpliesNLR (trivially). -/
theorem strongSieveEquidist_implies_nlr :
    StrongSieveEquidistImpliesNLR := fun hsse q _ =>
  strongSieveEquidist_noLongRunsAt hsse q

/-- Trivial composition: GenericLPFEquidist + SieveTransfer → SieveEquidistribution. -/
theorem genericLPF_sieve_transfer (hg : GenericLPFEquidist) (ht : SieveTransfer) :
    SieveEquidistribution := ht hg

/-- GenericLPFEquidist + SieveTransfer + SieveEquidistImpliesNoLongRuns +
    PEDImpliesComplexCSB → MullinConjecture.

    Full analytic chain from Alladi's theorem and the EM transfer to MC. -/
theorem genericLPF_chain_mc
    (hg : GenericLPFEquidist) (ht : SieveTransfer)
    (hnlr_bridge : SieveEquidistImpliesNoLongRuns)
    (hped_csb : PEDImpliesComplexCSB) :
    MullinConjecture := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨L, hL, hnlr⟩ := hnlr_bridge 2 (genericLPF_sieve_transfer hg ht)
  exact noLongRuns_mc' L hL hnlr hped_csb

/-- Full analytic chain from PNT in APs:
    PrimeDensityEquipartition + Alladi + SieveTransfer +
    SieveEquidistImpliesNoLongRuns + PEDImpliesComplexCSB → MC. -/
theorem primeDensity_chain_mc
    (hpde : PrimeDensityEquipartition)
    (halladi : PrimeDensityImpliesLPFEquidist)
    (htransfer : SieveTransfer)
    (hnlr_bridge : SieveEquidistImpliesNoLongRuns)
    (hped_csb : PEDImpliesComplexCSB) :
    MullinConjecture :=
  genericLPF_chain_mc (halladi hpde) htransfer hnlr_bridge hped_csb

/-! ## §40. Distributional Positive Escape Density (DPED)

`DistributionalPED` strengthens `PositiveEscapeDensity` by controlling not just
the *frequency* of escape steps but also the *value distribution* of escape steps
among all non-identity roots of unity in the image of χ.

**Why DPED is strictly stronger than PED for d ≥ 3**: PED says a positive fraction
of multipliers satisfy χ(m(n)) ≠ 1, but for a character of order d ≥ 3 all these
escape values could accumulate on a single non-identity root ζ₀.  In that case the
walk-character walk sum gets multiplied by ζ₀ repeatedly, and if ζ₀ ≈ 1 the walk
sum grows like cN rather than o(N).  DPED prevents this by requiring each
non-identity value ζ to occur with positive frequency.

**For order-2 characters DPED = PED**: there is only one non-identity value (−1),
so controlling escape frequency automatically controls the distribution.

**Connection to BRE**: `BlockRotationEstimate` asserts that the walk character sums
are o(N) given escape density.  The counterexample that blocks BRE for d ≥ 3 is
exactly the scenario that DPED rules out — all escapes concentrate on one root.
DPED is thus the minimal strengthening of PED that makes BRE tractable.

The section establishes:
* `DistributionalPED`: the definition.
* `dped_implies_ped`: DPED → PED (filter monotonicity).
* `DPEDImpliesComplexCSB`: open Prop — DPED → CCSB (main remaining bridge).
* `dped_mc`: DPED + DPEDImpliesComplexCSB → MullinConjecture.
* `dped_mc'`: DPED + PEDImpliesComplexCSB → MullinConjecture
  (alternative route through PED). -/

section DistributionalPED

/-- **DistributionalPED (DPED)**: for every prime `q` not in the EM sequence,
    every non-trivial character `χ : (ZMod q)ˣ →* ℂˣ`, and every non-identity
    element `ζ` in the image of `χ`, a positive fraction of the multipliers
    `emMultUnit q n` satisfy `χ(emMultUnit q n) = ζ`.

    Formally: there exist `δ > 0` and `N₀` such that for all `N ≥ N₀`,
    ```
    #{k < N : χ(emMultUnit q k) = ζ} ≥ δ * N
    ```

    **Relationship to PED**: DPED implies PED (via `dped_implies_ped` below) by
    filter monotonicity: {k : χ(m(k)) = ζ} ⊆ {k : χ(m(k)) ≠ 1} when ζ ≠ 1.

    **Open Prop**: proving DPED requires showing not only that escapes occur often,
    but that the distribution of escape values is balanced across all non-identity
    roots — a refined equidistribution property of the EM multiplier sequence. -/
def DistributionalPED : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ζ : ℂˣ) (_hζ : ζ ≠ 1) (_hζ_im : ζ ∈ Set.range χ),
  ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    δ * (N : ℝ) ≤
      ↑((Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂˣ) = ζ)).card

/-- **DPED implies PED**: distributional positive escape density implies positive
    escape density.

    **Proof**: Given DPED, fix a non-trivial χ.  Since χ ≠ 1, there exists a unit
    `u` such that `χ u ≠ 1`; set `ζ = χ u`.  Then `ζ ≠ 1` and `ζ ∈ Set.range χ`.
    Apply DPED to obtain `δ > 0` and `N₀` with
    `#{k < N : χ(m(k)) = ζ} ≥ δN` for all `N ≥ N₀`.
    Since `χ(m(k)) = ζ ≠ 1` implies `χ(m(k)) ≠ 1`, the escape set
    `{k : χ(m(k)) ≠ 1}` contains `{k : χ(m(k)) = ζ}`, so its cardinality is
    at least `δN` by `Finset.card_le_card`. -/
theorem dped_implies_ped : DistributionalPED → PositiveEscapeDensity := by
  intro hdped q inst hq hne χ hχ
  haveI : Fact (Nat.Prime q) := inst
  -- Since χ ≠ 1, pick a unit u with χ u ≠ 1, set ζ = χ u
  obtain ⟨u, hu⟩ : ∃ u : (ZMod q)ˣ, χ u ≠ 1 := by
    by_contra hall
    push_neg at hall
    exact hχ (MonoidHom.ext fun u => Units.ext (by simpa using hall u))
  set ζ := χ u with hζ_def
  have hζ_ne : ζ ≠ 1 := hu
  have hζ_im : ζ ∈ Set.range χ := ⟨u, rfl⟩
  -- Apply DPED to get δ and N₀
  obtain ⟨δ, hδ, N₀, hN₀⟩ := hdped q hq hne χ hχ ζ hζ_ne hζ_im
  refine ⟨δ, hδ, N₀, fun N hN => ?_⟩
  -- The set {k : χ(m(k)) = ζ} ⊆ {k : χ(m(k)) ≠ 1}
  have hsubset : (Finset.range N).filter (fun n => (χ (emMultUnit q hq hne n) : ℂˣ) = ζ) ⊆
      (Finset.range N).filter (fun k => χ (emMultUnit q hq hne k) ≠ 1) := by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2 ▸ hζ_ne⟩
  calc δ * (N : ℝ)
      ≤ ↑((Finset.range N).filter (fun n => (χ (emMultUnit q hq hne n) : ℂˣ) = ζ)).card :=
          hN₀ N hN
    _ ≤ ↑((Finset.range N).filter (fun k => χ (emMultUnit q hq hne k) ≠ 1)).card := by
          exact_mod_cast Finset.card_le_card hsubset

/-- **DPEDImpliesComplexCSB**: distributional positive escape density implies
    the complex character sum bound.

    For a non-trivial character `χ` of order `d`, DPED ensures that the `d − 1`
    non-identity values `ζ₁, …, ζ_{d-1}` each appear with positive density `δⱼ > 0`
    among the multipliers.  This distributional control prevents the walk character
    sum from drifting in any fixed direction in ℂˣ: the rotation contributed by
    escape steps averages to zero (since the `ζⱼ` sum to −1 over all d-th roots).

    **Why this is more tractable than `PEDImpliesComplexCSB`**: PED only says
    escapes are frequent; they could all be in the same direction ζ₀.  DPED rules
    out this worst case.  The block-rotation argument then shows each block of
    consecutive walk values has average ≈ 0 in ℂ, giving the o(N) bound.

    **Open Prop**: formally proving the analytic cancellation from distributional
    data requires a harmonic analysis argument connecting the walk recurrence to
    the distribution of multiplier values — the central open problem of this
    formalization. -/
def DPEDImpliesComplexCSB : Prop := DistributionalPED → ComplexCharSumBound

/-- **DPED → MC** (via DPEDImpliesComplexCSB): given distributional escape density
    and the DPED → CCSB bridge, we obtain Mullin's Conjecture.

    Chain: DPED → (DPEDImpliesComplexCSB) → CCSB → (complex_csb_mc') → MC. -/
theorem dped_mc
    (hdped : DistributionalPED)
    (hdped_csb : DPEDImpliesComplexCSB) :
    MullinConjecture :=
  complex_csb_mc' (hdped_csb hdped)

/-- **DPED → MC** (via PED route): given distributional escape density and
    the PED → CCSB bridge, we obtain Mullin's Conjecture.

    Chain: DPED → (dped_implies_ped) → PED → (PEDImpliesComplexCSB) → CCSB
           → (complex_csb_mc') → MC. -/
theorem dped_mc'
    (hdped : DistributionalPED)
    (hped_csb : PEDImpliesComplexCSB) :
    MullinConjecture :=
  ped_mc' (dped_implies_ped hdped) hped_csb

end DistributionalPED

end PrimeDensityEquipartition

/-! ## §73. Quadratic Walk Sum Decomposition

For an **order-2 character** χ (values ±1), the walk telescope identity
(§37, `walk_telescope_identity`) yields a powerful constraint on escape
positions.

**Key identity**: splitting the telescoping sum
  ∑_{n<N} χ(w(n)) · (χ(m(n)) − 1) = χ(w(N)) − χ(w(0))
into kernel terms (contributing 0) and escape terms (contributing −2·χ(w(n)))
shows that ∑_{escape n} χ(w(n)) = (χ(w(0)) − χ(w(N))) / 2,
hence |∑_{escape n} χ(w(n))| ≤ 1.

This means the walk sum ∑_{n<N} χ(w(n)) decomposes as:
  (kernel-block contribution) + (escape-position contribution with ‖·‖ ≤ 1)

We also define `QuadraticCCSB`, the restriction of `ComplexCharSumBound` to
order-2 characters, which is strictly weaker than full CCSB.
-/

section QuadraticWalkSum

/-- **Escape-telescope identity for order-2 characters**: the telescoping sum
    restricted to escape positions (where χ(m(n)) = −1) satisfies
      −2 · ∑_{escape} χ(w(n)) = χ(w(N)) − χ(w(0)).

    **Proof**: Split the telescope sum by the predicate χ(m(n)) = 1.
    Kernel terms vanish (factor χ(m(n))−1 = 0).  Escape terms have
    χ(m(n))−1 = −2, giving the stated identity. -/
theorem escape_telescope_order2 {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (N : Nat) :
    (-2 : ℂ) * ∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      (χ (emWalkUnit q hq hne n) : ℂ) =
    (χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ) := by
  -- Start from the telescope identity
  have htel := walk_telescope_identity q hq hne χ N
  -- Split the LHS sum by the predicate (χ(m(n)) = 1)
  have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.range N)
    (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1)
    (fun n => (χ (emWalkUnit q hq hne n) : ℂ) *
      ((χ (emMultUnit q hq hne n) : ℂ) - 1))).symm
  rw [hsplit] at htel
  -- Kernel terms: each χ(m(n)) = 1, so χ(m(n)) - 1 = 0, so term = 0
  have hker_zero : ∑ n ∈ (Finset.range N).filter
      (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
    (χ (emWalkUnit q hq hne n) : ℂ) *
      ((χ (emMultUnit q hq hne n) : ℂ) - 1) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_filter] at hn
    rw [hn.2, sub_self, mul_zero]
  rw [hker_zero, zero_add] at htel
  -- Escape terms: for order-2 χ, χ(m(n)) ∈ {1, -1}; filter says ≠ 1, so = -1
  -- Hence χ(m(n)) - 1 = -2, so term = χ(w(n)) * (-2) = -2 * χ(w(n))
  have hesc_terms : ∀ n ∈ (Finset.range N).filter
      (fun n => ¬(χ (emMultUnit q hq hne n) : ℂ) = 1),
    (χ (emWalkUnit q hq hne n) : ℂ) *
      ((χ (emMultUnit q hq hne n) : ℂ) - 1) =
    (-2 : ℂ) * (χ (emWalkUnit q hq hne n) : ℂ) := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    rcases hord2 (emMultUnit q hq hne n) with hm | hm
    · exact absurd hm hn.2
    · rw [hm]; ring
  rw [Finset.sum_congr rfl hesc_terms] at htel
  -- Factor out -2 from the sum
  rw [← Finset.mul_sum] at htel
  -- The filter predicate ¬(... = 1) is the same as (... ≠ 1)
  exact htel

/-- **Escape sum norm bound for order-2 characters**: the sum of walk
    character values at escape positions has norm at most 1.

    **Proof**: From `escape_telescope_order2`,
      2·‖∑_{escape} χ(w(n))‖ = ‖χ(w(N)) − χ(w(0))‖ ≤ 2
    so ‖∑_{escape} χ(w(n))‖ ≤ 1. -/
theorem escape_sum_order2_bounded {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (N : Nat) :
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ 1 := by
  -- From escape_telescope_order2: (-2) * escape_sum = χ(w(N)) - χ(w(0))
  set S := ∑ n ∈ (Finset.range N).filter
    (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
    (χ (emWalkUnit q hq hne n) : ℂ) with hS_def
  have hid := escape_telescope_order2 hq hne χ hord2 N
  -- Take norms: ‖(-2) * S‖ = 2 * ‖S‖
  have hnorm_lhs : ‖(-2 : ℂ) * S‖ = 2 * ‖S‖ := by
    rw [norm_mul, norm_neg, Complex.norm_ofNat]
  -- RHS norm ≤ 2 (triangle inequality + each walk char has norm 1)
  have hnorm_rhs : ‖(χ (emWalkUnit q hq hne N) : ℂ) -
      (χ (emWalkUnit q hq hne 0) : ℂ)‖ ≤ 2 := by
    calc ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖
        ≤ ‖(χ (emWalkUnit q hq hne N) : ℂ)‖ + ‖(χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
          norm_sub_le _ _
      _ = 1 + 1 := by
          rw [walkTelescope_char_norm_one χ _, walkTelescope_char_norm_one χ _]
      _ = 2 := by ring
  -- Combine: 2 * ‖S‖ = ‖(-2) * S‖ = ‖RHS‖ ≤ 2
  rw [hid] at hnorm_lhs
  have h2S : 2 * ‖S‖ ≤ 2 := by linarith
  linarith

/-- **Walk sum splits into kernel-block and escape contributions**: for an
    order-2 character χ, the full walk character sum equals the kernel-only sum
    plus the escape-only sum. This is just Finset.sum_filter_add_sum_filter_not
    specialized to the walk setting. -/
theorem quadratic_walk_sum_split {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
    (∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
      (χ (emWalkUnit q hq hne n) : ℂ)) +
    (∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      (χ (emWalkUnit q hq hne n) : ℂ)) :=
  (Finset.sum_filter_add_sum_filter_not (Finset.range N)
    (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1) _).symm

/-- **Walk sum norm bound from kernel-block sum**: for order-2 χ, the walk
    character sum norm is within 1 of the kernel-block sum norm.  More precisely:
      ‖∑_{n<N} χ(w(n))‖ ≤ ‖∑_{kernel n} χ(w(n))‖ + 1.

    **Proof**: Split the sum, apply triangle inequality, use the escape bound. -/
theorem walk_sum_le_kernel_sum_add_one {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (N : Nat) :
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ + 1 := by
  rw [quadratic_walk_sum_split hq hne χ N]
  calc ‖(∑ n ∈ (Finset.range N).filter
          (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
        (χ (emWalkUnit q hq hne n) : ℂ)) +
        (∑ n ∈ (Finset.range N).filter
          (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
        (χ (emWalkUnit q hq hne n) : ℂ))‖
      ≤ ‖∑ n ∈ (Finset.range N).filter
          (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
        (χ (emWalkUnit q hq hne n) : ℂ)‖ +
        ‖∑ n ∈ (Finset.range N).filter
          (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
        (χ (emWalkUnit q hq hne n) : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖∑ n ∈ (Finset.range N).filter
          (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
        (χ (emWalkUnit q hq hne n) : ℂ)‖ + 1 := by
        linarith [escape_sum_order2_bounded hq hne χ hord2 N]

/-- **QuadraticCCSB**: `ComplexCharSumBound` restricted to order-2 characters.
    This is strictly weaker than full CCSB since it only handles characters
    with values in {+1, −1} (i.e., Jacobi/Legendre symbols). -/
def QuadraticCCSB : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (_hord2 : IsOrder2 χ),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- **CCSB implies QuadraticCCSB**: the full complex character sum bound
    implies the restriction to order-2 characters (trivial specialization). -/
theorem ccsb_implies_quadratic_ccsb (hccsb : ComplexCharSumBound) :
    QuadraticCCSB := by
  intro q _ hq hne χ hχ _hord2 ε hε
  exact hccsb q hq hne χ hχ ε hε

/-- **Reverse triangle for kernel sum**: the kernel-block sum norm is within 1
    of the full walk sum norm (reverse direction of `walk_sum_le_kernel_sum_add_one`).
    Specifically: ‖∑_{kernel} χ(w(n))‖ ≤ ‖∑_{all} χ(w(n))‖ + 1. -/
theorem kernel_sum_le_walk_sum_add_one {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (N : Nat) :
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ + 1 := by
  set kerSum := ∑ n ∈ (Finset.range N).filter
      (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
    (χ (emWalkUnit q hq hne n) : ℂ)
  set escSum := ∑ n ∈ (Finset.range N).filter
      (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
    (χ (emWalkUnit q hq hne n) : ℂ)
  have hsplit : ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
      kerSum + escSum := quadratic_walk_sum_split hq hne χ N
  have hesc := escape_sum_order2_bounded hq hne χ hord2 N
  -- kerSum = total - escSum, so ‖kerSum‖ ≤ ‖total‖ + ‖escSum‖ ≤ ‖total‖ + 1
  have hker_eq : kerSum = (∑ n ∈ Finset.range N,
      (χ (emWalkUnit q hq hne n) : ℂ)) - escSum := by
    rw [hsplit]; ring
  calc ‖kerSum‖ = ‖(∑ n ∈ Finset.range N,
          (χ (emWalkUnit q hq hne n) : ℂ)) - escSum‖ := by rw [hker_eq]
    _ ≤ ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ +
        ‖escSum‖ := norm_sub_le _ _
    _ ≤ ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ + 1 := by
        linarith

/-- **QuadraticCCSB equivalent to kernel-block CCSB**: for order-2 characters,
    the walk sum is o(N) iff the kernel-block sum is o(N), since they differ
    by at most 1 (the escape contribution). -/
theorem quadratic_ccsb_iff_kernel_ccsb :
    QuadraticCCSB ↔
    (∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
     ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (_hord2 : IsOrder2 χ),
     ∀ (ε : ℝ) (_hε : 0 < ε),
     ∃ N₀ : ℕ, ∀ N ≥ N₀,
       ‖∑ n ∈ (Finset.range N).filter
           (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
         (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * N) := by
  constructor
  · -- Forward: QuadraticCCSB → kernel-block CCSB
    intro hqccsb q _ hq hne χ hχ hord2 ε hε
    -- Use ε/2 for the walk sum, then add 1
    obtain ⟨N₁, hN₁⟩ := hqccsb q hq hne χ hχ hord2 (ε / 2) (by linarith)
    -- Choose N₀ large enough that 1 ≤ (ε/2) * N₀
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / ε)
    refine ⟨max N₁ N₂, fun N hN => ?_⟩
    have hN₁_le : N₁ ≤ N := (le_max_left N₁ N₂).trans hN
    have hN₂_le : N₂ ≤ N := (le_max_right N₁ N₂).trans hN
    calc ‖∑ n ∈ (Finset.range N).filter
            (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
          (χ (emWalkUnit q hq hne n) : ℂ)‖
        ≤ ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ + 1 :=
          kernel_sum_le_walk_sum_add_one hq hne χ hord2 N
      _ ≤ ε / 2 * N + 1 := by linarith [hN₁ N hN₁_le]
      _ ≤ ε / 2 * N + ε / 2 * N := by
          have : 1 ≤ ε / 2 * N := by
            have hN₂_le_r : (N₂ : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN₂_le
            have : 2 / ε < (N : ℝ) := lt_of_lt_of_le hN₂ hN₂_le_r
            rw [div_lt_iff₀ hε] at this
            linarith
          linarith
      _ = ε * N := by ring
  · -- Backward: kernel-block CCSB → QuadraticCCSB
    intro hkccsb q _ hq hne χ hχ hord2 ε hε
    obtain ⟨N₁, hN₁⟩ := hkccsb q hq hne χ hχ hord2 (ε / 2) (by linarith)
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / ε)
    refine ⟨max N₁ N₂, fun N hN => ?_⟩
    have hN₁_le : N₁ ≤ N := (le_max_left N₁ N₂).trans hN
    have hN₂_le : N₂ ≤ N := (le_max_right N₁ N₂).trans hN
    calc ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖
        ≤ ‖∑ n ∈ (Finset.range N).filter
            (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
          (χ (emWalkUnit q hq hne n) : ℂ)‖ + 1 :=
          walk_sum_le_kernel_sum_add_one hq hne χ hord2 N
      _ ≤ ε / 2 * N + 1 := by linarith [hN₁ N hN₁_le]
      _ ≤ ε / 2 * N + ε / 2 * N := by
          have : 1 ≤ ε / 2 * N := by
            have hN₂_le_r : (N₂ : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN₂_le
            have : 2 / ε < (N : ℝ) := lt_of_lt_of_le hN₂ hN₂_le_r
            rw [div_lt_iff₀ hε] at this
            linarith
          linarith
      _ = ε * N := by ring

end QuadraticWalkSum

/-! ## §74. Escape Decorrelation Hypothesis

For order-2 characters, the Van der Corput inequality (VdC, proved in §69 of
`LargeSieveAnalytic.lean`) reduces `QuadraticCCSB` to bounding h-point
correlations of the multiplier character sequence.

Specifically, the walk autocorrelation at lag h equals:
  R_h(n) = χ(w(n+h)) · χ(w(n)) = ∏_{j<h} χ(m(n+j))
using the multi-step recurrence and the order-2 identity χ(w(n))² = 1.

We define `EscapeDecorrelation` as the hypothesis that the h-fold multiplier
character products have partial sums o(N) for every h ≥ 1.  Combined with VdC,
this yields `QuadraticCCSB`.

**Key results**:
1. `local_char_walk_multi_step`: χ(w(n+h)) = χ(w(n)) · ∏_{j<h} χ(m(n+j)) (local copy of §53 result)
2. `quadratic_autocorrelation_eq_mult_product`: χ(w(n+h))·χ(w(n)) = ∏_{j<h} χ(m(n+j)) for order-2 χ
3. `EscapeDecorrelation`: open Prop — h-fold multiplier products have sums o(N)
4. `escape_dec_h1_specializes`: h=1 case simplifies to single multiplier char sum
5. `escape_dec_implies_quadratic_ccsb`: EscapeDecorrelation → QuadraticCCSB (with VdC hypothesis)
-/

section EscapeDecorrelation

/-- **Multi-step walk recurrence (local)**: χ(w(n+h)) = χ(w(n)) · ∏_{j<h} χ(m(n+j)).
    This is a local copy of `char_walk_multi_step` from LargeSieveHarmonic.lean §53,
    proved here to avoid cross-file import dependencies. -/
theorem local_char_walk_multi_step (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (n h : Nat) :
    (χ (emWalkUnit q hq hne (n + h)) : ℂ) =
    (χ (emWalkUnit q hq hne n) : ℂ) *
    ∏ j ∈ Finset.range h, (χ (emMultUnit q hq hne (n + j)) : ℂ) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show n + (h + 1) = (n + h) + 1 from by omega]
    rw [char_walk_recurrence q hq hne χ (n + h)]
    rw [ih]
    rw [Finset.prod_range_succ]
    ring

/-- **Quadratic autocorrelation equals multiplier product**: for an order-2
    character χ, the product χ(w(n+h)) · χ(w(n)) equals ∏_{j<h} χ(m(n+j)).

    **Proof**: By `local_char_walk_multi_step`,
      χ(w(n+h)) = χ(w(n)) · ∏_{j<h} χ(m(n+j)).
    Multiplying both sides by χ(w(n)) and using χ(w(n))² = 1 (from `order2_sq_eq_one`)
    gives: χ(w(n+h)) · χ(w(n)) = χ(w(n))² · ∏ = 1 · ∏ = ∏. -/
theorem quadratic_autocorrelation_eq_mult_product
    {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q)
    (hne : ∀ k, seq k ≠ q) (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ)
    (n h : Nat) :
    (χ (emWalkUnit q hq hne (n + h)) : ℂ) * (χ (emWalkUnit q hq hne n) : ℂ) =
    ∏ j ∈ Finset.range h, (χ (emMultUnit q hq hne (n + j)) : ℂ) := by
  rw [local_char_walk_multi_step q hq hne χ n h]
  -- LHS = (χ(w(n)) * ∏) * χ(w(n)) = χ(w(n))² * ∏
  have hsq : (χ (emWalkUnit q hq hne n) : ℂ) ^ 2 = 1 :=
    order2_sq_eq_one χ hord2 (emWalkUnit q hq hne n)
  -- χ(w(n))² = 1, so factor it out
  have : (χ (emWalkUnit q hq hne n) : ℂ) *
      (∏ j ∈ Finset.range h, (χ (emMultUnit q hq hne (n + j)) : ℂ)) *
      (χ (emWalkUnit q hq hne n) : ℂ) =
      (χ (emWalkUnit q hq hne n) : ℂ) ^ 2 *
      (∏ j ∈ Finset.range h, (χ (emMultUnit q hq hne (n + j)) : ℂ)) := by ring
  rw [this, hsq, one_mul]

/-- **EscapeDecorrelation**: for every h ≥ 1, the h-fold product of consecutive
    multiplier character values has partial sums o(N).  For order-2 characters,
    this is equivalent to saying the walk autocorrelation R_h = o(N) for all h,
    via `quadratic_autocorrelation_eq_mult_product`.

    Combined with the Van der Corput inequality (§69, `vanDerCorputBound`),
    this implies `QuadraticCCSB`.

    This is weaker than `HigherOrderDecorrelation` (§69) which applies to all
    characters, not just order-2 ones.  For order-2 characters, however,
    the two are equivalent. -/
def EscapeDecorrelation : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (_hord2 : IsOrder2 χ),
  ∀ (h : ℕ) (_hh : 0 < h),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N,
      ∏ j ∈ Finset.range h, (χ (emMultUnit q hq hne (n + j)) : ℂ)‖ ≤ ε * N

/-- **h=1 specialization**: `EscapeDecorrelation` at h=1 gives
    ‖∑_{n<N} χ(m(n))‖ ≤ ε·N, the multiplier character sum bound.

    **Proof**: `∏ j ∈ Finset.range 1, χ(m(n+j)) = χ(m(n+0)) = χ(m(n))`. -/
theorem escape_dec_h1_specializes (hed : EscapeDecorrelation)
    (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) (hord2 : IsOrder2 χ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ Finset.range N, (χ (emMultUnit q hq hne n) : ℂ)‖ ≤ ε * N := by
  obtain ⟨N₀, hN₀⟩ := hed q hq hne χ hχ hord2 1 one_pos ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : ∀ n, ∏ j ∈ Finset.range 1, (χ (emMultUnit q hq hne (n + j)) : ℂ) =
      (χ (emMultUnit q hq hne n) : ℂ) := by
    intro n
    simp
  simp_rw [h1] at hN₀
  exact hN₀ N hN

/-- **Walk autocorrelation sum from EscapeDecorrelation**: for order-2 χ,
    `EscapeDecorrelation` at lag h implies the walk autocorrelation sum
    ∑_{n<N} χ(w(n+h))·χ(w(n)) = o(N).

    **Proof**: By `quadratic_autocorrelation_eq_mult_product`,
    χ(w(n+h))·χ(w(n)) = ∏_{j<h} χ(m(n+j)).  The result follows directly. -/
theorem escape_dec_implies_walk_autocorr_bound (hed : EscapeDecorrelation)
    (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) (hord2 : IsOrder2 χ)
    (h : ℕ) (hh : 0 < h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ Finset.range N,
        ((χ (emWalkUnit q hq hne (n + h)) : ℂ) *
         (χ (emWalkUnit q hq hne n) : ℂ))‖ ≤ ε * N := by
  obtain ⟨N₀, hN₀⟩ := hed q hq hne χ hχ hord2 h hh ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have hcongr : ∀ n ∈ Finset.range N,
      (χ (emWalkUnit q hq hne (n + h)) : ℂ) * (χ (emWalkUnit q hq hne n) : ℂ) =
      ∏ j ∈ Finset.range h, (χ (emMultUnit q hq hne (n + j)) : ℂ) :=
    fun n _ => quadratic_autocorrelation_eq_mult_product hq hne χ hord2 n h
  rw [Finset.sum_congr rfl hcongr]
  exact hN₀ N hN

/-- **EscapeDecorrelation implies QuadraticCCSB via VdC**: given a Van der Corput
    type bound (stated as a local hypothesis to avoid cross-file imports) and
    `EscapeDecorrelation`, we obtain `QuadraticCCSB`.

    The VdC hypothesis states: for all ε > 0, if every autocorrelation R_h is
    bounded by ε·N (for 1 ≤ h ≤ H) and H is large enough, then |S_N|² ≤ C·ε·N²
    for large N.

    This is the content of `vanDerCorputBound` (§69, `LargeSieveAnalytic.lean`),
    specialized to order-2 characters where the autocorrelation equals the
    multiplier product sum.

    The VdC hypothesis is parameterized as:
      For all (q, χ) order-2, ε > 0:
      if ∀ h ∈ [1,H], ‖R_h(N)‖ ≤ ε·N for large N, then ‖S_N‖ ≤ C(ε,H)·N for large N,
      where C(ε,H) → 0 as H → ∞ with ε → 0 appropriately. -/
theorem escape_dec_implies_quadratic_ccsb
    (hvdc : ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
      (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (_hord2 : IsOrder2 χ),
      ∀ (δ : ℝ) (_hδ : 0 < δ),
      ∃ H₀ : ℕ, ∀ H ≥ H₀,
        (∀ (h : ℕ), 1 ≤ h → h ≤ H →
         ∃ N₀ : ℕ, ∀ N ≥ N₀,
           ‖∑ n ∈ Finset.range N,
             ((χ (emWalkUnit q hq hne (n + h)) : ℂ) *
              (χ (emWalkUnit q hq hne n) : ℂ))‖ ≤ δ * N) →
        ∃ N₁ : ℕ, ∀ N ≥ N₁,
          ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ δ * N)
    (hed : EscapeDecorrelation) : QuadraticCCSB := by
  intro q _ hq hne χ hχ hord2 ε hε
  -- Use VdC with δ = ε
  obtain ⟨H₀, hH₀⟩ := hvdc q hq hne χ hχ hord2 ε hε
  -- Take H = max H₀ 1 (ensuring H ≥ H₀ and H ≥ 1)
  set H := max H₀ 1 with hH_def
  have hH_ge : H ≥ H₀ := le_max_left H₀ 1
  -- Apply VdC at this H
  apply hH₀ H hH_ge
  -- Need: for all 1 ≤ h ≤ H, the walk autocorrelation is ≤ ε·N
  intro h hh1 _hhH
  -- EscapeDecorrelation at lag h gives multiplier product bound,
  -- which equals walk autocorrelation by quadratic_autocorrelation_eq_mult_product
  exact escape_dec_implies_walk_autocorr_bound hed q hq hne χ hχ hord2 h hh1 ε hε

/-- **EscapeDecorrelation implies QuadraticCCSB implies MC**: the chain from
    escape decorrelation through quadratic CCSB to Mullin's Conjecture,
    assuming the VdC bridge and CCSB → MC pathway.

    Chain: EscapeDecorrelation →[VdC]→ QuadraticCCSB → CCSB → MC
    (The last step CCSB → MC is via `complex_csb_mc'` from §34, but QuadraticCCSB
    is weaker than full CCSB. For the MC implication we need CCSB for ALL characters
    not just order-2 ones. Thus the full MC chain requires additional hypotheses
    for characters of order ≥ 3.) -/
theorem escape_dec_quadratic_ccsb_chain
    (hvdc : ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
      (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1) (_hord2 : IsOrder2 χ),
      ∀ (δ : ℝ) (_hδ : 0 < δ),
      ∃ H₀ : ℕ, ∀ H ≥ H₀,
        (∀ (h : ℕ), 1 ≤ h → h ≤ H →
         ∃ N₀ : ℕ, ∀ N ≥ N₀,
           ‖∑ n ∈ Finset.range N,
             ((χ (emWalkUnit q hq hne (n + h)) : ℂ) *
              (χ (emWalkUnit q hq hne n) : ℂ))‖ ≤ δ * N) →
        ∃ N₁ : ℕ, ∀ N ≥ N₁,
          ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ δ * N)
    (hed : EscapeDecorrelation) : QuadraticCCSB :=
  escape_dec_implies_quadratic_ccsb hvdc hed

end EscapeDecorrelation

/-! ## §76. General Walk Sum Decomposition

This section extends the order-2 results of §73 to characters of arbitrary order.

**Key insight**: For ANY non-trivial character χ, the telescope identity
(§37) splits cleanly into kernel terms (= 0) and escape terms.  The
*weighted* escape sum `∑_{esc} χ(w(n))·(χ(m(n))−1)` has norm ≤ 2
regardless of the character order.

**What does NOT generalize**: For order-2 characters, all escape
rotations equal −1, so χ(m(n))−1 = −2 is constant, and one can divide
by −2 to bound the *unweighted* escape sum `∑_{esc} χ(w(n))` by 1.
For characters of order d ≥ 3, the escape rotations χ(m(n))−1 vary
among d−1 different non-zero values.  The unweighted escape sum
`∑_{esc} χ(w(n))` is therefore NOT bounded by O(1) in general:
adversarial phase alignment among d−1 rotations can cause constructive
interference making the escape sum Θ(N).

Consequently, for d ≥ 3, CCSB does NOT reduce to controlling the
kernel-block sum alone (unlike the d = 2 case proved in §73).

**Results proved here**:
1. `escape_telescope_general` — weighted escape sum = χ(w(N))−χ(w(0)) for all χ
2. `escape_char_val_sub_one_norm_pos` — pointwise: χ(u) ≠ 1 → ‖χ(u)−1‖ > 0
3. `escape_min_dist_pos` — finite minimum distance for nontrivial character
4. `general_walk_sum_le_kernel_sum_add_escape_sum` — ‖S_N‖ ≤ ‖S_ker‖+‖S_esc‖
5. `general_kernel_sum_le_walk_sum_add_escape_sum` — ‖S_ker‖ ≤ ‖S_N‖+‖S_esc‖
-/

section GeneralWalkSumDecomposition

/-- **General escape telescope**: for any character χ (not necessarily order 2),
    the telescope identity restricted to escape steps gives
      ∑_{esc} χ(w(n)) · (χ(m(n)) − 1) = χ(w(N)) − χ(w(0)).

    Kernel terms (χ(m(n)) = 1) contribute zero to the telescope sum,
    so only escape terms remain. -/
theorem escape_telescope_general {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      ((χ (emWalkUnit q hq hne n) : ℂ) * ((χ (emMultUnit q hq hne n) : ℂ) - 1)) =
    (χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ) := by
  have htel := walk_telescope_identity q hq hne χ N
  -- Split the LHS sum by the predicate (χ(m(n)) = 1)
  have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.range N)
    (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1)
    (fun n => (χ (emWalkUnit q hq hne n) : ℂ) *
      ((χ (emMultUnit q hq hne n) : ℂ) - 1))).symm
  rw [hsplit] at htel
  -- Kernel terms vanish: χ(m(n)) = 1 implies χ(m(n)) - 1 = 0
  have hker_zero : ∑ n ∈ (Finset.range N).filter
      (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
    (χ (emWalkUnit q hq hne n) : ℂ) *
      ((χ (emMultUnit q hq hne n) : ℂ) - 1) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [Finset.mem_filter] at hn
    rw [hn.2, sub_self, mul_zero]
  rw [hker_zero, zero_add] at htel
  exact htel

/-- **General weighted escape norm bound**: the weighted escape sum has
    norm at most 2, for any character. This is an immediate corollary of
    `escape_telescope_general` and the triangle inequality. -/
theorem escape_telescope_general_norm_bound {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      ((χ (emWalkUnit q hq hne n) : ℂ) * ((χ (emMultUnit q hq hne n) : ℂ) - 1))‖ ≤ 2 := by
  rw [escape_telescope_general hq hne χ N]
  calc ‖(χ (emWalkUnit q hq hne N) : ℂ) - (χ (emWalkUnit q hq hne 0) : ℂ)‖
      ≤ ‖(χ (emWalkUnit q hq hne N) : ℂ)‖ + ‖(χ (emWalkUnit q hq hne 0) : ℂ)‖ :=
        norm_sub_le _ _
    _ = 1 + 1 := by
        rw [walkTelescope_char_norm_one χ _, walkTelescope_char_norm_one χ _]
    _ = 2 := by ring

/-- **Pointwise escape distance**: if a character value is not 1, then
    ‖χ(u) − 1‖ > 0.  Immediate from the fact that χ(u) ≠ 1 makes
    χ(u) − 1 nonzero. -/
theorem escape_char_val_sub_one_norm_pos {q : Nat} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (u : (ZMod q)ˣ)
    (hne : (χ u : ℂ) ≠ 1) :
    0 < ‖(χ u : ℂ) - 1‖ :=
  norm_pos_iff.mpr (sub_ne_zero.mpr hne)

/-- **Minimum escape distance**: for a non-trivial character χ, there
    exists a positive constant δ such that ‖χ(u) − 1‖ ≥ δ for every u
    with χ(u) ≠ 1.  The character image is finite (since the domain is
    finite), so the minimum over the non-empty set of non-identity
    character values is achieved and positive. -/
theorem escape_min_dist_pos {q : Nat} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : (ZMod q)ˣ, (χ u : ℂ) ≠ 1 → δ ≤ ‖(χ u : ℂ) - 1‖ := by
  -- Since χ ≠ 1, there exists some unit u₀ with χ(u₀) ≠ 1
  have hne_exists : ∃ u₀ : (ZMod q)ˣ, (χ u₀ : ℂ) ≠ 1 := by
    by_contra hall
    push_neg at hall
    apply hχ
    ext u
    specialize hall u
    -- χ u = 1 as ℂˣ iff (χ u : ℂ) = (1 : ℂ)
    have : χ u = 1 := Units.val_injective (by simp [Units.val_one, hall])
    simp [this]
  -- Consider the set of distances {‖χ(u) - 1‖ : u ∈ univ, χ(u) ≠ 1}
  set S := Finset.univ.filter (fun u : (ZMod q)ˣ => (χ u : ℂ) ≠ 1) with hS_def
  have hS_nonempty : S.Nonempty := by
    obtain ⟨u₀, hu₀⟩ := hne_exists
    exact ⟨u₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₀⟩⟩
  -- The image set of distances
  set T := S.image (fun u => ‖(χ u : ℂ) - 1‖) with hT_def
  have hT_nonempty : T.Nonempty := hS_nonempty.image _
  -- All elements of T are positive (each χ(u) ≠ 1 means ‖χ(u)-1‖ > 0)
  have hT_pos : ∀ t ∈ T, 0 < t := by
    intro t ht
    rw [hT_def, Finset.mem_image] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact escape_char_val_sub_one_norm_pos χ u
      ((Finset.mem_filter.mp hu).2)
  -- Take δ = min of T
  set δ := T.min' hT_nonempty with hδ_def
  refine ⟨δ, ?_, ?_⟩
  · -- δ > 0: δ is the minimum of a finite set of positive reals
    exact hT_pos δ (Finset.min'_mem T hT_nonempty)
  · -- ∀ u, χ(u) ≠ 1 → δ ≤ ‖χ(u) - 1‖
    intro u hu
    apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩

/-- **General walk sum triangle bound**: for any character (not just order 2),
    the full walk sum norm is bounded by the kernel-block sum norm plus the
    escape sum norm.  This is simply the triangle inequality applied to
    the kernel-escape decomposition `quadratic_walk_sum_split`.

    (The name `quadratic_walk_sum_split` is historical — it does not
    require IsOrder2.) -/
theorem general_walk_sum_le_kernel_sum_add_escape_sum {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ +
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ := by
  rw [quadratic_walk_sum_split hq hne χ N]
  exact norm_add_le _ _

/-- **General kernel sum triangle bound**: the kernel-block sum norm is
    bounded by the full walk sum norm plus the escape sum norm.
    Reverse direction of `general_walk_sum_le_kernel_sum_add_escape_sum`.
    No IsOrder2 hypothesis needed. -/
theorem general_kernel_sum_le_walk_sum_add_escape_sum {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (N : Nat) :
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ +
    ‖∑ n ∈ (Finset.range N).filter
        (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
      (χ (emWalkUnit q hq hne n) : ℂ)‖ := by
  set kerSum := ∑ n ∈ (Finset.range N).filter
      (fun n => (χ (emMultUnit q hq hne n) : ℂ) = 1),
    (χ (emWalkUnit q hq hne n) : ℂ)
  set escSum := ∑ n ∈ (Finset.range N).filter
      (fun n => (χ (emMultUnit q hq hne n) : ℂ) ≠ 1),
    (χ (emWalkUnit q hq hne n) : ℂ)
  have hsplit : ∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ) =
      kerSum + escSum := quadratic_walk_sum_split hq hne χ N
  have hker_eq : kerSum = (∑ n ∈ Finset.range N,
      (χ (emWalkUnit q hq hne n) : ℂ)) - escSum := by
    rw [hsplit]; ring
  calc ‖kerSum‖
      = ‖(∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)) - escSum‖ := by
        rw [hker_eq]
    _ ≤ ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ + ‖escSum‖ :=
        norm_sub_le _ _

end GeneralWalkSumDecomposition

/-! ## §77. Quadratic Block Alternation Structure

This section documents structural properties of the d=2 (order-2 character)
walk that are unique to the quadratic case.

**Key insight unique to d=2**: For order-2 characters, the walk character
χ(w(n)) takes values in {+1, −1}, and every escape step negates this value.
Between consecutive escapes, the walk character is constant.  The kernel-block
sum `∑_{ker} χ(w(n))` is therefore a pure alternating series of block lengths:

  s · (L₁ − L₂ + L₃ − ⋯)

where s ∈ {+1, −1} is the initial sign and Lₖ is the length of the k-th
kernel block.  CCSB for order-2 characters is thus equivalent to this
alternating block-length sum being o(N) — a much more concrete condition
than the general CCSB.

For d ≥ 3, escape rotations are NOT all the same, so no analogous
alternation structure exists (see §76 discussion).

**Results proved here**:
1. `order2_not_one_eq_neg_one` — for d=2, χ(u) ≠ 1 implies χ(u) = −1
2. `kernel_opposite_after_escape` — kernel step then escape flips walk char
3. `kernel_block_walk_char_constant` — consecutive kernel steps preserve walk char
4. `quadratic_kernel_sum_on_block` — kernel block sum = block_length · χ(w(start))
-/

section QuadraticBlockAlternation

/-- For an order-2 character, if a character value is not 1 then it must be −1.
    This is the dichotomy from `IsOrder2` with the first branch excluded. -/
theorem order2_not_one_eq_neg_one {q : Nat} [Fact (Nat.Prime q)]
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (u : (ZMod q)ˣ)
    (hne : (χ u : ℂ) ≠ 1) :
    (χ u : ℂ) = -1 := by
  rcases hord2 u with h | h
  · exact absurd h hne
  · exact h

/-- **Kernel-then-escape flips walk character**: if step n is a kernel step
    (χ(m(n)) = 1) and step n+1 is an escape (χ(m(n+1)) ≠ 1), then for an
    order-2 character, χ(w(n+2)) = −χ(w(n)).

    **Proof**: By `char_walk_recurrence`, χ(w(n+1)) = χ(w(n)) · χ(m(n)) = χ(w(n)) · 1
    and χ(w(n+2)) = χ(w(n+1)) · χ(m(n+1)) = χ(w(n)) · (−1) = −χ(w(n)). -/
theorem kernel_opposite_after_escape {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (n : Nat)
    (hker_n : (χ (emMultUnit q hq hne n) : ℂ) = 1)
    (hesc : (χ (emMultUnit q hq hne (n + 1)) : ℂ) ≠ 1) :
    (χ (emWalkUnit q hq hne (n + 2)) : ℂ) =
      -(χ (emWalkUnit q hq hne n) : ℂ) := by
  -- Step 1: χ(w(n+1)) = χ(w(n)) · χ(m(n)) = χ(w(n)) · 1 = χ(w(n))
  have h1 : (χ (emWalkUnit q hq hne (n + 1)) : ℂ) =
      (χ (emWalkUnit q hq hne n) : ℂ) := by
    rw [char_walk_recurrence q hq hne χ n, hker_n, mul_one]
  -- Step 2: χ(m(n+1)) = -1 since it's an escape for order-2
  have h2 : (χ (emMultUnit q hq hne (n + 1)) : ℂ) = -1 :=
    order2_not_one_eq_neg_one χ hord2 _ hesc
  -- Step 3: χ(w(n+2)) = χ(w(n+1)) · χ(m(n+1)) = χ(w(n)) · (-1) = -χ(w(n))
  rw [char_walk_recurrence q hq hne χ (n + 1), h1, h2, mul_neg_one]

/-- **Consecutive kernel steps preserve walk character**: if steps n, n+1, ..., n+k-1
    are all kernel steps (χ(m(n+j)) = 1 for j < k), then χ(w(n+k)) = χ(w(n)).

    This is an induction on `kernel_preserves_walk_char`. -/
theorem kernel_block_walk_char_constant {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (n k : Nat)
    (hker : ∀ j, j < k → (χ (emMultUnit q hq hne (n + j)) : ℂ) = 1) :
    (χ (emWalkUnit q hq hne (n + k)) : ℂ) =
      (χ (emWalkUnit q hq hne n) : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hker_prev : ∀ j, j < k → (χ (emMultUnit q hq hne (n + j)) : ℂ) = 1 :=
      fun j hj => hker j (Nat.lt_succ_of_lt hj)
    rw [show n + (k + 1) = (n + k) + 1 from by omega]
    rw [char_walk_recurrence q hq hne χ (n + k)]
    rw [hker k (Nat.lt_succ_iff.mpr le_rfl), mul_one]
    exact ih hker_prev

/-- **Kernel block sum formula**: on a block of L consecutive kernel steps
    starting at index n, the sum of walk character values equals L times
    the walk character value at the start of the block.

    This is the quantitative consequence of `kernel_block_walk_char_constant`:
    since all walk character values in the block are equal, the sum is just
    the common value times the block length. -/
theorem quadratic_kernel_sum_on_block {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (n L : Nat)
    (hker : ∀ j, j < L → (χ (emMultUnit q hq hne (n + j)) : ℂ) = 1) :
    ∑ j ∈ Finset.range L, (χ (emWalkUnit q hq hne (n + j)) : ℂ) =
      L * (χ (emWalkUnit q hq hne n) : ℂ) := by
  have hcongr : ∀ j ∈ Finset.range L, (χ (emWalkUnit q hq hne (n + j)) : ℂ) =
      (χ (emWalkUnit q hq hne n) : ℂ) := by
    intro j hj
    exact kernel_block_walk_char_constant hq hne χ n j
      (fun i hi => hker i (Nat.lt_trans hi (Finset.mem_range.mp hj)))
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_comm]

end QuadraticBlockAlternation

/-! ## §78. Escape Alternation Structure

For order-2 characters, escapes from the kernel alternate the walk character
value between +1 and −1. This section formalizes:

1. `escape_values_alternate` — if e₁ is an escape position and all steps
   between e₁ and e₂ are kernel steps, then χ(w(e₂)) = −χ(w(e₁)).
2. `kernel_sum_between_escapes` — the kernel-block sum between consecutive
   escapes e₁, e₂ equals (e₂ − e₁ − 1) · (−χ(w(e₁))).
-/

section EscapeAlternation

/-- **Escape alternation for order-2 characters**: if position e₁ is an escape
    (χ(m(e₁)) ≠ 1) and all positions strictly between e₁ and e₂ are kernel
    steps (χ(m(j)) = 1), then the walk character flips:
    χ(w(e₂)) = −χ(w(e₁)).

    Proof: The escape at e₁ gives χ(w(e₁+1)) = χ(w(e₁))·χ(m(e₁)) = −χ(w(e₁))
    (by `char_walk_recurrence` + `order2_not_one_eq_neg_one`). Then the
    kernel steps from e₁+1 to e₂ preserve the walk character
    (by `kernel_block_walk_char_constant`). -/
theorem escape_values_alternate {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (e₁ e₂ : Nat)
    (hlt : e₁ < e₂)
    (hesc₁ : (χ (emMultUnit q hq hne e₁) : ℂ) ≠ 1)
    (hker_between : ∀ j, e₁ < j → j < e₂ →
      (χ (emMultUnit q hq hne j) : ℂ) = 1) :
    (χ (emWalkUnit q hq hne e₂) : ℂ) =
      -(χ (emWalkUnit q hq hne e₁) : ℂ) := by
  -- Write e₂ = (e₁ + 1) + (e₂ - e₁ - 1)
  have hle : e₁ + 1 ≤ e₂ := hlt
  set k := e₂ - (e₁ + 1) with hk_def
  have he₂_eq : e₂ = e₁ + 1 + k := by omega
  -- Step 1: escape at e₁ flips walk char
  have hm_neg : (χ (emMultUnit q hq hne e₁) : ℂ) = -1 :=
    order2_not_one_eq_neg_one χ hord2 _ hesc₁
  have hflip : (χ (emWalkUnit q hq hne (e₁ + 1)) : ℂ) =
      -(χ (emWalkUnit q hq hne e₁) : ℂ) :=
    escape_flips_walk_char hq hne χ e₁ hm_neg
  -- Step 2: kernel steps from e₁+1 to e₂ preserve walk char
  have hker_block : ∀ j, j < k →
      (χ (emMultUnit q hq hne (e₁ + 1 + j)) : ℂ) = 1 := by
    intro j hj
    apply hker_between (e₁ + 1 + j)
    · omega
    · omega
  have hconst : (χ (emWalkUnit q hq hne (e₁ + 1 + k)) : ℂ) =
      (χ (emWalkUnit q hq hne (e₁ + 1)) : ℂ) :=
    kernel_block_walk_char_constant hq hne χ (e₁ + 1) k hker_block
  -- Combine
  rw [he₂_eq, hconst, hflip]

/-- **Kernel-block sum between consecutive escapes**: if e₁ is an escape
    position and all steps from e₁+1 to e₂−1 are kernel steps, then the
    sum of walk character values over these kernel positions equals
    (e₂ − e₁ − 1) · (−χ(w(e₁))).

    The kernel block starts at e₁+1 (after the escape flips the walk char
    to −χ(w(e₁))) and runs for e₂−e₁−1 steps. By
    `quadratic_kernel_sum_on_block`, the sum is the block length times the
    common walk char value, which is −χ(w(e₁)). -/
theorem kernel_sum_between_escapes {q : Nat} [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (χ : (ZMod q)ˣ →* ℂˣ) (hord2 : IsOrder2 χ) (e₁ e₂ : Nat)
    (hlt : e₁ + 1 < e₂)
    (hesc₁ : (χ (emMultUnit q hq hne e₁) : ℂ) ≠ 1)
    (hker : ∀ j, e₁ < j → j < e₂ →
      (χ (emMultUnit q hq hne j) : ℂ) = 1) :
    ∑ j ∈ Finset.range (e₂ - e₁ - 1),
      (χ (emWalkUnit q hq hne (e₁ + 1 + j)) : ℂ) =
    (e₂ - e₁ - 1 : ℕ) * (-(χ (emWalkUnit q hq hne e₁) : ℂ)) := by
  -- The kernel block starts at e₁+1 with length L = e₂ - e₁ - 1
  set L := e₂ - e₁ - 1 with hL_def
  -- All steps in [e₁+1, e₁+1+L) are kernel steps
  have hker_block : ∀ j, j < L →
      (χ (emMultUnit q hq hne (e₁ + 1 + j)) : ℂ) = 1 := by
    intro j hj
    apply hker (e₁ + 1 + j)
    · omega
    · omega
  -- Apply quadratic_kernel_sum_on_block to get sum = L · χ(w(e₁+1))
  have hblock := quadratic_kernel_sum_on_block hq hne χ (e₁ + 1) L hker_block
  rw [hblock]
  -- Now show χ(w(e₁+1)) = -χ(w(e₁))
  have hm_neg : (χ (emMultUnit q hq hne e₁) : ℂ) = -1 :=
    order2_not_one_eq_neg_one χ hord2 _ hesc₁
  have hflip : (χ (emWalkUnit q hq hne (e₁ + 1)) : ℂ) =
      -(χ (emWalkUnit q hq hne e₁) : ℂ) :=
    escape_flips_walk_char hq hne χ e₁ hm_neg
  rw [hflip]

end EscapeAlternation

/-! ## §39. Coprimality Refreshing and Death Rate Infrastructure

This section establishes three classes of auxiliary results:

1. **Coprimality refreshing**: the identity `d ∣ (E-1)*R + 1 ↔ d ∣ R - 1` when `d ∣ E`,
   which governs how coprimality evolves along the Euclid-Mullin recursion
   `P(n+1) = P(n) · seq(n+1) = P(n) · minFac(P(n) + 1)`.

2. **No safe cycle / death rate bound**: given a lower bound `μ_min > 0` on per-state
   "death rates" `δ`, the survival probability over a set decays as `(1 - μ_min)^|C|`.

3. **Neg-inv involution**: on `(ZMod q)ˣ` with `q` prime and `q ≥ 3`, the map `w ↦ -w⁻¹`
   is an involution (hence bijection), corresponding to the walk bridge `walkZ = -1`.
-/

section CoprimRefresh

/-- **Coprimality refreshing (divisibility form)**: if `d ∣ E` then
    `d ∣ (E - 1) * R + 1 ↔ d ∣ R - 1`.

    This follows from the ring identity `(E - 1) * R + 1 = E * R - (R - 1)`:
    since `d ∣ E * R`, the two divisibility conditions are equivalent. -/
theorem coprimality_refreshing_int (E R d : ℤ) (hd : d ∣ E) :
    d ∣ (E - 1) * R + 1 ↔ d ∣ R - 1 := by
  have hkey : (E - 1) * R + 1 = E * R - (R - 1) := by ring
  rw [hkey]
  have hdER : d ∣ E * R := hd.mul_right R
  constructor
  · intro h
    -- d ∣ E*R and d ∣ E*R - (R-1), so d ∣ (E*R) - (E*R - (R-1)) = R-1
    have : d ∣ E * R - (E * R - (R - 1)) := dvd_sub hdER h
    rwa [sub_sub_cancel] at this
  · intro h
    exact dvd_sub hdER h

/-- **Coprimality refreshing (non-divisibility)**: if `d ∣ E` and `d ∤ (R - 1)`,
    then `d ∤ (E - 1) * R + 1`. Contrapositive of the forward direction of
    `coprimality_refreshing_int`. -/
theorem coprimality_refreshing_ndvd (E R d : ℤ) (hdvd : d ∣ E)
    (hndvd : ¬ d ∣ R - 1) : ¬ d ∣ (E - 1) * R + 1 :=
  fun h => hndvd ((coprimality_refreshing_int E R d hdvd).mp h)

end CoprimRefresh

section NoSafeCycle

/-- **No safe cycle bound**: if every element of `C` has a "death rate" at least `μ_min`
    (i.e., `δ x ≥ μ_min` for all `x ∈ C`), and `0 ≤ δ x ≤ 1` for all `x ∈ C`, then
    the product `∏ c ∈ C, (1 - δ c) ≤ (1 - μ_min) ^ C.card`.

    This models survival probability: if each state independently kills the walk with
    probability at least `μ_min`, the probability of surviving the entire cycle `C`
    decays exponentially. -/
theorem no_safe_cycle {α : Type*} (C : Finset α) (δ : α → ℝ) (μ_min : ℝ)
    (hδ_lower : ∀ c ∈ C, μ_min ≤ δ c)
    (hδ_upper : ∀ c ∈ C, δ c ≤ 1) :
    ∏ c ∈ C, (1 - δ c) ≤ (1 - μ_min) ^ C.card := by
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod
  · intro i hi
    linarith [hδ_upper i hi]
  · intro i hi
    linarith [hδ_lower i hi]

/-- **Bijection preserves sum**: if `σ` is a bijection on a `Fintype`, then
    `∑ x, f (σ x) = ∑ x, f x`. This is a direct wrapper around `Equiv.sum_comp`. -/
theorem sum_equiv_eq {α : Type*} [Fintype α] (σ : α ≃ α) (f : α → ℝ) :
    ∑ x, f (σ x) = ∑ x, f x :=
  σ.sum_comp f

end NoSafeCycle

section NegInvInvolution

/-- **Neg-inv is an involution on `(ZMod q)ˣ`**: the map `w ↦ -w⁻¹` satisfies
    `(-(-w⁻¹)⁻¹) = w`. This is because `(-w⁻¹)⁻¹ = (-1)⁻¹ · w = -w`, so
    `-(-w) = w`.

    This map arises naturally from the walk bridge: `walkZ(q,n) = -1` iff
    `q ∣ prod(n) + 1`, and the action of multiplication by `seq(n+1)` on
    `walkZ(q,n) = -1` sends the position to `-walkZ(q,n)⁻¹ · seq(n+1)`. -/
theorem neg_inv_involutive (q : ℕ) [Fact (Nat.Prime q)] :
    Function.Involutive (fun w : (ZMod q)ˣ => -w⁻¹) := by
  intro w
  simp [inv_neg, inv_inv]

/-- **Neg-inv is a bijection on `(ZMod q)ˣ`**. -/
theorem neg_inv_bijective (q : ℕ) [Fact (Nat.Prime q)] :
    Function.Bijective (fun w : (ZMod q)ˣ => -w⁻¹) :=
  (neg_inv_involutive q).bijective

/-- **Neg-inv as an equivalence on `(ZMod q)ˣ`**. -/
noncomputable def negInvEquiv (q : ℕ) [Fact (Nat.Prime q)] : (ZMod q)ˣ ≃ (ZMod q)ˣ :=
  Equiv.ofBijective _ (neg_inv_bijective q)

end NegInvInvolution

section WalkTelescope

/-- **Walk product telescope**: if positions satisfy `w (n + 1) = w n * m n` for all `n`,
    then `w (n + k) = w n * ∏ i ∈ Finset.range k, m (n + i)`.

    This is a direct induction on `k`, giving the standard multiplicative telescope
    for random walks on groups. -/
theorem walk_product_telescope {G : Type*} [CommGroup G]
    (w : ℕ → G) (m : ℕ → G) (hstep : ∀ n, w (n + 1) = w n * m n)
    (n k : ℕ) :
    w (n + k) = w n * ∏ i ∈ Finset.range k, m (n + i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih]
    rw [show n + (k + 1) = (n + k) + 1 from by omega]
    exact hstep (n + k)

/-- **Character ratio from walk step**: if `w (n + 1) = w n * m n` for a group `G`,
    and `χ : G →* H` is a group homomorphism to a commutative group, then
    `χ (m n) = χ (w n)⁻¹ * χ (w (n + 1))`. -/
theorem char_ratio_of_walk_step {G H : Type*} [Group G] [CommGroup H]
    (w : ℕ → G) (m : ℕ → G) (hstep : ∀ n, w (n + 1) = w n * m n)
    (χ : G →* H) (n : ℕ) :
    χ (m n) = (χ (w n))⁻¹ * χ (w (n + 1)) := by
  rw [hstep n, map_mul]
  group

/-- **Coprimality refreshing (natural number form)**: for natural numbers `E, R`
    with `E ≥ 2` and `R ≥ 1`, and a prime `p` dividing `E`:
    `p ∣ (E - 1) * R + 1 ↔ p ∣ R - 1`, where arithmetic is in `ℤ`.

    This is a specialization of `coprimality_refreshing_int` to the case
    where `E` and `R` are natural numbers lifted to `ℤ`. -/
theorem coprimality_refreshing_nat (E R p : ℕ)
    (hp : (p : ℤ) ∣ (E : ℤ)) :
    (p : ℤ) ∣ ((E : ℤ) - 1) * (R : ℤ) + 1 ↔ (p : ℤ) ∣ ((R : ℤ) - 1) :=
  coprimality_refreshing_int (E : ℤ) (R : ℤ) (p : ℤ) hp

end WalkTelescope
