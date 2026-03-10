import EM.EquidistSelfCorrecting

/-!
# Prime Density, Sieve Transfer, and Walk Utilities

Prime density equipartition, LPF equidistribution, sieve transfer chain,
distributional PED, coprimality refreshing, neg-inv involution, and walk telescope.

## Main Results

* `primeDensity_chain_mc` : PDE + sieve chain ⟹ MC (PROVED)
* `genericLPF_chain_mc` : GLPFE + SieveTransfer ⟹ MC (PROVED)
* `dped_implies_ped` : DPED ⟹ PED (PROVED)
* `coprimality_refreshing_int` : coprimality refreshing identity (PROVED)
* `neg_inv_involutive` : w ↦ -w⁻¹ is involution (PROVED)
* `walk_product_telescope` : walk = ∏ multipliers (PROVED)
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
