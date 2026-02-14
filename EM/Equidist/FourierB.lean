import EM.Equidist.Fourier
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Character Orthogonality Counting and Fourier Reduction (Part B)

This is Part B of the character sum framework, split from `Fourier.lean` for
compilation performance. It contains:

* §29: Character orthogonality counting formula
* §30: Complex character sum bound and Fourier reduction

Part A (`Fourier.lean`) contains §24-28: CharacterSumFramework,
TailSECharacterChain, GlobalTailSEDecomposition, DecorrelationPrinciple,
CofinalCycleProduct.
-/

open Mullin Euclid MullinGroup RotorRouter

/-! ## §29: Character Orthogonality Counting Formula

The fundamental bridge between character sums and the walk hitting count.
By Fourier inversion on the finite abelian group `(ZMod q)ˣ` of order `q-1`:

```
WalkHitCount q hq hne t N
  = N/(q-1) + (1/(q-1)) · Σ_{χ ≠ χ₀} χ(t)⁻¹ · [Σ_{n<N} χ(emWalkUnit q n)]
```

The trivial character contributes exactly `N/(q-1)`.  If for each non-trivial
character χ the partial sum `|Σ_{n<N} χ(emWalkUnit q n)| = o(N)`, then the
hitting count is `N/(q-1) + o(N) → ∞`, giving cofinal hitting and hence
`WalkEquidistribution`.

This section formalises:

* `WalkHitCount`: the count `#{n < N : emWalkUnit q n = t}`.
* `CharSumBound`: the o(N) cancellation property for non-trivial characters,
  stated as an open Prop (requires ℂ-valued character theory not yet in Mathlib).
* `HitCountLowerBound`: an open Prop encapsulating the Fourier inversion
  consequence — the walk hits every target at linear rate.
* `hitCountLowerBound_implies_we`: the proved reduction
  `HitCountLowerBound → WalkEquidistribution`.
* `char_sum_bound_mc`: the full chain to MullinConjecture.

The key structural result is `cofinal_of_hitCount_unbounded`:
if the hitting count is unbounded, cofinal hitting follows by pure monotonicity.
The arithmetic bound `WalkHitCount ≥ N/(2*(q-1))` yields unboundedness.
All logical connections are formally verified; the only open content is the
Fourier inversion formula and the character cancellation bound. -/

section CharOrthogonalityCounting
open MullinGroup

/-- **WalkHitCount**: the number of steps `n < N` at which the unit-level walk
    equals the target `t`.

    This is the "empirical frequency" of the walk at `t` in the first `N` steps.
    By character orthogonality (Fourier inversion on `(ZMod q)ˣ`), it equals
    `N/(q-1)` plus a correction from the non-trivial character sums. -/
noncomputable def WalkHitCount (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (t : (ZMod q)ˣ) (N : Nat) : Nat :=
  ((Finset.range N).filter (fun n => emWalkUnit q hq hne n = t)).card

/-- **WalkHitCount is monotone in N**: adding one more step can only
    increase (or leave unchanged) the hitting count. -/
theorem walkHitCount_mono (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (t : (ZMod q)ˣ) {M N : Nat} (h : M ≤ N) :
    WalkHitCount q hq hne t M ≤ WalkHitCount q hq hne t N := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono h

/-- **WalkHitCount is positive when the walk visits t**: if the walk equals `t`
    at step `n`, then `WalkHitCount q t (n + 1) ≥ 1`. -/
theorem walkHitCount_pos_of_hit (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (t : (ZMod q)ˣ) {n : Nat} (hn : emWalkUnit q hq hne n = t) :
    1 ≤ WalkHitCount q hq hne t (n + 1) :=
  Finset.card_pos.mpr ⟨n, by simp [Finset.mem_filter, hn]⟩

/-- **WalkHitCount grows without bound if the walk visits t cofinally**:
    if for every `N₀` there is `n ≥ N₀` with `emWalkUnit q n = t`, then
    `WalkHitCount q t N → ∞`. -/
theorem walkHitCount_unbounded_of_cofinal (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (t : (ZMod q)ˣ)
    (hcof : ∀ N₀, ∃ n, N₀ ≤ n ∧ emWalkUnit q hq hne n = t) :
    ∀ K, ∃ N, K ≤ WalkHitCount q hq hne t N := by
  intro K
  induction K with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨N₀, hN₀⟩ := ih
    obtain ⟨n, hn_ge, heq⟩ := hcof N₀
    refine ⟨n + 1, ?_⟩
    -- The filter for [0, N₀) is a subset of the filter for [0, n+1)
    -- and n ∈ filter([0,n+1)) \ filter([0,N₀))
    -- so WalkHitCount(n+1) ≥ WalkHitCount(N₀) + 1 ≥ k + 1
    have hstep : n ∉ Finset.range N₀ := by simp; omega
    have hmem : n ∈ (Finset.range (n + 1)).filter
        (fun m => emWalkUnit q hq hne m = t) := by
      simp [Finset.mem_filter, heq]
    -- The filter for N₀ is a strict subset of the filter for n+1
    have hstrictSub : (Finset.range N₀).filter (fun m => emWalkUnit q hq hne m = t) ⊂
        (Finset.range (n + 1)).filter (fun m => emWalkUnit q hq hne m = t) := by
      constructor
      · apply Finset.filter_subset_filter
        exact Finset.range_mono (Nat.le_succ_of_le hn_ge)
      · intro hsub
        have : n ∈ (Finset.range N₀).filter (fun m => emWalkUnit q hq hne m = t) :=
          hsub hmem
        simp [Finset.mem_filter] at this
        exact hstep (Finset.mem_range.mpr this.1)
    have hcard : WalkHitCount q hq hne t N₀ < WalkHitCount q hq hne t (n + 1) :=
      Finset.card_lt_card hstrictSub
    omega

/-- **Cofinal hitting from unbounded count**: if `WalkHitCount q t N` is
    unbounded (for every `K` there is `N` with `WalkHitCount ≥ K`), then
    the walk hits `t` cofinally.

    The argument: if the count exceeds the count at `N₀` for some large `N`,
    then there must be a new hit strictly after step `N₀`. -/
theorem cofinal_of_hitCount_unbounded (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (t : (ZMod q)ˣ)
    (hunbd : ∀ K, ∃ N, K ≤ WalkHitCount q hq hne t N) :
    ∀ N₀, ∃ n, N₀ ≤ n ∧ emWalkUnit q hq hne n = t := by
  intro N₀
  obtain ⟨N, hN⟩ := hunbd (WalkHitCount q hq hne t N₀ + 1)
  have hlt : N₀ < N := by
    by_contra h; push Not at h
    exact absurd (walkHitCount_mono q hq hne t h) (by omega)
  suffices ∃ n ∈ Finset.range N, N₀ ≤ n ∧ emWalkUnit q hq hne n = t by
    obtain ⟨n, _, hn₀, heq⟩ := this; exact ⟨n, hn₀, heq⟩
  by_contra hall; push Not at hall
  have : WalkHitCount q hq hne t N ≤ WalkHitCount q hq hne t N₀ := by
    apply Finset.card_le_card; intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨Nat.lt_of_not_le fun hge => hall n (Finset.mem_range.mpr hn.1) hge hn.2, hn.2⟩
  omega

/-- **Unbounded count from linear lower bound**: if `WalkHitCount q t N ≥ N / (2*(q-1))`
    for all large `N`, then `WalkHitCount` is unbounded.

    This is the arithmetic bridge: a count that grows at least linearly
    eventually exceeds any fixed bound `K`. -/
theorem unbounded_of_linear_lower_bound (q : Nat) [Fact (Nat.Prime q)]
    (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (t : (ZMod q)ˣ)
    (hlb : ∃ N₀, ∀ N ≥ N₀, WalkHitCount q hq hne t N * (2 * (q - 1)) ≥ N) :
    ∀ K, ∃ M, K ≤ WalkHitCount q hq hne t M := by
  intro K
  obtain ⟨N₀, hN₀⟩ := hlb
  have hq1 : 0 < 2 * (q - 1) := by have := (Fact.out : Nat.Prime q).two_le; omega
  let M := max N₀ (2 * (q - 1) * (K + 1))
  refine ⟨M, ?_⟩
  have hM := hN₀ M (le_max_left _ _)
  have hM2 : 2 * (q - 1) * (K + 1) ≤ M := le_max_right _ _
  nlinarith

open Classical in
/-- **CharSumBound**: the analytic hypothesis that non-trivial character sums
    over the EM walk are `o(N)`.

    For a prime `q` not in the EM sequence, `CharSumBound` asserts that for
    every non-trivial group homomorphism `χ : (ZMod q)ˣ →* G`, the number
    of steps `n < N` where `χ(emWalkUnit q n) ≠ 1` grows at most as `ε * N`
    for any `ε > 0` and all sufficiently large `N`.

    The standard analytic form (`∑_{n<N} χ(w(n)) = o(N)` for complex-valued
    characters χ) implies this formulation via a pigeonhole argument.
    `CharSumBound` is stated purely group-theoretically to avoid requiring
    `ℂ` in the formal development.

    Combined with `HitCountLowerBound`, this implies `WalkEquidistribution`
    and hence MullinConjecture. -/
def CharSumBound : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ {G : Type*} [CommGroup G] (χ : (ZMod q)ˣ →* G) (_hχ : ∃ g, χ g ≠ 1),
  ∀ (ε_num ε_den : ℕ) (_hε : 0 < ε_den),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ((Finset.range N).filter (fun n => χ (emWalkUnit q hq hne n) ≠ 1)).card * ε_den ≤
    ε_num * N

/-- **HitCountLowerBound**: the consequence of Fourier inversion that
    every walk target is hit at linear rate.

    This encapsulates the content of the character orthogonality counting
    formula: if CharSumBound holds (all non-trivial character sums are o(N)),
    then by Fourier inversion on `(ZMod q)ˣ`, every target `t` is hit at
    least `N / (2*(q-1))` times in the first `N` steps, for large `N`.

    **Open Prop**: the Fourier inversion step requires ℂ-valued Dirichlet
    characters and the Plancherel identity on finite abelian groups, which
    is not yet available in the Mathlib ZMod API.  Together with
    `CharSumBound`, it implies `WalkEquidistribution`. -/
def HitCountLowerBound : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (t : (ZMod q)ˣ),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    WalkHitCount q hq hne t N * (2 * (q - 1)) ≥ N

/-- **HitCountLowerBound → WalkEquidistribution**: a linear lower bound on
    the hitting count implies that every target is visited cofinally.

    The proof chains:
    - linear lower bound → WalkHitCount is unbounded (arithmetic)
    - unbounded WalkHitCount → cofinal hitting (`cofinal_of_hitCount_unbounded`)
    - cofinal hitting of every target = WalkEquidistribution -/
theorem hitCountLowerBound_implies_we
    (hlb : HitCountLowerBound) :
    WalkEquidistribution := by
  intro q _ hq hne t N₀
  -- Build the unboundedness of WalkHitCount from the linear lower bound
  have hunbd : ∀ K, ∃ M, K ≤ WalkHitCount q hq hne t M :=
    unbounded_of_linear_lower_bound q hq hne t (hlb q hq hne t)
  -- Conclude cofinal hitting
  exact cofinal_of_hitCount_unbounded q hq hne t hunbd N₀

/-- **CharSumBound + HitCountLowerBound → WalkEquidistribution**:
    the bridge between the two open analytic Props and walk equidistribution.

    - `CharSumBound` (analytic): non-trivial character sums are `o(N)`.
    - `HitCountLowerBound` (algebraic/Fourier): this cancellation implies
      the walk hits every target at rate `≥ N/(2*(q-1))`.
    Together they give cofinal hitting of every target ∈ (ZMod q)ˣ. -/
theorem char_sum_bound_implies_we
    (_hcsb : CharSumBound)
    (hlb : HitCountLowerBound) :
    WalkEquidistribution :=
  hitCountLowerBound_implies_we hlb

/-- **CharSumBound + HitCountLowerBound → DynamicalHitting**: the key
    implication for Mullin's Conjecture via walk equidistribution. -/
theorem char_sum_bound_implies_dh
    (hcsb : CharSumBound)
    (hlb : HitCountLowerBound) :
    DynamicalHitting :=
  walk_equidist_implies_dh (char_sum_bound_implies_we hcsb hlb)

/-- **CharSumBound + HitCountLowerBound → MullinConjecture**:
    the complete analytic reduction chain.

    ```
    CharSumBound + HitCountLowerBound
        →[§29]→ WalkEquidistribution
        →[proved]→ DynamicalHitting
        →[proved]→ MullinConjecture
    ```

    The two open Props encapsulate all analytic content:
    - `CharSumBound`: the hard analysis — non-trivial character sums cancel.
    - `HitCountLowerBound`: the algebra bridge — Fourier inversion converts
      character cancellation into a linear lower bound on hitting frequency.
    All logical implications between these Props and MullinConjecture are
    formally verified. -/
theorem char_sum_bound_mc
    (hcsb : CharSumBound)
    (hlb : HitCountLowerBound) :
    MullinConjecture :=
  walk_equidist_mc (char_sum_bound_implies_we hcsb hlb)

/-! ## §30. Complex Character Sum Bound and Fourier Reduction

This section provides the analytically correct formulation of character sum
cancellation using complex-valued Dirichlet characters, and states the open
hypothesis that this implies the linear hitting lower bound.

The key insight is the Fourier inversion formula on the finite abelian group
`(ZMod q)ˣ` of order `φ(q) = q - 1`:

```
WalkHitCount q t N = (1/(q-1)) · Σ_χ χ(t)⁻¹ · [Σ_{n<N} χ(emWalkUnit q n)]
```

The trivial character (χ = 1) contributes exactly N/(q-1).  If for each
non-trivial χ : (ZMod q)ˣ →* ℂˣ the partial sum has `‖Σ_{n<N} χ(w(n))‖ = o(N)`,
then the hitting count is `N/(q-1) + o(N)`, which is `≥ N/(2*(q-1))` for
large N.  This gives `HitCountLowerBound`, and hence `WalkEquidistribution`.

**`ComplexCharSumBound`** is the analytically correct open Prop.
**`complex_csb_implies_hitCount_lb`** is the open Prop encapsulating the
Fourier inversion step (requires character orthogonality on finite abelian
groups over ℂ, not yet formally connected to our walk setting).
**`complex_csb_mc`** is the proved reduction chain. -/

/-- **ComplexCharSumBound**: for every prime `q` not in the EM sequence,
    every non-trivial multiplicative character `χ : (ZMod q)ˣ →* ℂˣ` satisfies
    the cancellation bound `‖Σ_{n<N} χ(emWalkUnit q n)‖ ≤ ε · N` for all
    sufficiently large `N` and any `ε > 0`.

    This is the analytically correct `o(N)` statement: the partial sums of a
    non-trivial character along the EM walk grow strictly sublinearly.

    For a prime `q`, `(ZMod q)ˣ` is cyclic of order `q - 1`.  A character
    `χ : (ZMod q)ˣ →* ℂˣ` maps into roots of unity (all values have norm 1).
    The cancellation `o(N)` is the dynamical equidistribution hypothesis.

    **Open Prop**: the proof requires deep analytic number theory — relating the
    EM walk's equidistribution to the spectral gap of the associated dynamical
    system.  All downstream implications are formally verified. -/
def ComplexCharSumBound : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
  ∀ (ε : ℝ) (_hε : 0 < ε),
  ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * N

/-- **ComplexCharSumBound implies HitCountLowerBound**: the open Prop
    encapsulating the Fourier inversion step.

    By the Plancherel/orthogonality formula on the finite abelian group
    `(ZMod q)ˣ`, the indicator sum decomposes as a character expansion:

    ```
    WalkHitCount q t N = (1/(q-1)) Σ_χ χ(t)⁻¹ · [Σ_{n<N} χ(w(n))]
    ```

    Under `ComplexCharSumBound`, each non-trivial character contributes `o(N)`,
    so the total is `N/(q-1) + o(N) ≥ N/(2*(q-1))` for large `N`.

    **Open Prop**: the formal connection requires:
    1. The character orthogonality formula (available in Mathlib for finite
       abelian groups, but not yet wired to our `WalkHitCount` definition).
    2. A bound converting complex `o(N)` estimates to integer inequalities.

    Both are standard but require non-trivial formalization work. -/
def ComplexCSBImpliesHitCountLB : Prop :=
  ComplexCharSumBound → HitCountLowerBound

/-- **WalkHitCountFourierStep**: the exact Fourier expansion of WalkHitCount via
    Dirichlet character orthogonality.

    For prime `q` not in the EM sequence, the hitting count satisfies the
    character expansion:
    ```
    WalkHitCount q t N · (q - 1) = ∑_{χ : DirichletCharacter ℂ q} χ(t⁻¹) · ∑_{n<N} χ(w(n))
    ```

    Here `(q - 1) = φ(q)` is the number of Dirichlet characters mod `q`, the
    trivial character contributes exactly `N`, and all other terms give the
    Fourier error.

    **Open Prop**: the proof uses `DirichletCharacter.sum_char_inv_mul_char_eq`
    with `R = ℂ` (which requires `HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)`),
    plus interchange of finite sums. Both steps are standard but require connecting
    our `WalkHitCount` and `emWalkUnit` definitions to the Mathlib character API. -/
def WalkHitCountFourierStep : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
  ∀ (t : (ZMod q)ˣ) (N : Nat),
  (WalkHitCount q hq hne t N : ℂ) * (q - 1 : ℕ) =
    ∑ χ : DirichletCharacter ℂ q,
      χ ↑(t⁻¹ : (ZMod q)ˣ) * ∑ n ∈ Finset.range N, χ ↑(emWalkUnit q hq hne n)

/-- **WalkHitCountFourierStep holds**: the Fourier expansion of WalkHitCount via Dirichlet
    character orthogonality on the finite abelian group `(ZMod q)ˣ`.

    **Proof**: By the character orthogonality formula on `(ZMod q)ˣ`:
    ```
    ∑_χ χ(t⁻¹) * χ(w) = if ↑t = ↑w then q.totient else 0
    ```
    Summing over `n < N` and swapping the order of summation yields the
    Fourier expansion of the indicator `[emWalkUnit q n = t]`. -/
theorem walk_hit_count_fourier_step : WalkHitCountFourierStep := by
  intro q inst hq hne t N
  haveI : Fact (Nat.Prime q) := inst
  have hqprime : Nat.Prime q := Fact.out
  have hq2 : 2 ≤ q := hqprime.two_le
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero (q : ℂ) := ⟨by exact_mod_cast hqprime.ne_zero⟩
  haveI : NeZero (Monoid.exponent (ZMod q)ˣ : ℂ) :=
    ⟨by exact_mod_cast (Monoid.ExponentExists.of_finite.exponent_pos).ne'⟩
  haveI : IsSepClosed ℂ := IsSepClosed.of_isAlgClosed ℂ
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ) := inferInstance
  have htotient : q.totient = q - 1 := Nat.totient_prime hqprime
  -- RHS = ∑_χ χ(t⁻¹) * ∑_{n<N} χ(emWalkUnit n)
  --     = ∑_χ ∑_{n<N} χ(t⁻¹) * χ(emWalkUnit n)     [mul distributes over sum]
  --     = ∑_{n<N} ∑_χ χ(t⁻¹) * χ(emWalkUnit n)     [swap sums]
  --     = ∑_{n<N} (if t = emWalkUnit n then (q-1) else 0)   [orthogonality]
  --     = (q-1) * WalkHitCount
  --
  -- Orthogonality lemma for each n
  have horth : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q,
      χ ↑(t⁻¹ : (ZMod q)ˣ) * χ ↑(emWalkUnit q hq hne n) =
      if t = emWalkUnit q hq hne n then (q - 1 : ℕ) else 0 := by
    intro n
    have ha : IsUnit (↑t : ZMod q) := Units.isUnit t
    have hinv : (↑(t⁻¹ : (ZMod q)ˣ) : ZMod q) = (↑t : ZMod q)⁻¹ :=
      Units.val_inv_eq_inv_val t
    -- Rewrite the sum using hinv to match sum_char_inv_mul_char_eq
    conv_lhs =>
      arg 2; ext χ
      rw [show χ ↑(t⁻¹ : (ZMod q)ˣ) = χ (↑t : ZMod q)⁻¹ by rw [hinv]]
    have hkey := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha
        (↑(emWalkUnit q hq hne n) : ZMod q)
    rw [hkey, htotient]
    -- Now: if ↑t = ↑(emWalkUnit n) then (q-1) else 0
    -- Need: if t = emWalkUnit n then (q-1) else 0
    simp only [Units.val_injective.eq_iff]
    split_ifs <;> simp
  -- RHS → ∑_χ ∑_n ... → ∑_n ∑_χ ... → ∑_n indicator → (q-1) * WalkHitCount
  -- Unfold WalkHitCount and work in ℂ
  simp only [WalkHitCount]
  -- Expand mul: ∑_χ f(χ) * ∑_n g(n) = ∑_χ ∑_n f(χ) * g(n)
  conv_rhs =>
    arg 2; ext χ
    rw [Finset.mul_sum]
  -- Swap ∑_χ ∑_n to ∑_n ∑_χ
  rw [Finset.sum_comm]
  -- Apply orthogonality: inner sum = if t = emWalkUnit n then (q-1) else 0
  simp_rw [horth]
  -- Now: ∑_{n<N} ↑(if t = emWalkUnit n then (q-1) else 0) = ↑card * ↑(q-1)
  -- Prove the identity in ℕ, then cast to ℂ
  suffices key : (Finset.filter (fun n => emWalkUnit q hq hne n = t) (Finset.range N)).card *
      (q - 1) = ∑ x ∈ Finset.range N, if t = emWalkUnit q hq hne x then q - 1 else 0 by
    exact_mod_cast key
  simp_rw [eq_comm (a := t)]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

/-- A non-trivial `DirichletCharacter` has non-trivial `toUnitHom`. -/
theorem dirichlet_ne_one_iff_toUnitHom_ne_one {q : ℕ}
    (ψ : DirichletCharacter ℂ q) :
    ψ ≠ 1 ↔ ψ.toUnitHom ≠ 1 := by
  have h1 : (1 : DirichletCharacter ℂ q).toUnitHom = 1 := by ext; simp [MulChar.one_apply_coe]
  have key : ψ = 1 ↔ ψ.toUnitHom = 1 :=
    (DirichletCharacter.toUnitHom_inj (χ := ψ) 1).symm.trans (by rw [h1])
  exact key.not

/-- For a `DirichletCharacter ℂ q` and unit `u : (ZMod q)ˣ`, the character
    value (coerced to ℂ) equals the `toUnitHom` value coerced from `ℂˣ`. -/
theorem dirichlet_val_eq_toUnitHom {q : ℕ}
    (ψ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    ψ ↑u = (ψ.toUnitHom u : ℂ) :=
  (MulChar.coe_toUnitHom ψ u).symm

/-- Bounding non-trivial `DirichletCharacter ℂ q` sums given a per-prime bound
    on the underlying `(ZMod q)ˣ →* ℂˣ` character sums along the EM walk.

    This is the shared core used by both `dirichlet_char_sum_le_of_csb`
    (which obtains the unit-hom bound from `ComplexCharSumBound`) and
    `dirichlet_char_sum_le_of_mmcsb` in `LargeSieve.lean`
    (which obtains it from `MultiModularCSB`). -/
theorem dirichlet_char_sum_le_of_unit_bound
    {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (hbound : ∀ (χ : (ZMod q)ˣ →* ℂˣ) (_hχ : χ ≠ 1),
      ∀ (ε : ℝ) (_hε : 0 < ε),
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ‖∑ n ∈ Finset.range N, (χ (emWalkUnit q hq hne n) : ℂ)‖ ≤ ε * N)
    (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ Finset.range N, ψ ↑(emWalkUnit q hq hne n)‖ ≤ ε * N := by
  have hψ' : ψ.toUnitHom ≠ 1 := (dirichlet_ne_one_iff_toUnitHom_ne_one ψ).mp hψ
  obtain ⟨N₀, hN₀⟩ := hbound ψ.toUnitHom hψ' ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  simp_rw [dirichlet_val_eq_toUnitHom]
  exact hN₀ N hN

/-- Bounding non-trivial `DirichletCharacter ℂ q` sums via `ComplexCharSumBound`.
    Specializes `dirichlet_char_sum_le_of_unit_bound` with the global CCSB hypothesis. -/
private theorem dirichlet_char_sum_le_of_csb
    (hcsb : ComplexCharSumBound)
    {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q)
    (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ‖∑ n ∈ Finset.range N, ψ ↑(emWalkUnit q hq hne n)‖ ≤ ε * N :=
  dirichlet_char_sum_le_of_unit_bound hq hne (hcsb q hq hne) ψ hψ ε hε

/-- **WalkHitCountFourierStep → ComplexCSBImpliesHitCountLB**:
    given the Fourier expansion identity for `WalkHitCount`, the complex
    character sum bound implies the linear hitting lower bound.

    **Proof sketch**: Fix prime `q`, target `t`, and large `N`.
    1. Apply `WalkHitCountFourierStep` to write `WalkHitCount * (q-1)` as
       a character sum.
    2. The trivial character contributes exactly `N`.
    3. Each non-trivial character's partial sum has norm `≤ ε * N` by CCSB.
       Use `ε = 1 / (2 * Fintype.card (DirichletCharacter ℂ q))`.
    4. The total error has norm `≤ (card - 1) * ε * N < N/2`.
    5. Hence `WalkHitCount * (q-1) ≥ N/2`, so `WalkHitCount * (2*(q-1)) ≥ N`. -/
theorem fourier_step_implies_csb_lb
    (hfstep : WalkHitCountFourierStep) :
    ComplexCSBImpliesHitCountLB := by
  intro hcsb q inst hq hne t
  haveI : Fact (Nat.Prime q) := inst
  haveI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  have hqprime : Nat.Prime q := Fact.out
  have hq2 : 1 < q := hqprime.one_lt
  -- The number of Dirichlet characters
  let card := Fintype.card (DirichletCharacter ℂ q)
  have hcard_pos : 0 < card := Fintype.card_pos
  -- Choose ε = 1 / (2 * card) for the CCSB bound
  let ε : ℝ := 1 / (2 * card)
  have hε : 0 < ε := by positivity
  -- For each non-trivial character, get a threshold via CCSB
  -- Use classical choice to define the threshold function
  let getN₀ : DirichletCharacter ℂ q → ℕ := fun ψ =>
    if hψ : ψ = 1 then 0
    else (dirichlet_char_sum_le_of_csb hcsb hq hne ψ hψ ε hε).choose
  -- The global threshold is the sup over all non-trivial characters
  let N₀ := Finset.univ.sup getN₀
  use N₀
  intro N hN
  -- For each non-trivial character, the sum bound holds for N ≥ N₀
  have hbounds : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ‖∑ n ∈ Finset.range N, ψ ↑(emWalkUnit q hq hne n)‖ ≤ ε * N := by
    intro ψ hψ
    have hN₀_le : getN₀ ψ ≤ N₀ := Finset.le_sup (Finset.mem_univ ψ)
    have hN_ge : N ≥ getN₀ ψ := Nat.le_trans hN₀_le hN
    have : N ≥ (dirichlet_char_sum_le_of_csb hcsb hq hne ψ hψ ε hε).choose := by
      simp only [getN₀, dif_neg hψ] at hN_ge
      exact hN_ge
    exact (dirichlet_char_sum_le_of_csb hcsb hq hne ψ hψ ε hε).choose_spec N this
  -- Apply the Fourier step identity (uses DirichletCharacter.fintype globally)
  have hfourier : (WalkHitCount q hq hne t N : ℂ) * (q - 1 : ℕ) =
      ∑ χ : DirichletCharacter ℂ q,
        χ ↑(t⁻¹ : (ZMod q)ˣ) * ∑ n ∈ Finset.range N, χ ↑(emWalkUnit q hq hne n) :=
    hfstep q hq hne t N
  -- Separate trivial and non-trivial characters
  rw [← Finset.add_sum_erase Finset.univ _
      (Finset.mem_univ (1 : DirichletCharacter ℂ q))] at hfourier
  -- Trivial character contribution: χ₁(t⁻¹) * ∑_n χ₁(w(n)) = 1 * N = N
  have h_triv : (1 : DirichletCharacter ℂ q) ↑(t⁻¹ : (ZMod q)ˣ) *
      ∑ n ∈ Finset.range N, (1 : DirichletCharacter ℂ q) ↑(emWalkUnit q hq hne n) = N := by
    simp only [MulChar.one_apply_coe, one_mul, Finset.sum_const, Finset.card_range]; ring
  -- Abbreviation for the error sum
  let Serr := ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
      χ ↑(t⁻¹ : (ZMod q)ˣ) * ∑ n ∈ Finset.range N, χ ↑(emWalkUnit q hq hne n)
  -- Error bound: ‖Serr‖ ≤ (card - 1) * ε * N
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
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
            Finset.card_univ, nsmul_eq_mul]
          simp only [card, Nat.cast_sub hcard_pos]; ring
  -- From hfourier: WalkHitCount * (q-1) = N + Serr (as complex numbers)
  have hfourier' : (WalkHitCount q hq hne t N : ℂ) * (q - 1 : ℕ) = N + Serr := by
    rw [hfourier, h_triv]
  -- Convert the complex identity to a real inequality
  -- re(N + Serr) ≥ N - ‖Serr‖ ≥ N - (card-1)*ε*N
  have h_re_ineq : (WalkHitCount q hq hne t N : ℝ) * (q - 1 : ℕ) ≥ N - (card - 1) * ε * N := by
    have hlhs_re : ((WalkHitCount q hq hne t N : ℂ) * (q - 1 : ℕ)).re =
        (WalkHitCount q hq hne t N : ℝ) * (q - 1 : ℕ) := by
      simp [Complex.mul_re, Complex.natCast_re]
    have hrhs_re : (↑N + Serr).re ≥ (N : ℝ) - (card - 1) * ε * N := by
      rw [Complex.add_re, show (N : ℂ).re = (N : ℝ) from Complex.natCast_re N]
      have hre_lb : -‖Serr‖ ≤ Serr.re := (abs_le.mp (RCLike.abs_re_le_norm Serr)).1
      linarith
    rw [← hlhs_re, hfourier']
    exact hrhs_re
  -- (card-1)*ε = (card-1)/(2*card) ≤ 1/2
  have h_eps_small : (card - 1 : ℝ) * ε ≤ 1 / 2 := by
    simp only [ε]
    have hcard_pos' : (0 : ℝ) < card := Nat.cast_pos.mpr hcard_pos
    rw [show (card - 1 : ℝ) * (1 / (2 * card)) = (card - 1) / (2 * card) from by ring,
      div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  have h_whc_half : (WalkHitCount q hq hne t N : ℝ) * (q - 1 : ℕ) ≥ N / 2 := by
    have hN_nn : (N : ℝ) ≥ 0 := Nat.cast_nonneg N
    nlinarith
  -- Convert: WalkHitCount * (2*(q-1)) ≥ N (as ℕ)
  rw [ge_iff_le, ← Nat.cast_le (α := ℝ)]
  push_cast
  have hq1_pos : (0 : ℝ) < (q - 1 : ℕ) := by exact_mod_cast (show 0 < q - 1 by omega)
  linarith

/-- **ComplexCSBImpliesHitCountLB is proved**: composing the Fourier step identity
    with the Fourier step → hit count lower bound theorem gives the full bridge. -/
theorem complex_csb_implies_hit_count_lb_proved : ComplexCSBImpliesHitCountLB :=
  fourier_step_implies_csb_lb walk_hit_count_fourier_step

/-- **ComplexCharSumBound + Fourier step → WalkEquidistribution**:
    given both the analytic cancellation and the Fourier inversion bridge,
    the walk visits every target cofinally. -/
theorem complex_csb_implies_we
    (hcsb : ComplexCharSumBound)
    (hfourier : ComplexCSBImpliesHitCountLB) :
    WalkEquidistribution :=
  hitCountLowerBound_implies_we (hfourier hcsb)

/-- **ComplexCharSumBound + Fourier step → MullinConjecture**:
    the complete analytic reduction chain via complex character sums.

    ```
    ComplexCharSumBound + ComplexCSBImpliesHitCountLB
        →[§30]→ HitCountLowerBound
        →[proved]→ WalkEquidistribution
        →[proved]→ DynamicalHitting
        →[proved]→ MullinConjecture
    ```

    `ComplexCharSumBound` is the analytically correct hypothesis:
    non-trivial ℂ-valued character sums along the EM walk are `o(N)`.
    `ComplexCSBImpliesHitCountLB` is the Fourier inversion bridge.
    All other logical implications are formally verified. -/
theorem complex_csb_mc
    (hcsb : ComplexCharSumBound)
    (hfourier : ComplexCSBImpliesHitCountLB) :
    MullinConjecture :=
  walk_equidist_mc (complex_csb_implies_we hcsb hfourier)

end CharOrthogonalityCounting
