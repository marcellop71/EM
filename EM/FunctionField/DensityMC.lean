import EM.FunctionField.FFSieve
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The genuine density statement for almost-all GenMixedMC over F_p[t]

This file formalizes the REAL function-field density statement that the counting
proxies `FFAlmostAllGenMixedMC` / `FFPSCD` in `FFSieve.lean` stand in for: the
proportion of monic squarefree starting points `m` of degree `1..n` that satisfy
`Q ∤ m` yet do NOT have the fixed monic irreducible `Q` `ffTreeReachable` —
measured against all monic squarefree polynomials of degree `1..n` — tends to
`0` as `n → ∞` (`ff_almost_all_genmixed_density`, conditional on the Kornblum
divergence hypothesis `FFDirichletDensity` ONLY).

The proof mirrors, over `F_p[t]`, the unconditional integer chain
`EM/IK/DirichletDensity.lean` → `EM/Ensemble/UnconditionalPSCD.lean` →
`MixedEnsemble.lean` (Parts 5–7, 15, 18–19):

* trapped starting points are sieve-confined (walk stays in a proper subset of
  residues mod `Q` missing `-1` and `0`) — pigeonhole over the finitely many
  proper subsets of the residue field `F_p[t]/Q = AdjoinRoot Q`;
* confined starting points avoid every monic irreducible in an excluded residue
  class dividing `m + 1` — a congruence sieve;
* over `F_p[t]` the sieve counting is EXACT (the function-field luxury): monic
  polynomials of degree `d ≥ deg N` distribute exactly `p^(d - deg N)` per residue
  class mod any monic `N` (`ffMonicDeg_residue_card`, division-algorithm bijection),
  so the sieved density is exactly `∏ (1 - p^(-deg P))` — no `+2` error term and no
  `weak_fmcd` epsilon-management;
* the sieve product tends to `0` provided `∑_{P ≡ a (Q)} p^(-deg P) = ∞` for each
  nonzero residue class `a` — this divergence is the isolated named hypothesis
  `FFDirichletDensity` (= Kornblum's theorem, the FF analogue of Dirichlet's
  theorem on primes in APs; over ℤ the corresponding input is proved
  unconditionally in `IK.DirichletDensity`).

The denominator frame uses the unconditional quarter bound
`p^d ≤ 4 * ffSqfreeDegCount p d` (FF analogue of `sqfreeCount_ge_quarter`),
obtained from the exact count of multiples of `P^2` among monics.

Note that the restriction to starting points with `Q ∤ m` is NECESSARY, exactly as
coprimality `gcd(m, q) = 1` is over ℤ: if `Q ∣ m` then `Q` divides every mixed walk
product from `m`, hence never divides `walk + 1`, so `Q` is unreachable from every
such `m ≠ Q` (`ff_not_reachable_of_dvd_start`).

## Main definitions

* `ffMonicDeg`, `ffSqfreeDegCount`, `ffSqfreeCount` -- the counting frame
* `ffTrappedDegCount`, `ffTrappedCount` -- trapped (hitting-failure) counts
* `ffReachableEver`, `ffAllowedFactors`, `FFAllFactorsIn` -- confinement frame
* `ffConfinedDegCount`, `ffConfinedCount`, `ffProperSubsets` -- confined counts
* `ffSievedDegCount`, `ffExcludedUpTo`, `ffClassIrredUpTo` -- the sieve frame
* `FFDirichletDensity` -- the isolated divergence hypothesis (Kornblum)
* `FFAlmostAllGenMixedDensity` -- the genuine density statement, as a Prop

## Main results

* `ffMonicDeg_residue_card` -- EXACT residue-class count `p^(d - deg N)` (division
  algorithm bijection; the FF luxury)
* `ffSqfreeDegCount_quarter` -- `p^d ≤ 4 * ffSqfreeDegCount p d` (unconditional)
* `ffSievedDegCount_le_real` -- exact sieve bound `≤ (∏ (1 - p^(-deg P))) * p^d`
* `ff_reachable_of_walk_dvd` -- walk extension: `Q ∣ walk + 1` at any step of any
  valid selection implies `ffTreeReachable`
* `ff_trapped_le_sum_confined` -- pigeonhole over proper residue subsets
* `ff_density_pscd` -- per-subset confinement decay (conditional on
  `FFDirichletDensity`)
* `ff_almost_all_genmixed_density` -- **headline**: trapped density → 0
  (conditional on `FFDirichletDensity` ONLY)

## References

* Integer-side blueprint: `EM/IK/DirichletDensity.lean`,
  `EM/Ensemble/UnconditionalPSCD.lean`, `EM/Ensemble/MixedEnsemble.lean`
* Proxy statements being replaced: `EM/FunctionField/FFSieve.lean`
* H. Kornblum, *Über die Primfunktionen in einer arithmetischen Progression*,
  Math. Z. 5 (1919)
-/

namespace FunctionFieldAnalog

open Polynomial Classical Filter

open scoped Classical

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Part 0: Elementary preliminaries -/

section Preliminaries

/-- `p ≥ 2` as a natural number fact, used throughout. -/
private theorem p_two_le : 2 ≤ p := hp.out.two_le

/-- Adding `1` to a monic polynomial of positive degree keeps it monic with the
    same degree. -/
private theorem monic_add_one {m : Polynomial (ZMod p)} (hm : m.Monic)
    (hd : 0 < m.natDegree) : (m + 1).Monic ∧ (m + 1).natDegree = m.natDegree := by
  have hdeg : degree (1 : Polynomial (ZMod p)) < degree m := by
    rw [Polynomial.degree_one]
    exact_mod_cast Polynomial.natDegree_pos_iff_degree_pos.mp hd
  exact ⟨hm.add_of_left hdeg, Polynomial.natDegree_add_eq_left_of_degree_lt hdeg⟩

/-- Geometric growth: `∑_{i < n} p^i ≤ p^n`. -/
private theorem geom_sum_le (n : ℕ) : ∑ i ∈ Finset.range n, p ^ i ≤ p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h2 : 2 ≤ p := p_two_le p
    nlinarith [pow_pos (show 0 < p by omega) n]

end Preliminaries

/-! ## Part 1: Counting frames -/

section CountingFrames

/-- The Finset of monic polynomials of degree exactly `d` over `F_p`. -/
noncomputable def ffMonicDeg (d : ℕ) : Finset (Polynomial (ZMod p)) :=
  (monic_natDegree_finite (ZMod p) d).toFinset

theorem mem_ffMonicDeg {d : ℕ} {m : Polynomial (ZMod p)} :
    m ∈ ffMonicDeg p d ↔ m.Monic ∧ m.natDegree = d := by
  simp [ffMonicDeg]

/-- There are exactly `p^d` monic polynomials of degree `d` (Finset version of
    `card_monic_of_degree`). -/
theorem ffMonicDeg_card (d : ℕ) : (ffMonicDeg p d).card = p ^ d := by
  have : Fintype ↑{f : Polynomial (ZMod p) | f.Monic ∧ f.natDegree = d} :=
    (monic_natDegree_finite (ZMod p) d).fintype
  rw [ffMonicDeg, Set.Finite.card_toFinset, ← card_monic_of_degree p d]
  exact Fintype.card_eq.mpr ⟨Equiv.refl _⟩

/-- Any filtered subfamily of monics of degree `d` has at most `p^d` elements. -/
theorem card_filter_ffMonicDeg_le (d : ℕ) (pred : Polynomial (ZMod p) → Prop) :
    ((ffMonicDeg p d).filter pred).card ≤ p ^ d := by
  calc ((ffMonicDeg p d).filter pred).card ≤ (ffMonicDeg p d).card :=
        Finset.card_filter_le _ _
    _ = p ^ d := ffMonicDeg_card p d

private theorem resLT_finite (D : ℕ) :
    Set.Finite {r : Polynomial (ZMod p) | r.degree < (D : WithBot ℕ)} := by
  apply Set.Finite.of_finite_image (f := fun r => X ^ D + r)
  · apply Set.Finite.subset (monic_natDegree_finite (ZMod p) D)
    rintro f ⟨r, hr, rfl⟩
    have hdX : degree (X ^ D : Polynomial (ZMod p)) = (D : WithBot ℕ) := degree_X_pow D
    have hmono : (X ^ D + r : Polynomial (ZMod p)).Monic :=
      (monic_X_pow D).add_of_left (by rw [hdX]; exact hr)
    refine ⟨hmono, ?_⟩
    have := Polynomial.natDegree_add_eq_left_of_degree_lt
      (p := (X ^ D : Polynomial (ZMod p))) (q := r) (by rw [hdX]; exact hr)
    rw [this, natDegree_X_pow]
  · intro r _ r' _ h
    exact add_left_cancel h

/-- The Finset of residue representatives of degree `< D` (all polynomials of
    degree `< D`, including `0`). -/
noncomputable def ffResLT (D : ℕ) : Finset (Polynomial (ZMod p)) :=
  (resLT_finite p D).toFinset

theorem mem_ffResLT {D : ℕ} {r : Polynomial (ZMod p)} :
    r ∈ ffResLT p D ↔ r.degree < (D : WithBot ℕ) := by
  simp [ffResLT]

/-- There are at most `p^D` residues of degree `< D` (injection `r ↦ X^D + r`
    into the monics of degree `D`). -/
theorem ffResLT_card_le (D : ℕ) : (ffResLT p D).card ≤ p ^ D := by
  rw [← ffMonicDeg_card p D]
  apply Finset.card_le_card_of_injOn (fun r => X ^ D + r)
  · intro r hr
    rw [Finset.mem_coe, mem_ffResLT] at hr
    have hdX : degree (X ^ D : Polynomial (ZMod p)) = (D : WithBot ℕ) := degree_X_pow D
    rw [Finset.mem_coe, mem_ffMonicDeg]
    constructor
    · exact (monic_X_pow D).add_of_left (by rw [hdX]; exact hr)
    · rw [Polynomial.natDegree_add_eq_left_of_degree_lt (by rw [hdX]; exact hr),
        natDegree_X_pow]
  · intro r _ r' _ h
    exact add_left_cancel h

end CountingFrames

/-! ## Part 2: Exact residue-class counts (the function-field luxury)

Over `F_p[t]` the distribution of monic polynomials in residue classes is EXACT:
for a monic modulus `N` and any residue `r`, exactly `p^(d - deg N)` monic
polynomials of degree `d ≥ deg N` are `≡ r (mod N)`. The proof is the division
algorithm bijection `g ↦ g·N + (r mod N)` — no error term, in contrast with the
`X/N + 2` bound `residue_class_count_le'` of `MixedEnsemble.lean` Part 18. -/

section ResidueCounts

variable {N : Polynomial (ZMod p)}

private theorem dvd_sub_modByMonic (r : Polynomial (ZMod p)) :
    N ∣ r - r %ₘ N := by
  have h := Polynomial.modByMonic_add_div r N
  exact ⟨r /ₘ N, by linear_combination -h⟩

/-- **Exact residue-class count** (division-algorithm bijection): for monic `N`
    with `deg N ≤ d`, exactly `p^(d - deg N)` monic polynomials of degree `d` lie
    in the residue class of `r` mod `N`. -/
theorem ffMonicDeg_residue_card (hN : N.Monic) (r : Polynomial (ZMod p)) {d : ℕ}
    (hd : N.natDegree ≤ d) :
    ((ffMonicDeg p d).filter (fun m => N ∣ m - r)).card = p ^ (d - N.natDegree) := by
  have hN0 : N ≠ 0 := hN.ne_zero
  have hrm : degree (r %ₘ N) < degree N := Polynomial.degree_modByMonic_lt r hN
  have hdegN : degree N = (N.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hN0
  rw [← ffMonicDeg_card p (d - N.natDegree)]
  apply Finset.card_bij' (i := fun m _ => (m - r %ₘ N) /ₘ N)
    (j := fun g _ => g * N + r %ₘ N)
  -- i maps into the target
  · intro m hm
    rw [Finset.mem_filter, mem_ffMonicDeg] at hm
    obtain ⟨⟨hmon, hmd⟩, hdvd⟩ := hm
    -- N divides m - r %ₘ N
    have hdvd' : N ∣ m - r %ₘ N := by
      have h1 : m - r %ₘ N = (m - r) + (r - r %ₘ N) := by ring
      rw [h1]
      exact dvd_add hdvd (dvd_sub_modByMonic p r)
    -- m - r %ₘ N is monic of degree d
    have hsub_monic : (m - r %ₘ N).Monic := by
      rw [sub_eq_add_neg]
      apply hmon.add_of_left
      rw [Polynomial.degree_neg, Polynomial.degree_eq_natDegree hmon.ne_zero, hmd]
      exact lt_of_lt_of_le hrm (by rw [hdegN]; exact_mod_cast hd)
    have hsub_deg : (m - r %ₘ N).natDegree = d := by
      rw [sub_eq_add_neg]
      rw [Polynomial.natDegree_add_eq_left_of_degree_lt, hmd]
      rw [Polynomial.degree_neg, Polynomial.degree_eq_natDegree hmon.ne_zero, hmd]
      exact lt_of_lt_of_le hrm (by rw [hdegN]; exact_mod_cast hd)
    -- write m - r %ₘ N = N * g
    have hfact : N * ((m - r %ₘ N) /ₘ N) = m - r %ₘ N := by
      have h0 : (m - r %ₘ N) %ₘ N = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hN).mpr hdvd'
      have h := Polynomial.modByMonic_add_div (m - r %ₘ N) N
      rw [h0, zero_add] at h
      exact h
    have hg_monic : ((m - r %ₘ N) /ₘ N).Monic := by
      apply hN.of_mul_monic_left
      rw [hfact]; exact hsub_monic
    rw [mem_ffMonicDeg]
    refine ⟨hg_monic, ?_⟩
    have := hN.natDegree_mul hg_monic
    rw [hfact, hsub_deg] at this
    omega
  -- j maps into the source
  · intro g hg
    rw [mem_ffMonicDeg] at hg
    obtain ⟨hgm, hgd⟩ := hg
    have hgN_monic : (g * N).Monic := hgm.mul hN
    have hgN_deg : (g * N).natDegree = d := by
      rw [hgm.natDegree_mul hN, hgd]; omega
    have hlt : degree (r %ₘ N) < degree (g * N) := by
      rw [Polynomial.degree_eq_natDegree hgN_monic.ne_zero, hgN_deg]
      exact lt_of_lt_of_le hrm (by rw [hdegN]; exact_mod_cast hd)
    rw [Finset.mem_filter, mem_ffMonicDeg]
    refine ⟨⟨hgN_monic.add_of_left hlt, ?_⟩, ?_⟩
    · rw [Polynomial.natDegree_add_eq_left_of_degree_lt hlt, hgN_deg]
    · have h1 : g * N + r %ₘ N - r = g * N - (r - r %ₘ N) := by ring
      rw [h1]
      exact dvd_sub (dvd_mul_left N g) (dvd_sub_modByMonic p r)
  -- left inverse
  · intro m hm
    rw [Finset.mem_filter, mem_ffMonicDeg] at hm
    obtain ⟨⟨hmon, hmd⟩, hdvd⟩ := hm
    have hdvd' : N ∣ m - r %ₘ N := by
      have h1 : m - r %ₘ N = (m - r) + (r - r %ₘ N) := by ring
      rw [h1]
      exact dvd_add hdvd (dvd_sub_modByMonic p r)
    have hfact : N * ((m - r %ₘ N) /ₘ N) = m - r %ₘ N := by
      have h0 : (m - r %ₘ N) %ₘ N = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hN).mpr hdvd'
      have h := Polynomial.modByMonic_add_div (m - r %ₘ N) N
      rw [h0, zero_add] at h
      exact h
    calc (m - r %ₘ N) /ₘ N * N + r %ₘ N
        = N * ((m - r %ₘ N) /ₘ N) + r %ₘ N := by ring
      _ = (m - r %ₘ N) + r %ₘ N := by rw [hfact]
      _ = m := by ring
  -- right inverse
  · intro g hg
    rw [mem_ffMonicDeg] at hg
    obtain ⟨hgm, _⟩ := hg
    have h1 : g * N + r %ₘ N - r %ₘ N = N * g := by ring
    rw [h1]
    -- (N * g) /ₘ N = g
    have h0 : (N * g) %ₘ N = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hN).mpr ⟨g, rfl⟩
    have h := Polynomial.modByMonic_add_div (N * g) N
    rw [h0, zero_add] at h
    exact mul_left_cancel₀ hN.ne_zero h

/-- If `N ∣ x - r` and `deg r < deg N`, then `r` is the canonical remainder of
    `x` mod `N`. -/
private theorem modByMonic_eq_of_dvd_sub (hN : N.Monic) {x r : Polynomial (ZMod p)}
    (hdvd : N ∣ x - r) (hr : degree r < degree N) : x %ₘ N = r := by
  have hdvd' : N ∣ x %ₘ N - r := by
    have h1 : x %ₘ N - r = (x - r) - (x - x %ₘ N) := by ring
    rw [h1]
    exact dvd_sub hdvd (dvd_sub_modByMonic p x)
  by_contra hne
  have hne0 : x %ₘ N - r ≠ 0 := sub_ne_zero.mpr hne
  have hlt : degree (x %ₘ N - r) < degree N :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
      (max_lt (Polynomial.degree_modByMonic_lt x hN) hr)
  exact absurd (Polynomial.degree_le_of_dvd hdvd' hne0) (not_le.mpr hlt)

end ResidueCounts

/-! ## Part 3: Squarefree lower bound (quarter bound)

FF analogue of `sqfreeCount_ge_quarter`: at least a quarter of the monic
polynomials of each degree `d ≥ 1` are squarefree. The non-squarefree ones are
covered by the multiples of `P^2` over monic irreducibles `P` of degree
`e ≤ d/2`; the exact residue count gives `p^(d-2e)` multiples each, and the
irreducible count bound `π(e) ≤ p^e/e` makes the total at most `(3/4)·p^d`. -/

section SquarefreeBound

/-- The Finset of monic irreducible polynomials of degree exactly `d`. -/
noncomputable def ffIrredDeg (d : ℕ) : Finset (Polynomial (ZMod p)) :=
  (ffMonicDeg p d).filter (fun P => Irreducible P)

theorem mem_ffIrredDeg {d : ℕ} {P : Polynomial (ZMod p)} :
    P ∈ ffIrredDeg p d ↔ P.Monic ∧ Irreducible P ∧ P.natDegree = d := by
  simp only [ffIrredDeg, Finset.mem_filter, mem_ffMonicDeg]
  tauto

/-- Bridge to the subtype count of `IrreducibilityDensity.lean`:
    `π(d) ≤ p^d / d`. -/
theorem ffIrredDeg_card_le (d : ℕ) (hd : 0 < d) :
    (ffIrredDeg p d).card ≤ p ^ d / d := by
  have heq : ffIrredDeg p d =
      Set.toFinset {Q : Polynomial (ZMod p) | Q.Monic ∧ Irreducible Q ∧ Q.natDegree = d} := by
    ext P
    rw [mem_ffIrredDeg, Set.mem_toFinset, Set.mem_ofPred_eq]
  rw [heq, Set.toFinset_card]
  exact ff_irreducible_count_le p d hd

/-- Trivial bound `π(d) ≤ p^d`. -/
theorem ffIrredDeg_card_le_pow (d : ℕ) : (ffIrredDeg p d).card ≤ p ^ d :=
  card_filter_ffMonicDeg_le p d _

/-- The count of monic squarefree polynomials of degree exactly `d`. -/
noncomputable def ffSqfreeDegCount (d : ℕ) : ℕ :=
  ((ffMonicDeg p d).filter (fun m => Squarefree m)).card

/-- The count of monic squarefree polynomials of degree `1 ≤ deg ≤ n` — the
    denominator frame of the density statement (degree-`0` constants are
    excluded: they are not valid walk starting points). -/
noncomputable def ffSqfreeCount (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 n, ffSqfreeDegCount p d

/-- Multiples of `P^2` among monics of degree `d` number exactly `p^(d - 2·deg P)`
    (specialization of the exact residue count at `r = 0`). -/
private theorem sq_multiples_card {P : Polynomial (ZMod p)} (hPm : P.Monic)
    {d : ℕ} (hd : 2 * P.natDegree ≤ d) :
    ((ffMonicDeg p d).filter (fun m => P ^ 2 ∣ m)).card = p ^ (d - 2 * P.natDegree) := by
  have h := ffMonicDeg_residue_card p (hPm.pow 2) (0 : Polynomial (ZMod p))
    (d := d) (by rw [Polynomial.natDegree_pow]; omega)
  simp only [sub_zero] at h
  rwa [Polynomial.natDegree_pow] at h

/-- Every non-squarefree monic polynomial of degree `d` is a multiple of `P^2`
    for some monic irreducible `P` of degree `e` with `2e ≤ d`. -/
private theorem nonsqfree_subset_cover (d : ℕ) :
    (ffMonicDeg p d).filter (fun m => ¬ Squarefree m) ⊆
      (Finset.Icc 1 (d / 2)).biUnion (fun e => (ffIrredDeg p e).biUnion
        (fun P => (ffMonicDeg p d).filter (fun m => P ^ 2 ∣ m))) := by
  intro m hm
  rw [Finset.mem_filter, mem_ffMonicDeg] at hm
  obtain ⟨⟨hmon, hmd⟩, hnsf⟩ := hm
  rw [Squarefree] at hnsf
  push Not at hnsf
  obtain ⟨x, hxx, hxu⟩ := hnsf
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_dvd_iff] at hxx
    exact hmon.ne_zero hxx
  obtain ⟨P, hPm, hPi, hPx⟩ := Polynomial.exists_monic_irreducible_factor x
    (fun hu => hxu hu)
  have hP2 : P ^ 2 ∣ m := by
    calc P ^ 2 = P * P := sq P
      _ ∣ x * x := mul_dvd_mul hPx hPx
      _ ∣ m := hxx
  have hPd : 0 < P.natDegree := hPi.natDegree_pos
  have h2e : 2 * P.natDegree ≤ d := by
    have hne : P ^ 2 ≠ 0 := pow_ne_zero 2 hPi.ne_zero
    have := Polynomial.natDegree_le_of_dvd hP2 hmon.ne_zero
    rw [Polynomial.natDegree_pow, hmd] at this
    omega
  rw [Finset.mem_biUnion]
  refine ⟨P.natDegree, ?_, ?_⟩
  · rw [Finset.mem_Icc]
    omega
  · rw [Finset.mem_biUnion]
    exact ⟨P, (mem_ffIrredDeg p).mpr ⟨hPm, hPi, rfl⟩,
      Finset.mem_filter.mpr ⟨(mem_ffMonicDeg p).mpr ⟨hmon, hmd⟩, hP2⟩⟩

/-- **Quarter bound** (unconditional): `p^d ≤ 4 · #\{monic squarefree of degree d\}`
    for every `d ≥ 1`. FF analogue of `sqfreeCount_ge_quarter_nat`. -/
theorem ffSqfreeDegCount_quarter (d : ℕ) (hd : 1 ≤ d) :
    p ^ d ≤ 4 * ffSqfreeDegCount p d := by
  have hp2 : 2 ≤ p := p_two_le p
  -- split monics into squarefree and non-squarefree
  have hsplit : ffSqfreeDegCount p d +
      ((ffMonicDeg p d).filter (fun m => ¬ Squarefree m)).card = p ^ d := by
    rw [ffSqfreeDegCount, ← ffMonicDeg_card p d]
    exact Finset.card_filter_add_card_filter_not _
  -- bound the non-squarefree count
  set NS := ((ffMonicDeg p d).filter (fun m => ¬ Squarefree m)).card with hNS
  have hcover : NS ≤ ∑ e ∈ Finset.Icc 1 (d / 2), (ffIrredDeg p e).card * p ^ (d - 2 * e) := by
    calc NS ≤ ((Finset.Icc 1 (d / 2)).biUnion (fun e => (ffIrredDeg p e).biUnion
          (fun P => (ffMonicDeg p d).filter (fun m => P ^ 2 ∣ m)))).card :=
          Finset.card_le_card (nonsqfree_subset_cover p d)
      _ ≤ ∑ e ∈ Finset.Icc 1 (d / 2), ((ffIrredDeg p e).biUnion
          (fun P => (ffMonicDeg p d).filter (fun m => P ^ 2 ∣ m))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ e ∈ Finset.Icc 1 (d / 2), (ffIrredDeg p e).card * p ^ (d - 2 * e) := by
          apply Finset.sum_le_sum
          intro e he
          rw [Finset.mem_Icc] at he
          calc ((ffIrredDeg p e).biUnion
              (fun P => (ffMonicDeg p d).filter (fun m => P ^ 2 ∣ m))).card
              ≤ ∑ P ∈ ffIrredDeg p e, ((ffMonicDeg p d).filter (fun m => P ^ 2 ∣ m)).card :=
                Finset.card_biUnion_le
            _ = ∑ P ∈ ffIrredDeg p e, p ^ (d - 2 * e) := by
                apply Finset.sum_congr rfl
                intro P hP
                obtain ⟨hPm, _, hPd⟩ := (mem_ffIrredDeg p).mp hP
                rw [← hPd] at he ⊢
                exact sq_multiples_card p hPm (by omega)
            _ = (ffIrredDeg p e).card * p ^ (d - 2 * e) := by
                rw [Finset.sum_const, smul_eq_mul]
  -- degree-1 case: no room for a square factor
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · -- d = 1
    have hd1 : d = 1 := by omega
    subst hd1
    rw [show (1 : ℕ) / 2 = 0 by norm_num, Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, Nat.le_zero] at hcover
    omega
  -- d ≥ 2: term e = 1 contributes ≤ p^(d-1); terms e ≥ 2 contribute ≤ p^(d-1)/2 · 2
  · have hterm1 : (ffIrredDeg p 1).card * p ^ (d - 2 * 1) ≤ p ^ (d - 1) := by
      calc (ffIrredDeg p 1).card * p ^ (d - 2 * 1)
          ≤ p ^ 1 * p ^ (d - 2) := by
            exact Nat.mul_le_mul_right _ (ffIrredDeg_card_le_pow p 1)
        _ = p ^ (d - 1) := by
            rw [← pow_add]
            congr 1
            omega
    have htail : 2 * ∑ e ∈ Finset.Icc 2 (d / 2), (ffIrredDeg p e).card * p ^ (d - 2 * e)
        ≤ p ^ (d - 1) := by
      have hstep : ∀ e ∈ Finset.Icc 2 (d / 2),
          2 * ((ffIrredDeg p e).card * p ^ (d - 2 * e)) ≤ p ^ (d - e) := by
        intro e he
        rw [Finset.mem_Icc] at he
        have hcard : (ffIrredDeg p e).card ≤ p ^ e / 2 := by
          calc (ffIrredDeg p e).card ≤ p ^ e / e := ffIrredDeg_card_le p e (by omega)
            _ ≤ p ^ e / 2 := Nat.div_le_div_left he.1 (by omega)
        calc 2 * ((ffIrredDeg p e).card * p ^ (d - 2 * e))
            ≤ 2 * (p ^ e / 2) * p ^ (d - 2 * e) := by
              rw [mul_assoc]
              exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcard)
          _ ≤ p ^ e * p ^ (d - 2 * e) := by
              have h2 : 2 * (p ^ e / 2) ≤ p ^ e := by omega
              exact Nat.mul_le_mul_right _ h2
          _ = p ^ (d - e) := by
              rw [← pow_add]
              congr 1
              have := Nat.div_mul_le_self d 2
              omega
      calc 2 * ∑ e ∈ Finset.Icc 2 (d / 2), (ffIrredDeg p e).card * p ^ (d - 2 * e)
          = ∑ e ∈ Finset.Icc 2 (d / 2), 2 * ((ffIrredDeg p e).card * p ^ (d - 2 * e)) := by
            rw [Finset.mul_sum]
        _ ≤ ∑ e ∈ Finset.Icc 2 (d / 2), p ^ (d - e) := Finset.sum_le_sum hstep
        _ = ∑ j ∈ (Finset.Icc 2 (d / 2)).image (fun e => d - e), p ^ j := by
            rw [Finset.sum_image]
            intro e he e' he' h
            simp only [Finset.mem_coe, Finset.mem_Icc] at he he'
            have h : d - e = d - e' := h
            have h2 : 2 * e ≤ d := by
              have := Nat.div_mul_le_self d 2
              omega
            have h2' : 2 * e' ≤ d := by
              have := Nat.div_mul_le_self d 2
              omega
            omega
        _ ≤ ∑ j ∈ Finset.range (d - 1), p ^ j := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              rw [Finset.mem_image] at hj
              obtain ⟨e, he, rfl⟩ := hj
              rw [Finset.mem_Icc] at he
              rw [Finset.mem_range]
              omega
            · intro j _ _
              positivity
        _ ≤ p ^ (d - 1) := geom_sum_le p (d - 1)
    -- assemble: 2·NS ≤ 2·p^(d-1) + p^(d-1) = 3·p^(d-1), and 6·p^(d-1) ≤ 3·p^d
    have hIcc : Finset.Icc 1 (d / 2) = insert 1 (Finset.Icc 2 (d / 2)) := by
      ext e
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h1mem : (1 : ℕ) ∉ Finset.Icc 2 (d / 2) := by
      rw [Finset.mem_Icc]; omega
    rw [hIcc, Finset.sum_insert h1mem] at hcover
    have hNS3 : 2 * NS ≤ 3 * p ^ (d - 1) := by
      have := hterm1
      omega
    have hpd : p ^ d = p * p ^ (d - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hp_pos : 0 < p ^ (d - 1) := pow_pos (by omega) _
    -- 4·(p^d − NS) ≥ p^d  ⟺  4·NS ≤ 3·p^d
    have h4NS : 4 * NS ≤ 3 * p ^ d := by
      calc 4 * NS = 2 * (2 * NS) := by ring
        _ ≤ 2 * (3 * p ^ (d - 1)) := by omega
        _ = 6 * p ^ (d - 1) := by ring
        _ ≤ 3 * (p * p ^ (d - 1)) := by nlinarith
        _ = 3 * p ^ d := by rw [← hpd]
    omega

/-- Positivity of the squarefree frame for `n ≥ 1`. -/
theorem ffSqfreeCount_pos (n : ℕ) (hn : 1 ≤ n) : 0 < ffSqfreeCount p n := by
  have h1 : 0 < ffSqfreeDegCount p 1 := by
    have := ffSqfreeDegCount_quarter p 1 le_rfl
    have hp2 : 2 ≤ p := p_two_le p
    have : 0 < p ^ 1 := by positivity
    omega
  calc 0 < ffSqfreeDegCount p 1 := h1
    _ ≤ ∑ d ∈ Finset.Icc 1 n, ffSqfreeDegCount p d :=
      Finset.single_le_sum (fun d _ => Nat.zero_le _) (by rw [Finset.mem_Icc]; omega)

/-- Real-valued lower bound: `p^n / 4 ≤ ffSqfreeCount p n` for `n ≥ 1`. -/
theorem ffSqfreeCount_ge_real (n : ℕ) (hn : 1 ≤ n) :
    (p : ℝ) ^ n / 4 ≤ (ffSqfreeCount p n : ℝ) := by
  have h1 : (p : ℝ) ^ n ≤ 4 * (ffSqfreeDegCount p n : ℝ) := by
    exact_mod_cast ffSqfreeDegCount_quarter p n hn
  have h2 : (ffSqfreeDegCount p n : ℝ) ≤ (ffSqfreeCount p n : ℝ) := by
    exact_mod_cast Finset.single_le_sum (f := fun d => ffSqfreeDegCount p d)
      (fun d _ => Nat.zero_le _) (by rw [Finset.mem_Icc]; omega)
  linarith

end SquarefreeBound

/-! ## Part 4: Greedy completion and walk extension

Any prefix of a valid mixed selection can be modified at one step: if `P` is a
monic irreducible factor of `walk + 1` at step `n`, there is a valid selection
that agrees with the original strictly before step `n`, selects `P` at step `n`,
and continues greedily afterwards (choosing an arbitrary monic irreducible factor
at each later step, which always exists since the accumulator stays monic of
positive degree). This gives the two structural facts the sieve needs:

* `ff_reachable_of_walk_dvd`: `Q ∣ walk + 1` at any step forces `ffTreeReachable`;
* `ff_factor_reachable`: every monic irreducible factor `P ∣ m + 1` puts the
  residue `(m * P) %ₘ Q` into the reachable set `ffReachableEver`. -/

section WalkExtension

/-- Choice of a monic irreducible factor (junk value `X` on units). -/
private noncomputable def ffPick (f : Polynomial (ZMod p)) : Polynomial (ZMod p) :=
  if h : IsUnit f then X else Classical.choose (f.exists_monic_irreducible_factor h)

private theorem ffPick_spec {f : Polynomial (ZMod p)} (hf : ¬IsUnit f) :
    (ffPick p f).Monic ∧ Irreducible (ffPick p f) ∧ ffPick p f ∣ f := by
  rw [ffPick, dif_neg hf]
  exact Classical.choose_spec (f.exists_monic_irreducible_factor hf)

/-- The greedy accumulator from seed `a`: multiply by a chosen monic irreducible
    factor of `acc + 1` at each step. -/
private noncomputable def ffGreedyAcc (a : Polynomial (ZMod p)) : ℕ → Polynomial (ZMod p)
  | 0 => a
  | k + 1 => ffGreedyAcc a k * ffPick p (ffGreedyAcc a k + 1)

private theorem ffGreedyAcc_monic {a : Polynomial (ZMod p)} (ha : a.Monic)
    (ha' : 0 < a.natDegree) :
    ∀ k, (ffGreedyAcc p a k).Monic ∧ 0 < (ffGreedyAcc p a k).natDegree := by
  intro k
  induction k with
  | zero => exact ⟨ha, ha'⟩
  | succ k ih =>
    have hsucc := monic_add_one p ih.1 ih.2
    have hnu : ¬IsUnit (ffGreedyAcc p a k + 1) :=
      Polynomial.not_isUnit_of_natDegree_pos _ (by rw [hsucc.2]; exact ih.2)
    have hpick := ffPick_spec p hnu
    constructor
    · exact ih.1.mul hpick.1
    · rw [show ffGreedyAcc p a (k + 1) =
        ffGreedyAcc p a k * ffPick p (ffGreedyAcc p a k + 1) from rfl,
        ih.1.natDegree_mul hpick.1]
      omega

/-- The accumulator at each greedy step is not a unit after adding one. -/
private theorem ffGreedyAcc_succ_not_unit {a : Polynomial (ZMod p)} (ha : a.Monic)
    (ha' : 0 < a.natDegree) (k : ℕ) : ¬IsUnit (ffGreedyAcc p a k + 1) := by
  have h := ffGreedyAcc_monic p ha ha' k
  have hsucc := monic_add_one p h.1 h.2
  exact Polynomial.not_isUnit_of_natDegree_pos _ (by rw [hsucc.2]; exact h.2)

/-- The all-greedy selection from a starting point. -/
private noncomputable def ffGreedySel (m : Polynomial (ZMod p)) : FFMixedSelection p :=
  ⟨fun k => ffPick p (ffGreedyAcc p m k + 1)⟩

private theorem ffGreedySel_walkProd (m : Polynomial (ZMod p)) :
    ∀ k, ffMixedWalkProd p m (ffGreedySel p m) k = ffGreedyAcc p m k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [ffMixedWalkProd_succ, ih]; rfl

/-- Valid mixed selections exist from every monic starting point of positive
    degree: the greedy selection is valid. -/
private theorem ffGreedySel_valid {m : Polynomial (ZMod p)} (hm : m.Monic)
    (hd : 0 < m.natDegree) : FFMixedSelectionValid p m (ffGreedySel p m) := by
  refine ⟨hm, hd, fun n => ?_⟩
  rw [show (ffGreedySel p m).sel n = ffPick p (ffGreedyAcc p m n + 1) from rfl,
    ffGreedySel_walkProd]
  exact ffPick_spec p (ffGreedyAcc_succ_not_unit p hm hd n)

/-- The extension of `σ` at step `n` by the factor `P`: agree with `σ` strictly
    before `n`, select `P` at step `n`, continue greedily afterwards. -/
private noncomputable def ffExtSel (m : Polynomial (ZMod p)) (σ : FFMixedSelection p)
    (n : ℕ) (P : Polynomial (ZMod p)) : FFMixedSelection p :=
  ⟨fun k => if k < n then σ.sel k
    else if k = n then P
    else ffPick p (ffGreedyAcc p (ffMixedWalkProd p m σ n * P) (k - n - 1) + 1)⟩

private theorem ffExtSel_sel (m : Polynomial (ZMod p)) (σ : FFMixedSelection p)
    (n : ℕ) (P : Polynomial (ZMod p)) (k : ℕ) :
    (ffExtSel p m σ n P).sel k = if k < n then σ.sel k
      else if k = n then P
      else ffPick p (ffGreedyAcc p (ffMixedWalkProd p m σ n * P) (k - n - 1) + 1) := rfl

private theorem ffExtSel_walkProd (m : Polynomial (ZMod p)) (σ : FFMixedSelection p)
    (n : ℕ) (P : Polynomial (ZMod p)) :
    ∀ k, ffMixedWalkProd p m (ffExtSel p m σ n P) k =
      if k ≤ n then ffMixedWalkProd p m σ k
      else ffGreedyAcc p (ffMixedWalkProd p m σ n * P) (k - n - 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ffMixedWalkProd_succ, ih, ffExtSel_sel]
    by_cases h1 : k + 1 ≤ n
    · rw [if_pos (by omega : k ≤ n), if_pos h1, if_pos (by omega : k < n),
        ← ffMixedWalkProd_succ]
    · by_cases h2 : k = n
      · subst h2
        rw [if_pos le_rfl, if_neg h1, if_neg (lt_irrefl k), if_pos rfl,
          show k + 1 - k - 1 = 0 from by omega]
        rfl
      · have hk : n < k := by omega
        rw [if_neg (by omega : ¬k ≤ n), if_neg h1, if_neg (by omega : ¬k < n),
          if_neg h2, show k + 1 - n - 1 = (k - n - 1) + 1 from by omega]
        rfl

private theorem ffExtSel_valid {m : Polynomial (ZMod p)} {σ : FFMixedSelection p}
    (hv : FFMixedSelectionValid p m σ) {n : ℕ} {P : Polynomial (ZMod p)}
    (hPm : P.Monic) (hPi : Irreducible P)
    (hdvd : P ∣ ffMixedWalkProd p m σ n + 1) :
    FFMixedSelectionValid p m (ffExtSel p m σ n P) := by
  have hseedm : (ffMixedWalkProd p m σ n * P).Monic :=
    (ffMixedWalkProd_monic hv n).mul hPm
  have hseedd : 0 < (ffMixedWalkProd p m σ n * P).natDegree := by
    rw [(ffMixedWalkProd_monic hv n).natDegree_mul hPm]
    have := ffMixedWalkProd_natDegree_pos hv n
    omega
  refine ⟨hv.1, hv.2.1, fun k => ?_⟩
  rw [ffExtSel_sel, ffExtSel_walkProd]
  by_cases h1 : k < n
  · rw [if_pos h1, if_pos (by omega : k ≤ n)]
    exact hv.2.2 k
  · by_cases h2 : k = n
    · subst h2
      rw [if_neg (lt_irrefl k), if_pos rfl, if_pos le_rfl]
      exact ⟨hPm, hPi, hdvd⟩
    · have hk : n < k := by omega
      rw [if_neg h1, if_neg h2, if_neg (by omega : ¬k ≤ n)]
      exact ffPick_spec p (ffGreedyAcc_succ_not_unit p hseedm hseedd (k - n - 1))

/-- **Walk extension**: if `Q` (monic irreducible) divides `walk + 1` at any step
    of any valid selection from `m`, then `Q` is `ffTreeReachable` from `m`. -/
theorem ff_reachable_of_walk_dvd {m Q : Polynomial (ZMod p)} {σ : FFMixedSelection p}
    (hv : FFMixedSelectionValid p m σ) (hQm : Q.Monic) (hQi : Irreducible Q)
    {n : ℕ} (hdvd : Q ∣ ffMixedWalkProd p m σ n + 1) :
    ffTreeReachable p m Q :=
  Or.inr ⟨ffExtSel p m σ n Q, ffExtSel_valid p hv hQm hQi hdvd,
    ⟨n, by rw [ffExtSel_sel, if_neg (lt_irrefl n), if_pos rfl]⟩⟩

/-- The set of residues mod `Q` visited by some valid mixed walk from `start`
    at some step (FF analogue of `reachableEver`). Residue representatives are
    canonical remainders `walk %ₘ Q`, so all members have degree `< deg Q`. -/
def ffReachableEver (start Q : Polynomial (ZMod p)) : Set (Polynomial (ZMod p)) :=
  {r | ∃ σ : FFMixedSelection p, FFMixedSelectionValid p start σ ∧
    ∃ n : ℕ, ffMixedWalkProd p start σ n %ₘ Q = r}

theorem ffReachableEver_finite (start : Polynomial (ZMod p)) {Q : Polynomial (ZMod p)}
    (hQm : Q.Monic) : (ffReachableEver p start Q).Finite := by
  apply (resLT_finite p Q.natDegree).subset
  rintro r ⟨σ, hv, n, rfl⟩
  have h := Polynomial.degree_modByMonic_lt (ffMixedWalkProd p start σ n) hQm
  rwa [Polynomial.degree_eq_natDegree hQm.ne_zero] at h

/-- If the residue of `-1` is reachable, then `Q` is tree-reachable: the walk
    step with `walk ≡ -1 (mod Q)` has `Q ∣ walk + 1`, so `ff_reachable_of_walk_dvd`
    applies. -/
theorem ff_treeReachable_of_neg_one_mem {m Q : Polynomial (ZMod p)}
    (hQm : Q.Monic) (hQi : Irreducible Q)
    (h : (-1 : Polynomial (ZMod p)) ∈ ffReachableEver p m Q) :
    ffTreeReachable p m Q := by
  obtain ⟨σ, hv, n, hmod⟩ := h
  have hdvd : Q ∣ ffMixedWalkProd p m σ n + 1 := by
    have h1 := dvd_sub_modByMonic p (N := Q) (ffMixedWalkProd p m σ n)
    rw [hmod, sub_neg_eq_add] at h1
    exact h1
  exact ff_reachable_of_walk_dvd p hv hQm hQi hdvd

/-- **Step-0 factor confinement**: every monic irreducible factor `P` of `m + 1`
    moves the walk to position `m * P`, so `(m * P) %ₘ Q` is a reachable residue. -/
theorem ff_factor_reachable {m : Polynomial (ZMod p)} (Q : Polynomial (ZMod p))
    (hm : m.Monic) (hd : 0 < m.natDegree) {P : Polynomial (ZMod p)}
    (hPm : P.Monic) (hPi : Irreducible P) (hdvd : P ∣ m + 1) :
    (m * P) %ₘ Q ∈ ffReachableEver p m Q := by
  have hv := ffGreedySel_valid p hm hd
  have hdvd0 : P ∣ ffMixedWalkProd p m (ffGreedySel p m) 0 + 1 := hdvd
  refine ⟨ffExtSel p m (ffGreedySel p m) 0 P, ffExtSel_valid p hv hPm hPi hdvd0, 1, ?_⟩
  rw [ffExtSel_walkProd, if_neg (by omega : ¬(1 : ℕ) ≤ 0)]
  rfl

end WalkExtension

/-! ## Part 5: Confinement counts and the pigeonhole over proper residue subsets

A trapped starting point `m` (monic squarefree, `Q ∤ m`, `Q` not tree-reachable)
has its reachable residue set `ffReachableEver p m Q` missing the nonzero residue
`-1` (else `ff_treeReachable_of_neg_one_mem` fires). At step 0 every monic
irreducible factor `P ∣ m + 1` has `(m * P) %ₘ Q` reachable, so `m` is confined
to the proper subset `R = ffReachableEver`. Pigeonholing over the finitely many
subsets of the residue Finset `ffResLT p (deg Q)` that miss a nonzero residue
bounds the trapped count by a finite sum of confined counts. -/

section ConfinementCounts

/-- Congruent polynomials have equal canonical remainders. -/
private theorem modByMonic_congr {N : Polynomial (ZMod p)} (hN : N.Monic)
    {x y : Polynomial (ZMod p)} (h : N ∣ x - y) : x %ₘ N = y %ₘ N := by
  apply modByMonic_eq_of_dvd_sub p hN _ (Polynomial.degree_modByMonic_lt y hN)
  have h1 : x - y %ₘ N = (x - y) + (y - y %ₘ N) := by ring
  rw [h1]
  exact dvd_add h (dvd_sub_modByMonic p y)

/-- Equal canonical remainders give a congruence. -/
private theorem dvd_sub_of_modByMonic_eq {N : Polynomial (ZMod p)}
    {x y : Polynomial (ZMod p)} (h : x %ₘ N = y %ₘ N) : N ∣ x - y := by
  have h' := dvd_sub (dvd_sub_modByMonic p (N := N) x) (dvd_sub_modByMonic p (N := N) y)
  rw [h] at h'
  have heq : x - y %ₘ N - (y - y %ₘ N) = x - y := by ring
  rwa [heq] at h'

/-- The allowed factor residues at walk position `c` for target subset `R`:
    factors `P` whose product position `(c * P) %ₘ Q` lies in `R`. -/
def ffAllowedFactors (Q c : Polynomial (ZMod p)) (R : Finset (Polynomial (ZMod p))) :
    Set (Polynomial (ZMod p)) :=
  {P | (c * P) %ₘ Q ∈ R}

/-- All monic irreducible factors of `N` lie in the set `F`. -/
def FFAllFactorsIn (N : Polynomial (ZMod p)) (F : Set (Polynomial (ZMod p))) : Prop :=
  ∀ P : Polynomial (ZMod p), P.Monic → Irreducible P → P ∣ N → P ∈ F

/-- Count of trapped starting points of degree exactly `d`: monic squarefree `m`
    with `Q ∤ m` from which `Q` is not tree-reachable. -/
noncomputable def ffTrappedDegCount (Q : Polynomial (ZMod p)) (d : ℕ) : ℕ :=
  ((ffMonicDeg p d).filter (fun m => Squarefree m ∧ ¬Q ∣ m ∧
    ¬ffTreeReachable p m Q)).card

/-- Total trapped count over degrees `1 ≤ deg ≤ n` (numerator of the trapped
    density). -/
noncomputable def ffTrappedCount (Q : Polynomial (ZMod p)) (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 n, ffTrappedDegCount p Q d

/-- Count of confined starting points of degree exactly `d`: monic squarefree `m`
    with `Q ∤ m` all of whose step-0 factor moves land in `R`. -/
noncomputable def ffConfinedDegCount (Q : Polynomial (ZMod p))
    (R : Finset (Polynomial (ZMod p))) (d : ℕ) : ℕ :=
  ((ffMonicDeg p d).filter (fun m => Squarefree m ∧ ¬Q ∣ m ∧
    FFAllFactorsIn p (m + 1) (ffAllowedFactors p Q m R))).card

/-- Total confined count over degrees `1 ≤ deg ≤ n`. -/
noncomputable def ffConfinedCount (Q : Polynomial (ZMod p))
    (R : Finset (Polynomial (ZMod p))) (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 n, ffConfinedDegCount p Q R d

/-- Trapped starting points are squarefree, so the trapped count is dominated by
    the squarefree frame degree by degree. -/
theorem ffTrappedDegCount_le (Q : Polynomial (ZMod p)) (d : ℕ) :
    ffTrappedDegCount p Q d ≤ ffSqfreeDegCount p d := by
  apply Finset.card_le_card
  intro m hm
  rw [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, hm.2.1⟩

theorem ffTrappedCount_le (Q : Polynomial (ZMod p)) (n : ℕ) :
    ffTrappedCount p Q n ≤ ffSqfreeCount p n :=
  Finset.sum_le_sum fun d _ => ffTrappedDegCount_le p Q d

/-- The finite family of residue subsets used in the pigeonhole: subsets of the
    residues of degree `< deg Q` that miss at least one nonzero residue. -/
noncomputable def ffProperSubsets (Q : Polynomial (ZMod p)) :
    Finset (Finset (Polynomial (ZMod p))) :=
  (ffResLT p Q.natDegree).powerset.filter
    (fun R => ∃ a ∈ ffResLT p Q.natDegree, a ≠ 0 ∧ a ∉ R)

/-- **Per-degree pigeonhole**: each trapped `m` is confined to the proper subset
    `ffReachableEver p m Q`, so the trapped count is bounded by the sum of
    confined counts over all proper residue subsets. -/
theorem ff_trapped_deg_le_sum_confined {Q : Polynomial (ZMod p)}
    (hQm : Q.Monic) (hQi : Irreducible Q) {d : ℕ} (hd : 1 ≤ d) :
    ffTrappedDegCount p Q d ≤
      ∑ R ∈ ffProperSubsets p Q, ffConfinedDegCount p Q R d := by
  have hDq : 0 < Q.natDegree := hQi.natDegree_pos
  calc ffTrappedDegCount p Q d
      ≤ ((ffProperSubsets p Q).biUnion (fun R =>
          (ffMonicDeg p d).filter (fun m => Squarefree m ∧ ¬Q ∣ m ∧
            FFAllFactorsIn p (m + 1) (ffAllowedFactors p Q m R)))).card := by
        apply Finset.card_le_card
        intro m hm
        rw [Finset.mem_filter, mem_ffMonicDeg] at hm
        obtain ⟨⟨hmon, hmd⟩, hsf, hndvd, hnreach⟩ := hm
        have hmpos : 0 < m.natDegree := by omega
        set Rm := (ffReachableEver_finite p m hQm).toFinset with hRm
        rw [Finset.mem_biUnion]
        refine ⟨Rm, ?_, ?_⟩
        · -- Rm is a proper subset
          rw [ffProperSubsets, Finset.mem_filter, Finset.mem_powerset]
          constructor
          · intro r hr
            rw [hRm, Set.Finite.mem_toFinset] at hr
            obtain ⟨σ, hv, k, rfl⟩ := hr
            rw [mem_ffResLT]
            have h := Polynomial.degree_modByMonic_lt (ffMixedWalkProd p m σ k) hQm
            rwa [Polynomial.degree_eq_natDegree hQm.ne_zero] at h
          · refine ⟨-1, ?_, neg_ne_zero.mpr one_ne_zero, ?_⟩
            · rw [mem_ffResLT, Polynomial.degree_neg, Polynomial.degree_one]
              exact_mod_cast hDq
            · rw [hRm, Set.Finite.mem_toFinset]
              intro hmem
              exact hnreach (ff_treeReachable_of_neg_one_mem p hQm hQi hmem)
        · -- m is confined to Rm
          rw [Finset.mem_filter, mem_ffMonicDeg]
          refine ⟨⟨hmon, hmd⟩, hsf, hndvd, ?_⟩
          intro P hPm hPi hPdvd
          show (m * P) %ₘ Q ∈ Rm
          rw [hRm, Set.Finite.mem_toFinset]
          exact ff_factor_reachable p Q hmon hmpos hPm hPi hPdvd
    _ ≤ ∑ R ∈ ffProperSubsets p Q, ffConfinedDegCount p Q R d :=
        Finset.card_biUnion_le

/-- **Pigeonhole over proper residue subsets**: the trapped count is bounded by
    the sum of confined counts over the (finitely many) proper residue subsets. -/
theorem ff_trapped_le_sum_confined {Q : Polynomial (ZMod p)}
    (hQm : Q.Monic) (hQi : Irreducible Q) (n : ℕ) :
    ffTrappedCount p Q n ≤ ∑ R ∈ ffProperSubsets p Q, ffConfinedCount p Q R n := by
  rw [ffTrappedCount]
  calc ∑ d ∈ Finset.Icc 1 n, ffTrappedDegCount p Q d
      ≤ ∑ d ∈ Finset.Icc 1 n, ∑ R ∈ ffProperSubsets p Q, ffConfinedDegCount p Q R d := by
        apply Finset.sum_le_sum
        intro d hd
        rw [Finset.mem_Icc] at hd
        exact ff_trapped_deg_le_sum_confined p hQm hQi hd.1
    _ = ∑ R ∈ ffProperSubsets p Q, ffConfinedCount p Q R n := Finset.sum_comm

end ConfinementCounts

/-! ## Part 6: The exact congruence sieve

Counting monics of degree `d` whose shift `m + 1` avoids every modulus in a
finite set `S` of monic irreducibles. Over `F_p[t]` this is EXACT: partitioning
by the residue `m %ₘ ∏ S` and using the exact residue-class count of Part 2,
the sieved count is at most `#good residues × p^(d - deg ∏S)`, and the good
residues mod `∏ S` inject into the product of the per-modulus good residues by
CRT (coprimality of distinct monic irreducibles), giving the clean bound
`ffSievedDegCount S d ≤ (∏_{P ∈ S} (1 - p^(-deg P))) · p^d` — no error term. -/

section CongruenceSieve

/-- Count of monic `m` of degree exactly `d` with `m + 1` avoiding every
    modulus in `S`. -/
noncomputable def ffSievedDegCount (S : Finset (Polynomial (ZMod p))) (d : ℕ) : ℕ :=
  ((ffMonicDeg p d).filter (fun m => ∀ P ∈ S, ¬P ∣ m + 1)).card

/-- The "good" residues mod `∏ S`: canonical remainders `r` (degree `< deg ∏S`)
    with `r + 1` avoiding every `P ∈ S`. -/
private noncomputable def ffGoodRes (S : Finset (Polynomial (ZMod p))) :
    Finset (Polynomial (ZMod p)) :=
  (ffResLT p (∏ P ∈ S, P).natDegree).filter (fun r => ∀ P ∈ S, ¬P ∣ r + 1)

/-- Single modulus: the good residues mod `P₀` are all residues except `-1`. -/
private theorem ffGoodRes_singleton_card_le {P₀ : Polynomial (ZMod p)}
    (hP₀i : Irreducible P₀) :
    (ffGoodRes p {P₀}).card ≤ p ^ P₀.natDegree - 1 := by
  have hd : 0 < P₀.natDegree := hP₀i.natDegree_pos
  have hneg : (-1 : Polynomial (ZMod p)) ∈ ffResLT p P₀.natDegree := by
    rw [mem_ffResLT, Polynomial.degree_neg, Polynomial.degree_one]
    exact_mod_cast hd
  have hsub : ffGoodRes p {P₀} ⊆ (ffResLT p P₀.natDegree).erase (-1) := by
    intro r hr
    rw [ffGoodRes, Finset.mem_filter, Finset.prod_singleton] at hr
    rw [Finset.mem_erase]
    refine ⟨?_, hr.1⟩
    intro hr1
    exact hr.2 P₀ (Finset.mem_singleton_self P₀) (by rw [hr1, neg_add_cancel]; exact dvd_zero P₀)
  calc (ffGoodRes p {P₀}).card ≤ ((ffResLT p P₀.natDegree).erase (-1)).card :=
        Finset.card_le_card hsub
    _ = (ffResLT p P₀.natDegree).card - 1 := Finset.card_erase_of_mem hneg
    _ ≤ p ^ P₀.natDegree - 1 := by
        have := ffResLT_card_le p P₀.natDegree
        omega

/-- **CRT bound for good residues**: for a finite set of (distinct) monic
    irreducibles, the good residues mod `∏ S` inject into the product of the
    per-modulus good residues, giving `#good ≤ ∏ (p^(deg P) - 1)`. -/
private theorem ffGoodRes_card_le (S : Finset (Polynomial (ZMod p)))
    (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P) :
    (ffGoodRes p S).card ≤ ∏ P ∈ S, (p ^ P.natDegree - 1) := by
  induction S using Finset.cons_induction with
  | empty =>
    calc (ffGoodRes p ∅).card ≤ (ffResLT p (∏ P ∈ (∅ : Finset (Polynomial (ZMod p))), P).natDegree).card :=
          Finset.card_filter_le _ _
      _ ≤ 1 := by
          have h := ffResLT_card_le p (∏ P ∈ (∅ : Finset (Polynomial (ZMod p))), P).natDegree
          simp only [Finset.prod_empty, Polynomial.natDegree_one, pow_zero] at h
          simpa using h
      _ = ∏ P ∈ (∅ : Finset (Polynomial (ZMod p))), (p ^ P.natDegree - 1) := by simp
  | cons P₀ S' hP₀ ih =>
    obtain ⟨hP₀m, hP₀i⟩ := hS P₀ (Finset.mem_cons_self P₀ S')
    have hS' : ∀ P ∈ S', P.Monic ∧ Irreducible P :=
      fun P hP => hS P (Finset.mem_cons_of_mem hP)
    set N' := ∏ P ∈ S', P with hN'
    have hN'm : N'.Monic := Polynomial.monic_prod_of_monic _ _ (fun P hP => (hS' P hP).1)
    -- P₀ does not divide the product of the other (distinct) monic irreducibles
    have hndvd : ¬P₀ ∣ N' := by
      intro hdvd
      have hprime : Prime P₀ := hP₀i.prime
      obtain ⟨P, hPmem, hPdvd⟩ := hprime.exists_mem_finset_dvd hdvd
      have : P₀ = P := Polynomial.eq_of_monic_of_associated hP₀m (hS' P hPmem).1
        (hP₀i.associated_of_dvd (hS' P hPmem).2 hPdvd)
      exact hP₀ (this ▸ hPmem)
    have hcop : IsCoprime P₀ N' := hP₀i.coprime_iff_not_dvd.mpr hndvd
    set N := ∏ P ∈ Finset.cons P₀ S' hP₀, P with hN
    have hNeq : N = P₀ * N' := Finset.prod_cons hP₀
    have hNm : N.Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun P hP => (hS P hP).1)
    -- inject into the product of per-modulus good residue sets
    have hinj : (ffGoodRes p (Finset.cons P₀ S' hP₀)).card ≤
        ((ffGoodRes p S') ×ˢ (ffGoodRes p {P₀})).card := by
      apply Finset.card_le_card_of_injOn (fun r => (r %ₘ N', r %ₘ P₀))
      · intro r hr
        rw [Finset.mem_coe, ffGoodRes, Finset.mem_filter] at hr
        obtain ⟨hrRes, hravoid⟩ := hr
        rw [Finset.mem_coe, Finset.mem_product]
        constructor
        · rw [ffGoodRes, Finset.mem_filter]
          constructor
          · rw [mem_ffResLT]
            have h := Polynomial.degree_modByMonic_lt r hN'm
            rwa [Polynomial.degree_eq_natDegree hN'm.ne_zero] at h
          · intro P hP hPdvd
            have hPN' : P ∣ N' := Finset.dvd_prod_of_mem _ hP
            have hPr : P ∣ r + 1 := by
              have h1 : r + 1 = (r - r %ₘ N') + (r %ₘ N' + 1) := by ring
              rw [h1]
              exact dvd_add (hPN'.trans (dvd_sub_modByMonic p r)) hPdvd
            exact hravoid P (Finset.mem_cons_of_mem hP) hPr
        · rw [ffGoodRes, Finset.mem_filter, Finset.prod_singleton]
          constructor
          · rw [mem_ffResLT]
            have h := Polynomial.degree_modByMonic_lt r hP₀m
            rwa [Polynomial.degree_eq_natDegree hP₀m.ne_zero] at h
          · intro P hP hPdvd
            rw [Finset.mem_singleton] at hP
            subst hP
            have hPr : P ∣ r + 1 := by
              have h1 : r + 1 = (r - r %ₘ P) + (r %ₘ P + 1) := by ring
              rw [h1]
              exact dvd_add (dvd_sub_modByMonic p r) hPdvd
            exact hravoid P (Finset.mem_cons_self P S') hPr
      · intro r₁ hr₁ r₂ hr₂ heq
        rw [Finset.mem_coe, ffGoodRes, Finset.mem_filter, mem_ffResLT] at hr₁ hr₂
        rw [Prod.mk.injEq] at heq
        have hd1 : N' ∣ r₁ - r₂ := dvd_sub_of_modByMonic_eq p heq.1
        have hd2 : P₀ ∣ r₁ - r₂ := dvd_sub_of_modByMonic_eq p heq.2
        have hNdvd : N ∣ r₁ - r₂ := hNeq ▸ hcop.mul_dvd hd2 hd1
        by_contra hne
        have hne0 : r₁ - r₂ ≠ 0 := sub_ne_zero.mpr hne
        have hlt : (r₁ - r₂).degree < N.degree := by
          rw [Polynomial.degree_eq_natDegree hNm.ne_zero]
          exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hr₁.1 hr₂.1)
        exact absurd (Polynomial.degree_le_of_dvd hNdvd hne0) (not_le.mpr hlt)
    calc (ffGoodRes p (Finset.cons P₀ S' hP₀)).card
        ≤ ((ffGoodRes p S') ×ˢ (ffGoodRes p {P₀})).card := hinj
      _ = (ffGoodRes p S').card * (ffGoodRes p {P₀}).card := Finset.card_product _ _
      _ ≤ (∏ P ∈ S', (p ^ P.natDegree - 1)) * (p ^ P₀.natDegree - 1) :=
          Nat.mul_le_mul (ih hS') (ffGoodRes_singleton_card_le p hP₀i)
      _ = ∏ P ∈ Finset.cons P₀ S' hP₀, (p ^ P.natDegree - 1) := by
          rw [Finset.prod_cons, mul_comm]

/-- Partition by residue class mod `∏ S`: the sieved count is at most the number
    of good residues times the exact per-class count `p^(d - deg ∏S)`. -/
private theorem ffSievedDegCount_le_aux (S : Finset (Polynomial (ZMod p)))
    (hS : ∀ P ∈ S, P.Monic) {d : ℕ} (hd : (∏ P ∈ S, P).natDegree ≤ d) :
    ffSievedDegCount p S d ≤
      (ffGoodRes p S).card * p ^ (d - (∏ P ∈ S, P).natDegree) := by
  set N := ∏ P ∈ S, P with hN
  have hNm : N.Monic := Polynomial.monic_prod_of_monic _ _ hS
  calc ffSievedDegCount p S d
      ≤ ((ffGoodRes p S).biUnion (fun r =>
          (ffMonicDeg p d).filter (fun m => N ∣ m - r))).card := by
        apply Finset.card_le_card
        intro m hm
        rw [Finset.mem_filter] at hm
        obtain ⟨hmdeg, hmavoid⟩ := hm
        rw [Finset.mem_biUnion]
        refine ⟨m %ₘ N, ?_, ?_⟩
        · rw [ffGoodRes, Finset.mem_filter]
          constructor
          · rw [mem_ffResLT]
            have h := Polynomial.degree_modByMonic_lt m hNm
            rwa [Polynomial.degree_eq_natDegree hNm.ne_zero] at h
          · intro P hP hPdvd
            have hPN : P ∣ N := Finset.dvd_prod_of_mem _ hP
            have hPm1 : P ∣ m + 1 := by
              have h1 : m + 1 = (m - m %ₘ N) + (m %ₘ N + 1) := by ring
              rw [h1]
              exact dvd_add (hPN.trans (dvd_sub_modByMonic p m)) hPdvd
            exact hmavoid P hP hPm1
        · exact Finset.mem_filter.mpr ⟨hmdeg, dvd_sub_modByMonic p m⟩
    _ ≤ ∑ r ∈ ffGoodRes p S, ((ffMonicDeg p d).filter (fun m => N ∣ m - r)).card :=
        Finset.card_biUnion_le
    _ = ∑ _r ∈ ffGoodRes p S, p ^ (d - N.natDegree) :=
        Finset.sum_congr rfl (fun r _ => ffMonicDeg_residue_card p hNm r hd)
    _ = (ffGoodRes p S).card * p ^ (d - N.natDegree) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- **Exact sieve bound** (real-valued): for a finite set `S` of monic
    irreducibles and any degree `d ≥ deg ∏S`, the count of monic `m` of degree
    `d` with `m + 1` avoiding every `P ∈ S` is at most
    `(∏_{P ∈ S} (1 - p^(-deg P))) · p^d` — the function-field luxury: no `+2`
    error term per class, so no epsilon-management in the decay argument. -/
theorem ffSievedDegCount_le_real (S : Finset (Polynomial (ZMod p)))
    (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P) {d : ℕ}
    (hd : (∏ P ∈ S, P).natDegree ≤ d) :
    (ffSievedDegCount p S d : ℝ) ≤
      (∏ P ∈ S, (1 - 1 / (p : ℝ) ^ P.natDegree)) * (p : ℝ) ^ d := by
  have hp1 : (1 : ℕ) ≤ p := (p_two_le p).trans' (by omega)
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have := p_two_le p
    positivity
  set N := ∏ P ∈ S, P with hN
  have hNdeg : N.natDegree = ∑ P ∈ S, P.natDegree :=
    Polynomial.natDegree_prod _ _ (fun P hP => (hS P hP).1.ne_zero)
  -- natural-number chain
  have hnat : ffSievedDegCount p S d ≤
      (∏ P ∈ S, (p ^ P.natDegree - 1)) * p ^ (d - N.natDegree) :=
    le_trans (ffSievedDegCount_le_aux p S (fun P hP => (hS P hP).1) hd)
      (Nat.mul_le_mul_right _ (ffGoodRes_card_le p S hS))
  -- cast the product of (p^e - 1)
  have hcast : ((∏ P ∈ S, (p ^ P.natDegree - 1) : ℕ) : ℝ) =
      ∏ P ∈ S, ((p : ℝ) ^ P.natDegree - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro P _
    have h1 : 1 ≤ p ^ P.natDegree := Nat.one_le_pow _ _ (by have := p_two_le p; omega)
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]
  -- the sieve product identity: ∏(1 - p^{-e}) * p^d = ∏(p^e - 1) * p^{d - deg N}
  have hprod_id : (∏ P ∈ S, (1 - 1 / (p : ℝ) ^ P.natDegree)) * (p : ℝ) ^ d =
      (∏ P ∈ S, ((p : ℝ) ^ P.natDegree - 1)) * (p : ℝ) ^ (d - N.natDegree) := by
    have hfac : ∀ P ∈ S, (1 - 1 / (p : ℝ) ^ P.natDegree) =
        ((p : ℝ) ^ P.natDegree - 1) / (p : ℝ) ^ P.natDegree := by
      intro P _
      have hpe : ((p : ℝ) ^ P.natDegree) ≠ 0 := by positivity
      field_simp
    rw [Finset.prod_congr rfl hfac, Finset.prod_div_distrib,
      Finset.prod_pow_eq_pow_sum, ← hNdeg]
    have hsplit : (p : ℝ) ^ d = (p : ℝ) ^ N.natDegree * (p : ℝ) ^ (d - N.natDegree) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    have hpN : ((p : ℝ) ^ N.natDegree) ≠ 0 := by positivity
    field_simp
  calc (ffSievedDegCount p S d : ℝ)
      ≤ ((∏ P ∈ S, (p ^ P.natDegree - 1)) * p ^ (d - N.natDegree) : ℕ) := by
        exact_mod_cast hnat
    _ = (∏ P ∈ S, ((p : ℝ) ^ P.natDegree - 1)) * (p : ℝ) ^ (d - N.natDegree) := by
        rw [Nat.cast_mul, hcast, Nat.cast_pow]
    _ = (∏ P ∈ S, (1 - 1 / (p : ℝ) ^ P.natDegree)) * (p : ℝ) ^ d := hprod_id.symm

end CongruenceSieve

/-! ## Part 7: Kornblum divergence, per-subset decay, and the headline

The last analytic input: for each nonzero residue class `a` mod a monic
irreducible `Q`, the sum `∑_{P ≡ a (Q)} p^(-deg P)` over monic irreducibles `P`
diverges. This is Kornblum's function-field analogue of Dirichlet's theorem
(1919); its proof needs polynomial L-functions, which are not in Mathlib, so it
is isolated as the named hypothesis `FFDirichletDensity`. Everything downstream
is proved: the divergence forces the sieve product over each excluded class to
vanish (`1 - x ≤ exp(-x)`), hence each confined density tends to `0`
(`ff_density_pscd`), hence by the pigeonhole of Part 5 the trapped density tends
to `0` (`ff_almost_all_genmixed_density`). -/

section DensityHeadline

/-- The monic irreducibles of degree `1 ≤ deg ≤ Y` in the residue class of `a`
    mod `Q`. -/
noncomputable def ffClassIrredUpTo (Q a : Polynomial (ZMod p)) (Y : ℕ) :
    Finset (Polynomial (ZMod p)) :=
  (Finset.Icc 1 Y).biUnion (fun e => (ffIrredDeg p e).filter (fun P => P %ₘ Q = a %ₘ Q))

/-- **Kornblum's theorem, as an isolated hypothesis**: for every monic
    irreducible modulus `Q` and every residue class `a` with `Q ∤ a`, the sum
    `∑_{P ≡ a (Q)} p^(-deg P)` over monic irreducibles `P` diverges (its partial
    sums, cut off at degree `Y`, tend to infinity).

    This is the function-field analogue of Dirichlet's theorem on primes in
    arithmetic progressions (H. Kornblum, Math. Z. 5 (1919)); over `ℤ` the
    corresponding statement is proved unconditionally in
    `EM/IK/DirichletDensity.lean`. Over `F_p[t]` the proof needs polynomial
    L-functions (nonvanishing at `s = 1`), which Mathlib does not yet have, so
    it is kept as the SOLE open hypothesis of this file's headline. -/
def FFDirichletDensity : Prop :=
  ∀ Q : Polynomial (ZMod p), Q.Monic → Irreducible Q →
    ∀ a : Polynomial (ZMod p), ¬Q ∣ a →
      Filter.Tendsto
        (fun Y => ∑ P ∈ ffClassIrredUpTo p Q a Y, 1 / (p : ℝ) ^ P.natDegree)
        Filter.atTop Filter.atTop

/-- The excluded sieve moduli for walk-position class `c` and target subset `R`:
    monic irreducibles `P` of degree `1 ≤ deg ≤ Y` whose factor move lands
    outside `R`. -/
noncomputable def ffExcludedUpTo (Q c : Polynomial (ZMod p))
    (R : Finset (Polynomial (ZMod p))) (Y : ℕ) : Finset (Polynomial (ZMod p)) :=
  (Finset.Icc 1 Y).biUnion (fun e =>
    (ffIrredDeg p e).filter (fun P => (c * P) %ₘ Q ∉ R))

private theorem ffExcludedUpTo_spec {Q c : Polynomial (ZMod p)}
    {R : Finset (Polynomial (ZMod p))} {Y : ℕ} {P : Polynomial (ZMod p)}
    (hP : P ∈ ffExcludedUpTo p Q c R Y) :
    P.Monic ∧ Irreducible P ∧ (c * P) %ₘ Q ∉ R := by
  rw [ffExcludedUpTo, Finset.mem_biUnion] at hP
  obtain ⟨e, _, hPf⟩ := hP
  rw [Finset.mem_filter, mem_ffIrredDeg] at hPf
  exact ⟨hPf.1.1, hPf.1.2.1, hPf.2⟩

/-- Confined count within a fixed residue class `c` of the starting point. -/
private noncomputable def ffConfinedClassDegCount (Q c : Polynomial (ZMod p))
    (R : Finset (Polynomial (ZMod p))) (d : ℕ) : ℕ :=
  ((ffMonicDeg p d).filter (fun m => Squarefree m ∧ m %ₘ Q = c ∧
    FFAllFactorsIn p (m + 1) (ffAllowedFactors p Q m R))).card

/-- Split the confined count over the nonzero residue classes of the starting
    point (`Q ∤ m` forces a nonzero class). -/
private theorem ffConfinedDegCount_le_sum_classes {Q : Polynomial (ZMod p)}
    (hQm : Q.Monic) (R : Finset (Polynomial (ZMod p))) (d : ℕ) :
    ffConfinedDegCount p Q R d ≤
      ∑ c ∈ (ffResLT p Q.natDegree).erase 0, ffConfinedClassDegCount p Q c R d := by
  calc ffConfinedDegCount p Q R d
      ≤ (((ffResLT p Q.natDegree).erase 0).biUnion (fun c =>
          (ffMonicDeg p d).filter (fun m => Squarefree m ∧ m %ₘ Q = c ∧
            FFAllFactorsIn p (m + 1) (ffAllowedFactors p Q m R)))).card := by
        apply Finset.card_le_card
        intro m hm
        rw [Finset.mem_filter] at hm
        obtain ⟨hmdeg, hsf, hndvd, hconf⟩ := hm
        rw [Finset.mem_biUnion]
        refine ⟨m %ₘ Q, ?_, ?_⟩
        · rw [Finset.mem_erase]
          constructor
          · intro h0
            exact hndvd ((Polynomial.modByMonic_eq_zero_iff_dvd hQm).mp h0)
          · rw [mem_ffResLT]
            have h := Polynomial.degree_modByMonic_lt m hQm
            rwa [Polynomial.degree_eq_natDegree hQm.ne_zero] at h
        · exact Finset.mem_filter.mpr ⟨hmdeg, hsf, rfl, hconf⟩
    _ ≤ ∑ c ∈ (ffResLT p Q.natDegree).erase 0, ffConfinedClassDegCount p Q c R d :=
        Finset.card_biUnion_le

/-- Within class `c`, a confined starting point avoids every excluded sieve
    modulus: the confined class count is bounded by the sieved count. -/
private theorem ffConfinedClass_le_sieved {Q : Polynomial (ZMod p)} (hQm : Q.Monic)
    (c : Polynomial (ZMod p)) (R : Finset (Polynomial (ZMod p))) (Y d : ℕ) :
    ffConfinedClassDegCount p Q c R d ≤
      ffSievedDegCount p (ffExcludedUpTo p Q c R Y) d := by
  apply Finset.card_le_card
  intro m hm
  rw [Finset.mem_filter] at hm ⊢
  obtain ⟨hmdeg, hsf, hclass, hconf⟩ := hm
  refine ⟨hmdeg, fun P hP hPdvd => ?_⟩
  obtain ⟨hPm, hPi, hPex⟩ := ffExcludedUpTo_spec p hP
  have hallow : (m * P) %ₘ Q ∈ R := hconf P hPm hPi hPdvd
  have hcongr : (m * P) %ₘ Q = (c * P) %ₘ Q := by
    apply modByMonic_congr p hQm
    have h1 : Q ∣ m - c := by
      rw [← hclass]
      exact dvd_sub_modByMonic p m
    have h2 : m * P - c * P = (m - c) * P := by ring
    rw [h2]
    exact h1.mul_right P
  rw [hcongr] at hallow
  exact hPex hallow

/-- For a nonzero class `c` and a missing nonzero residue `a`, there is a
    nonzero residue class `b` (`b ≈ c⁻¹·a`) whose monic irreducibles all move
    the walk from position `c` to the missing residue `a`. -/
private theorem ff_exists_excluded_class {Q : Polynomial (ZMod p)}
    (hQm : Q.Monic) (hQi : Irreducible Q) {c a : Polynomial (ZMod p)}
    (hc : c.degree < Q.degree) (hc0 : c ≠ 0)
    (ha : a.degree < Q.degree) (ha0 : a ≠ 0) :
    ∃ b : Polynomial (ZMod p), ¬Q ∣ b ∧
      ∀ P : Polynomial (ZMod p), P %ₘ Q = b %ₘ Q → (c * P) %ₘ Q = a := by
  have hQc : ¬Q ∣ c := fun hdvd =>
    absurd (Polynomial.degree_le_of_dvd hdvd hc0) (not_le.mpr hc)
  have hQa : ¬Q ∣ a := fun hdvd =>
    absurd (Polynomial.degree_le_of_dvd hdvd ha0) (not_le.mpr ha)
  have hcop : IsCoprime Q c := hQi.coprime_iff_not_dvd.mpr hQc
  obtain ⟨u, v, huv⟩ := hcop
  -- c * (v * a) ≡ a (mod Q)
  have hkey : Q ∣ c * (v * a) - a := ⟨-(u * a), by linear_combination a * huv⟩
  refine ⟨v * a, ?_, ?_⟩
  · intro hdvd
    apply hQa
    have h1 : Q ∣ c * (v * a) := hdvd.mul_left c
    have h2 := dvd_sub h1 hkey
    have heq : c * (v * a) - (c * (v * a) - a) = a := by ring
    rwa [heq] at h2
  · intro P hP
    have hcongr1 : (c * P) %ₘ Q = (c * (v * a)) %ₘ Q := by
      apply modByMonic_congr p hQm
      have h1 : Q ∣ P - v * a := dvd_sub_of_modByMonic_eq p hP
      have h2 : c * P - c * (v * a) = (P - v * a) * c := by ring
      rw [h2]
      exact h1.mul_right c
    have hcongr2 : (c * (v * a)) %ₘ Q = a %ₘ Q := modByMonic_congr p hQm hkey
    have ha_self : a %ₘ Q = a := (Polynomial.modByMonic_eq_self_iff hQm).mpr ha
    rw [hcongr1, hcongr2, ha_self]

/-- **Per-subset confinement decay** (FF-PSCD, the genuine density version):
    assuming `FFDirichletDensity`, for every monic irreducible `Q` and every
    residue subset `R` missing some nonzero residue, the density of confined
    starting points among monic squarefree polynomials of degree `1..n` tends
    to `0` as `n → ∞`. -/
theorem ff_density_pscd (hFF : FFDirichletDensity p) {Q : Polynomial (ZMod p)}
    (hQm : Q.Monic) (hQi : Irreducible Q) (R : Finset (Polynomial (ZMod p)))
    (hR : ∃ a ∈ ffResLT p Q.natDegree, a ≠ 0 ∧ a ∉ R) :
    Filter.Tendsto
      (fun n => (ffConfinedCount p Q R n : ℝ) / (ffSqfreeCount p n : ℝ))
      Filter.atTop (nhds 0) := by
  obtain ⟨a, haRes, ha0, haR⟩ := hR
  have hp2 : 2 ≤ p := p_two_le p
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hQdeg : Q.degree = (Q.natDegree : WithBot ℕ) :=
    Polynomial.degree_eq_natDegree hQm.ne_zero
  have hadeg : a.degree < Q.degree := by rw [hQdeg]; exact (mem_ffResLT p).mp haRes
  set classes := (ffResLT p Q.natDegree).erase 0 with hclasses
  -- per-class excluded residue class witness (b ≈ c⁻¹ · a)
  have hclass : ∀ c ∈ classes, ∃ b, ¬Q ∣ b ∧
      ∀ P : Polynomial (ZMod p), P %ₘ Q = b %ₘ Q → (c * P) %ₘ Q = a := by
    intro c hc
    rw [hclasses, Finset.mem_erase] at hc
    exact ff_exists_excluded_class p hQm hQi
      (by rw [hQdeg]; exact (mem_ffResLT p).mp hc.2) hc.1 hadeg ha0
  rw [Metric.tendsto_atTop]
  intro ε hε
  set Cq : ℝ := (p : ℝ) ^ Q.natDegree with hCq
  have hCq0 : 0 < Cq := by positivity
  set ε' : ℝ := ε / (8 * Cq) with hε'def
  have hε'0 : 0 < ε' := by positivity
  set M : ℝ := -Real.log ε' + 1 with hM
  -- Step 1: for each class c, a degree cutoff Y beyond which the sieve product
  -- over the excluded moduli is < ε'
  have hkey : ∀ c ∈ classes, ∃ Y₀ : ℕ, ∀ Y ≥ Y₀,
      ∏ P ∈ ffExcludedUpTo p Q c R Y, (1 - 1 / (p : ℝ) ^ P.natDegree) < ε' := by
    intro c hc
    obtain ⟨b, hbQ, hbmul⟩ := hclass c hc
    have htend := hFF Q hQm hQi b hbQ
    rw [Filter.tendsto_atTop] at htend
    have hev := htend M
    rw [Filter.eventually_atTop] at hev
    obtain ⟨Y₀, hY₀⟩ := hev
    refine ⟨Y₀, fun Y hY => ?_⟩
    set S := ffExcludedUpTo p Q c R Y with hSdef
    have hSspec : ∀ P ∈ S, P.Monic ∧ Irreducible P ∧ (c * P) %ₘ Q ∉ R :=
      fun P hP => ffExcludedUpTo_spec p hP
    have hfac_nonneg : ∀ P ∈ S, (0 : ℝ) ≤ 1 - 1 / (p : ℝ) ^ P.natDegree := by
      intro P hP
      have hpe : (1 : ℝ) ≤ (p : ℝ) ^ P.natDegree := one_le_pow₀ hp1.le
      have h2 : 1 / (p : ℝ) ^ P.natDegree ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact hpe
      linarith
    -- product ≤ exp(-sum) over the excluded moduli
    have hprod_exp : ∏ P ∈ S, (1 - 1 / (p : ℝ) ^ P.natDegree) ≤
        Real.exp (-(∑ P ∈ S, 1 / (p : ℝ) ^ P.natDegree)) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      apply Finset.prod_le_prod hfac_nonneg
      intro P _
      have h := Real.add_one_le_exp (-(1 / (p : ℝ) ^ P.natDegree))
      linarith
    -- the class-b irreducibles are all excluded
    have hsub : ffClassIrredUpTo p Q b Y ⊆ S := by
      intro P hP
      rw [ffClassIrredUpTo, Finset.mem_biUnion] at hP
      obtain ⟨e, he, hPf⟩ := hP
      rw [Finset.mem_filter] at hPf
      rw [hSdef, ffExcludedUpTo, Finset.mem_biUnion]
      refine ⟨e, he, Finset.mem_filter.mpr ⟨hPf.1, ?_⟩⟩
      rw [hbmul P hPf.2]
      exact haR
    have hsum_ge : M ≤ ∑ P ∈ S, 1 / (p : ℝ) ^ P.natDegree :=
      le_trans (hY₀ Y hY)
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _ => by positivity))
    calc ∏ P ∈ S, (1 - 1 / (p : ℝ) ^ P.natDegree)
        ≤ Real.exp (-(∑ P ∈ S, 1 / (p : ℝ) ^ P.natDegree)) := hprod_exp
      _ ≤ Real.exp (Real.log ε' - 1) := by
          apply Real.exp_le_exp_of_le
          rw [hM] at hsum_ge
          linarith
      _ < Real.exp (Real.log ε') := Real.exp_strictMono (by linarith)
      _ = ε' := Real.exp_log hε'0
  -- Step 2: uniform cutoff Y over the finitely many classes
  set Yfun : Polynomial (ZMod p) → ℕ := fun c =>
    if hc : c ∈ classes then (hkey c hc).choose else 0
  set Y := classes.sup Yfun with hYdef
  have hprod_small : ∀ c ∈ classes,
      ∏ P ∈ ffExcludedUpTo p Q c R Y, (1 - 1 / (p : ℝ) ^ P.natDegree) < ε' := by
    intro c hc
    apply (hkey c hc).choose_spec
    have hYfun : Yfun c = (hkey c hc).choose := dif_pos hc
    calc (hkey c hc).choose = Yfun c := hYfun.symm
      _ ≤ classes.sup Yfun := Finset.le_sup hc
  -- Step 3: per-degree confined bound beyond the sieve threshold degree
  set D0 := classes.sup (fun c => (∏ P ∈ ffExcludedUpTo p Q c R Y, P).natDegree)
    with hD0
  have hcard_classes : (classes.card : ℝ) ≤ Cq := by
    have h1 : classes.card ≤ (ffResLT p Q.natDegree).card :=
      Finset.card_le_card (Finset.erase_subset _ _)
    have h2 := ffResLT_card_le p Q.natDegree
    rw [hCq]
    exact_mod_cast le_trans h1 h2
  have hdeg_bound : ∀ d, D0 < d →
      (ffConfinedDegCount p Q R d : ℝ) ≤ Cq * ε' * (p : ℝ) ^ d := by
    intro d hdD0
    have hsplit : (ffConfinedDegCount p Q R d : ℝ) ≤
        ∑ c ∈ classes, (ffSievedDegCount p (ffExcludedUpTo p Q c R Y) d : ℝ) := by
      have h1 := ffConfinedDegCount_le_sum_classes p hQm R d
      have h2 : ∑ c ∈ classes, ffConfinedClassDegCount p Q c R d ≤
          ∑ c ∈ classes, ffSievedDegCount p (ffExcludedUpTo p Q c R Y) d :=
        Finset.sum_le_sum (fun c _ => ffConfinedClass_le_sieved p hQm c R Y d)
      exact_mod_cast le_trans h1 h2
    have hper : ∀ c ∈ classes,
        (ffSievedDegCount p (ffExcludedUpTo p Q c R Y) d : ℝ) ≤ ε' * (p : ℝ) ^ d := by
      intro c hc
      have hS : ∀ P ∈ ffExcludedUpTo p Q c R Y, P.Monic ∧ Irreducible P :=
        fun P hP => ⟨(ffExcludedUpTo_spec p hP).1, (ffExcludedUpTo_spec p hP).2.1⟩
      have hdN : (∏ P ∈ ffExcludedUpTo p Q c R Y, P).natDegree ≤ d :=
        le_trans (Finset.le_sup (f := fun c =>
          (∏ P ∈ ffExcludedUpTo p Q c R Y, P).natDegree) hc) hdD0.le
      calc (ffSievedDegCount p (ffExcludedUpTo p Q c R Y) d : ℝ)
          ≤ (∏ P ∈ ffExcludedUpTo p Q c R Y, (1 - 1 / (p : ℝ) ^ P.natDegree)) *
              (p : ℝ) ^ d := ffSievedDegCount_le_real p _ hS hdN
        _ ≤ ε' * (p : ℝ) ^ d :=
            mul_le_mul_of_nonneg_right (hprod_small c hc).le (by positivity)
    calc (ffConfinedDegCount p Q R d : ℝ)
        ≤ ∑ c ∈ classes, (ffSievedDegCount p (ffExcludedUpTo p Q c R Y) d : ℝ) :=
          hsplit
      _ ≤ ∑ _c ∈ classes, ε' * (p : ℝ) ^ d := Finset.sum_le_sum hper
      _ = (classes.card : ℝ) * (ε' * (p : ℝ) ^ d) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Cq * ε' * (p : ℝ) ^ d := by
          have hpos : (0 : ℝ) ≤ ε' * (p : ℝ) ^ d := by positivity
          nlinarith
  -- Step 4: global count bound
  have hcount : ∀ n : ℕ, (ffConfinedCount p Q R n : ℝ) ≤
      (p : ℝ) ^ (D0 + 1) + Cq * ε' * ∑ d ∈ Finset.Icc 1 n, (p : ℝ) ^ d := by
    intro n
    have hterm : ∀ d ∈ Finset.Icc 1 n, (ffConfinedDegCount p Q R d : ℝ) ≤
        (if d ≤ D0 then (p : ℝ) ^ d else 0) + Cq * ε' * (p : ℝ) ^ d := by
      intro d _
      by_cases hdD : d ≤ D0
      · rw [if_pos hdD]
        have h1 : (ffConfinedDegCount p Q R d : ℝ) ≤ (p : ℝ) ^ d := by
          have := card_filter_ffMonicDeg_le p d (fun m => Squarefree m ∧ ¬Q ∣ m ∧
            FFAllFactorsIn p (m + 1) (ffAllowedFactors p Q m R))
          exact_mod_cast this
        have h2 : (0 : ℝ) ≤ Cq * ε' * (p : ℝ) ^ d := by positivity
        linarith
      · rw [if_neg hdD]
        have := hdeg_bound d (by omega)
        linarith
    calc (ffConfinedCount p Q R n : ℝ)
        = ∑ d ∈ Finset.Icc 1 n, (ffConfinedDegCount p Q R d : ℝ) := by
          rw [ffConfinedCount, Nat.cast_sum]
      _ ≤ ∑ d ∈ Finset.Icc 1 n,
            ((if d ≤ D0 then (p : ℝ) ^ d else 0) + Cq * ε' * (p : ℝ) ^ d) :=
          Finset.sum_le_sum hterm
      _ = (∑ d ∈ Finset.Icc 1 n, (if d ≤ D0 then (p : ℝ) ^ d else 0)) +
            Cq * ε' * ∑ d ∈ Finset.Icc 1 n, (p : ℝ) ^ d := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (p : ℝ) ^ (D0 + 1) + Cq * ε' * ∑ d ∈ Finset.Icc 1 n, (p : ℝ) ^ d := by
          have hif : ∑ d ∈ Finset.Icc 1 n, (if d ≤ D0 then (p : ℝ) ^ d else 0) ≤
              (p : ℝ) ^ (D0 + 1) := by
            calc ∑ d ∈ Finset.Icc 1 n, (if d ≤ D0 then (p : ℝ) ^ d else 0)
                = ∑ d ∈ (Finset.Icc 1 n).filter (· ≤ D0), (p : ℝ) ^ d :=
                  (Finset.sum_filter _ _).symm
              _ ≤ ∑ d ∈ Finset.range (D0 + 1), (p : ℝ) ^ d := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro d hd
                    rw [Finset.mem_filter] at hd
                    rw [Finset.mem_range]
                    omega
                  · intro d _ _
                    positivity
              _ ≤ (p : ℝ) ^ (D0 + 1) := by exact_mod_cast geom_sum_le p (D0 + 1)
          linarith
  -- Step 5: denominator frame
  have hframe : ∀ n : ℕ, (∑ d ∈ Finset.Icc 1 n, (p : ℝ) ^ d) ≤
      4 * (ffSqfreeCount p n : ℝ) := by
    intro n
    have hnat : ∑ d ∈ Finset.Icc 1 n, p ^ d ≤ 4 * ffSqfreeCount p n := by
      rw [ffSqfreeCount, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mem_Icc] at hd
      exact ffSqfreeDegCount_quarter p d hd.1
    exact_mod_cast hnat
  -- Step 6: choose n₀ killing the low-degree contribution
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 8 * (p : ℝ) ^ (D0 + 1) / ε < (p : ℝ) ^ n₀ :=
    pow_unbounded_of_one_lt _ hp1
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnn₀ : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hsq_pos : (0 : ℝ) < (ffSqfreeCount p n : ℝ) :=
    Nat.cast_pos.mpr (ffSqfreeCount_pos p n hn1)
  have hsq_ge : (p : ℝ) ^ n / 4 ≤ (ffSqfreeCount p n : ℝ) := ffSqfreeCount_ge_real p n hn1
  have hpn_pos : (0 : ℝ) < (p : ℝ) ^ n := by positivity
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  -- assemble: density ≤ 4·p^(D0+1)/p^n + ε/2 < ε
  have hA : (p : ℝ) ^ (D0 + 1) / (ffSqfreeCount p n : ℝ) < ε / 2 := by
    have h1 : (p : ℝ) ^ (D0 + 1) / (ffSqfreeCount p n : ℝ) ≤
        (p : ℝ) ^ (D0 + 1) / ((p : ℝ) ^ n / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hsq_ge
    have h2 : (p : ℝ) ^ (D0 + 1) / ((p : ℝ) ^ n / 4) = 4 * (p : ℝ) ^ (D0 + 1) / (p : ℝ) ^ n := by
      field_simp
    have hpn₀ : (p : ℝ) ^ n₀ ≤ (p : ℝ) ^ n := pow_le_pow_right₀ hp1.le hnn₀
    have h3 : 8 * (p : ℝ) ^ (D0 + 1) < ε * (p : ℝ) ^ n := by
      have h4 : 8 * (p : ℝ) ^ (D0 + 1) / ε < (p : ℝ) ^ n := lt_of_lt_of_le hn₀ hpn₀
      calc 8 * (p : ℝ) ^ (D0 + 1) = (8 * (p : ℝ) ^ (D0 + 1) / ε) * ε := by
            field_simp
        _ < (p : ℝ) ^ n * ε := by
            exact mul_lt_mul_of_pos_right h4 hε
        _ = ε * (p : ℝ) ^ n := mul_comm _ _
    have h5 : 4 * (p : ℝ) ^ (D0 + 1) / (p : ℝ) ^ n < ε / 2 := by
      rw [div_lt_div_iff₀ hpn_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    linarith
  have hB : Cq * ε' * (∑ d ∈ Finset.Icc 1 n, (p : ℝ) ^ d) / (ffSqfreeCount p n : ℝ) ≤
      ε / 2 := by
    have h1 : Cq * ε' * (∑ d ∈ Finset.Icc 1 n, (p : ℝ) ^ d) ≤
        Cq * ε' * (4 * (ffSqfreeCount p n : ℝ)) :=
      mul_le_mul_of_nonneg_left (hframe n) (by positivity)
    have h2 : Cq * ε' * (4 * (ffSqfreeCount p n : ℝ)) / (ffSqfreeCount p n : ℝ) =
        4 * Cq * ε' := by
      field_simp
    have h3 : 4 * Cq * ε' = ε / 2 := by
      rw [hε'def]
      field_simp
      ring
    calc Cq * ε' * (∑ d ∈ Finset.Icc 1 n, (p : ℝ) ^ d) / (ffSqfreeCount p n : ℝ)
        ≤ Cq * ε' * (4 * (ffSqfreeCount p n : ℝ)) / (ffSqfreeCount p n : ℝ) :=
          div_le_div_of_nonneg_right h1 hsq_pos.le
      _ = 4 * Cq * ε' := h2
      _ = ε / 2 := h3
  calc (ffConfinedCount p Q R n : ℝ) / (ffSqfreeCount p n : ℝ)
      ≤ ((p : ℝ) ^ (D0 + 1) + Cq * ε' * ∑ d ∈ Finset.Icc 1 n, (p : ℝ) ^ d) /
          (ffSqfreeCount p n : ℝ) :=
        div_le_div_of_nonneg_right (hcount n) hsq_pos.le
    _ = (p : ℝ) ^ (D0 + 1) / (ffSqfreeCount p n : ℝ) +
          Cq * ε' * (∑ d ∈ Finset.Icc 1 n, (p : ℝ) ^ d) / (ffSqfreeCount p n : ℝ) :=
        add_div _ _ _
    _ < ε := by linarith

/-- **The genuine almost-all GenMixedMC density statement** over `F_p[t]`: for
    every monic irreducible target `Q`, the proportion of monic squarefree
    starting points `m` of degree `1..n` that satisfy `Q ∤ m` yet do NOT have
    `Q` tree-reachable tends to `0` as `n → ∞` (proportion measured against all
    monic squarefree polynomials of degree `1..n`).

    This is what the counting proxies `FFPSCD` / `FFAlmostAllGenMixedMC` of
    `FFSieve.lean` stand in for. -/
def FFAlmostAllGenMixedDensity : Prop :=
  ∀ Q : Polynomial (ZMod p), Q.Monic → Irreducible Q →
    Filter.Tendsto
      (fun n => (ffTrappedCount p Q n : ℝ) / (ffSqfreeCount p n : ℝ))
      Filter.atTop (nhds 0)

/-- **HEADLINE**: `FFDirichletDensity` (Kornblum) implies the genuine density
    statement: the trapped density tends to `0` for every monic irreducible
    target. Conditional on `FFDirichletDensity` ONLY. -/
theorem ff_almost_all_genmixed_density (hFF : FFDirichletDensity p) :
    FFAlmostAllGenMixedDensity p := by
  intro Q hQm hQi
  -- the sum of confined densities over the proper subsets tends to 0
  have hsum : Filter.Tendsto
      (fun n => ∑ R ∈ ffProperSubsets p Q,
        (ffConfinedCount p Q R n : ℝ) / (ffSqfreeCount p n : ℝ))
      Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ) = ∑ _R ∈ ffProperSubsets p Q, (0 : ℝ) := by simp
    rw [h0]
    apply tendsto_finsetSum
    intro R hR
    rw [ffProperSubsets, Finset.mem_filter] at hR
    exact ff_density_pscd p hFF hQm hQi R hR.2
  have hnonneg : ∀ n : ℕ,
      0 ≤ (ffTrappedCount p Q n : ℝ) / (ffSqfreeCount p n : ℝ) :=
    fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hle : ∀ n : ℕ, (ffTrappedCount p Q n : ℝ) / (ffSqfreeCount p n : ℝ) ≤
      ∑ R ∈ ffProperSubsets p Q,
        (ffConfinedCount p Q R n : ℝ) / (ffSqfreeCount p n : ℝ) := by
    intro n
    by_cases hsq : ffSqfreeCount p n = 0
    · have htr : ffTrappedCount p Q n = 0 := by
        have := ffTrappedCount_le p Q n
        omega
      rw [htr]
      simp only [Nat.cast_zero, zero_div]
      exact Finset.sum_nonneg fun R _ =>
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · have hpos : (0 : ℝ) < (ffSqfreeCount p n : ℝ) :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero hsq)
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ hpos.le
      exact_mod_cast ff_trapped_le_sum_confined p hQm hQi n
  exact squeeze_zero hnonneg hle hsum

end DensityHeadline

end FunctionFieldAnalog
