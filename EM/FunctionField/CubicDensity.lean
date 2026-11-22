import EM.FunctionField.CubicStep
import EM.FunctionField.StableAnalyticDensity
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The density of the cubic condition, from Kronecker's root-count theorem

2026-11-22.

For `p ≡ 1 (mod 3)` and `ω` a primitive cube root of unity in `𝔽_p`, a sequence over `𝔽_p[X]`
whose term at stage `2` is `X − ω` has a linear term at stage `3` iff `−6(5 + ω)` is a cube
in `𝔽_p`, and a term of degree `3` otherwise (`SecondGeneration.lean`). The seed of this
branch is the pair `(p, ω)`, i.e. a prime of degree one of `ℤ[ω]`.

The pairs `(ω, b)` with `ω² + ω + 1 = 0`, `b³ = −6(5 + ω)` are the roots mod `p` of one
polynomial with integer coefficients,

  `S(X) = (X³ + 30)² − 6 (X³ + 30) + 36`,

the norm from `ℤ[ω]` of `X³ + 6(5 + ω)`. So for `p ∉ {2, 3, 7}`

  `#{roots of S mod p} = 3 · #{ω : −6(5 + ω) is a cube}`   (`rootCount_sextic`).

## The quoted statement

`KroneckerDensity f` — the mean number of roots mod `p` of `f`, in analytic density, is `1`:

  `(x − 1) ∑_p N_p(f) · log p · p^{−x} → 1`   as `x → 1⁺`.

For `f` irreducible over `ℚ` this is Kronecker's theorem (1880); it follows from the simple
pole of the Dedekind zeta function of `ℚ[X]/(f)`, or from the Chebotarev density theorem and
Burnside's lemma. It is used here as a hypothesis for the single polynomial `S`. It is not in
Mathlib. The Tau Ceti library has a Chebotarev density theorem
(`NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`); the root-count form was not
found there under that name and has not been derived from it here.

## Main results

* `rootCount_sextic` — the identity above, unconditional.
* `cube_density` — under `KroneckerDensity sextic`, the mean over the primes of
  `#{ω : −6(5+ω) is a cube mod p}` is `1/3`.
* `ffSeq_three_natDegree_eq_one_iff` — the link to the sequences: with `X − ω` at stage `2`,
  the term at stage `3` is linear iff `−6(5 + ω)` is a cube.

## Reading

The mean number of pairs `(p, ω)` per prime is `1` (two for `p ≡ 1 (mod 3)`, none for
`p ≡ 2`). So, granted the quoted statement, one third of the branches `(p, ω)` capture a
linear polynomial at stage `3` and two thirds take the whole cubic. This is a statement about
the family of all `p`; it says nothing about a fixed `p`.

The degree at stage `3` is a function of the pair `(p, ω)`, not of `p`: the conditions for
`ω` and for `ω²` are different (`5 + ω` and `5 + ω²` differ by the two primes of `ℤ[ω]`
above `7`). The joint law of the two conditions at one `p` is not treated here.
-/

namespace FunctionFieldAnalog

namespace CubicDensity

open Polynomial Filter Topology StableAnalyticDensity SecondGeneration CubicStep CompositeFloors

/-- The number of roots of `f` modulo `n`. -/
noncomputable def rootCount (f : ℤ[X]) (n : ℕ) : ℕ :=
  Set.ncard {b : ZMod n | (f.map (Int.castRingHom (ZMod n))).IsRoot b}

/-- The mean number of roots mod `p` of `f` is `1`, in analytic density. -/
def KroneckerDensity (f : ℤ[X]) : Prop :=
  Tendsto (fun x : ℝ => (x - 1) * ∑' n : ℕ, (rootCount f n : ℝ) * pw x n) (𝓝[>] 1) (𝓝 1)

/-- `S = (X³ + 30)² − 6 (X³ + 30) + 36`. -/
noncomputable def sextic : ℤ[X] := (X ^ 3 + 30) ^ 2 - 6 * (X ^ 3 + 30) + 36

/-- The number of `ω` mod `n` with `ω² + ω + 1 = 0` and `−6(5 + ω)` a cube. -/
noncomputable def cubeCount (n : ℕ) : ℕ :=
  Set.ncard {ω : ZMod n | ω ^ 2 + ω + 1 = 0 ∧ ∃ b : ZMod n, b ^ 3 = -(6 * (5 + ω))}

/-! ## 1. The root count of the sextic -/

section Prime

variable {p : ℕ} [Fact p.Prime]

theorem c756_ne_zero (h2 : p ≠ 2) (h3 : p ≠ 3) (h7 : p ≠ 7) : (756 : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  intro h
  have h' : ((756 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have hfac : (756 : ℕ) = 2 ^ 2 * 3 ^ 3 * 7 := by norm_num
  rw [hfac] at h'
  rcases hp.dvd_mul.mp h' with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))
  · exact h7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)

theorem isRoot_sextic (b : ZMod p) :
    (sextic.map (Int.castRingHom (ZMod p))).IsRoot b ↔
      (b ^ 3 + 30) ^ 2 - 6 * (b ^ 3 + 30) + 36 = 0 := by
  simp [sextic, IsRoot.def]

theorem isPrimitiveRoot_of_phi3 (h3 : (3 : ZMod p) ≠ 0) {ω : ZMod p}
    (hω : ω ^ 2 + ω + 1 = 0) : IsPrimitiveRoot ω 3 := by
  have h1 : ω ≠ 1 := by
    rintro rfl
    exact h3 (by linear_combination hω)
  refine IsPrimitiveRoot.mk_of_lt ω (by norm_num) (by linear_combination (ω - 1) * hω) ?_
  intro l hl0 hl3
  interval_cases l
  · simpa using h1
  · intro h2
    apply h1
    have h4 : ω = -2 := by linear_combination hω - h2
    rw [h4] at h2
    exact absurd (by linear_combination h2 : (3 : ZMod p) = 0) h3

/-- The fibre `{b : b³ = a}` has `3` elements when `a ≠ 0` is a cube and `𝔽_p` has a primitive
cube root of unity. -/
theorem card_cube_fibre {ω a : ZMod p} (hω : IsPrimitiveRoot ω 3) (ha : a ≠ 0)
    (hex : ∃ b : ZMod p, b ^ 3 = a) :
    (Finset.univ.filter fun b : ZMod p => b ^ 3 = a).card = 3 := by
  classical
  have heq : (Finset.univ.filter fun b : ZMod p => b ^ 3 = a) = (nthRoots 3 a).toFinset := by
    ext b
    simp [mem_nthRoots]
  rw [heq, Multiset.toFinset_card_of_nodup (hω.nthRoots_nodup ha), hω.card_nthRoots]
  simp [hex]

/-- **The root count.** For `p ∉ {2, 3, 7}`, the number of roots of `S` mod `p` is three
times the number of `ω` with `−6(5 + ω)` a cube. -/
theorem rootCount_sextic (h2 : p ≠ 2) (h3 : p ≠ 3) (h7 : p ≠ 7) :
    rootCount sextic p = 3 * cubeCount p := by
  classical
  have h756 := c756_ne_zero h2 h3 h7
  have h6 : (6 : ZMod p) ≠ 0 := fun h => h756 (by linear_combination 126 * h)
  have h3' : (3 : ZMod p) ≠ 0 := fun h => h756 (by linear_combination 252 * h)
  have h21 : (21 : ZMod p) ≠ 0 := fun h => h756 (by linear_combination 36 * h)
  set R : Finset (ZMod p) :=
    Finset.univ.filter fun b => (b ^ 3 + 30) ^ 2 - 6 * (b ^ 3 + 30) + 36 = 0 with hR
  set Cs : Finset (ZMod p) :=
    Finset.univ.filter fun ω => ω ^ 2 + ω + 1 = 0 ∧ ∃ b : ZMod p, b ^ 3 = -(6 * (5 + ω))
    with hCs
  have hroot : rootCount sextic p = R.card := by
    rw [rootCount, Set.ncard_eq_toFinset_card']
    congr 1
    ext b
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq, hR, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact isRoot_sextic b
  have hcube : cubeCount p = Cs.card := by
    rw [cubeCount, Set.ncard_eq_toFinset_card']
    congr 1
    ext ω
    simp [hCs]
  have hRU : R = Cs.biUnion fun ω => Finset.univ.filter fun b => b ^ 3 = -(6 * (5 + ω)) := by
    ext b
    simp only [hR, hCs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hb
      refine ⟨-(b ^ 3 + 30) / 6, ⟨?_, b, ?_⟩, ?_⟩
      · field_simp
        linear_combination hb
      · field_simp; ring
      · field_simp; ring
    · rintro ⟨ω, ⟨hω, -⟩, hb⟩
      rw [hb]
      linear_combination 36 * hω
  have hdisj : (Cs : Set (ZMod p)).PairwiseDisjoint
      fun ω => Finset.univ.filter fun b => b ^ 3 = -(6 * (5 + ω)) := by
    intro ω _ ω' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro b hb hb'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
    apply hne
    have : (6 : ZMod p) * ω = 6 * ω' := by linear_combination hb - hb'
    exact mul_left_cancel₀ h6 this
  rw [hroot, hcube, hRU, Finset.card_biUnion hdisj]
  have hfib : ∀ ω ∈ Cs, (Finset.univ.filter fun b : ZMod p => b ^ 3 = -(6 * (5 + ω))).card = 3 := by
    intro ω hω
    simp only [hCs, Finset.mem_filter, Finset.mem_univ, true_and] at hω
    refine card_cube_fibre (isPrimitiveRoot_of_phi3 h3' hω.1) ?_ hω.2
    intro h0
    have h5 : ω = -5 := by
      have : (6 : ZMod p) * (5 + ω) = 0 := by linear_combination -h0
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h6
      · linear_combination h
    have := hω.1
    rw [h5] at this
    exact h21 (by linear_combination this)
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]

/-- At a prime, at most two `ω` are counted. -/
theorem cubeCount_le_two : cubeCount p ≤ 2 := by
  classical
  set q : (ZMod p)[X] := X ^ 2 + X + 1 with hqdef
  have hq : q.natDegree ≤ 2 := by rw [hqdef]; compute_degree
  have hq0 : q ≠ 0 := by
    intro h
    have h2 := congrArg (fun r : (ZMod p)[X] => r.coeff 2) h
    simp [hqdef, coeff_X, coeff_one] at h2
  rw [cubeCount, Set.ncard_eq_toFinset_card']
  have hsub : (Set.toFinset {ω : ZMod p | ω ^ 2 + ω + 1 = 0 ∧
      ∃ b : ZMod p, b ^ 3 = -(6 * (5 + ω))}) ⊆ q.roots.toFinset := by
    intro ω hω
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at hω
    rw [Multiset.mem_toFinset, mem_roots hq0]
    simpa [hqdef, IsRoot.def] using hω.1
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans ((card_roots' q).trans hq))

end Prime

/-! ## 2. The density -/

theorem pw_eq_zero_of_not_prime (x : ℝ) {n : ℕ} (hn : ¬ n.Prime) : pw x n = 0 := by
  simp [pw, hn]

theorem summable_cubeCount {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ => (cubeCount n : ℝ) * pw x n := by
  refine Summable.of_norm_bounded ((summable_pw hx).mul_left 2) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pw_nonneg x n), abs_of_nonneg (Nat.cast_nonneg _)]
  by_cases hn : n.Prime
  · have : Fact n.Prime := ⟨hn⟩
    have : (cubeCount n : ℝ) ≤ 2 := by exact_mod_cast cubeCount_le_two
    exact mul_le_mul_of_nonneg_right this (pw_nonneg x n)
  · simp [pw_eq_zero_of_not_prime x hn]

/-- The discrepancy between the two counts is supported on `{2, 3, 7}`. -/
theorem discrepancy_eq_zero (x : ℝ) {n : ℕ} (hn : n ∉ ({2, 3, 7} : Finset ℕ)) :
    ((rootCount sextic n : ℝ) - 3 * (cubeCount n : ℝ)) * pw x n = 0 := by
  by_cases hp : n.Prime
  · have : Fact n.Prime := ⟨hp⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [rootCount_sextic hn.1 hn.2.1 hn.2.2]
    push_cast
    ring
  · rw [pw_eq_zero_of_not_prime x hp, mul_zero]

/-- **The density of the cubic condition.** Under Kronecker's root-count theorem for the
sextic `S`, the mean over the primes of the number of `ω` with `−6(5 + ω)` a cube is `1/3`:

  `(x − 1) ∑_p #{ω : ω² + ω + 1 = 0, −6(5+ω) a cube mod p} · log p · p^{−x} → 1/3`. -/
theorem cube_density (hK : KroneckerDensity sextic) :
    Tendsto (fun x : ℝ => (x - 1) * ∑' n : ℕ, (cubeCount n : ℝ) * pw x n) (𝓝[>] 1)
      (𝓝 (1 / 3)) := by
  set T : Finset ℕ := {2, 3, 7} with hT
  let E : ℝ → ℝ := fun x => ∑ n ∈ T, ((rootCount sextic n : ℝ) - 3 * (cubeCount n : ℝ)) * pw x n
  -- the correction is continuous at `1`
  have hEcont : ContinuousAt E 1 := by
    refine tendsto_finsetSum _ fun n hn => ?_
    have hn0 : (n : ℝ) ≠ 0 := by
      simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hn
      rcases hn with rfl | rfl | rfl <;> norm_num
    have hc : ContinuousAt (fun x : ℝ => pw x n) 1 := by
      unfold pw
      exact (continuousAt_const).div (Real.continuous_const_rpow hn0).continuousAt
        (by positivity)
    exact (continuousAt_const.mul hc)
  have hE0 : Tendsto (fun x : ℝ => (x - 1) * E x) (𝓝[>] 1) (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x - 1) (𝓝[>] 1) (𝓝 0) := by
      have : Tendsto (fun x : ℝ => x - 1) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_id.sub continuous_const).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto E (𝓝[>] 1) (𝓝 (E 1)) := hEcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h1.mul h2
  -- the identity `∑ rootCount = 3 ∑ cubeCount + E` for `x > 1`
  have hid : ∀ x : ℝ, 1 < x → (x - 1) * ∑' n : ℕ, (cubeCount n : ℝ) * pw x n =
      ((x - 1) * ∑' n : ℕ, (rootCount sextic n : ℝ) * pw x n - (x - 1) * E x) / 3 := by
    intro x hx
    have hd : HasSum (fun n : ℕ => ((rootCount sextic n : ℝ) - 3 * (cubeCount n : ℝ)) * pw x n)
        (E x) := hasSum_sum_of_ne_finset_zero fun n hn => discrepancy_eq_zero x hn
    have hc := (summable_cubeCount hx).hasSum.mul_left 3
    have hsum := hc.add hd
    have hfun : (fun n : ℕ => 3 * ((cubeCount n : ℝ) * pw x n) +
        ((rootCount sextic n : ℝ) - 3 * (cubeCount n : ℝ)) * pw x n) =
        fun n : ℕ => (rootCount sextic n : ℝ) * pw x n := by
      funext n; ring
    rw [hfun] at hsum
    rw [hsum.tsum_eq]
    ring
  have hlim : Tendsto (fun x : ℝ =>
      ((x - 1) * ∑' n : ℕ, (rootCount sextic n : ℝ) * pw x n - (x - 1) * E x) / 3) (𝓝[>] 1)
      (𝓝 ((1 - 0) / 3)) := (hK.sub hE0).div_const 3
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hid x hx).symm

/-! ## 3. The link to the sequences -/

/-- **The cubic condition decides stage `3`.** For `p ≡ 1 (mod 3)` and a sequence whose term
at stage `2` is `X − ω`: the term at stage `3` is linear iff `−6(5 + ω)` is a cube, and has
degree `3` otherwise. -/
theorem ffSeq_three_natDegree_eq_one_iff {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1)
    (d : FFEMData p) {ω : ZMod p} (hω : ω ^ 2 + ω + 1 = 0) (h2 : d.ffSeq 2 = X - C ω) :
    ((d.ffSeq 3).natDegree = 1 ↔ ∃ b : ZMod p, b ^ 3 = -(6 * (5 + ω))) ∧
      ((d.ffSeq 3).natDegree = 3 ↔ ¬ ∃ b : ZMod p, b ^ 3 = -(6 * (5 + ω))) := by
  have h3 := three_ne_zero_of_one_mod_three hp3
  have hE : d.ffProd 2 + 1 = cubic ω := by
    rw [d.ffProd_succ 1, ffProd_one, h2, cubic]
  by_cases hcube : ∃ b : ZMod p, b ^ 3 = -(6 * (5 + ω))
  · obtain ⟨b, hb⟩ := hcube
    have hroot := cubic_root h3 hω hb
    have hdvd : X - C ((b - 1 + ω) / 3) ∣ d.ffProd 2 + 1 := by
      rw [hE]; exact dvd_iff_isRoot.mpr hroot
    have hle : (d.ffSeq 3).natDegree ≤ _ :=
      d.ffSeq_minimal 2 _ (monic_X_sub_C _) (irreducible_X_sub_C _) hdvd
    rw [natDegree_X_sub_C] at hle
    have hpos : 0 < (d.ffSeq 3).natDegree := (d.ffSeq_succ 2).2.1.natDegree_pos
    have h1 : (d.ffSeq 3).natDegree = 1 := by omega
    exact ⟨⟨fun _ => ⟨b, hb⟩, fun _ => h1⟩, ⟨fun h => by omega, fun h => absurd ⟨b, hb⟩ h⟩⟩
  · have hirr : Irreducible (d.ffProd 2 + 1) := by
      rw [hE]
      exact (cubic_irreducible_iff h3 hω).mpr fun b hb => hcube ⟨b, hb⟩
    have hseq := ffSeq_succ_eq_of_irreducible d 2 hirr
    have hdeg : (d.ffSeq 3).natDegree = 3 := by
      rw [hseq, hE, cubic]
      compute_degree!
    exact ⟨⟨fun h => by omega, fun h => absurd h hcube⟩, ⟨fun _ => hcube, fun _ => hdeg⟩⟩

end CubicDensity

end FunctionFieldAnalog
