import EM.FunctionField.DensityMC
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Kornblum's theorem, part 2: the von Mangoldt identity over `F_p[t]`

Throughout, "polynomial" means a polynomial over `F_p = ZMod p`, and `q = p`.

For a completely multiplicative function `φ` on polynomials (a monoid
homomorphism `F_p[t] →* ℂ`) we define

* `charSum φ n = A_n(φ) = ∑_{f monic, deg f = n} φ(f)`, the `n`-th coefficient of
  the `L`-series `L(u, φ) = ∑_f φ(f) u^{deg f}`;
* `psi φ n = Ψ_n(φ) = ∑_{(P, j) : j · deg P = n} deg P · φ(P)^j`, the sum running
  over monic irreducible `P` and `j ≥ 1`; this is the `n`-th coefficient of the
  logarithmic derivative `u L'(u, φ) / L(u, φ)` (the sum of `Λ(f) φ(f)` over
  monic `f` of degree `n`, where `Λ(P^j) = deg P`).

The main result is the **von Mangoldt identity** (`vonMangoldt_identity`)

  `n · A_n(φ) = ∑_{k ≤ n} Ψ_k(φ) · A_{n-k}(φ)`,

i.e. `u L' = L · Ψ` coefficient by coefficient. It is proved without Euler
products: unique factorisation gives `deg f = ∑_{(P, j) : P^j ∣ f} deg P`
(`sum_pow_dvd_eq_natDegree`), and the monic multiples of `P^j` of degree `n` are
`P^j · h` with `h` monic of degree `n - j deg P` (`sum_filter_dvd`).

Consequences: for the constant function `φ = 1` one gets `Ψ_n(1) = p^n` for
`n ≥ 1` (`psiNat_eq`: the prime polynomial theorem in von Mangoldt form), and
hence `|Ψ_n(φ)| ≤ p^n` whenever `|φ| ≤ 1` (`norm_psi_le`).
-/

namespace FunctionFieldAnalog.Kornblum

open Polynomial Finset

open scoped Classical

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Definitions -/

/-- The monic irreducible polynomials of degree between `1` and `n`. -/
noncomputable def irrUpTo (n : ℕ) : Finset (Polynomial (ZMod p)) :=
  (Icc 1 n).biUnion (fun e => ffIrredDeg p e)

theorem mem_irrUpTo {n : ℕ} {P : Polynomial (ZMod p)} :
    P ∈ irrUpTo p n ↔ P.Monic ∧ Irreducible P ∧ P.natDegree ≤ n := by
  simp only [irrUpTo, mem_biUnion, mem_Icc, mem_ffIrredDeg]
  constructor
  · rintro ⟨e, ⟨_, he⟩, hm, hi, hd⟩
    exact ⟨hm, hi, hd ▸ he⟩
  · rintro ⟨hm, hi, hd⟩
    exact ⟨P.natDegree, ⟨hi.natDegree_pos, hd⟩, hm, hi, rfl⟩

/-- `A_n(φ)`: the sum of `φ` over the monic polynomials of degree `n`. -/
noncomputable def charSum (φ : Polynomial (ZMod p) →* ℂ) (n : ℕ) : ℂ :=
  ∑ f ∈ ffMonicDeg p n, φ f

/-- `Ψ_n(φ)`: the sum of `deg P · φ(P)^j` over the pairs (monic irreducible `P`,
    exponent `j ≥ 1`) with `j · deg P = n`. -/
noncomputable def psi (φ : Polynomial (ZMod p) →* ℂ) (n : ℕ) : ℂ :=
  ∑ P ∈ irrUpTo p n, ∑ j ∈ Icc 1 n,
    if j * P.natDegree = n then (P.natDegree : ℂ) * φ P ^ j else 0

/-- `Ψ_n(1)` as a natural number: the sum of `deg P` over the pairs `(P, j)` with
    `j · deg P = n`. -/
noncomputable def psiNat (n : ℕ) : ℕ :=
  ∑ P ∈ irrUpTo p n, ∑ j ∈ Icc 1 n, if j * P.natDegree = n then P.natDegree else 0

/-! ## Reindexing `Ψ` -/

/-- In the definition of `Ψ_n` the index ranges may be enlarged to any `N ≥ n`. -/
theorem psi_eq_of_le (φ : Polynomial (ZMod p) →* ℂ) {n N : ℕ} (h : n ≤ N) :
    psi p φ n = ∑ P ∈ irrUpTo p N, ∑ j ∈ Icc 1 N,
      if j * P.natDegree = n then (P.natDegree : ℂ) * φ P ^ j else 0 := by
  unfold psi
  have hsub : irrUpTo p n ⊆ irrUpTo p N := fun P hP => by
    rw [mem_irrUpTo] at hP ⊢
    exact ⟨hP.1, hP.2.1, hP.2.2.trans h⟩
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun P hP => ?_
    have hPd : 0 < P.natDegree := ((mem_irrUpTo p).mp hP).2.1.natDegree_pos
    refine sum_subset (Icc_subset_Icc le_rfl h) fun j hj hj' => ?_
    split_ifs with heq
    · exfalso
      apply hj'
      rw [mem_Icc] at hj ⊢
      exact ⟨hj.1, heq ▸ Nat.le_mul_of_pos_right j hPd⟩
    · rfl
  · intro P hP hP'
    apply sum_eq_zero
    intro j hj
    split_ifs with heq
    · exfalso
      apply hP'
      rw [mem_irrUpTo] at hP ⊢
      exact ⟨hP.1, hP.2.1, heq ▸ Nat.le_mul_of_pos_left _ (mem_Icc.mp hj).1⟩
    · rfl

/-- **Reindexing by prime powers**: a weighted sum of the `Ψ_k`, `k ≤ N`, is a sum
    over the pairs `(P, j)` with `j · deg P ≤ N`. -/
theorem sum_psi_mul (φ : Polynomial (ZMod p) →* ℂ) (g : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ range (N + 1), psi p φ k * g k =
      ∑ P ∈ irrUpTo p N, ∑ j ∈ Icc 1 N,
        if j * P.natDegree ≤ N then
          (P.natDegree : ℂ) * φ P ^ j * g (j * P.natDegree) else 0 := by
  have h1 : ∀ k ∈ range (N + 1), psi p φ k * g k =
      ∑ P ∈ irrUpTo p N, ∑ j ∈ Icc 1 N,
        if j * P.natDegree = k then (P.natDegree : ℂ) * φ P ^ j * g k else 0 := by
    intro k hk
    rw [psi_eq_of_le p φ (Nat.lt_succ_iff.mp (mem_range.mp hk)), sum_mul]
    refine sum_congr rfl fun P _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun P _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  simp only [Finset.sum_ite_eq, mem_range, Nat.lt_succ_iff]

/-! ## Monic multiples of a monic polynomial -/

/-- The monic multiples of degree `n` of a monic `g` are `g · h` with `h` monic of
    degree `n - deg g`; hence the sum of `φ` over them is `φ(g) · A_{n - deg g}`. -/
theorem sum_filter_dvd (φ : Polynomial (ZMod p) →* ℂ) {g : Polynomial (ZMod p)}
    (hg : g.Monic) {n : ℕ} (h : g.natDegree ≤ n) :
    ∑ f ∈ (ffMonicDeg p n).filter (fun f => g ∣ f), φ f =
      φ g * charSum p φ (n - g.natDegree) := by
  rw [charSum, mul_sum]
  symm
  refine sum_bij (fun c _ => g * c) ?_ ?_ ?_ ?_
  · intro c hc
    rw [mem_ffMonicDeg] at hc
    rw [mem_filter, mem_ffMonicDeg]
    exact ⟨⟨hg.mul hc.1, by rw [hg.natDegree_mul hc.1, hc.2]; omega⟩, dvd_mul_right _ _⟩
  · intro c1 _ c2 _ h12
    exact mul_left_cancel₀ hg.ne_zero h12
  · intro f hf
    rw [mem_filter, mem_ffMonicDeg] at hf
    obtain ⟨⟨hfm, hfd⟩, c, rfl⟩ := hf
    have hcm : c.Monic := hg.of_mul_monic_left hfm
    refine ⟨c, ?_, rfl⟩
    rw [mem_ffMonicDeg]
    refine ⟨hcm, ?_⟩
    rw [hg.natDegree_mul hcm] at hfd
    omega
  · intro c _
    rw [map_mul]

/-- A monic polynomial has no monic multiple of smaller degree. -/
theorem filter_dvd_eq_empty {g : Polynomial (ZMod p)} {n : ℕ} (h : n < g.natDegree) :
    (ffMonicDeg p n).filter (fun f => g ∣ f) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro f hf hdvd
  rw [mem_ffMonicDeg] at hf
  have := natDegree_le_of_dvd hdvd hf.1.ne_zero
  omega

/-! ## The degree as a sum over prime-power divisors -/

/-- **Unique factorisation, in degree form**: for a monic polynomial `f` of degree
    `n`, the sum of `deg P` over the pairs (monic irreducible `P`, `j ≥ 1`) with
    `P^j ∣ f` equals `n`. (This is `∑_{g ∣ f} Λ(g) = deg f`.) -/
theorem sum_pow_dvd_eq_natDegree {f : Polynomial (ZMod p)} (hf : f.Monic) {n : ℕ}
    (hn : f.natDegree = n) :
    ∑ P ∈ irrUpTo p n, ∑ j ∈ Icc 1 n, (if P ^ j ∣ f then P.natDegree else 0) = n := by
  have hf0 := hf.ne_zero
  set nf := UniqueFactorizationMonoid.normalizedFactors f with hnf
  have hirr : ∀ g ∈ nf, Irreducible g := fun g hg =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor g hg
  have hmon : ∀ g ∈ nf, g.Monic := fun g hg => by
    have h1 := UniqueFactorizationMonoid.normalize_normalized_factor g hg
    rw [← h1]
    exact monic_normalize (hirr g hg).ne_zero
  have hprod : nf.prod = f := by
    have h := UniqueFactorizationMonoid.prod_normalizedFactors_eq hf0
    rwa [hf.normalize_eq_self] at h
  have hdeg : ∑ P ∈ nf.toFinset, nf.count P * P.natDegree = n := by
    rw [← hn]
    conv_rhs => rw [← hprod]
    rw [natDegree_multiset_prod_of_monic _ hmon, Finset.sum_multiset_map_count]
    simp [smul_eq_mul]
  have hcount : ∀ P : Polynomial (ZMod p), P.Monic → Irreducible P →
      ∀ j : ℕ, P ^ j ∣ f ↔ j ≤ nf.count P := by
    intro P hPm hPi j
    rw [pow_dvd_iff_le_emultiplicity,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPi hf0,
      hPm.normalize_eq_self]
    exact Nat.cast_le
  have hsub : nf.toFinset ⊆ irrUpTo p n := by
    intro P hP
    rw [Multiset.mem_toFinset] at hP
    rw [mem_irrUpTo]
    refine ⟨hmon P hP, hirr P hP, ?_⟩
    rw [← hn]
    exact natDegree_le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP) hf0
  refine Eq.trans ?_ hdeg
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun P hP => ?_
    have hP' := (mem_irrUpTo p).mp (hsub hP)
    have hPd : 0 < P.natDegree := hP'.2.1.natDegree_pos
    have hcn : nf.count P ≤ n := by
      have hdvd : P ^ nf.count P ∣ f := (hcount P hP'.1 hP'.2.1 _).mpr le_rfl
      have h1 := natDegree_le_of_dvd hdvd hf0
      rw [hP'.1.natDegree_pow, hn] at h1
      exact (Nat.le_mul_of_pos_right _ hPd).trans h1
    rw [← sum_filter, sum_const, smul_eq_mul]
    congr 1
    have hfil : (Icc 1 n).filter (fun j => P ^ j ∣ f) = Icc 1 (nf.count P) := by
      ext j
      simp only [mem_filter, mem_Icc, hcount P hP'.1 hP'.2.1]
      omega
    rw [hfil, Nat.card_Icc]
    omega
  · intro P hP hP'
    have hP'' := (mem_irrUpTo p).mp hP
    have hc0 : nf.count P = 0 := Multiset.count_eq_zero.mpr (by simpa using hP')
    apply sum_eq_zero
    intro j hj
    split_ifs with hdvd
    · exfalso
      rw [hcount P hP''.1 hP''.2.1, hc0] at hdvd
      have := (mem_Icc.mp hj).1
      omega
    · rfl

/-! ## The von Mangoldt identity -/

/-- **The von Mangoldt identity** `n · A_n(φ) = ∑_{k ≤ n} Ψ_k(φ) · A_{n-k}(φ)` for a
    completely multiplicative `φ`: the coefficientwise form of `u L' = L · Ψ`. -/
theorem vonMangoldt_identity (φ : Polynomial (ZMod p) →* ℂ) (n : ℕ) :
    (n : ℂ) * charSum p φ n = ∑ k ∈ range (n + 1), psi p φ k * charSum p φ (n - k) := by
  rw [sum_psi_mul p φ (fun k => charSum p φ (n - k)) n]
  have h1 : (n : ℂ) * charSum p φ n = ∑ f ∈ ffMonicDeg p n, ∑ P ∈ irrUpTo p n,
      ∑ j ∈ Icc 1 n, (if P ^ j ∣ f then (P.natDegree : ℂ) * φ f else 0) := by
    rw [charSum, mul_sum]
    refine sum_congr rfl fun f hf => ?_
    rw [mem_ffMonicDeg] at hf
    have h := sum_pow_dvd_eq_natDegree p hf.1 hf.2
    have h' : (n : ℂ) = ∑ P ∈ irrUpTo p n, ∑ j ∈ Icc 1 n,
        (if P ^ j ∣ f then (P.natDegree : ℂ) else 0) := by
      conv_lhs => rw [← h]
      push_cast
      rfl
    rw [h', sum_mul]
    refine sum_congr rfl fun P _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [h1, sum_comm]
  refine sum_congr rfl fun P hP => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have hPm := ((mem_irrUpTo p).mp hP).1
  have hpow : (P ^ j).Monic := hPm.pow j
  have hdegpow : (P ^ j).natDegree = j * P.natDegree := hPm.natDegree_pow j
  rw [← sum_filter, ← mul_sum]
  split_ifs with hle
  · rw [sum_filter_dvd p φ hpow (by rw [hdegpow]; exact hle), hdegpow, map_pow]
    ring
  · rw [filter_dvd_eq_empty p (by rw [hdegpow]; omega)]
    simp

/-! ## The trivial function: `Ψ_n(1) = p^n` -/

theorem psi_one (n : ℕ) : psi p 1 n = (psiNat p n : ℂ) := by
  simp [psi, psiNat]

theorem charSum_one (n : ℕ) : charSum p 1 n = (p : ℂ) ^ n := by
  simp [charSum, ffMonicDeg_card]

/-- **Prime polynomial theorem, von Mangoldt form**: `∑_{j · deg P = n} deg P = p^n`
    for `n ≥ 1`. -/
theorem psiNat_eq {n : ℕ} (hn : 0 < n) : psiNat p n = p ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h1 := vonMangoldt_identity p 1 (m + 1)
  have h0 := vonMangoldt_identity p 1 m
  simp only [charSum_one] at h0 h1
  rw [sum_range_succ] at h1
  have h2 : ∑ k ∈ range (m + 1), psi p 1 k * (p : ℂ) ^ (m + 1 - k) =
      p * ∑ k ∈ range (m + 1), psi p 1 k * (p : ℂ) ^ (m - k) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    have hk' : m + 1 - k = (m - k) + 1 := by have := mem_range.mp hk; omega
    rw [hk', pow_succ]
    ring
  rw [h2, ← h0, Nat.sub_self, pow_zero, mul_one, psi_one] at h1
  have h3 : ((psiNat p (m + 1) : ℕ) : ℂ) = ((p ^ (m + 1) : ℕ) : ℂ) := by
    push_cast at h1 ⊢
    linear_combination -h1
  exact_mod_cast h3

/-- `|Ψ_n(φ)| ≤ Ψ_n(1)` when `|φ| ≤ 1`. -/
theorem norm_psi_le (φ : Polynomial (ZMod p) →* ℂ) (hφ : ∀ f, ‖φ f‖ ≤ 1) (n : ℕ) :
    ‖psi p φ n‖ ≤ psiNat p n := by
  unfold psi psiNat
  push_cast
  refine (norm_sum_le _ _).trans (sum_le_sum fun P _ =>
    (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_))
  split_ifs
  · rw [norm_mul, norm_pow, Complex.norm_natCast]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (pow_le_one₀ (norm_nonneg _) (hφ P))
  · simp

end FunctionFieldAnalog.Kornblum
