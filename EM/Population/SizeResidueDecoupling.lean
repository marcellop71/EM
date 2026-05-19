import EM.Population.SeededGrowth
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.ChineseRemainder

/-!
# The joint object: walk position and multiplier size

The residue walk sees `P mod q`; the growth constant sees `log minFac(P+1) / log P`.  How are
the two coordinates coupled along a `T`-orbit?  Exactly through the prime/composite bit, and
not otherwise:

* **Prime stage** (`multiplier_residue_of_prime_stage`).  If `P + 1` is prime the multiplier
  is `P + 1` itself, so its residue is *forced* by the walk position: `minFac(P+1) ≡ w + 1`.
  This is the autonomous branch `w ↦ w(w+1)` of `AutonomousBranch`, and it is the branch on
  which `C > 0` lives (`DefectTelescope`, `SeededGrowth`).
* **Composite stage** (`exists_seed_composite_residue_size`).  In the ensemble, every walk
  position `w ≠ −1`, every unit residue `a`, and every size bound `K` are realized together:
  there is a squarefree seed `m` with `m ≡ w (mod q)`, `m + 1` composite,
  `minFac(m+1) ≡ a (mod q)` and `minFac(m+1) ≥ K`.  Construction: `m = 2m'` with `m'` a
  Dirichlet prime in a CRT class chosen so that `2m'+1 ≡ 0 (mod p)` for a Dirichlet prime
  `p ≡ a`, `p > K`, and `2m'+1 ≡ 2 (mod r)` for every other odd prime `r < p`, `≡ w+1 ≠ 0
  (mod q)`.  Then `minFac(2m'+1) = p`.

So the size coordinate constrains the residue coordinate only through primality of the
Euclid number.  On `{C = 0}` (composite stages cofinally) the growth projection therefore
carries no residue information beyond "the walk is not on its autonomous branch at these
stages" — which is why the two projections are not on a par, and why nothing above the floor
came from the growth side.  This is an ensemble (population) statement about seeds; along the
orbit of `2` the pairs `(w_n, size_n)` are what they are (orbit-specificity, Dead Ends #90/#117).
-/

noncomputable section

open Finset

namespace SizeResidueDecoupling

/-- **Prime stage: the residue is forced by the position.** -/
theorem multiplier_residue_of_prime_stage {P : ℕ} (hP : Nat.Prime (P + 1)) (q : ℕ) :
    (Nat.minFac (P + 1) : ZMod q) = (P : ZMod q) + 1 := by
  rw [Nat.Prime.minFac_eq hP]; push_cast; rfl

/-- The seeded form: at a prime stage of any orbit, `genSeq m n ≡ genProd m n + 1`. -/
theorem genSeq_residue_of_prime_stage {m n : ℕ} (h : Nat.Prime (genProd m n + 1)) (q : ℕ) :
    (genSeq m n : ZMod q) = (genProd m n : ZMod q) + 1 :=
  multiplier_residue_of_prime_stage h q

/-! ## The composite-stage realization theorem -/

/-- The odd primes up to `p`. -/
def oddPrimesLe (p : ℕ) : Finset ℕ := (range (p + 1)).filter (fun r => Nat.Prime r ∧ r ≠ 2)

theorem mem_oddPrimesLe {p r : ℕ} : r ∈ oddPrimesLe p ↔ r ≤ p ∧ Nat.Prime r ∧ r ≠ 2 := by
  unfold oddPrimesLe
  rw [Finset.mem_filter, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

theorem two_isUnit_of_odd_prime {r : ℕ} (hr : Nat.Prime r) (hr2 : r ≠ 2) :
    IsUnit (2 : ZMod r) := by
  have := (ZMod.isUnit_iff_coprime 2 r).mpr ((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2))
  simpa using this

/-- **Composite stage: position, residue and size are jointly free in the ensemble.**
For an odd prime `q`, a walk position `w ≠ −1`, a unit residue `a` and a bound `K`, there is a
squarefree seed `m ≡ w (mod q)` whose Euclid number `m + 1` is composite with least prime
factor `≡ a (mod q)` and `≥ K`. -/
theorem exists_seed_composite_residue_size {q : ℕ} (hq : Nat.Prime q) (hq2 : q ≠ 2)
    {w a : ZMod q} (hw : IsUnit w) (hw1 : w ≠ -1) (ha : IsUnit a) (K : ℕ) :
    ∃ m : ℕ, Squarefree m ∧ 2 ≤ m ∧ (m : ZMod q) = w ∧ ¬ Nat.Prime (m + 1) ∧
      (Nat.minFac (m + 1) : ZMod q) = a ∧ K ≤ Nat.minFac (m + 1) := by
  have : NeZero q := ⟨hq.ne_zero⟩
  have hqf : Fact (Nat.Prime q) := ⟨hq⟩
  -- Step 1: a Dirichlet prime `p ≡ a (mod q)`, `p > max K q`
  obtain ⟨p, hpgt, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod ha (max K q)
  have hpK : K < p := lt_of_le_of_lt (le_max_left _ _) hpgt
  have hpq : q < p := lt_of_le_of_lt (le_max_right _ _) hpgt
  have hp2 : p ≠ 2 := by have := hq.two_le; omega
  have : NeZero p := ⟨hp.ne_zero⟩
  -- Step 2: the CRT class
  set t := oddPrimesLe p with ht
  have hqt : q ∈ t := mem_oddPrimesLe.mpr ⟨hpq.le, hq, hq2⟩
  have hpt : p ∈ t := mem_oddPrimesLe.mpr ⟨le_rfl, hp, hp2⟩
  -- residues: `w/2` at `q`, `−1/2` at `p`, `1/2` elsewhere
  let res : ℕ → ℕ := fun r =>
    if r = q then (w * (2 : ZMod q)⁻¹).val
    else if r = p then (-(2 : ZMod p)⁻¹).val
    else ((2 : ZMod r)⁻¹).val
  have hs : ∀ r ∈ t, (id r) ≠ 0 := fun r hr => (mem_oddPrimesLe.mp hr).2.1.ne_zero
  have hpp : Set.Pairwise (t : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro r hr r' hr' hne
    exact (Nat.coprime_primes (mem_oddPrimesLe.mp hr).2.1 (mem_oddPrimesLe.mp hr').2.1).mpr hne
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset res id t hs hpp
  simp only [id] at hc
  -- each residue is a unit mod its prime, hence `c` is coprime to every `r ∈ t`
  have hres_unit : ∀ r ∈ t, IsUnit ((res r : ℕ) : ZMod r) := by
    intro r hr
    obtain ⟨_, hr', hr2⟩ := mem_oddPrimesLe.mp hr
    have : NeZero r := ⟨hr'.ne_zero⟩
    have : Fact (Nat.Prime r) := ⟨hr'⟩
    simp only [res]
    split_ifs with h1 h2
    · subst h1
      rw [ZMod.natCast_zmod_val]
      exact hw.mul (two_isUnit_of_odd_prime hq hq2).inv
    · subst h2
      rw [ZMod.natCast_zmod_val]
      exact (two_isUnit_of_odd_prime hp hp2).inv.neg
    · rw [ZMod.natCast_zmod_val]
      exact (two_isUnit_of_odd_prime hr' hr2).inv
  have hc_mod : ∀ r ∈ t, ((c : ℕ) : ZMod r) = ((res r : ℕ) : ZMod r) := by
    intro r hr
    rw [ZMod.natCast_eq_natCast_iff']
    exact hc r hr
  have hc_unit : ∀ r ∈ t, IsUnit ((c : ℕ) : ZMod r) := fun r hr =>
    (hc_mod r hr) ▸ hres_unit r hr
  set L := ∏ r ∈ t, r with hL
  have hLpos : 0 < L := Finset.prod_pos fun r hr => (mem_oddPrimesLe.mp hr).2.1.pos
  have hcL : Nat.Coprime (c : ℕ) L := by
    rw [hL, Nat.coprime_prod_right_iff]
    intro r hr
    exact (ZMod.isUnit_iff_coprime _ _).mp (hc_unit r hr)
  have : NeZero L := ⟨hLpos.ne'⟩
  -- Step 3: a Dirichlet prime `m' > L` in the class of `c` mod `L`
  obtain ⟨m', hm'L, hm', hm'c⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((ZMod.isUnit_iff_coprime _ _).mpr hcL) L
  -- `m' ≡ res r (mod r)` for every `r ∈ t`
  have hm'_mod : ∀ r ∈ t, ((m' : ℕ) : ZMod r) = ((res r : ℕ) : ZMod r) := by
    intro r hr
    have hdvd : r ∣ L := Finset.dvd_prod_of_mem _ hr
    have h1 : m' % L = (c : ℕ) % L := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hm'c
    rw [ZMod.natCast_eq_natCast_iff']
    have h2 := hc r hr
    calc m' % r = m' % L % r := (Nat.mod_mod_of_dvd m' hdvd).symm
      _ = (c : ℕ) % L % r := by rw [h1]
      _ = (c : ℕ) % r := Nat.mod_mod_of_dvd _ hdvd
      _ = res r % r := h2
  -- `L ≥ p`, so `m' > p ≥ 3`
  have hpL : p ≤ L := Finset.single_le_prod' (fun r hr => (mem_oddPrimesLe.mp hr).2.1.one_lt.le)
    hpt
  have hm'p : p < m' := lt_of_le_of_lt hpL hm'L
  have hm'2 : m' ≠ 2 := by have := hq.two_le; omega
  have hm'odd : Nat.Coprime 2 m' := (Nat.coprime_primes Nat.prime_two hm').mpr (Ne.symm hm'2)
  -- `p ∣ 2 m' + 1`
  have hdvd : p ∣ 2 * m' + 1 := by
    have h := hm'_mod p hpt
    have hpq' : p ≠ q := hpq.ne'
    simp only [res, hpq', if_false, if_true] at h
    rw [ZMod.natCast_zmod_val] at h
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [h]
    linear_combination -(ZMod.mul_inv_of_unit _ (two_isUnit_of_odd_prime hp hp2))
  -- `minFac (2 m' + 1) = p`: no smaller prime divides
  have hmin : Nat.minFac (2 * m' + 1) = p := by
    apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le hdvd)
    by_contra hlt
    push Not at hlt
    have hne1 : 2 * m' + 1 ≠ 1 := by omega
    have hr := Nat.minFac_prime hne1
    have hrd := Nat.minFac_dvd (2 * m' + 1)
    set r := Nat.minFac (2 * m' + 1) with hr_def
    by_cases hr2 : r = 2
    · rw [hr2] at hrd
      omega
    · have hrt : r ∈ t := mem_oddPrimesLe.mpr ⟨hlt.le, hr, hr2⟩
      have : NeZero r := ⟨hr.ne_zero⟩
      have h := hm'_mod r hrt
      have hzero : ((2 * m' + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hrd
      by_cases hrq : r = q
      · -- residue `w + 1 ≠ 0`
        subst hrq
        simp only [res, if_true] at h
        rw [ZMod.natCast_zmod_val] at h
        push_cast at hzero
        rw [h] at hzero
        have h2 := ZMod.mul_inv_of_unit _ (two_isUnit_of_odd_prime hr hr2)
        have : w + 1 = 0 := by linear_combination hzero - w * h2
        exact hw1 (eq_neg_of_add_eq_zero_left this)
      · have hrp : r ≠ p := hlt.ne
        simp only [res, hrq, hrp, if_false] at h
        rw [ZMod.natCast_zmod_val] at h
        push_cast at hzero
        rw [h] at hzero
        have h2' := ZMod.mul_inv_of_unit _ (two_isUnit_of_odd_prime hr hr2)
        -- `1 + 1 = 0` in `ZMod r` means `r ∣ 2`
        have h2 : ((2 : ℕ) : ZMod r) = 0 := by
          have : (2 : ZMod r) = 0 := by linear_combination hzero - h2'
          exact_mod_cast this
        rw [ZMod.natCast_eq_zero_iff] at h2
        have := Nat.le_of_dvd (by norm_num) h2
        have := hr.two_le
        omega
  -- the seed
  refine ⟨2 * m', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- squarefree
    exact (Nat.squarefree_mul hm'odd).mpr ⟨Nat.prime_two.squarefree, hm'.squarefree⟩
  · have := hm'.two_le; omega
  · -- `2 m' ≡ w`
    have h := hm'_mod q hqt
    simp only [res, if_true] at h
    rw [ZMod.natCast_zmod_val] at h
    push_cast
    rw [h]
    linear_combination w * ZMod.mul_inv_of_unit _ (two_isUnit_of_odd_prime hq hq2)
  · -- composite
    intro hprime
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p hdvd) with h | h
    · exact hp.one_lt.ne' h
    · omega
  · rw [hmin]; exact hpa
  · rw [hmin]; exact hpK.le

/-- **Landscape.**  The two coordinates are coupled exactly through primality: at a prime stage
the multiplier residue is `w + 1`; at composite stages every `(w ≠ −1, a, size ≥ K)` occurs. -/
theorem size_residue_landscape :
    (∀ {P : ℕ}, Nat.Prime (P + 1) → ∀ q : ℕ, (Nat.minFac (P + 1) : ZMod q) = (P : ZMod q) + 1) ∧
    (∀ {q : ℕ}, Nat.Prime q → q ≠ 2 → ∀ {w a : ZMod q}, IsUnit w → w ≠ -1 → IsUnit a → ∀ K : ℕ,
      ∃ m : ℕ, Squarefree m ∧ 2 ≤ m ∧ (m : ZMod q) = w ∧ ¬ Nat.Prime (m + 1) ∧
        (Nat.minFac (m + 1) : ZMod q) = a ∧ K ≤ Nat.minFac (m + 1)) :=
  ⟨fun hP q => multiplier_residue_of_prime_stage hP q, by
    intro q hq hq2 w a hw hw1 ha K
    exact exists_seed_composite_residue_size hq hq2 hw hw1 ha K⟩

end SizeResidueDecoupling

end
