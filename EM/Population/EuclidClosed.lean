import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# Euclid's construction with free choice of sub-product generates every prime

Euclid's argument produces a new prime from a finite set `I` of known primes: any prime
factor of `1 + ∏ I`. The Euclid–Mullin sequence, and every branch of the Euclid tree
(`EM/Stochastic/MixedTree.lean`), always takes `I` to be **all** primes found so far on
the branch. If instead `I` may be **any** finite subset of the primes found so far, every
prime is produced.

## Main results

* `IsEuclidClosed S` — `S` is a set of primes containing every prime factor of
  `1 + ∏ I` for every finite `I ⊆ S`.
* `IsEuclidClosed.mem_of_prime` — a Euclid-closed set contains every prime.
* `Generated` — the primes obtainable from nothing by the rule; `generated_iff_prime`:
  these are all the primes.

This is the weakening of `MixedMC` in which the constraint "multiply the whole product"
is dropped. It is a theorem of A. R. Booker (*A variant of the Euclid–Mullin sequence
containing every prime*, J. Integer Seq. 19 (2016)); the stronger statement that primes
below `q` already suffice to produce `q` is Booker–Pomerance (Proc. AMS 145 (2017)). The
proof below was written for this file and has not been compared with Booker's.

## Proof

Suppose `q ∉ S`. Call a residue class mod `q` *recurrent* if it contains infinitely many
primes of `S`, and let `F` be the (finite) set of primes of `S` in non-recurrent classes,
with product `f`. Let `A` be the set of residues attainable as products of distinct
recurrent primes avoiding any prescribed finite set; `A` is closed under multiplication
and `0 ∉ A`. For `a ∈ A` the number `1 + f·N`, with `N ≡ a` a product of recurrent
primes, has all its prime factors in `S` and outside `F`, so `f·a + 1 ∈ A`. Thus
`a ↦ f·a + 1` permutes the finite set `A`, and so does `a ↦ c·a` for `c ∈ A`. Summing:
if `A ≠ {1}` then `∑ A = 0`, whence `|A| ≡ 0 (mod q)` with `1 ≤ |A| < q`; if `A = {1}`
then `f ≡ 0`. Both are impossible.

## What this does not give

The gap to `MixedMC` is exactly the restriction of `I` to the prefixes of one branch. The
argument uses products of many primes from one residue class, which a branch prefix
cannot select.
-/

open Finset

namespace EuclidClosed

/-- A set of primes closed under Euclid's construction with free sub-products: for every
    finite `I ⊆ S`, every prime factor of `1 + ∏ I` is in `S`. -/
def IsEuclidClosed (S : Set ℕ) : Prop :=
  (∀ p ∈ S, p.Prime) ∧
    ∀ I : Finset ℕ, (↑I : Set ℕ) ⊆ S → ∀ p : ℕ, p.Prime → p ∣ (∏ i ∈ I, i) + 1 → p ∈ S

/-- The primes of `S` in the residue class `c` mod `q`. -/
def fibre (S : Set ℕ) (q : ℕ) (c : ZMod q) : Set ℕ := {p | p ∈ S ∧ ((p : ℕ) : ZMod q) = c}

/-- The primes of `S` whose residue class mod `q` contains only finitely many primes of `S`. -/
def nonRec (S : Set ℕ) (q : ℕ) : Set ℕ := {p | p ∈ S ∧ (fibre S q ((p : ℕ) : ZMod q)).Finite}

/-- Residues attainable as a product of distinct recurrent primes of `S` avoiding any
    prescribed finite set. -/
def Attain (S : Set ℕ) (q : ℕ) : Set (ZMod q) :=
  {a | ∀ B : Finset ℕ, ∃ J : Finset ℕ,
    (∀ j ∈ J, j ∈ S ∧ j ∉ nonRec S q) ∧ Disjoint J B ∧ (((∏ j ∈ J, j : ℕ) : ℕ) : ZMod q) = a}

variable {S : Set ℕ} {q : ℕ}

theorem nonRec_finite (S : Set ℕ) (q : ℕ) [NeZero q] : (nonRec S q).Finite := by
  have hsub : nonRec S q ⊆ ⋃ c ∈ {c : ZMod q | (fibre S q c).Finite}, fibre S q c := by
    rintro p ⟨hp, hfin⟩
    exact Set.mem_biUnion (x := ((p : ℕ) : ZMod q)) hfin ⟨hp, rfl⟩
  exact (Set.Finite.biUnion (Set.toFinite _) (fun c hc => hc)).subset hsub

theorem one_mem_attain : (1 : ZMod q) ∈ Attain S q :=
  fun B => ⟨∅, by simp, by simp, by simp⟩

theorem mul_mem_attain {a b : ZMod q} (ha : a ∈ Attain S q) (hb : b ∈ Attain S q) :
    a * b ∈ Attain S q := by
  intro B
  obtain ⟨J₁, h₁S, h₁B, h₁⟩ := ha B
  obtain ⟨J₂, h₂S, h₂B, h₂⟩ := hb (B ∪ J₁)
  have hsplit := Finset.disjoint_union_right.mp h₂B
  refine ⟨J₁ ∪ J₂, ?_, ?_, ?_⟩
  · intro j hj
    rcases Finset.mem_union.mp hj with h | h
    exacts [h₁S j h, h₂S j h]
  · exact Finset.disjoint_union_left.mpr ⟨h₁B, hsplit.1⟩
  · rw [Finset.prod_union hsplit.2.symm, Nat.cast_mul, h₁, h₂]

/-- A recurrent prime's residue is attainable. -/
theorem cast_mem_attain {p : ℕ} (hp : p ∈ S) (hpF : p ∉ nonRec S q) :
    ((p : ℕ) : ZMod q) ∈ Attain S q := by
  intro B
  have hinf : (fibre S q ((p : ℕ) : ZMod q)).Infinite := fun hfin => hpF ⟨hp, hfin⟩
  obtain ⟨p', ⟨hp'S, hp'c⟩, hp'B⟩ := hinf.exists_notMem_finset B
  refine ⟨{p'}, ?_, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    refine ⟨hp'S, fun hF' => hinf ?_⟩
    rw [← hp'c]
    exact hF'.2
  · exact Finset.disjoint_singleton_left.mpr hp'B
  · rw [Finset.prod_singleton]
    exact hp'c

/-- A positive integer all of whose prime factors are recurrent primes of `S` has an
    attainable residue. -/
theorem natCast_mem_attain :
    ∀ n : ℕ, 1 ≤ n → (∀ p : ℕ, p.Prime → p ∣ n → p ∈ S ∧ p ∉ nonRec S q) →
      ((n : ℕ) : ZMod q) ∈ Attain S q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hpr
    rcases Nat.eq_or_lt_of_le hn with h1 | h1
    · rw [← h1, Nat.cast_one]
      exact one_mem_attain
    · have hmp := Nat.minFac_prime (by omega : n ≠ 1)
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      have hkpos : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, mul_zero] at hk; omega
        · exact h0
      have hklt : k < n := by
        calc k < 2 * k := by omega
          _ ≤ n.minFac * k := Nat.mul_le_mul_right k hmp.two_le
          _ = n := hk.symm
      have hkA := ih k hklt hkpos
        (fun p hp hpk => hpr p hp (by rw [hk]; exact Dvd.dvd.mul_left hpk _))
      have hm := hpr _ hmp (Nat.minFac_dvd n)
      have hprod := mul_mem_attain (cast_mem_attain hm.1 hm.2) hkA
      rw [← Nat.cast_mul, ← hk] at hprod
      exact hprod

/-- **A Euclid-closed set contains every prime.** -/
theorem IsEuclidClosed.mem_of_prime (hS : IsEuclidClosed S) (hqp : q.Prime) : q ∈ S := by
  by_contra hq
  have : Fact q.Prime := ⟨hqp⟩
  have hne : ∀ p ∈ S, ((p : ℕ) : ZMod q) ≠ 0 := by
    intro p hp
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hq (((Nat.prime_dvd_prime_iff_eq hqp (hS.1 p hp)).mp hd) ▸ hp)
  have hFfin := nonRec_finite S q
  have hFS : nonRec S q ⊆ S := fun p hp => hp.1
  have hFmem : ∀ p, p ∈ hFfin.toFinset ↔ p ∈ nonRec S q := fun p => hFfin.mem_toFinset
  -- `0` is not attainable
  have hA0 : (0 : ZMod q) ∉ Attain S q := by
    intro h0
    obtain ⟨J, hJS, -, hJ⟩ := h0 ∅
    rw [Nat.cast_prod] at hJ
    exact (Finset.prod_ne_zero_iff.mpr (fun j hj => hne j (hJS j hj).1)) hJ
  -- the product of the non-recurrent primes, mod `q`
  obtain ⟨fq, hfq⟩ : ∃ fq : ZMod q, fq = ((∏ p ∈ hFfin.toFinset, p : ℕ) : ZMod q) := ⟨_, rfl⟩
  have hfq0 : fq ≠ 0 := by
    rw [hfq, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    obtain ⟨p, hpF, hqp'⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hqp) _).mp hd
    have hpS := hFS ((hFmem p).mp hpF)
    exact hq (((Nat.prime_dvd_prime_iff_eq hqp (hS.1 p hpS)).mp hqp') ▸ hpS)
  -- the key closure: `a ↦ f·a + 1` preserves `Attain`
  have hAstep : ∀ a ∈ Attain S q, fq * a + 1 ∈ Attain S q := by
    intro a ha
    obtain ⟨J, hJS, hJB, hJ⟩ := ha hFfin.toFinset
    have hIS : (↑(hFfin.toFinset ∪ J) : Set ℕ) ⊆ S := by
      intro x hx
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hx) with h | h
      · exact hFS ((hFmem x).mp h)
      · exact (hJS x h).1
    have hprod : ∏ i ∈ hFfin.toFinset ∪ J, i = (∏ p ∈ hFfin.toFinset, p) * ∏ j ∈ J, j :=
      Finset.prod_union hJB.symm
    have hmem := natCast_mem_attain (S := S) (q := q) ((∏ i ∈ hFfin.toFinset ∪ J, i) + 1)
      (by omega) (by
        intro p hp hpd
        refine ⟨hS.2 _ hIS p hp hpd, fun hpF => ?_⟩
        have hpI : p ∣ ∏ i ∈ hFfin.toFinset ∪ J, i :=
          Finset.dvd_prod_of_mem _ (Finset.mem_union_left _ ((hFmem p).mpr hpF))
        exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpI).mp hpd)))
    rw [hprod, Nat.cast_add, Nat.cast_mul, Nat.cast_one, hJ, ← hfq] at hmem
    exact hmem
  -- `Attain` as a finset
  have hAfin : (Attain S q).Finite := Set.toFinite _
  have hAf : ∀ a, a ∈ hAfin.toFinset ↔ a ∈ Attain S q := fun a => hAfin.mem_toFinset
  -- an injective self-map of `Attain` preserves the sum
  have hperm : ∀ g : ZMod q → ZMod q, Function.Injective g →
      (∀ a ∈ Attain S q, g a ∈ Attain S q) →
      ∑ a ∈ hAfin.toFinset, g a = ∑ a ∈ hAfin.toFinset, a := by
    intro g hg hgA
    have himg : hAfin.toFinset.image g = hAfin.toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact (hAf _).mpr (hgA a ((hAf a).mp ha))
      · rw [Finset.card_image_of_injective _ hg]
    calc ∑ a ∈ hAfin.toFinset, g a = ∑ x ∈ hAfin.toFinset.image g, x :=
          (Finset.sum_image (f := fun x => x) (fun _ _ _ _ h => hg h)).symm
      _ = ∑ a ∈ hAfin.toFinset, a := by rw [himg]
  have h1 : fq * ∑ a ∈ hAfin.toFinset, a + (hAfin.toFinset.card : ZMod q) =
      ∑ a ∈ hAfin.toFinset, a := by
    have := hperm (fun a => fq * a + 1)
      (fun a b h => mul_left_cancel₀ hfq0 (add_right_cancel (h : fq * a + 1 = fq * b + 1)))
      hAstep
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
      at this
    exact this
  have hcard_pos : 0 < hAfin.toFinset.card :=
    Finset.card_pos.mpr ⟨1, (hAf 1).mpr one_mem_attain⟩
  have hcard_lt : hAfin.toFinset.card < q := by
    have hsub : hAfin.toFinset ⊆ (Finset.univ : Finset (ZMod q)).erase 0 := fun a ha =>
      Finset.mem_erase.mpr ⟨fun h0 => hA0 (h0 ▸ (hAf a).mp ha), Finset.mem_univ _⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at hle
    have := hqp.two_le
    omega
  by_cases hex : ∃ c ∈ Attain S q, c ≠ 1
  · obtain ⟨c, hc, hc1⟩ := hex
    have hc0 : c ≠ 0 := fun h => hA0 (h ▸ hc)
    have h2 := hperm (fun a => c * a)
      (fun a b h => mul_left_cancel₀ hc0 (h : c * a = c * b))
      (fun a ha => mul_mem_attain hc ha)
    rw [← Finset.mul_sum] at h2
    have hσ : ∑ a ∈ hAfin.toFinset, a = 0 := by
      have : (c - 1) * ∑ a ∈ hAfin.toFinset, a = 0 := by rw [sub_mul, one_mul, h2, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1)
    rw [hσ, mul_zero, zero_add] at h1
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp h1
    exact absurd (Nat.le_of_dvd hcard_pos hdvd) (by omega)
  · have hall : ∀ c ∈ Attain S q, c = 1 := fun c hc => by
      by_contra h
      exact hex ⟨c, hc, h⟩
    have h := hall _ (hAstep 1 one_mem_attain)
    exact hfq0 (by linear_combination h)

/-- The set of all primes is Euclid-closed, so it is the unique Euclid-closed set. -/
theorem isEuclidClosed_primes : IsEuclidClosed {p : ℕ | p.Prime} :=
  ⟨fun _ hp => hp, fun _ _ _ hp _ => hp⟩

theorem IsEuclidClosed.eq_primes (hS : IsEuclidClosed S) : S = {p : ℕ | p.Prime} :=
  Set.eq_of_subset_of_subset (fun p hp => hS.1 p hp) (fun _ hp => hS.mem_of_prime hp)

/-- The primes **generated from nothing** by Euclid's construction with free sub-products:
    `p` is generated if it is a prime factor of `1 + ∏ I` for a finite set `I` of generated
    primes. (With `I = ∅` this gives `2`.) -/
inductive Generated : ℕ → Prop
  | step (I : Finset ℕ) (hI : ∀ i ∈ I, Generated i) (p : ℕ) (hp : p.Prime)
      (hd : p ∣ (∏ i ∈ I, i) + 1) : Generated p

theorem Generated.prime {p : ℕ} (h : Generated p) : p.Prime := by
  cases h with
  | step I hI p hp hd => exact hp

/-- **Every prime is generated**: Euclid's construction, with the sub-product chosen
    freely at each step, produces all the primes. -/
theorem generated_iff_prime {p : ℕ} : Generated p ↔ p.Prime := by
  refine ⟨Generated.prime, fun hp => ?_⟩
  have hclosed : IsEuclidClosed {p : ℕ | Generated p} :=
    ⟨fun _ h => Generated.prime h, fun I hI p hp hd => Generated.step I (fun i hi => hI hi) p hp hd⟩
  exact hclosed.mem_of_prime hp

end EuclidClosed
