import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

/-!
# The Euclid tree with exponents `1` or `2` reaches every prime

A branch of the Euclid tree (`EM/Stochastic/MixedTree.lean`) holds a finite set `D` of
primes and extends it by any prime factor of `1 + ∏ D`. Whether every prime is reached
(`MixedMC`) is open. Here each prime of `D` may enter the product with exponent `1` **or**
`2`: `D` is extended by any prime factor of `1 + ∏_{r ∈ D} r ^ e r` with `e r ∈ {1, 2}`.
Every prime must still be used; none may be dropped.

## Main results

* `Reach D₀ D` — `D` is obtained from the finite set `D₀` by such extensions.
* `exists_reach_mem` — from any finite set of primes `D₀`, every prime `q` is reached.
* `exists_reach_superset` — hence every finite set of primes is contained in one node.
* `exists_node_mem` — the case `D₀ = ∅`, whose first step is `1 + 1 = 2`.

With all exponents equal to `1` this is the statement `MixedMC`, so the theorem is the
weakening of `MixedMC` (hence of Mullin's conjecture) obtained by allowing squares.

## Proof

Suppose `q` is never reached from `D₀`. For a node `D` let `G D ⊆ (ℤ/q)ˣ` be the residues
of the admissible products. Adjoining a prime of class `c` gives `G (D ∪ {p}) = c·G D ∪
c²·G D`, so `|G|` never decreases; choose `D` with `|G D|` maximal. Then `c²·G D ⊆ c·G D`,
so `c·G D = G D`: the class of every prime factor of every admissible `N + 1` lies in the
stabiliser `T` of `G D`. Hence `x + 1 ∈ T` for all `x ∈ G D`. Fix `a ∈ G D`; since
`T·a ⊆ G D`, the map `h ↦ a·h + 1` sends `T` into `T`, so it permutes the finite set `T`,
as does `h ↦ c·h` for `c ∈ T`. If `T ≠ {1}` then `∑ T = 0`, and comparing sums gives
`|T| ≡ 0 (mod q)` with `1 ≤ |T| < q`; if `T = {1}` then `a = 0`. Both are impossible
(`no_affine_stable`).

## Where the squares are used

Only in `c²·G ⊆ c·G ⟹ c·G = G`. With exponent `1` alone, `G D` is a single residue and
`|G|` carries no information; that case is `MixedMC`.

## Status

Not found in the literature consulted (Booker 2016, Booker–Pomerance 2017, Booker–Irvine
2016, Wooley 2017 by title); no systematic search was made. The same argument with
"optional factor" in place of "optional square" reproves Booker's free-sub-product theorem
(`EM/Population/EuclidClosed.lean`).
-/

open Finset

namespace SquareTree

/-- `Reach D₀ D`: the set `D` is obtained from `D₀` by repeatedly adjoining a prime factor
    of `1 + ∏_{r ∈ D} r ^ e r`, where every exponent `e r` is `1` or `2`. -/
inductive Reach (D₀ : Finset ℕ) : Finset ℕ → Prop
  | refl : Reach D₀ D₀
  | step {D : Finset ℕ} (hD : Reach D₀ D) (e : ℕ → ℕ) (he : ∀ r ∈ D, e r = 1 ∨ e r = 2)
      (p : ℕ) (hp : p.Prime) (hd : p ∣ (∏ r ∈ D, r ^ e r) + 1) : Reach D₀ (insert p D)

theorem Reach.prime {D₀ D : Finset ℕ} (h₀ : ∀ r ∈ D₀, r.Prime) (h : Reach D₀ D) :
    ∀ r ∈ D, r.Prime := by
  induction h with
  | refl => exact h₀
  | step hD e he p hp hd ih =>
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hp
    · exact ih r hr

theorem Reach.subset {D₀ D : Finset ℕ} (h : Reach D₀ D) : D₀ ⊆ D := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step hD e he p hp hd ih => exact ih.trans (Finset.subset_insert _ _)

theorem Reach.trans {D₀ D₁ D₂ : Finset ℕ} (h₁ : Reach D₀ D₁) (h₂ : Reach D₁ D₂) :
    Reach D₀ D₂ := by
  induction h₂ with
  | refl => exact h₁
  | step hD e he p hp hd ih => exact Reach.step ih e he p hp hd

/-! ## The algebraic core -/

/-- A subset `T` of `ℤ/q` that contains `1`, omits `0`, and is closed under multiplication
    cannot be mapped into itself by `h ↦ a·h + 1` with `a ≠ 0`. -/
theorem no_affine_stable {q : ℕ} [Fact q.Prime] (T : Set (ZMod q)) (h1 : (1 : ZMod q) ∈ T)
    (h0 : (0 : ZMod q) ∉ T) (hmul : ∀ x ∈ T, ∀ y ∈ T, x * y ∈ T) (a : ZMod q) (ha : a ≠ 0)
    (hstep : ∀ h ∈ T, a * h + 1 ∈ T) : False := by
  have hqp : q.Prime := Fact.out
  have hTfin : T.Finite := Set.toFinite _
  have hTf : ∀ x, x ∈ hTfin.toFinset ↔ x ∈ T := fun x => hTfin.mem_toFinset
  have hperm : ∀ g : ZMod q → ZMod q, Function.Injective g → (∀ x ∈ T, g x ∈ T) →
      ∑ x ∈ hTfin.toFinset, g x = ∑ x ∈ hTfin.toFinset, x := by
    intro g hg hgT
    have himg : hTfin.toFinset.image g = hTfin.toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact (hTf _).mpr (hgT y ((hTf y).mp hy))
      · rw [Finset.card_image_of_injective _ hg]
    calc ∑ x ∈ hTfin.toFinset, g x = ∑ x ∈ hTfin.toFinset.image g, x :=
          (Finset.sum_image (f := fun x => x) (fun _ _ _ _ h => hg h)).symm
      _ = ∑ x ∈ hTfin.toFinset, x := by rw [himg]
  have hsum : a * ∑ x ∈ hTfin.toFinset, x + (hTfin.toFinset.card : ZMod q) =
      ∑ x ∈ hTfin.toFinset, x := by
    have := hperm (fun h => a * h + 1)
      (fun x y h => mul_left_cancel₀ ha (add_right_cancel (h : a * x + 1 = a * y + 1))) hstep
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
      at this
    exact this
  have hcard_pos : 0 < hTfin.toFinset.card := Finset.card_pos.mpr ⟨1, (hTf 1).mpr h1⟩
  have hcard_lt : hTfin.toFinset.card < q := by
    have hsub : hTfin.toFinset ⊆ (Finset.univ : Finset (ZMod q)).erase 0 := fun x hx =>
      Finset.mem_erase.mpr ⟨fun hx0 => h0 (hx0 ▸ (hTf x).mp hx), Finset.mem_univ _⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at hle
    have := hqp.two_le
    omega
  by_cases hex : ∃ c ∈ T, c ≠ 1
  · obtain ⟨c, hc, hc1⟩ := hex
    have hc0 : c ≠ 0 := fun h => h0 (h ▸ hc)
    have h2 := hperm (fun x => c * x)
      (fun x y h => mul_left_cancel₀ hc0 (h : c * x = c * y)) (fun x hx => hmul c hc x hx)
    rw [← Finset.mul_sum] at h2
    have hσ : ∑ x ∈ hTfin.toFinset, x = 0 := by
      have : (c - 1) * ∑ x ∈ hTfin.toFinset, x = 0 := by rw [sub_mul, one_mul, h2, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1)
    rw [hσ, mul_zero, zero_add] at hsum
    have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hsum
    exact absurd (Nat.le_of_dvd hcard_pos hdvd) (by omega)
  · have hall : ∀ c ∈ T, c = 1 := fun c hc => by
      by_contra h
      exact hex ⟨c, hc, h⟩
    have h := hall _ (hstep 1 h1)
    exact ha (by linear_combination h)

/-- If `T ⊆ ℤ/q` contains `1` and is closed under multiplication, then it contains the
    residue of every positive integer all of whose prime factors have residue in `T`. -/
theorem natCast_mem_of_primeFactors {q : ℕ} (T : Set (ZMod q)) (h1 : (1 : ZMod q) ∈ T)
    (hmul : ∀ x ∈ T, ∀ y ∈ T, x * y ∈ T) :
    ∀ n : ℕ, 1 ≤ n → (∀ p : ℕ, p.Prime → p ∣ n → ((p : ℕ) : ZMod q) ∈ T) →
      ((n : ℕ) : ZMod q) ∈ T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hpr
    rcases Nat.eq_or_lt_of_le hn with hn1 | hn1
    · rw [← hn1, Nat.cast_one]
      exact h1
    · have hmp := Nat.minFac_prime (by omega : n ≠ 1)
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      have hkpos : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · rw [hk0, mul_zero] at hk; omega
        · exact hk0
      have hklt : k < n := by
        calc k < 2 * k := by omega
          _ ≤ n.minFac * k := Nat.mul_le_mul_right k hmp.two_le
          _ = n := hk.symm
      have hkT := ih k hklt hkpos
        (fun p hp hpk => hpr p hp (by rw [hk]; exact Dvd.dvd.mul_left hpk _))
      have hprod := hmul _ (hpr _ hmp (Nat.minFac_dvd n)) _ hkT
      rw [← Nat.cast_mul, ← hk] at hprod
      exact hprod

/-! ## Attainable residues and their stabiliser -/

/-- The residues mod `q` of the admissible products at the node `D`. -/
def G (q : ℕ) (D : Finset ℕ) : Set (ZMod q) :=
  {x | ∃ e : ℕ → ℕ, (∀ r ∈ D, e r = 1 ∨ e r = 2) ∧ x = ((∏ r ∈ D, r ^ e r : ℕ) : ZMod q)}

/-- The nonzero residues that map `G q D` into itself by multiplication. -/
def Stab (q : ℕ) (D : Finset ℕ) : Set (ZMod q) :=
  {h | h ≠ 0 ∧ ∀ x ∈ G q D, h * x ∈ G q D}

/-- Adjoining a new prime `p` multiplies the attainable residues by `p` or by `p²`. -/
theorem mul_pow_mem_G_insert {q : ℕ} {D : Finset ℕ} {p : ℕ} (hpD : p ∉ D) {x : ZMod q}
    (hx : x ∈ G q D) {j : ℕ} (hj : j = 1 ∨ j = 2) :
    ((p : ℕ) : ZMod q) ^ j * x ∈ G q (insert p D) := by
  obtain ⟨e, he, rfl⟩ := hx
  refine ⟨Function.update e p j, ?_, ?_⟩
  · intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hrD
    · rw [Function.update_self]; exact hj
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hrD hpD)]; exact he r hrD
  · rw [Finset.prod_insert hpD, Function.update_self, Nat.cast_mul, Nat.cast_pow]
    congr 2
    exact Finset.prod_congr rfl (fun r hr => by
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hr hpD)])

/-! ## The theorem -/

/-- **Every prime is reached.** From any finite set of primes `D₀`, the Euclid tree with
    exponents `1` or `2` reaches a node containing any given prime `q`. -/
theorem exists_reach_mem {D₀ : Finset ℕ} (h₀ : ∀ r ∈ D₀, r.Prime) {q : ℕ} (hq : q.Prime) :
    ∃ D, Reach D₀ D ∧ q ∈ D := by
  classical
  by_contra hno
  have hno' : ∀ D, Reach D₀ D → q ∉ D := fun D hD hqD => hno ⟨D, hD, hqD⟩
  have : Fact q.Prime := ⟨hq⟩
  have hne : ∀ D, Reach D₀ D → ∀ r ∈ D, ((r : ℕ) : ZMod q) ≠ 0 := by
    intro D hD r hr
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    exact hno' D hD (((Nat.prime_dvd_prime_iff_eq hq (hD.prime h₀ r hr)).mp hd) ▸ hr)
  -- a node with the largest number of attainable residues
  have hbound : ∀ D, (G q D).ncard ≤ q := fun D => by
    calc (G q D).ncard ≤ (Set.univ : Set (ZMod q)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = q := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card]
  obtain ⟨D, hD, hmax⟩ : ∃ D, Reach D₀ D ∧
      ∀ D', Reach D₀ D' → (G q D').ncard ≤ (G q D).ncard := by
    have hP := Nat.findGreatest_spec (P := fun k => ∃ D, Reach D₀ D ∧ (G q D).ncard = k)
      (hbound D₀) ⟨D₀, Reach.refl, rfl⟩
    obtain ⟨D, hD, hk⟩ := hP
    refine ⟨D, hD, fun D' hD' => ?_⟩
    rw [hk]
    exact Nat.le_findGreatest (P := fun k => ∃ D, Reach D₀ D ∧ (G q D).ncard = k)
      (hbound D') ⟨D', hD', rfl⟩
  -- the class of every prime factor of every admissible `N + 1` stabilises `G q D`
  have hchild : ∀ e : ℕ → ℕ, (∀ r ∈ D, e r = 1 ∨ e r = 2) → ∀ p : ℕ, p.Prime →
      p ∣ (∏ r ∈ D, r ^ e r) + 1 → ((p : ℕ) : ZMod q) ∈ Stab q D := by
    intro e he p hp hd
    have hnode : Reach D₀ (insert p D) := Reach.step hD e he p hp hd
    have hc0 : ((p : ℕ) : ZMod q) ≠ 0 := hne _ hnode p (Finset.mem_insert_self _ _)
    have hpD : p ∉ D := by
      intro hpD
      have he0 : e p ≠ 0 := by rcases he p hpD with h | h <;> omega
      have hdvd : p ∣ ∏ r ∈ D, r ^ e r :=
        (dvd_pow_self p he0).trans (Finset.dvd_prod_of_mem (fun r => r ^ e r) hpD)
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hdvd).mp hd))
    refine ⟨hc0, fun x hx => ?_⟩
    by_contra hnot
    have himg : (fun y => ((p : ℕ) : ZMod q) * y) '' G q D ⊆ G q (insert p D) := by
      rintro _ ⟨y, hy, rfl⟩
      have := mul_pow_mem_G_insert hpD hy (j := 1) (Or.inl rfl)
      rwa [pow_one] at this
    have hsq : ((p : ℕ) : ZMod q) ^ 2 * x ∈ G q (insert p D) :=
      mul_pow_mem_G_insert hpD hx (Or.inr rfl)
    have hnew : ((p : ℕ) : ZMod q) ^ 2 * x ∉ (fun y => ((p : ℕ) : ZMod q) * y) '' G q D := by
      rintro ⟨y, hy, hyx⟩
      have hyeq : y = ((p : ℕ) : ZMod q) * x := by
        apply mul_left_cancel₀ hc0
        have hyx' : ((p : ℕ) : ZMod q) * y = ((p : ℕ) : ZMod q) ^ 2 * x := hyx
        rw [hyx', pow_two, mul_assoc]
      exact hnot (hyeq ▸ hy)
    have hcard : (G q D).ncard + 1 ≤ (G q (insert p D)).ncard := by
      calc (G q D).ncard + 1
          = ((fun y => ((p : ℕ) : ZMod q) * y) '' G q D).ncard + 1 := by
            rw [Set.ncard_image_of_injective _ (mul_right_injective₀ hc0)]
        _ = (insert (((p : ℕ) : ZMod q) ^ 2 * x)
              ((fun y => ((p : ℕ) : ZMod q) * y) '' G q D)).ncard :=
            (Set.ncard_insert_of_notMem hnew).symm
        _ ≤ (G q (insert p D)).ncard :=
            Set.ncard_le_ncard (Set.insert_subset hsq himg)
    have := hmax _ hnode
    omega
  have hT1 : (1 : ZMod q) ∈ Stab q D := ⟨one_ne_zero, fun x hx => by rwa [one_mul]⟩
  have hT0 : (0 : ZMod q) ∉ Stab q D := fun h => h.1 rfl
  have hTmul : ∀ x ∈ Stab q D, ∀ y ∈ Stab q D, x * y ∈ Stab q D := by
    intro x hx y hy
    refine ⟨mul_ne_zero hx.1 hy.1, fun z hz => ?_⟩
    rw [mul_assoc]
    exact hx.2 _ (hy.2 z hz)
  -- hence `x + 1` stabilises `G q D` for every attainable `x`
  have hplus : ∀ x ∈ G q D, x + 1 ∈ Stab q D := by
    rintro _ ⟨e, he, rfl⟩
    have hpos : 1 ≤ (∏ r ∈ D, r ^ e r) + 1 := Nat.succ_pos _
    have := natCast_mem_of_primeFactors (Stab q D) hT1 hTmul _ hpos
      (fun p hp hd => hchild e he p hp hd)
    rwa [Nat.cast_add, Nat.cast_one] at this
  -- an attainable residue
  have haG : (((∏ r ∈ D, r ^ (1 : ℕ) : ℕ) : ℕ) : ZMod q) ∈ G q D :=
    ⟨fun _ => 1, fun _ _ => Or.inl rfl, rfl⟩
  have ha0 : (((∏ r ∈ D, r ^ (1 : ℕ) : ℕ) : ℕ) : ZMod q) ≠ 0 := by
    rw [Nat.cast_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun r hr => by
      rw [Nat.cast_pow]; exact pow_ne_zero _ (hne D hD r hr))
  exact no_affine_stable (Stab q D) hT1 hT0 hTmul _ ha0
    (fun h hh => by rw [mul_comm]; exact hplus _ (hh.2 _ haG))

/-- Every finite set of primes is contained in a single node. -/
theorem exists_reach_superset {D₀ : Finset ℕ} (h₀ : ∀ r ∈ D₀, r.Prime) (Q : Finset ℕ)
    (hQ : ∀ r ∈ Q, r.Prime) : ∃ D, Reach D₀ D ∧ Q ⊆ D := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨D₀, Reach.refl, Finset.empty_subset _⟩
  | insert a Q _ ih =>
    obtain ⟨D₁, hD₁, hQD₁⟩ := ih (fun r hr => hQ r (Finset.mem_insert_of_mem hr))
    obtain ⟨D₂, hD₂, haD₂⟩ := exists_reach_mem (hD₁.prime h₀)
      (hQ a (Finset.mem_insert_self _ _))
    refine ⟨D₂, hD₁.trans hD₂, ?_⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hrQ
    · exact haD₂
    · exact hD₂.subset (hQD₁ hrQ)

/-- From nothing: every prime lies in some node of the Euclid tree with exponents `1`
    or `2`. -/
theorem exists_node_mem {q : ℕ} (hq : q.Prime) : ∃ D, Reach ∅ D ∧ q ∈ D :=
  exists_reach_mem (by simp) hq

end SquareTree
