import EM.Population.LargeStepRoughness
import EM.ForMathlib.CoprimeAffineBlock

/-!
# The selection law: the type-measure counting layer (WP2)

This file supplies **WP2** of the seed-average program: the exact counting
identity that converts the box process of `EM/Population/LargeStepRoughness.lean`
into a *measure* on seeds.

Fix a prime `q`, a truncation `Y`, a horizon `n`, and a reference seed `m₀`
whose first `n` `q`-free multipliers are nondegenerate and `≤ Y`.  The
**modulus** is

```
modulus q Y = ∏ {r ≤ Y : r prime, r ≠ q}
```

— note that it **excludes `q`**, so the `q`-free type is a function of
`m mod (M_Y / q)` and the `q`-coordinate remains CRT-free.  This is load-bearing
for Lemma C downstream (`EM/Population/SeedCapture.lean`).

The four deliverables:

* **A2** (`genSeqAvoid_prefix_eq_of_modEq`) — the `q`-free analogue of Lemma B:
  the first `n` multipliers of the `q`-free dynamics are a function of the seed
  modulo `M`, provided they are nondegenerate and `≤ Y`.
* **A1** (`card_filter_crt`) — generic CRT product counting: for a finset `P` of
  primes with product `M`, the number of `m < M` whose residue lies in a
  prescribed local set `S r` at every `r ∈ P` is `∏ (S r).card`.
* **A3** (`mem_cell_iff_local`) — the **type cell** `stepCell q Y n m₀` (seeds in
  one period reproducing `m₀`'s prefix and `m₀`'s small-prime divisibility) is
  cut out by local residue conditions, one per prime `r ≤ Y`, `r ≠ q`, in the
  three-case partition of WP0 (a):
  `r ∣ m₀` ↦ `{0}`; `r` a multiplier ↦ one class `{-c_i⁻¹}`; otherwise ↦ the
  box `box q m₀ r n`.
* **A4** (`selection_law`) — the exact identity
  `#(cell ∩ {survives up to y}) = survival q m₀ y n · #cell`,
  with `survival` the roughness survival product of
  `EM/Population/LargeStepRoughness.lean`.

References: WP0 (a)/(c), `agents/state/findings.md`, Session 310.
-/

noncomputable section
open Classical

namespace SelectionLaw

open SeedCapture SeedTypes LargeStepRoughness

/-! ## Part A1.  Generic CRT product counting

WP0 (a), `findings.md`, Session 310.  The local sets are a *dependent* family
`S : (r : ℕ) → Finset (ZMod r)`; the counting statement is over one full period
`range (∏ r ∈ P, r)`. -/

/-- Counting a single residue condition on one full block: the reduction map
`Finset.range a → ZMod a` is a bijection.

WP0 (a), `findings.md`, Session 310. -/
theorem card_range_filter_cast {a : ℕ} (ha : 0 < a) (S : Finset (ZMod a)) :
    ((Finset.range a).filter (fun u => ((u : ℕ) : ZMod a) ∈ S)).card = S.card := by
  have : NeZero a := ⟨ha.ne'⟩
  refine Finset.card_bij (fun u _ => ((u : ℕ) : ZMod a)) ?_ ?_ ?_
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro u hu v hv h
    rw [Finset.mem_filter, Finset.mem_range] at hu hv
    have h2 := congrArg ZMod.val h
    rwa [ZMod.val_cast_of_lt hu.1, ZMod.val_cast_of_lt hv.1] at h2
  · intro x hx
    refine ⟨x.val, ?_, ZMod.natCast_rightInverse x⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩
    rw [ZMod.natCast_rightInverse x]
    exact hx

/-- A predicate periodic with period `d > 0` is determined by the residue. -/
private theorem periodic_mod {p : ℕ → Prop} {d : ℕ} (_hd : 0 < d)
    (hp : ∀ x, p (x + d) = p x) (m : ℕ) : p (m % d) = p m := by
  conv_rhs => rw [← Nat.mod_add_div m d]
  generalize m / d = t
  induction t with
  | zero => simp
  | succ t ih =>
    have hrw : m % d + d * (t + 1) = (m % d + d * t) + d := by ring
    rw [hrw, hp]
    exact ih

/-- Splitting a full period `a·B` (with `a`, `B` coprime) into the two coordinate
counts, for predicates periodic of period `a` resp. `B`.

WP0 (a), `findings.md`, Session 310. -/
private theorem card_split {a B : ℕ} (ha : 0 < a) (hB : 0 < B) (hcop : Nat.Coprime a B)
    (p s : ℕ → Prop) [DecidablePred p] [DecidablePred s]
    (hp : ∀ x, p (x + a) = p x) (hs : ∀ x, s (x + B) = s x) :
    ((Finset.range (a * B)).filter (fun m => p m ∧ s m)).card
      = ((Finset.range a).filter p).card * ((Finset.range B).filter s).card := by
  have habpos : 0 < a * B := Nat.mul_pos ha hB
  have hpm : ∀ m, p (m % a) = p m := fun m => periodic_mod ha hp m
  have hsm : ∀ m, s (m % B) = s m := fun m => periodic_mod hB hs m
  rw [← Finset.card_product]
  refine Finset.card_bij (fun m _ => (m % a, m % B)) ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter] at hm
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ ha), by
        rw [hpm]; exact hm.2.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hB), by
        rw [hsm]; exact hm.2.2⟩
  · intro m1 h1 m2 h2 heq
    rw [Finset.mem_filter, Finset.mem_range] at h1 h2
    have hpa : m1 ≡ m2 [MOD a] := congrArg Prod.fst heq
    have hpb : m1 ≡ m2 [MOD B] := congrArg Prod.snd heq
    have hab : m1 ≡ m2 [MOD a * B] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hpa, hpb⟩
    have := hab
    rw [Nat.ModEq, Nat.mod_eq_of_lt h1.1, Nat.mod_eq_of_lt h2.1] at this
    exact this
  · rintro ⟨u, v⟩ hb
    rw [Finset.mem_product] at hb
    obtain ⟨hu, hv⟩ := hb
    rw [Finset.mem_filter, Finset.mem_range] at hu hv
    obtain ⟨x, hxu, hxv⟩ := Nat.chineseRemainder hcop u v
    refine ⟨x % (a * B), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ habpos), ?_⟩
      constructor
      · rw [← hpm]
        have hma : x % (a * B) ≡ u [MOD a] :=
          ((Nat.mod_modEq x (a * B)).of_dvd ⟨B, rfl⟩).trans hxu
        rw [Nat.ModEq] at hma
        rw [hma, Nat.mod_eq_of_lt hu.1]
        exact hu.2
      · rw [← hsm]
        have hmb : x % (a * B) ≡ v [MOD B] :=
          ((Nat.mod_modEq x (a * B)).of_dvd ⟨a, by ring⟩).trans hxv
        rw [Nat.ModEq] at hmb
        rw [hmb, Nat.mod_eq_of_lt hv.1]
        exact hv.2
    · have hma : x % (a * B) ≡ u [MOD a] :=
        ((Nat.mod_modEq x (a * B)).of_dvd ⟨B, rfl⟩).trans hxu
      have hmb : x % (a * B) ≡ v [MOD B] :=
        ((Nat.mod_modEq x (a * B)).of_dvd ⟨a, by ring⟩).trans hxv
      rw [Nat.ModEq] at hma hmb
      rw [Prod.mk.injEq]
      exact ⟨by rw [hma, Nat.mod_eq_of_lt hu.1], by rw [hmb, Nat.mod_eq_of_lt hv.1]⟩

/-- **A1 — generic CRT product counting.**  For a finset `P` of primes and a
family of local sets `S r ⊆ ZMod r`, exactly `∏ (S r).card` of the residues in
one full period `∏ r ∈ P, r` satisfy all the local conditions.

WP0 (a), `findings.md`, Session 310. -/
theorem card_filter_crt (S : (r : ℕ) → Finset (ZMod r)) (P : Finset ℕ) :
    (∀ r ∈ P, r.Prime) →
    ((Finset.range (∏ r ∈ P, r)).filter
        (fun m => ∀ r ∈ P, ((m : ℕ) : ZMod r) ∈ S r)).card
      = ∏ r ∈ P, (S r).card := by
  classical
  induction P using Finset.induction_on with
  | empty => intro _; simp
  | @insert a T haT ih =>
    intro hP
    have hPa : a.Prime := hP a (Finset.mem_insert_self a T)
    have hPT : ∀ r ∈ T, r.Prime := fun r hr => hP r (Finset.mem_insert_of_mem hr)
    have hBpos : 0 < ∏ r ∈ T, r :=
      Finset.prod_pos fun r hr => (hPT r hr).pos
    have hcop : Nat.Coprime a (∏ r ∈ T, r) := by
      refine Nat.coprime_prod_right_iff.mpr ?_
      intro r hr
      refine (Nat.coprime_primes hPa (hPT r hr)).mpr ?_
      rintro rfl
      exact haT hr
    have hprod : ∏ r ∈ insert a T, r = a * ∏ r ∈ T, r := Finset.prod_insert haT
    have hcard : ∏ r ∈ insert a T, (S r).card
        = (S a).card * ∏ r ∈ T, (S r).card := Finset.prod_insert haT
    rw [hprod, hcard]
    have hpred : ((Finset.range (a * ∏ r ∈ T, r)).filter
          (fun m => ∀ r ∈ insert a T, ((m : ℕ) : ZMod r) ∈ S r))
        = (Finset.range (a * ∏ r ∈ T, r)).filter
          (fun m => (((m : ℕ) : ZMod a) ∈ S a) ∧ ∀ r ∈ T, ((m : ℕ) : ZMod r) ∈ S r) := by
      refine Finset.filter_congr ?_
      intro m _
      exact Finset.forall_mem_insert _ _ _
    have hpa : ∀ x : ℕ, (((x + a : ℕ) : ZMod a) ∈ S a) = (((x : ℕ) : ZMod a) ∈ S a) := by
      intro x
      apply propext
      have hc : ((x + a : ℕ) : ZMod a) = ((x : ℕ) : ZMod a) := by
        push_cast
        simp
      rw [hc]
    have hpb : ∀ x : ℕ, (∀ r ∈ T, ((x + ∏ r ∈ T, r : ℕ) : ZMod r) ∈ S r)
        = (∀ r ∈ T, ((x : ℕ) : ZMod r) ∈ S r) := by
      intro x
      apply propext
      refine forall_congr' fun r => imp_congr_right fun hr => ?_
      have hdvd : r ∣ ∏ r ∈ T, r := Finset.dvd_prod_of_mem _ hr
      have hc : ((x + ∏ r ∈ T, r : ℕ) : ZMod r) = ((x : ℕ) : ZMod r) := by
        rw [Nat.cast_add, (ZMod.natCast_eq_zero_iff _ _).mpr hdvd, add_zero]
      rw [hc]
    have hsplit := card_split hPa.pos hBpos hcop
      (fun m : ℕ => ((m : ℕ) : ZMod a) ∈ S a)
      (fun m : ℕ => ∀ r ∈ T, ((m : ℕ) : ZMod r) ∈ S r) hpa hpb
    rw [hpred, hsplit, card_range_filter_cast hPa.pos (S a), ih hPT]

/-! ## Part A2.  `q`-free prefix determinism (the `q`-free Lemma B)

WP0 (b), `findings.md`, Session 310. -/

/-- **One-step `q`-free CRT invariance.**  If `A ≡ B [MOD M]`, `M` is divisible
by every prime `≤ Y` other than `q`, and the `q`-free least factor of `A + 1` is
nondegenerate and `≤ Y`, then the `q`-free least factors of `A + 1` and `B + 1`
agree.

WP0 (b), `findings.md`, Session 310. -/
theorem qfree_minFac_eq_of_modEq {q M Y A B : ℕ} (hq : q.Prime)
    (hM : ∀ r : ℕ, r.Prime → r ≤ Y → r ≠ q → r ∣ M) (hmod : A ≡ B [MOD M])
    (h2 : 2 ≤ (qfreePart q (A + 1)).minFac)
    (hle : (qfreePart q (A + 1)).minFac ≤ Y) :
    (qfreePart q (B + 1)).minFac = (qfreePart q (A + 1)).minFac := by
  have hAne : A + 1 ≠ 0 := Nat.succ_ne_zero A
  have hBne : B + 1 ≠ 0 := Nat.succ_ne_zero B
  have hqfA : 2 ≤ qfreePart q (A + 1) := by
    have hpos := qfreePart_pos (N := A + 1) q hAne
    by_contra hcon
    have h1 : qfreePart q (A + 1) = 1 := by omega
    rw [h1, Nat.minFac_one] at h2
    omega
  obtain ⟨hpprime, hpA, hpq⟩ := minFac_qfreePart_spec hq hAne hqfA
  have hpM : (qfreePart q (A + 1)).minFac ∣ M := hM _ hpprime hle hpq
  have hmodp : A % (qfreePart q (A + 1)).minFac = B % (qfreePart q (A + 1)).minFac :=
    Nat.ModEq.of_dvd hpM hmod
  have hpB : (qfreePart q (A + 1)).minFac ∣ B + 1 :=
    (MullinCRT.dvd_succ_iff_of_mod_eq hmodp).mp hpA
  have hpBq : (qfreePart q (A + 1)).minFac ∣ qfreePart q (B + 1) :=
    (prime_dvd_qfreePart_iff hq hpprime hpq hBne).mpr hpB
  have hqfB : 2 ≤ qfreePart q (B + 1) :=
    le_trans hpprime.two_le (Nat.le_of_dvd (qfreePart_pos q hBne) hpBq)
  have hsp : (qfreePart q (B + 1)).minFac ≤ (qfreePart q (A + 1)).minFac :=
    Nat.minFac_le_of_dvd hpprime.two_le hpBq
  obtain ⟨hsprime, hsB, hsq⟩ := minFac_qfreePart_spec hq hBne hqfB
  have hsM : (qfreePart q (B + 1)).minFac ∣ M := hM _ hsprime (le_trans hsp hle) hsq
  have hmods : A % (qfreePart q (B + 1)).minFac = B % (qfreePart q (B + 1)).minFac :=
    Nat.ModEq.of_dvd hsM hmod
  have hsA : (qfreePart q (B + 1)).minFac ∣ A + 1 :=
    (MullinCRT.dvd_succ_iff_of_mod_eq hmods).mpr hsB
  have hge := minFac_qfreePart_least hq hAne hsprime hsq hsA
  omega

/-- **A2 — the `q`-free Lemma B.**  If `M` is divisible by every prime `≤ Y`
other than `q`, and the first `n` multipliers of the `q`-free orbit of `m` are
nondegenerate and `≤ Y`, then every seed `m' ≡ m [MOD M]` produces exactly the
same first `n` `q`-free multipliers.

The nondegeneracy hypothesis `2 ≤ genSeqAvoid` is essential: it rules out the
`q`-power tail case, in which `qfreePart = 1` and the dynamics stalls.

WP0 (b), `findings.md`, Session 310. -/
theorem genSeqAvoid_prefix_eq_of_modEq {q m m' M Y n : ℕ} (hq : q.Prime)
    (hM : ∀ r : ℕ, r.Prime → r ≤ Y → r ≠ q → r ∣ M) (hmod : m ≡ m' [MOD M])
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y) :
    ∀ j < n, genSeqAvoid q m' j = genSeqAvoid q m j := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    have ihres := ih (fun j hj => hnd j (Nat.lt_succ_of_lt hj))
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact ihres j h
    · have hc : seedCofactorAvoid q m' j = seedCofactorAvoid q m j :=
        Finset.prod_congr rfl (fun i hi =>
          ihres i (lt_of_lt_of_le (Finset.mem_range.mp hi) (by omega)))
      have hPm : genProdAvoid q m j = m * seedCofactorAvoid q m j :=
        genProdAvoid_eq_seed_mul_cofactor q m j
      have hPm' : genProdAvoid q m' j = m' * seedCofactorAvoid q m j := by
        rw [genProdAvoid_eq_seed_mul_cofactor, hc]
      have h2 : 2 ≤ (qfreePart q (m * seedCofactorAvoid q m j + 1)).minFac := by
        rw [← hPm, ← genSeqAvoid_def]
        exact (hnd j hj).1
      have hle : (qfreePart q (m * seedCofactorAvoid q m j + 1)).minFac ≤ Y := by
        rw [← hPm, ← genSeqAvoid_def]
        exact (hnd j hj).2
      rw [genSeqAvoid_def, genSeqAvoid_def, hPm, hPm']
      exact qfree_minFac_eq_of_modEq hq hM (Nat.ModEq.mul_right _ hmod) h2 hle

/-- **A2, corollary.**  The `q`-free cofactors up to `n` are also determined by
the seed modulo `M`.

WP0 (b), `findings.md`, Session 310. -/
theorem seedCofactorAvoid_eq_of_modEq {q m m' M Y n : ℕ} (hq : q.Prime)
    (hM : ∀ r : ℕ, r.Prime → r ≤ Y → r ≠ q → r ∣ M) (hmod : m ≡ m' [MOD M])
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y) :
    ∀ k ≤ n, seedCofactorAvoid q m' k = seedCofactorAvoid q m k := by
  intro k hk
  exact Finset.prod_congr rfl fun i hi =>
    genSeqAvoid_prefix_eq_of_modEq hq hM hmod hnd i
      (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)

/-! ## Part A3.  The type cell and its local characterization

WP0 (a), `findings.md`, Session 310. -/

/-- The truncation modulus: the product of all primes `r ≤ Y` **other than `q`**.
Excluding `q` is load-bearing: it leaves `m mod q` CRT-free. -/
def modulus (q Y : ℕ) : ℕ := ∏ r ∈ bandUpTo q Y, r

theorem mem_bandUpTo {q Y r : ℕ} : r ∈ bandUpTo q Y ↔ r ≤ Y ∧ r.Prime ∧ r ≠ q := by
  rw [bandUpTo, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

theorem dvd_modulus {q Y r : ℕ} (hr : r.Prime) (hrY : r ≤ Y) (hrq : r ≠ q) :
    r ∣ modulus q Y :=
  Finset.dvd_prod_of_mem _ (mem_bandUpTo.mpr ⟨hrY, hr, hrq⟩)

theorem modulus_pos (q Y : ℕ) : 0 < modulus q Y :=
  Finset.prod_pos fun _ hr => (mem_bandUpTo.mp hr).2.1.pos

/-- The modulus is a product of **distinct primes**, hence squarefree.  (Exported for the
profinite/CRT layer, which needs to know that `modulus q Y` factors with multiplicity one.) -/
theorem modulus_squarefree (q Y : ℕ) : Squarefree (modulus q Y) := by
  rw [modulus]
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun r hr s hs hrs => ?_)
    (fun r hr => (mem_bandUpTo.mp hr).2.1.squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (mem_bandUpTo.mp (Finset.mem_coe.mp hr)).2.1
    (mem_bandUpTo.mp (Finset.mem_coe.mp hs)).2.1).mpr hrs

/-- Every prime factor of `modulus q Y` differs from `q`, so the modulus is coprime to `q`.
This is the load-bearing "`q`-coordinate stays CRT-free" fact, in divisibility form. -/
theorem coprime_modulus_self {q : ℕ} (hq : q.Prime) (Y : ℕ) :
    Nat.Coprime (modulus q Y) q := by
  rw [modulus, Nat.coprime_comm]
  refine Nat.Coprime.prod_right fun r hr => ?_
  exact (Nat.coprime_primes hq (mem_bandUpTo.mp hr).2.1).mpr
    (Ne.symm (mem_bandUpTo.mp hr).2.2)

/-- Restatement of `dvd_modulus` in the naming convention of the profinite layer: every
prime `r ≤ Y` other than `q` divides the modulus. -/
theorem prime_dvd_modulus {q Y r : ℕ} (hr : r.Prime) (hrY : r ≤ Y) (hrq : r ≠ q) :
    r ∣ modulus q Y :=
  dvd_modulus hr hrY hrq

/-! ### Multipliers are neither in the bag nor divide their own cofactor -/

/-- A nondegenerate multiplier never divides the seed: it divides the Euclid
number, and would otherwise divide `1`.  (This is the fact `D ∩ P = ∅` of
WP0 (a).)

WP0 (a), `findings.md`, Session 310. -/
theorem multiplier_not_dvd_seed {q m₀ i : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (h2 : 2 ≤ genSeqAvoid q m₀ i) : ¬ genSeqAvoid q m₀ i ∣ m₀ := by
  intro hdvd
  have hP : genSeqAvoid q m₀ i ∣ genProdAvoid q m₀ i :=
    hdvd.trans ⟨seedCofactorAvoid q m₀ i, genProdAvoid_eq_seed_mul_cofactor q m₀ i⟩
  have hS := genSeqAvoid_dvd_succ hq hm₀ h2
  have hone : genSeqAvoid q m₀ i ∣ 1 := (Nat.dvd_add_right hP).mp hS
  have := Nat.dvd_one.mp hone
  omega

/-- A nondegenerate multiplier never divides its own cofactor: this is what makes
`c_i` invertible modulo `p_{i+1}`, so that the local factor at a multiplier is
*one* residue class rather than the empty set.  (WP0 (a), implicit fact 1.)

WP0 (a), `findings.md`, Session 310. -/
theorem multiplier_not_dvd_cofactor {q m₀ i : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (h2 : 2 ≤ genSeqAvoid q m₀ i) : ¬ genSeqAvoid q m₀ i ∣ seedCofactorAvoid q m₀ i := by
  intro hdvd
  have hP : genSeqAvoid q m₀ i ∣ genProdAvoid q m₀ i := by
    rw [genProdAvoid_eq_seed_mul_cofactor]
    exact Dvd.dvd.mul_left hdvd m₀
  have hS := genSeqAvoid_dvd_succ hq hm₀ h2
  have hone : genSeqAvoid q m₀ i ∣ 1 := (Nat.dvd_add_right hP).mp hS
  have := Nat.dvd_one.mp hone
  omega

/-! ### The local sets -/

/-- **The local set at a prime `r ≤ Y`, `r ≠ q`** — the WP0 (a) three-case
partition:

* `r ∣ m₀` (`r` in the divisor set `D`): the single class `{0}`;
* `r` a multiplier of the reference orbit before time `n`: the single class
  `{-c_i⁻¹}`;
* otherwise (`r` active): the box `box q m₀ r n`.

WP0 (a), `findings.md`, Session 310. -/
def localSet (q n m₀ r : ℕ) : Finset (ZMod r) :=
  if r ∣ m₀ then {0}
  else if h : ∃ i, i < n ∧ genSeqAvoid q m₀ i = r then
    {-((seedCofactorAvoid q m₀ h.choose : ℕ) : ZMod r)⁻¹}
  else box q m₀ r n

theorem localSet_of_dvd {q n m₀ r : ℕ} (h : r ∣ m₀) : localSet q n m₀ r = {0} :=
  if_pos h

theorem localSet_of_mult {q n m₀ r : ℕ} (h1 : ¬ r ∣ m₀)
    (h : ∃ i, i < n ∧ genSeqAvoid q m₀ i = r) :
    localSet q n m₀ r = {-((seedCofactorAvoid q m₀ h.choose : ℕ) : ZMod r)⁻¹} := by
  rw [localSet, if_neg h1, dif_pos h]

theorem localSet_of_active {q n m₀ r : ℕ} (h : ¬ inBag q m₀ r n) :
    localSet q n m₀ r = box q m₀ r n := by
  rw [inBag, not_or] at h
  rw [localSet, if_neg h.1, dif_neg h.2]

theorem localSet_card_of_dvd {q n m₀ r : ℕ} (h : r ∣ m₀) :
    (localSet q n m₀ r).card = 1 := by
  rw [localSet_of_dvd h, Finset.card_singleton]

theorem localSet_card_of_mult {q n m₀ r : ℕ} (h1 : ¬ r ∣ m₀)
    (h : ∃ i, i < n ∧ genSeqAvoid q m₀ i = r) : (localSet q n m₀ r).card = 1 := by
  rw [localSet_of_mult h1 h, Finset.card_singleton]

theorem localSet_card_of_active {q n m₀ r : ℕ} (h : ¬ inBag q m₀ r n) :
    (localSet q n m₀ r).card = boxCard q m₀ r n := by
  rw [localSet_of_active h, boxCard]

/-! ### The key exposedness lemma -/

/-- **The local conditions kill every exposed prime.**  If the residue of `m` at
every prime `r ≤ Y`, `r ≠ q` lies in the local set, then at every step `j < n`
that is `s`-exposed for the reference orbit (`s < p̃_{j+1}`), the prime `s` does
not divide the Euclid number `m·c_j + 1` of the *candidate* seed.

This is the engine of the ⟸ half of `mem_cell_iff_local`: all three cases of the
WP0 (a) partition reduce to Lemma A (revisit-freeness) for the reference orbit.

WP0 (a), `findings.md`, Session 310. -/
theorem local_not_dvd_of_exposed {q Y n m₀ m : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y)
    (hloc : ∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ localSet q n m₀ r)
    {s j : ℕ} (hs : s.Prime) (hsY : s ≤ Y) (hsq : s ≠ q) (hj : j < n)
    (hexp : s < genSeqAvoid q m₀ j) :
    ¬ s ∣ m * seedCofactorAvoid q m₀ j + 1 := by
  have : Fact s.Prime := ⟨hs⟩
  have hnd2 : ∀ i < n, 2 ≤ genSeqAvoid q m₀ i := fun i hi => (hnd i hi).1
  have hmem := hloc s (mem_bandUpTo.mpr ⟨hsY, hs, hsq⟩)
  by_cases hd : s ∣ m₀
  · -- `s ∈ D`: then `s ∣ m`, so `s ∤ m·c + 1`.
    rw [localSet_of_dvd hd, Finset.mem_singleton, ZMod.natCast_eq_zero_iff] at hmem
    intro hcon
    have h1 : s ∣ m * seedCofactorAvoid q m₀ j := Dvd.dvd.mul_right hmem _
    have : s ∣ 1 := (Nat.dvd_add_right h1).mp hcon
    have := Nat.dvd_one.mp this
    exact hs.one_lt.ne' this
  · by_cases hmu : ∃ i, i < n ∧ genSeqAvoid q m₀ i = s
    · -- `s` is a multiplier: then `m ≡ m₀ (mod s)`, and step `j` is `s`-exposed
      -- for the reference orbit.
      rw [localSet_of_mult hd hmu, Finset.mem_singleton] at hmem
      have hilt : hmu.choose < n := hmu.choose_spec.1
      have hieq : genSeqAvoid q m₀ hmu.choose = s := hmu.choose_spec.2
      have h2i : 2 ≤ genSeqAvoid q m₀ hmu.choose := hnd2 _ hilt
      have hci0 : ((seedCofactorAvoid q m₀ hmu.choose : ℕ) : ZMod s) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hcon
        exact multiplier_not_dvd_cofactor hq hm₀ h2i (by rw [hieq]; exact hcon)
      have hdvdi : s ∣ m₀ * seedCofactorAvoid q m₀ hmu.choose + 1 := by
        have := genSeqAvoid_dvd_succ hq hm₀ h2i
        rw [hieq, genProdAvoid_eq_seed_mul_cofactor] at this
        exact this
      have hm₀eq : ((m₀ : ℕ) : ZMod s) = -((seedCofactorAvoid q m₀ hmu.choose : ℕ) : ZMod s)⁻¹ :=
        (hit_iff_eq_neg_inv hs hci0).mp (hit_iff_dvd.mpr hdvdi)
      have hmm₀ : ((m : ℕ) : ZMod s) = ((m₀ : ℕ) : ZMod s) := by rw [hmem, hm₀eq]
      intro hcon
      have hhit : ((m : ℕ) : ZMod s) * ((seedCofactorAvoid q m₀ j : ℕ) : ZMod s) = -1 :=
        hit_iff_dvd.mpr hcon
      rw [hmm₀] at hhit
      have hdvd0 : s ∣ m₀ * seedCofactorAvoid q m₀ j + 1 := hit_iff_dvd.mp hhit
      rw [← genProdAvoid_eq_seed_mul_cofactor] at hdvd0
      exact not_dvd_succ_of_exposed_avoid hq hm₀ hs hsq hexp hdvd0
    · -- `s` is active: the death point `-c_j⁻¹` has already been removed.
      have hbag : ¬ inBag q m₀ s n := fun h => h.elim hd hmu
      rw [localSet_of_active hbag] at hmem
      have hcj0 : ((seedCofactorAvoid q m₀ j : ℕ) : ZMod s) ≠ 0 :=
        cofactor_ne_zero_of_not_inBag hs hbag hnd2 (le_of_lt hj)
      have hvis : ((seedCofactorAvoid q m₀ j : ℕ) : ZMod s) ∈ visitedAt q m₀ s n := by
        rw [visitedAt, Finset.mem_image]
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hexp⟩, rfl⟩
      intro hcon
      have hhit : ((m : ℕ) : ZMod s) * ((seedCofactorAvoid q m₀ j : ℕ) : ZMod s) = -1 :=
        hit_iff_dvd.mpr hcon
      have hmeq := (hit_iff_eq_neg_inv hs hcj0).mp hhit
      rw [box, Finset.mem_sdiff] at hmem
      exact hmem.2 (Finset.mem_image.mpr ⟨_, hvis, hmeq.symm⟩)

/-- **One step of the ⟸ half of A3.**  If the residues of `m` obey all the local
conditions and the prefix of `m` agrees with `m₀` below `j`, then the `j`-th
multipliers agree.

WP0 (a), `findings.md`, Session 310. -/
theorem step_of_local {q Y n m₀ m : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y)
    (hloc : ∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ localSet q n m₀ r)
    {j : ℕ} (hjn : j < n)
    (hprefj : ∀ i < j, genSeqAvoid q m i = genSeqAvoid q m₀ i) :
    genSeqAvoid q m j = genSeqAvoid q m₀ j := by
  have hnd2 : ∀ i < n, 2 ≤ genSeqAvoid q m₀ i := fun i hi => (hnd i hi).1
  have hcof : seedCofactorAvoid q m j = seedCofactorAvoid q m₀ j :=
    Finset.prod_congr rfl (fun i hi => hprefj i (Finset.mem_range.mp hi))
  have hPm : genProdAvoid q m j = m * seedCofactorAvoid q m₀ j := by
    rw [genProdAvoid_eq_seed_mul_cofactor, hcof]
  have h2p : 2 ≤ genSeqAvoid q m₀ j := (hnd j hjn).1
  have hpY : genSeqAvoid q m₀ j ≤ Y := (hnd j hjn).2
  have hpprime : Nat.Prime (genSeqAvoid q m₀ j) := genSeqAvoid_prime h2p
  have : Fact (Nat.Prime (genSeqAvoid q m₀ j)) := ⟨hpprime⟩
  have hpq : genSeqAvoid q m₀ j ≠ q := genSeqAvoid_ne_avoided hq hm₀ h2p
  have hpd : ¬ genSeqAvoid q m₀ j ∣ m₀ := multiplier_not_dvd_seed hq hm₀ h2p
  have hmu : ∃ i, i < n ∧ genSeqAvoid q m₀ i = genSeqAvoid q m₀ j := ⟨j, hjn, rfl⟩
  have hich : hmu.choose = j :=
    genSeqAvoid_injOn hq hm₀ hnd2 hmu.choose_spec.1 hjn hmu.choose_spec.2
  have hloc_p := hloc _ (mem_bandUpTo.mpr ⟨hpY, hpprime, hpq⟩)
  rw [localSet_of_mult hpd hmu, Finset.mem_singleton, hich] at hloc_p
  have hcj0 : ((seedCofactorAvoid q m₀ j : ℕ) : ZMod (genSeqAvoid q m₀ j)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact multiplier_not_dvd_cofactor hq hm₀ h2p
  have hhit : ((m : ℕ) : ZMod (genSeqAvoid q m₀ j)) *
      ((seedCofactorAvoid q m₀ j : ℕ) : ZMod (genSeqAvoid q m₀ j)) = -1 :=
    (hit_iff_eq_neg_inv hpprime hcj0).mpr hloc_p
  have hpdvd : genSeqAvoid q m₀ j ∣ m * seedCofactorAvoid q m₀ j + 1 :=
    hit_iff_dvd.mp hhit
  have hne : m * seedCofactorAvoid q m₀ j + 1 ≠ 0 := Nat.succ_ne_zero _
  have hpqf : genSeqAvoid q m₀ j ∣ qfreePart q (m * seedCofactorAvoid q m₀ j + 1) :=
    (prime_dvd_qfreePart_iff hq hpprime hpq hne).mpr hpdvd
  have h2qf : 2 ≤ qfreePart q (m * seedCofactorAvoid q m₀ j + 1) :=
    le_trans hpprime.two_le (Nat.le_of_dvd (qfreePart_pos q hne) hpqf)
  have htle : (qfreePart q (m * seedCofactorAvoid q m₀ j + 1)).minFac ≤ genSeqAvoid q m₀ j :=
    Nat.minFac_le_of_dvd hpprime.two_le hpqf
  obtain ⟨htprime, htdvd, htq⟩ := minFac_qfreePart_spec hq hne h2qf
  rw [genSeqAvoid_def, hPm]
  by_contra hcon
  have htlt : (qfreePart q (m * seedCofactorAvoid q m₀ j + 1)).minFac < genSeqAvoid q m₀ j :=
    lt_of_le_of_ne htle hcon
  exact local_not_dvd_of_exposed hq hm₀ hnd hloc htprime
    (le_trans htlt.le hpY) htq hjn htlt htdvd

/-- **A3 — the type cell is cut out by local residue conditions.**

For a seed `m ≥ 1`, the conjunction of
* "`m` reproduces the first `n` `q`-free multipliers of `m₀`", and
* "`m` and `m₀` have the same small prime divisors (`r ≤ Y`, `r ≠ q`)"

is equivalent to the conjunction over the primes `r ≤ Y`, `r ≠ q` of the local
conditions `m mod r ∈ localSet q n m₀ r`.

The ⟸ direction is where the hypothesis "all multipliers `≤ Y`" earns its keep:
every prime below a multiplier is then itself `≤ Y`, hence controlled by the
local data.

WP0 (a), `findings.md`, Session 310. -/
theorem mem_cell_iff_local {q Y n m₀ : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y)
    {m : ℕ} (hm : 1 ≤ m) :
    ((∀ j < n, genSeqAvoid q m j = genSeqAvoid q m₀ j) ∧
        (∀ r : ℕ, r.Prime → r ≤ Y → r ≠ q → (r ∣ m ↔ r ∣ m₀)))
      ↔ (∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ localSet q n m₀ r) := by
  have hnd2 : ∀ i < n, 2 ≤ genSeqAvoid q m₀ i := fun i hi => (hnd i hi).1
  constructor
  · rintro ⟨hpref, hdvd⟩ r hrmem
    obtain ⟨hrY, hr, hrq⟩ := mem_bandUpTo.mp hrmem
    have : Fact r.Prime := ⟨hr⟩
    have hcof : ∀ k ≤ n, seedCofactorAvoid q m k = seedCofactorAvoid q m₀ k := by
      intro k hk
      exact Finset.prod_congr rfl fun i hi =>
        hpref i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)
    by_cases hd : r ∣ m₀
    · rw [localSet_of_dvd hd, Finset.mem_singleton, ZMod.natCast_eq_zero_iff]
      exact (hdvd r hr hrY hrq).mpr hd
    · by_cases hmu : ∃ i, i < n ∧ genSeqAvoid q m₀ i = r
      · rw [localSet_of_mult hd hmu, Finset.mem_singleton]
        have hilt : hmu.choose < n := hmu.choose_spec.1
        have hieq : genSeqAvoid q m₀ hmu.choose = r := hmu.choose_spec.2
        have h2i : 2 ≤ genSeqAvoid q m hmu.choose := by
          rw [hpref _ hilt, hieq]; exact hr.two_le
        have hdvdsucc := genSeqAvoid_dvd_succ hq hm h2i
        rw [hpref _ hilt, hieq, genProdAvoid_eq_seed_mul_cofactor,
          hcof _ (le_of_lt hilt)] at hdvdsucc
        have hci0 : ((seedCofactorAvoid q m₀ hmu.choose : ℕ) : ZMod r) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hcon
          exact multiplier_not_dvd_cofactor hq hm₀ (hnd2 _ hilt) (by rw [hieq]; exact hcon)
        exact (hit_iff_eq_neg_inv hr hci0).mp (hit_iff_dvd.mpr hdvdsucc)
      · have hbag : ¬ inBag q m₀ r n := fun h => h.elim hd hmu
        rw [localSet_of_active hbag, box, Finset.mem_sdiff]
        refine ⟨(mem_unitFinset hr).mpr ?_, ?_⟩
        · rw [Ne, ZMod.natCast_eq_zero_iff]
          exact fun h => hd ((hdvd r hr hrY hrq).mp h)
        · intro hmem
          obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hmem
          obtain ⟨j, hj, hexp, hcv⟩ := mem_visitedAt hv
          have hv0 : v ≠ 0 := visitedAt_ne_zero hr hbag hnd2 hv
          have hhit : ((m : ℕ) : ZMod r) * v = -1 :=
            (hit_iff_eq_neg_inv hr hv0).mpr hveq.symm
          rw [← hcv] at hhit
          have hdvd0 : r ∣ m * seedCofactorAvoid q m₀ j + 1 := hit_iff_dvd.mp hhit
          have hdvd1 : r ∣ genProdAvoid q m j + 1 := by
            rw [genProdAvoid_eq_seed_mul_cofactor, hcof j (le_of_lt hj)]
            exact hdvd0
          exact not_dvd_succ_of_exposed_avoid hq hm hr hrq
            (by rw [hpref j hj]; exact hexp) hdvd1
  · intro hloc
    have hdvdiff : ∀ r : ℕ, r.Prime → r ≤ Y → r ≠ q → (r ∣ m ↔ r ∣ m₀) := by
      intro r hr hrY hrq
      have : Fact r.Prime := ⟨hr⟩
      have hmem := hloc r (mem_bandUpTo.mpr ⟨hrY, hr, hrq⟩)
      by_cases hd : r ∣ m₀
      · rw [localSet_of_dvd hd, Finset.mem_singleton, ZMod.natCast_eq_zero_iff] at hmem
        exact iff_of_true hmem hd
      · have hne : ((m : ℕ) : ZMod r) ≠ 0 := by
          by_cases hmu : ∃ i, i < n ∧ genSeqAvoid q m₀ i = r
          · rw [localSet_of_mult hd hmu, Finset.mem_singleton] at hmem
            have hilt : hmu.choose < n := hmu.choose_spec.1
            have hieq : genSeqAvoid q m₀ hmu.choose = r := hmu.choose_spec.2
            have hci0 : ((seedCofactorAvoid q m₀ hmu.choose : ℕ) : ZMod r) ≠ 0 := by
              rw [Ne, ZMod.natCast_eq_zero_iff]
              intro hcon
              exact multiplier_not_dvd_cofactor hq hm₀ (hnd2 _ hilt) (by rw [hieq]; exact hcon)
            rw [hmem]
            simpa using hci0
          · have hbag : ¬ inBag q m₀ r n := fun h => h.elim hd hmu
            rw [localSet_of_active hbag, box, Finset.mem_sdiff] at hmem
            exact (mem_unitFinset hr).mp hmem.1
        refine iff_of_false ?_ hd
        intro hcon
        exact hne ((ZMod.natCast_eq_zero_iff m r).mpr hcon)
    refine ⟨?_, hdvdiff⟩
    have key2 : ∀ k, ∀ j < k, j < n → genSeqAvoid q m j = genSeqAvoid q m₀ j := by
      intro k
      induction k with
      | zero => intro j hj _; omega
      | succ k ih =>
        intro j hj hjn
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact ih j h hjn
        · exact step_of_local hq hm₀ hnd hloc hjn
            (fun i hi => ih i (by omega) (by omega))
    exact fun j hj => key2 (j + 1) j (Nat.lt_succ_self j) hj

/-- **The type cell.**  One full period `[1, M]` of seeds reproducing `m₀`'s
first `n` `q`-free multipliers and `m₀`'s small-prime divisibility pattern.

WP0 (a), `findings.md`, Session 310. -/
def stepCell (q Y n m₀ : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (modulus q Y + 1)).filter (fun m =>
    (∀ j < n, genSeqAvoid q m j = genSeqAvoid q m₀ j) ∧
      (∀ r : ℕ, r.Prime → r ≤ Y → r ≠ q → (r ∣ m ↔ r ∣ m₀)))

theorem mem_stepCell {q Y n m₀ m : ℕ} :
    m ∈ stepCell q Y n m₀ ↔
      (1 ≤ m ∧ m < modulus q Y + 1) ∧
        ((∀ j < n, genSeqAvoid q m j = genSeqAvoid q m₀ j) ∧
          (∀ r : ℕ, r.Prime → r ≤ Y → r ≠ q → (r ∣ m ↔ r ∣ m₀))) := by
  rw [stepCell, Finset.mem_filter, Finset.mem_Ico]

/-- **Sanity: the cell is nonempty.**  The reference seed itself belongs to its
own cell, provided it lies in the chosen period.

WP0 (a), `findings.md`, Session 310. -/
theorem self_mem_stepCell {q Y n m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hlt : m₀ ≤ modulus q Y) :
    m₀ ∈ stepCell q Y n m₀ :=
  mem_stepCell.mpr ⟨⟨hm₀, by omega⟩, fun _ _ => rfl, fun _ _ _ _ => Iff.rfl⟩

theorem stepCell_nonempty {q Y n m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hlt : m₀ ≤ modulus q Y) :
    (stepCell q Y n m₀).Nonempty :=
  ⟨m₀, self_mem_stepCell hm₀ hlt⟩

/-- **Sanity: cells at the same depth with different prefix data are disjoint.**

WP0 (a), `findings.md`, Session 310. -/
theorem stepCell_disjoint {q Y n m₀ m₁ : ℕ} {j : ℕ} (hj : j < n)
    (hne : genSeqAvoid q m₀ j ≠ genSeqAvoid q m₁ j) :
    Disjoint (stepCell q Y n m₀) (stepCell q Y n m₁) := by
  rw [Finset.disjoint_left]
  intro m h0 h1
  have e0 := (mem_stepCell.mp h0).2.1 j hj
  have e1 := (mem_stepCell.mp h1).2.1 j hj
  exact hne (e0.symm.trans e1)

/-! ### Counting the cell -/

/-- The local-residue predicate is periodic with period `modulus q Y`. -/
private theorem localPred_periodic (q Y : ℕ) (S : (r : ℕ) → Finset (ZMod r)) :
    Function.Periodic
      (fun m : ℕ => ∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ S r) (modulus q Y) := by
  intro x
  apply propext
  refine forall_congr' fun r => imp_congr_right fun hr => ?_
  obtain ⟨hrY, hrp, hrq⟩ := mem_bandUpTo.mp hr
  have hcast : ((x + modulus q Y : ℕ) : ZMod r) = ((x : ℕ) : ZMod r) := by
    push_cast
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr (dvd_modulus hrp hrY hrq)]
    ring
  rw [hcast]

/-- **The block count of a local-residue condition.**  Combines A1 with
periodicity to count on the period `[1, M]`.

WP0 (a), `findings.md`, Session 310. -/
theorem card_local_filter (q Y : ℕ) (S : (r : ℕ) → Finset (ZMod r)) :
    ((Finset.Ico 1 (modulus q Y + 1)).filter
        (fun m => ∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ S r)).card
      = ∏ r ∈ bandUpTo q Y, (S r).card := by
  have h1 : modulus q Y + 1 = 1 + modulus q Y := by omega
  rw [h1, Nat.filter_Ico_card_eq_of_periodic 1 (modulus q Y) _ (localPred_periodic q Y S),
    Nat.count_eq_card_filter_range]
  exact card_filter_crt S (bandUpTo q Y) (fun r hr => (mem_bandUpTo.mp hr).2.1)

/-- **A3, counting form.**  The cell has exactly `∏ |localSet r|` elements.

WP0 (a), `findings.md`, Session 310. -/
theorem stepCell_card {q Y n m₀ : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y) :
    (stepCell q Y n m₀).card = ∏ r ∈ bandUpTo q Y, (localSet q n m₀ r).card := by
  have hcell : stepCell q Y n m₀ = (Finset.Ico 1 (modulus q Y + 1)).filter
      (fun m => ∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ localSet q n m₀ r) := by
    rw [stepCell]
    refine Finset.filter_congr ?_
    intro m hm
    exact mem_cell_iff_local hq hm₀ hnd (Finset.mem_Ico.mp hm).1
  rw [hcell, card_local_filter q Y (fun r => localSet q n m₀ r)]

/-! ## Part A4.  The selection law

WP0 (c), `findings.md`, Session 310. -/

/-- **The one-step survival event.**  Deliberately phrased *without* reference to
the value of `genSeqAvoid`: "no prime `≤ y` other than `q` divides the current
Euclid number".  This avoids the `q`-power subtlety — if `genProdAvoid + 1` is a
power of `q` then `SurvivesUpTo` holds and `qfreePart` degenerates, which is
exactly the regime the survival product is designed to bound.

WP0 (c), `findings.md`, Session 310. -/
def SurvivesUpTo (q y n m : ℕ) : Prop :=
  ∀ r : ℕ, r.Prime → r ≤ y → r ≠ q → ¬ (r ∣ genProdAvoid q m n + 1)

/-- The local set of the *survival-filtered* cell: at the primes `r ≤ y` the
death point `-c_n⁻¹` is removed. -/
def localSurvSet (q y n m₀ r : ℕ) : Finset (ZMod r) :=
  if r ≤ y then
    (localSet q n m₀ r).filter
      (fun x => x * ((seedCofactorAvoid q m₀ n : ℕ) : ZMod r) + 1 ≠ 0)
  else localSet q n m₀ r

theorem localSurvSet_subset {q y n m₀ r : ℕ} :
    localSurvSet q y n m₀ r ⊆ localSet q n m₀ r := by
  rw [localSurvSet]
  split
  · exact Finset.filter_subset _ _
  · exact le_rfl

/-- **A4, local ratio.**  At every prime `r ≤ y` of the band, removing the death
point multiplies the local count by exactly `1 - ρ_r(n)`.

The three cases are the WP0 (c) accounting:
* `r ∈ D` or `r` a multiplier: `r` is in the bag, `ρ_r = 0`, and the death
  condition is automatic (`r ∣ m` resp. `r ∣ c_n`), so nothing is removed;
* `r` active and `c_n` old mod `r`: the death point was already removed,
  `ρ_r = 0`;
* `r` active and `c_n` new mod `r`: exactly one element leaves the box, and
  `|B| - 1 = (1 - 1/|B|)·|B|`.

WP0 (c), `findings.md`, Session 310. -/
theorem localSurvSet_card_eq {q Y y n m₀ r : ℕ}
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y)
    (hr : r.Prime) (hry : r ≤ y) :
    ((localSurvSet q y n m₀ r).card : ℝ)
      = (1 - rho q m₀ r n) * ((localSet q n m₀ r).card : ℝ) := by
  have : Fact r.Prime := ⟨hr⟩
  have hnd2 : ∀ i < n, 2 ≤ genSeqAvoid q m₀ i := fun i hi => (hnd i hi).1
  rw [localSurvSet, if_pos hry]
  by_cases hd : r ∣ m₀
  · have hbag : inBag q m₀ r n := Or.inl hd
    rw [localSet_of_dvd hd, Finset.filter_singleton, if_pos (by simp), rho_eq_zero_of_inBag hbag]
    simp
  · by_cases hmu : ∃ i, i < n ∧ genSeqAvoid q m₀ i = r
    · have hilt : hmu.choose < n := hmu.choose_spec.1
      have hieq : genSeqAvoid q m₀ hmu.choose = r := hmu.choose_spec.2
      have hbag : inBag q m₀ r n := Or.inr ⟨hmu.choose, hilt, hieq⟩
      have hcn0 : ((seedCofactorAvoid q m₀ n : ℕ) : ZMod r) = 0 := by
        rw [ZMod.natCast_eq_zero_iff, ← hieq, seedCofactorAvoid]
        exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hilt)
      rw [localSet_of_mult hd hmu, Finset.filter_singleton, if_pos (by simp [hcn0]),
        rho_eq_zero_of_inBag hbag]
      simp
    · have hbag : ¬ inBag q m₀ r n := fun h => h.elim hd hmu
      have hcn0 : ((seedCofactorAvoid q m₀ n : ℕ) : ZMod r) ≠ 0 :=
        cofactor_ne_zero_of_not_inBag hr hbag hnd2 (le_refl n)
      have hiff : ∀ x : ZMod r,
          (x * ((seedCofactorAvoid q m₀ n : ℕ) : ZMod r) + 1 ≠ 0) ↔
            x ≠ -((seedCofactorAvoid q m₀ n : ℕ) : ZMod r)⁻¹ := by
        intro x
        rw [not_iff_not, add_eq_zero_iff_eq_neg, hit_iff_eq_neg_inv hr hcn0]
      have hfil : (localSet q n m₀ r).filter
            (fun x => x * ((seedCofactorAvoid q m₀ n : ℕ) : ZMod r) + 1 ≠ 0)
          = (box q m₀ r n).erase (-((seedCofactorAvoid q m₀ n : ℕ) : ZMod r)⁻¹) := by
        rw [localSet_of_active hbag, ← Finset.filter_ne']
        exact Finset.filter_congr fun x _ => hiff x
      rw [hfil, localSet_card_of_active hbag]
      by_cases hnew : isNew q m₀ r n
      · have hmemb : -((seedCofactorAvoid q m₀ n : ℕ) : ZMod r)⁻¹ ∈ box q m₀ r n := by
          rw [box, Finset.mem_sdiff]
          refine ⟨(mem_unitFinset hr).mpr (by simpa using hcn0), ?_⟩
          intro hmem
          obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hmem
          have hvc : v = ((seedCofactorAvoid q m₀ n : ℕ) : ZMod r) := neg_inv_injective hr hveq
          rw [hvc] at hv
          exact hnew hv
        have hbpos : 0 < boxCard q m₀ r n := by
          rw [boxCard]
          exact Finset.card_pos.mpr ⟨_, hmemb⟩
        rw [Finset.card_erase_of_mem hmemb, rho_of_active ⟨hbag, hnew⟩, ← boxCard]
        have hbne : (boxCard q m₀ r n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [Nat.cast_sub (by omega : 1 ≤ boxCard q m₀ r n), Nat.cast_one]
        field_simp
      · have hnotmem : -((seedCofactorAvoid q m₀ n : ℕ) : ZMod r)⁻¹ ∉ box q m₀ r n := by
          rw [box, Finset.mem_sdiff]
          intro hcon
          refine hcon.2 (Finset.mem_image.mpr ⟨_, ?_, rfl⟩)
          exact not_not.mp hnew
        rw [Finset.erase_eq_of_notMem hnotmem, rho_eq_zero_of_old hnew, ← boxCard]
        ring

/-- Membership in the survival-filtered cell is again a local condition.

WP0 (c), `findings.md`, Session 310. -/
theorem mem_survCell_iff_local {q Y y n m₀ : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y) (hyY : y ≤ Y)
    {m : ℕ} (hm : 1 ≤ m) :
    (((∀ j < n, genSeqAvoid q m j = genSeqAvoid q m₀ j) ∧
        (∀ r : ℕ, r.Prime → r ≤ Y → r ≠ q → (r ∣ m ↔ r ∣ m₀))) ∧ SurvivesUpTo q y n m)
      ↔ (∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ localSurvSet q y n m₀ r) := by
  constructor
  · rintro ⟨hcell, hsurv⟩ r hrmem
    obtain ⟨hrY, hr, hrq⟩ := mem_bandUpTo.mp hrmem
    have hloc := (mem_cell_iff_local hq hm₀ hnd hm).mp hcell r hrmem
    rw [localSurvSet]
    split
    · rename_i hry
      refine Finset.mem_filter.mpr ⟨hloc, ?_⟩
      have hcof : seedCofactorAvoid q m n = seedCofactorAvoid q m₀ n :=
        Finset.prod_congr rfl fun i hi => hcell.1 i (Finset.mem_range.mp hi)
      have hnd0 : ¬ r ∣ m * seedCofactorAvoid q m₀ n + 1 := by
        have := hsurv r hr hry hrq
        rwa [genProdAvoid_eq_seed_mul_cofactor, hcof] at this
      intro hcon
      refine hnd0 ?_
      have : ((m * seedCofactorAvoid q m₀ n + 1 : ℕ) : ZMod r) = 0 := by
        push_cast
        exact hcon
      exact (ZMod.natCast_eq_zero_iff _ _).mp this
    · exact hloc
  · intro hloc
    have hloc' : ∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ localSet q n m₀ r :=
      fun r hr => localSurvSet_subset (hloc r hr)
    have hcell := (mem_cell_iff_local hq hm₀ hnd hm).mpr hloc'
    refine ⟨hcell, ?_⟩
    intro r hr hry hrq
    have hrmem : r ∈ bandUpTo q Y := mem_bandUpTo.mpr ⟨le_trans hry hyY, hr, hrq⟩
    have hmem := hloc r hrmem
    rw [localSurvSet, if_pos hry, Finset.mem_filter] at hmem
    have hcof : seedCofactorAvoid q m n = seedCofactorAvoid q m₀ n :=
      Finset.prod_congr rfl fun i hi => hcell.1 i (Finset.mem_range.mp hi)
    rw [genProdAvoid_eq_seed_mul_cofactor, hcof]
    intro hcon
    refine hmem.2 ?_
    have : ((m * seedCofactorAvoid q m₀ n + 1 : ℕ) : ZMod r) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hcon
    push_cast at this
    exact this

/-- Restriction of the band: for `y ≤ Y`, the primes of `bandUpTo q Y` that are
`≤ y` are exactly `bandUpTo q y`. -/
theorem bandUpTo_filter {q y Y : ℕ} (hyY : y ≤ Y) :
    (bandUpTo q Y).filter (fun r => r ≤ y) = bandUpTo q y := by
  ext r
  rw [Finset.mem_filter, mem_bandUpTo, mem_bandUpTo]
  constructor
  · rintro ⟨⟨_, hp, hq⟩, hry⟩; exact ⟨hry, hp, hq⟩
  · rintro ⟨hry, hp, hq⟩; exact ⟨⟨le_trans hry hyY, hp, hq⟩, hry⟩

/-- **A4 — the selection law.**  Inside one type cell, the fraction of seeds
whose next Euclid number has no prime factor `≤ y` other than `q` is *exactly*
the roughness survival product `survival q m₀ y n`.

This is the counting identity that turns the deterministic box process of
`EM/Population/LargeStepRoughness.lean` into a measure on seeds.

WP0 (a)/(c), `findings.md`, Session 310. -/
theorem selection_law {q Y y n m₀ : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y) (hyY : y ≤ Y) :
    (((stepCell q Y n m₀).filter (fun m => SurvivesUpTo q y n m)).card : ℝ)
      = survival q m₀ y n * ((stepCell q Y n m₀).card : ℝ) := by
  -- The filtered cell is again a local-residue set.
  have hfil : (stepCell q Y n m₀).filter (fun m => SurvivesUpTo q y n m)
      = (Finset.Ico 1 (modulus q Y + 1)).filter
        (fun m => ∀ r ∈ bandUpTo q Y, ((m : ℕ) : ZMod r) ∈ localSurvSet q y n m₀ r) := by
    rw [stepCell, Finset.filter_filter]
    refine Finset.filter_congr ?_
    intro m hm
    exact mem_survCell_iff_local hq hm₀ hnd hyY (Finset.mem_Ico.mp hm).1
  rw [hfil, card_local_filter q Y (fun r => localSurvSet q y n m₀ r),
    stepCell_card hq hm₀ hnd]
  push_cast
  -- Split each local count into the survival factor and the plain count.
  have hstep : ∀ r ∈ bandUpTo q Y,
      ((localSurvSet q y n m₀ r).card : ℝ)
        = (if r ≤ y then 1 - rho q m₀ r n else 1) * ((localSet q n m₀ r).card : ℝ) := by
    intro r hrmem
    obtain ⟨hrY, hr, hrq⟩ := mem_bandUpTo.mp hrmem
    by_cases hry : r ≤ y
    · rw [if_pos hry]
      exact localSurvSet_card_eq hnd hr hry
    · rw [if_neg hry, localSurvSet, if_neg hry, one_mul]
  rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_filter, bandUpTo_filter hyY, survival]

/-- **A4, inequality form.**  The version consumed by the downstream
tree-Chernoff argument.

WP0 (c), `findings.md`, Session 310. -/
theorem selection_law_ge {q Y y n m₀ : ℕ} (hq : q.Prime) (hm₀ : 1 ≤ m₀)
    (hnd : ∀ j < n, 2 ≤ genSeqAvoid q m₀ j ∧ genSeqAvoid q m₀ j ≤ Y) (hyY : y ≤ Y) :
    survival q m₀ y n * ((stepCell q Y n m₀).card : ℝ)
      ≤ (((stepCell q Y n m₀).filter (fun m => SurvivesUpTo q y n m)).card : ℝ) :=
  le_of_eq (selection_law hq hm₀ hnd hyY).symm

end SelectionLaw

end
