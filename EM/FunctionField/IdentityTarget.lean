import EM.FunctionField.CompositeEntry

/-!
# The target is the identity: over `𝔽_2` every recurrence is a capture

A prime `Q` divides a Euclid number `N + 1` when `N ≡ -1` in the residue group `G_Q`.
Finite groups give one thing for free, *recurrence*: every walk in `G_Q` repeats a value, and
every element has finite order. Recurrence produces the value `1`, never a prescribed other
value. So what finiteness proves, uniformly in `p`, is the **Mersenne form** `Q ∣ W - 1`:

* `dvd_pow_sub_one` — `Q ∣ N^(p^deg Q - 1) - 1` (recurrence in the exponent).
* `exists_window_sub_one` — if `Q` never divides the running product, then in every stretch
  of `p^deg Q` stages there is a window of consecutive terms `a_{i+1}, …, a_{i+k}` with
  `Q ∣ a_{i+1} ⋯ a_{i+k} - 1` (recurrence in time).

The Euclid rule asks for the **Euclid form** `Q ∣ W + 1`. The two forms differ by the
element `-1` of the constants `𝔽_p^×`, which has order `2` for odd `p` and can be avoided by
a subgroup. Over `𝔽_2` the group of constants is trivial, `-1 = 1`, and the two forms are the
same statement:

* `dvd_pow_add_one` — `Q ∣ N^(2^deg Q - 1) + 1` for every `N` prime to `Q`.
* `dvd_prod_pow_add_one` — hence every prime outside a finite set `D` of primes divides
  `(∏ D)^(2^deg Q - 1) + 1`: the Euclid tree with a uniform exponent reaches every prime in
  one step.
* `exists_window_add_one` — **every prime missed by the sequence divides the Euclid
  polynomial of a window of consecutive terms**, infinitely often and with gaps at most
  `2^deg Q`.

## Reading

Mullin's conjecture over `𝔽_2` for `Q` is the anchored case of the last statement (`i = 0`,
the window starts at the seed) together with minimality. The unanchored statement is a
weakening of the conjecture that is true over `𝔽_2`, and whose proof uses exactly `-1 = 1`:
over `𝔽_p`, `p` odd, and over `ℤ`, the same argument gives windows `≡ 1`, the wrong sign.
(`docs/analysis/mersenne_duality_2026-10-27.md` treats this sign over `ℤ`; in
characteristic 2 the Euclid and Mersenne problems coincide.)

No capture by the sequence itself is proved here.
-/

namespace FunctionFieldAnalog

namespace IdentityTarget

open Polynomial FrobeniusOrbit CompositeFloors

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- Values at a root of `Q` lie in `𝔽_{p^deg Q}`. -/
theorem aeval_pow_eq_self {Q : (ZMod p)[X]} (hQ : Irreducible Q) {β : Lp p}
    (hβ : aeval β Q = 0) (N : (ZMod p)[X]) :
    aeval β N ^ p ^ Q.natDegree = aeval β N := by
  have h : (⇑(φ p))^[Q.natDegree] (aeval β N) = aeval β N := by
    rw [← aeval_iterate, (isPeriodicPt_natDegree p hQ hβ).eq]
  rwa [φ_iterate] at h

/-! ## Recurrence in the exponent -/

/-- **Mersenne form, any `p`.** `Q ∣ N^(p^deg Q - 1) - 1` for `N` prime to `Q`. -/
theorem dvd_pow_sub_one {Q N : (ZMod p)[X]} (hQ : Irreducible Q) (hN : ¬ Q ∣ N) :
    Q ∣ N ^ (p ^ Q.natDegree - 1) - 1 := by
  obtain ⟨β, hβ⟩ := exists_aeval_eq_zero p hQ
  have hx : aeval β N ≠ 0 := fun h => hN (FibreRule.dvd_of_aeval_eq_zero p hQ hβ h)
  have hfix := aeval_pow_eq_self hQ hβ N
  apply FibreRule.dvd_of_aeval_eq_zero p hQ hβ
  rw [map_sub, map_pow, map_one, sub_eq_zero]
  have hpos : 0 < p ^ Q.natDegree := pow_pos (Fact.out : p.Prime).pos _
  have : aeval β N ^ (p ^ Q.natDegree - 1) * aeval β N = 1 * aeval β N := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, hfix, one_mul]
  exact mul_right_cancel₀ hx this

/-- **Euclid form over `𝔽_2`.** `Q ∣ N^(2^deg Q - 1) + 1` for `N` prime to `Q`. -/
theorem dvd_pow_add_one {Q N : (ZMod 2)[X]} (hQ : Irreducible Q) (hN : ¬ Q ∣ N) :
    Q ∣ N ^ (2 ^ Q.natDegree - 1) + 1 := by
  have h := dvd_pow_sub_one hQ hN
  have e : N ^ (2 ^ Q.natDegree - 1) + 1 = N ^ (2 ^ Q.natDegree - 1) - 1 := by
    linear_combination two_eq_zero_poly
  rwa [e]

/-- A monic irreducible outside a finite set of monic irreducibles does not divide their
    product. -/
theorem not_dvd_prod {D : Finset (ZMod p)[X]} (hD : ∀ r ∈ D, r.Monic ∧ Irreducible r)
    {Q : (ZMod p)[X]} (hQm : Q.Monic) (hQ : Irreducible Q) (hQD : Q ∉ D) :
    ¬ Q ∣ ∏ r ∈ D, r := by
  intro h
  obtain ⟨r, hr, hdvd⟩ := (Prime.dvd_finsetProd_iff hQ.prime _).mp h
  have := eq_of_monic_of_associated hQm (hD r hr).1 (hQ.associated_of_dvd (hD r hr).2 hdvd)
  exact hQD (this ▸ hr)

/-- **The uniform-exponent Euclid tree over `𝔽_2` reaches every prime in one step.** -/
theorem dvd_prod_pow_add_one {D : Finset (ZMod 2)[X]} (hD : ∀ r ∈ D, r.Monic ∧ Irreducible r)
    {Q : (ZMod 2)[X]} (hQm : Q.Monic) (hQ : Irreducible Q) (hQD : Q ∉ D) :
    Q ∣ (∏ r ∈ D, r) ^ (2 ^ Q.natDegree - 1) + 1 :=
  dvd_pow_add_one hQ (not_dvd_prod hD hQm hQ hQD)

/-! ## Recurrence in time -/

/-- The product of the `k` consecutive terms `a_{i+1}, …, a_{i+k}`. -/
noncomputable def window (d : FFEMData p) (i k : ℕ) : (ZMod p)[X] :=
  ∏ m ∈ Finset.range k, d.ffSeq (i + m + 1)

theorem ffProd_add (d : FFEMData p) (i k : ℕ) :
    d.ffProd (i + k) = d.ffProd i * window d i k := by
  induction k with
  | zero => simp [window]
  | succ k ih =>
    rw [← add_assoc, d.ffProd_succ, ih, window, window, Finset.prod_range_succ, mul_assoc]

/-- A prime that never appears never divides the running product. -/
theorem not_dvd_ffProd_of_missed (d : FFEMData p) {Q : (ZMod p)[X]} (hQm : Q.Monic)
    (hQ : Irreducible Q) (hmiss : ∀ n, d.ffSeq n ≠ Q) (n : ℕ) : ¬ Q ∣ d.ffProd n := by
  induction n with
  | zero =>
    intro h
    rw [d.ffProd_zero] at h
    have := eq_of_monic_of_associated hQm monic_X (hQ.associated_of_dvd irreducible_X h)
    exact hmiss 0 (by rw [d.ffSeq_zero, this])
  | succ n ih =>
    intro h
    rw [d.ffProd_succ] at h
    rcases hQ.prime.dvd_or_dvd h with h | h
    · exact ih h
    · obtain ⟨hm, hi, -⟩ := d.ffSeq_succ n
      exact hmiss (n + 1) (eq_of_monic_of_associated hQm hm (hQ.associated_of_dvd hi h)).symm

/-- **Recurrence, Mersenne form (any `p`).** If `Q` never divides the running product, every
    stretch of `p^deg Q` stages contains a window of consecutive terms whose product is
    `≡ 1 (mod Q)`. -/
theorem exists_window_sub_one (d : FFEMData p) {Q : (ZMod p)[X]} (hQ : Irreducible Q)
    (hmiss : ∀ n, ¬ Q ∣ d.ffProd n) (N : ℕ) :
    ∃ i k, N ≤ i ∧ 0 < k ∧ i + k ≤ N + p ^ Q.natDegree ∧ Q ∣ window d i k - 1 := by
  classical
  obtain ⟨β, hβ⟩ := exists_aeval_eq_zero p hQ
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hdeg : Q.natDegree ≠ 0 := hQ.natDegree_pos.ne'
  set q := p ^ Q.natDegree with hq
  have hne : (X ^ q - X : (Lp p)[X]) ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ hdeg hp1
  set S := (X ^ q - X : (Lp p)[X]).roots.toFinset with hS
  have hScard : S.card ≤ q :=
    calc S.card ≤ Multiset.card (X ^ q - X : (Lp p)[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ q - X : (Lp p)[X]).natDegree := card_roots' _
      _ = q := FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ hdeg hp1
  let f : ℕ → Lp p := fun m => aeval β (d.ffProd (N + m))
  have hmaps : ∀ m ∈ Finset.range (q + 1), f m ∈ S := by
    intro m _
    rw [hS, Multiset.mem_toFinset, mem_roots hne, IsRoot.def, eval_sub, eval_pow, eval_X,
      sub_eq_zero]
    exact aeval_pow_eq_self hQ hβ _
  have key : ∀ a b, a < b → b ≤ q → f a = f b →
      ∃ i k, N ≤ i ∧ 0 < k ∧ i + k ≤ N + q ∧ Q ∣ window d i k - 1 := by
    intro a b hab hb hfab
    refine ⟨N + a, b - a, by omega, by omega, by omega, ?_⟩
    apply FibreRule.dvd_of_aeval_eq_zero p hQ hβ
    have hx : aeval β (d.ffProd (N + a)) ≠ 0 := fun h =>
      hmiss (N + a) (FibreRule.dvd_of_aeval_eq_zero p hQ hβ h)
    have hprod : d.ffProd (N + b) = d.ffProd (N + a) * window d (N + a) (b - a) := by
      rw [← ffProd_add]; congr 1; omega
    have h1 : aeval β (d.ffProd (N + a)) =
        aeval β (d.ffProd (N + a)) * aeval β (window d (N + a) (b - a)) := by
      have : aeval β (d.ffProd (N + a)) = aeval β (d.ffProd (N + b)) := hfab
      rw [← map_mul, ← hprod]; exact this
    rw [map_sub, map_one, sub_eq_zero]
    have h2 : aeval β (d.ffProd (N + a)) * aeval β (window d (N + a) (b - a)) =
        aeval β (d.ffProd (N + a)) * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel₀ hx h2
  obtain ⟨a, ha, b, hb, hab, hfab⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by rw [Finset.card_range]; omega : S.card < (Finset.range (q + 1)).card) hmaps
  rw [Finset.mem_range] at ha hb
  rcases lt_or_gt_of_ne hab with h | h
  · exact key a b h (by omega) hfab
  · exact key b a h (by omega) hfab.symm

/-- **Every missed prime divides a window Euclid polynomial (`𝔽_2`).** If the monic
    irreducible `Q` never appears in the sequence, then for every `N` there are consecutive
    terms `a_{i+1}, …, a_{i+k}` with `N ≤ i`, `i + k ≤ N + 2^deg Q` and
    `Q ∣ a_{i+1} ⋯ a_{i+k} + 1`. -/
theorem exists_window_add_one (d : FFEMData 2) {Q : (ZMod 2)[X]} (hQm : Q.Monic)
    (hQ : Irreducible Q) (hmiss : ∀ n, d.ffSeq n ≠ Q) (N : ℕ) :
    ∃ i k, N ≤ i ∧ 0 < k ∧ i + k ≤ N + 2 ^ Q.natDegree ∧ Q ∣ window d i k + 1 := by
  obtain ⟨i, k, hi, hk, hik, h⟩ :=
    exists_window_sub_one d hQ (not_dvd_ffProd_of_missed d hQm hQ hmiss) N
  refine ⟨i, k, hi, hk, hik, ?_⟩
  have e : window d i k + 1 = window d i k - 1 := by linear_combination two_eq_zero_poly
  rwa [e]

end IdentityTarget

end FunctionFieldAnalog
