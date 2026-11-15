import EM.FunctionField.TwistedThreshold

/-!
# The map `x ↦ P_n(x)` along the sequence: where the tower holds and where it breaks

`FibreRule.lean` reads the next term as the shortest Frobenius orbit in the fibre of the map
`P_n` over `−1`. The Galois object behind all fibres at once is the monodromy group of
`P_n(x) − y`. This file answers, as far as elementary means go, the question "is that group
the full symmetric group at every stage?". It is not, and the failure has an exact shape.

## Main results

* `exists_comp_iff_irreducible` — **the tower breaks exactly at composite stages**:
  `P_{n+1}` is a polynomial in `P_n` iff `P_n + 1` is irreducible (and then
  `P_{n+1} = g ∘ P_n`, `g = X² + X`). So after a prime stage the monodromy of `P_{n+1}` is
  imprimitive (blocks = fibres of `P_n`), and after a composite stage `P_{n+1}` does not
  factor through `P_n`.
* `two_dvd_natDegree_of_inert` — the imprimitivity seen at every base point: at a prime
  stage, if `y² + y = c` has no solution in `𝔽_p`, every irreducible factor of
  `P_{n+1} − c` has even degree. (For `c = −1` this is the `Φ₃` criterion.)
* `pow_eq_self_of_sylv_iterate_eq`, `aeval_ffProd_pow_eq_of_run` — over `𝔽_2`, **a run of
  prime stages has 2-group monodromy**: if stages `n, …, n+k−1` are prime and `k < 2^u`,
  then over every base point `c ∈ 𝔽_{2^e}` the whole fibre of `P_n ↦ P_{n+k}` lies in
  `𝔽_{2^{e·2^u}}`. For `c = 1`, `e = 1` this is the field in which the autonomous threshold
  theorem lives.

## Reading

The degree prohibitions of `AutonomousThreshold.lean` and the trace conditions of
`TwistedThreshold.lean` are the visible part of one fact: over `𝔽_2` the step `g` is
additive, the cover `P_n ↦ P_{n+k}` is a torsor under `ker (F+1)^k`, and Frobenius acts on
that kernel unipotently. A 2-group has few cycle types; that is why degrees are forbidden.
A composite stage ends the run and the next product is no longer a function of the
previous one (`exists_comp_iff_irreducible`): the tower, and with it every statement of
this kind, restarts from `k = 0`.

Whether `P_{n+1}` can be decomposable in another way after a composite stage, and what its
monodromy group is, is not decided here.
-/

namespace FunctionFieldAnalog

namespace RunMonodromy

open Polynomial FrobeniusOrbit CompositeFloors

/-! ## Any characteristic -/

section General

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- **The tower breaks exactly at composite stages.** `P_{n+1}` is a polynomial in `P_n`
    iff the Euclid polynomial `P_n + 1` is irreducible. -/
theorem exists_comp_iff_irreducible (d : FFEMData p) (n : ℕ) :
    (∃ h : (ZMod p)[X], d.ffProd (n + 1) = h.comp (d.ffProd n)) ↔
      Irreducible (d.ffProd n + 1) := by
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨hπm, hπi, hπd⟩ := d.ffSeq_succ n
    have hm := ffProd_natDegree_pos d n
    have hEdeg : (d.ffProd n + 1).natDegree = (d.ffProd n).natDegree :=
      natDegree_add_eq_left_of_natDegree_lt (by rwa [natDegree_one])
    have hπle : (d.ffSeq (n + 1)).natDegree ≤ (d.ffProd n).natDegree := by
      rw [← hEdeg]
      exact natDegree_le_of_dvd hπd (euclid_monic d n).ne_zero
    have hπpos : 0 < (d.ffSeq (n + 1)).natDegree := hπi.natDegree_pos
    have hdeg : h.natDegree * (d.ffProd n).natDegree =
        (d.ffProd n).natDegree + (d.ffSeq (n + 1)).natDegree := by
      rw [← natDegree_comp, ← hh, d.ffProd_succ, (ffProd_monic p d n).natDegree_mul hπm]
    have h1 : 1 < h.natDegree := by
      by_contra hlt
      push Not at hlt
      have := Nat.mul_le_mul_right (d.ffProd n).natDegree hlt
      omega
    have h3 : h.natDegree < 3 := by
      by_contra hge
      push Not at hge
      have := Nat.mul_le_mul_right (d.ffProd n).natDegree hge
      omega
    have h2 : h.natDegree = 2 := by omega
    rw [h2] at hdeg
    have heq : d.ffProd n + 1 = d.ffSeq (n + 1) :=
      eq_of_monic_of_dvd_of_natDegree_le hπm (euclid_monic d n) hπd (by omega)
    rw [heq]
    exact hπi
  · intro h
    refine ⟨X ^ 2 + X, ?_⟩
    rw [ffProd_succ_of_irreducible d n h]
    simp only [add_comp, pow_comp, X_comp]
    ring

/-- A Frobenius-fixed element of `𝔽̄_p` is a constant. -/
theorem exists_algebraMap_eq_of_pow_eq {r : Lp p} (h : r ^ p = r) :
    ∃ a : ZMod p, algebraMap (ZMod p) (Lp p) a = r := by
  have h0 : aeval r (∏ a : ZMod p, (X - C a)) = 0 := by
    rw [FibreRule.prod_X_sub_C, map_sub, map_pow, aeval_X, h, sub_self]
  rw [map_prod] at h0
  obtain ⟨a, -, ha⟩ := Finset.prod_eq_zero_iff.mp h0
  refine ⟨a, ?_⟩
  rw [map_sub, aeval_X, aeval_C] at ha
  exact (sub_eq_zero.mp ha).symm

/-- **Imprimitivity at every base point.** At a prime stage, if `y² + y = c` has no solution
    in `𝔽_p`, every irreducible factor of `P_{n+1} − c` has even degree. -/
theorem two_dvd_natDegree_of_inert (d : FFEMData p) (n : ℕ)
    (hirr : Irreducible (d.ffProd n + 1)) {c : ZMod p} (hc : ∀ a : ZMod p, a ^ 2 + a ≠ c)
    {f : (ZMod p)[X]} (hf : Irreducible f) (hdvd : f ∣ d.ffProd (n + 1) - C c) :
    2 ∣ f.natDegree := by
  obtain ⟨β, hβ⟩ := exists_aeval_eq_zero p hf
  set r : Lp p := aeval β (d.ffProd n) with hr
  have hroot : aeval β (d.ffProd (n + 1) - C c) = 0 := by
    obtain ⟨g, hg⟩ := hdvd
    rw [hg, map_mul, hβ, zero_mul]
  have hq : r ^ 2 + r = algebraMap (ZMod p) (Lp p) c := by
    rw [ffProd_succ_of_irreducible d n hirr, map_sub, map_mul, map_add, map_one, aeval_C,
      ← hr] at hroot
    linear_combination hroot
  have hperd : Function.IsPeriodicPt (⇑(φ p)) f.natDegree r := by
    show (⇑(φ p))^[f.natDegree] r = r
    rw [hr, ← aeval_iterate, (isPeriodicPt_natDegree p hf hβ).eq]
  have hper2 : Function.IsPeriodicPt (⇑(φ p)) 2 r := by
    show (⇑(φ p))^[2] r = r
    have hs : (φ p r) ^ 2 + φ p r = algebraMap (ZMod p) (Lp p) c := by
      have := congrArg (φ p) hq
      have hc' : φ p (algebraMap (ZMod p) (Lp p) c) = algebraMap (ZMod p) (Lp p) c :=
        RingHom.congr_fun (φ_comp_algebraMap p) c
      rw [map_add, map_pow, hc'] at this
      exact this
    have hprod : (φ p r - r) * (φ p r + r + 1) = 0 := by linear_combination hs - hq
    rw [Function.iterate_succ_apply, Function.iterate_one]
    rcases mul_eq_zero.mp hprod with h | h
    · rw [sub_eq_zero.mp h, sub_eq_zero.mp h]
    · have h1 : φ p r = -r - 1 := by linear_combination h
      rw [h1, map_sub, map_neg, map_one, h1]
      ring
  by_contra hodd
  have hcop : Nat.gcd 2 f.natDegree = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
  have hper1 := hper2.gcd hperd
  rw [hcop] at hper1
  have hfix : r ^ p = r := by
    have : (⇑(φ p))^[1] r = r := hper1
    rwa [Function.iterate_one, φ_apply] at this
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_pow_eq p hfix
  refine hc a ((algebraMap (ZMod p) (Lp p)).injective ?_)
  rw [map_add, map_pow, ha, hq]

end General

/-! ## Characteristic two: a run of prime stages has 2-group monodromy -/

section CharTwo

open FunctionFieldAnalog.CharTwo AutonomousThreshold

/-- The operator `F^e + 1` on `𝔽̄_2`. -/
noncomputable def frobAdd (e : ℕ) (x : Lp 2) : Lp 2 := x ^ 2 ^ e + x

theorem frobAdd_zero (e : ℕ) : frobAdd e 0 = 0 := by
  rw [frobAdd, zero_pow (by positivity), add_zero]

theorem sylv_add (a b : Lp 2) : sylv (a + b) = sylv a + sylv b := by
  simp only [sylv]
  linear_combination (a * b) * two_eq_zero_L

theorem sylv_iterate_add (j : ℕ) (a b : Lp 2) :
    sylv^[j] (a + b) = sylv^[j] a + sylv^[j] b := by
  induction j generalizing a b with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      sylv_add, ih]

theorem sylv_iterate_zero (j : ℕ) : sylv^[j] (0 : Lp 2) = 0 :=
  Function.iterate_fixed (by simp [sylv]) j

theorem sylv_iterate_pow (j i : ℕ) (z : Lp 2) :
    sylv^[j] (z ^ 2 ^ i) = (sylv^[j] z) ^ 2 ^ i := by
  have := φ_iterate_sylv_iterate i j z
  rw [φ_iterate, φ_iterate] at this
  exact this.symm

/-- `F^e + 1` commutes with `F + 1`. -/
theorem commute_frobAdd_sylv (e : ℕ) : Function.Commute (frobAdd e) sylv := by
  intro z
  show frobAdd e (sylv z) = sylv (frobAdd e z)
  simp only [frobAdd, sylv, add_pow_char_pow]
  linear_combination (-(z ^ 2 ^ e * z)) * two_eq_zero_L

/-- `F^{e+1} + 1 = (F^e + 1) + F^e (F + 1)`. -/
theorem frobAdd_succ (e : ℕ) (y : Lp 2) :
    frobAdd (e + 1) y = frobAdd e y + (sylv y) ^ 2 ^ e := by
  simp only [frobAdd, sylv, add_pow_char_pow]
  linear_combination (-(y ^ 2 ^ e)) * two_eq_zero_L

/-- `F + 1` divides `F^e + 1`: one factor `F^e + 1` uses up one factor `F + 1`. -/
theorem sylv_iterate_frobAdd_eq_zero (e : ℕ) {j : ℕ} {y : Lp 2} (h : sylv^[j + 1] y = 0) :
    sylv^[j] (frobAdd e y) = 0 := by
  induction e with
  | zero =>
    have h0 : frobAdd 0 y = 0 := by
      simp only [frobAdd, pow_zero, pow_one]
      exact CharTwo.add_self_eq_zero y
    rw [h0, sylv_iterate_zero]
  | succ e ih =>
    rw [frobAdd_succ, sylv_iterate_add, ih, sylv_iterate_pow, ← Function.iterate_succ_apply, h,
      zero_pow (by positivity), add_zero]

/-- `ker (F+1)^j ⊆ ker (F^e+1)^j`. -/
theorem frobAdd_iterate_eq_zero (e : ℕ) :
    ∀ (j : ℕ) (y : Lp 2), sylv^[j] y = 0 → (frobAdd e)^[j] y = 0 := by
  intro j
  induction j with
  | zero => intro y h; exact h
  | succ j ih =>
    intro y h
    rw [Function.iterate_succ_apply]
    exact ih _ (sylv_iterate_frobAdd_eq_zero e h)

/-- `(F^e + 1)^{2^u} = F^{e·2^u} + 1` in characteristic two. -/
theorem frobAdd_iterate_two_pow (e u : ℕ) (z : Lp 2) :
    (frobAdd e)^[2 ^ u] z = z ^ 2 ^ (e * 2 ^ u) + z := by
  induction u generalizing z with
  | zero => simp [frobAdd]
  | succ u ih =>
    have hsplit : (frobAdd e)^[2 ^ (u + 1)] z = (frobAdd e)^[2 ^ u] ((frobAdd e)^[2 ^ u] z) := by
      rw [← Function.iterate_add_apply, ← two_mul, ← pow_succ']
    have hQ : (2 : ℕ) ^ (e * 2 ^ u) * 2 ^ (e * 2 ^ u) = 2 ^ (e * 2 ^ (u + 1)) := by
      rw [← pow_add]
      congr 1
      ring
    rw [hsplit, ih, ih, add_pow_char_pow, ← pow_mul, hQ]
    linear_combination CharTwo.add_self_eq_zero (z ^ 2 ^ (e * 2 ^ u))

/-- **The fibre of `(F + 1)^k` over a point of `𝔽_{2^e}`.** If `(F+1)^k r = c` with
    `c ∈ 𝔽_{2^e}` and `k < 2^u`, then `r ∈ 𝔽_{2^{e·2^u}}`. -/
theorem pow_eq_self_of_sylv_iterate_eq {k u e : ℕ} (hk : k < 2 ^ u) {r c : Lp 2}
    (hc : c ^ 2 ^ e = c) (h : sylv^[k] r = c) : r ^ 2 ^ (e * 2 ^ u) = r := by
  have h0 : sylv^[k] (frobAdd e r) = 0 := by
    have := ((commute_frobAdd_sylv e).iterate_right k).eq r
    rw [← this, h, frobAdd, hc]
    exact CharTwo.add_self_eq_zero c
  have h1 : (frobAdd e)^[k + 1] r = 0 := by
    rw [Function.iterate_succ_apply]
    exact frobAdd_iterate_eq_zero e k _ h0
  have h2 : (frobAdd e)^[2 ^ u] r = 0 := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hk)
    rw [hj, Nat.add_comm (k + 1) j, Function.iterate_add_apply, h1]
    exact Function.iterate_fixed (frobAdd_zero e) j
  rw [frobAdd_iterate_two_pow] at h2
  linear_combination h2 - r * two_eq_zero_L

/-- **A run of prime stages has 2-group monodromy.** Let stages `n, …, n+k−1` be
    irreducible and `k < 2^u`. If `P_{n+k}(β) = c` with `c ∈ 𝔽_{2^e}`, then
    `P_n(β) ∈ 𝔽_{2^{e·2^u}}`: over every base point, the fibre of `P_n ↦ P_{n+k}` is defined
    over the extension of 2-power degree `2^u`. -/
theorem aeval_ffProd_pow_eq_of_run (d : FFEMData 2) (n k : ℕ)
    (h : ∀ j, j < k → Irreducible (d.ffProd (n + j) + 1)) {u e : ℕ} (hk : k < 2 ^ u)
    {β c : Lp 2} (hc : c ^ 2 ^ e = c) (hβ : aeval β (d.ffProd (n + k)) = c) :
    aeval β (d.ffProd n) ^ 2 ^ (e * 2 ^ u) = aeval β (d.ffProd n) := by
  rw [ffProd_add_of_run d n k h, aeval_sylvPoly_iterate] at hβ
  exact pow_eq_self_of_sylv_iterate_eq hk hc hβ

end CharTwo

end RunMonodromy

end FunctionFieldAnalog
