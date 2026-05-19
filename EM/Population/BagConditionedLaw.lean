import EM.Population.HeadDomination
import EM.ForMathlib.CoprimeAffineBlock

/-!
# The bag-conditioned multiplier law

Every Euclid number `P_n + 1` of the orbit lies in the arithmetic progression `1 (mod P_n)`, and
its least prime factor is a prime outside the bag (the primes dividing `P_n`).  The population
statement that matches this — as opposed to the fixed-modulus statements refuted in
`HeadDomination` — is: *among `m ≡ 1 (mod P)`, what is the law of `minFac m`?*

Answer (`tendsto_bagClass_div_ap`): for a prime `p ∤ P`, the density of
`{m ≡ 1 (mod P) : minFac m = p}` relative to the progression is

  `bagWeight P p = (1/p) · ∏_{r < p, r prime, r ∤ P} (1 − 1/r)`.

The proof is `HeadDomination`'s CRT counting with the primes of the bag removed from the sieve:
`m ≡ 1 (mod P)` already excludes every prime dividing `P`, so `minFac m = p` reduces to
`m ≡ 0 (mod p)` together with coprimality to the product `N'` of the primes below `p` outside
the bag; the two congruences combine to one class mod `p·P`, and along that progression the
coprimality to `N'` occurs `φ(N')` times per block of `N'` (`card_coprime_affine_block`).

Consequences:

* (`bagWeight_least_missing`, `tendsto_least_missing_div_ap`) if `q` is the **least prime
  outside the bag** (every prime `r < q` divides `P`), the product is empty and
  `bagWeight P q = 1/q` — exactly.  In the population containing the Euclid numbers, the least
  missing prime is selected with density exactly `1/q`, whatever the residue class of `q`,
  whatever the bag.  This is Shanks' heuristic with the correct, biased, bag-dependent law, and
  it is a theorem;
* the law is head-dominated by the least missing primes, exactly as in `HeadDomination`
  (`bagWeight P p = c_P(p) − c_P(p+1)` with `c_P(p) = ∏_{r<p, r∤P}(1−1/r)`, the telescoping of
  `HeadDomination.w_eq_cfun_sub` with the bag primes removed; not repeated here) — which is why
  fixed-modulus population equidistribution was never the object relevant to the orbit.  What
  the orbit inherits from this is, again, only heuristic: `P_n + 1` is one member of the
  progression, not a random one.
-/

noncomputable section
open Classical

open Finset

namespace BagConditionedLaw

/-! Part 1 (the affine block count `coprime_mod_iff`, `card_coprime_affine_block`,
`card_coprime_affine_blocks`) now lives in `EM/ForMathlib/CoprimeAffineBlock.lean`
(Mathlib-only; extracted 2026-08-18). -/

/-! ## Part 2: the sieve outside the bag -/

/-- The product of the primes below `p` that do not divide `P`. -/
def Nbag (P p : ℕ) : ℕ := ∏ r ∈ (range p).filter (fun r => Nat.Prime r ∧ ¬ r ∣ P), r

/-- `φ (Nbag P p)`, as a product of `r − 1`. -/
def Abag (P p : ℕ) : ℕ := ∏ r ∈ (range p).filter (fun r => Nat.Prime r ∧ ¬ r ∣ P), (r - 1)

/-- The bag-conditioned weight `(1/p) ∏_{r<p, r ∤ P}(1 − 1/r)`. -/
def bagWeight (P p : ℕ) : ℝ := (Abag P p : ℝ) / (Nbag P p : ℝ) / p

theorem Nbag_pos (P p : ℕ) : 0 < Nbag P p :=
  Finset.prod_pos fun _ hr => (Finset.mem_filter.mp hr).2.1.pos

theorem Abag_pos (P p : ℕ) : 0 < Abag P p :=
  Finset.prod_pos fun _ hr => by have := (Finset.mem_filter.mp hr).2.1.two_le; omega

theorem totient_Nbag (P p : ℕ) : Nat.totient (Nbag P p) = Abag P p :=
  HeadDomination.totient_prod_primes _ fun _ hr => (Finset.mem_filter.mp hr).2.1

theorem coprime_Nbag_iff (k P p : ℕ) :
    Nat.Coprime k (Nbag P p) ↔ ∀ r, Nat.Prime r → r < p → ¬ r ∣ P → ¬ r ∣ k := by
  unfold Nbag
  rw [Nat.coprime_prod_right_iff]
  constructor
  · intro h r hr hrp hrP hdvd
    have := h r (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrp, hr, hrP⟩)
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp this.symm hdvd
  · intro h r hr
    obtain ⟨hrp, hr', hrP⟩ := Finset.mem_filter.mp hr
    exact ((Nat.Prime.coprime_iff_not_dvd hr').mpr (h r hr' (Finset.mem_range.mp hrp) hrP)).symm

/-- `P` is coprime to `Nbag P p`. -/
theorem coprime_P_Nbag (P p : ℕ) : Nat.Coprime P (Nbag P p) := by
  unfold Nbag
  rw [Nat.coprime_prod_right_iff]
  intro r hr
  obtain ⟨_, hr', hrP⟩ := Finset.mem_filter.mp hr
  exact ((Nat.Prime.coprime_iff_not_dvd hr').mpr hrP).symm

/-- A prime `p` is coprime to `Nbag P p` (all its prime factors are `< p`). -/
theorem coprime_p_Nbag {p : ℕ} (hp : Nat.Prime p) (P : ℕ) : Nat.Coprime p (Nbag P p) := by
  unfold Nbag
  rw [Nat.coprime_prod_right_iff]
  intro r hr
  obtain ⟨hrp, hr', _⟩ := Finset.mem_filter.mp hr
  exact (Nat.coprime_primes hp hr').mpr (by have := Finset.mem_range.mp hrp; omega)

/-- **The reduction of `minFac m = p` on the progression.**  For `m ≥ 2` with `m ≡ 1 (mod P)`
and a prime `p ∤ P`: `minFac m = p ↔ p ∣ m ∧ Coprime m (Nbag P p)`. -/
theorem minFac_eq_iff_on_ap {P p m : ℕ} (hp : Nat.Prime p) (hm : 2 ≤ m) (hmP : m % P = 1 % P) :
    Nat.minFac m = p ↔ p ∣ m ∧ Nat.Coprime m (Nbag P p) := by
  have hm1 : m ≠ 1 := by omega
  -- primes dividing `P` do not divide `m`
  have hbag : ∀ r, Nat.Prime r → r ∣ P → ¬ r ∣ m := by
    intro r hr hrP hrm
    have h1 : m % r = 1 % r := by
      rw [← Nat.mod_mod_of_dvd m hrP, hmP, Nat.mod_mod_of_dvd 1 hrP]
    have h2 : m % r = 0 := Nat.mod_eq_zero_of_dvd hrm
    have h3 : 1 % r = 1 := Nat.mod_eq_of_lt hr.one_lt
    omega
  constructor
  · intro h
    refine ⟨h ▸ Nat.minFac_dvd m, ?_⟩
    rw [coprime_Nbag_iff]
    intro r hr hrp _ hrm
    have := Nat.minFac_le_of_dvd hr.two_le hrm
    omega
  · rintro ⟨hpm, hcop⟩
    apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le hpm)
    by_contra hlt
    push Not at hlt
    have hr := Nat.minFac_prime hm1
    have hrm := Nat.minFac_dvd m
    by_cases hrP : Nat.minFac m ∣ P
    · exact hbag _ hr hrP hrm
    · exact (coprime_Nbag_iff m P p).mp hcop _ hr hlt hrP hrm

/-! ## Part 3: the counts -/

/-- The progression population: `#{m ∈ [2, X] : m ≡ 1 (mod P)}`. -/
def apCount (P X : ℕ) : ℕ := ((Icc 2 X).filter (fun m => m % P = 1 % P)).card

/-- The bag-conditioned class count: `#{m ∈ [2, X] : m ≡ 1 (mod P), minFac m = p}`. -/
def bagClassCount (P p X : ℕ) : ℕ :=
  ((Icc 2 X).filter (fun m => m % P = 1 % P ∧ Nat.minFac m = p)).card

/-- The residue mod `p·P` that is `0 mod p` and `1 mod P`. -/
def crtClass (P p : ℕ) (hp : Nat.Prime p) (hpP : ¬ p ∣ P) : ℕ :=
  (Nat.chineseRemainder ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpP) 0 1).1

theorem crtClass_spec (P p : ℕ) (hp : Nat.Prime p) (hpP : ¬ p ∣ P) :
    crtClass P p hp hpP % p = 0 ∧ crtClass P p hp hpP % P = 1 % P := by
  unfold crtClass
  obtain ⟨h1, h2⟩ := (Nat.chineseRemainder ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpP) 0 1).2
  exact ⟨by simpa [Nat.ModEq] using h1, h2⟩

theorem crtClass_lt (P p : ℕ) (hp : Nat.Prime p) (hpP : ¬ p ∣ P) (hP : 0 < P) :
    crtClass P p hp hpP < p * P :=
  Nat.chineseRemainder_lt_mul _ 0 1 hp.ne_zero hP.ne'

/-- Membership in the class set, parametrised: `m ≡ 1 (P)` and `p ∣ m` iff `m ≡ c₀ (mod pP)`. -/
theorem mem_class_iff {P p m : ℕ} (hp : Nat.Prime p) (hpP : ¬ p ∣ P) :
    (m % P = 1 % P ∧ p ∣ m) ↔ m % (p * P) = crtClass P p hp hpP % (p * P) := by
  set c := crtClass P p hp hpP
  obtain ⟨hc1, hc2⟩ := crtClass_spec P p hp hpP
  have hcop : Nat.Coprime p P := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpP
  constructor
  · rintro ⟨h1, h2⟩
    have hmp : m ≡ c [MOD p] := by
      show m % p = c % p; rw [Nat.mod_eq_zero_of_dvd h2, hc1]
    have hmP : m ≡ c [MOD P] := by show m % P = c % P; rw [h1, hc2]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hmp, hmP⟩
  · intro h
    obtain ⟨h1, h2⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mpr h
    refine ⟨?_, ?_⟩
    · show m % P = 1 % P; exact (show m % P = c % P from h2).trans hc2
    · exact Nat.dvd_of_mod_eq_zero ((show m % p = c % p from h1).trans hc1)

/-! ## Part 4: block bounds along the progression -/

/-- Notation: `M = p·P`, `c₀` the CRT class, `N' = Nbag P p`.  `M` is coprime to `N'`. -/
theorem coprime_M_Nbag {p : ℕ} (hp : Nat.Prime p) (P : ℕ) : Nat.Coprime (p * P) (Nbag P p) :=
  Nat.Coprime.mul_left (coprime_p_Nbag hp P) (coprime_P_Nbag P p)



section Counting

variable {P p : ℕ} (hp : Nat.Prime p) (hpP : ¬ p ∣ P) (hP : 0 < P)
include hp hpP hP

/-- The class set is the image of the affine parametrisation restricted by coprimality. -/
theorem bagClass_eq_image (X : ℕ) :
    (Icc 2 X).filter (fun m => m % P = 1 % P ∧ Nat.minFac m = p) =
      ((Finset.range (X + 1)).filter (fun t =>
        2 ≤ crtClass P p hp hpP + p * P * t ∧ crtClass P p hp hpP + p * P * t ≤ X ∧
        Nat.Coprime (Nbag P p) (p * P * t + crtClass P p hp hpP))).image
        (fun t => crtClass P p hp hpP + p * P * t) := by
  set c := crtClass P p hp hpP with hc
  set M := p * P with hM
  have hMpos : 0 < M := Nat.mul_pos hp.pos hP
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨hm2, hmX⟩, hmP, hmin⟩
    have hcls := (minFac_eq_iff_on_ap hp hm2 hmP).mp hmin
    have hmod : m % M = c % M := (mem_class_iff hp hpP).mp ⟨hmP, hcls.1⟩
    have hclt : c < M := crtClass_lt P p hp hpP hP
    -- m = c + M t with t = (m - c) / M
    have hcm : c ≤ m := by
      by_contra hlt; push Not at hlt
      have : m % M = m := Nat.mod_eq_of_lt (lt_trans hlt hclt)
      have : c % M = c := Nat.mod_eq_of_lt hclt
      omega
    have hdvd : M ∣ m - c := by
      have := (Nat.modEq_iff_dvd' hcm).mp (show c ≡ m [MOD M] from hmod.symm)
      exact this
    obtain ⟨t, ht⟩ := hdvd
    have htM : t ≤ M * t := Nat.le_mul_of_pos_left t hMpos
    refine ⟨t, ?_, ?_⟩
    · refine ⟨by omega, ⟨by omega, by omega, ?_⟩⟩
      rw [show M * t + c = m by omega]
      exact hcls.2.symm
    · omega
  · rintro ⟨t, ⟨_, h2, hX, hcop⟩, rfl⟩
    have hmP : (c + M * t) % P = 1 % P := by
      have := (mem_class_iff (m := c + M * t) hp hpP).mpr
        (by rw [Nat.add_mul_mod_self_left])
      exact this.1
    have hpm : p ∣ c + M * t :=
      ((mem_class_iff (m := c + M * t) hp hpP).mpr
        (by rw [Nat.add_mul_mod_self_left])).2
    refine ⟨⟨h2, hX⟩, hmP, ?_⟩
    rw [minFac_eq_iff_on_ap hp h2 hmP]
    refine ⟨hpm, ?_⟩
    rw [show c + M * t = M * t + c by ring]
    exact hcop.symm

/-- Lower bound: `⌊((X − c₀)/M)/N'⌋ · A' ≤ bagClassCount`. -/
theorem bagClassCount_ge (X : ℕ) :
    ((X - crtClass P p hp hpP) / (p * P) / Nbag P p) * Abag P p ≤ bagClassCount P p X := by
  set c := crtClass P p hp hpP with hc
  set M := p * P with hM
  set N' := Nbag P p with hN'
  have hMpos : 0 < M := Nat.mul_pos hp.pos hP
  have hM2 : 2 ≤ M := by
    have := hp.two_le
    calc 2 ≤ p := this
      _ = p * 1 := (mul_one p).symm
      _ ≤ p * P := Nat.mul_le_mul_left p hP
  unfold bagClassCount
  rw [bagClass_eq_image hp hpP hP]
  set T := (X - c) / M with hT
  set B := T / N' with hB
  -- the block `Ico 1 (1 + B N')` of parameters is admissible
  have hsub : (Ico 1 (1 + B * N')).filter (fun t => Nat.Coprime N' (M * t + c)) ⊆
      (Finset.range (X + 1)).filter (fun t => 2 ≤ c + M * t ∧ c + M * t ≤ X ∧
        Nat.Coprime N' (M * t + c)) := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_Ico] at ht
    rw [Finset.mem_filter, Finset.mem_range]
    have htB : t ≤ B * N' := by omega
    have htT : t ≤ T := le_trans htB (Nat.div_mul_le_self T N')
    have hMt : M * t ≤ X - c := by
      calc M * t ≤ M * T := Nat.mul_le_mul_left M htT
        _ ≤ X - c := by rw [hT, mul_comm]; exact Nat.div_mul_le_self _ _
    have htM : t ≤ M * t := Nat.le_mul_of_pos_left t hMpos
    refine ⟨?_, ?_, ?_, ht.2⟩
    · omega
    · have := ht.1.1; nlinarith
    · omega
  have hinj : Set.InjOn (fun t => c + M * t) ((Ico 1 (1 + B * N')).filter
      (fun t => Nat.Coprime N' (M * t + c)) : Set ℕ) := by
    intro a _ b _ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_left hMpos (by omega)
  calc (T / N') * Abag P p
      = B * Nat.totient N' := by rw [hB, totient_Nbag]
    _ = ((Ico 1 (1 + B * N')).filter (fun t => Nat.Coprime N' (M * t + c))).card :=
        (card_coprime_affine_blocks (Nbag_pos P p) (coprime_M_Nbag hp P) c 1 B).symm
    _ = (((Ico 1 (1 + B * N')).filter (fun t => Nat.Coprime N' (M * t + c))).image
          (fun t => c + M * t)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card (Finset.image_subset_image hsub)

/-- Upper bound: `bagClassCount ≤ (⌊(X/M)/N'⌋ + 1) · A'`. -/
theorem bagClassCount_le (X : ℕ) :
    bagClassCount P p X ≤ (X / (p * P) / Nbag P p + 1) * Abag P p := by
  set c := crtClass P p hp hpP with hc
  set M := p * P with hM
  set N' := Nbag P p with hN'
  have hMpos : 0 < M := Nat.mul_pos hp.pos hP
  unfold bagClassCount
  rw [bagClass_eq_image hp hpP hP]
  set B := X / M / N' with hB
  have hsub : (Finset.range (X + 1)).filter (fun t => 2 ≤ c + M * t ∧ c + M * t ≤ X ∧
        Nat.Coprime N' (M * t + c)) ⊆
      (Ico 0 (0 + (B + 1) * N')).filter (fun t => Nat.Coprime N' (M * t + c)) := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_range] at ht
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨Nat.zero_le _, ?_⟩, ht.2.2.2⟩
    have hMt : M * t ≤ X := by omega
    have ht1 : t ≤ X / M := (Nat.le_div_iff_mul_le hMpos).mpr (by rw [mul_comm]; exact hMt)
    have ht2 : X / M < (B + 1) * N' := by
      rw [hB]
      have := Nat.lt_div_mul_add (a := X / M) (Nbag_pos P p)
      nlinarith [Nat.div_add_mod (X / M) N', Nat.mod_lt (X / M) (Nbag_pos P p)]
    omega
  calc (((Finset.range (X + 1)).filter (fun t => 2 ≤ c + M * t ∧ c + M * t ≤ X ∧
          Nat.Coprime N' (M * t + c))).image (fun t => c + M * t)).card
      ≤ ((Finset.range (X + 1)).filter (fun t => 2 ≤ c + M * t ∧ c + M * t ≤ X ∧
          Nat.Coprime N' (M * t + c))).card := Finset.card_image_le
    _ ≤ ((Ico 0 (0 + (B + 1) * N')).filter (fun t => Nat.Coprime N' (M * t + c))).card :=
        Finset.card_le_card hsub
    _ = (B + 1) * Nat.totient N' :=
        card_coprime_affine_blocks (Nbag_pos P p) (coprime_M_Nbag hp P) c 0 (B + 1)
    _ = (B + 1) * Abag P p := by rw [totient_Nbag]

end Counting

/-! ## Part 5: the densities -/

theorem apCount_bounds (P X : ℕ) (hP : 0 < P) :
    (X / P) * 1 ≤ apCount P X + 2 ∧ apCount P X ≤ (X / P + 1) * 1 := by
  -- the progression `1 mod P` meets `[0, X]` in `⌊X/P⌋ + 1` points and `[2, X]` in at least
  -- `⌊X/P⌋ − 1` of them; we go through blocks with `N = P`, `a = 1`, `b = 1`, coprimality
  -- replaced by the class condition — done directly.
  unfold apCount
  constructor
  · -- lower bound: the points `1 + P·t`, `1 ≤ t ≤ ⌊X/P⌋ − 1`... use `t ∈ Ico 1 (X/P)`
    have hsub : (Ico 1 (X / P)).image (fun t => 1 + P * t) ⊆
        (Icc 2 X).filter (fun m => m % P = 1 % P) := by
      intro m hm
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hm
      rw [Finset.mem_Ico] at ht
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by nlinarith, ?_⟩, by rw [Nat.add_mul_mod_self_left]⟩
      have : P * t < P * (X / P) := Nat.mul_lt_mul_of_pos_left ht.2 hP
      have := Nat.mul_div_le X P
      omega
    have hinj : Set.InjOn (fun t => 1 + P * t) ((Ico 1 (X / P)) : Set ℕ) := by
      intro a _ b _ h; simp only at h; exact Nat.eq_of_mul_eq_mul_left hP (by omega)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Nat.card_Ico] at h1
    omega
  · have hsub : (Icc 2 X).filter (fun m => m % P = 1 % P) ⊆
        (Icc 0 (X / P)).image (fun t => 1 + P * t) := by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      have h1P : 1 % P ≤ 1 := Nat.mod_le 1 P
      have hm1 : m % P = 1 % P := hm.2
      -- m ≥ 1 % P; write m = 1 % P + P * (m / P); and 1 % P = 1 unless P = 1
      rcases Nat.eq_or_lt_of_le hP with hP1 | hP1
      · -- P = 1
        have hP1' : P = 1 := by omega
        subst hP1'
        refine Finset.mem_image.mpr ⟨m - 1, ?_, by omega⟩
        rw [Finset.mem_Icc, Nat.div_one]; omega
      · have h1P' : 1 % P = 1 := Nat.mod_eq_of_lt hP1
        rw [h1P'] at hm1
        refine Finset.mem_image.mpr ⟨m / P, ?_, ?_⟩
        · rw [Finset.mem_Icc]; exact ⟨Nat.zero_le _, Nat.div_le_div_right hm.1.2⟩
        · have := Nat.div_add_mod m P; rw [hm1] at this; omega
    have h1 := Finset.card_le_card hsub
    calc _ ≤ ((Icc 0 (X / P)).image (fun t => 1 + P * t)).card := h1
      _ ≤ (Icc 0 (X / P)).card := Finset.card_image_le
      _ = X / P + 1 := by simp
      _ = (X / P + 1) * 1 := (mul_one _).symm

/-- **The progression has density `1/P`.** -/
theorem tendsto_apCount_div (P : ℕ) (hP : 0 < P) :
    Filter.Tendsto (fun X : ℕ => (apCount P X : ℝ) / X) Filter.atTop (nhds (1 / (P : ℝ))) := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := exists_nat_gt (3 / ε)
  refine ⟨max X₀ 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hXX₀ : (X₀ : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_left _ _) hX
  obtain ⟨hlo, hhi⟩ := apCount_bounds P X hP
  obtain ⟨hd1, hd2⟩ := HeadDomination.nat_div_bounds X P hP
  have hlo' : (X : ℝ) / P - 1 ≤ (apCount P X : ℝ) + 2 := by
    have : ((X / P : ℕ) : ℝ) ≤ (apCount P X : ℝ) + 2 := by exact_mod_cast (by simpa using hlo)
    linarith
  have hhi' : (apCount P X : ℝ) ≤ (X : ℝ) / P + 1 := by
    have : (apCount P X : ℝ) ≤ ((X / P : ℕ) : ℝ) + 1 := by exact_mod_cast (by simpa using hhi)
    linarith
  have hkey : (3 : ℝ) < ε * X := by
    have : (3 : ℝ) / ε < X := lt_of_lt_of_le hX₀ hXX₀
    rw [div_lt_iff₀ hε] at this; linarith
  rw [Real.dist_eq, abs_lt]
  have hlow : 1 / (P : ℝ) - ε < (apCount P X : ℝ) / X := by
    rw [lt_div_iff₀ hXpos]
    have : (X : ℝ) * (1 / P) = X / P := by ring
    nlinarith
  have hup : (apCount P X : ℝ) / X < 1 / (P : ℝ) + ε := by
    rw [div_lt_iff₀ hXpos]
    have : (X : ℝ) * (1 / P) = X / P := by ring
    nlinarith
  constructor <;> linarith

/-- **The bag-conditioned class has density `bagWeight P p / P`.** -/
theorem tendsto_bagClassCount_div {P p : ℕ} (hp : Nat.Prime p) (hpP : ¬ p ∣ P) (hP : 0 < P) :
    Filter.Tendsto (fun X : ℕ => (bagClassCount P p X : ℝ) / X) Filter.atTop
      (nhds (bagWeight P p / P)) := by
  set c := crtClass P p hp hpP with hc
  set M := p * P with hM
  set N' := Nbag P p with hN'
  set A' := Abag P p with hA'
  have hMpos : 0 < M := Nat.mul_pos hp.pos hP
  have hN'pos : 0 < N' := Nbag_pos P p
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hN'r : (0 : ℝ) < N' := by exact_mod_cast hN'pos
  have hval : bagWeight P p / P = (A' : ℝ) / (M * N') := by
    unfold bagWeight; rw [hM, ← hN', ← hA']; push_cast; field_simp
  rw [hval, Metric.tendsto_atTop]
  intro ε hε
  -- error terms are `O(1/X)`: `A' · (c/(M N') + 2) / X`
  set K : ℝ := (A' : ℝ) * ((c : ℝ) / (M * N') + 2) with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨X₀, hX₀⟩ := exists_nat_gt (K / ε)
  refine ⟨max X₀ 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hXX₀ : (X₀ : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_left _ _) hX
  have hKX : K < ε * X := by
    have : K / ε < X := lt_of_lt_of_le hX₀ hXX₀
    rw [div_lt_iff₀ hε] at this; linarith
  have hlo := bagClassCount_ge hp hpP hP X
  have hhi := bagClassCount_le hp hpP hP X
  -- real forms of the two Nat divisions
  have hd_lo : ((X : ℝ) - c) / M / N' - 2 ≤ (((X - c) / M / N' : ℕ) : ℝ) := by
    have h1 := (HeadDomination.nat_div_bounds (X - c) M hMpos).1
    have h2 := (HeadDomination.nat_div_bounds ((X - c) / M) N' hN'pos).1
    have hsub : (X : ℝ) - c ≤ ((X - c : ℕ) : ℝ) := by
      rcases le_or_gt c X with h | h
      · rw [Nat.cast_sub h]
      · rw [Nat.sub_eq_zero_of_le h.le]; push_cast
        have : (X : ℝ) < c := by exact_mod_cast h
        linarith
    have h3 : ((X : ℝ) - c) / M ≤ ((X - c : ℕ) : ℝ) / M := div_le_div_of_nonneg_right hsub hMr.le
    have h4 : (((X : ℝ) - c) / M - 1) / N' ≤ (((X - c) / M : ℕ) : ℝ) / N' :=
      div_le_div_of_nonneg_right (by linarith) hN'r.le
    have h5 : (1 : ℝ) / N' ≤ 1 := by rw [div_le_one hN'r]; exact_mod_cast hN'pos
    have h6 : (((X : ℝ) - c) / M - 1) / N' = ((X : ℝ) - c) / M / N' - 1 / N' := by ring
    linarith
  have hd_hi : (((X / M / N' : ℕ) : ℝ)) ≤ (X : ℝ) / M / N' := by
    have h1 := (HeadDomination.nat_div_bounds X M hMpos).2
    have h2 := (HeadDomination.nat_div_bounds (X / M) N' hN'pos).2
    calc (((X / M / N' : ℕ) : ℝ)) ≤ ((X / M : ℕ) : ℝ) / N' := h2
      _ ≤ (X : ℝ) / M / N' := div_le_div_of_nonneg_right h1 hN'r.le
  have hlo' : ((X : ℝ) - c) / (M * N') * A' - 2 * A' ≤ (bagClassCount P p X : ℝ) := by
    have : (((X - c) / M / N' : ℕ) : ℝ) * A' ≤ (bagClassCount P p X : ℝ) := by exact_mod_cast hlo
    have hA : (0 : ℝ) ≤ A' := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_right hd_lo hA
    rw [div_div] at this
    linarith
  have hhi' : (bagClassCount P p X : ℝ) ≤ (X : ℝ) / (M * N') * A' + A' := by
    have : (bagClassCount P p X : ℝ) ≤ (((X / M / N' : ℕ) : ℝ) + 1) * A' := by exact_mod_cast hhi
    have hA : (0 : ℝ) ≤ A' := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_right hd_hi hA
    rw [div_div] at this
    linarith
  rw [Real.dist_eq, abs_lt]
  set w := (A' : ℝ) / (M * N') with hw
  have hw0 : 0 ≤ w := by positivity
  have hlow : w - ε < (bagClassCount P p X : ℝ) / X := by
    rw [lt_div_iff₀ hXpos]
    have e1 : ((X : ℝ) - c) / (M * N') * A' = X * w - (c : ℝ) / (M * N') * A' := by
      rw [hw]; ring
    have hcK : (c : ℝ) / (M * N') * A' + 2 * A' = K := by rw [hK]; ring
    nlinarith
  have hup : (bagClassCount P p X : ℝ) / X < w + ε := by
    rw [div_lt_iff₀ hXpos]
    have e2 : (X : ℝ) / (M * N') * A' = X * w := by rw [hw]; ring
    have hAK : (A' : ℝ) ≤ K := by
      rw [hK]; nlinarith [(Nat.cast_nonneg A' : (0:ℝ) ≤ A'), show (0:ℝ) ≤ (c : ℝ) / (M * N') by positivity]
    nlinarith
  constructor <;> linarith

/-- **The bag-conditioned multiplier law.**  Relative to the progression `1 (mod P)`, the least
prime factor equals the prime `p ∤ P` with density `bagWeight P p = (1/p)∏_{r<p, r∤P}(1−1/r)`. -/
theorem tendsto_bagClass_div_ap {P p : ℕ} (hp : Nat.Prime p) (hpP : ¬ p ∣ P) (hP : 0 < P) :
    Filter.Tendsto (fun X : ℕ => (bagClassCount P p X : ℝ) / (apCount P X : ℝ)) Filter.atTop
      (nhds (bagWeight P p)) := by
  have h1 := tendsto_bagClassCount_div hp hpP hP
  have h2 := tendsto_apCount_div P hP
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hne : (1 : ℝ) / P ≠ 0 := by positivity
  have := h1.div h2 hne
  have hval : bagWeight P p / P / (1 / (P : ℝ)) = bagWeight P p := by field_simp
  rw [hval] at this
  refine this.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (3 * P)] with X hX
  have hXpos : (0 : ℝ) < X := by
    have : 0 < X := by omega
    exact_mod_cast this
  exact div_div_div_cancel_right₀ hXpos.ne' _ _

/-! ## Part 6: the least missing prime -/

/-- **The least prime outside the bag is selected with density exactly `1/q`.**  If every prime
below `q` divides `P`, the sieve outside the bag is empty and `bagWeight P q = 1/q`, whatever
`q`'s residue classes and whatever the bag. -/
theorem bagWeight_least_missing {P q : ℕ}
    (hleast : ∀ r, Nat.Prime r → r < q → r ∣ P) : bagWeight P q = 1 / (q : ℝ) := by
  have hempty : (range q).filter (fun r => Nat.Prime r ∧ ¬ r ∣ P) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro r hr ⟨hr', hrP⟩
    exact hrP (hleast r hr' (Finset.mem_range.mp hr))
  unfold bagWeight Abag Nbag
  rw [hempty]
  simp

/-- The Shanks heuristic, made exact at the population level: for the least prime `q` outside
the bag of `P`, the class `{m ≡ 1 (mod P) : minFac m = q}` has relative density exactly `1/q`. -/
theorem tendsto_least_missing_div_ap {P q : ℕ} (hq : Nat.Prime q) (hqP : ¬ q ∣ P) (hP : 0 < P)
    (hleast : ∀ r, Nat.Prime r → r < q → r ∣ P) :
    Filter.Tendsto (fun X : ℕ => (bagClassCount P q X : ℝ) / (apCount P X : ℝ)) Filter.atTop
      (nhds (1 / (q : ℝ))) := by
  rw [← bagWeight_least_missing hleast]
  exact tendsto_bagClass_div_ap hq hqP hP

end BagConditionedLaw

end
