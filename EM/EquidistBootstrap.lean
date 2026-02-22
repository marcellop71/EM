import EM.EquidistCharPRE

/-!
# Inductive Bootstrap, Minimality Sieve, and Irreducible Core

* Inductive bootstrap: MC(<p) + PrimeResidueEscape → SE(p)
* PrimeResidueEscape proved elementarily
* Minimality sieve: `minimality_sieve`, `walkZ_hit_at_seq_succ`
* Irreducible core: `DynamicalHitting → MullinConjecture`
-/

open Mullin Euclid MullinGroup RotorRouter


/-! ## §11. Inductive Bootstrap: MC below p → SE at p

The key structural observation: assuming Mullin's Conjecture for all primes
below p, the multiplier residues mod p include all primes in {3, 5, ..., p−2}.
Under the hypothesis that these primes escape every proper subgroup of (Z/pZ)×
(**PrimeResidueEscape**, a consequence of Burgess's bound on the least character
non-residue), SubgroupEscape holds at p.

Note: this does NOT use Dirichlet's theorem on primes in arithmetic progressions.
We do not need every residue class mod p to contain a prime < p (which is false).
We only need: for every proper subgroup H, some prime < p lies outside H.
This is the content of Burgess's theorem: the least element of (Z/pZ)× \ H
is O(p^{0.161}), hence < p for all p.

This establishes **MC(< p) → SE(p)**, showing that the algebraic component
of the reduction is "bootstrapped" from MC at smaller primes. The missing
ingredient for a full inductive proof of MC is the dynamical component
(EMPR / MixingHypothesis / HH) — SE alone does not give MC.
-/

section InductiveBootstrap

/-- MC holds for all primes below p: every prime r < p appears in the
    Euclid-Mullin sequence. -/
def mc_below (p : Nat) : Prop :=
  ∀ r, Nat.Prime r → r < p → ∃ k, seq k = r

/-- A prime r < p maps to a nonzero element of ZMod p. -/
private theorem natCast_prime_ne_zero {p r : Nat} [Fact (Nat.Prime p)]
    (hr : Nat.Prime r) (hrp : r < p) : ((r : Nat) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have : p ≤ r := Nat.le_of_dvd (by have := hr.one_lt; omega) hdvd
  omega

/-- **Prime Residue Escape**: for every prime p ≥ 5 and proper subgroup
    H < (Z/pZ)×, some prime r ∈ [3, p) has residue outside H.

    Proved elementarily (no Burgess needed): if all odd primes < p are in H,
    then every odd integer < p is in H (by factorization). In particular
    p−2 ≡ −2 and p−4 ≡ −4 are in H, so 2 = (−4)(−2)⁻¹ ∈ H. Now all
    primes < p are in H, hence H = (Z/pZ)× — contradicting H proper. -/
def PrimeResidueEscape : Prop :=
  ∀ (p : Nat) [Fact (Nat.Prime p)], 5 ≤ p →
    ∀ (H : Subgroup (ZMod p)ˣ), H ≠ ⊤ →
      ∃ (r : Nat) (hr : Nat.Prime r) (hrp : r < p),
        3 ≤ r ∧ Units.mk0 ((r : Nat) : ZMod p) (natCast_prime_ne_zero hr hrp) ∉ H

/-- Any m ∈ [1, p) maps to a nonzero element of ZMod p. -/
private theorem natCast_pos_ne_zero {p m : Nat} [Fact (Nat.Prime p)]
    (hm : 1 ≤ m) (hmp : m < p) : ((m : Nat) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd; exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

/-- If every prime r < p maps into H, then every m ∈ [1, p) maps into H.
    Proof by strong induction: m = 1 is trivial, m prime is by hypothesis,
    m composite factors as minFac(m) · (m/minFac(m)) with both factors smaller. -/
private theorem unit_mem_of_all_primes_mem {p : Nat} [Fact (Nat.Prime p)]
    (H : Subgroup (ZMod p)ˣ)
    (hp : ∀ r, Nat.Prime r → r < p → (hr : ((r : Nat) : ZMod p) ≠ 0) →
      Units.mk0 ((r : Nat) : ZMod p) hr ∈ H)
    (m : Nat) (hm1 : 1 ≤ m) (hmp : m < p) (hm0 : ((m : Nat) : ZMod p) ≠ 0) :
    Units.mk0 ((m : Nat) : ZMod p) hm0 ∈ H := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases hm_one : m = 1
    · -- m = 1: the unit is 1
      subst hm_one; convert H.one_mem using 1; exact Units.ext (by simp)
    · -- m ≥ 2
      have hm2 : 2 ≤ m := by omega
      by_cases hprime : Nat.Prime m
      · -- m is prime: in H by hypothesis
        exact hp m hprime hmp hm0
      · -- m is composite: factor via minFac
        have hm2' : m ≠ 1 := by omega
        have hfp : (Nat.minFac m).Prime := Nat.minFac_prime hm2'
        have hfd : Nat.minFac m ∣ m := Nat.minFac_dvd m
        have hfne : Nat.minFac m ≠ m := fun h => hprime (h ▸ hfp)
        have hflt : Nat.minFac m < m := lt_of_le_of_ne (Nat.minFac_le (by omega)) hfne
        set a := Nat.minFac m with ha_def
        set b := m / a with hb_def
        have hab : a * b = m := Nat.mul_div_cancel' hfd
        have hb1 : 1 ≤ b := by
          rw [Nat.one_le_iff_ne_zero]; intro hb0
          rw [hb0, Nat.mul_zero] at hab; omega
        have hblt : b < m :=
          Nat.div_lt_self (by omega) hfp.one_lt
        have hap : a < p := lt_trans hflt hmp
        have hbp : b < p := lt_trans hblt hmp
        have ha0 : ((a : Nat) : ZMod p) ≠ 0 :=
          natCast_pos_ne_zero (Nat.one_le_of_lt hfp.one_lt) hap
        have hb0 : ((b : Nat) : ZMod p) ≠ 0 := natCast_pos_ne_zero hb1 hbp
        -- Both factors map into H
        have ha_mem : Units.mk0 ((a : Nat) : ZMod p) ha0 ∈ H :=
          hp a hfp hap ha0
        have hb_mem : Units.mk0 ((b : Nat) : ZMod p) hb0 ∈ H :=
          ih b hblt hb1 hbp hb0
        -- m = a * b, so unit(m) = unit(a) * unit(b)
        have heq : Units.mk0 ((m : Nat) : ZMod p) hm0 =
            Units.mk0 ((a : Nat) : ZMod p) ha0 *
            Units.mk0 ((b : Nat) : ZMod p) hb0 := by
          apply Units.ext; simp only [Units.val_mk0, Units.val_mul]
          rw [← Nat.cast_mul]; congr 1; exact hab.symm
        rw [heq]; exact H.mul_mem ha_mem hb_mem

/-- Odd integers in [1, p) are in H if all odd primes < p are in H.
    The induction works because odd numbers only have odd prime factors. -/
private theorem odd_unit_mem_of_odd_primes_mem {p : Nat} [Fact (Nat.Prime p)]
    (H : Subgroup (ZMod p)ˣ)
    (hp : ∀ r, Nat.Prime r → r < p → 3 ≤ r → (hr : ((r : Nat) : ZMod p) ≠ 0) →
      Units.mk0 ((r : Nat) : ZMod p) hr ∈ H)
    (m : Nat) (hm1 : 1 ≤ m) (hmp : m < p) (hm0 : ((m : Nat) : ZMod p) ≠ 0)
    (hm_odd : ¬ 2 ∣ m) :
    Units.mk0 ((m : Nat) : ZMod p) hm0 ∈ H := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases hm_one : m = 1
    · subst hm_one; convert H.one_mem using 1; exact Units.ext (by simp)
    · have hm2 : 2 ≤ m := by omega
      by_cases hprime : Nat.Prime m
      · have hm3 : 3 ≤ m := by
          by_contra h; push_neg at h
          exact hm_odd ⟨1, by omega⟩
        exact hp m hprime hmp hm3 hm0
      · have hm2' : m ≠ 1 := by omega
        have hfp : (Nat.minFac m).Prime := Nat.minFac_prime hm2'
        have hfd : Nat.minFac m ∣ m := Nat.minFac_dvd m
        have hfne : Nat.minFac m ≠ m := fun h => hprime (h ▸ hfp)
        have hflt : Nat.minFac m < m := lt_of_le_of_ne (Nat.minFac_le (by omega)) hfne
        set a := Nat.minFac m with ha_def
        set b := m / a with hb_def
        have hab : a * b = m := Nat.mul_div_cancel' hfd
        have ha_odd : ¬ 2 ∣ a := fun h => hm_odd (dvd_trans h hfd)
        have hb_odd : ¬ 2 ∣ b := by
          intro h2b; apply hm_odd; rw [← hab]; exact dvd_mul_of_dvd_right h2b a
        have hb1 : 1 ≤ b := by
          rw [Nat.one_le_iff_ne_zero]; intro hb0
          rw [hb0, Nat.mul_zero] at hab; omega
        have hblt : b < m := Nat.div_lt_self (by omega) hfp.one_lt
        have hap : a < p := lt_trans hflt hmp
        have hbp : b < p := lt_trans hblt hmp
        have ha0 : ((a : Nat) : ZMod p) ≠ 0 :=
          natCast_pos_ne_zero (Nat.one_le_of_lt hfp.one_lt) hap
        have hb0 : ((b : Nat) : ZMod p) ≠ 0 := natCast_pos_ne_zero hb1 hbp
        have ha3 : 3 ≤ a := by
          by_contra h; push_neg at h
          exact ha_odd ⟨1, by have := hfp.two_le; omega⟩
        have ha_mem : Units.mk0 ((a : Nat) : ZMod p) ha0 ∈ H :=
          hp a hfp hap ha3 ha0
        have hb_mem : Units.mk0 ((b : Nat) : ZMod p) hb0 ∈ H :=
          ih b hblt hb1 hbp hb0 hb_odd
        have heq : Units.mk0 ((m : Nat) : ZMod p) hm0 =
            Units.mk0 ((a : Nat) : ZMod p) ha0 *
            Units.mk0 ((b : Nat) : ZMod p) hb0 := by
          apply Units.ext; simp only [Units.val_mk0, Units.val_mul]
          rw [← Nat.cast_mul]; congr 1; exact hab.symm
        rw [heq]; exact H.mul_mem ha_mem hb_mem

open Classical in
/-- If every prime r < p maps into H, then H = ⊤.
    Uses a cardinality argument: the map k ↦ Units.mk0 (k+1) for k ∈ {0,...,p−2}
    injects into H, giving |H| ≥ p−1 = |(ZMod p)ˣ|. -/
private theorem subgroup_eq_top_of_all_primes_mem {p : Nat} [inst : Fact (Nat.Prime p)]
    (H : Subgroup (ZMod p)ˣ)
    (hp : ∀ r, Nat.Prime r → r < p → (hr : ((r : Nat) : ZMod p) ≠ 0) →
      Units.mk0 ((r : Nat) : ZMod p) hr ∈ H) :
    H = ⊤ := by
  -- Show every unit is in H via its ZMod.val representative
  rw [Subgroup.eq_top_iff']
  intro u
  -- The natural number representative
  set m := ZMod.val u.val with hm_def
  have hm_lt : m < p := ZMod.val_lt u.val
  have hm_pos : 0 < m := by
    by_contra h; push_neg at h
    have : m = 0 := by omega
    rw [hm_def] at this
    have : u.val = 0 := by rwa [ZMod.val_eq_zero] at this
    exact u.ne_zero this
  have hm0 : ((m : Nat) : ZMod p) ≠ 0 := natCast_pos_ne_zero (by omega) hm_lt
  -- Round-trip: casting m back gives u.val
  have hcast : ((m : Nat) : ZMod p) = u.val := by
    rw [hm_def]; exact ZMod.natCast_zmod_val u.val
  -- So Units.mk0 (m : ZMod p) = u
  have hu_eq : Units.mk0 ((m : Nat) : ZMod p) hm0 = u :=
    Units.ext hcast
  rw [← hu_eq]
  exact unit_mem_of_all_primes_mem H hp m (by omega) hm_lt hm0

/-- **PrimeResidueEscape holds for all primes p ≥ 5.**

    Elementary proof (no Burgess needed): assume all odd primes r ∈ [3, p)
    are in a proper subgroup H. Then every odd integer in [1, p) is in H
    (by prime factorization). In particular p−2 ≡ −2 and p−4 ≡ −4 are
    in H, giving 2 = (−4)(−2)⁻¹ ∈ H. Now all primes < p are in H,
    hence H = (Z/pZ)× — contradicting H proper. -/
theorem prime_residue_escape : PrimeResidueEscape := by
  intro p inst hp5 H hH
  -- Proof by contradiction: assume every odd prime r ∈ [3,p) is in H
  by_contra h_all_in
  push_neg at h_all_in
  -- h_all_in : ∀ r, Nat.Prime r → r < p → 3 ≤ r → Units.mk0 ... ∈ H
  apply hH
  -- Adapt h_all_in to use generic nonzero proof
  have hodd : ∀ r, Nat.Prime r → r < p → 3 ≤ r → (hr : ((r : Nat) : ZMod p) ≠ 0) →
      Units.mk0 ((r : Nat) : ZMod p) hr ∈ H := by
    intro r hr hrp hr3 hr0
    convert h_all_in r hr hrp hr3 using 1
  -- Step 1: Show 2 ∈ H via the (-4)·(-2)⁻¹ trick
  have hp_prime := (Fact.out : Nat.Prime p)
  have hp_odd : ¬ 2 ∣ p := by
    intro h; rcases hp_prime.eq_one_or_self_of_dvd 2 h with h | h <;> omega
  -- p-2 and p-4 are odd, in [1, p)
  have hpm2_ne : ((p - 2 : Nat) : ZMod p) ≠ 0 := natCast_pos_ne_zero (by omega) (by omega)
  have hpm4_ne : ((p - 4 : Nat) : ZMod p) ≠ 0 := natCast_pos_ne_zero (by omega) (by omega)
  have hpm2_odd : ¬ 2 ∣ (p - 2) := by
    intro ⟨k, hk⟩; apply hp_odd; exact ⟨k + 1, by omega⟩
  have hpm4_odd : ¬ 2 ∣ (p - 4) := by
    intro ⟨k, hk⟩; apply hp_odd; exact ⟨k + 2, by omega⟩
  -- p-2 and p-4 map to units in H (odd, so only odd prime factors)
  have hm2_mem : Units.mk0 ((p - 2 : Nat) : ZMod p) hpm2_ne ∈ H :=
    odd_unit_mem_of_odd_primes_mem H hodd _ (by omega) (by omega) hpm2_ne hpm2_odd
  have hm4_mem : Units.mk0 ((p - 4 : Nat) : ZMod p) hpm4_ne ∈ H :=
    odd_unit_mem_of_odd_primes_mem H hodd _ (by omega) (by omega) hpm4_ne hpm4_odd
  -- Key: 2 * (p-2) ≡ p + (p-4) ≡ p-4 (mod p)
  have h2_ne : ((2 : Nat) : ZMod p) ≠ 0 := natCast_pos_ne_zero (by omega) (by omega)
  have hmul : Units.mk0 ((2 : Nat) : ZMod p) h2_ne *
      Units.mk0 ((p - 2 : Nat) : ZMod p) hpm2_ne =
      Units.mk0 ((p - 4 : Nat) : ZMod p) hpm4_ne := by
    apply Units.ext; simp only [Units.val_mk0, Units.val_mul]
    rw [← Nat.cast_ofNat, ← Nat.cast_mul]
    show ((2 * (p - 2) : Nat) : ZMod p) = ((p - 4 : Nat) : ZMod p)
    have : 2 * (p - 2) = p + (p - 4) := by omega
    rw [this, Nat.cast_add]; simp
  -- So 2 = (p-4) * (p-2)⁻¹ ∈ H
  have h2_mem : Units.mk0 ((2 : Nat) : ZMod p) h2_ne ∈ H := by
    have h2_eq : Units.mk0 ((2 : Nat) : ZMod p) h2_ne =
        Units.mk0 ((p - 4 : Nat) : ZMod p) hpm4_ne *
        (Units.mk0 ((p - 2 : Nat) : ZMod p) hpm2_ne)⁻¹ := by
      rw [← hmul, mul_assoc, mul_inv_cancel, mul_one]
    rw [h2_eq]; exact H.mul_mem hm4_mem (H.inv_mem hm2_mem)
  -- Step 2: Now all primes < p are in H → H = ⊤
  apply subgroup_eq_top_of_all_primes_mem
  intro r hr hrp hr0
  by_cases hr2 : r = 2
  · subst hr2; convert h2_mem using 1
  · exact hodd r hr hrp (by have := hr.two_le; omega) hr0

open Classical in
/-- **Inductive bootstrap for SE**: if MC holds for all primes below p
    and PrimeResidueEscape holds, then SubgroupEscape holds at p.

    Proof: each prime r ∈ [3, p) appears as seq(k) for some k ≥ 1
    (by mc_below, noting seq(0) = 2 ≠ r since r ≥ 3). Then
    multZ(p, k−1) = seq(k) mod p = r mod p.  PrimeResidueEscape gives
    an r outside any given proper subgroup H, so H is escaped. -/
theorem mc_below_pre_implies_se (hpre : PrimeResidueEscape)
    {p : Nat} [inst : Fact (Nat.Prime p)] (hp : IsPrime p) (hne : ∀ k, seq k ≠ p)
    (hmc : mc_below p) :
    ∀ H : Subgroup (ZMod p)ˣ, H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ p n) (multZ_ne_zero hp hne n)) ∉ H := by
  intro H hH
  -- p ≥ 5 since p is prime, p ≠ 2 (= seq 0), p ≠ 3 (= seq 1)
  have hp5 : 5 ≤ p := by
    have hp2 := (Fact.out : Nat.Prime p).two_le
    by_contra h; push_neg at h
    interval_cases p
    · exact absurd seq_zero (hne 0)
    · exact absurd seq_one (hne 1)
    · exact absurd (Fact.out : Nat.Prime 4) (by decide)
  obtain ⟨r, hr_prime, hrp, hr3, hr_notin⟩ := hpre p hp5 H hH
  obtain ⟨k, hk⟩ := hmc r hr_prime hrp
  -- k ≥ 1 since seq(0) = 2 and r ≥ 3
  have hk1 : k ≥ 1 := by
    rcases k with _ | k
    · simp only [seq_zero] at hk; omega
    · omega
  refine ⟨k - 1, ?_⟩
  have hmult_eq : multZ p (k - 1) = ((r : Nat) : ZMod p) := by
    unfold multZ
    congr 1
    exact_mod_cast (show (k - 1) + 1 = k from Nat.sub_add_cancel hk1) ▸ hk
  rw [show Units.mk0 (multZ p (k - 1)) (multZ_ne_zero hp hne (k - 1)) =
    Units.mk0 ((r : Nat) : ZMod p) (natCast_prime_ne_zero hr_prime hrp) from
    Units.ext hmult_eq]
  exact hr_notin

end InductiveBootstrap

/-! ## §12. Minimality Sieve

The Euclid-Mullin sequence uses **minFac** (the smallest prime factor) at each step,
not just any prime factor. This creates strong constraints: at step n, every prime
r < seq(n+1) must have walkZ(r,n) ≠ -1, since otherwise r would divide prod(n)+1
and being smaller than minFac(prod(n)+1) would contradict minimality.

This "minimality sieve" couples the walks mod different primes: at each step,
the hitting condition (walkZ = -1) is satisfied by exactly one prime (the new term),
while all smaller primes are simultaneously forced away from -1. -/

section MinimalitySieve

/-- **Minimality Sieve**: Every prime smaller than seq(n+1) avoids -1 in the walk.

    Since seq(n+1) = minFac(prod(n)+1), any prime r < seq(n+1) that divided
    prod(n)+1 would satisfy minFac(prod(n)+1) ≤ r < seq(n+1) = minFac(prod(n)+1),
    a contradiction. Therefore walkZ(r,n) ≠ -1. -/
theorem minimality_sieve {n : Nat} {r : Nat} (hr : Nat.Prime r)
    (hr_small : r < seq (n + 1)) :
    walkZ r n ≠ -1 := by
  intro h
  rw [walkZ_eq_neg_one_iff] at h
  have hge : 2 ≤ prod n + 1 := by have := prod_ge_two n; omega
  have hle : minFac (prod n + 1) ≤ r := minFac_min' _ _ hge hr.two_le h
  rw [seq_succ] at hr_small
  omega

/-- The walk hits -1 at the next sequence term: walkZ(seq(n+1), n) = -1.

    This is because seq(n+1) = minFac(prod(n)+1) divides prod(n)+1. -/
theorem walkZ_hit_at_seq_succ (n : Nat) :
    walkZ (seq (n + 1)) n = -1 := by
  rw [walkZ_eq_neg_one_iff, seq_succ]
  exact minFac_dvd _ (by have := prod_ge_two n; omega)

/-- Walk nonzero for missing primes: if a prime r never appears in the EM sequence,
    then walkZ(r,n) ≠ 0 for all n. -/
theorem walkZ_ne_zero_of_not_in_seq {r : Nat} (hr : IsPrime r)
    (hne : ∀ m, seq m ≠ r) (n : Nat) : walkZ r n ≠ 0 := by
  unfold walkZ
  intro h
  have : r ∣ prod n := by rwa [ZMod.natCast_eq_zero_iff] at h
  exact prime_not_in_seq_not_dvd_prod hr hne n this

/-- For primes not in the EM sequence and below seq(n+1), the walk position is
    a unit: it is neither 0 nor -1 in ZMod r. -/
theorem walkZ_unit_of_small_missing {n : Nat} {r : Nat} (hr : Nat.Prime r)
    (hne : ∀ m, seq m ≠ r) (hr_small : r < seq (n + 1)) :
    walkZ r n ≠ 0 ∧ walkZ r n ≠ -1 :=
  ⟨walkZ_ne_zero_of_not_in_seq hr.toIsPrime hne n, minimality_sieve hr hr_small⟩

/-- **Minimality captures target** (walkZ formulation): if walkZ(q,n) = -1 and all
    primes below q already appear in the sequence by step n, then seq(n+1) = q. -/
theorem minimality_captures {q n : Nat} (hq : IsPrime q)
    (hwalk : walkZ q n = -1)
    (hall : ∀ p, p < q → IsPrime p → ∃ m, m ≤ n ∧ seq m = p) :
    seq (n + 1) = q :=
  captures_target hq ((walkZ_eq_neg_one_iff n).mp hwalk) hall

/-- **Cross-prime walk constraint**: at every step n of the EM sequence,
    seq(n+1) is the UNIQUE prime hitting -1 among all primes up to seq(n+1).

    More precisely: walkZ(seq(n+1), n) = -1 (hitting), and for every
    prime r < seq(n+1), walkZ(r, n) ≠ -1 (sieve exclusion). -/
theorem cross_prime_constraint (n : Nat) :
    walkZ (seq (n + 1)) n = -1 ∧
    ∀ r, Nat.Prime r → r < seq (n + 1) → walkZ r n ≠ -1 :=
  ⟨walkZ_hit_at_seq_succ n, fun _ hr hrs => minimality_sieve hr hrs⟩

/-- **Minimality + confinement coupling**: if the walk mod q is confined
    (all multipliers lie in a proper subgroup H), then the minimality sieve
    simultaneously constrains all small primes. At each step n:
    - The multiplier at step n lies in H (confinement at q)
    - Every prime r < seq(n+1) avoids -1 in its own walk (minimality)

    This cross-modulus coupling is the key constraint that minFac provides:
    confinement at q forces a structured walk, while minimality forces
    all smaller primes away from -1 simultaneously. -/
theorem minimality_confinement_coupling
    {q : Nat} [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ m, seq m ≠ q)
    (H : Subgroup (ZMod q)ˣ)
    (hconf : ∀ k, (Units.mk0 (multZ q k) (multZ_ne_zero hq hne k)) ∈ H)
    (n : Nat) :
    (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∈ H ∧
    (∀ r, Nat.Prime r → r < seq (n + 1) → walkZ r n ≠ -1) :=
  ⟨hconf n, fun _ hr hrs => minimality_sieve hr hrs⟩

end MinimalitySieve

/-! ## §13. The Irreducible Core: One Hypothesis Suffices

The inductive bootstrap (§11) shows MC(< p) + PrimeResidueEscape → SE(p).
This means SubgroupEscape is "free" once MC holds for smaller primes.

Combined with a dynamical hypothesis — that SE at q implies the walk hits -1 —
we get a single-hypothesis reduction of Mullin's Conjecture. The hypothesis,
`DynamicalHitting`, is equivalent to `MixingHypothesis` but is stated in SE
form rather than closure form.

The comparison:
- **Old**: SE (global, open) + MH (open) → MC
- **New**: DynamicalHitting (open) → MC

PrimeResidueEscape is proved elementarily (no Burgess needed), so the sole
remaining open hypothesis is DynamicalHitting. The algebraic component (SE)
is derived automatically from the induction at each step. -/

section IrreducibleCore

/-- **Dynamical Hitting Hypothesis**: if SubgroupEscape holds at q (all
    multiplier residues escape every proper subgroup of (ZMod q)ˣ), then
    the walk hits -1 cofinally (HittingHypothesis at q).

    This is the irreducible dynamical core of Mullin's Conjecture: the
    algebraic condition (generation) implies the analytical condition (hitting).

    Equivalent to `MixingHypothesis` via `se_implies_full_generation`. -/
def DynamicalHitting : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H) →
    ∀ N, ∃ n, N ≤ n ∧ q ∣ (prod n + 1)

/-- MixingHypothesis implies DynamicalHitting.

    MH takes "closure = ⊤" as antecedent; DH takes the equivalent "SE at q".
    The conversion uses: SE at q → closure = ⊤ (by contradiction: if closure
    is proper, SE escapes it, but every mult is in the closure). -/
theorem mixing_implies_dynamical_hitting (hmh : MixingHypothesis) :
    DynamicalHitting := by
  intro q _ hq hne hse N
  -- Convert local SE to full generation
  have hfull : Subgroup.closure
      (Set.range (fun n => Units.mk0 (multZ q n) (multZ_ne_zero hq hne n))) = ⊤ := by
    by_contra h
    obtain ⟨n, hn⟩ := hse (Subgroup.closure _) h
    exact hn (Subgroup.subset_closure ⟨n, rfl⟩)
  -- Apply MH
  obtain ⟨n, hn, hw⟩ := hmh q hq hne hfull N
  exact ⟨n, hn, (walkZ_eq_neg_one_iff n).mp hw⟩

/-- DynamicalHitting implies MixingHypothesis.

    DH takes "SE at q" as antecedent; MH takes "closure = ⊤".
    The conversion uses: closure = ⊤ → SE at q (by contradiction: if all
    mults are in H, then closure ≤ H < ⊤, contradicting closure = ⊤). -/
theorem dynamical_hitting_implies_mixing (hdh : DynamicalHitting) :
    MixingHypothesis := by
  intro q _ hq hne hfull N
  -- Convert full generation to local SE
  have hse : ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H := by
    intro H hH
    by_contra hall
    push_neg at hall
    -- All generators are in H, so closure ≤ H
    have hle : Subgroup.closure
        (Set.range (fun n => Units.mk0 (multZ q n) (multZ_ne_zero hq hne n))) ≤ H := by
      rw [Subgroup.closure_le]
      intro x ⟨n, hn⟩
      exact hn ▸ hall n
    exact hH (top_le_iff.mp (hfull ▸ hle))
  -- Apply DH
  obtain ⟨n, hn, hdvd⟩ := hdh q hq hne hse N
  exact ⟨n, hn, (walkZ_eq_neg_one_iff n).mpr hdvd⟩

open Classical in
/-- **The one-hypothesis reduction**: DynamicalHitting + PrimeResidueEscape
    imply Mullin's Conjecture, by strong induction on p.

    At each prime p: the induction hypothesis gives MC(< p), the inductive
    bootstrap (`mc_below_pre_implies_se`) gives SE(p) from PrimeResidueEscape,
    and DynamicalHitting gives HH(p). Then `captures_target` turns the
    hitting event into seq(n+1) = p.

    This eliminates SubgroupEscape from the hypothesis list entirely.
    Since PrimeResidueEscape is proved (`prime_residue_escape`), see
    `dynamical_hitting_implies_mullin` for the clean one-hypothesis version. -/
theorem dynamical_hitting_pre_implies_mullin
    (hdh : DynamicalHitting) (hpre : PrimeResidueEscape) :
    MullinConjecture := by
  unfold MullinConjecture
  suffices ∀ k q, q ≤ k → IsPrime q → ∃ n, seq n = q by
    intro q hq; exact this q q (Nat.le_refl q) hq
  intro k
  induction k with
  | zero => intro q hle hq; exact absurd hq.1 (by omega)
  | succ k ih =>
    intro q hle hq
    match Nat.lt_or_ge q (k + 1) with
    | .inl hlt => exact ih q (by omega) hq
    | .inr _ =>
      by_contra hnotexists
      have hne : ∀ m, seq m ≠ q := fun m heq => hnotexists ⟨m, heq⟩
      -- IH gives MC(< q)
      have hmc : mc_below q := fun r hr hrq => ih r (by omega) hr.toIsPrime
      -- Bootstrap: MC(< q) + PrimeResidueEscape → SE(q)
      haveI : Fact (Nat.Prime q) := ⟨IsPrime.toNatPrime hq⟩
      have hse := mc_below_pre_implies_se hpre hq hne hmc
      -- DynamicalHitting: SE(q) → HH(q)
      obtain ⟨N, hN⟩ := exists_bound q (fun p hpq hp => ih p (by omega) hp)
      obtain ⟨n, hn_ge, hn_dvd⟩ := hdh q hq hne hse N
      -- All primes < q appeared by step n
      have hall : ∀ p, p < q → IsPrime p → ∃ m, m ≤ n ∧ seq m = p := by
        intro p hpq hp
        obtain ⟨m, hm, hseqm⟩ := hN p hpq hp
        exact ⟨m, by omega, hseqm⟩
      -- captures_target: seq(n+1) = q, contradicting q ∉ seq
      exact hnotexists ⟨n + 1, captures_target hq hn_dvd hall⟩

/-- **The one-hypothesis theorem**: DynamicalHitting alone implies Mullin's
    Conjecture. PrimeResidueEscape is proved elementarily (no Burgess needed),
    so the sole remaining open hypothesis is DynamicalHitting. -/
theorem dynamical_hitting_implies_mullin (hdh : DynamicalHitting) :
    MullinConjecture :=
  dynamical_hitting_pre_implies_mullin hdh prime_residue_escape

end IrreducibleCore

/-! ## §13b. The Single Hit Theorem

The weakest hitting condition in the "hitting family" that suffices for MC:
`SingleHitHypothesis` asks for a single hit on -1 past the sieve gap,
with `mc_below q` as an additional hypothesis.

Comparison with the two neighbouring hypotheses:
- **DynamicalHitting**: SE(q) → ∀ N, ∃ n ≥ N, q ∣ prod(n)+1.
  Cofinal hitting, does NOT require mc_below q.
- **SingleHitHypothesis**: mc_below(q) → SE(q) →
  ∀ N₀ with sieve-gap property, ∃ n ≥ N₀, q ∣ prod(n)+1.
  Single hit past the sieve gap; requires mc_below q (available from induction).
- **HittingHypothesis**: hne → ∀ N, ∃ n ≥ N, q ∣ prod(n)+1.
  Cofinal hitting; neither SE nor mc_below; strongest but hardest to verify.

SHH is strictly weaker than DH in two ways: (1) it assumes mc_below q,
(2) it asks for one hit past a specific bound rather than cofinal hitting.
Both extras are harmless in the inductive proof but make SHH genuinely
weaker as a standalone mathematical statement. -/

section SingleHit

/-- **Single Hit Hypothesis**: for every missing prime q, if MC(< q) holds
    and SubgroupEscape holds at q, then there is at least one hit on -1
    past the sieve gap (the point where all primes < q have appeared).

    This is strictly weaker than DynamicalHitting in two ways:
    (1) SHH assumes MC(< q), which DH does not.
    (2) SHH asks for one hit past a specific bound, while DH asks for
        cofinal hitting (infinitely many hits past any bound).
    Both extras are harmless in the inductive proof but make SHH
    genuinely weaker as a standalone mathematical statement. -/
def SingleHitHypothesis : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    mc_below q →
    (∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ n, (Units.mk0 (multZ q n) (multZ_ne_zero hq hne n)) ∉ H) →
    ∀ (N₀ : Nat), (∀ p, p < q → IsPrime p → ∃ m, m ≤ N₀ ∧ seq m = p) →
      ∃ n, N₀ ≤ n ∧ q ∣ (prod n + 1)

/-- **DH implies SingleHitHypothesis**: DynamicalHitting is strictly stronger
    because it does not require mc_below q and gives cofinal hitting. -/
theorem dh_implies_single_hit (hdh : DynamicalHitting) : SingleHitHypothesis := by
  intro q _ hq hne _hmc hse N₀ _hN₀
  exact hdh q hq hne hse N₀

/-- **HH implies SingleHitHypothesis**: HittingHypothesis does not need SE
    or mc_below at all, so it trivially implies SingleHitHypothesis. -/
theorem hh_implies_single_hit (hhh : HittingHypothesis) : SingleHitHypothesis := by
  intro q _ hq hne _hmc _hse N₀ _hN₀
  exact hhh q hq hne N₀

open Classical in
/-- **The Single Hit Theorem**: SingleHitHypothesis + PrimeResidueEscape
    imply Mullin's Conjecture, by strong induction on p.

    At each prime p: the induction hypothesis gives mc_below p, the
    bootstrap gives SE(p) from PRE, and SingleHitHypothesis gives a
    hit past the sieve gap. captures_target finishes. -/
theorem single_hit_pre_implies_mullin
    (hsh : SingleHitHypothesis) (hpre : PrimeResidueEscape) :
    MullinConjecture := by
  unfold MullinConjecture
  suffices ∀ k q, q ≤ k → IsPrime q → ∃ n, seq n = q by
    intro q hq; exact this q q (Nat.le_refl q) hq
  intro k
  induction k with
  | zero => intro q hle hq; exact absurd hq.1 (by omega)
  | succ k ih =>
    intro q hle hq
    match Nat.lt_or_ge q (k + 1) with
    | .inl hlt => exact ih q (by omega) hq
    | .inr _ =>
      by_contra hnotexists
      have hne : ∀ m, seq m ≠ q := fun m heq => hnotexists ⟨m, heq⟩
      -- IH gives MC(< q)
      have hmc : mc_below q := fun r hr hrq => ih r (by omega) hr.toIsPrime
      -- Bootstrap: MC(< q) + PrimeResidueEscape → SE(q)
      haveI : Fact (Nat.Prime q) := ⟨IsPrime.toNatPrime hq⟩
      have hse := mc_below_pre_implies_se hpre hq hne hmc
      -- exists_bound: uniform bound N₀ such that all primes < q appear by N₀
      obtain ⟨N, hN⟩ := exists_bound q (fun p hpq hp => ih p (by omega) hp)
      -- SingleHitHypothesis: MC(< q) + SE(q) + sieve gap → ∃ n ≥ N, q ∣ prod n + 1
      obtain ⟨n, hn_ge, hn_dvd⟩ := hsh q hq hne hmc hse N hN
      -- All primes < q appeared by step n (since n ≥ N)
      have hall : ∀ p, p < q → IsPrime p → ∃ m, m ≤ n ∧ seq m = p := by
        intro p hpq hp
        obtain ⟨m, hm, hseqm⟩ := hN p hpq hp
        exact ⟨m, by omega, hseqm⟩
      -- captures_target: seq(n+1) = q, contradicting q ∉ seq
      exact hnotexists ⟨n + 1, captures_target hq hn_dvd hall⟩

/-- **The Single Hit Theorem (clean version)**: SingleHitHypothesis alone
    implies Mullin's Conjecture. PrimeResidueEscape is proved elementarily. -/
theorem single_hit_implies_mc (hsh : SingleHitHypothesis) :
    MullinConjecture :=
  single_hit_pre_implies_mullin hsh prime_residue_escape

/-- DH → MC factors through SingleHitHypothesis:
    DH → SingleHitHypothesis → MC. -/
theorem dh_mc_via_single_hit (hdh : DynamicalHitting) : MullinConjecture :=
  single_hit_implies_mc (dh_implies_single_hit hdh)

end SingleHit

/-! ## First Passage Structure

The walk mod q has a binary structure: it hits -1 at most once (in a
meaningful way). After the prime q enters the sequence at step k
(i.e., seq(k) = q), the product prod(m) for all m >= k is divisible by q,
so walkZ(q,m) = 0 for all m >= k. In particular, walkZ(q,m) != -1 for
q >= 3, since 0 != -1 in ZMod q.

This means the walk mod q has two phases:
1. **Pre-entry**: q is not yet in the sequence. walkZ(q,n) != 0 for all n.
   The walk can hit -1 (triggering q's entry) or stay away.
2. **Post-entry**: q = seq(k). walkZ(q,m) = 0 for all m >= k.
   The walk is dead — collapsed to zero forever.

The transition from phase 1 to phase 2 is irreversible: once q enters,
it divides all subsequent products. -/

section FirstPassage

/-- If q divides prod(n), then walkZ(q,n) = 0. This is the basic cast lemma. -/
theorem walkZ_eq_zero_of_dvd {q : Nat} {n : Nat} (h : q ∣ prod n) :
    walkZ q n = 0 := by
  simp only [walkZ]
  rwa [ZMod.natCast_eq_zero_iff]

/-- After a prime enters the sequence, the walk collapses to zero.
    If seq(k) = q and k <= m, then q | prod(m), so walkZ(q,m) = 0. -/
theorem walkZ_zero_after_entry {q : Nat} {k m : Nat}
    (hseq : seq k = q) (hle : k ≤ m) :
    walkZ q m = 0 := by
  apply walkZ_eq_zero_of_dvd
  rw [← hseq]
  exact seq_dvd_prod k m hle

/-- After entry, the walk never hits -1 again (for q >= 3).
    Since walkZ(q,m) = 0 and 0 != -1 in ZMod q for q >= 3,
    the walk can never hit -1 after q enters the sequence. -/
theorem walkZ_ne_neg_one_after_entry {q : Nat} [Fact (Nat.Prime q)]
    {k m : Nat} (hseq : seq k = q) (hle : k ≤ m) (hq3 : q ≥ 3) :
    walkZ q m ≠ -1 := by
  rw [walkZ_zero_after_entry hseq hle]
  exact neg_one_ne_zero_of_prime_ge_three hq3 |>.symm

/-- At the capture step itself: walkZ(seq(n+1), n) = -1 (the walk hits -1),
    and then walkZ(seq(n+1), m) = 0 for all m >= n+1.
    This combines `walkZ_hit_at_seq_succ` with `walkZ_zero_after_entry`. -/
theorem walkZ_capture_then_collapse {n m : Nat} (hm : n + 1 ≤ m) :
    walkZ (seq (n + 1)) n = -1 ∧ walkZ (seq (n + 1)) m = 0 :=
  ⟨walkZ_hit_at_seq_succ n, walkZ_zero_after_entry rfl hm⟩

/-- The walk mod q cannot hit -1 at two distinct times that are both
    followed by capture. If walkZ(q,n) = -1 and seq(n+1) = q, then
    for any m > n, walkZ(q,m) != -1. -/
theorem at_most_one_capture {q : Nat} [Fact (Nat.Prime q)]
    {n m : Nat} (hseq : seq (n + 1) = q) (hm : n < m) (hq3 : q ≥ 3) :
    walkZ q m ≠ -1 :=
  walkZ_ne_neg_one_after_entry hseq (by omega) hq3

/-- No prime can be captured twice in the sequence.
    This is immediate from seq being injective.
    If seq(j) = q and seq(k) = q, then j = k. -/
theorem seq_entry_unique {q : Nat} {j k : Nat}
    (hj : seq j = q) (hk : seq k = q) : j = k :=
  seq_injective j k (hj.trans hk.symm)

/-- **First-passage decomposition**: for any prime q >= 3, exactly one of
    two cases holds:
    1. q never appears in the sequence (walkZ(q,n) != 0 for all n), or
    2. q = seq(k) for a unique k, and walkZ(q,m) = 0 for all m >= k.

    This is the "binary structure" of the walk mod q. -/
theorem first_passage_dichotomy (q : Nat) (_hq : IsPrime q) :
    (∀ n, seq n ≠ q) ∨ (∃! k, seq k = q) := by
  by_cases h : ∃ k, seq k = q
  · obtain ⟨k, hk⟩ := h
    right
    exact ⟨k, hk, fun k' hk' => seq_entry_unique hk' hk⟩
  · left
    push_neg at h
    exact h

/-- In the "never appears" case, walkZ(q,n) is always nonzero. -/
theorem walkZ_always_nonzero_of_missing (q : Nat) (hq : IsPrime q)
    (hmiss : ∀ n, seq n ≠ q) (n : Nat) :
    walkZ q n ≠ 0 :=
  walkZ_ne_zero_of_not_in_seq hq hmiss n

/-- In the "appears once" case, walkZ(q,m) = 0 from the entry point onward. -/
theorem walkZ_zero_from_entry (q : Nat) {k : Nat}
    (hentry : seq k = q) (m : Nat) (hm : k ≤ m) :
    walkZ q m = 0 :=
  walkZ_zero_after_entry hentry hm

end FirstPassage
