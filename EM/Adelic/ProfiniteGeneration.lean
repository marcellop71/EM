import EM.Equidist.Bootstrap

/-!
# Profinite Generation: EM Multipliers Generate (ZMod N)x

For any modulus N > 1, the prime residues below N generate the full
unit group (ZMod N)x. Combined with MCBelow, this shows the EM
multiplier subgroup equals (ZMod N)x at every composite modulus.

## Main results

* `primeUnitsBelow_generate` -- primes < N generate (ZMod N)x (pure NT)
* `mc_below_implies_full_generation` -- MCBelow N => EM multipliers generate (ZMod N)x
* `mc_implies_full_generation` -- full MC => EM multipliers generate (ZMod N)x for all N
-/

open Mullin Euclid MullinGroup RotorRouter
open Classical

/-! ## Part 1: ZMod helpers for composite modulus -/

/-- The ZMod.val of a unit of ZMod N is positive (for N > 1). -/
private theorem val_unit_pos' {N : Nat} (hN : 1 < N) (u : (ZMod N)ˣ) :
    0 < ZMod.val (u : ZMod N) := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (1 < N) := ⟨hN⟩
  rw [Nat.pos_iff_ne_zero]
  intro h
  exact u.ne_zero ((ZMod.val_eq_zero (u : ZMod N)).mp h)

/-! ## Part 2: Primes below N generate (ZMod N)x -/

/-- The set of "prime units below N": units of (ZMod N) coming from primes < N
    that are coprime to N. -/
def primeUnitsBelow (N : Nat) : Set (ZMod N)ˣ :=
  {u | ∃ p : Nat, p.Prime ∧ p < N ∧
    ∃ (hcop : Nat.Coprime p N), ZMod.unitOfCoprime p hcop = u}

/-- If every prime r < N that is coprime to N maps into a subgroup H,
    then every unit m in [1, N) with gcd(m,N) = 1 maps into H.
    Proof by strong induction on m. -/
private theorem unit_mem_of_all_coprime_primes_mem {N : Nat}
    (H : Subgroup (ZMod N)ˣ)
    (hp : ∀ r, Nat.Prime r → r < N → (hcop : Nat.Coprime r N) →
      ZMod.unitOfCoprime r hcop ∈ H)
    (m : Nat) (hm1 : 1 <= m) (hmN : m < N) (hcop : Nat.Coprime m N) :
    ZMod.unitOfCoprime m hcop ∈ H := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases hm_one : m = 1
    · -- m = 1: unitOfCoprime 1 _ = 1
      subst hm_one
      convert H.one_mem using 1
      apply Units.ext
      simp [ZMod.coe_unitOfCoprime]
    · by_cases hprime : Nat.Prime m
      · exact hp m hprime hmN hcop
      · -- m is composite: factor via minFac
        have hfp : (Nat.minFac m).Prime := Nat.minFac_prime hm_one
        have hfd : Nat.minFac m ∣ m := Nat.minFac_dvd m
        have hfne : Nat.minFac m ≠ m := fun h => hprime (h ▸ hfp)
        have hflt : Nat.minFac m < m :=
          lt_of_le_of_ne (Nat.minFac_le (by omega)) hfne
        set a := Nat.minFac m with ha_def
        set b := m / a with hb_def
        have hab : a * b = m := Nat.mul_div_cancel' hfd
        have hb1 : 1 <= b := by
          rw [Nat.one_le_iff_ne_zero]; intro hb0
          rw [hb0, Nat.mul_zero] at hab; omega
        have hblt : b < m := Nat.div_lt_self (by omega) hfp.one_lt
        have hap : a < N := lt_trans hflt hmN
        have hbp : b < N := lt_trans hblt hmN
        -- Key: coprimality propagates through factors
        have ha_cop : Nat.Coprime a N := hcop.coprime_dvd_left hfd
        have hb_dvd : b ∣ m := ⟨a, by rw [mul_comm]; exact hab.symm⟩
        have hb_cop : Nat.Coprime b N := hcop.coprime_dvd_left hb_dvd
        have ha_mem := hp a hfp hap ha_cop
        have hb_mem := ih b hblt hb1 hbp hb_cop
        -- m = a * b, so unitOfCoprime m = unitOfCoprime a * unitOfCoprime b
        have heq : ZMod.unitOfCoprime m hcop =
            ZMod.unitOfCoprime a ha_cop *
            ZMod.unitOfCoprime b hb_cop := by
          apply Units.ext
          simp only [ZMod.coe_unitOfCoprime, Units.val_mul]
          push_cast [← hab]
          ring
        rw [heq]; exact H.mul_mem ha_mem hb_mem

/-- **Every unit of (ZMod N)x is a product of prime units below N.**
    This is a pure number theory result: every integer coprime to N
    factors as a product of primes, all of which are coprime to N. -/
theorem primeUnitsBelow_generate (N : Nat) (hN : 1 < N) :
    Subgroup.closure (primeUnitsBelow N) = ⊤ := by
  haveI : NeZero N := ⟨by omega⟩
  rw [Subgroup.eq_top_iff']
  intro u
  -- The natural representative
  set m := ZMod.val (u : ZMod N) with hm_def
  have hm_lt : m < N := ZMod.val_lt (u : ZMod N)
  have hm_pos : 0 < m := val_unit_pos' hN u
  have hcop : Nat.Coprime m N := ZMod.val_coe_unit_coprime u
  -- Round-trip: casting m back gives u.val
  have hcast : ((m : Nat) : ZMod N) = (u : ZMod N) := by
    rw [hm_def]; exact ZMod.natCast_zmod_val (u : ZMod N)
  -- unitOfCoprime m hcop = u
  have hu_eq : ZMod.unitOfCoprime m hcop = u :=
    Units.ext (by simp only [ZMod.coe_unitOfCoprime]; exact hcast)
  rw [← hu_eq]
  -- Show every coprime prime < N maps into closure(primeUnitsBelow N)
  apply unit_mem_of_all_coprime_primes_mem
  · intro r hr hrN hrcop
    apply Subgroup.subset_closure
    show ZMod.unitOfCoprime r hrcop ∈ primeUnitsBelow N
    exact ⟨r, hr, hrN, hrcop, rfl⟩
  · omega
  · exact hm_lt

/-! ## Part 3: Application to the Euclid-Mullin sequence -/

/-- The set of EM multiplier residues mod N: units coming from sequence terms. -/
def emMultiplierUnits (N : Nat) : Set (ZMod N)ˣ :=
  {u | ∃ k, ∃ (hcop : Nat.Coprime (seq k) N),
    ZMod.unitOfCoprime (seq k) hcop = u}

/-- Under MCBelow N, every prime < N coprime to N is in emMultiplierUnits N. -/
private theorem primeUnitsBelow_subset_emMultiplierUnits {N : Nat}
    (hMC : MCBelow N) : primeUnitsBelow N ⊆ emMultiplierUnits N := by
  intro u ⟨p, hp, hpN, hcop, hu⟩
  obtain ⟨k, hk⟩ := hMC p hp hpN
  -- seq k = p, so unitOfCoprime (seq k) = unitOfCoprime p
  have hcop' : Nat.Coprime (seq k) N := by rwa [hk]
  refine ⟨k, hcop', ?_⟩
  -- Need: unitOfCoprime (seq k) hcop' = u
  -- We know: unitOfCoprime p hcop = u and seq k = p
  have : ZMod.unitOfCoprime (seq k) hcop' = ZMod.unitOfCoprime p hcop := by
    apply Units.ext
    simp only [ZMod.coe_unitOfCoprime, hk]
  rw [this]; exact hu

/-- **Under MC(< N), the EM multiplier units generate the full group (ZMod N)x.**

    Proof: MCBelow gives every prime < N as some seq k. These primes
    generate (ZMod N)x by `primeUnitsBelow_generate`. Since primeUnitsBelow
    is contained in emMultiplierUnits under MCBelow, the result follows. -/
theorem mc_below_implies_full_generation (N : Nat) (hN : 1 < N)
    (hMC : MCBelow N) :
    Subgroup.closure (emMultiplierUnits N) = ⊤ := by
  -- primeUnitsBelow N ⊆ emMultiplierUnits N under MCBelow
  have hsub := primeUnitsBelow_subset_emMultiplierUnits hMC
  -- closure(primeUnitsBelow N) ≤ closure(emMultiplierUnits N)
  have hmono := Subgroup.closure_mono hsub
  -- closure(primeUnitsBelow N) = ⊤
  have htop := primeUnitsBelow_generate N hN
  -- Therefore closure(emMultiplierUnits N) = ⊤
  exact top_le_iff.mp (htop ▸ hmono)

/-- **Under full MC, the EM multiplier units generate (ZMod N)x for every N > 1.** -/
theorem mc_implies_full_generation (hMC : MullinConjecture) (N : Nat) (hN : 1 < N) :
    Subgroup.closure (emMultiplierUnits N) = ⊤ := by
  apply mc_below_implies_full_generation N hN
  -- Bridge: MullinConjecture (uses IsPrime) → MCBelow (uses Nat.Prime)
  intro r hr hrN
  exact hMC r hr.toIsPrime

/-! ## Part 4: Landscape -/

/-- **Profinite Generation Landscape.**
    1. Every unit mod N is a product of primes < N (pure number theory)
    2. Under MC(< N), the EM multipliers include all primes < N
    3. Therefore, the multiplier subgroup = full group
    4. Generation => equidistribution is OPEN (= DSL, cf. Dead End #130) -/
theorem profinite_generation_landscape :
    (∀ N, 1 < N → Subgroup.closure (primeUnitsBelow N) = ⊤) ∧
    (MullinConjecture → ∀ N, 1 < N → Subgroup.closure (emMultiplierUnits N) = ⊤) ∧
    True :=
  ⟨primeUnitsBelow_generate, mc_implies_full_generation, trivial⟩
