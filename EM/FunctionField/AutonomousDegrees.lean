import EM.FunctionField.CharTwo

/-!
# Degree constraints after autonomous steps

The `Φ₃` exclusion of `AutonomousMap.lean` says that, under perpetual irreducibility and for
`p ≡ 2 (mod 3)`, no *linear* irreducible can be captured.  The Frobenius-orbit method gives the
full statement, unconditionally and for a single autonomous step:

* **Even degrees** (`p ≡ 2 (mod 3)`, so `p = 2, 5, 11, …`): if the Euclid polynomial `E_n` is
  irreducible, then every irreducible factor of `E_{n+1} = Φ₃(P_n)` has even degree
  (`FrobeniusOrbit.even_natDegree_of_dvd_phi3`); in particular the next selected factor
  `ffSeq (n+2)` has even degree (`ffSeq_natDegree_even_of_irreducible`).  Reason: a root `β` of
  such a factor has `P_n(β) = ω` a primitive cube root of unity, whose Frobenius period is `2`,
  and periods of `P_n(β)` divide the degree of `β`.
* **Degrees divisible by 4** (`p = 2`): after two consecutive irreducible stages,
  `E_{n+2} = P_n⁴ + P_n + 1`, and a root `y` of `y⁴ + y + 1` has period `4`; so every irreducible
  factor of `E_{n+2}` has degree divisible by `4` (`four_dvd_natDegree_of_two_irreducible`).

Over `𝔽_5` with the seed `X` every stage is autonomous, so the selected degrees are the powers
of two seen in `StableTower.lean`; over `𝔽_2` autonomous runs have length at most three
(`CompositeFloors.lean`), so these constraints bite only briefly — the mechanism, not the
conclusion, is the point.
-/

namespace FunctionFieldAnalog

namespace AutonomousDegrees

open Polynomial FrobeniusOrbit CompositeFloors FunctionFieldAnalog.CharTwo

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- After an irreducible stage the Euclid polynomial is `Φ₃(P_n) = P_n² + P_n + 1`. -/
theorem euclid_succ_eq_phi3 (d : FFEMData p) (n : ℕ) (h : Irreducible (d.ffProd n + 1)) :
    d.ffProd (n + 1) + 1 = d.ffProd n ^ 2 + d.ffProd n + 1 := by
  rw [ffProd_succ_of_irreducible d n h]; ring

/-- **Even-degree exclusion for one autonomous step**, `p ≡ 2 (mod 3)`: every irreducible factor
of the Euclid polynomial following an irreducible one has even degree. -/
theorem even_natDegree_of_dvd_euclid_succ (hp3 : p % 3 = 2) (d : FFEMData p) (n : ℕ)
    (h : Irreducible (d.ffProd n + 1)) {f : (ZMod p)[X]} (hf : Irreducible f)
    (hdvd : f ∣ d.ffProd (n + 1) + 1) : Even f.natDegree := by
  rw [euclid_succ_eq_phi3 d n h] at hdvd
  exact even_natDegree_of_dvd_phi3 p hp3 hf hdvd

/-- The selected factor after an irreducible stage has even degree (`p ≡ 2 (mod 3)`). -/
theorem ffSeq_natDegree_even_of_irreducible (hp3 : p % 3 = 2) (d : FFEMData p) (n : ℕ)
    (h : Irreducible (d.ffProd n + 1)) : Even (d.ffSeq (n + 2)).natDegree := by
  obtain ⟨_, hirr, hdvd⟩ := d.ffSeq_succ (n + 1)
  exact even_natDegree_of_dvd_euclid_succ hp3 d n h hirr hdvd

/-- Over `𝔽_2`, after two irreducible stages every irreducible factor of the next Euclid
polynomial `P⁴ + P + 1` has degree divisible by `4`. -/
theorem four_dvd_natDegree_of_two_irreducible (d : FFEMData 2) (n : ℕ)
    (h0 : Irreducible (d.ffProd n + 1)) (h1 : Irreducible (d.ffProd (n + 1) + 1))
    {f : (ZMod 2)[X]} (hf : Irreducible f) (hdvd : f ∣ d.ffProd (n + 2) + 1) :
    4 ∣ f.natDegree := by
  rw [ffProd_add_two_of_two_irreducible d n h0 h1] at hdvd
  obtain ⟨β, hβ⟩ := exists_aeval_eq_zero 2 hf
  obtain ⟨g, hg⟩ := hdvd
  have hy : (aeval β (d.ffProd n)) ^ 4 + aeval β (d.ffProd n) + 1 = 0 := by
    have := congrArg (aeval β) hg
    rwa [map_mul, hβ, zero_mul, map_add, map_add, map_pow, map_one] at this
  rw [← quartic_root_minimalPeriod hy]
  exact minimalPeriod_aeval_dvd_natDegree 2 hf hβ _

theorem four_dvd_ffSeq_natDegree_of_two_irreducible (d : FFEMData 2) (n : ℕ)
    (h0 : Irreducible (d.ffProd n + 1)) (h1 : Irreducible (d.ffProd (n + 1) + 1)) :
    4 ∣ (d.ffSeq (n + 3)).natDegree := by
  obtain ⟨_, hirr, hdvd⟩ := d.ffSeq_succ (n + 2)
  exact four_dvd_natDegree_of_two_irreducible d n h0 h1 hirr hdvd

end AutonomousDegrees

end FunctionFieldAnalog
