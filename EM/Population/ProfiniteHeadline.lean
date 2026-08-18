import EM.Population.ProfiniteEnsemble
import EM.Population.ProfiniteDynamics
import EM.Population.AlmostAllDensity

/-!
# The profinite headline: almost every profinite seed captures every prime

This file transfers the finite counting chain of Sessions 310–312 to the ambient
probability space `(Ω, μ)` of `EM/Population/ProfiniteEnsemble.lean`, where

```
Ω = Π (r : Nat.Primes), ZMod r,   μ = Π (uniform on ZMod r).
```

The greedy Euclid–Mullin dynamics on `Ω` is `ProfiniteDynamics.profSeq`.  The
results are:

* `covering` — for a fixed prime `q` and `ε > 0` there is a finite set `P` of
  primes and a set `T` of residue classes mod `∏_{r ∈ P} r` with
  `#T ≤ (ε/2)·∏_{r ∈ P} r`, containing the reduction of **every** profinite point
  whose `q`-coordinate is nonzero and whose profinite orbit misses `q` in its
  first `n` steps.
* `measure_missing_le` — hence that event has measure at most `ε`;
* `measure_missing_eq_zero` — hence, letting `ε → 0` and `n → ∞`,
  `μ { x : x_q ≠ 0 ∧ the orbit of x never selects q } = 0`;
* `measure_some_prime_missed_eq_zero` — hence, by **countable additivity**,
  `μ { x : ∃ q, x_q ≠ 0 ∧ the orbit of x never selects q } = 0`.

The last step is the whole point of moving to a countably additive measure:
upper natural density is only finitely *sub*additive, so the per-`q` density statements
of `AlmostAllDensity` do **not** combine (this is dead end #168).

## Scope — read this before quoting anything below

* **`ℕ ⊂ Ω` is `μ`-null.**  `ProfiniteEnsemble.measure_range_iota_eq_zero` proves
  it.  So "`μ`-almost every seed" is **not** "almost all integer seeds": a
  `μ`-null set can have upper natural density `1` in `ℕ`, and a `μ`-full set can
  meet `ℕ` in a set of density `0`.  **These are statements about a random
  model**, and no transfer to the integers is claimed or available here.
* **Nothing is said about the orbit of `2`.**  Mullin's Conjecture is not
  approached.  The orbit-specificity obstructions, dead ends **#90** and
  **#117**, are *untouched*: every statement below quantifies over the ensemble,
  and none specializes to a single seed.
* **Mathematically new content: none.**  The mathematics is the already-proved
  finite counting chain `TheoremC.theorem_C → FiberTheoremC.theorem_C_fiber →
  TypeBadSmall.type_bad_small → AlmostAllDensity.uncaptured_in_few_classes`.  The
  passage from "one prime at a time" to "all primes" is *measure-theoretic
  packaging*.  That is a feature — there is no analytic risk in packaging — and
  it must be said, not hidden.  Simultaneity in `q` was never a rate problem; it
  is an additivity problem.
* **Not dead end #101, not #155.**  #101 is the (dead) proposal to house the
  Euler–Mullin *walk* in `Ẑ`, to extract orbit information.  #155 is a
  Loeb-measure receptacle, vacuous because the hyperfinite orbit is null for
  *every* sequence.  Here `Ω` is the *sample space of a population statement*: it
  carries no walk and no orbit claim, and the nullity of `ℕ` is a **declared
  scope limitation**, not a defect that voids the theorem.
* **Unconditional.**  No equidistribution hypothesis occurs anywhere in the
  chain.

## The transfer, in one paragraph

Fix `q` and `ε`.  `AlmostAllDensity`-style counting supplies a horizon `n`, a
truncation `Y ≥ q`, the period `M = ∏ {r ≤ Y : r prime, r ≠ q}` and a set `T` of
residues mod `M` with `#T ≤ (ε/2)M` covering every integer seed that is coprime
to `q` and misses `q` before depth `n`.  Given a profinite `x` with `x_q ≠ 0`
whose orbit misses `q` before depth `n`, lift `x` by CRT to an integer `m'`
agreeing with `x` at **every** prime coordinate `≤ Y`, `q` included.  Then
`¬ q ∣ m'`; and if the *integer* orbit of `m'` selected `q` at some minimal
`j₀ < n`, all of its multipliers up to and including `j₀` would lie in `[2, Y]`
(the earlier ones by the `q`-free coupling and the residue-determinacy of the
`q`-free prefix, the last one because it is `q ≤ Y`), so the band-local agreement
lemma `ProfiniteDynamics.profProd_agree_of_agree` would force
`profSeq x j₀ = q` — contradiction.  Hence `m'` is covered by `T`, and so is `x`.
The hypothesis `q ≤ Y` is load-bearing, and both of its uses are about the prime
`q` itself.  The period `M` deliberately omits `q`, so the lift is taken modulo
the *full* band `fullBand Y` and agrees with `x` at every prime coordinate `≤ Y`;
`q ≤ Y` is what places the coordinate `q` in that band, which is (i) how
`x_q ≠ 0` yields `¬ q ∣ m'`, and (ii) how the last multiplier of the prefix,
which is `q`, meets the bound `≤ Y` demanded by `profProd_agree_of_agree`.

Session 314, WP-4.
-/

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace ProfiniteHeadline

open ProfiniteEnsemble SeedCapture SelectionLaw

/-! ## 1. Bands of primes as `Finset Nat.Primes` -/

/-- The band of primes `≤ Y` other than `q`, as a finset of the prime subtype.  This
is the `Nat.Primes`-side version of `LargeStepRoughness.bandUpTo`. -/
def bandPrimes (q Y : ℕ) : Finset Nat.Primes :=
  (LargeStepRoughness.bandUpTo q Y).subtype Nat.Prime

/-- **All** primes `≤ Y`, as a finset of the prime subtype.  This is the modulus of the
CRT lift: it includes the coordinate `q`, which `bandPrimes` deliberately omits. -/
def fullBand (Y : ℕ) : Finset Nat.Primes :=
  (Finset.range (Y + 1)).subtype Nat.Prime

theorem mem_bandPrimes {q Y : ℕ} {r : Nat.Primes} :
    r ∈ bandPrimes q Y ↔ ((r : ℕ)) ∈ LargeStepRoughness.bandUpTo q Y :=
  Finset.mem_subtype

theorem mem_fullBand {Y : ℕ} {r : Nat.Primes} : r ∈ fullBand Y ↔ ((r : ℕ)) ≤ Y := by
  constructor
  · intro h
    have h' : ((r : ℕ)) ∈ Finset.range (Y + 1) := Finset.mem_subtype.mp h
    rw [Finset.mem_range] at h'
    omega
  · intro h
    exact Finset.mem_subtype.mpr (Finset.mem_range.mpr (by omega))

theorem bandPrimes_subset_fullBand (q Y : ℕ) : bandPrimes q Y ⊆ fullBand Y := by
  intro r hr
  rw [mem_bandPrimes, LargeStepRoughness.bandUpTo, Finset.mem_filter, Finset.mem_range] at hr
  exact mem_fullBand.mpr (by omega)

/-- The modulus of the band is exactly the selection-law modulus. -/
theorem emModulus_bandPrimes (q Y : ℕ) :
    emModulus (bandPrimes q Y) = SelectionLaw.modulus q Y := by
  rw [emModulus, bandPrimes, SelectionLaw.modulus]
  refine Finset.prod_subtype_of_mem (fun x => x) ?_
  intro x hx
  rw [LargeStepRoughness.bandUpTo, Finset.mem_filter] at hx
  exact hx.2.1

/-! ## 2. Coordinates versus the CRT reduction -/

/-- Points agreeing on the coordinates of `P` have the same reduction mod `∏_{r ∈ P} r`. -/
theorem redMod_eq_of_coord_eq {P : Finset Nat.Primes} {x y : Ω}
    (h : ∀ r ∈ P, x r = y r) : redMod P x = redMod P y := by
  unfold redMod
  congr 1
  funext r
  exact h (r : Nat.Primes) r.2

/-- Conversely, the reduction mod `∏_{r ∈ P} r` determines the coordinates of `P`. -/
theorem coord_eq_of_redMod_eq {P : Finset Nat.Primes} {x y : Ω}
    (h : redMod P x = redMod P y) {r : Nat.Primes} (hr : r ∈ P) : x r = y r := by
  have h' := congrArg (crtEquiv P) h
  simp only [redMod, RingEquiv.apply_symm_apply] at h'
  exact congrFun h' ⟨r, hr⟩

/-! ## 3. The covering lemma, with the prefix clause exported

`AlmostAllDensity.uncaptured_in_few_classes` is not quite enough for the transfer: to
show that the CRT lift `m'` of a profinite point misses `q`, one needs to know that the
`q`-free prefix of its residue class is nondegenerate and bounded by `Y`.  That
information is present in the *first disjunct* of the three-bad-type filter — a residue
class whose `q`-free prefix is degenerate is itself in the bad set — so it can simply be
exported alongside the covering.  This is `AlmostAllDensity.uncaptured_in_few_classes`
with one extra conclusion; the proof is the same. -/

/-- **The covering lemma with the prefix clause.**  For a fixed prime `q` and `ε > 0`
there are a horizon `n`, a truncation `Y ≥ q` and a set `T` of residues modulo
`M = SelectionLaw.modulus q Y` with `#T ≤ (ε/2)·M`, such that

* every positive `m` coprime to `q` whose genuine orbit misses `q` before depth `n` has
  `periodRep M m ∈ T`, and
* every residue class **not** in `T` has a nondegenerate `q`-free prefix bounded by `Y`
  out to depth `n + 1`. -/
theorem covering_strong (q : ℕ) (hq : q.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n Y : ℕ) (T : Finset ℕ), q ≤ Y ∧
      (T.card : ℝ) ≤ ε / 2 * ((SelectionLaw.modulus q Y : ℕ) : ℝ) ∧
      (∀ m, 1 ≤ m → (¬ q ∣ m ∧ ¬ ∃ j < n, genSeq m j = q) →
        PeriodicDensity.periodRep (SelectionLaw.modulus q Y) m ∈ T) ∧
      (∀ m : ℕ, PeriodicDensity.periodRep (SelectionLaw.modulus q Y) m ∉ T →
        ∀ j < n + 1,
          2 ≤ genSeqAvoid q (PeriodicDensity.periodRep (SelectionLaw.modulus q Y) m) j ∧
            genSeqAvoid q (PeriodicDensity.periodRep (SelectionLaw.modulus q Y) m) j ≤ Y) := by
  classical
  obtain ⟨n, Y, Cc, hqY, hM, hT⟩ := TypeBadSmall.type_bad_small q hq (ε / 2) (by positivity)
  refine ⟨n, Y, (LSPlus.sampleSpace q Y).filter (fun m =>
      ¬ (∀ j < n + 1, 2 ≤ genSeqAvoid q m j ∧ genSeqAvoid q m j ≤ Y)
      ∨ (1 : ℝ) / Cc ≤ ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ m),
            (1 : ℝ) / r
      ∨ FiberTheoremC.FiberGood q Y Cc n m), hqY, ?_, ?_, ?_⟩
  · rw [TailAssembly.card_sampleSpace] at hT
    exact hT
  · intro m hm1 hmm
    obtain ⟨hqm, hcap⟩ := hmm
    set c : ℕ := PeriodicDensity.periodRep (modulus q Y) m with hc
    have hcmem : c ∈ LSPlus.sampleSpace q Y := PeriodicDensity.periodRep_mem_Ico hM
    have hcong : c ≡ m [MOD modulus q Y] := (PeriodicDensity.periodRep_modEq _ m).symm
    refine Finset.mem_filter.mpr ⟨hcmem, ?_⟩
    by_cases hnd : ∀ j < n + 1, 2 ≤ genSeqAvoid q c j ∧ genSeqAvoid q c j ≤ Y
    · by_cases hmass : (1 : ℝ) / Cc ≤
          ∑ r ∈ (Finset.Ioc (Cc ^ 2) Y).filter (fun r => r.Prime ∧ r ∣ c), (1 : ℝ) / r
      · exact Or.inr (Or.inl hmass)
      · exact Or.inr (Or.inr ⟨hnd, le_of_lt (not_le.mp hmass), m, hm1, hqm, hcong, hcap⟩)
    · exact Or.inl hnd
  · intro m hnotT j hj
    by_contra hbad
    exact hnotT (Finset.mem_filter.mpr ⟨PeriodicDensity.periodRep_mem_Ico hM,
      Or.inl (fun hall => hbad (hall j hj))⟩)

/-! ## 4. The covering, transferred to the profinite ensemble -/

/-- **The profinite covering lemma.**  For a fixed prime `q` and `ε > 0` there are a
finite set `P` of primes, a horizon `n` and a set `T` of residue classes modulo
`emModulus P` with `#T ≤ (ε/2)·emModulus P`, such that every profinite point whose
`q`-coordinate is nonzero and whose profinite orbit misses `q` in its first `n` steps
reduces into `T`.

The proof is the CRT lift described in the module docstring. -/
theorem covering (q : ℕ) (hq : q.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : Finset Nat.Primes) (n : ℕ) (T : Finset (ZMod (emModulus P))),
      (T.card : ℝ) ≤ ε / 2 * ((emModulus P : ℕ) : ℝ) ∧
      ∀ x : Ω, x ⟨q, hq⟩ ≠ 0 → (¬ ∃ j < n, ProfiniteDynamics.profSeq x j = q) →
        redMod P x ∈ T := by
  classical
  obtain ⟨n, Y, T, hqY, hTcard, hcov, hdeg⟩ := covering_strong q hq hε
  set P : Finset Nat.Primes := bandPrimes q Y with hP
  have hPM : emModulus P = SelectionLaw.modulus q Y := emModulus_bandPrimes q Y
  refine ⟨P, n, T.image (fun t => ((t : ℕ) : ZMod (emModulus P))), ?_, ?_⟩
  · have h1 : (((T.image (fun t => ((t : ℕ) : ZMod (emModulus P)))).card : ℕ) : ℝ)
        ≤ ((T.card : ℕ) : ℝ) := by
      exact_mod_cast Finset.card_image_le
    have h2 : ((T.card : ℕ) : ℝ) ≤ ε / 2 * ((emModulus P : ℕ) : ℝ) := by
      rw [hPM]; exact hTcard
    exact le_trans h1 h2
  intro x hxq hmiss
  -- The CRT lift `m'`: an integer agreeing with `x` at every prime coordinate `≤ Y`.
  set Pf : Finset Nat.Primes := fullBand Y with hPf
  have hMfpos : 0 < emModulus Pf := emModulus_pos Pf
  have : NeZero (emModulus Pf) := ⟨hMfpos.ne'⟩
  obtain ⟨a, ha⟩ := ZMod.natCast_zmod_surjective (n := emModulus Pf) (redMod Pf x)
  set m' : ℕ := a + emModulus Pf with hm'
  have hm'1 : 1 ≤ m' := by omega
  have hm'cast : ((m' : ℕ) : ZMod (emModulus Pf)) = redMod Pf x := by
    rw [hm', Nat.cast_add, ZMod.natCast_self, add_zero, ha]
  have hredPf : redMod Pf (ProfiniteEnsemble.iota m') = redMod Pf x := by
    rw [redMod_iota]; exact hm'cast
  -- Band agreement between `x` and `m'`.
  have hagree : ∀ r : Nat.Primes, ((r : ℕ)) ≤ Y → x r = ((m' : ℕ) : ZMod ((r : ℕ))) := by
    intro r hr
    have := coord_eq_of_redMod_eq hredPf.symm (mem_fullBand.mpr hr)
    exact this
  -- `¬ q ∣ m'`, from the nonvanishing of the `q`-coordinate.
  have hqm' : ¬ q ∣ m' := by
    intro hdvd
    apply hxq
    have hqmem : ((⟨q, hq⟩ : Nat.Primes) : ℕ) ≤ Y := hqY
    rw [hagree ⟨q, hq⟩ hqmem]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  -- The residue class of the lift.
  set c : ℕ := PeriodicDensity.periodRep (SelectionLaw.modulus q Y) m' with hc
  have hcong : c ≡ m' [MOD SelectionLaw.modulus q Y] :=
    (PeriodicDensity.periodRep_modEq _ m').symm
  have hMdvd : ∀ r : ℕ, r.Prime → r ≤ Y → r ≠ q → r ∣ SelectionLaw.modulus q Y :=
    fun r hr hrY hrq => SelectionLaw.dvd_modulus hr hrY hrq
  -- **The heart**: the residue class of the lift is in `T`.
  have hcT : c ∈ T := by
    by_contra hcT
    -- The `q`-free prefix of `c` is nondegenerate and `≤ Y`, hence so is that of `m'`.
    have hnd : ∀ j < n + 1, 2 ≤ genSeqAvoid q c j ∧ genSeqAvoid q c j ≤ Y := hdeg m' hcT
    have hprefix : ∀ j < n + 1, genSeqAvoid q m' j = genSeqAvoid q c j :=
      SelectionLaw.genSeqAvoid_prefix_eq_of_modEq hq hMdvd hcong hnd
    have hndm' : ∀ j < n + 1, 2 ≤ genSeqAvoid q m' j ∧ genSeqAvoid q m' j ≤ Y := by
      intro j hj
      rw [hprefix j hj]
      exact hnd j hj
    -- The genuine orbit of `m'` misses `q` before depth `n`.
    have hmiss' : ¬ ∃ j < n, genSeq m' j = q := by
      intro hex
      -- take the *first* capture index
      have hex' : ∃ j, j < n ∧ genSeq m' j = q := hex
      set j₀ : ℕ := Nat.find hex' with hj₀
      obtain ⟨hj₀n, hj₀q⟩ : j₀ < n ∧ genSeq m' j₀ = q := Nat.find_spec hex'
      have hbefore : ∀ j < j₀, genSeq m' j ≠ q := by
        intro j hj hjq
        exact Nat.find_min hex' hj ⟨lt_trans hj hj₀n, hjq⟩
      -- before `j₀` the genuine and `q`-free dynamics coincide
      have hcoup : ∀ j < j₀, genSeqAvoid q m' j = genSeq m' j :=
        SeedCapture.genSeqAvoid_eq_genSeq_of_missed hq hm'1 hbefore
      -- all multipliers up to and including `j₀` lie in `[2, Y]`
      have hsmall : ∀ j < j₀ + 1,
          2 ≤ ProfiniteDynamics.profSeq (ProfiniteDynamics.iota m') j ∧
            ProfiniteDynamics.profSeq (ProfiniteDynamics.iota m') j ≤ Y := by
        intro j hj
        rw [ProfiniteDynamics.profSeq_iota hm'1]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · have h1 := hndm' j (by omega)
          rw [hcoup j h] at h1
          exact h1
        · subst h
          exact ⟨hj₀q ▸ hq.two_le, hj₀q ▸ hqY⟩
      have hag' : ProfiniteDynamics.AgreeUpTo Y (ProfiniteDynamics.iota m') x := by
        intro r hr
        exact (hagree r hr).symm
      have hstep := (ProfiniteDynamics.profProd_agree_of_agree hag' (j₀ + 1) hsmall).2 j₀
        (Nat.lt_succ_self j₀)
      rw [ProfiniteDynamics.profSeq_iota hm'1] at hstep
      exact hmiss ⟨j₀, hj₀n, by rw [hstep]; exact hj₀q⟩
    exact hcT (hcov m' hm'1 ⟨hqm', hmiss'⟩)
  -- Transport: `redMod P x` is the class of `c`.
  have hredP : redMod P x = ((m' : ℕ) : ZMod (emModulus P)) := by
    rw [← redMod_iota P m']
    refine redMod_eq_of_coord_eq ?_
    intro r hr
    have hrY : ((r : ℕ)) ≤ Y := by
      rw [hP, mem_bandPrimes, LargeStepRoughness.bandUpTo, Finset.mem_filter,
        Finset.mem_range] at hr
      omega
    exact hagree r hrY
  have hcm' : ((c : ℕ) : ZMod (emModulus P)) = ((m' : ℕ) : ZMod (emModulus P)) := by
    rw [ZMod.natCast_eq_natCast_iff, hPM]
    exact hcong
  refine Finset.mem_image.mpr ⟨c, hcT, ?_⟩
  rw [hcm', hredP]

/-! ## 5. The headline -/

/-- **The event that the profinite orbit of `x` never selects `q`**, relativized to the
points whose `q`-coordinate is nonzero.  The relativization is the exact profinite
analogue of the clause `¬ q ∣ m` in the integer statements, and is kept deliberately. -/
def MissingEvent (q : ℕ) (hq : q.Prime) : Set Ω :=
  {x : Ω | x ⟨q, hq⟩ ≠ 0 ∧ ¬ ∃ j, ProfiniteDynamics.profSeq x j = q}

/-- **The quantitative headline.**  For every prime `q` and every `ε > 0`, the profinite
points with nonzero `q`-coordinate whose orbit never selects `q` form a set of measure at
most `ε`.

No measurability of the event is needed: `μ` is an outer measure, so `measure_mono`
applies to arbitrary sets, and only the covering cylinder — which depends on finitely
many coordinates — has to be measurable. -/
theorem measure_missing_le (q : ℕ) (hq : q.Prime) {ε : ℝ} (hε : 0 < ε) :
    μ (MissingEvent q hq) ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨P, n, T, hTcard, hcov⟩ := covering q hq hε
  have hsub : MissingEvent q hq ⊆ {x : Ω | redMod P x ∈ T} := by
    rintro x ⟨hxq, hmiss⟩
    exact hcov x hxq (fun ⟨j, _, hj⟩ => hmiss ⟨j, hj⟩)
  have hMp : (0 : ℝ) < ((emModulus P : ℕ) : ℝ) := by
    exact_mod_cast emModulus_pos P
  have hreal : ((T.card : ℕ) : ℝ) ≤ ε * ((emModulus P : ℕ) : ℝ) := by
    nlinarith [hTcard, hMp, hε]
  have hkey : ((T.card : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal ε * ((emModulus P : ℕ) : ℝ≥0∞) := by
    calc ((T.card : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((T.card : ℕ) : ℝ) := by simp
      _ ≤ ENNReal.ofReal (ε * ((emModulus P : ℕ) : ℝ)) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal ε * ENNReal.ofReal ((emModulus P : ℕ) : ℝ) :=
          ENNReal.ofReal_mul hε.le
      _ = ENNReal.ofReal ε * ((emModulus P : ℕ) : ℝ≥0∞) := by simp
  calc μ (MissingEvent q hq) ≤ μ {x : Ω | redMod P x ∈ T} := measure_mono hsub
    _ = ((T.card : ℕ) : ℝ≥0∞) / ((emModulus P : ℕ) : ℝ≥0∞) := measure_residue_classes P T
    _ ≤ ENNReal.ofReal ε := ENNReal.div_le_of_le_mul hkey

/-- **The headline, for one prime.**  The profinite points with nonzero `q`-coordinate
whose greedy orbit never selects `q` form a `μ`-null set.

*Scope.*  This is a statement about the random model `(Ω, μ)`.  Since `ℕ ⊂ Ω` is itself
`μ`-null (`ProfiniteEnsemble.measure_range_iota_eq_zero`), it implies **nothing** about
any particular integer seed, and in particular nothing about the Euler–Mullin orbit of
`2`.  Dead ends #90 and #117 are untouched. -/
theorem measure_missing_eq_zero (q : ℕ) (hq : q.Prime) : μ (MissingEvent q hq) = 0 := by
  refine le_antisymm ?_ (by simp)
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro δ hδ _
  have hδ' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  calc μ (MissingEvent q hq) ≤ ENNReal.ofReal ((δ : ℝ)) := measure_missing_le q hq hδ'
    _ = (δ : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
    _ ≤ 0 + (δ : ℝ≥0∞) := by simp

/-- **The headline.**  `μ`-almost every profinite point captures *every* prime whose
coordinate it does not already annihilate.

This is the step that natural density cannot perform: the per-`q` statements are combined
by **countable additivity**, using only that the primes are countable.  No `q`-uniform
rate is used anywhere; for each fixed `q` the horizon is sent to infinity separately.

*Scope.*  As above: a statement about the random model.  `ℕ` is `μ`-null, so nothing
follows about integer seeds, let alone about the orbit of `2`.  The mathematics is the
finite counting chain; this file is packaging. -/
theorem measure_some_prime_missed_eq_zero :
    μ {x : Ω | ∃ q : Nat.Primes, x q ≠ 0 ∧ ¬ ∃ j, ProfiniteDynamics.profSeq x j = ((q : ℕ))}
      = 0 := by
  have hset : {x : Ω | ∃ q : Nat.Primes,
      x q ≠ 0 ∧ ¬ ∃ j, ProfiniteDynamics.profSeq x j = ((q : ℕ))}
      = ⋃ q : Nat.Primes, MissingEvent ((q : ℕ)) q.2 := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, MissingEvent]
    rfl
  rw [hset]
  exact measure_iUnion_null fun q => measure_missing_eq_zero ((q : ℕ)) q.2

end ProfiniteHeadline

end
