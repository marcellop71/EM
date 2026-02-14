import EM.MullinRotorBridge
import EM.MullinGroupSEInstances

/-!
# Equidistribution Hypotheses for Mullin's Conjecture

Equidistribution hypotheses and their implications:
* `MultEquidistribution`: every unit appears as multiplier infinitely often
* `PairEquidistribution`: every (walk, multiplier) pair appears cofinally
* `pe_implies_mullin`: PairEquidistribution → MullinConjecture
* Bootstrapping: descent via auxiliary primes
-/

open Mullin Euclid MullinGroup RotorRouter

open Mullin Euclid MullinGroup RotorRouter

/-! ## Multiplier Equidistribution (marginal) -/

/-- **Multiplier Equidistribution**: every unit in `(ZMod q)ˣ` appears as a
    multiplier residue `seq(n+1) mod q` infinitely often.

    This is the *marginal* equidistribution statement about the smallest prime
    factors of `prod(n)+1`. It implies `SubgroupEscape` (no proper subgroup
    confines all multipliers) but not `EMPointwiseRecurrence` (which requires
    knowing the multiplier distribution *conditioned on* the walk position). -/
def MultEquidistribution : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∀ (a : (ZMod q)ˣ), ∀ N, ∃ n, N ≤ n ∧
      Units.mk0 (multZ q n) (multZ_ne_zero hq hne n) = a

/-- **MultEquidistribution → SubgroupEscape**: if every unit appears as a
    multiplier, no proper subgroup confines all multipliers.

    Given `H ≠ ⊤`, pick `u ∉ H` (exists since `H` is proper). By
    equidistribution, some multiplier equals `u`, hence escapes `H`. -/
theorem me_implies_se (hme : MultEquidistribution) : SubgroupEscape := by
  intro q inst hq hne H hH
  haveI : Fact (Nat.Prime q) := inst
  -- H ≠ ⊤ implies some element lies outside H
  obtain ⟨u, hu⟩ : ∃ u : (ZMod q)ˣ, u ∉ H := by
    by_contra h; push_neg at h
    exact hH (eq_top_iff.mpr fun x _ => h x)
  -- By equidistribution, some multiplier equals u
  obtain ⟨n, _, hmult⟩ := hme q hq hne u 0
  exact ⟨n, by rw [hmult]; exact hu⟩

/-! ## Pair Equidistribution (joint) -/

/-- **Pair Equidistribution**: every (walk position, multiplier) pair in
    `(ZMod q)ˣ × (ZMod q)ˣ` appears cofinally.

    This captures the "no conspiracy" principle: the walk position `prod(n) mod q`
    (determined by multipliers at steps `0, …, n-1`) is heuristically independent
    of the next multiplier `seq(n+1) mod q` (determined by the factorization of
    the astronomically large `prod(n)+1`). Any dependence would require algebraic
    structure in `prod(n)+1` mod `q` — and no such structure exists for primes
    `q` not in the sequence. -/
def PairEquidistribution : Prop :=
  ∀ (q : Nat) [Fact (Nat.Prime q)] (hq : IsPrime q) (hne : ∀ k, seq k ≠ q),
    ∀ (x s : (ZMod q)ˣ), ∀ N, ∃ n, N ≤ n ∧
      emWalkUnit q hq hne n = x ∧ emMultUnit q hq hne n = s

/-- **PairEquidistribution → MultEquidistribution**: the joint statement
    implies the marginal — project onto the multiplier coordinate. -/
theorem pe_implies_me (hpe : PairEquidistribution) : MultEquidistribution := by
  intro q inst hq hne a N
  haveI : Fact (Nat.Prime q) := inst
  obtain ⟨n, hn, _, hmult⟩ := hpe q hq hne 1 a N
  exact ⟨n, hn, hmult⟩

/-- **PairEquidistribution → SubgroupEscape** (via MultEquidistribution). -/
theorem pe_implies_se (hpe : PairEquidistribution) : SubgroupEscape :=
  me_implies_se (pe_implies_me hpe)

/-- **PairEquidistribution → EMPointwiseRecurrence**: at every infinitely-visited
    state, every multiplier value appears. PairEquidistribution gives this
    unconditionally — the `VisitsInfOften` and `s ∈ Set.range` hypotheses
    of `PointwiseRecurrence` are simply discarded. -/
theorem pe_implies_empr (hpe : PairEquidistribution) : EMPointwiseRecurrence := by
  intro q inst hq hne
  haveI : Fact (Nat.Prime q) := inst
  intro x _ s _ N
  exact hpe q hq hne x s N

/-! ## Direct path: PairEquidistribution → MullinConjecture -/

/-- **PairEquidistribution → HittingHypothesis**: the walk visits `-1`,
    bypassing the SE/EMPR decomposition entirely.

    Pick the walk target to be the unit `-1`; PairEquidistribution immediately
    supplies a step `n` where `walkZ q n = -1`, i.e., `q ∣ prod(n) + 1`. -/
theorem pe_implies_hh (hpe : PairEquidistribution) : HittingHypothesis := by
  intro q hq hne N
  haveI : Fact (Nat.Prime q) := ⟨IsPrime.toNatPrime hq⟩
  let neg1 : (ZMod q)ˣ := Units.mk0 (-1) (neg_ne_zero.mpr one_ne_zero)
  obtain ⟨n, hn, hwalk, _⟩ := hpe q hq hne neg1 1 N
  -- Extract walkZ q n = -1 from the unit-level equality
  have hval : walkZ q n = -1 := by
    have := congrArg Units.val hwalk
    simpa [emWalkUnit, neg1] using this
  exact ⟨n, hn, (walkZ_eq_neg_one_iff n).mp hval⟩

/-- **PairEquidistribution → MullinConjecture** (direct path via HH). -/
theorem pe_implies_mullin (hpe : PairEquidistribution) : MullinConjecture :=
  hh_implies_mullin (pe_implies_hh hpe)

/-- **PairEquidistribution → MullinConjecture** (structural path via SE + EMPR).

    This alternative proof goes through the full decomposition, showing that
    PairEquidistribution implies both leaves independently. -/
theorem pe_implies_mullin' (hpe : PairEquidistribution) : MullinConjecture :=
  empr_se_implies_mullin (pe_implies_empr hpe) (pe_implies_se hpe)

/-! ## Bootstrapping: Descent via auxiliary primes

The bootstrapping approach connects the Hitting Hypothesis across different
primes via the **cofinal pigeonhole principle** and **multiplier pinning**.

Key structural results:

* `cofinal_pigeonhole`: classifying cofinally many events into finitely many
  buckets, some bucket is hit cofinally.
* `multiplier_pinning`: HH(p) + MC for primes < p → seq(n+1) = p cofinally.
* `seq_determines_multZ`: seq(n+1) = p → multZ q n = (p : ZMod q).
* `bootstrap_partial_pe`: combining pinning with pigeonhole gives a specific
  walk-multiplier pair that appears cofinally.

### The descent structure

For a target prime q and residue class s ∈ (ZMod q)ˣ, if we can find an
auxiliary prime p ≡ s (mod q) with p ∉ seq and HH(p) holding, then:

1. Multiplier pinning gives seq(n+1) = p cofinally.
2. At those steps, multZ(q, n) = (p : ZMod q) = s.
3. Pigeonhole on the walk position gives some x₀ with the pair (x₀, s)
   appearing cofinally — a partial PE result for the pair (x₀, s).

The walk position x₀ is selected by pigeonhole, not by choice.
Getting ALL walk positions requires additional mixing structure.
-/

section Bootstrapping

/-- **Cofinal pigeonhole**: if a property holds cofinally among natural numbers,
    and we classify naturals into finitely many classes, some class is hit
    cofinally.

    Proof: if no class is hit cofinally, each class has a bound past which it
    is never hit. Past the maximum of all bounds, no class is hit — contradicting
    the property holding cofinally. -/
theorem cofinal_pigeonhole {α : Type*} [Fintype α]
    (P : ℕ → Prop) (f : ℕ → α)
    (hinf : ∀ N, ∃ n, N ≤ n ∧ P n) :
    ∃ a : α, ∀ N, ∃ n, N ≤ n ∧ P n ∧ f n = a := by
  by_contra h
  push_neg at h
  -- h : ∀ a, ∃ Na, ∀ n, Na ≤ n → P n → f n ≠ a
  choose Na hNa using h
  obtain ⟨n, hn, hPn⟩ := hinf (Finset.univ.sup Na)
  exact hNa (f n) n (le_trans (Finset.le_sup (Finset.mem_univ _)) hn) hPn rfl

/-- **Multiplier pinning**: if p is prime, HH(p) holds, and all primes below p
    appear in the sequence, then `seq(n+1) = p` cofinally.

    At steps where `p ∣ prod(n)+1` (given by HH), the `captures_target` lemma
    forces `minFac(prod(n)+1) = p` once all smaller primes have appeared
    (since they divide `prod(n)` and hence cannot divide `prod(n)+1`). -/
theorem multiplier_pinning {p : Nat} (hp : IsPrime p)
    (hHH : ∀ N, ∃ n, N ≤ n ∧ p ∣ prod n + 1)
    (hMC_small : ∀ r, r < p → IsPrime r → ∃ m, seq m = r) :
    ∀ N, ∃ n, N ≤ n ∧ seq (n + 1) = p := by
  obtain ⟨N₀, hN₀⟩ := exists_bound p hMC_small
  intro N
  obtain ⟨n, hn, hdvd⟩ := hHH (max N N₀)
  exact ⟨n, by omega, captures_target hp hdvd fun r hr hrp =>
    let ⟨m, hm, hseqm⟩ := hN₀ r hr hrp; ⟨m, by omega, hseqm⟩⟩

/-- `seq(n+1) = p` determines the multiplier residue: `multZ q n = (p : ZMod q)`. -/
theorem seq_determines_multZ {p q n : Nat} (hseq : seq (n + 1) = p) :
    multZ q n = (p : ZMod q) := by
  simp only [multZ, hseq]

/-- **Bootstrap partial PE**: if p is prime, HH(p) holds, MC holds for primes
    below p, and q is another prime not in seq, then some walk position
    x₀ ∈ (ZMod q)ˣ satisfies: cofinally many n have
    `walkZ(q,n) = x₀` and `multZ(q,n) = (p : ZMod q)`.

    If additionally `(p : ZMod q) = s` for a target unit `s`, this gives a
    specific walk-multiplier pair (x₀, s) appearing cofinally — one entry
    of the PairEquidistribution table. -/
theorem bootstrap_partial_pe {p q : Nat} [Fact (Nat.Prime q)]
    (hp : IsPrime p) (hq : IsPrime q) (hne_q : ∀ k, seq k ≠ q)
    (hHH : ∀ N, ∃ n, N ≤ n ∧ p ∣ prod n + 1)
    (hMC_small : ∀ r, r < p → IsPrime r → ∃ m, seq m = r) :
    ∃ x : (ZMod q)ˣ, ∀ N, ∃ n, N ≤ n ∧
      emWalkUnit q hq hne_q n = x ∧
      multZ q n = (p : ZMod q) := by
  have hpin := multiplier_pinning hp hHH hMC_small
  have hinf : ∀ N, ∃ n, N ≤ n ∧ multZ q n = (p : ZMod q) :=
    fun N => let ⟨n, hn, hs⟩ := hpin N; ⟨n, hn, seq_determines_multZ hs⟩
  obtain ⟨x, hx⟩ := cofinal_pigeonhole _ (emWalkUnit q hq hne_q) hinf
  exact ⟨x, fun N => let ⟨n, hn, hm, hw⟩ := hx N; ⟨n, hn, hw, hm⟩⟩

/-- **HH → PE (vacuously)**: if HH holds for all primes, then
    PairEquidistribution is vacuously true — because HH → MC, so no prime
    satisfies `∀ k, seq k ≠ q`, making PE's universal quantifier vacuous.

    This reveals the logical structure: PE and HH are equivalent in strength
    (both imply MC, both follow from MC's negation being inconsistent), and
    the bootstrapping machinery is valuable precisely when HH is known for
    SOME primes but not all. -/
theorem hh_implies_pe_vacuous (hHH : HittingHypothesis) : PairEquidistribution := by
  intro q _ hq hne
  exact absurd (hh_implies_mullin hHH q hq) (fun ⟨n, hn⟩ => hne n hn)

/-- **The descent principle**: if p is prime, p ∉ seq, and all primes below p
    appear in the sequence, then HH(p) is equivalent to `p` appearing.

    Forward: HH(p) + `captures_target` forces seq(n+1) = p, contradicting p ∉ seq.
    So HH(p) + MC(<p) + p ∉ seq is inconsistent — meaning HH(p) forces p to appear.

    This is the heart of `hh_implies_mullin`, isolated as a standalone principle:
    the Hitting Hypothesis for any single prime, combined with MC for all
    smaller primes, forces that prime to appear in the sequence. -/
theorem hh_forces_appearance {p : Nat} (hp : IsPrime p)
    (hne : ∀ k, seq k ≠ p)
    (hHH : ∀ N, ∃ n, N ≤ n ∧ p ∣ prod n + 1)
    (hMC_small : ∀ r, r < p → IsPrime r → ∃ m, seq m = r) :
    False := by
  obtain ⟨n, _, hseq⟩ := multiplier_pinning hp hHH hMC_small 0
  exact hne (n + 1) hseq

end Bootstrapping
