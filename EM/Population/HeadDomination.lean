import EM.IK.Karamata

/-!
# Head domination: the least prime factor is *not* equidistributed among rough integers

`RoughLPFEquidist q` (`EM/Population/AlladiDensity.lean`) asserts that among the `q`-rough
integers `m ≤ X` (those with `minFac m > q`), the residue `minFac m mod q` is equidistributed
on the coprime classes: each class has density `c/(q−1)`, where `c` is the density of the
`q`-rough integers.  `MinFacResidueEquidist` and `PopulationEquidist` assert the same for the
shifted-squarefree subpopulation.  All three were introduced as consequences of "standard
analytic number theory" (Dirichlet + sieve).

**They are not consequences of anything of the sort, and they are false.**  This file proves
the first half as a theorem and explains the second.

## The theorem: the class densities are explicit convergent series

For a prime `p`, the set `{m : minFac m = p}` has natural density

  `w p = cfun p / p`,   `cfun n = ∏_{r < n, r prime} (1 − 1/r) = Apr n / Npr n`

(`m` is divisible by `p` and coprime to the primes below `p`; the conditions are periodic and
independent by CRT — `card_minFac_eq_ge`, `card_minFac_eq_le`).  For prime `p`,
`cfun (p+1) = (1 − 1/p) cfun p`, so the weights **telescope**: `w p = cfun p − cfun (p+1)`
(`w_eq_cfun_sub`).  Hence every class sum converges, its tail beyond `P` is `≤ cfun (P+1)`, and
`cfun → 0` because `∑ 1/p` diverges (`cfun_tendsto_zero`).  Putting the counting bounds
together:

* `tendsto_roughCount_div` — the `q`-rough integers have density `cfun (q+1)`;
* `tendsto_classCount_div` — the class `a` has density `∑_{p ≡ a (q), p > q} w p`;
* `roughLPFEquidist_iff` — **`RoughLPFEquidist q ⟺ ∀ a coprime, ∑_{p ≡ a (q), p > q} w p =
  cfun (q+1)/(q−1)`**;
* `primesEquidistAsympImpliesRoughLPF_iff` — since its hypothesis is a theorem
  (`IK.primesEquidistInAP_asymp_proved`, Karamata), the registered open point
  `PrimesEquidistAsympImpliesRoughLPF` **is** the family of these identities over all primes `q`;
* `sum_tsum_wcls` — the class sums add up to `cfun (q+1)`;
* `not_roughLPFEquidist_of_head` — the head-domination criterion: a finite set of primes of one
  class carrying more than the equidistributed share already refutes `RoughLPFEquidist q`.

## The argument: why the identity fails

The identity `∑_{p ≡ a} w p = cfun (q+1)/(q−1)` asks a *convergent* series with strictly
decreasing terms to split evenly among the `q − 1` classes.  Dirichlet's theorem — and every
theorem about counting functions of primes — is silent about it: asymptotic equidistribution of
`π(x; q, a)` constrains the tail of the series, and the tail carries no mass in the limit.
What decides the value is the *head*: the first few primes above `q`.  Concretely, let `p₀` be
the least prime above `q` (Bertrand: `p₀ < 2q`).  Its own weight is the fraction `1/p₀` of the
whole `q`-rough mass, already almost the full equidistributed share `1/(q−1)`; if the remaining
mass `1 − 1/p₀` were split evenly, the class of `p₀` would receive about `2/q`, twice its
share.  Equidistribution therefore requires the primes `≡ p₀ (mod q)` to be *systematically
deficient* — in the `w`-weighted sense — for ever after, at every prime `q`.  There is no reason
for that, and it does not happen: the informal derivations of these hypotheses
("size-dependent weights are equidistributed by Dirichlet") mistook a statement about
divergent counting functions for one about a convergent weighted sum.  The same mechanism, one
step earlier, is what Dead Ends #137/#157 recorded for the unconditioned ensemble.

For a *given* `q`, "the class of `p₀` exceeds its share" is a finite quantitative fact — a
rational inequality between finitely many values of `cfun` — certifiable through
`not_roughLPFEquidist_of_head` by exact arithmetic on a finite head.  Deliberately, no such
certificate is included here: the mathematics of the situation is the equivalence, and the
project's rule is proofs, not computation.  What is asserted, and what the reader can check
against the criterion in a few lines of arithmetic, is that the identity fails at small `q`
(already at `q = 5`, in the class of `p₀ = 7`).

## Consequences

The same mechanism, with the sieve weights `g(r) = r/(r²−1)` in place of `1/r`, applies to
`MinFacResidueEquidist q` and `PopulationEquidist` (the head is again carried by `p₀`).  So
`DeterministicStabilityLemma := PopulationEquidist → CME`, `DSLHitting`, and
`PopulationTransfer` are vacuous, and every master theorem with premise
`∀ q, MinFacResidueEquidist q` (`full_chain_dsl`, `wpnt_dsl_implies_mc`,
`alladi_dsl_implies_mc`, `dsl_closes_all`) has a false premise.  What survives is the
orbit-level chain `CME ⇒ CCSB ⇒ MC` (`cme_implies_mc`), which never used the population.
The population statement that *is* true is the double limit `z → ∞` after `X → ∞`; it follows
from `PrimeLogSumEquidistAsymp` by partial summation, but it is not what the reduction network
consumed.  See Dead End #160.
-/

noncomputable section
open Classical

open Finset

/-! ## The retired hypotheses, kept live only as the subject of the characterization

These definitions were introduced in `EM/Population/AlladiDensity.lean` as the entry of the
Alladi chain (archived to `EM/Archive/Population/AlladiDensityArchive.lean`, Dead End #160).
They live here so that `roughLPFEquidist_iff` and `primesEquidistAsympImpliesRoughLPF_iff`
can be stated; they are not targets. -/

/-- Count of integers `m ∈ [2, X]` with `minFac m > z` — the `z`-rough integers. -/
def roughCount (z X : Nat) : Nat :=
  ((Finset.Icc 2 X).filter (fun m => z < Nat.minFac m)).card

/-- The rough count is at most `X − 1`. -/
theorem roughCount_le_card (z X : Nat) : roughCount z X ≤ X - 1 := by
  have := Finset.card_filter_le (Finset.Icc 2 X) (fun m => z < Nat.minFac m)
  simp [roughCount, Nat.card_Icc] at this ⊢; omega

/-- **Equidistribution of `minFac mod q` among `q`-rough integers** (RETIRED, FALSE — see the
module docstring).  For each coprime class `a`, the density of
`{m ∈ [2,X] : minFac m > q, minFac m ≡ a}` is `c/(q−1)`, `c` the density of the `q`-rough
integers.  Characterized as a series identity by `HeadDomination.roughLPFEquidist_iff`. -/
def RoughLPFEquidist (q : Nat) : Prop :=
  ∀ (a : Nat), 0 < a → a < q → Nat.Coprime a q →
    ∃ (c : ℝ), 0 < c ∧
      Filter.Tendsto (fun X : Nat => (roughCount q X : ℝ) / (X : ℝ))
        Filter.atTop (nhds c) ∧
      Filter.Tendsto (fun X : Nat =>
        (((Finset.Icc 2 X).filter
          (fun m => q < Nat.minFac m ∧ Nat.minFac m % q = a)).card : ℝ) / (X : ℝ))
        Filter.atTop (nhds (c / (q - 1 : ℝ)))

/-- **The first Alladi link on the asymptotic ANT input** (RETIRED, FALSE).  Its hypothesis is
a theorem (`IK.primesEquidistInAP_asymp_proved`), so it is equivalent to
`∀ q prime, RoughLPFEquidist q` — the false series identity
(`HeadDomination.primesEquidistAsympImpliesRoughLPF_iff`). -/
def PrimesEquidistAsympImpliesRoughLPF : Prop :=
  IK.PrimesEquidistInAPAsymp → ∀ (q : Nat), Nat.Prime q → RoughLPFEquidist q

namespace HeadDomination

/-! ## Part 1: primorials below `p` and their totients -/

/-- The product of the primes below `p`. -/
def Npr (p : ℕ) : ℕ := ∏ r ∈ (range p).filter Nat.Prime, r

/-- The product of `r − 1` over the primes `r` below `p`; equals `φ (Npr p)`. -/
def Apr (p : ℕ) : ℕ := ∏ r ∈ (range p).filter Nat.Prime, (r - 1)

theorem Npr_pos (p : ℕ) : 0 < Npr p :=
  Finset.prod_pos fun _ hr => (Finset.mem_filter.mp hr).2.pos

theorem Apr_pos (p : ℕ) : 0 < Apr p :=
  Finset.prod_pos fun _ hr => by
    have := (Finset.mem_filter.mp hr).2.two_le; omega

/-- `φ` of a product of distinct primes is the product of `r − 1`. -/
theorem totient_prod_primes (s : Finset ℕ) (hs : ∀ r ∈ s, Nat.Prime r) :
    Nat.totient (∏ r ∈ s, r) = ∏ r ∈ s, (r - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hpa : Nat.Prime a := hs a (Finset.mem_insert_self a s)
    have hcop : Nat.Coprime a (∏ r ∈ s, r) := by
      rw [Nat.coprime_prod_right_iff]
      intro r hr
      exact (Nat.coprime_primes hpa (hs r (Finset.mem_insert_of_mem hr))).mpr
        (fun h => ha (h ▸ hr))
    rw [Nat.totient_mul hcop, Nat.totient_prime hpa,
      ih fun r hr => hs r (Finset.mem_insert_of_mem hr)]

theorem totient_Npr (p : ℕ) : Nat.totient (Npr p) = Apr p :=
  totient_prod_primes _ fun _ hr => (Finset.mem_filter.mp hr).2

/-- Coprimality to `Npr p` is exactly "no prime factor below `p`". -/
theorem coprime_Npr_iff (k p : ℕ) :
    Nat.Coprime k (Npr p) ↔ ∀ r, Nat.Prime r → r < p → ¬ r ∣ k := by
  unfold Npr
  rw [Nat.coprime_prod_right_iff]
  constructor
  · intro h r hr hrp hdvd
    have := h r (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrp, hr⟩)
    exact (Nat.Prime.coprime_iff_not_dvd hr).mp this.symm hdvd
  · intro h r hr
    obtain ⟨hrp, hr'⟩ := Finset.mem_filter.mp hr
    exact ((Nat.Prime.coprime_iff_not_dvd hr').mpr (h r hr' (Finset.mem_range.mp hrp))).symm

/-- `p · Npr p = Npr (p+1)` for prime `p`. -/
theorem Npr_succ_of_prime {p : ℕ} (hp : Nat.Prime p) : Npr (p + 1) = p * Npr p := by
  unfold Npr
  rw [Finset.range_add_one, Finset.filter_insert, if_pos hp, Finset.prod_insert]
  simp

/-- Monotonicity: `Npr a ∣ Npr b` for `a ≤ b`. -/
theorem Npr_dvd_Npr {a b : ℕ} (h : a ≤ b) : Npr a ∣ Npr b :=
  Finset.prod_dvd_prod_of_subset _ _ _
    (Finset.filter_subset_filter _ (Finset.range_subset_range.mpr h))

/-! ## Part 2: block counting of integers coprime to `N` -/

/-- Exactly `φ N` integers in each block of `N` consecutive integers are coprime to `N`,
so `B · φ N` of the integers in `[1, B·N]` are. -/
theorem card_coprime_Ico_blocks (N B : ℕ) :
    ((Ico 1 (1 + B * N)).filter (fun k => Nat.Coprime N k)).card = B * Nat.totient N := by
  induction B with
  | zero => simp
  | succ B ih =>
    have hsplit : Ico 1 (1 + (B + 1) * N) = Ico 1 (1 + B * N) ∪ Ico (1 + B * N) (1 + B * N + N) := by
      rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
      congr 1; ring
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint, ih,
      Nat.filter_coprime_Ico_eq_totient N (1 + B * N)]
    · ring
    · exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)

/-- Lower bound: at least `⌊Y/N⌋ · φ N` integers in `[1, Y]` are coprime to `N`. -/
theorem card_coprime_Icc_ge (N Y : ℕ) :
    (Y / N) * Nat.totient N ≤ ((Icc 1 Y).filter (fun k => Nat.Coprime N k)).card := by
  rw [← card_coprime_Ico_blocks N (Y / N)]
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro k hk
  rw [Finset.mem_Ico] at hk
  rw [Finset.mem_Icc]
  refine ⟨hk.1, ?_⟩
  have := Nat.div_mul_le_self Y N
  omega

/-- Upper bound: at most `(⌊Y/N⌋ + 1) · φ N` integers in `[0, Y]` are coprime to `N`
(for `N ≥ 1`). -/
theorem card_coprime_le (N Y : ℕ) (hN : 0 < N) :
    ((Icc 0 Y).filter (fun k => Nat.Coprime N k)).card ≤ (Y / N + 1) * Nat.totient N := by
  have hblocks : ((Ico 0 ((Y / N + 1) * N)).filter (fun k => Nat.Coprime N k)).card =
      (Y / N + 1) * Nat.totient N := by
    -- shift `card_coprime_Ico_blocks` down by one: `Ico 0 (BN)` versus `Ico 1 (1 + BN)`
    have key : ∀ B : ℕ, ((Ico 0 (B * N)).filter (fun k => Nat.Coprime N k)).card =
        B * Nat.totient N := by
      intro B
      induction B with
      | zero => simp
      | succ B ih =>
        have hsplit : Ico 0 ((B + 1) * N) = Ico 0 (B * N) ∪ Ico (B * N) (B * N + N) := by
          rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
          congr 1; ring
        rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint, ih,
          Nat.filter_coprime_Ico_eq_totient N (B * N)]
        · ring
        · exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)
    exact key _
  rw [← hblocks]
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_Ico]
  refine ⟨Nat.zero_le _, ?_⟩
  have h1 : Y < (Y / N + 1) * N := by
    have := Nat.lt_div_mul_add hN (a := Y)
    -- `Y < Y / N * N + N`
    nlinarith [Nat.div_add_mod Y N, Nat.mod_lt Y hN]
  omega

/-! ## Part 3: the counting lower bound for `{m : minFac m = p}` -/

/-- If `k ≥ 1` has no prime factor below the prime `p`, then `minFac (p·k) = p`. -/
theorem minFac_mul_eq_of_coprime {p k : ℕ} (hp : Nat.Prime p) (hk1 : 1 ≤ k)
    (hk : Nat.Coprime (Npr p) k) : Nat.minFac (p * k) = p := by
  have hpk1 : p * k ≠ 1 := by
    have := hp.two_le; intro h
    have : p * k ≥ 2 * 1 := Nat.mul_le_mul this hk1
    omega
  have hle : Nat.minFac (p * k) ≤ p :=
    Nat.minFac_le_of_dvd hp.two_le (Dvd.intro k rfl)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exfalso
    have hr := Nat.minFac_prime hpk1
    have hdvd := Nat.minFac_dvd (p * k)
    rcases (Nat.Prime.dvd_mul hr).mp hdvd with h | h
    · -- minFac ∣ p with minFac < p: contradiction with primality of p
      have := (Nat.prime_dvd_prime_iff_eq hr hp).mp h
      omega
    · exact (coprime_Npr_iff k p).mp hk.symm _ hr hlt h
  · exact heq

/-- **The counting lower bound.**  For prime `p`,
`⌊X / (p · Npr p)⌋ · Apr p ≤ #{m ∈ [2, X] : minFac m = p}`. -/
theorem card_minFac_eq_ge {p : ℕ} (hp : Nat.Prime p) (X : ℕ) :
    (X / (p * Npr p)) * Apr p ≤ ((Icc 2 X).filter (fun m => Nat.minFac m = p)).card := by
  -- the image of `{k ∈ [1, X/p] : Coprime (Npr p) k}` under `k ↦ p k`
  set S := (Icc 1 (X / p)).filter (fun k => Nat.Coprime (Npr p) k) with hS
  have himg : S.image (fun k => p * k) ⊆ (Icc 2 X).filter (fun m => Nat.minFac m = p) := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, minFac_mul_eq_of_coprime hp hk.1.1 hk.2⟩
    · have := hp.two_le
      calc 2 ≤ p * 1 := by omega
        _ ≤ p * k := Nat.mul_le_mul_left p hk.1.1
    · calc p * k ≤ p * (X / p) := Nat.mul_le_mul_left p hk.1.2
        _ ≤ X := Nat.mul_div_le X p
  have hinj : Set.InjOn (fun k => p * k) (S : Set ℕ) := by
    intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hp.pos h
  calc (X / (p * Npr p)) * Apr p
      = ((X / p) / Npr p) * Nat.totient (Npr p) := by
        rw [Nat.div_div_eq_div_mul, totient_Npr]
    _ ≤ S.card := card_coprime_Icc_ge (Npr p) (X / p)
    _ = (S.image (fun k => p * k)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card himg

/-! ## Part 4: the counting upper bound for the rough integers -/

/-- `q`-rough integers `m ≥ 2` are coprime to the product of the primes `≤ q`. -/
theorem coprime_of_rough {q m : ℕ} (hrough : q < Nat.minFac m) :
    Nat.Coprime (Npr (q + 1)) m := by
  rw [Nat.coprime_comm, coprime_Npr_iff]
  intro r hr hrq hdvd
  have := Nat.minFac_le_of_dvd hr.two_le hdvd
  omega

/-- Upper bound: `roughCount q X ≤ (X / N + 1) · φ N` with `N = Npr (q+1)`. -/
theorem roughCount_le (q X : ℕ) :
    roughCount q X ≤ (X / Npr (q + 1) + 1) * Nat.totient (Npr (q + 1)) := by
  unfold roughCount
  calc ((Icc 2 X).filter (fun m => q < Nat.minFac m)).card
      ≤ ((Icc 0 X).filter (fun k => Nat.Coprime (Npr (q + 1)) k)).card := by
        apply Finset.card_le_card
        intro m hm
        rw [Finset.mem_filter, Finset.mem_Icc] at hm
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨Nat.zero_le _, hm.1.2⟩, coprime_of_rough hm.2⟩
    _ ≤ _ := card_coprime_le _ _ (Npr_pos _)

/-- Upper bound companion to `card_minFac_eq_ge`:
`#{m ∈ [2, X] : minFac m = p} ≤ (⌊X/(p · Npr p)⌋ + 1) · Apr p`. -/
theorem card_minFac_eq_le {p : ℕ} (hp : Nat.Prime p) (X : ℕ) :
    ((Icc 2 X).filter (fun m => Nat.minFac m = p)).card ≤ (X / (p * Npr p) + 1) * Apr p := by
  set S := (Icc 0 (X / p)).filter (fun k => Nat.Coprime (Npr p) k) with hS
  have hsub : (Icc 2 X).filter (fun m => Nat.minFac m = p) ⊆ S.image (fun k => p * k) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm2, hmX⟩, hmin⟩ := hm
    have hdvd : p ∣ m := hmin ▸ Nat.minFac_dvd m
    obtain ⟨k, rfl⟩ := hdvd
    refine Finset.mem_image.mpr ⟨k, ?_, rfl⟩
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.zero_le _, ?_⟩, ?_⟩
    · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by rw [mul_comm]; exact hmX)
    · rw [Nat.coprime_comm, coprime_Npr_iff]
      intro r hr hrp hrk
      have : Nat.minFac (p * k) ≤ r :=
        Nat.minFac_le_of_dvd hr.two_le (Dvd.dvd.mul_left hrk p)
      omega
  calc ((Icc 2 X).filter (fun m => Nat.minFac m = p)).card
      ≤ (S.image (fun k => p * k)).card := Finset.card_le_card hsub
    _ ≤ S.card := Finset.card_image_le
    _ ≤ ((X / p) / Npr p + 1) * Nat.totient (Npr p) := card_coprime_le _ _ (Npr_pos p)
    _ = (X / (p * Npr p) + 1) * Apr p := by rw [Nat.div_div_eq_div_mul, totient_Npr]

/-- Lower bound companion to `roughCount_le`: `⌊X/N⌋ · φ N − 1 ≤ roughCount q X`. -/
theorem roughCount_ge (q X : ℕ) :
    (X / Npr (q + 1)) * Nat.totient (Npr (q + 1)) ≤ roughCount q X + 1 := by
  unfold roughCount
  set N := Npr (q + 1)
  have hsub : (Icc 1 X).filter (fun k => Nat.Coprime N k) ⊆
      insert 1 ((Icc 2 X).filter (fun m => q < Nat.minFac m)) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · left; omega
    · right
      refine ⟨⟨hk2, hk.1.2⟩, ?_⟩
      by_contra hcon
      push Not at hcon
      have hr := Nat.minFac_prime (by omega : k ≠ 1)
      have := (coprime_Npr_iff k (q + 1)).mp hk.2.symm _ hr (by omega) (Nat.minFac_dvd k)
      exact this
  calc (X / N) * Nat.totient N
      ≤ ((Icc 1 X).filter (fun k => Nat.Coprime N k)).card := card_coprime_Icc_ge N X
    _ ≤ (insert 1 ((Icc 2 X).filter (fun m => q < Nat.minFac m))).card :=
        Finset.card_le_card hsub
    _ ≤ _ := Finset.card_insert_le _ _

/-! ## Part 5: the weights, their telescoping, and the tail

`cfun n = Apr n / Npr n = ∏_{r < n, r prime} (1 − 1/r)` is the density of the integers with no
prime factor below `n`, and `w p = cfun p / p` is the density of `{m : minFac m = p}`.  For
prime `p`, `cfun (p+1) = (1 − 1/p) · cfun p`, so **`w p = cfun p − cfun (p+1)`**: the weights
telescope, the class sums are convergent, and every tail is a value of `cfun`.  Finally
`cfun → 0` because `∑ 1/p` diverges. -/

/-- `∏_{r < n} (1 − 1/r)` over primes, as `Apr n / Npr n`. -/
def cfun (n : ℕ) : ℝ := (Apr n : ℝ) / Npr n

/-- The density of `{m : minFac m = p}`. -/
def w (p : ℕ) : ℝ := cfun p / p

theorem cfun_nonneg (n : ℕ) : 0 ≤ cfun n := by unfold cfun; positivity

theorem cfun_pos (n : ℕ) : 0 < cfun n := by
  unfold cfun; exact div_pos (by exact_mod_cast Apr_pos n) (by exact_mod_cast Npr_pos n)

theorem w_nonneg (p : ℕ) : 0 ≤ w p := by unfold w; exact div_nonneg (cfun_nonneg p) (Nat.cast_nonneg p)

/-- `Apr (p+1) = (p − 1) · Apr p` for prime `p`. -/
theorem Apr_succ_of_prime {p : ℕ} (hp : Nat.Prime p) : Apr (p + 1) = (p - 1) * Apr p := by
  unfold Apr
  rw [Finset.range_add_one, Finset.filter_insert, if_pos hp, Finset.prod_insert]
  simp

/-- For non-prime `n`, `Npr` and `Apr` do not move. -/
theorem Npr_succ_of_not_prime {n : ℕ} (hn : ¬ Nat.Prime n) : Npr (n + 1) = Npr n := by
  unfold Npr; rw [Finset.range_add_one, Finset.filter_insert, if_neg hn]

theorem Apr_succ_of_not_prime {n : ℕ} (hn : ¬ Nat.Prime n) : Apr (n + 1) = Apr n := by
  unfold Apr; rw [Finset.range_add_one, Finset.filter_insert, if_neg hn]

/-- **Telescoping**: `w p = cfun p − cfun (p+1)` for prime `p`. -/
theorem w_eq_cfun_sub {p : ℕ} (hp : Nat.Prime p) : w p = cfun p - cfun (p + 1) := by
  unfold w cfun
  rw [Apr_succ_of_prime hp, Npr_succ_of_prime hp]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hN : (Npr p : ℝ) ≠ 0 := by exact_mod_cast (Npr_pos p).ne'
  have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le]; simp
  push_cast [hp1]
  field_simp
  ring

theorem cfun_succ_of_not_prime {n : ℕ} (hn : ¬ Nat.Prime n) : cfun (n + 1) = cfun n := by
  unfold cfun; rw [Apr_succ_of_not_prime hn, Npr_succ_of_not_prime hn]

/-- The step `cfun n − cfun (n+1)` is `w n` at primes and `0` elsewhere. -/
theorem cfun_sub_succ (n : ℕ) :
    cfun n - cfun (n + 1) = if Nat.Prime n then w n else 0 := by
  split_ifs with h
  · exact (w_eq_cfun_sub h).symm
  · rw [cfun_succ_of_not_prime h]; ring

theorem cfun_antitone : Antitone cfun := by
  apply antitone_nat_of_succ_le
  intro n
  have := cfun_sub_succ n
  split_ifs at this with h
  · linarith [w_nonneg n]
  · linarith

/-- The telescoped partial sums: `∑_{q < n ≤ P} [n prime] w n = cfun (q+1) − cfun (P+1)`. -/
theorem sum_w_Ioc (q P : ℕ) (hqP : q ≤ P) :
    ∑ n ∈ Ioc q P, (if Nat.Prime n then w n else 0) = cfun (q + 1) - cfun (P + 1) := by
  induction P, hqP using Nat.le_induction with
  | base => simp
  | succ P hP ih =>
    rw [Finset.sum_Ioc_succ_top hP, ih, ← cfun_sub_succ]; ring

/-- `1 − 1/r ≤ exp (−1/r)`, hence `cfun n ≤ exp (− ∑_{r < n} 1/r)`. -/
theorem cfun_le_exp (n : ℕ) :
    cfun n ≤ Real.exp (-(∑ r ∈ (range n).filter Nat.Prime, (1 : ℝ) / r)) := by
  unfold cfun Apr Npr
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib, ← Finset.sum_neg_distrib,
    Real.exp_sum]
  apply Finset.prod_le_prod
  · intro r hr; positivity
  · intro r hr
    have hr' := (Finset.mem_filter.mp hr).2
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr'.pos
    have h1 : ((r - 1 : ℕ) : ℝ) / r = 1 + (-(1 / (r : ℝ))) := by
      rw [Nat.cast_sub hr'.one_le]; field_simp; ring
    rw [h1]
    exact Real.add_one_le_exp _ |>.trans_eq' (by ring)

/-- The partial sums of `1/p` over primes are unbounded (Euler; Mathlib's
`not_summable_one_div_on_primes`). -/
theorem tendsto_sum_inv_primes :
    Filter.Tendsto (fun n => ∑ r ∈ (range n).filter Nat.Prime, (1 : ℝ) / r)
      Filter.atTop Filter.atTop := by
  have h := not_summable_one_div_on_primes
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun n => Set.indicator_apply_nonneg fun _ => by positivity)] at h
  refine h.congr fun n => ?_
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun r _ => by simp [Set.indicator_apply]

/-- **The tail vanishes**: `cfun n → 0`. -/
theorem cfun_tendsto_zero : Filter.Tendsto cfun Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n => Real.exp (-(∑ r ∈ (range n).filter Nat.Prime, (1 : ℝ) / r)))
      Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp tendsto_sum_inv_primes)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 cfun_nonneg cfun_le_exp

/-! ## Part 6: the class densities are exactly the class sums of the weights

`classCount q a X` is the counting function inside `RoughLPFEquidist`.  We show it has density
`∑' n, wcls q a n`, the sum of `w p` over the primes `p > q` in the class `a`, and that
`roughCount q X` has density `cfun (q+1)`.  Consequently `RoughLPFEquidist q` is *equivalent*
to the family of identities `∑_{p ≡ a (q), p > q} w_p = cfun (q+1)/(q−1)`. -/

/-- The counting function of `RoughLPFEquidist`. -/
def classCount (q a X : ℕ) : ℕ :=
  ((Icc 2 X).filter (fun m => q < Nat.minFac m ∧ Nat.minFac m % q = a)).card

/-- The weight `w n` restricted to primes `n > q`. -/
def wq (q n : ℕ) : ℝ := if Nat.Prime n ∧ q < n then w n else 0

/-- The weight `w n` restricted to primes `n > q` in the class `a`. -/
def wcls (q a n : ℕ) : ℝ := if Nat.Prime n ∧ q < n ∧ n % q = a then w n else 0

theorem wq_nonneg (q n : ℕ) : 0 ≤ wq q n := by unfold wq; split_ifs <;> simp [w_nonneg]

theorem wcls_nonneg (q a n : ℕ) : 0 ≤ wcls q a n := by
  unfold wcls; split_ifs <;> simp [w_nonneg]

theorem wcls_le_wq (q a n : ℕ) : wcls q a n ≤ wq q n := by
  unfold wcls wq
  by_cases h1 : Nat.Prime n ∧ q < n ∧ n % q = a
  · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1⟩]
  · rw [if_neg h1]
    split_ifs
    · exact w_nonneg n
    · exact le_refl _

/-- The partial sums of `wq q`: for `N ≥ q + 1`, `∑_{n < N} wq q n = cfun (q+1) − cfun N`. -/
theorem sum_range_wq {q N : ℕ} (hN : q + 1 ≤ N) :
    ∑ n ∈ range N, wq q n = cfun (q + 1) - cfun N := by
  have hsplit : range N = range (q + 1) ∪ Ioc q (N - 1) := by
    ext n; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (range (q + 1)) (Ioc q (N - 1)) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_range] at h1; simp only [Finset.mem_Ioc] at h2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have h0 : ∑ n ∈ range (q + 1), wq q n = 0 := by
    apply Finset.sum_eq_zero; intro n hn
    simp only [Finset.mem_range] at hn
    unfold wq; rw [if_neg]; omega
  have h1 : ∑ n ∈ Ioc q (N - 1), wq q n = ∑ n ∈ Ioc q (N - 1), (if Nat.Prime n then w n else 0) := by
    apply Finset.sum_congr rfl; intro n hn
    simp only [Finset.mem_Ioc] at hn
    unfold wq; simp [hn.1]
  rw [h0, h1, sum_w_Ioc q (N - 1) (by omega), zero_add]
  congr 2; omega

theorem sum_range_wq_le (q N : ℕ) : ∑ n ∈ range N, wq q n ≤ cfun (q + 1) := by
  rcases le_or_gt (q + 1) N with h | h
  · rw [sum_range_wq h]; linarith [cfun_nonneg N]
  · rw [Finset.sum_eq_zero]
    · exact cfun_nonneg _
    · intro n hn; simp only [Finset.mem_range] at hn; unfold wq; rw [if_neg]; omega

theorem summable_wq (q : ℕ) : Summable (wq q) :=
  summable_of_sum_range_le (wq_nonneg q) (sum_range_wq_le q)

/-- **The weights sum to the density of the `q`-rough integers.** -/
theorem hasSum_wq (q : ℕ) : HasSum (wq q) (cfun (q + 1)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (wq_nonneg q)]
  have h : Filter.Tendsto (fun N => cfun (q + 1) - cfun N) Filter.atTop (nhds (cfun (q + 1) - 0)) :=
    tendsto_const_nhds.sub cfun_tendsto_zero
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (q + 1)] with N hN
  exact (sum_range_wq hN).symm

theorem summable_wcls (q a : ℕ) : Summable (wcls q a) :=
  Summable.of_nonneg_of_le (wcls_nonneg q a) (wcls_le_wq q a) (summable_wq q)

/-- The tail of the class sum beyond `P ≥ q` is at most `cfun (P+1)`. -/
theorem tsum_wcls_tail_le {q P : ℕ} (hqP : q ≤ P) (a : ℕ) :
    ∑' n, wcls q a n - ∑ n ∈ range (P + 1), wcls q a n ≤ cfun (P + 1) := by
  have hsum := (summable_wcls q a).sum_add_tsum_nat_add (P + 1)
  rw [← hsum, add_sub_cancel_left]
  -- the shifted tail of `wcls q a` is dominated by `wq P`, which sums to `cfun (P+1)`
  have hle : ∀ i, wcls q a (i + (P + 1)) ≤ wq P (i + (P + 1)) := by
    intro i
    refine (wcls_le_wq q a _).trans (le_of_eq ?_)
    unfold wq
    by_cases hp : Nat.Prime (i + (P + 1))
    · rw [if_pos ⟨hp, by omega⟩, if_pos ⟨hp, by omega⟩]
    · rw [if_neg (fun h => hp h.1), if_neg (fun h => hp h.1)]
  have hsumP : Summable (fun i => wq P (i + (P + 1))) :=
    (summable_wq P).comp_injective (add_left_injective (P + 1))
  calc ∑' i, wcls q a (i + (P + 1))
      ≤ ∑' i, wq P (i + (P + 1)) :=
        ((summable_wcls q a).comp_injective (add_left_injective (P + 1))).tsum_le_tsum hle hsumP
    _ = ∑' n, wq P n - ∑ n ∈ range (P + 1), wq P n := by
        rw [← (summable_wq P).sum_add_tsum_nat_add (P + 1)]; ring
    _ = cfun (P + 1) := by
        rw [(hasSum_wq P).tsum_eq, sum_range_wq (le_refl _), sub_self, sub_zero]

/-- The finite class head `∑_{n ≤ P} wcls q a n` is the sum of `w` over the primes in the class
up to `P`. -/
theorem sum_range_wcls (q a P : ℕ) :
    ∑ n ∈ range (P + 1), wcls q a n =
      ∑ p ∈ (Ioc q P).filter (fun p => Nat.Prime p ∧ p % q = a), w p := by
  unfold wcls
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h3, by omega⟩, h2, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨by omega, h3, h1, h4⟩
  · intros; rfl

/-- `⌊X/d⌋ ≥ X/d − 1` and `⌊X/d⌋ ≤ X/d` in `ℝ`. -/
theorem nat_div_bounds (X d : ℕ) (hd : 0 < d) :
    (X : ℝ) / d - 1 ≤ ((X / d : ℕ) : ℝ) ∧ ((X / d : ℕ) : ℝ) ≤ (X : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · rw [sub_le_iff_le_add, div_le_iff₀ hd']
    have := Nat.lt_div_mul_add hd (a := X)
    have h2 : (X : ℝ) < ((X / d : ℕ) : ℝ) * d + d := by exact_mod_cast this
    linarith
  · rw [le_div_iff₀ hd']
    exact_mod_cast Nat.div_mul_le_self X d

theorem w_eq (p : ℕ) : w p = (Apr p : ℝ) / (p * Npr p) := by
  unfold w cfun; rw [div_div, mul_comm]

/-- **Density of the rough integers**: `roughCount q X / X → cfun (q+1)`. -/
theorem tendsto_roughCount_div (q : ℕ) :
    Filter.Tendsto (fun X : ℕ => (roughCount q X : ℝ) / X) Filter.atTop (nhds (cfun (q + 1))) := by
  set N := Npr (q + 1) with hN
  set A := Apr (q + 1) with hA
  have hNpos : 0 < N := Npr_pos _
  have hcf : cfun (q + 1) = (A : ℝ) / N := rfl
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := exists_nat_gt (((A : ℝ) + 1) / ε)
  refine ⟨max X₀ 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hXX₀ : (X₀ : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_left _ _) hX
  have hlo := roughCount_ge q X
  have hhi := roughCount_le q X
  rw [totient_Npr] at hlo hhi
  obtain ⟨hd1, hd2⟩ := nat_div_bounds X N hNpos
  have hlo' : ((X : ℝ) / N - 1) * A ≤ (roughCount q X : ℝ) + 1 := by
    have : (((X / N : ℕ) : ℝ)) * A ≤ (roughCount q X : ℝ) + 1 := by exact_mod_cast hlo
    exact (mul_le_mul_of_nonneg_right hd1 (Nat.cast_nonneg A)).trans this
  have hhi' : (roughCount q X : ℝ) ≤ ((X : ℝ) / N + 1) * A := by
    have : (roughCount q X : ℝ) ≤ (((X / N : ℕ) : ℝ) + 1) * A := by exact_mod_cast hhi
    exact this.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg A))
  rw [Real.dist_eq, hcf, abs_lt]
  have hkey : (A : ℝ) + 1 < ε * X := by
    have : ((A : ℝ) + 1) / ε < X := lt_of_lt_of_le hX₀ hXX₀
    rw [div_lt_iff₀ hε] at this; linarith
  set c := (A : ℝ) / N with hc
  have h1 : ((X : ℝ) / N - 1) * A = X * c - A := by rw [hc]; ring
  have h2 : ((X : ℝ) / N + 1) * A = X * c + A := by rw [hc]; ring
  rw [h1] at hlo'; rw [h2] at hhi'
  have hR : ((roughCount q X : ℝ)) / X = (roughCount q X : ℝ) * (1 / X) := by ring
  have hlow : c - ε < (roughCount q X : ℝ) / X := by
    rw [lt_div_iff₀ hXpos]; nlinarith
  have hup : (roughCount q X : ℝ) / X < c + ε := by
    rw [div_lt_iff₀ hXpos]; nlinarith
  constructor <;> linarith

/-- Below `P`, the class set contains the disjoint union of `{minFac m = p}` over the primes `p`
of the class in `(q, P]`. -/
theorem classCount_ge (q a P X : ℕ) :
    ∑ p ∈ (Ioc q P).filter (fun p => Nat.Prime p ∧ p % q = a),
        ((Icc 2 X).filter (fun m => Nat.minFac m = p)).card ≤ classCount q a X := by
  set H := (Ioc q P).filter (fun p => Nat.Prime p ∧ p % q = a) with hH
  set t : ℕ → Finset ℕ := fun p => (Icc 2 X).filter (fun m => Nat.minFac m = p) with ht
  have hdisj : (H : Set ℕ).PairwiseDisjoint t := by
    intro p _ p' _ hne
    rw [Function.onFun, ht]
    exact Finset.disjoint_filter.mpr fun m _ h1 h2 => hne (h1.symm.trans h2)
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro m hm
  obtain ⟨p, hp, hmp⟩ := Finset.mem_biUnion.mp hm
  rw [hH, Finset.mem_filter, Finset.mem_Ioc] at hp
  rw [ht, Finset.mem_filter] at hmp
  rw [Finset.mem_filter]
  exact ⟨hmp.1, by rw [hmp.2]; exact hp.1.1, by rw [hmp.2]; exact hp.2.2⟩

/-- Above `P`, the class set lies in the `P`-rough integers. -/
theorem classCount_le (q a P X : ℕ) (_hqP : q ≤ P) :
    classCount q a X ≤
      (∑ p ∈ (Ioc q P).filter (fun p => Nat.Prime p ∧ p % q = a),
        ((Icc 2 X).filter (fun m => Nat.minFac m = p)).card) + roughCount P X := by
  set H := (Ioc q P).filter (fun p => Nat.Prime p ∧ p % q = a) with hH
  set t : ℕ → Finset ℕ := fun p => (Icc 2 X).filter (fun m => Nat.minFac m = p) with ht
  have hsub : (Icc 2 X).filter (fun m => q < Nat.minFac m ∧ Nat.minFac m % q = a) ⊆
      H.biUnion t ∪ (Icc 2 X).filter (fun m => P < Nat.minFac m) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨hm2, hmX⟩, hq, ha⟩ := hm
    rw [Finset.mem_union]
    rcases le_or_gt (Nat.minFac m) P with hle | hlt
    · left
      refine Finset.mem_biUnion.mpr ⟨Nat.minFac m, ?_, ?_⟩
      · rw [hH, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hq, hle⟩, Nat.minFac_prime (by omega), ha⟩
      · rw [ht, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hm2, hmX⟩, rfl⟩
    · right
      rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hm2, hmX⟩, hlt⟩
  unfold classCount roughCount
  calc ((Icc 2 X).filter (fun m => q < Nat.minFac m ∧ Nat.minFac m % q = a)).card
      ≤ (H.biUnion t ∪ (Icc 2 X).filter (fun m => P < Nat.minFac m)).card :=
        Finset.card_le_card hsub
    _ ≤ (H.biUnion t).card + ((Icc 2 X).filter (fun m => P < Nat.minFac m)).card :=
        Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right Finset.card_biUnion_le _

/-- **Density of a residue class of the least prime factor.**
`classCount q a X / X → ∑_{p ≡ a (q), p > q} w_p`. -/
theorem tendsto_classCount_div (q a : ℕ) :
    Filter.Tendsto (fun X : ℕ => (classCount q a X : ℝ) / X) Filter.atTop
      (nhds (∑' n, wcls q a n)) := by
  set L := ∑' n, wcls q a n with hL
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P₀, hP₀⟩ := (Metric.tendsto_atTop.mp cfun_tendsto_zero) (ε / 3) (by positivity)
  set P := max q P₀ with hP
  have hqP : q ≤ P := le_max_left _ _
  have hcP : cfun (P + 1) < ε / 3 := by
    have := hP₀ (P + 1) (by have := le_max_right q P₀; omega)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (cfun_nonneg _)] at this
  set H := (Ioc q P).filter (fun p => Nat.Prime p ∧ p % q = a) with hH
  set S := ∑ p ∈ H, w p with hS
  have hSL : S ≤ L := by
    rw [hS, ← sum_range_wcls]
    exact (summable_wcls q a).sum_le_tsum _ (fun n _ => wcls_nonneg q a n)
  have hLS : L - S ≤ cfun (P + 1) := by
    rw [hS, ← sum_range_wcls]; exact tsum_wcls_tail_le hqP a
  set K : ℝ := (∑ p ∈ H, (Apr p : ℝ)) + Apr (P + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨X₀, hX₀⟩ := exists_nat_gt (3 * K / ε)
  refine ⟨max X₀ 1, fun X hX => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hXX₀ : (X₀ : ℝ) ≤ X := by exact_mod_cast le_trans (le_max_left _ _) hX
  have hKX : K < ε / 3 * X := by
    have : 3 * K / ε < X := lt_of_lt_of_le hX₀ hXX₀
    rw [div_lt_iff₀ hε] at this; linarith
  -- lower bound: `X·S − ∑_H Apr ≤ classCount`
  have hlow : (X : ℝ) * S - ∑ p ∈ H, (Apr p : ℝ) ≤ classCount q a X := by
    have h1 := classCount_ge q a P X
    have h2 : ∀ p ∈ H, (X : ℝ) * w p - Apr p ≤
        (((Icc 2 X).filter (fun m => Nat.minFac m = p)).card : ℝ) := by
      intro p hp
      have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
      have hcount := card_minFac_eq_ge hp' X
      have hd := (nat_div_bounds X (p * Npr p) (Nat.mul_pos hp'.pos (Npr_pos p))).1
      push_cast at hd
      rw [w_eq]
      calc (X : ℝ) * ((Apr p : ℝ) / (p * Npr p)) - Apr p
          = ((X : ℝ) / (p * Npr p) - 1) * Apr p := by ring
        _ ≤ ((X / (p * Npr p) : ℕ) : ℝ) * Apr p :=
            mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg _)
        _ ≤ _ := by exact_mod_cast hcount
    calc (X : ℝ) * S - ∑ p ∈ H, (Apr p : ℝ)
        = ∑ p ∈ H, ((X : ℝ) * w p - Apr p) := by
          rw [hS, Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ ∑ p ∈ H, (((Icc 2 X).filter (fun m => Nat.minFac m = p)).card : ℝ) :=
          Finset.sum_le_sum h2
      _ ≤ classCount q a X := by exact_mod_cast h1
  -- upper bound: `classCount ≤ X·(S + cfun (P+1)) + K`
  have hup : (classCount q a X : ℝ) ≤ X * (S + cfun (P + 1)) + K := by
    have h1 := classCount_le q a P X hqP
    have h2 : ∀ p ∈ H, (((Icc 2 X).filter (fun m => Nat.minFac m = p)).card : ℝ) ≤
        (X : ℝ) * w p + Apr p := by
      intro p hp
      have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
      have hcount := card_minFac_eq_le hp' X
      have hd := (nat_div_bounds X (p * Npr p) (Nat.mul_pos hp'.pos (Npr_pos p))).2
      push_cast at hd
      rw [w_eq]
      calc (((Icc 2 X).filter (fun m => Nat.minFac m = p)).card : ℝ)
          ≤ (((X / (p * Npr p) : ℕ) : ℝ) + 1) * Apr p := by exact_mod_cast hcount
        _ ≤ ((X : ℝ) / (p * Npr p) + 1) * Apr p :=
            mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ = (X : ℝ) * ((Apr p : ℝ) / (p * Npr p)) + Apr p := by ring
    have h3 : (roughCount P X : ℝ) ≤ X * cfun (P + 1) + Apr (P + 1) := by
      have hcount := roughCount_le P X
      rw [totient_Npr] at hcount
      have hd := (nat_div_bounds X (Npr (P + 1)) (Npr_pos _)).2
      calc (roughCount P X : ℝ)
          ≤ (((X / Npr (P + 1) : ℕ) : ℝ) + 1) * Apr (P + 1) := by exact_mod_cast hcount
        _ ≤ ((X : ℝ) / Npr (P + 1) + 1) * Apr (P + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        _ = X * cfun (P + 1) + Apr (P + 1) := by unfold cfun; ring
    calc (classCount q a X : ℝ)
        ≤ (∑ p ∈ H, (((Icc 2 X).filter (fun m => Nat.minFac m = p)).card : ℝ)) +
            roughCount P X := by exact_mod_cast h1
      _ ≤ (∑ p ∈ H, ((X : ℝ) * w p + Apr p)) + (X * cfun (P + 1) + Apr (P + 1)) :=
          add_le_add (Finset.sum_le_sum h2) h3
      _ = X * (S + cfun (P + 1)) + K := by
          rw [hS, hK, Finset.sum_add_distrib, mul_add, Finset.mul_sum]; ring
  -- conclude
  rw [Real.dist_eq, abs_lt]
  have hApr_le_K : ∑ p ∈ H, (Apr p : ℝ) ≤ K := by
    rw [hK]; linarith [(Nat.cast_nonneg (Apr (P + 1)) : (0:ℝ) ≤ Apr (P + 1))]
  have hlow' : L - 2 * (ε / 3) < (classCount q a X : ℝ) / X := by
    rw [lt_div_iff₀ hXpos]; nlinarith
  have hup' : (classCount q a X : ℝ) / X < L + 2 * (ε / 3) := by
    rw [div_lt_iff₀ hXpos]; nlinarith
  constructor <;> linarith

/-! ## Part 7: the characterization -/

/-- **`RoughLPFEquidist q` is an identity between convergent series.**  It holds iff for every
coprime class `a`, `∑_{p ≡ a (q), p > q} w_p = cfun (q+1)/(q−1)`.  Dirichlet's theorem, and
indeed any statement about counting functions of primes, is silent about the left-hand side:
the series converges, its value is dominated by the first primes above `q`, and whether it
splits evenly is a question about the arithmetic of those primes. -/
theorem roughLPFEquidist_iff (q : ℕ) :
    RoughLPFEquidist q ↔
      ∀ a : ℕ, 0 < a → a < q → Nat.Coprime a q →
        ∑' n, wcls q a n = cfun (q + 1) / (q - 1 : ℝ) := by
  constructor
  · intro h a ha haq hcop
    obtain ⟨c, _, h1, h2⟩ := h a ha haq hcop
    have hc : c = cfun (q + 1) := tendsto_nhds_unique h1 (tendsto_roughCount_div q)
    have hL : c / (q - 1 : ℝ) = ∑' n, wcls q a n :=
      tendsto_nhds_unique h2 (tendsto_classCount_div q a)
    rw [← hL, hc]
  · intro h a ha haq hcop
    refine ⟨cfun (q + 1), cfun_pos _, tendsto_roughCount_div q, ?_⟩
    have := tendsto_classCount_div q a
    rwa [h a ha haq hcop] at this

/-- **The registered open point `PrimesEquidistAsympImpliesRoughLPF` is a family of series
identities.**  Its hypothesis is a theorem (`IK.primesEquidistInAP_asymp_proved`), so it says
exactly that `∑_{p ≡ a (q), p > q} w_p = cfun (q+1)/(q−1)` for every prime `q` and coprime `a`. -/
theorem primesEquidistAsympImpliesRoughLPF_iff :
    PrimesEquidistAsympImpliesRoughLPF ↔
      ∀ q : ℕ, Nat.Prime q → ∀ a : ℕ, 0 < a → a < q → Nat.Coprime a q →
        ∑' n, wcls q a n = cfun (q + 1) / (q - 1 : ℝ) := by
  constructor
  · intro h q hq
    exact (roughLPFEquidist_iff q).mp (h IK.primesEquidistInAP_asymp_proved q hq)
  · intro h _ q hq
    exact (roughLPFEquidist_iff q).mpr (h q hq)

/-- **The head-domination criterion.**  If a finite set `H` of primes `p > q` in the class `a`
already carries more than the equidistributed share, `RoughLPFEquidist q` fails.  (Every term
of the class series is nonnegative, so a partial sum bounds the whole.) -/
theorem not_roughLPFEquidist_of_head {q a : ℕ} (ha : 0 < a) (haq : a < q)
    (hcop : Nat.Coprime a q) (H : Finset ℕ)
    (hH : ∀ p ∈ H, Nat.Prime p ∧ q < p ∧ p % q = a)
    (hhead : cfun (q + 1) / (q - 1 : ℝ) < ∑ p ∈ H, w p) :
    ¬ RoughLPFEquidist q := by
  rw [roughLPFEquidist_iff]
  intro h
  have hid := h a ha haq hcop
  have hle : ∑ p ∈ H, w p ≤ ∑' n, wcls q a n := by
    calc ∑ p ∈ H, w p = ∑ p ∈ H, wcls q a p := by
          apply Finset.sum_congr rfl
          intro p hp; unfold wcls; rw [if_pos (hH p hp)]
      _ ≤ ∑' n, wcls q a n :=
          (summable_wcls q a).sum_le_tsum _ (fun n _ => wcls_nonneg q a n)
  linarith

/-- The class densities of the coprime classes add up to the density of the rough integers:
`∑_a ∑' wcls q a = cfun (q+1)` for prime `q` (every prime `p > q` lies in exactly one coprime
class).  Together with `roughLPFEquidist_iff`, equidistribution says the `q − 1` summands are
equal — a constraint on the *arithmetic* of the primes just above `q`, not on their asymptotic
counting. -/
theorem sum_tsum_wcls {q : ℕ} (hq : Nat.Prime q) :
    ∑ a ∈ (range q).filter (fun a => 0 < a), ∑' n, wcls q a n = cfun (q + 1) := by
  rw [← (hasSum_wq q).tsum_eq,
    ← Summable.tsum_finsetSum (fun a _ => summable_wcls q a)]
  apply tsum_congr
  intro n
  unfold wcls wq
  by_cases hn : Nat.Prime n ∧ q < n
  · rw [if_pos hn]
    have hmod : 0 < n % q := by
      rcases Nat.eq_zero_or_pos (n % q) with h0 | hpos
      · exfalso
        have hdvd : q ∣ n := Nat.dvd_of_mod_eq_zero h0
        have := (Nat.prime_dvd_prime_iff_eq hq hn.1).mp hdvd
        omega
      · exact hpos
    rw [Finset.sum_eq_single (n % q)]
    · rw [if_pos ⟨hn.1, hn.2, rfl⟩]
    · intro b _ hb; rw [if_neg]; intro h; exact hb h.2.2.symm
    · intro h; exfalso; apply h
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt n hq.pos, hmod⟩
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro a _; rw [if_neg]; intro h; exact hn ⟨h.1, h.2.1⟩

end HeadDomination

end
