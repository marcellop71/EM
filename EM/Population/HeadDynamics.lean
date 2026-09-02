import EM.Population.ClassInfinitude
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# The head: Mullin's conjecture as an extremal compositeness statement

Let the **head** `head n` be the least prime not among `seq 0, …, seq n` (the least missing
prime).  The next multiplier `seq (n+1) = lpf (E_n)` is a missing prime, so

    head n ≤ seq (n+1)                                  (`head_le_seq_succ`),

with equality exactly when the head is captured.  The head is nondecreasing and moves only when
captured (`head_succ_eq_or`, `head_lt_of_captured`).  Hence:

* **MC ⟺ `head n → ∞`** (`mullin_iff_head_tendsto`);
* **MC ⟺ the head is captured infinitely often ⟺ `lpf (E_n)` attains its trivial lower bound
  `head n` infinitely often** (`mullin_iff_head_captured_io`);
* **MC ⟺ the least prime factor of the Euclid number is bounded by *some* function of the
  head** (`mullin_iff_exists_bound`): MC fails iff the head stalls while the multipliers, being
  distinct primes, escape to infinity.

The last form makes the ladder `(C∞) ⇐ (S) ⇐ RD ⇐ MC` legible as a hierarchy of "the least
factor is small": `lpf(E_n) ≤ E_n^{1/2}` i.o.; `lpf(E_n) < 2^{n−c}` i.o.; `∑ 1/lpf(E_n) = ∞`;
`lpf(E_n) = head n` i.o.  Mullin's conjecture is the top rung — the Euclid number is as composed
as it can possibly be, infinitely often — and nothing weaker suffices: a sequence whose least
factor is always the *second* missing prime satisfies every lower rung and fails MC.

## Non-confinement and the composite floor

On the perpetual-primality branch from `N₁` every late multiplier is `E_n = P_n + 1 ≡ 1` modulo
`prod N₁` (`perpetual_seq_mod_prod`).  So

    NotConfined := ∀ N ≥ 1, ∃ n ≥ N, seq (n+1) ≢ 1 (mod prod N)

implies `(C∞)` (`notConfined_implies_infinitelyManyComposite`); `NotConfined` is implied by MC
(via Dirichlet: infinitely many primes `≡ −1 (mod prod N)` all appear) and by `CI(2 mod 3)`.
The ladder near the floor is therefore

    MC ⟹ CI(2 mod 3) ⟹ NotConfined ⟹ (C∞),      ¬CI(3 mod 4) ⟹ (C∞),      CI(1 mod 4) ⟹ (C∞).

## Two structural facts about consecutive Euclid numbers

* Consecutive Euclid numbers are coprime (`coprime_euclid_succ`): a common prime `r` would give
  `seq (n+1) ≡ 1 (mod r)` with `2 ≤ seq (n+1) ≤ r`.
* A prime hit at stage `n` (`r ∣ E_n`) divides `E_m`, `m > n`, iff the product of the multipliers
  `seq (n+1) ⋯ seq m` is `≡ 1 (mod r)` (`dvd_euclid_iff_prod_mul_eq_one`): after its first hit, a
  prime's future hits are returns of the multiplier product to the identity.

See `docs/analysis/compositeness_2026-09-02.md`.
-/

open Mullin Euclid
open scoped Classical

namespace HeadDynamics

/-! ## 1. The bag and the head -/

/-- `q` lies in the bag at stage `n`. -/
def InBag (n q : ℕ) : Prop := ∃ k ≤ n, seq k = q

/-- `q` is missing at stage `n`: a prime not in the bag. -/
def Missing (n q : ℕ) : Prop := Nat.Prime q ∧ ¬ InBag n q

theorem inBag_mono {n q : ℕ} (h : InBag n q) : InBag (n + 1) q := by
  obtain ⟨k, hk, hkq⟩ := h; exact ⟨k, by omega, hkq⟩

theorem missing_of_missing_succ {n q : ℕ} (h : Missing (n + 1) q) : Missing n q :=
  ⟨h.1, fun hb => h.2 (inBag_mono hb)⟩

/-- The next multiplier is missing at stage `n`. -/
theorem missing_seq_succ (n : ℕ) : Missing n (seq (n + 1)) := by
  refine ⟨EuclidClasses.seq_nat_prime _, ?_⟩
  rintro ⟨k, hk, hkq⟩
  have := seq_injective k (n + 1) hkq
  omega

theorem exists_missing (n : ℕ) : ∃ q, Missing n q := ⟨_, missing_seq_succ n⟩

/-- **The head**: the least missing prime at stage `n`. -/
noncomputable def head (n : ℕ) : ℕ := Nat.find (exists_missing n)

theorem head_missing (n : ℕ) : Missing n (head n) := Nat.find_spec (exists_missing n)

theorem head_prime (n : ℕ) : Nat.Prime (head n) := (head_missing n).1

theorem head_le {n q : ℕ} (hq : Missing n q) : head n ≤ q := Nat.find_min' (exists_missing n) hq

theorem inBag_of_prime_lt_head {n q : ℕ} (hq : Nat.Prime q) (hlt : q < head n) : InBag n q := by
  by_contra h
  exact absurd (head_le ⟨hq, h⟩) (by omega)

/-- `head n ≤ lpf (E_n)`. -/
theorem head_le_seq_succ (n : ℕ) : head n ≤ seq (n + 1) := head_le (missing_seq_succ n)

theorem head_mono (n : ℕ) : head n ≤ head (n + 1) :=
  head_le (missing_of_missing_succ (head_missing (n + 1)))

theorem head_monotone : Monotone head := monotone_nat_of_le_succ head_mono

/-- The head moves only when it is captured. -/
theorem head_succ_eq_or (n : ℕ) : head (n + 1) = head n ∨ seq (n + 1) = head n := by
  by_cases h : seq (n + 1) = head n
  · exact Or.inr h
  · left
    have hmiss : Missing (n + 1) (head n) := by
      refine ⟨head_prime n, ?_⟩
      rintro ⟨k, hk, hkq⟩
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · exact (head_missing n).2 ⟨k, by omega, hkq⟩
      · have : k = n + 1 := by omega
        exact h (this ▸ hkq)
    exact le_antisymm (head_le hmiss) (head_mono n)

/-- A capture moves the head strictly. -/
theorem head_lt_of_captured {n : ℕ} (h : seq (n + 1) = head n) : head n < head (n + 1) := by
  have hle := head_mono n
  have hne : head (n + 1) ≠ head n := by
    intro heq
    have hm := head_missing (n + 1)
    exact hm.2 ⟨n + 1, le_rfl, by rw [h, heq]⟩
  omega

/-- **Head capture is a hit**: if the head divides the Euclid number, it is selected. -/
theorem seq_succ_eq_head_of_dvd {n : ℕ} (h : head n ∣ prod n + 1) : seq (n + 1) = head n := by
  apply captures_target (Nat.prime_def_lt.mp (head_prime n) |> fun ⟨h2, hd⟩ => ⟨h2, fun d hdvd => ?_⟩) h
  · intro p hp hpp
    obtain ⟨k, hk, hkp⟩ := inBag_of_prime_lt_head (Nat.prime_def_lt.mpr ⟨hpp.1,
      fun m hm hmd => (hpp.2 m hmd).resolve_right (ne_of_lt hm)⟩) hp
    exact ⟨k, hk, hkp⟩
  · exact (Nat.dvd_prime (head_prime n)).mp hdvd

/-! ## 2. Mullin's conjecture through the head -/

theorem head_gt_of_all_appear {B n : ℕ} (hall : ∀ q, Nat.Prime q → q ≤ B → InBag n q) :
    B < head n := by
  by_contra h
  exact (head_missing n).2 (hall _ (head_prime n) (by omega))

/-- **MC ⟺ the head tends to infinity.** -/
theorem mullin_iff_head_tendsto : MullinConjecture ↔ Filter.Tendsto head Filter.atTop Filter.atTop := by
  constructor
  · intro hmc
    rw [Filter.tendsto_atTop_atTop]
    intro B
    -- every prime `≤ B` appears at some stage; take the max of those stages
    have hstage : ∀ q, Nat.Prime q → q ≤ B → ∃ k, seq k = q := fun q hq _ =>
      hmc q (Nat.prime_def_lt.mp hq |> fun ⟨h2, hd⟩ => ⟨h2, fun d hdvd => by
        rcases Nat.lt_or_ge d q with hlt | hge
        · exact Or.inl (hd d hlt hdvd)
        · exact Or.inr (Nat.le_antisymm (Nat.le_of_dvd hq.pos hdvd) hge)⟩)
    classical
    let stage : ℕ → ℕ := fun q => if h : Nat.Prime q ∧ q ≤ B then Nat.find (hstage q h.1 h.2) else 0
    refine ⟨(Finset.range (B + 1)).sup stage, fun n hn => le_of_lt (head_gt_of_all_appear ?_)⟩
    intro q hq hqB
    have hk : seq (Nat.find (hstage q hq hqB)) = q := Nat.find_spec (hstage q hq hqB)
    refine ⟨Nat.find (hstage q hq hqB), le_trans ?_ hn, hk⟩
    have : stage q = Nat.find (hstage q hq hqB) := by simp [stage, hq, hqB]
    rw [← this]
    exact Finset.le_sup (f := stage) (Finset.mem_range.mpr (by omega))
  · intro ht q hq
    have hq' : Nat.Prime q := Nat.prime_def_lt.mpr ⟨hq.1, fun m hm hmd => (hq.2 m hmd).resolve_right (ne_of_lt hm)⟩
    rw [Filter.tendsto_atTop_atTop] at ht
    obtain ⟨N, hN⟩ := ht (q + 1)
    obtain ⟨k, _, hk⟩ := inBag_of_prime_lt_head hq' (show q < head N from by have := hN N le_rfl; omega)
    exact ⟨k, hk⟩

/-- Eventually constant head ⟹ no capture from that stage on. -/
theorem head_eq_of_no_capture {N n : ℕ} (hN : N ≤ n) (h : ∀ m, N ≤ m → seq (m + 1) ≠ head m) :
    head n = head N := by
  induction n with
  | zero => have : N = 0 := by omega
            subst this; rfl
  | succ n ih =>
    rcases Nat.lt_or_ge N (n + 1) with hlt | hge
    · have := ih (by omega)
      rcases head_succ_eq_or n with h1 | h2
      · rw [h1, this]
      · exact absurd h2 (h n (by omega))
    · have : N = n + 1 := by omega
      subst this; rfl

/-- **MC ⟺ the head is captured infinitely often** (the least prime factor of the Euclid number
attains its trivial lower bound infinitely often). -/
theorem mullin_iff_head_captured_io :
    MullinConjecture ↔ ∀ N, ∃ n, N ≤ n ∧ seq (n + 1) = head n := by
  rw [mullin_iff_head_tendsto]
  constructor
  · intro ht N
    by_contra h
    push Not at h
    have hconst : ∀ n, N ≤ n → head n = head N := fun n hn => head_eq_of_no_capture hn h
    rw [Filter.tendsto_atTop_atTop] at ht
    obtain ⟨M, hM⟩ := ht (head N + 1)
    have := hM (max M N) (le_max_left _ _)
    rw [hconst _ (le_max_right _ _)] at this
    omega
  · intro hcap
    rw [Filter.tendsto_atTop_atTop]
    intro B
    -- the head strictly increases at each of `B` captures, so eventually exceeds `B`
    suffices ∀ k : ℕ, ∃ n, k ≤ head n by
      obtain ⟨n, hn⟩ := this B
      exact ⟨n, fun m hm => le_trans hn (head_monotone hm)⟩
    intro k
    induction k with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨m, hm, hcapm⟩ := hcap n
      refine ⟨m + 1, ?_⟩
      have h1 := head_lt_of_captured hcapm
      have h2 := head_monotone hm
      omega

/-- **MC ⟺ the least prime factor of the Euclid number is bounded by some function of the head.**
MC fails iff the head stalls while the multipliers escape to infinity. -/
theorem mullin_iff_exists_bound :
    MullinConjecture ↔ ∃ f : ℕ → ℕ, ∀ n, seq (n + 1) ≤ f (head n) := by
  constructor
  · intro hmc
    have ht := mullin_iff_head_tendsto.mp hmc
    rw [Filter.tendsto_atTop_atTop] at ht
    -- for each `q` choose a stage after which the head exceeds `q`
    have hstage : ∀ q : ℕ, ∃ N, ∀ n, N ≤ n → q + 1 ≤ head n := fun q => ht (q + 1)
    classical
    refine ⟨fun q => (Finset.range (Nat.find (hstage q) + 1)).sup (fun n => seq (n + 1)), fun n => ?_⟩
    set q := head n with hq
    have hspec := Nat.find_spec (hstage q)
    have hn : n < Nat.find (hstage q) := by
      by_contra h
      have := hspec n (by omega)
      omega
    exact Finset.le_sup (f := fun n => seq (n + 1)) (Finset.mem_range.mpr (by omega))
  · rintro ⟨f, hf⟩
    rw [mullin_iff_head_tendsto]
    by_contra hnot
    -- a monotone sequence that does not tend to infinity is bounded, hence eventually constant
    have hbdd : ∃ B, ∀ n, head n ≤ B := by
      by_contra h
      push Not at h
      apply hnot
      rw [Filter.tendsto_atTop_atTop]
      intro B
      obtain ⟨n, hn⟩ := h B
      exact ⟨n, fun m hm => le_trans hn.le (head_monotone hm)⟩
    obtain ⟨B, hB⟩ := hbdd
    -- the multipliers are then bounded by `max_{q ≤ B} f q`, contradicting injectivity
    classical
    let M := (Finset.range (B + 1)).sup f
    have hseq : ∀ n, seq (n + 1) ≤ M := fun n =>
      le_trans (hf n) (Finset.le_sup (f := f) (Finset.mem_range.mpr (by have := hB n; omega)))
    -- `seq` is injective on `M + 2` indices, all with values `≤ M`: pigeonhole
    have hinj : Set.InjOn (fun n => seq (n + 1)) (Finset.range (M + 2) : Set ℕ) :=
      fun a _ b _ h => by have := seq_injective (a + 1) (b + 1) h; omega
    have hcard := Finset.card_le_card_of_injOn (fun n => seq (n + 1)) (t := Finset.range (M + 1))
      (fun n _ => Finset.mem_range.mpr (by show seq (n + 1) < M + 1; have := hseq n; omega)) hinj
    simp at hcard

/-! ## 3. Non-confinement and the composite floor -/

theorem prod_dvd_prod_of_le {N n : ℕ} (h : N ≤ n) : prod N ∣ prod n := by
  induction n with
  | zero => have : N = 0 := by omega
            subst this; exact dvd_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge N (n + 1) with hlt | hge
    · rw [prod_succ]; exact Dvd.dvd.mul_right (ih (by omega)) _
    · have : N = n + 1 := by omega
      subst this; exact dvd_rfl

open AutonomousBranch

/-- On the perpetual-primality branch every late multiplier is `≡ 1` modulo `prod N₁`. -/
theorem perpetual_seq_mod_prod {N₁ : ℕ} (hpp : PerpetualPrimality N₁) {n : ℕ} (hn : N₁ ≤ n) :
    seq (n + 1) % prod N₁ = 1 := by
  rw [perpetual_seq_succ hpp hn]
  obtain ⟨k, hk⟩ := prod_dvd_prod_of_le hn
  have h2 := prod_ge_two N₁
  rw [hk, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- **Non-confinement**: the multipliers are not eventually `≡ 1` modulo the current accumulator. -/
def NotConfined : Prop := ∀ N, 1 ≤ N → ∃ n, N ≤ n ∧ seq (n + 1) % prod N ≠ 1

/-- **`NotConfined ⟹ (C∞)`.** -/
theorem notConfined_implies_infinitelyManyComposite (h : NotConfined) : InfinitelyManyComposite := by
  by_contra hc
  obtain ⟨N₁, hpp⟩ := EuclidClasses.exists_perpetual_of_not_infinitelyManyComposite hc
  have hpp' : PerpetualPrimality (max N₁ 1) := fun n hn => hpp n (le_trans (le_max_left _ _) hn)
  obtain ⟨n, hn, hne⟩ := h (max N₁ 1) (le_max_right _ _)
  exact hne (perpetual_seq_mod_prod hpp' hn)

/-- `CI(2 mod 3) ⟹ NotConfined`. -/
theorem classInfinitude_two_mod_three_implies_notConfined
    (h : EuclidClasses.ClassInfinitude 3 2) : NotConfined := by
  intro N hN
  obtain ⟨k, hk, hk2⟩ := h (N + 1)
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  refine ⟨n, by omega, ?_⟩
  intro h1
  obtain ⟨c, hc⟩ := EuclidClasses.three_dvd_prod hN
  have : seq (n + 1) % 3 = 1 := by
    have hmod : seq (n + 1) % (3 * c) = 1 := by rwa [← hc]
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · exfalso; rw [h, mul_zero] at hc; have := prod_ge_two N; omega
      · exact h
    have := Nat.mod_mod_of_dvd (seq (n + 1)) (Dvd.intro c rfl : 3 ∣ 3 * c)
    omega
  omega

/-- **MC ⟹ NotConfined**, via Dirichlet's theorem: infinitely many primes are `≡ −1 (mod prod N)`,
and all of them appear. -/
theorem mullin_implies_notConfined (hmc : MullinConjecture) : NotConfined := by
  intro N hN
  have h2 := prod_ge_two N
  have h3 : 3 ≤ prod N := by
    obtain ⟨c, hc⟩ := EuclidClasses.three_dvd_prod hN
    have := EuclidClasses.two_dvd_prod N
    omega
  have : NeZero (prod N) := ⟨by omega⟩
  have hinf : {p : ℕ | p.Prime ∧ (p : ZMod (prod N)) = -1}.Infinite :=
    Nat.infinite_setOfPred_prime_and_eq_mod isUnit_one.neg
  obtain ⟨p, ⟨hp, hpmod⟩, hnot⟩ := hinf.exists_notMem_finset ((Finset.range (N + 1)).image seq)
  obtain ⟨k, hk⟩ := hmc p ⟨hp.two_le, fun d hd => (Nat.dvd_prime hp).mp hd⟩
  have hkN : N + 1 ≤ k := by
    by_contra h
    exact hnot (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), hk⟩)
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  refine ⟨n, by omega, ?_⟩
  rw [hk]
  intro h1
  have hcast : ((p % prod N : ℕ) : ZMod (prod N)) = (p : ZMod (prod N)) := ZMod.natCast_mod p (prod N)
  rw [h1, hpmod] at hcast
  have h20 : ((2 : ℕ) : ZMod (prod N)) = 0 := by
    push_cast at hcast ⊢
    linear_combination hcast
  rw [ZMod.natCast_eq_zero_iff] at h20
  have := Nat.le_of_dvd (by norm_num) h20
  omega

/-- **`CI(1 mod 4) ⟹ (C∞)`**: on the perpetual branch every late multiplier is `≡ 3 (mod 4)`. -/
theorem classInfinitude_one_mod_four_implies_infinitelyManyComposite
    (h : EuclidClasses.ClassInfinitude 4 1) : InfinitelyManyComposite := by
  by_contra hc
  obtain ⟨N₁, hpp⟩ := EuclidClasses.exists_perpetual_of_not_infinitelyManyComposite hc
  obtain ⟨k, hk, hk1⟩ := h (N₁ + 1)
  have := EuclidClasses.perpetual_seq_mod_four hpp hk
  omega

/-! ## 4. Consecutive Euclid numbers -/

theorem prod_eq_prod_mul_prod_Ioc {n m : ℕ} (hnm : n ≤ m) :
    prod m = prod n * ∏ k ∈ Finset.Ioc n m, seq k := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this; simp
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hlt | hge
    · rw [prod_succ, ih (by omega), Finset.prod_Ioc_succ_top (by omega), mul_assoc]
    · have : n = m + 1 := by omega
      subst this; simp

/-- **After a hit, further hits are returns of the multiplier product to `1`.**  If `r ∣ E_n` then
for `m ≥ n`: `r ∣ E_m ↔ seq (n+1) ⋯ seq m ≡ 1 (mod r)`. -/
theorem dvd_euclid_iff_prod_mul_eq_one {r n m : ℕ} (hn : r ∣ prod n + 1) (hnm : n ≤ m) :
    r ∣ prod m + 1 ↔ ((∏ k ∈ Finset.Ioc n m, seq k : ℕ) : ZMod r) = 1 := by
  have hPn : (prod n : ZMod r) = -1 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr hn
    push_cast at this
    linear_combination this
  rw [← ZMod.natCast_eq_zero_iff, prod_eq_prod_mul_prod_Ioc hnm]
  push_cast
  rw [hPn]
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-- **Consecutive Euclid numbers are coprime.** -/
theorem coprime_euclid_succ (n : ℕ) : Nat.Coprime (prod n + 1) (prod (n + 1) + 1) := by
  apply Nat.coprime_of_dvd
  intro r hr hdn hdn1
  have h2 : 2 ≤ r := hr.two_le
  have : Fact (1 < r) := ⟨hr.one_lt⟩
  -- `seq (n+1) ≡ 1 (mod r)`
  have hmod : ((seq (n + 1) : ℕ) : ZMod r) = 1 := by
    have h := (dvd_euclid_iff_prod_mul_eq_one hdn (Nat.le_succ n)).mp hdn1
    rwa [Finset.prod_Ioc_succ_top le_rfl, Finset.Ioc_self, Finset.prod_empty, one_mul] at h
  have hval : seq (n + 1) % r = 1 := by
    have := congrArg ZMod.val hmod
    rwa [ZMod.val_natCast, ZMod.val_one] at this
  -- but `2 ≤ seq (n+1) ≤ r`
  have hle : seq (n + 1) ≤ r := by
    rw [seq_succ]
    exact minFac_min' _ _ (by have := prod_ge_two n; omega) h2 hdn
  have hge : 2 ≤ seq (n + 1) := (seq_isPrime _).1
  rcases Nat.lt_or_ge (seq (n + 1)) r with hlt | hge'
  · rw [Nat.mod_eq_of_lt hlt] at hval; omega
  · have : seq (n + 1) = r := by omega
    rw [this, Nat.mod_self] at hval; omega

end HeadDynamics
