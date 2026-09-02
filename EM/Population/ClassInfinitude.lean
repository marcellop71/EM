import EM.Population.AutonomousBranch
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.Finite.Basic

/-!
# Residue classes of the Euclid–Mullin primes, and the composite floor

The Euclid numbers `E_n = prod n + 1` carry two frozen residues: `E_n ≡ 3 (mod 4)` (since
`prod n = 2 · odd`) and `E_n ≡ 1 (mod 3)` (since `3 = seq 1 ∣ prod n`) for `n ≥ 1`.  Both are
statements about *classes*, and they are the only positive divisibility information the sequence
yields for free (the "sign asymmetry" of `paper/why_its_hard.tex`).

## Class infinitude

`ClassInfinitude m a` says infinitely many Euclid–Mullin primes are `≡ a (mod m)`.  Two
instances sit right above the composite floor `(C∞)` (`AutonomousBranch.InfinitelyManyComposite`):

* **`CI(2 mod 3) ⟹ (C∞)`** (`classInfinitude_two_mod_three_implies_infinitelyManyComposite`):
  on the perpetual-primality branch every late multiplier is a prime Euclid number, hence
  `≡ 1 (mod 3)`.
* **`¬ CI(3 mod 4) ⟹ (C∞)`** (`not_classInfinitude_three_mod_four_implies_infinitelyManyComposite`):
  on that branch every late multiplier is `≡ 3 (mod 4)`.

So if the composite floor fails, the Euclid–Mullin primes are eventually all `≡ 7 (mod 12)`.
Both `CI(2 mod 3)` and `CI(3 mod 4)` are implied by Mullin's conjecture (every prime appears) and
by Weak Mullin; `CI(2 mod 3)` is therefore at least as hard as `(C∞)`, while `CI(3 mod 4)` is the
one class statement that is *not* blocked by the composite floor — the weakest open statement
with an unconditional positive ingredient, namely:

* **every Euclid number has a prime factor `≡ 3 (mod 4)`**
  (`exists_prime_dvd_euclid_three_mod_four`), since `E_n ≡ 3 (mod 4)`.

## After a prime Euclid number

If `E_n` is prime then the next Euclid number is `Φ₃(prod n) = P² + P + 1`, and **every prime
factor of it is `≡ 1 (mod 3)`** (`prime_dvd_euclid_succ_mod_three`): the integer twin of the
even-degree exclusion of `EM/FunctionField/AutonomousDegrees.lean`, and the reason the
autonomous branch confines the multipliers to `1 (mod 3)`.

See `docs/analysis/logic_routes_2026-09-01.md` §8.4, §17.
-/

open Mullin Euclid

namespace EuclidClasses

/-! ## 1. Frozen residues -/

/-- The repository's `IsPrime` is `Nat.Prime`. -/
theorem seq_nat_prime (k : ℕ) : Nat.Prime (seq k) := by
  obtain ⟨h2, hd⟩ := seq_isPrime k
  exact Nat.prime_def_lt.mpr ⟨h2, fun m hm hdvd => (hd m hdvd).resolve_right (ne_of_lt hm)⟩

theorem seq_zero' : seq 0 = 2 := seq_zero

theorem two_dvd_prod (n : ℕ) : 2 ∣ prod n := by
  have := seq_dvd_prod 0 n (Nat.zero_le n)
  rwa [seq_zero'] at this

theorem three_dvd_prod {n : ℕ} (hn : 1 ≤ n) : 3 ∣ prod n := by
  have := seq_dvd_prod 1 n hn
  rwa [seq_one] at this

/-- `E_n ≡ 1 (mod 3)` for `n ≥ 1`. -/
theorem euclid_mod_three {n : ℕ} (hn : 1 ≤ n) : (prod n + 1) % 3 = 1 := by
  obtain ⟨k, hk⟩ := three_dvd_prod hn
  omega

theorem seq_odd {k : ℕ} (hk : 1 ≤ k) : Odd (seq k) := by
  have hp : Nat.Prime (seq k) := seq_nat_prime k
  refine hp.odd_of_ne_two ?_
  intro h
  have : seq k = seq 0 := by rw [h, seq_zero']
  exact absurd (seq_injective k 0 this) (by omega)

/-- `prod n = 2 · (odd)`. -/
theorem prod_eq_two_mul_odd (n : ℕ) : ∃ m, Odd m ∧ prod n = 2 * m := by
  induction n with
  | zero => exact ⟨1, odd_one, by rw [prod_zero]⟩
  | succ n ih =>
    obtain ⟨m, hm, hprod⟩ := ih
    refine ⟨m * seq (n + 1), hm.mul (seq_odd (by omega)), ?_⟩
    rw [prod_succ, hprod]; ring

theorem prod_mod_four (n : ℕ) : prod n % 4 = 2 := by
  obtain ⟨m, ⟨k, hk⟩, hprod⟩ := prod_eq_two_mul_odd n
  omega

/-- `E_n ≡ 3 (mod 4)` for every `n`. -/
theorem euclid_mod_four (n : ℕ) : (prod n + 1) % 4 = 3 := by
  have := prod_mod_four n; omega

/-! ## 2. The class-hit fact: every Euclid number has a prime factor `≡ 3 (mod 4)` -/

/-- A positive integer `≡ 3 (mod 4)` has a prime factor `≡ 3 (mod 4)`. -/
theorem exists_prime_dvd_three_mod_four : ∀ n : ℕ, n % 4 = 3 → ∃ p, Nat.Prime p ∧ p ∣ n ∧ p % 4 = 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn1 : n ≠ 1 := by omega
    have hn0 : n ≠ 0 := by omega
    have hp : Nat.Prime (Nat.minFac n) := Nat.minFac_prime hn1
    have hdvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
    have hodd : Nat.minFac n % 2 = 1 := by
      rcases hp.eq_two_or_odd with h2 | hodd
      · exfalso
        have : 2 ∣ n := h2 ▸ hdvd
        omega
      · exact hodd
    by_cases h3 : Nat.minFac n % 4 = 3
    · exact ⟨_, hp, hdvd, h3⟩
    · have h1 : Nat.minFac n % 4 = 1 := by omega
      obtain ⟨m, hm⟩ := hdvd
      have hm3 : m % 4 = 3 := by
        have hmod : n % 4 = Nat.minFac n % 4 * (m % 4) % 4 := by
          have := Nat.mul_mod (Nat.minFac n) m 4
          rwa [← hm] at this
        rw [h1] at hmod; omega
      have hmlt : m < n := by
        have h2 : 2 ≤ Nat.minFac n := hp.two_le
        have hm0 : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h | h
          · exfalso; rw [h, mul_zero] at hm; exact hn0 hm
          · exact h
        nlinarith
      obtain ⟨p, hpp, hpm, hp3⟩ := ih m hmlt hm3
      exact ⟨p, hpp, hm ▸ Dvd.dvd.mul_left hpm _, hp3⟩

/-- **Every Euclid number has a prime factor `≡ 3 (mod 4)`.** -/
theorem exists_prime_dvd_euclid_three_mod_four (n : ℕ) :
    ∃ p, Nat.Prime p ∧ p ∣ prod n + 1 ∧ p % 4 = 3 :=
  exists_prime_dvd_three_mod_four _ (euclid_mod_four n)

/-! ## 3. Class infinitude and the composite floor -/

/-- Infinitely many Euclid–Mullin primes are `≡ a (mod m)`. -/
def ClassInfinitude (m a : ℕ) : Prop := ∀ N, ∃ k, N ≤ k ∧ seq k % m = a

open AutonomousBranch

/-- Under perpetual primality from `N₁`, late multipliers are prime Euclid numbers, hence
`≡ 1 (mod 3)`. -/
theorem perpetual_seq_mod_three {N₁ : ℕ} (hpp : PerpetualPrimality N₁) {k : ℕ}
    (hk : N₁ + 1 ≤ k) (hk1 : 2 ≤ k) : seq k % 3 = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [perpetual_seq_succ hpp (by omega)]
  exact euclid_mod_three (by omega)

/-- Under perpetual primality from `N₁`, late multipliers are `≡ 3 (mod 4)`. -/
theorem perpetual_seq_mod_four {N₁ : ℕ} (hpp : PerpetualPrimality N₁) {k : ℕ}
    (hk : N₁ + 1 ≤ k) : seq k % 4 = 3 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [perpetual_seq_succ hpp (by omega)]
  exact euclid_mod_four n

theorem exists_perpetual_of_not_infinitelyManyComposite (h : ¬ InfinitelyManyComposite) :
    ∃ N₁, PerpetualPrimality N₁ := by
  simp only [InfinitelyManyComposite, not_forall, not_exists, not_and, not_not] at h
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => hN n hn⟩

/-- **`CI(2 mod 3) ⟹ (C∞)`.** -/
theorem classInfinitude_two_mod_three_implies_infinitelyManyComposite
    (h : ClassInfinitude 3 2) : InfinitelyManyComposite := by
  by_contra hc
  obtain ⟨N₁, hpp⟩ := exists_perpetual_of_not_infinitelyManyComposite hc
  obtain ⟨k, hk, hk2⟩ := h (N₁ + 2)
  have h1 : seq k % 3 = 1 := perpetual_seq_mod_three hpp (by omega) (by omega)
  omega

/-- **`¬ CI(3 mod 4) ⟹ (C∞)`.**  Equivalently, on the perpetual-primality branch infinitely
many multipliers are `≡ 3 (mod 4)`. -/
theorem not_classInfinitude_three_mod_four_implies_infinitelyManyComposite
    (h : ¬ ClassInfinitude 4 3) : InfinitelyManyComposite := by
  by_contra hc
  obtain ⟨N₁, hpp⟩ := exists_perpetual_of_not_infinitelyManyComposite hc
  apply h
  intro N
  exact ⟨max N (N₁ + 1), le_max_left _ _, perpetual_seq_mod_four hpp (le_max_right _ _)⟩

/-- If the composite floor fails, the Euclid–Mullin primes are eventually all `≡ 7 (mod 12)`. -/
theorem perpetual_seq_mod_twelve {N₁ : ℕ} (hpp : PerpetualPrimality N₁) {k : ℕ}
    (hk : N₁ + 1 ≤ k) (hk1 : 2 ≤ k) : seq k % 12 = 7 := by
  have h3 := perpetual_seq_mod_three hpp hk hk1
  have h4 := perpetual_seq_mod_four hpp hk
  omega

/-! ## 4. After a prime Euclid number, every prime factor of the next one is `≡ 1 (mod 3)` -/

/-- The autonomous step: if `E_n` is prime, `E_{n+1} = P² + P + 1`. -/
theorem euclid_succ_of_prime {n : ℕ} (h : Nat.Prime (prod n + 1)) :
    prod (n + 1) + 1 = prod n ^ 2 + prod n + 1 := by
  rw [prod_succ, seq_succ, euclid_minFac_self_of_prime h]; ring

/-- **The integer twin of the even-degree exclusion.**  If `E_n` is prime (`n ≥ 0`), every prime
factor `q` of `E_{n+1}` satisfies `q ≡ 1 (mod 3)`: `prod n` is a primitive cube root of unity
modulo `q`. -/
theorem prime_dvd_euclid_succ_mod_three {n : ℕ} (h : Nat.Prime (prod n + 1)) {q : ℕ}
    (hq : Nat.Prime q) (hdvd : q ∣ prod (n + 1) + 1) : q % 3 = 1 := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [euclid_succ_of_prime h] at hdvd
  -- `q ≠ 3` since `E_{n+1} ≡ 1 (mod 3)`
  have hq3 : q ≠ 3 := by
    rintro rfl
    have := euclid_mod_three (n := n + 1) (by omega)
    rw [euclid_succ_of_prime h] at this
    omega
  set P : ZMod q := (prod n : ZMod q) with hP
  have hΦ : P ^ 2 + P + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at this
    exact this
  have hP1 : P ≠ 1 := by
    intro h1
    rw [h1] at hΦ
    have h3 : ((3 : ℕ) : ZMod q) = 0 := by exact_mod_cast (by linear_combination hΦ : (3 : ZMod q) = 0)
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3)
  have hP0 : P ≠ 0 := by
    rintro h0; rw [h0] at hΦ; norm_num at hΦ
  have hP3 : P ^ 3 = 1 := by linear_combination (P - 1) * hΦ
  -- the unit `P` has order exactly 3
  set u : (ZMod q)ˣ := Units.mk0 P hP0 with hu
  have hu3 : u ^ 3 = 1 := by
    ext; simp [hu, hP3]
  have hu1 : u ≠ 1 := by
    intro h1
    apply hP1
    have := congrArg Units.val h1
    simpa [hu] using this
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdvd' : orderOf u ∣ Fintype.card (ZMod q)ˣ := orderOf_dvd_card
  rw [hord, ZMod.card_units] at hdvd'
  have := hq.two_le
  omega

end EuclidClasses
