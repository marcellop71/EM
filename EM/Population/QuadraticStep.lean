import EM.Population.Dichotomy
import EM.FunctionField.AutonomousMap
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# The Euclid step as a norm: discriminants, the splitting law, and the frozen rung

2026-09-24.  Companion to `docs/analysis/euclid_systems_theory_2026-09-23.md` §§1–4.

Write `E_n = prod n + 1`, `p = seq (n+1) = lpf E_n`, and `c_n = E_n / p` (`cofactor`), the
part of the Euclid number the greedy rule discards.  Then

* `euclid_succ_eq_norm`: `E_{n+1} = c p² − p + 1`, the norm of `p·ω − 1` in `ℤ[ω]`,
  `ω² − ω + c = 0`;
* `four_cofactor_mul_euclid_succ`: `4 c E_{n+1} = (2E_n − 1)² − D_n` with the discriminant
  `D_n = 1 − 4c_n` (`disc`);
* `isSquare_disc_of_dvd` (**splitting law**): every divisor `ℓ` of `E_{n+1}` has `D_n` a
  square mod `ℓ` — all prime factors of the next Euclid number split or ramify in
  `ℚ(√D_n)`, at once;
* on a prime stage `c_n = 1` and `D_n = −3` (`disc_eq_neg_three_of_prime`).

A prime `q` is **frozen** (`Frozen`) if from some stage on `D_n` is a non-square mod `q`
(and `q` was not collected earlier): then `q` can never divide a Euclid number again, so it
is missing (`frozen_missing`).  On a Sylvester tower every `q ≡ 2 (mod 3)` outside the bag is
frozen (`frozen_of_perpetual`), since `−3` is a non-square there.  Hence the **frozen rung**

    MC ⟹ NoFrozen ⟹ (C∞)

(`noFrozen_of_mc`, `infinitelyManyComposite_of_noFrozen`), the first rung of the ladder
whose character is arithmetic (a splitting condition) rather than a size condition.

Also here: the seeded easy direction of the dichotomy conjecture,
`sgrowth_eq_zero_of_genMC`: an orbit that captures every prime coprime to its seed is not
eventually a Sylvester tower — via `Φ₃` and Dirichlet, for every seed `m ≥ 2`.
-/

noncomputable section
open Classical Mullin

namespace QuadraticStep

/-! ## 1. Cofactor and discriminant -/

/-- The discarded cofactor `c_n = E_n / lpf E_n`. -/
def cofactor (n : ℕ) : ℕ := (prod n + 1) / Mullin.seq (n + 1)

/-- The discriminant `D_n = 1 − 4 c_n` of the step. -/
def disc (n : ℕ) : ℤ := 1 - 4 * (cofactor n : ℤ)

theorem seq_succ_dvd_euclid (n : ℕ) : Mullin.seq (n + 1) ∣ prod n + 1 := by
  rw [seq_succ]; exact Euclid.minFac_dvd _ (by have := prod_ge_two n; omega)

theorem seq_succ_pos (n : ℕ) : 0 < Mullin.seq (n + 1) :=
  ((MullinGroup.isPrime_iff_natPrime _).mp (seq_isPrime (n + 1))).pos

theorem seq_mul_cofactor (n : ℕ) : Mullin.seq (n + 1) * cofactor n = prod n + 1 :=
  Nat.mul_div_cancel' (seq_succ_dvd_euclid n)

theorem cofactor_pos (n : ℕ) : 0 < cofactor n :=
  Nat.div_pos (Nat.le_of_dvd (by omega) (seq_succ_dvd_euclid n)) (seq_succ_pos n)

/-- **The norm identity**: `E_{n+1} = c p² − p + 1`. -/
theorem euclid_succ_eq_norm (n : ℕ) :
    ((prod (n + 1) + 1 : ℕ) : ℤ)
      = (cofactor n : ℤ) * (Mullin.seq (n + 1) : ℤ) ^ 2 - (Mullin.seq (n + 1) : ℤ) + 1 := by
  have h := seq_mul_cofactor n
  rw [prod_succ]
  push_cast
  have h' : (Mullin.seq (n + 1) : ℤ) * (cofactor n : ℤ) = (prod n : ℤ) + 1 := by
    exact_mod_cast h
  linear_combination (-(Mullin.seq (n + 1) : ℤ)) * h'

/-- `4 c E_{n+1} = (2 E_n − 1)² − D_n`. -/
theorem four_cofactor_mul_euclid_succ (n : ℕ) :
    4 * (cofactor n : ℤ) * ((prod (n + 1) + 1 : ℕ) : ℤ)
      = (2 * ((prod n + 1 : ℕ) : ℤ) - 1) ^ 2 - disc n := by
  have h := seq_mul_cofactor n
  have h' : (Mullin.seq (n + 1) : ℤ) * (cofactor n : ℤ) = ((prod n + 1 : ℕ) : ℤ) := by
    exact_mod_cast h
  rw [euclid_succ_eq_norm]
  unfold disc
  push_cast at h' ⊢
  linear_combination
    (4 * ((cofactor n : ℤ) * (Mullin.seq (n + 1) : ℤ) + (prod n : ℤ))) * h'

/-- **The splitting law.**  If `ℓ ∣ E_{n+1}` then `D_n` is a square modulo `ℓ`. -/
theorem isSquare_disc_of_dvd {ℓ n : ℕ} (h : ℓ ∣ prod (n + 1) + 1) :
    IsSquare ((disc n : ZMod ℓ)) := by
  have hid := four_cofactor_mul_euclid_succ n
  have h0 : (((prod (n + 1) + 1 : ℕ) : ℤ) : ZMod ℓ) = 0 := by
    rw [Int.cast_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr h
  refine ⟨(2 * ((prod n + 1 : ℕ) : ZMod ℓ) - 1), ?_⟩
  have := congrArg (fun z : ℤ => (z : ZMod ℓ)) hid
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_sub, Int.cast_pow, Int.cast_one,
    Int.cast_natCast, h0, mul_zero] at this
  push_cast at this ⊢
  linear_combination this

/-- On a prime stage the cofactor is `1`. -/
theorem cofactor_eq_one_of_prime {n : ℕ} (h : Nat.Prime (prod n + 1)) : cofactor n = 1 := by
  have hs : Mullin.seq (n + 1) = prod n + 1 := by
    rw [seq_succ]; exact AutonomousBranch.euclid_minFac_self_of_prime h
  unfold cofactor
  rw [hs, Nat.div_self (by omega)]

/-- On a prime stage `D_n = −3`. -/
theorem disc_eq_neg_three_of_prime {n : ℕ} (h : Nat.Prime (prod n + 1)) : disc n = -3 := by
  unfold disc; rw [cofactor_eq_one_of_prime h]; norm_num

/-! ## 2. Frozen primes -/

/-- `q` is **frozen**: not collected up to stage `N + 1`, and from stage `N` on the
discriminant is a non-square mod `q`. -/
def Frozen (q : ℕ) : Prop :=
  q.Prime ∧ ∃ N, ¬ q ∣ prod (N + 1) ∧ ∀ n, N ≤ n → ¬ IsSquare ((disc n : ZMod q))

/-- **A frozen prime is missing.** -/
theorem frozen_missing {q : ℕ} (h : Frozen q) : ∀ k, Mullin.seq k ≠ q := by
  obtain ⟨-, N, hnd, hns⟩ := h
  intro k hk
  rcases le_or_gt k (N + 1) with hle | hgt
  · exact hnd (hk ▸ seq_dvd_prod k (N + 1) hle)
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    have hdvd : Mullin.seq (n + 2) ∣ prod (n + 1) + 1 := seq_succ_dvd_euclid (n + 1)
    rw [hk] at hdvd
    exact hns n (by omega) (isSquare_disc_of_dvd hdvd)

/-- **NoFrozen**: every frozen prime is collected (equivalently, no prime is frozen). -/
def NoFrozen : Prop := ∀ q, Frozen q → ∃ k, Mullin.seq k = q

theorem noFrozen_iff : NoFrozen ↔ ∀ q, ¬ Frozen q := by
  constructor
  · intro h q hq
    obtain ⟨k, hk⟩ := h q hq
    exact frozen_missing hq k hk
  · intro h q hq
    exact absurd hq (h q)

/-- MC ⟹ NoFrozen. -/
theorem noFrozen_of_mc (hmc : MullinConjecture) : NoFrozen := fun q hq =>
  hmc q ((MullinGroup.isPrime_iff_natPrime q).mpr hq.1)

/-! ## 3. `−3` is a non-square mod `q ≡ 2 (mod 3)` -/

theorem not_isSquare_neg_three {q : ℕ} [Fact (Nat.Prime q)] (hq3 : q % 3 = 2) (hq5 : 5 ≤ q) :
    ¬ IsSquare ((-3 : ℤ) : ZMod q) := by
  rintro ⟨r, hr⟩
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 q).mp (by exact_mod_cast h)
    exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
  apply FunctionFieldAnalog.phi3_no_roots q hq3 hq5 ((r - 1) * (2 : ZMod q)⁻¹)
  push_cast at hr
  field_simp
  linear_combination -hr

/-- **On a Sylvester tower every `q ≡ 2 (mod 3)` outside the bag is frozen.** -/
theorem frozen_of_perpetual {N q : ℕ} (hpp : AutonomousBranch.PerpetualPrimality N)
    (hq : q.Prime) (hq3 : q % 3 = 2) (hq5 : 5 ≤ q) (hnd : ¬ q ∣ prod (N + 1)) : Frozen q := by
  have : Fact (Nat.Prime q) := ⟨hq⟩
  refine ⟨hq, N, hnd, fun n hn => ?_⟩
  rw [disc_eq_neg_three_of_prime (hpp n hn)]
  exact not_isSquare_neg_three hq3 hq5

/-! ## 4. Dirichlet for the class `2 (mod 3)` -/

theorem exists_prime_two_mod_three_gt (B : ℕ) : ∃ q, B < q ∧ q.Prime ∧ q % 3 = 2 := by
  have hu : IsUnit ((2 : ℕ) : ZMod 3) := (ZMod.unitOfCoprime 2 (by norm_num)).isUnit
  obtain ⟨q, hq, hqp, hq2⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu B
  refine ⟨q, hq, hqp, ?_⟩
  have := (ZMod.natCast_eq_natCast_iff' q 2 3).mp hq2
  omega

/-! ## 5. The frozen rung: NoFrozen ⟹ (C∞) -/

/-- **NoFrozen ⟹ (C∞).**  A perpetual tower would freeze a Dirichlet prime `q ≡ 2 (mod 3)`
beyond the bag, which NoFrozen says is collected, which a frozen prime never is. -/
theorem infinitelyManyComposite_of_noFrozen (h : NoFrozen) :
    AutonomousBranch.InfinitelyManyComposite := by
  rw [AutonomousBranch.infinitelyManyComposite_iff_no_perpetual_primality]
  intro N hpp
  obtain ⟨q, hqB, hq, hq3⟩ := exists_prime_two_mod_three_gt (prod (N + 1))
  have hnd : ¬ q ∣ prod (N + 1) := fun hd =>
    absurd (Nat.le_of_dvd (by have := prod_ge_two (N + 1); omega) hd) (by omega)
  have hq5 : 5 ≤ q := by have := prod_ge_two (N + 1); omega
  have hfr := frozen_of_perpetual hpp hq hq3 hq5 hnd
  obtain ⟨k, hk⟩ := h q hfr
  exact frozen_missing hfr k hk

/-- **The frozen rung.** -/
theorem frozen_rung :
    (MullinConjecture → NoFrozen) ∧ (NoFrozen → AutonomousBranch.InfinitelyManyComposite) :=
  ⟨noFrozen_of_mc, infinitelyManyComposite_of_noFrozen⟩

/-! ## 6. The seeded easy direction of the dichotomy conjecture -/

open SeededGrowth in
/-- **GenMC(m) ⟹ `sgrowth m = 0`.**  If the orbit of `m` were a Sylvester tower from stage
`N₀`, a prime `q ≡ 2 (mod 3)` beyond `genProd m (N₀+1)` would never be selected: a selection
at a later stage `k` needs `q ∣ genProd m k + 1` with `genProd m k = P(P+1)`, i.e. a root of
`Φ₃` mod `q`. -/
theorem sgrowth_eq_zero_of_genMC {m : ℕ} (hm : 2 ≤ m) (h : GenMullinConjecture m) :
    sgrowth m = 0 := by
  by_contra hne
  have hpos : 0 < sgrowth m := lt_of_le_of_ne (sgrowth_nonneg hm) (Ne.symm hne)
  obtain ⟨N₀, hN₀⟩ := (sgrowth_pos_iff_eventually_prime hm).mp hpos
  -- on the tower `genSeq m n = genProd m n + 1`
  have hstep : ∀ n, N₀ ≤ n → genProd m (n + 1) = genProd m n * (genProd m n + 1) := by
    intro n hn
    rw [genProd_succ, genSeq_def, Nat.Prime.minFac_eq (hN₀ n hn)]
  obtain ⟨q, hqB, hq, hq3⟩ := exists_prime_two_mod_three_gt (genProd m (N₀ + 1))
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have hpos' : 1 ≤ genProd m (N₀ + 1) := genProd_pos (by omega) _
  have hq5 : 5 ≤ q := by
    have := hstep N₀ le_rfl
    have hP : m ≤ genProd m N₀ :=
      Nat.le_of_dvd (genProd_pos (show 1 ≤ m by omega) N₀) (start_dvd_genProd m N₀)
    have h6 : 6 ≤ genProd m N₀ * (genProd m N₀ + 1) := by nlinarith
    omega
  have hnd : ¬ q ∣ genProd m (N₀ + 1) := fun hd =>
    absurd (Nat.le_of_dvd hpos' hd) (by omega)
  have hqm : ¬ q ∣ m := fun hd => hnd (hd.trans (start_dvd_genProd m _))
  obtain ⟨k, hk⟩ := h q hq hqm
  -- `q` divides `genProd m (k+1)`; if `k + 1 ≤ N₀ + 1` this contradicts `hnd`
  rcases le_or_gt k N₀ with hle | hgt
  · have : genSeq m k ∣ genProd m (N₀ + 1) := by
      have h1 : genSeq m k ∣ genProd m (k + 1) := by rw [genProd_succ]; exact dvd_mul_left _ _
      exact h1.trans (by
        have := genProd_dvd_genProd m (k + 1) (N₀ - k)
        rwa [show k + 1 + (N₀ - k) = N₀ + 1 by omega] at this)
    exact hnd (hk ▸ this)
  · -- `k ≥ N₀ + 1`: `q ∣ genProd m k + 1` with `genProd m k = P (P + 1)`, `P = genProd m (k-1)`
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : N₀ ≤ j := by omega
    have hdvd : q ∣ genProd m (j + 1) + 1 := by
      rw [← hk]; exact genSeq_dvd_genProd_succ m (j + 1)
    rw [hstep j hj] at hdvd
    have hz : ((genProd m j * (genProd m j + 1) + 1 : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at hz
    exact FunctionFieldAnalog.phi3_no_roots q hq3 hq5 (genProd m j : ZMod q)
      (by linear_combination hz)

end QuadraticStep

end
