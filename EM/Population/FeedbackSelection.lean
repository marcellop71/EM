import EM.Population.QuadraticStep
import EM.Population.BackwardLevels
import EM.Population.GreedyRigidity

/-!
# Feedback selection: autonomy is take-all, and all steering happens at deviations

2026-11-08.  Companion to `docs/analysis/feedback_selection_2026-11-08.md`.

A **Euclid rule** appends to the accumulator `P` a nontrivial divisor `σ(E)` of the Euclid
number `E = P + 1`.  The take-all rule `σ(E) = E` is Sylvester's recurrence, an autonomous
polynomial map `P ↦ P² + P`; the greedy rule `σ = lpf` is Euclid–Mullin.  Every rule is the
Sylvester map *divided by the discarded cofactor* `c = E / σ(E)`:

    P_{n+1} · c_n = P_n² + P_n          (`walkZ_succ_mul_cofactor`, modulo `q`)

so the whole non-autonomy of a rule sits in the residues of its cofactors.  This file proves
the two structural facts of the "feedback selection" viewpoint.

**1. Autonomy is take-all** (`sel_cast_eq_of_autonomous`).  If the residue of `σ(E)` modulo
a prime `q` is a function of the residue of `E` (on inputs coprime to `q`), then
`σ(E) ≡ E (mod q)` for all such `E`: by Dirichlet every unit class contains a prime, on a
prime the rule has no choice, and the function is therefore the identity on units.  Hence
the cofactor of an autonomous rule is `≡ 1` (`cofactor_cast_eq_one_of_autonomous`), the
walk modulo `q` is the Sylvester walk, and the greedy rule is autonomous modulo no odd prime
(`greedy_not_autonomous`).  No Galois-theoretic or arboreal control of the walk can be
bought by making the selection autonomous: the only autonomous rule is the one whose prime
support has density zero (Odoni).

**2. All steering happens at deviations.**  Call stage `n` **`q`-autonomous** if
`c_n ≡ 1 (mod q)` (`StageAutonomous`; a prime Euclid number is autonomous modulo every
`q`, `stageAutonomous_of_prime`) and a **deviation** otherwise (`Deviates`).  Along an
autonomous run the walk modulo `q` is the Sylvester iteration (`walkZ_add_of_run`), and

* a capture of `q` at the end of a nonempty autonomous run forces a root of `Φ₃` modulo `q`
  (`phi3_root_of_capture_after_run`); so for `q ≡ 2 (mod 3)`, `q ≥ 5`, **every capture is
  immediately preceded by a deviation** (`deviates_of_dvd_two_mod_three`), and MC forces one
  for every such prime (`exists_deviation_before_capture_of_mc`);
* an autonomous *tail* freezes every `q ≡ 2 (mod 3)` outside the bag
  (`frozen_of_autonomous_tail`, generalising `QuadraticStep.frozen_of_perpetual` from
  prime stages `c_n = 1` to residue-autonomous stages `c_n ≡ 1`);
* on an autonomous tail capture is **decided in fewer than `q` steps**
  (`capture_iff_of_autonomous_tail`), by pigeonhole on the Sylvester orbit in `𝔽_q`
  (`exists_iterate_lt_card_of_exists`).

**3. A rung.**  `NoAutonomousTail` — for every `q ≡ 2 (mod 3)` outside the bag the cofactors are
not eventually `≡ 1 (mod q)` — sits strictly between the frozen rung and `(C∞)`:
`MC ⟹ NoFrozen ⟹ NoAutonomousTail ⟹ (C∞)` (`autonomous_rung`).  It is the most elementary
open statement about cofactor residues, and it already implies infinitely many composite
Euclid numbers.

The positive half — that the greedy cofactor residues steer the walk into `−1` — is the
conjecture itself; its choice-free relaxation is `MixedMC` (`EM/Stochastic/MixedMC.lean`).
-/

noncomputable section
open Classical Mullin MullinGroup QuadraticStep BackwardLevels

namespace FeedbackSelection

/-! ## 1. Euclid rules and autonomy -/

/-- A **Euclid rule**: for every Euclid number `E ≥ 2`, a nontrivial divisor to append. -/
structure EuclidRule where
  /-- The selected multiplier. -/
  sel : ℕ → ℕ
  sel_dvd : ∀ E, 2 ≤ E → sel E ∣ E
  two_le_sel : ∀ E, 2 ≤ E → 2 ≤ sel E

/-- The greedy rule (Euclid–Mullin): the least prime factor. -/
def greedyRule : EuclidRule where
  sel := Nat.minFac
  sel_dvd := fun E _ => Nat.minFac_dvd E
  two_le_sel := fun E hE => (Nat.minFac_prime (by omega)).two_le

/-- The take-all rule (Sylvester): the whole Euclid number. -/
def takeAllRule : EuclidRule where
  sel := id
  sel_dvd := fun _ _ => dvd_rfl
  two_le_sel := fun _ hE => hE

/-- A rule is **autonomous modulo `q`** if the residue of its output is a function of the
residue of its input, on inputs coprime to `q`. -/
def Autonomous (σ : EuclidRule) (q : ℕ) : Prop :=
  ∃ h : ZMod q → ZMod q, ∀ E, 2 ≤ E → Nat.Coprime E q → (σ.sel E : ZMod q) = h (E : ZMod q)

/-- On a prime a rule has no choice. -/
theorem sel_eq_self_of_prime (σ : EuclidRule) {E : ℕ} (hE : E.Prime) : σ.sel E = E := by
  rcases (Nat.dvd_prime hE).mp (σ.sel_dvd E hE.two_le) with h | h
  · have := σ.two_le_sel E hE.two_le; omega
  · exact h

theorem takeAll_autonomous (q : ℕ) : Autonomous takeAllRule q := ⟨id, fun _ _ _ => rfl⟩

/-- **Autonomy is take-all.**  A rule autonomous modulo a prime `q` satisfies
`σ(E) ≡ E (mod q)` on every input coprime to `q`.  Dirichlet supplies a prime in the class
of `E`; on that prime the rule returns the prime itself. -/
theorem sel_cast_eq_of_autonomous {σ : EuclidRule} {q : ℕ} [Fact q.Prime]
    (h : Autonomous σ q) {E : ℕ} (hE : 2 ≤ E) (hcop : Nat.Coprime E q) :
    (σ.sel E : ZMod q) = (E : ZMod q) := by
  obtain ⟨h, hh⟩ := h
  have hu : IsUnit (E : ZMod q) := (ZMod.unitOfCoprime E hcop).isUnit
  obtain ⟨p, -, hpp, hpE⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu 1
  have hpq : p ≠ q := by
    rintro rfl
    rw [ZMod.natCast_self] at hpE
    exact hu.ne_zero hpE.symm
  have hpcop : Nat.Coprime p q := (Nat.coprime_primes hpp Fact.out).mpr hpq
  have h1 := hh E hE hcop
  have h2 := hh p hpp.two_le hpcop
  rw [sel_eq_self_of_prime σ hpp, hpE] at h2
  rw [h1]
  exact h2.symm

/-- The cofactor of an autonomous rule is `≡ 1 (mod q)`: modulo `q` the rule is Sylvester. -/
theorem cofactor_cast_eq_one_of_autonomous {σ : EuclidRule} {q : ℕ} [Fact q.Prime]
    (h : Autonomous σ q) {E : ℕ} (hE : 2 ≤ E) (hcop : Nat.Coprime E q) :
    ((E / σ.sel E : ℕ) : ZMod q) = 1 := by
  have hmul : σ.sel E * (E / σ.sel E) = E := Nat.mul_div_cancel' (σ.sel_dvd E hE)
  have hu : IsUnit (E : ZMod q) := (ZMod.unitOfCoprime E hcop).isUnit
  have hc := congrArg (fun n : ℕ => (n : ZMod q)) hmul
  simp only [Nat.cast_mul] at hc
  rw [sel_cast_eq_of_autonomous h hE hcop] at hc
  exact mul_left_cancel₀ hu.ne_zero (by rw [hc, mul_one])

/-- **The greedy rule is autonomous modulo no odd prime.**  Take a prime `r ≡ 2⁻¹ (mod q)`;
then `lpf(2r) = 2` while `2r ≡ 1`. -/
theorem greedy_not_autonomous {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) :
    ¬ Autonomous greedyRule q := by
  intro h
  have h2ne : (2 : ZMod q) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).mp this)
  have hu : IsUnit ((2 : ZMod q)⁻¹) := isUnit_iff_ne_zero.mpr (inv_ne_zero h2ne)
  obtain ⟨r, hr2, hrp, hr⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu 2
  have hrq : r ≠ q := by
    rintro rfl
    rw [ZMod.natCast_self] at hr
    exact hu.ne_zero hr.symm
  have hcop : Nat.Coprime (2 * r) q :=
    Nat.Coprime.mul_left ((Nat.coprime_primes Nat.prime_two hq.out).mpr (Ne.symm hq2))
      ((Nat.coprime_primes hrp hq.out).mpr hrq)
  have hsel := sel_cast_eq_of_autonomous h (E := 2 * r) (by omega) hcop
  have hmin : greedyRule.sel (2 * r) = 2 := (Nat.minFac_eq_two_iff _).mpr (dvd_mul_right 2 r)
  rw [hmin] at hsel
  push_cast at hsel
  rw [hr, mul_inv_cancel₀ h2ne] at hsel
  have : (1 : ZMod q) = 0 := by linear_combination hsel
  exact one_ne_zero this

/-! ## 2. Autonomous stages and deviations of the Euclid–Mullin walk -/

/-- Stage `n` is **`q`-autonomous**: the discarded cofactor is `≡ 1 (mod q)`. -/
def StageAutonomous (q n : ℕ) : Prop := (cofactor n : ZMod q) = 1

/-- Stage `n` **deviates** modulo `q`: the discarded cofactor is `≢ 1 (mod q)`. -/
def Deviates (q n : ℕ) : Prop := (cofactor n : ZMod q) ≠ 1

theorem not_deviates_iff {q n : ℕ} : ¬ Deviates q n ↔ StageAutonomous q n := by
  unfold Deviates StageAutonomous; exact not_not

/-- A prime Euclid number is an autonomous stage modulo every `q`. -/
theorem stageAutonomous_of_prime {q n : ℕ} (h : Nat.Prime (prod n + 1)) :
    StageAutonomous q n := by
  unfold StageAutonomous; rw [cofactor_eq_one_of_prime h]; simp

/-- **The master identity modulo `q`**: `P_{n+1} · c_n = P_n² + P_n`. -/
theorem walkZ_succ_mul_cofactor (q n : ℕ) :
    walkZ q (n + 1) * (cofactor n : ZMod q) = sylvWalk (walkZ q n) := by
  have h' : ((seq (n + 1) : ℕ) : ZMod q) * (cofactor n : ZMod q) = (prod n : ZMod q) + 1 := by
    have := congrArg (fun m : ℕ => (m : ZMod q)) (seq_mul_cofactor n)
    push_cast at this
    exact this
  simp only [walkZ, sylvWalk, prod_succ]
  push_cast
  rw [mul_assoc, h']
  ring

/-- On an autonomous stage the walk takes a Sylvester step. -/
theorem walkZ_succ_of_stageAutonomous {q n : ℕ} (h : StageAutonomous q n) :
    walkZ q (n + 1) = sylvWalk (walkZ q n) := by
  have := walkZ_succ_mul_cofactor q n
  unfold StageAutonomous at h
  rwa [h, mul_one] at this

/-- Along an autonomous run the walk is the Sylvester iteration. -/
theorem walkZ_add_of_run {q N k : ℕ} (h : ∀ j, j < k → StageAutonomous q (N + j)) :
    walkZ q (N + k) = sylvWalk^[k] (walkZ q N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih (fun j hj => h j (by omega)),
      ← walkZ_succ_of_stageAutonomous (h k (by omega))]
    rfl

/-- `q ∣ E_n` iff the walk sits at `−1`. -/
theorem dvd_euclid_iff_walkZ_eq_neg_one (q n : ℕ) : q ∣ prod n + 1 ↔ walkZ q n = -1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, walkZ, eq_neg_iff_add_eq_zero]

/-- A capture at the end of a nonempty autonomous run forces a root of `Φ₃` modulo `q`:
the state one step before the capture. -/
theorem phi3_root_of_capture_after_run {q N k : ℕ} (hk : 1 ≤ k)
    (h : ∀ j, j < k → StageAutonomous q (N + j)) (hd : q ∣ prod (N + k) + 1) :
    phi3 (walkZ q (N + (k - 1))) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 := walkZ_succ_of_stageAutonomous (h j (by omega))
  rw [show N + j + 1 = N + (j + 1) from rfl, (dvd_euclid_iff_walkZ_eq_neg_one _ _).mp hd] at h1
  exact (sylvWalk_eq_neg_one_iff _).mp h1.symm

/-- **One-step necessity.**  For `q ≡ 2 (mod 3)`, `q ≥ 5`, a capture of `q` is immediately
preceded by a deviation: `q ∣ E_{n+1}` forces `c_n ≢ 1 (mod q)`. -/
theorem deviates_of_dvd_two_mod_three {q n : ℕ} [Fact q.Prime] (hq3 : q % 3 = 2) (hq5 : 5 ≤ q)
    (hd : q ∣ prod (n + 1) + 1) : Deviates q n := by
  intro h
  have hp := phi3_root_of_capture_after_run (q := q) (N := n) (k := 1) le_rfl
    (fun j hj => by
      obtain rfl : j = 0 := (by omega)
      exact h) hd
  simp only [Nat.sub_self, Nat.add_zero] at hp
  apply FunctionFieldAnalog.phi3_no_roots q hq3 hq5 (walkZ q n)
  unfold phi3 at hp
  linear_combination hp

/-- **MC forces a deviation before every capture of a prime `≡ 2 (mod 3)`.** -/
theorem exists_deviation_before_capture_of_mc (hmc : MullinConjecture) {q : ℕ} [Fact q.Prime]
    (hq3 : q % 3 = 2) (hq5 : 5 ≤ q) : ∃ n, Deviates q n ∧ seq (n + 2) = q := by
  obtain ⟨k, hk⟩ := hmc q ((isPrime_iff_natPrime q).mpr Fact.out)
  have hk2 : 2 ≤ k := by
    by_contra hlt
    rcases Nat.lt_succ_iff.mp (not_le.mp hlt) |> Nat.le_one_iff_eq_zero_or_eq_one.mp with rfl | rfl
    · rw [seq_zero] at hk; omega
    · rw [seq_one] at hk; omega
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  refine ⟨n, deviates_of_dvd_two_mod_three hq3 hq5 ?_, hk⟩
  rw [← hk]; exact seq_succ_dvd_euclid (n + 1)

/-- **An autonomous tail freezes every `q ≡ 2 (mod 3)` outside the bag.**  On such a tail
`D_n = 1 − 4c_n ≡ −3`, a non-square.  Generalises `QuadraticStep.frozen_of_perpetual`. -/
theorem frozen_of_autonomous_tail {N q : ℕ} [Fact q.Prime] (hq3 : q % 3 = 2) (hq5 : 5 ≤ q)
    (h : ∀ n, N ≤ n → StageAutonomous q n) (hnd : ¬ q ∣ prod (N + 1)) : Frozen q := by
  refine ⟨Fact.out, N, hnd, fun n hn => ?_⟩
  have hc : (cofactor n : ZMod q) = 1 := h n hn
  have : ((disc n : ℤ) : ZMod q) = ((-3 : ℤ) : ZMod q) := by
    unfold disc; push_cast; rw [hc]; ring
  rw [this]
  exact not_isSquare_neg_three hq3 hq5

/-! ## 3. Finite decidability on an autonomous tail -/

theorem exists_iterate_lt_card_of_periodic {α : Type*} [Fintype α] (f : α → α) (x : α)
    {k : ℕ} (hk : Fintype.card α ≤ k) {i j : ℕ} (hij : i < j) (hj : j ≤ Fintype.card α)
    (heq : f^[i] x = f^[j] x) :
    ∃ k', k' < Fintype.card α ∧ f^[k'] x = f^[k] x := by
  have hper : Function.IsPeriodicPt f (j - i) (f^[i] x) := by
    show f^[j - i] (f^[i] x) = f^[i] x
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le]
    exact heq.symm
  refine ⟨(k - i) % (j - i) + i, ?_, ?_⟩
  · have := Nat.mod_lt (k - i) (by omega : 0 < j - i); omega
  · rw [Function.iterate_add_apply, hper.iterate_mod_apply, ← Function.iterate_add_apply,
      Nat.sub_add_cancel (by omega : i ≤ k)]

/-- **Pigeonhole on an orbit.**  In a finite set every point of an orbit is reached within
`card` steps. -/
theorem exists_iterate_lt_card_of_exists {α : Type*} [Fintype α] (f : α → α) (x : α) (k : ℕ) :
    ∃ k', k' < Fintype.card α ∧ f^[k'] x = f^[k] x := by
  by_cases hk : k < Fintype.card α
  · exact ⟨k, hk, rfl⟩
  · have hk' : Fintype.card α ≤ k := not_lt.mp hk
    obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card α + 1) => f^[(i : ℕ)] x) (by simp)
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact exists_iterate_lt_card_of_periodic f x hk' hlt (Nat.lt_succ_iff.mp j.isLt) heq
    · exact exists_iterate_lt_card_of_periodic f x hk' hlt (Nat.lt_succ_iff.mp i.isLt) heq.symm

/-- **On an autonomous tail, capture is decided in fewer than `q` steps.** -/
theorem capture_iff_of_autonomous_tail {q N : ℕ} [NeZero q]
    (h : ∀ n, N ≤ n → StageAutonomous q n) :
    (∃ k, q ∣ prod (N + k) + 1) ↔ ∃ k, k < q ∧ sylvWalk^[k] (walkZ q N) = -1 := by
  have hrun : ∀ k, walkZ q (N + k) = sylvWalk^[k] (walkZ q N) :=
    fun k => walkZ_add_of_run (fun j _ => h (N + j) (by omega))
  constructor
  · rintro ⟨k, hk⟩
    rw [dvd_euclid_iff_walkZ_eq_neg_one, hrun] at hk
    obtain ⟨k', hk', heq⟩ := exists_iterate_lt_card_of_exists sylvWalk (walkZ q N) k
    exact ⟨k', by simpa [ZMod.card] using hk', heq.trans hk⟩
  · rintro ⟨k, -, hk⟩
    exact ⟨k, by rw [dvd_euclid_iff_walkZ_eq_neg_one, hrun]; exact hk⟩

/-! ## 4. The rung: MC ⟹ NoFrozen ⟹ NoAutonomousTail ⟹ (C∞) -/

/-- **NoAutonomousTail**: for every prime `q ≡ 2 (mod 3)`, `q ≥ 5`, and every stage `N` at which
`q` is not yet in the bag, some later stage deviates modulo `q` — the cofactors are not
eventually `≡ 1 (mod q)`.  The most elementary open statement about cofactor residues: it asks
that one residue class modulo one prime not be hit forever. -/
def NoAutonomousTail : Prop :=
  ∀ q N : ℕ, q.Prime → q % 3 = 2 → 5 ≤ q → ¬ q ∣ prod (N + 1) → ∃ n, N ≤ n ∧ Deviates q n

/-- NoFrozen ⟹ NoAutonomousTail: an autonomous tail freezes `q`, and a frozen prime is never
collected. -/
theorem noAutonomousTail_of_noFrozen (h : NoFrozen) : NoAutonomousTail := by
  intro q N hq hq3 hq5 hnd
  have : Fact q.Prime := ⟨hq⟩
  by_contra hcon
  have hall : ∀ n, N ≤ n → StageAutonomous q n := fun n hn =>
    not_deviates_iff.mp (fun hd => hcon ⟨n, hn, hd⟩)
  have hfr := frozen_of_autonomous_tail hq3 hq5 hall hnd
  obtain ⟨k, hk⟩ := h q hfr
  exact frozen_missing hfr k hk

/-- MC ⟹ NoAutonomousTail. -/
theorem noAutonomousTail_of_mc (hmc : MullinConjecture) : NoAutonomousTail :=
  noAutonomousTail_of_noFrozen (noFrozen_of_mc hmc)

/-- NoAutonomousTail ⟹ (C∞): a perpetual tower is an autonomous tail modulo every prime, and
Dirichlet supplies a `q ≡ 2 (mod 3)` beyond the bag. -/
theorem infinitelyManyComposite_of_noAutonomousTail (h : NoAutonomousTail) :
    AutonomousBranch.InfinitelyManyComposite := by
  rw [AutonomousBranch.infinitelyManyComposite_iff_no_perpetual_primality]
  intro N hpp
  obtain ⟨q, hqB, hq, hq3⟩ := exists_prime_two_mod_three_gt (prod (N + 1))
  have hnd : ¬ q ∣ prod (N + 1) := fun hd =>
    absurd (Nat.le_of_dvd (by have := prod_ge_two (N + 1); omega) hd) (by omega)
  have hq5 : 5 ≤ q := by have := prod_ge_two (N + 1); omega
  obtain ⟨n, hn, hdev⟩ := h q N hq hq3 hq5 hnd
  exact hdev (stageAutonomous_of_prime (hpp n hn))

/-- **The autonomous rung**: `MC ⟹ NoFrozen ⟹ NoAutonomousTail ⟹ (C∞)`. -/
theorem autonomous_rung :
    (MullinConjecture → NoFrozen) ∧ (NoFrozen → NoAutonomousTail) ∧
    (NoAutonomousTail → AutonomousBranch.InfinitelyManyComposite) :=
  ⟨noFrozen_of_mc, noAutonomousTail_of_noFrozen, infinitelyManyComposite_of_noAutonomousTail⟩

/-! ## Landscape -/

/-- **Feedback selection.**  Autonomy modulo a prime is take-all; the greedy rule is
autonomous modulo no odd prime; a capture of `q ≡ 2 (mod 3)` is immediately preceded by a
deviation, and MC forces one for every such prime; an autonomous tail freezes those primes
and makes capture finitely decidable. -/
theorem feedback_selection_landscape :
    (∀ (σ : EuclidRule) (q : ℕ) [Fact q.Prime], Autonomous σ q →
      ∀ E, 2 ≤ E → Nat.Coprime E q → (σ.sel E : ZMod q) = (E : ZMod q)) ∧
    (∀ q : ℕ, [Fact q.Prime] → q ≠ 2 → ¬ Autonomous greedyRule q) ∧
    (∀ (q n : ℕ) [Fact q.Prime], q % 3 = 2 → 5 ≤ q → q ∣ prod (n + 1) + 1 → Deviates q n) ∧
    (MullinConjecture → ∀ q : ℕ, [Fact q.Prime] → q % 3 = 2 → 5 ≤ q →
      ∃ n, Deviates q n ∧ seq (n + 2) = q) ∧
    (∀ (N q : ℕ) [Fact q.Prime], q % 3 = 2 → 5 ≤ q → (∀ n, N ≤ n → StageAutonomous q n) →
      ¬ q ∣ prod (N + 1) → Frozen q) ∧
    (∀ (q N : ℕ) [NeZero q], (∀ n, N ≤ n → StageAutonomous q n) →
      ((∃ k, q ∣ prod (N + k) + 1) ↔ ∃ k, k < q ∧ sylvWalk^[k] (walkZ q N) = -1)) :=
  ⟨fun _ _ _ h _ hE hcop => sel_cast_eq_of_autonomous h hE hcop,
    fun _ _ hq2 => greedy_not_autonomous hq2,
    fun _ _ _ hq3 hq5 hd => deviates_of_dvd_two_mod_three hq3 hq5 hd,
    fun hmc _ _ hq3 hq5 => exists_deviation_before_capture_of_mc hmc hq3 hq5,
    fun _ _ _ hq3 hq5 h hnd => frozen_of_autonomous_tail hq3 hq5 h hnd,
    fun _ _ _ h => capture_iff_of_autonomous_tail h⟩

end FeedbackSelection

end
