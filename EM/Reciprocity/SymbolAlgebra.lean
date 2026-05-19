import EM.Population.HittingSetStructure
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Reciprocity Invariants: the Symbol Algebra (Run R-Reciprocity, first slice)

Companion to `EM/Obstruction/NoInvariant.lean` (Task A: the congruence class) and to
`docs/analysis/reciprocity_invariants.md` (Task C: the assessment this file begins to
formalize).  The max-side omission proofs (Cox–van der Poorten 1968; Booker,
arXiv:1107.3318; Pollack–Treviño, Monthly) run on *reciprocity data*: Kronecker/Jacobi
symbols between sequence data, evaluated at the Euclid number and computed twice — once
top-down by reciprocity, once bottom-up through the factorization.  Task C's verdict is
that on the min side this entire class of invariants collapses; this file lands the
first slice of that verdict, the pure symbol algebra:

* **Euclid unit law** (`euclid_unit_law`): `J(Pₙ + 1 | pᵢ) = 1` for every `i ≤ n` — the
  Euclid number is `≡ 1` modulo every earlier multiplier, so all "top-down" symbols
  against the orbit are pinned to `+1`.  Strong form modulo the whole accumulator:
  `euclid_unit_law_strong`.
* **Euclid parity law** (`euclid_parity_law`): `∏_{i ≤ n} J(pᵢ | p_{n+1}) = J(-1 | p_{n+1})`
  — the accumulator is `≡ -1` modulo the new multiplier, so the product of all symbols
  *at the new prime* is forced to the value `χ₄ p_{n+1}` (`euclid_parity_law_chi4`).
* **Symbol modulus** (`symbolModulus`, `symbolModulus_spec`): the entire level-`n`
  reciprocity datum of a new multiplier `π` — every symbol `J(pᵢ | π)`, the class
  `π mod 8`, and the congruence class `π mod m` — is a function of `π mod Πₙ` where
  `Πₙ = 8·m·Pₙ`.  This is claim (R1) of the assessment: *the reciprocity enrichment is
  exactly the congruence class with a modulus allowed to grow along the orbit.*
* **Character Non-Constancy Lemma** (`char_non_constancy`): a nontrivial character on
  `ZMod D` takes distinct values on primes above any bound `Y`.  This is the §4 lemma —
  the conceptual content of the whole EXTENDS verdict in one theorem.

## Why this kills the min-side transfer (the CvdP dichotomy, symbol version)

The max-side blocking mechanism is **support confinement**: if `p = maxFac(N_{n-1})` is
the last prime `≤ X` to appear, every prime factor of `N_{n-1}` lies in the *finite* set
`{omitted primes, p}`, a single real character `χ_d` can be made constant `= (-1/·)`
there, and the bottom-up product collapses to `(-1 | N) = -1` against the top-down `+1`.

Under `minFac` the confinement inverts: the factor support of the Euclid number is
*cofinite* (all primes `≥ p`), and by `char_non_constancy` **no** nontrivial character
is constant on the primes above any bound.  The discarded cofactor is the large part,
dynamically inert and arithmetically unconstrained; no choice of `d` controls `(d | C)`.
The contradiction machine cannot start.  See the analysis document §§4–5.

## Later slices (per the formalization plan, items 4–9)

`ReciprocityState`/`RTrans` (Definition R), iterated CRT over coprime moduli, the
two-prime fullness construction, the parity-correction lemma, and the assembly
`no_reciprocity_invariant` via Task A's eviction.
-/

open Mullin Euclid MullinGroup RotorRouter
open scoped NumberTheorySymbols
open ZMod

namespace Reciprocity

/-! ## Part 0: Oddness of the multipliers -/

/-- Every multiplier after the seed `2` is an odd prime (the accumulator is even, so the
candidate `Pₙ + 1` is odd). -/
theorem seq_succ_odd (n : ℕ) : Odd (seq (n + 1)) :=
  ((isPrime_iff_natPrime _).mp (seq_isPrime (n + 1))).odd_of_ne_two (seq_succ_ne_two n)

/-! ## Part 1: The Euclid unit law

`Pₙ + 1 ≡ 1 (mod pᵢ)` for every `i ≤ n`, hence every Jacobi symbol of the Euclid number
against an earlier multiplier is `+1`.  This is the "top-down" half of every
Cox–van der Poorten-style computation: symbols whose modulus is built from orbit primes
are pinned to `+1` for free.  -/

/-- **Euclid unit law.**  `J(Pₙ + 1 | pᵢ) = 1` for `i ≤ n`. -/
theorem euclid_unit_law {i n : ℕ} (h : i ≤ n) : J((prod n : ℤ) + 1 | seq i) = 1 := by
  have hdvd : (seq i : ℤ) ∣ (prod n : ℤ) := Int.natCast_dvd_natCast.mpr (seq_dvd_prod i n h)
  have hmod : (prod n : ℤ) + 1 ≡ 1 [ZMOD (seq i : ℤ)] :=
    Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using dvd_neg.mpr hdvd))
  calc J((prod n : ℤ) + 1 | seq i) = J(1 | seq i) := jacobiSym.mod_left' hmod
    _ = 1 := jacobiSym.one_left _

/-- **Euclid unit law, strong form.**  `J(Pₙ + 1 | Pₙ) = 1`: the Euclid number is `≡ 1`
modulo the *entire* accumulator, so the symbol against any divisor of `Pₙ` — in
particular any fundamental discriminant built from orbit primes — is `+1`. -/
theorem euclid_unit_law_strong (n : ℕ) : J((prod n : ℤ) + 1 | prod n) = 1 := by
  have hmod : (prod n : ℤ) + 1 ≡ 1 [ZMOD (prod n : ℤ)] :=
    Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simp))
  calc J((prod n : ℤ) + 1 | prod n) = J(1 | prod n) := jacobiSym.mod_left' hmod
    _ = 1 := jacobiSym.one_left _

/-! ## Part 2: The Euclid parity law

`Pₙ ≡ -1 (mod p_{n+1})`, so the product over `i ≤ n` of the symbols `(pᵢ | p_{n+1})`
collapses to `(-1 | p_{n+1}) = χ₄ p_{n+1}`.  This is the one *relation* the reciprocity
data of the orbit must satisfy — the "bottom-up" law.  In `F₂` coordinates it reads
`Σ_{i≤n} β_{i,n+1} ≡ (p_{n+1} − 1)/2 (mod 2)`.  -/

/-- The accumulator factors the symbol: `J(Pₙ | b) = ∏_{i ≤ n} J(pᵢ | b)`. -/
theorem jacobiSym_seq_prod (b n : ℕ) :
    J((prod n : ℤ) | b) = ∏ i ∈ Finset.range (n + 1), J((seq i : ℤ) | b) := by
  induction n with
  | zero => rw [Finset.prod_range_one, prod_zero, seq_zero]
  | succ n ih =>
      rw [Finset.prod_range_succ, ← ih, prod_succ]
      push_cast
      rw [jacobiSym.mul_left]

/-- **Euclid parity law.**  `∏_{i ≤ n} J(pᵢ | p_{n+1}) = J(-1 | p_{n+1})`. -/
theorem euclid_parity_law (n : ℕ) :
    ∏ i ∈ Finset.range (n + 1), J((seq i : ℤ) | seq (n + 1)) = J(-1 | seq (n + 1)) := by
  rw [← jacobiSym_seq_prod]
  refine jacobiSym.mod_left' ?_
  have hdvd : (seq (n + 1) : ℤ) ∣ (prod n : ℤ) + 1 := by
    have := Int.natCast_dvd_natCast.mpr (seq_dvd_succ_prod n)
    push_cast at this
    exact this
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using hdvd))

/-- **Euclid parity law, evaluated.**  The forced value is `χ₄ p_{n+1}`, i.e. the sign
`(-1)^((p_{n+1}−1)/2)`. -/
theorem euclid_parity_law_chi4 (n : ℕ) :
    ∏ i ∈ Finset.range (n + 1), J((seq i : ℤ) | seq (n + 1)) = χ₄ (seq (n + 1)) :=
  (euclid_parity_law n).trans (jacobiSym.at_neg_one (seq_succ_odd n))

/-! ## Part 3: The symbol modulus (claim R1)

The genuinely new data of the reciprocity enrichment is the symbols whose modulus is the
*new* multiplier: `β_{i,n+1} = (pᵢ | p_{n+1})`.  By `jacobiSym.mod_right'` each such
symbol is a function of `p_{n+1} mod 4pᵢ`; together with the classes mod `8` and mod `m`,
the entire level-`n` symbol update is a function of `π mod Πₙ`, `Πₙ := 8·m·Pₙ`.  The
reciprocity class is not a different *kind* of invariant — it is the congruence class
with a growing modulus.  This is what routes later slices through Task A's machinery. -/

/-- The moving symbol modulus `Πₙ = 8·m·Pₙ`.  All level-`n` reciprocity data of a new
multiplier is determined by its class mod `Πₙ` (`symbolModulus_spec`). -/
def symbolModulus (m n : ℕ) : ℕ := 8 * m * prod n

theorem four_mul_seq_dvd_symbolModulus {m i n : ℕ} (h : i ≤ n) :
    4 * seq i ∣ symbolModulus m n :=
  mul_dvd_mul (dvd_mul_of_dvd_left ⟨2, rfl⟩ m) (seq_dvd_prod i n h)

/-- A Jacobi symbol with fixed numerator `a` is a function of the (odd) denominator
mod `4a`. -/
theorem symbol_eq_of_modEq {a π π' : ℕ} (hπ : Odd π) (hπ' : Odd π')
    (h : π ≡ π' [MOD 4 * a]) : J((a : ℤ) | π) = J((a : ℤ) | π') := by
  rw [jacobiSym.mod_right' a hπ, jacobiSym.mod_right' a hπ']
  exact congrArg (fun k => J((a : ℤ) | k)) h

/-- **The symbol modulus determines everything (R1).**  If two odd candidates for the
new multiplier agree mod `Πₙ = 8·m·Pₙ`, they carry identical level-`n` reciprocity data:
every symbol `J(pᵢ | ·)` for `i ≤ n`, the class mod `8` (hence `χ₄`, `χ₈`), and the
underlying congruence class mod `m`. -/
theorem symbolModulus_spec {m n π π' : ℕ} (hπ : Odd π) (hπ' : Odd π')
    (h : π ≡ π' [MOD symbolModulus m n]) :
    (∀ i, i ≤ n → J((seq i : ℤ) | π) = J((seq i : ℤ) | π')) ∧
      π ≡ π' [MOD 8] ∧ π ≡ π' [MOD m] :=
  ⟨fun _ hi => symbol_eq_of_modEq hπ hπ' (h.of_dvd (four_mul_seq_dvd_symbolModulus hi)),
    h.of_dvd ((dvd_mul_right 8 m).mul_right (prod n)),
    h.of_dvd ((dvd_mul_left m 8).mul_right (prod n))⟩

/-! ## Part 4: The Character Non-Constancy Lemma (§4 of the assessment)

The max-side argument blocks a prime by making a real character *constant* on the factor
support of the Euclid number — possible because `maxFac` confines that support to a
finite set.  `minFac` confines the support to a *cofinite* set of primes, and no
nontrivial character is constant on the primes above any bound: Dirichlet supplies
primes in both a class where the character is `1` and a class where it is not.  This
lemma is the precise reason the Cox–van der Poorten / Booker transfer dies on the min
side, and the standalone conceptual content of the EXTENDS verdict. -/

/-- **Character Non-Constancy.**  A nontrivial character `χ` on `ZMod D` is not constant
on the primes exceeding any bound `Y`: there are primes `p, p' > Y` with
`χ p ≠ χ p'`. -/
theorem char_non_constancy {D : ℕ} [NeZero D] {R : Type*} [CommMonoidWithZero R]
    {χ : MulChar (ZMod D) R} (hχ : χ ≠ 1) (Y : ℕ) :
    ∃ p p' : ℕ, p.Prime ∧ p'.Prime ∧ Y < p ∧ Y < p' ∧
      χ (p : ZMod D) ≠ χ (p' : ZMod D) := by
  obtain ⟨b, hb⟩ := MulChar.ne_one_iff.mp hχ
  obtain ⟨p, hpY, hpp, hpe⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := D) (a := 1) isUnit_one Y
  obtain ⟨p', hp'Y, hp'p, hp'e⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := D) (a := (b : ZMod D)) b.isUnit Y
  refine ⟨p, p', hpp, hp'p, hpY, hp'Y, ?_⟩
  rw [hpe, hp'e, map_one]
  exact fun hcontra => hb hcontra.symm

/-- **Non-constancy in the form the transfer argument needs**: for every bound `Y` there
is a prime above `Y` on which `χ` does *not* take a prescribed value `c` — no single
target value can be enforced on the whole cofinite factor support. -/
theorem char_not_eventually_constant {D : ℕ} [NeZero D] {R : Type*}
    [CommMonoidWithZero R] {χ : MulChar (ZMod D) R} (hχ : χ ≠ 1) (c : R) (Y : ℕ) :
    ∃ p : ℕ, p.Prime ∧ Y < p ∧ χ (p : ZMod D) ≠ c := by
  obtain ⟨p, p', hpp, hp'p, hpY, hp'Y, hne⟩ := char_non_constancy hχ Y
  by_cases hc : χ (p : ZMod D) = c
  · exact ⟨p', hp'p, hp'Y, fun h => hne (hc.trans h.symm)⟩
  · exact ⟨p, hpp, hpY, hc⟩

end Reciprocity
