import EM.IK.Ch7AdditiveLS

/-!
# Chapter 7 (Part 4): Sieve Applications (Iwaniec-Kowalski)

§7.6 of Iwaniec-Kowalski: Large sieve as sieve, sieve weights,
Lemma 7.15, Theorem 7.14, Linnik's theorem on small quadratic non-residues,
and the general squarefree modulus case.

## References
- [IK] H. Iwaniec, E. Kowalski, *Analytic Number Theory*, 2004
-/

noncomputable section

open Classical

namespace IK

open Complex Finset BigOperators

/-!
## §7.6 Applications of the large sieve to sieving problems

This section formalizes the application of the large sieve inequality to sieving problems,
following IK §7.6.

### Overview

A **sieving problem** consists of:
- A finite set M of integers contained in an interval of length N
- A finite set P of primes
- For each p in P, a set Omega_p of "excluded" residue classes mod p

The **sifted set** S(M, P, Omega) = {m in M : m mod p not in Omega_p for all p in P}.

**Theorem 7.14** gives an upper bound: |S| ≤ (N + Q²) / H, where
H = Σ_{q ≤ Q, q squarefree, p|q → p in P} Π_{p|q} ω(p)/(p − ω(p)).

**Theorem 7.16** (Linnik): For almost all primes p, the least quadratic non-residue
is at most p^{1/(4√e) + ε}.

### Key definitions

- `sieveWeight`: the multiplicative weight h(p) = ω(p)/(p − ω(p))
- `Lemma715`: the individual modulus bound h(q)|S(0)|² ≤ Σ* |S(a/q)|²
- `LargeSieveAsSieve`: Theorem 7.14, the sifted set upper bound
- `LinnikSmallQNR`: Theorem 7.16, Linnik's result on small quadratic non-residues
-/

section LargeSieveAsSieve

/-!
### Sieve weights

The weight function h(p) = ω(p)/(p − ω(p)) for primes p with ω(p) = |Ω_p|.
For squarefree q with all prime factors in P, h(q) = Π_{p|q} h(p).
-/

/-- The sieve weight for a single prime p with ω(p) excluded residues — IK (7.37).
    h(p) = ω(p) / (p − ω(p)), assuming ω(p) < p. -/
def sieveWeight (p : ℕ) (ωp : ℕ) : ℝ :=
  (ωp : ℝ) / ((p : ℝ) - (ωp : ℝ))

/-- The sieve weight for a squarefree modulus q is the product of h(p) over prime factors.
    For q = p₁ · ... · pₖ squarefree, h(q) = Π h(pᵢ). -/
def sieveWeightProd (ω : ℕ → ℕ) (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, sieveWeight p (ω p)

/-- The total sieve density: H = Σ_{q ≤ Q} μ²(q) · Π_{p|q} h(p),
    summed over squarefree q whose prime factors all lie in a set P — IK (7.36). -/
def sieveDensity (P : Finset ℕ) (ω : ℕ → ℕ) (Q : ℕ) : ℝ :=
  ∑ q ∈ (Finset.range (Q + 1)).filter (fun q =>
    0 < q ∧ Squarefree q ∧ ∀ p ∈ q.primeFactors, p ∈ P),
    sieveWeightProd ω q

/-- For a single prime p, the sieve weight h(p) is nonneg when ω(p) < p. -/
theorem sieveWeight_nonneg {p : ℕ} {ωp : ℕ} (_hp : 0 < p) (hω : ωp < p) :
    0 ≤ sieveWeight p ωp := by
  unfold sieveWeight
  apply div_nonneg
  · exact Nat.cast_nonneg' ωp
  · have : (ωp : ℝ) < (p : ℝ) := Nat.cast_lt.mpr hω
    linarith

/-- For a single prime p, h(p) is positive when 0 < ω(p) < p. -/
theorem sieveWeight_pos {p : ℕ} {ωp : ℕ} (_hp : 0 < p) (hωpos : 0 < ωp) (hω : ωp < p) :
    0 < sieveWeight p ωp := by
  unfold sieveWeight
  apply div_pos
  · exact Nat.cast_pos.mpr hωpos
  · have : (ωp : ℝ) < (p : ℝ) := Nat.cast_lt.mpr hω
    linarith

/-- The sieve weight product over prime factors of q is nonneg when ω(p) < p for all p | q. -/
theorem sieveWeightProd_nonneg {ω : ℕ → ℕ} {q : ℕ}
    (hq : ∀ p ∈ q.primeFactors, ω p < p) :
    0 ≤ sieveWeightProd ω q := by
  unfold sieveWeightProd
  apply Finset.prod_nonneg
  intro p hp
  exact sieveWeight_nonneg (Nat.pos_of_ne_zero (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp)))
    (hq p hp)

/-!
### Sifted-support condition

For Lemma 7.15, the sequence `a` must be **sifted**: `a_n = 0` whenever `n mod p`
falls in an excluded residue class `Ω_p` for some prime `p | q`. Without this
condition the inequality is false (e.g., p=5, ω=3, a=(1,...,1) gives LHS > RHS = 0).

We parameterize the excluded classes as `Ω : ℕ → Finset ℕ` where `Ω p` gives
the set of excluded residues mod p (as natural numbers < p).
-/

/-- A sequence `a : Fin N → ℂ` is **sifted** with respect to excluded residues `Ω`
    and a set of primes `primes`: `a n = 0` whenever `n mod p ∈ Ω p` for some
    prime `p` in `primes`. -/
def IsSifted {N : ℕ} (a : Fin N → ℂ) (primes : Finset ℕ) (Ω : ℕ → Finset ℕ) : Prop :=
  ∀ n : Fin N, (∃ p ∈ primes, (n : ℕ) % p ∈ Ω p) → a n = 0

/-!
### Lemma 7.15: Individual modulus sieve bound

For any positive squarefree q whose prime factors lie in P, and with ω(p) < p for each
such prime, and for a sequence `a` that is **sifted** (a_n = 0 when n mod p ∈ Ω_p
for some p | q, where |Ω_p| = ω(p)):

  h(q) · |S(0)|² ≤ Σ*_{a mod q} |S(a/q)|²

where S(α) = Σ_n a_n e(nα) is the trigonometric polynomial.

The proof proceeds by induction on the number of prime factors of q:
- Base case (q = p prime): follows from DFT Parseval + Cauchy-Schwarz
- Inductive step: uses CRT factorization of the coprime sum

This is stated as an open Prop since the inductive step requires CRT factorization.
The base case (prime q) is proved as `lemma715_prime`.
-/

/-- **Lemma 7.15** (IK): Individual modulus sieve bound — IK (7.39).
    For squarefree q with prime factors in P and ω(p) < p, and a sifted sequence:
    h(q) · |S(0)|² ≤ Σ*_{a mod q} |S(a/q)|².

    Here S(α) = Σ_{n=1}^{N} a_n e(nα), and the sum on the right runs over
    (a, q) = 1. The sequence `a` must satisfy the sifted-support condition:
    `a n = 0` whenever `n mod p ∈ Ω p` for some prime factor `p` of `q`.

    The proof uses orthogonality of additive characters to show that the
    sum over non-excluded residues is bounded by the coprime exponential sums,
    with induction on the number of prime factors via CRT. -/
def Lemma715 : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℂ) (q : ℕ) (ω : ℕ → ℕ) (Ω : ℕ → Finset ℕ),
    0 < N → 0 < q → Squarefree q →
    (∀ p ∈ q.primeFactors, ω p < p) →
    (∀ p ∈ q.primeFactors, (Ω p).card = ω p) →
    (∀ p ∈ q.primeFactors, ∀ r ∈ Ω p, r < p) →
    IsSifted a q.primeFactors Ω →
    sieveWeightProd ω q *
      ‖∑ n : Fin N, a n‖ ^ 2 ≤
    ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2

/-!
### Lemma 7.15 base case: prime modulus

For q = p prime with ω excluded residue classes mod p, the bound
h(p) · |S(0)|² ≤ ∑_{b=1}^{p-1} |S(b/p)|² follows from:

1. **Residue class grouping**: Define A(r) = ∑_{n ≡ r (mod p)} a_n.
   Then S(0) = ∑_r A(r) and S(b/p) = ∑_r A(r)·e(rb/p).

2. **DFT Parseval over Z/pZ**: ∑_{b=0}^{p-1} |∑_r A(r)·e(rb/p)|² = p · ∑_r |A(r)|².

3. **Sifted support**: A(r) = 0 for r ∈ Ω_p, so by Cauchy-Schwarz:
   |S(0)|² = |∑_{r ∉ Ω_p} A(r)|² ≤ (p−ω) · ∑_r |A(r)|².

4. **Combine**: coprime sum = p·∑|A(r)|² − |S(0)|² ≥ ω/(p−ω)·|S(0)|² = h(p)·|S(0)|².

We state the DFT Parseval step as an open Prop (it could be derived from
`zmod_dft_parseval` in LargeSieveHarmonic, but requires bridging conventions
between `ZMod.dft`/`stdAddChar` and `eAN`).
-/

/-- **DFT Parseval for Z/pZ via eAN**: For prime p and any function A : Fin p → ℂ,
    ∑_{b=0}^{p-1} ‖∑_{r=0}^{p-1} A(r) · e(r·b/p)‖² = p · ∑_r ‖A(r)‖².

    This is the standard Parseval identity for the discrete Fourier transform
    on Z/pZ, expressed using the exponential `eAN`. It could be derived from
    `zmod_dft_parseval` in LargeSieveHarmonic by bridging between `stdAddChar`
    and `eAN`, but we state it independently for modularity. -/
def DFTParsevalPrime : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (A : Fin p → ℂ),
      ∑ b : Fin p,
        ‖∑ r : Fin p, A r * eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (p : ℝ))‖ ^ 2 =
      (p : ℝ) * ∑ r : Fin p, ‖A r‖ ^ 2

/-- **DFTParsevalPrime is a theorem**: proved by bridging from `exp_sum_energy_eq_parseval`
    (which works over `ZMod p`) to the `Fin p`-indexed form using `stdAddChar_mul_intCast_eq_eAN`.

    For `p = p' + 1`, `ZMod (p'+1) = Fin (p'+1)` definitionally, so the reindexing is transparent.
    The key step is showing that `stdAddChar (b * n)` equals `eAN(val(n) * val(b) / p)`. -/
theorem dft_parseval_prime_proved : DFTParsevalPrime := by
  intro p hp A
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- Decompose p = p' + 1 so ZMod p = Fin p definitionally
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  -- For p = p'+1, ZMod (p'+1) = Fin (p'+1) definitionally, so f = A
  -- Apply exp_sum_energy_eq_parseval (which works over ZMod p)
  have hpars := exp_sum_energy_eq_parseval (p := p' + 1) A
  -- hpars : ∑ a, ‖∑ n, A n * stdAddChar (a * n)‖² = (p'+1) * ∑ n, ‖A n‖²
  -- We need: for each b, stdAddChar(b * r) = eAN(r * b / (p'+1))
  -- Then the LHS of hpars matches our goal's LHS
  -- Bridge stdAddChar to eAN pointwise
  suffices hinner : ∀ (b r : Fin (p' + 1)),
      (ZMod.stdAddChar (N := p' + 1)
        ((b : ZMod (p' + 1)) * (r : ZMod (p' + 1))) : ℂ) =
      eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑(p' + 1) : ℝ)) by
    have key : ∀ b : Fin (p' + 1),
        (fun r => A r * eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / ↑(p' + 1))) =
        (fun r => A r * (ZMod.stdAddChar (N := p' + 1) ((b : ZMod (p' + 1)) * (r : ZMod (p' + 1))) : ℂ)) := by
      intro b; ext r; congr 1; exact (hinner b r).symm
    simp_rw [key] at hpars ⊢; exact hpars
  intro b r
  have hbridge := stdAddChar_mul_intCast_eq_eAN (p := p' + 1)
    (b : ZMod (p' + 1)) ((r : ℕ) : ℤ)
  have hcast : (((r : ℕ) : ℤ) : ZMod (p' + 1)) = (r : ZMod (p' + 1)) := by
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val (show ZMod (p' + 1) from r)
  rw [hcast] at hbridge
  exact hbridge.trans (by rw [eAN_eq_root_eAN]; congr 1)

/-- **Residue class sum**: for a sequence `a : Fin N → ℂ` and modulus `p`,
    `residueClassSum a p r` is ∑_{n : Fin N, n ≡ r (mod p)} a_n. -/
noncomputable def residueClassSum {N : ℕ} (a : Fin N → ℂ) (p : ℕ) (r : Fin p) : ℂ :=
  ∑ n ∈ (Finset.univ.filter (fun n : Fin N => (n : ℕ) % p = (r : ℕ))), a n

/-- The residue class sum of an excluded class is zero for a sifted sequence. -/
theorem residueClassSum_excluded {N p : ℕ} (a : Fin N → ℂ) (Ωp : Finset ℕ)
    (hsifted : ∀ n : Fin N, (n : ℕ) % p ∈ Ωp → a n = 0)
    (r : Fin p) (hr : (r : ℕ) ∈ Ωp) :
    residueClassSum a p r = 0 := by
  unfold residueClassSum
  apply Finset.sum_eq_zero
  intro n hn
  rw [Finset.mem_filter] at hn
  exact hsifted n (hn.2 ▸ hr)

/-- **Arithmetic core of Lemma 7.15 base case**: Given two real numbers
    `S0sq` (= |S(0)|²) and `sumAsq` (= ∑_r |A(r)|²), and parameters p, ωp
    with ωp < p, if:
    (A) `coprime_sum ≥ p * sumAsq - S0sq`  (from DFT Parseval, subtracting b=0)
    (B) `S0sq ≤ (p - ωp) * sumAsq`          (from Cauchy-Schwarz on non-excluded)
    then `ωp/(p-ωp) * S0sq ≤ coprime_sum`. -/
theorem sieve_weight_bound_of_parseval_cs
    {p ωp : ℕ} {S0sq sumAsq coprime_sum : ℝ}
    (hωp : ωp < p)
    (_hS0_nn : 0 ≤ S0sq) (_hsumA_nn : 0 ≤ sumAsq)
    (hA : (p : ℝ) * sumAsq - S0sq ≤ coprime_sum)
    (hB : S0sq ≤ ((p : ℝ) - (ωp : ℝ)) * sumAsq) :
    (ωp : ℝ) / ((p : ℝ) - (ωp : ℝ)) * S0sq ≤ coprime_sum := by
  have hp_ω_pos : (0 : ℝ) < (p : ℝ) - (ωp : ℝ) := by
    have : (ωp : ℝ) < (p : ℝ) := Nat.cast_lt.mpr hωp
    linarith
  -- From (B): sumAsq ≥ S0sq / (p - ωp)
  have hsumA_lb : S0sq / ((p : ℝ) - (ωp : ℝ)) ≤ sumAsq := by
    rw [div_le_iff₀ hp_ω_pos]
    linarith
  -- From (A): coprime_sum ≥ p * sumAsq - S0sq ≥ p * S0sq/(p-ωp) - S0sq
  --         = S0sq * (p/(p-ωp) - 1) = S0sq * ωp/(p-ωp)
  calc (ωp : ℝ) / ((p : ℝ) - (ωp : ℝ)) * S0sq
      = S0sq * ((ωp : ℝ) / ((p : ℝ) - (ωp : ℝ))) := by ring
    _ = S0sq * (((p : ℝ) - ((p : ℝ) - (ωp : ℝ))) / ((p : ℝ) - (ωp : ℝ))) := by ring
    _ = S0sq * ((p : ℝ) / ((p : ℝ) - (ωp : ℝ)) - 1) := by
        congr 1; rw [sub_div, div_self (ne_of_gt hp_ω_pos)]
    _ = (p : ℝ) * (S0sq / ((p : ℝ) - (ωp : ℝ))) - S0sq := by ring
    _ ≤ (p : ℝ) * sumAsq - S0sq := by
        linarith [mul_le_mul_of_nonneg_left hsumA_lb (le_of_lt (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega : p ≠ 0))))]
    _ ≤ coprime_sum := hA

/-- **Lemma 7.15 base case** (prime modulus): For prime p with ω < p excluded
    residue classes and a sifted sequence, h(p) · |S(0)|² ≤ ∑_{b coprime to p} |S(b/p)|².

    This is the base case of the induction in IK Lemma 7.15. The proof uses:
    1. DFT Parseval to relate coprime exponential sums to residue class sums
    2. Cauchy-Schwarz on the non-excluded residue classes
    3. The sifted-support condition (excluded class sums vanish)

    Stated as an open Prop since it requires the DFT Parseval identity
    (`DFTParsevalPrime`) and the regrouping identity (∑_n a_n e(nb/p) = ∑_r A(r) e(rb/p)).
    The arithmetic combination (Parseval + C-S → sieve weight bound) is proved
    as `sieve_weight_bound_of_parseval_cs`. -/
def Lemma715Prime : Prop :=
  ∀ (N : ℕ) (a : Fin N → ℂ) (p : ℕ) (ωp : ℕ) (Ωp : Finset ℕ),
    0 < N → Nat.Prime p →
    ωp < p →
    Ωp.card = ωp →
    (∀ r ∈ Ωp, r < p) →
    (∀ n : Fin N, (n : ℕ) % p ∈ Ωp → a n = 0) →
    sieveWeight p ωp *
      ‖∑ n : Fin N, a n‖ ^ 2 ≤
    ∑ b ∈ (Finset.range p).filter (Nat.Coprime · p),
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (p : ℝ))‖ ^ 2

/-- `eAN(n*b/p) = eAN((n%p)*b/p)` for natural numbers n, b, p with p > 0.
    This uses `n = p*(n/p) + (n%p)` and `eAN(integer) = 1`. -/
theorem eAN_mod_eq {n b p : ℕ} (hp : 0 < p) :
    eAN ((↑n : ℝ) * (↑b : ℝ) / (↑p : ℝ)) =
    eAN ((↑(n % p) : ℝ) * (↑b : ℝ) / (↑p : ℝ)) := by
  rw [eAN_eq_root_eAN, eAN_eq_root_eAN]
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp)
  -- Strategy: show n*b/p = (n/p)*b + (n%p)*b/p as reals, where (n/p)*b is integer.
  -- To avoid Nat.cast_div turning ↑(n/p) into ↑n/↑p, we work through intermediate steps.
  -- Step 1: n = (n/p)*p + n%p as naturals, hence as reals
  set q := n / p with hq_def
  have hdiv : p * q + n % p = n := Nat.div_add_mod n p
  have hdiv_real : (n : ℝ) = (q : ℝ) * (p : ℝ) + (↑(n % p) : ℝ) := by
    have : (p : ℝ) * (q : ℝ) + (↑(n % p) : ℝ) = (n : ℝ) := by exact_mod_cast hdiv
    linarith
  -- Step 2: The key arithmetic identity
  have harg : (↑n : ℝ) * ↑b / ↑p = (↑q : ℝ) * (↑b : ℝ) + (↑(n % p) : ℝ) * ↑b / ↑p := by
    rw [hdiv_real]
    field_simp
  rw [harg, _root_.eAN_add]
  -- Step 3: eAN(q*b) = 1 since q*b is a natural number
  have hint : _root_.eAN ((↑q : ℝ) * (↑b : ℝ)) = 1 := by
    have : (↑q : ℝ) * (↑b : ℝ) = (↑(q * b : ℕ) : ℝ) := by push_cast; ring
    rw [this, show (↑(q * b : ℕ) : ℝ) = (↑((q * b : ℕ) : ℤ) : ℝ) from by push_cast; rfl]
    exact _root_.eAN_intCast _
  rw [hint, one_mul]

/-- The regrouping identity: the exponential sum ∑_n a_n e(nb/p) equals
    ∑_r A(r) e(rb/p) where A = residueClassSum. This follows from
    `eAN_mod_eq` (e(nb/p) = e((n%p)b/p)) and partitioning by residue class.

    The proof uses `Finset.sum_fiberwise` to partition `Fin N` by residue mod p,
    then factors out `eAN(r*b/p)` on each fiber (constant since `n%p = r`). -/
theorem expsum_eq_residueClassSum_expsum {N p : ℕ} (a : Fin N → ℂ) (b : Fin p)
    (hp : 0 < p) :
    ∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ)) =
    ∑ r : Fin p, residueClassSum a p r *
      eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ)) := by
  -- Step 1: Replace eAN(n*b/p) with eAN((n%p)*b/p) using eAN_mod_eq
  have lhs_eq : ∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ)) =
      ∑ n : Fin N, a n * eAN ((↑((n : ℕ) % p) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ)) :=
    Finset.sum_congr rfl fun n _ => by rw [eAN_mod_eq hp]
  rw [lhs_eq]
  -- Step 2: Define g : Fin N → Fin p as g(n) = ⟨n%p, ...⟩
  let g : Fin N → Fin p := fun n => ⟨(n : ℕ) % p, Nat.mod_lt _ hp⟩
  -- Step 3: Use Finset.sum_fiberwise to partition by g
  -- ∑ n, f n = ∑ r, ∑ n with g n = r, f n
  rw [← Finset.sum_fiberwise (Finset.univ) g]
  -- Step 4: For each fiber r, show the inner sum equals residueClassSum * eAN(r*b/p)
  congr 1; ext r
  -- On the fiber where g(i) = r, we have (i : ℕ) % p = (r : ℕ),
  -- so eAN((i%p)*b/p) = eAN(r*b/p), and we can factor it out.
  have fiber_eq : ∀ i ∈ Finset.univ.filter (fun i : Fin N => g i = r),
      a i * eAN ((↑((i : ℕ) % p) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ)) =
      a i * eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, g] at hi
    have hmod : (i : ℕ) % p = (r : ℕ) := Fin.val_eq_of_eq hi
    rw [hmod]
  rw [Finset.sum_congr rfl fiber_eq, ← Finset.sum_mul]
  congr 1
  -- The sum over the fiber is residueClassSum
  unfold residueClassSum
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, g]
    constructor
    · intro h; exact Fin.val_eq_of_eq h
    · intro h; exact Fin.ext h
  · intro _ _; rfl

/-- Cauchy-Schwarz for finset sums of complex numbers:
    ‖∑_{i ∈ s} v_i‖² ≤ |s| · ∑_{i ∈ s} ‖v_i‖².
    Follows from triangle inequality + real Cauchy-Schwarz. -/
theorem norm_sq_sum_le_card_mul_sum_norm_sq {ι : Type*}
    (s : Finset ι) (v : ι → ℂ) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  -- ‖∑ v_i‖ ≤ ∑ ‖v_i‖ (triangle)
  have htri : ‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖ := norm_sum_le s v
  -- (∑ ‖v_i‖)² ≤ |s| · ∑ ‖v_i‖² (real C-S)
  have hcs : (∑ i ∈ s, ‖v i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
    exact sq_sum_le_card_mul_sum_sq
  calc ‖∑ i ∈ s, v i‖ ^ 2 ≤ (∑ i ∈ s, ‖v i‖) ^ 2 := by
        exact sq_le_sq' (by linarith [norm_nonneg (∑ i ∈ s, v i)]) htri
    _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖ ^ 2 := hcs

/-- For prime p, the sum over coprime residues (in `Finset.range p`) equals
    the sum over nonzero elements of `Fin p`. -/
theorem coprime_range_eq_nonzero_fin {p : ℕ} (hp : Nat.Prime p) (f : ℕ → ℝ) :
    ∑ b ∈ (Finset.range p).filter (Nat.Coprime · p), f b =
    ∑ b ∈ (Finset.univ : Finset (Fin p)).filter (fun b : Fin p => (b : ℕ) ≠ 0),
      f (b : ℕ) := by
  -- Forward: ℕ → Fin p via (· % p)
  -- Inverse: Fin p → ℕ via Fin.val
  apply Finset.sum_nbij' (fun b => (⟨b % p, Nat.mod_lt b hp.pos⟩ : Fin p)) (fun (b : Fin p) => (b : ℕ))
  · -- forward maps to target
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hbr := (Finset.mem_filter.mp hb).1
    have hb_lt := Finset.mem_range.mp hbr
    rw [Nat.mod_eq_of_lt hb_lt]
    intro h0; rw [h0] at hb
    exact absurd ((Finset.mem_filter.mp hb).2) (by simp [Nat.coprime_zero_left, hp.one_lt.ne'])
  · -- inverse maps to source
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨b.isLt, (hp.coprime_iff_not_dvd.mpr (fun hdvd =>
      hb (Nat.eq_zero_of_dvd_of_lt hdvd b.isLt))).symm⟩
  · -- left inverse
    intro b hb
    have hb_lt := Finset.mem_range.mp ((Finset.mem_filter.mp hb).1)
    simp [Nat.mod_eq_of_lt hb_lt]
  · -- right inverse
    intro b hb
    simp [Nat.mod_eq_of_lt b.isLt]
  · -- function values match
    intro b hb
    have hb_lt := Finset.mem_range.mp ((Finset.mem_filter.mp hb).1)
    simp [Nat.mod_eq_of_lt hb_lt]

/-- **Reduction**: `DFTParsevalPrime` implies `Lemma715Prime`.

    The proof combines:
    1. Regrouping: ∑_n a_n e(nb/p) = ∑_r A(r) e(rb/p)  (`expsum_eq_residueClassSum_expsum`)
    2. DFT Parseval: full sum (b=0..p-1) = p · ∑_r |A(r)|²  (`DFTParsevalPrime`)
    3. Excluded vanishing: A(r) = 0 for r ∈ Ωp  (`residueClassSum_excluded`)
    4. Cauchy-Schwarz on non-excluded classes  (`norm_sq_sum_le_card_mul_sum_norm_sq`)
    5. Arithmetic combination  (`sieve_weight_bound_of_parseval_cs`)

    The key bookkeeping step (coprime-to-nonzero bijection for prime p) is
    proved as `coprime_range_eq_nonzero_fin`. -/
theorem dftParseval_implies_lemma715Prime :
    DFTParsevalPrime → Lemma715Prime := by
  intro hParseval N a p ωp Ωp _hN hp hωp hcard hΩ_valid hsifted
  set A := residueClassSum a p
  -- Step 1: S(0) = ∑_r A(r)
  have s0_eq : ∑ n : Fin N, a n = ∑ r : Fin p, A r := by
    have h := expsum_eq_residueClassSum_expsum a ⟨0, hp.pos⟩ hp.pos
    simp only [Nat.cast_zero, mul_zero, zero_div] at h
    convert h using 1
    · apply Finset.sum_congr rfl; intro n _
      rw [show eAN (0 : ℝ) = 1 from by rw [eAN_eq_root_eAN]; exact _root_.eAN_zero, mul_one]
    · apply Finset.sum_congr rfl; intro r _
      rw [show eAN (0 : ℝ) = 1 from by rw [eAN_eq_root_eAN]; exact _root_.eAN_zero, mul_one]
  rw [s0_eq]
  -- Step 2: Regroup each coprime exponential sum
  have exp_regroup : ∀ b ∈ (Finset.range p).filter (Nat.Coprime · p),
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (p : ℝ))‖ ^ 2 =
      ‖∑ r : Fin p, A r * eAN ((↑(r : ℕ) : ℝ) * (b : ℝ) / (p : ℝ))‖ ^ 2 := by
    intro b hb
    have hb_lt : b < p := Finset.mem_range.mp ((Finset.mem_filter.mp hb).1)
    have := expsum_eq_residueClassSum_expsum a ⟨b, hb_lt⟩ hp.pos
    rw [this]
  rw [Finset.sum_congr rfl exp_regroup]
  -- Step 3: Parseval identity
  have parseval := hParseval p hp A
  -- Step 4: Split b=0 and b≠0 in Parseval sum
  have eAN_zero_eq : eAN (0 : ℝ) = 1 := by rw [eAN_eq_root_eAN]; exact _root_.eAN_zero
  have full_split : (p : ℝ) * ∑ r : Fin p, ‖A r‖ ^ 2 =
      ‖∑ r : Fin p, A r‖ ^ 2 +
      ∑ b ∈ (Finset.univ : Finset (Fin p)).filter (fun b : Fin p => (b : ℕ) ≠ 0),
        ‖∑ r : Fin p, A r * eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ))‖ ^ 2 := by
    rw [← parseval, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun b : Fin p => (b : ℕ) = 0)]
    congr 1
    have h0_unique : Finset.univ.filter (fun b : Fin p => (b : ℕ) = 0) = {⟨0, hp.pos⟩} := by
      ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
    rw [h0_unique, Finset.sum_singleton]
    congr 2; apply Finset.sum_congr rfl; intro r _
    simp only [Nat.cast_zero, mul_zero, zero_div, eAN_zero_eq, mul_one]
  -- Step 5: coprime sum (range) = nonzero sum (Fin p)
  have coprime_eq_nonzero := coprime_range_eq_nonzero_fin hp
    (fun b => ‖∑ r : Fin p, A r * eAN ((↑(r : ℕ) : ℝ) * (↑b : ℝ) / (↑p : ℝ))‖ ^ 2)
  rw [coprime_eq_nonzero]
  -- Goal: sieveWeight p ωp * ‖∑ A r‖² ≤ ∑_{b≠0} ‖∑ A_r e(rb/p)‖²
  -- From full_split: nonzero sum = p * ∑ ‖A r‖² - ‖∑ A r‖²
  have coprime_bound : (p : ℝ) * ∑ r : Fin p, ‖A r‖ ^ 2 - ‖∑ r : Fin p, A r‖ ^ 2 ≤
      ∑ b ∈ (Finset.univ : Finset (Fin p)).filter (fun b : Fin p => (b : ℕ) ≠ 0),
        ‖∑ r : Fin p, A r * eAN ((↑(r : ℕ) : ℝ) * (↑(b : ℕ) : ℝ) / (↑p : ℝ))‖ ^ 2 := by
    linarith [full_split]
  -- Step 6: Excluded class handling
  have hA_excl : ∀ r : Fin p, (r : ℕ) ∈ Ωp → A r = 0 :=
    fun r hr => residueClassSum_excluded a Ωp hsifted r hr
  -- ∑ A r = ∑_{r ∉ Ω} A r (excluded vanish)
  have sum_eq : ∑ r : Fin p, A r =
      ∑ r ∈ Finset.univ.filter (fun r : Fin p => (r : ℕ) ∉ Ωp), A r := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : Fin p => (r : ℕ) ∈ Ωp)]
    rw [Finset.sum_eq_zero (fun r hr => hA_excl r (Finset.mem_filter.mp hr).2), zero_add]
  -- ∑ ‖A r‖² = ∑_{r ∉ Ω} ‖A r‖² (excluded vanish)
  have norm_eq : ∑ r : Fin p, ‖A r‖ ^ 2 =
      ∑ r ∈ Finset.univ.filter (fun r : Fin p => (r : ℕ) ∉ Ωp), ‖A r‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : Fin p => (r : ℕ) ∈ Ωp)]
    rw [Finset.sum_eq_zero (fun r hr => by
      simp [hA_excl r (Finset.mem_filter.mp hr).2]), zero_add]
  -- Card of non-excluded = p - ωp
  set S := Finset.univ.filter (fun r : Fin p => (r : ℕ) ∉ Ωp)
  have hS_card : S.card = p - ωp := by
    show (Finset.univ.filter (fun r : Fin p => (r : ℕ) ∉ Ωp)).card = p - ωp
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
        Finset.card_univ, Fintype.card_fin]
    congr 1; rw [← hcard]
    -- Show #{r : Fin p | (r : ℕ) ∈ Ωp} = #Ωp via forward/inverse bijection
    apply Finset.card_nbij' (fun (r : Fin p) => (r : ℕ))
      (fun (b : ℕ) => ⟨b % p, Nat.mod_lt b hp.pos⟩)
    · intro r hr
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp hr)).2
    · intro b hb
      rw [Finset.mem_coe]
      have hb' := Finset.mem_coe.mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by rwa [Fin.val_mk, Nat.mod_eq_of_lt (hΩ_valid b hb')]⟩
    · intro r _; simp [Nat.mod_eq_of_lt r.isLt]
    · intro b hb
      have hb' := Finset.mem_coe.mp hb
      simp [Nat.mod_eq_of_lt (hΩ_valid b hb')]
  -- Step 7: Cauchy-Schwarz
  have cs : ‖∑ r : Fin p, A r‖ ^ 2 ≤ ((p : ℝ) - (ωp : ℝ)) * ∑ r : Fin p, ‖A r‖ ^ 2 := by
    rw [sum_eq, norm_eq]
    calc ‖∑ r ∈ S, A r‖ ^ 2
        ≤ (S.card : ℝ) * ∑ r ∈ S, ‖A r‖ ^ 2 := norm_sq_sum_le_card_mul_sum_norm_sq S A
      _ = ((p : ℝ) - (ωp : ℝ)) * ∑ r ∈ S, ‖A r‖ ^ 2 := by
          congr 1; rw [hS_card, Nat.cast_sub (le_of_lt hωp)]
  -- Step 8: Apply arithmetic core
  show sieveWeight p ωp * ‖∑ r : Fin p, A r‖ ^ 2 ≤ _
  unfold sieveWeight
  exact sieve_weight_bound_of_parseval_cs hωp
    (sq_nonneg _)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    coprime_bound
    cs

/-- **Lemma 7.15 (prime case) is now a theorem**: composing the proved
    `DFTParsevalPrime` with the reduction `dftParseval_implies_lemma715Prime`. -/
theorem lemma715Prime_proved : Lemma715Prime :=
  dftParseval_implies_lemma715Prime dft_parseval_prime_proved

/-!
### Theorem 7.14: The large sieve as a sieve

The main sieve bound: for a sequence supported on an interval of length N,

  |Z|² ≤ ((N + Q²) / H) · ‖a‖²

where Z = Σ_n a_n over the sifted set, and H = Σ_{q ≤ Q} h(q).

**Proof sketch** (IK):
1. By Lemma 7.15, for each squarefree q ≤ Q:
   h(q) · |Z|² ≤ Σ*_{a mod q} |S(a/q)|²
2. Sum over q ≤ Q: H · |Z|² ≤ Σ_{q ≤ Q} Σ*_{a mod q} |S(a/q)|²
3. By the Farey large sieve (Theorem 7.11): RHS ≤ (Q² + N − 1) · ‖a‖²
4. Divide by H.

We state this as a reduction from Lemma 7.15 + AdditiveLargeSieve → the bound.
The full statement is also recorded as a standalone open Prop.
-/

/-- **Theorem 7.14** (IK): The large sieve as a sieve — IK (7.35)/(7.38).
    Let M be a set of integers in an interval of length N, and for each prime
    p ≤ Q let Ω_p ⊂ Z/pZ be a set of ω(p) excluded residues with ω(p) < p.
    Then the cardinality S of the sifted set satisfies:

    S ≤ (N + Q²) / H

    where H = Σ_{q ≤ Q, squarefree} Π_{p|q} ω(p)/(p − ω(p)).

    Equivalently for the weighted version with sequence (a_n):
    |Z|² ≤ ((N + Q²) / H) · ‖a‖²

    This follows from Lemma 7.15 summed over q ≤ Q, combined with the Farey
    large sieve (Theorem 7.11, which follows from the ALS Theorem 7.7). -/
def LargeSieveAsSieve : Prop :=
  ∀ (N Q : ℕ) (P : Finset ℕ) (ω : ℕ → ℕ) (Ω : ℕ → Finset ℕ),
    1 ≤ N → 1 ≤ Q →
    (∀ p ∈ P, Nat.Prime p) →
    (∀ p ∈ P, 0 < ω p ∧ ω p < p) →
    (∀ p ∈ P, (p : ℕ) ≤ Q) →
    (∀ p ∈ P, (Ω p).card = ω p) →
    (∀ p ∈ P, ∀ r ∈ Ω p, r < p) →
    ∀ (a : Fin N → ℂ),
      IsSifted a P Ω →
      sieveDensity P ω Q *
        ‖∑ n : Fin N, a n‖ ^ 2 ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * l2NormSq a

/-- **Corollary**: The cardinality form of Theorem 7.14.
    For the characteristic function of a sifted set S ⊆ {1,...,N}:
    |S| ≤ (N + Q²) / H.

    This is the form most commonly used in applications. -/
def LargeSieveAsSieve_card : Prop :=
  ∀ (N Q : ℕ) (P : Finset ℕ) (ω : ℕ → ℕ) (Ω : ℕ → Finset ℕ),
    1 ≤ N → 1 ≤ Q →
    (∀ p ∈ P, Nat.Prime p) →
    (∀ p ∈ P, 0 < ω p ∧ ω p < p) →
    (∀ p ∈ P, (p : ℕ) ≤ Q) →
    (∀ p ∈ P, (Ω p).card = ω p) →
    (∀ p ∈ P, ∀ r ∈ Ω p, r < p) →
    ∀ (S : Finset (Fin N)),
      -- S is "sifted": elements of S avoid all excluded residues
      (∀ n ∈ S, ∀ p ∈ P, (n : ℕ) % p ∉ Ω p) →
      (S.card : ℝ) ≤ ((N : ℝ) + (Q : ℝ) ^ 2) / sieveDensity P ω Q

/-- The weighted form of Theorem 7.14 implies the cardinality form:
    simply take a_n = 1 if n ∈ S, 0 otherwise, and note ‖a‖² = |S| and Z = |S|.
    The set S must be sifted: no element falls in an excluded residue class. -/
theorem largeSieveAsSieve_implies_card (h : LargeSieveAsSieve) :
    ∀ (N Q : ℕ) (P : Finset ℕ) (ω : ℕ → ℕ) (Ω : ℕ → Finset ℕ),
    1 ≤ N → 1 ≤ Q →
    (∀ p ∈ P, Nat.Prime p) →
    (∀ p ∈ P, 0 < ω p ∧ ω p < p) →
    (∀ p ∈ P, (p : ℕ) ≤ Q) →
    (∀ p ∈ P, (Ω p).card = ω p) →
    (∀ p ∈ P, ∀ r ∈ Ω p, r < p) →
    0 < sieveDensity P ω Q →
    ∀ (S : Finset (Fin N)),
      (∀ n ∈ S, ∀ p ∈ P, (n : ℕ) % p ∉ Ω p) →
      (S.card : ℝ) ≤ ((N : ℝ) + (Q : ℝ) ^ 2) / sieveDensity P ω Q := by
  intro N Q P ω Ω hN hQ hP hω hPQ hΩcard hΩval hH S hSsifted
  -- Use a_n = indicator of S; then ‖a‖² = |S| and |Z|² = |S|²
  set a : Fin N → ℂ := fun n => if n ∈ S then 1 else 0
  -- The indicator of a sifted set is sifted
  have ha_sifted : IsSifted a P Ω := by
    intro n ⟨p, hp, hn⟩
    simp only [a]
    split_ifs with hmem
    · exact absurd hn (hSsifted n hmem p hp)
    · rfl
  have hbound := h N Q P ω Ω hN hQ hP hω hPQ hΩcard hΩval a ha_sifted
  -- Compute ‖a‖² = |S|
  have ha_norm : l2NormSq a = (S.card : ℝ) := by
    unfold l2NormSq
    simp only [a]
    conv_lhs =>
      arg 2; ext i
      rw [show ‖(if i ∈ S then (1 : ℂ) else 0)‖ ^ 2 =
            if i ∈ S then 1 else 0 by
        split <;> simp]
    rw [Finset.sum_ite_mem Finset.univ S (fun _ => (1 : ℝ))]
    simp
  -- Compute Z = ∑ a_n = |S|
  have ha_sum : ∑ n : Fin N, a n = (S.card : ℂ) := by
    simp only [a]
    trans (↑(∑ n : Fin N, if n ∈ S then (1 : ℕ) else 0) : ℂ)
    · push_cast; rfl
    · congr 1; simp
  have ha_sum_norm : ‖∑ n : Fin N, a n‖ ^ 2 = (S.card : ℝ) ^ 2 := by
    rw [ha_sum]; simp
  rw [ha_sum_norm, ha_norm] at hbound
  -- Now hbound : H * |S|² ≤ (N + Q²) * |S|
  by_cases hS : S.card = 0
  · simp [hS]; positivity
  · have hSpos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS)
    rw [le_div_iff₀ hH]
    -- Need: |S| * H ≤ N + Q²
    -- From hbound: H * |S|² ≤ (N + Q²) * |S|; divide by |S| > 0
    -- hbound : H * S² ≤ (N + Q²) * S
    -- Goal from le_div_iff₀: S * H ≤ N + Q²
    nlinarith [hbound, sq_nonneg (S.card : ℝ), sq_abs (S.card : ℝ)]

/-!
### Reduction: Lemma 7.15 + Farey LS → Theorem 7.14

The proof of Theorem 7.14 follows by:
1. Applying Lemma 7.15 for each squarefree q ≤ Q with prime factors in P
2. Summing: H · |Z|² ≤ Σ_{q ≤ Q} Σ*_{a mod q} |S(a/q)|²
3. The RHS is bounded by the Farey large sieve (Theorem 7.11)

We record this reduction as a theorem. Since the Farey large sieve itself follows
from the additive large sieve (ALS) by the spacing of Farey fractions, the full
chain is: ALS → Farey LS → (with Lemma 7.15) → Theorem 7.14.

The Farey large sieve is restated here with a proper (non-trivial) statement
for use in the reduction.
-/

/-- **Theorem 7.11** (restated): Large sieve at Farey fractions — IK (7.28).
    Σ_{q ≤ Q} Σ*_{a mod q} |Σ_n a_n e(an/q)|² ≤ (Q² + N − 1) · ‖a‖².

    This is the proper statement (the earlier FareyLargeSieve used True as a stub).
    It follows from the ALS by the fact that Farey fractions a/q with (a,q)=1
    and q ≤ Q are (1/Q²)-spaced. -/
def FareyLargeSieveProper : Prop :=
  ∀ (N Q : ℕ), 1 ≤ N → 1 ≤ Q →
    ∀ (a : Fin N → ℂ),
      ∑ q ∈ (Finset.range (Q + 1)).filter (0 < ·),
        ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
          ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 ≤
      ((Q : ℝ) ^ 2 + ↑N - 1) * l2NormSq a

/-- **Coprime fraction uniqueness**: If `b/q = b'/q'` as rationals with
    `gcd(b,q) = gcd(b',q') = 1` and `q, q' > 0`, then `q = q'` and `b = b'`. -/
private theorem coprime_frac_unique {br qr bs qs : ℕ}
    (hqr_pos : 0 < qr) (hqs_pos : 0 < qs)
    (hbr_cop : Nat.Coprime br qr) (hbs_cop : Nat.Coprime bs qs)
    (heq : (br : ℚ) / qr = (bs : ℚ) / qs) : qr = qs ∧ br = bs := by
  have hqr_ne : (qr : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqs_ne : (qs : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_eq_div_iff hqr_ne hqs_ne] at heq
  have heq_nat : br * qs = bs * qr := by exact_mod_cast heq
  have h_qr_dvd_qs : qr ∣ qs := by
    have h : qr ∣ br * qs := ⟨bs, by linarith [heq_nat]⟩
    exact hbr_cop.symm.dvd_of_dvd_mul_left h
  have h_qs_dvd_qr : qs ∣ qr := by
    have h : qs ∣ bs * qr := ⟨br, by linarith [heq_nat]⟩
    exact hbs_cop.symm.dvd_of_dvd_mul_left h
  have hqeq : qr = qs := Nat.le_antisymm (Nat.le_of_dvd hqs_pos h_qr_dvd_qs)
    (Nat.le_of_dvd hqr_pos h_qs_dvd_qr)
  refine ⟨hqeq, ?_⟩
  exact Nat.mul_right_cancel hqs_pos (hqeq ▸ heq_nat)

/-- **ALS implies Farey LS**: The additive large sieve (Theorem 7.7) implies the
    Farey large sieve (Theorem 7.11).

    The Farey fractions `b/q` with `(b,q) = 1`, `0 ≤ b < q`, `1 ≤ q ≤ Q` are
    `(1/Q²)`-spaced. Applying the ALS with `δ = 1/Q²` gives the bound
    `(Q² + N − 1) · ‖a‖²`.

    The proof enumerates the Farey pairs as `Fin R`, shows the points are spaced
    using the classical mediant property (Farey spacing), and applies the ALS. -/
theorem als_implies_farey_large_sieve_proper (hals : AdditiveLargeSieve) :
    FareyLargeSieveProper := by
  intro N Q hN hQ a
  -- Define the Farey finset as a sigma type
  let Qs := (Finset.range (Q + 1)).filter (0 < ·)
  let Bs : ℕ → Finset ℕ := fun q => (Finset.range q).filter (Nat.Coprime · q)
  let S := Qs.sigma Bs
  -- Convert the double sum to a sum over the sigma finset
  have hdouble : ∑ q ∈ Qs, ∑ b ∈ Bs q,
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 =
    ∑ x ∈ S, ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (x.2 : ℝ) / (x.1 : ℝ))‖ ^ 2 :=
    Finset.sum_sigma' Qs Bs _
  -- Show the double sum is what we want
  show ∑ q ∈ Qs, ∑ b ∈ Bs q,
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 ≤
    ((Q : ℝ) ^ 2 + ↑N - 1) * l2NormSq a
  -- Get the cardinality and enumeration
  set R := S.card
  -- Use the Finset equivalence to Fin R
  let e := S.equivFin
  -- Define the evaluation points
  let α : Fin R → ℝ := fun i =>
    let x := e.symm i
    (x.val.2 : ℝ) / (x.val.1 : ℝ)
  -- Step 1: Convert sigma sum to Fin sum
  have hfin_sum : ∑ x ∈ S,
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (x.2 : ℝ) / (x.1 : ℝ))‖ ^ 2 =
    ∑ i : Fin R,
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * α i)‖ ^ 2 := by
    rw [← Finset.sum_coe_sort S]
    apply Fintype.sum_equiv e
    intro x
    simp only [α, Equiv.symm_apply_apply]
    congr 1; congr 1; apply Finset.sum_congr rfl; intro n _
    congr 1; congr 1; rw [mul_div_assoc]
  -- Step 2: Match the ALS format (α r * ↑n = ↑n * α r)
  have hals_sum : ∑ i : Fin R,
      ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * α i)‖ ^ 2 =
    ∑ i : Fin R,
      ‖∑ n : Fin N, a n * eAN (α i * ↑(n : ℕ))‖ ^ 2 := by
    congr 1; ext i; congr 2; congr 1; ext n; congr 1; congr 1; ring
  -- Step 3: Handle Q = 1 separately (δ = 1/Q² = 1 > 1/2 violates ALS hypothesis)
  by_cases hQ1 : Q = 1
  · -- For Q = 1: only one Farey pair (q=1, b=0), bound by Cauchy-Schwarz
    subst hQ1
    simp only [Qs, Bs]
    have hQs : (Finset.range 2).filter (0 < ·) = {1} := by decide
    rw [hQs, Finset.sum_singleton]
    have hBs : (Finset.range 1).filter (Nat.Coprime · 1) = {0} := by decide
    rw [hBs, Finset.sum_singleton]
    -- eAN(n * 0 / 1) = eAN(0) = 1, so a n * eAN(...) = a n
    have hsimp_exp : ∀ n : Fin N,
        a n * eAN ((↑(n : ℕ) : ℝ) * ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) = a n := by
      intro n
      have : ((↑(n : ℕ) : ℝ) * ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) = 0 := by simp
      rw [this, eAN_eq_root_eAN, _root_.eAN_zero, mul_one]
    conv_lhs => rw [show ∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) =
        ∑ n : Fin N, a n from Finset.sum_congr rfl (fun n _ => hsimp_exp n)]
    -- Need: ‖∑ a_n‖² ≤ (↑1 ^ 2 + ↑N - 1) * l2NormSq a
    -- The coefficient (↑1)^2 + ↑N - 1 = ↑N
    have hcoeff : ((1 : ℕ) : ℝ) ^ 2 + (N : ℝ) - 1 = (N : ℝ) := by push_cast; ring
    rw [hcoeff]
    -- Triangle inequality + Chebyshev: ‖∑ a_n‖² ≤ (∑ ‖a_n‖)² ≤ N * ∑ ‖a_n‖²
    calc ‖∑ n : Fin N, a n‖ ^ 2
        ≤ (∑ n : Fin N, ‖a n‖) ^ 2 := by
          gcongr; exact norm_sum_le _ _
      _ ≤ ↑(Finset.univ : Finset (Fin N)).card * (∑ n : Fin N, ‖a n‖ ^ 2) :=
          sq_sum_le_card_mul_sum_sq
      _ = (N : ℝ) * l2NormSq a := by
          simp [l2NormSq]
  · -- For Q ≥ 2: use ALS with δ = 1/Q²
    have hQ2 : 2 ≤ Q := by omega
    have hQ_pos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr (by omega)
    have hQsq_pos : (0 : ℝ) < (Q : ℝ) ^ 2 := sq_pos_of_pos hQ_pos
    have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := div_pos one_pos hQsq_pos
    have hδ_le : 1 / (Q : ℝ) ^ 2 ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hQsq_pos (by norm_num : (0 : ℝ) < 2)]
      simp only [one_mul]
      have : (4 : ℝ) ≤ (Q : ℝ) ^ 2 := by
        have : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ2
        nlinarith
      linarith
    -- Show the Farey points are spaced
    have hspaced : IsSpaced α (1 / (Q : ℝ) ^ 2) := by
      intro r s hrs
      have hne : (e.symm r) ≠ (e.symm s) :=
        fun h => hrs (e.symm.injective h ▸ rfl)
      have hne' : (e.symm r).val ≠ (e.symm s).val :=
        fun h => hne (Subtype.val_injective h)
      -- Both pairs are in S
      have hmr := (e.symm r).prop
      have hms := (e.symm s).prop
      have hmr' : (e.symm r).val ∈ Qs.sigma Bs := hmr
      have hms' : (e.symm s).val ∈ Qs.sigma Bs := hms
      rw [Finset.mem_sigma] at hmr' hms'
      have hqr_mem := Finset.mem_filter.mp hmr'.1
      have hqs_mem := Finset.mem_filter.mp hms'.1
      have hqr_pos : 0 < (e.symm r).val.1 := hqr_mem.2
      have hqs_pos : 0 < (e.symm s).val.1 := hqs_mem.2
      have hqr_le : (e.symm r).val.1 ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hqr_mem.1)
      have hqs_le : (e.symm s).val.1 ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hqs_mem.1)
      have hbr_mem := Finset.mem_filter.mp hmr'.2
      have hbs_mem := Finset.mem_filter.mp hms'.2
      have hbr_lt : (e.symm r).val.2 < (e.symm r).val.1 := Finset.mem_range.mp hbr_mem.1
      have hbs_lt : (e.symm s).val.2 < (e.symm s).val.1 := Finset.mem_range.mp hbs_mem.1
      have hbr_cop : Nat.Coprime (e.symm r).val.2 (e.symm r).val.1 := hbr_mem.2
      have hbs_cop : Nat.Coprime (e.symm s).val.2 (e.symm s).val.1 := hbs_mem.2
      -- Abbreviate
      set qr := (e.symm r).val.1
      set br := (e.symm r).val.2
      set qs := (e.symm s).val.1
      set bs := (e.symm s).val.2
      -- Int.fract(b/q) = b/q since 0 ≤ b/q < 1
      have hqr_pos_r : (0 : ℝ) < (qr : ℝ) := Nat.cast_pos.mpr hqr_pos
      have hqs_pos_r : (0 : ℝ) < (qs : ℝ) := Nat.cast_pos.mpr hqs_pos
      have hfr : Int.fract ((br : ℝ) / (qr : ℝ)) = (br : ℝ) / (qr : ℝ) := by
        rw [Int.fract_eq_self]
        exact ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hqr_pos_r),
          by rw [div_lt_one hqr_pos_r]; exact_mod_cast hbr_lt⟩
      have hfs : Int.fract ((bs : ℝ) / (qs : ℝ)) = (bs : ℝ) / (qs : ℝ) := by
        rw [Int.fract_eq_self]
        exact ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hqs_pos_r),
          by rw [div_lt_one hqs_pos_r]; exact_mod_cast hbs_lt⟩
      show 1 / (Q : ℝ) ^ 2 ≤ |Int.fract (α r) - Int.fract (α s)|
      simp only [α]
      rw [hfr, hfs]
      -- The fractions br/qr ≠ bs/qs: coprimality forces uniqueness
      have hfrac_ne : ((br : ℤ) : ℚ) / (qr : ℚ) ≠ ((bs : ℤ) : ℚ) / (qs : ℚ) := by
        intro heq
        -- Convert the ℤ/ℚ fractions to ℕ/ℚ fractions
        have heq' : (br : ℚ) / qr = (bs : ℚ) / qs := by push_cast at heq ⊢; exact heq
        have ⟨hqeq, hbeq⟩ := coprime_frac_unique hqr_pos hqs_pos hbr_cop hbs_cop heq'
        exact hne' (Sigma.ext_iff.mpr ⟨hqeq, heq_of_eq hbeq⟩)
      -- Apply Farey spacing
      exact farey_spacing_proved Q (by omega) qr qs hqr_pos hqr_le hqs_pos hqs_le
        (br : ℤ) (bs : ℤ) hfrac_ne
    -- Apply ALS
    have hals_bound := hals R N α a (1 / (Q : ℝ) ^ 2) hδ hδ_le hN hspaced
    -- Simplify 1/(1/Q²) = Q²
    have hsimp : 1 / (1 / (Q : ℝ) ^ 2) + ↑N - 1 = (Q : ℝ) ^ 2 + ↑N - 1 := by
      rw [one_div_one_div]
    rw [hsimp] at hals_bound
    -- Chain: double sum = Fin sum ≤ (Q² + N - 1) * ‖a‖²
    rw [hdouble, hfin_sum, hals_sum]
    exact hals_bound

/-- **Reduction**: Lemma 7.15 + Farey large sieve → Theorem 7.14 (large sieve as sieve).

    Proof: For each squarefree q ≤ Q with prime factors in P, Lemma 7.15 gives
    h(q) · |Z|² ≤ Σ*_{a mod q} |S(a/q)|². Summing over such q:
    H · |Z|² ≤ Σ_{q ≤ Q} Σ*_{a mod q} |S(a/q)|² ≤ (Q² + N − 1) · ‖a‖²
    where the last step uses the Farey large sieve. Since N−1 ≤ N, we get
    H · |Z|² ≤ (N + Q²) · ‖a‖². -/
theorem lemma715_farey_implies_largeSieveAsSieve
    (h715 : Lemma715) (hfarey : FareyLargeSieveProper) :
    LargeSieveAsSieve := by
  intro N Q P ω Ω hN hQ hP hω hPQ hΩcard hΩval a ha_sifted
  have hfarey_bound := hfarey N Q hN hQ a
  -- Abbreviate the qualifying filter
  let qualQ := (Finset.range (Q + 1)).filter (fun q =>
    0 < q ∧ Squarefree q ∧ ∀ p ∈ q.primeFactors, p ∈ P)
  -- Step 1-2: For each qualifying q, apply Lemma 7.15 and sum
  have hsum : ∀ q ∈ qualQ,
      sieveWeightProd ω q * ‖∑ n : Fin N, a n‖ ^ 2 ≤
      ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
        ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 := by
    intro q hq
    have hqmem := (Finset.mem_filter.mp hq).2
    obtain ⟨hqpos, hqsf, hqP⟩ := hqmem
    have hωlt : ∀ p ∈ q.primeFactors, ω p < p := by
      intro p hp; exact (hω p (hqP p hp)).2
    have hΩcard_q : ∀ p ∈ q.primeFactors, (Ω p).card = ω p :=
      fun p hp => hΩcard p (hqP p hp)
    have hΩval_q : ∀ p ∈ q.primeFactors, ∀ r ∈ Ω p, r < p :=
      fun p hp => hΩval p (hqP p hp)
    -- The sifted condition for q's prime factors follows from sifted for P
    have ha_sifted_q : IsSifted a q.primeFactors Ω := by
      intro n ⟨p, hp, hn⟩
      exact ha_sifted n ⟨p, hqP p hp, hn⟩
    exact h715 N a q ω Ω hN hqpos hqsf hωlt hΩcard_q hΩval_q ha_sifted_q
  -- Step 3: H * |Z|² ≤ Σ_{qualQ} coprime_sum(q)
  have hH_le_qual : sieveDensity P ω Q * ‖∑ n : Fin N, a n‖ ^ 2 ≤
      ∑ q ∈ qualQ,
        ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
          ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 := by
    show sieveDensity P ω Q * _ ≤ _
    unfold sieveDensity
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hsum
  -- Step 4: qualQ sum ≤ full Farey sum (add nonneg terms for non-qualifying q)
  have hqual_le_farey :
      ∑ q ∈ qualQ,
        ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
          ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 ≤
      ∑ q ∈ (Finset.range (Q + 1)).filter (0 < ·),
        ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
          ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro q hq
      have hqmem := (Finset.mem_filter.mp hq)
      rw [Finset.mem_filter]
      exact ⟨hqmem.1, hqmem.2.1⟩
    · intro q _ _
      apply Finset.sum_nonneg; intros; positivity
  -- Step 5: Farey sum ≤ (Q² + N - 1) * ‖a‖² ≤ (N + Q²) * ‖a‖²
  have hNQ : ((Q : ℝ) ^ 2 + (N : ℝ) - 1) ≤ ((N : ℝ) + (Q : ℝ) ^ 2) := by
    have : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    linarith
  calc sieveDensity P ω Q * ‖∑ n : Fin N, a n‖ ^ 2
      ≤ ∑ q ∈ qualQ, ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
          ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 := hH_le_qual
    _ ≤ ∑ q ∈ (Finset.range (Q + 1)).filter (0 < ·),
          ∑ b ∈ (Finset.range q).filter (Nat.Coprime · q),
            ‖∑ n : Fin N, a n * eAN ((↑(n : ℕ) : ℝ) * (b : ℝ) / (q : ℝ))‖ ^ 2 := hqual_le_farey
    _ ≤ ((Q : ℝ) ^ 2 + ↑N - 1) * l2NormSq a := hfarey_bound
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2) * l2NormSq a := by
        apply mul_le_mul_of_nonneg_right hNQ
        unfold l2NormSq; apply Finset.sum_nonneg; intros; positivity

end LargeSieveAsSieve

end IK
