# Euclid vs Mersenne: the frozen walk (2026-10-27; memo only, no computation)

Prompted by the t5k.org largest-primes list: in what sense is a Euclid prime `p# + 1` the
opposite of a Mersenne prime `2^p − 1`, and does the opposition teach anything about MC?
Companion to `euclid_systems_theory_2026-09-23.md` §4 (Frozen/Unfrozen) and §14 (`CI(3 mod 4)`).

## 1. Which neighbour is smooth

| | number `N` | smooth neighbour | certificate |
|---|---|---|---|
| Mersenne | `2^p − 1` | `N + 1 = 2^p` (one prime, maximal power) | Lucas–Lehmer (`N+1` test) |
| Euclid / primorial | `p# + 1` | `N − 1 = p#` (every small prime, exponent 1) | Pocklington (`N−1` test) |
| Fermat | `2^{2^k} + 1` | `N − 1 = 2^{2^k}` | Pépin (`N−1` test) |

Both certificates are cheap; the record-size gap (Mersenne ≫ primorial) comes from the fast
special-form reduction mod `2^p − 1`, i.e. it is computational, not arithmetic.
(Pocklington for `E_n` is already used in `compositeness_2026-09-02.md`.)

## 2. Where the constraint lives — factors vs the number

* **Mersenne:** constraint on the *factors*. `q | 2^p − 1` ⟹ `ord_q 2 = p` ⟹ `q ≡ 1 (mod 2p)`.
* **Euclid:** constraint on the *number*. `p# + 1 ≡ 1 (mod ℓ)` for all `ℓ ≤ p`; the factors are
  only required to avoid `ℓ ≤ p`, with no residue-class constraint.

The prime-count heuristics for both families pick up the same Mertens factor `e^γ`, from
opposite sides (class restriction of factors vs sieving of the number). EM is the Euclid
side: no algebraic handle on the factors — the barrier the whole programme keeps meeting.

## 3. Mersenne/Fermat as the *frozen* Euclid walk (the lesson)

Walk formulation: `q | E_{n+1}` ⟺ `P_n ≡ −1 (mod q)`, with the multiplier (the chosen prime)
changing at every step. Freeze the multiplier at `a = 2`, `P_n = 2^n`:

* **Mersenne sign (hit `+1`):** `2^n ≡ 1 (mod q)` for some `n` for *every* odd `q`
  (Lagrange/Fermat). Trivial.
* **Euclid sign (hit `−1`):** `2^n ≡ −1 (mod q)` for some `n` ⟺ `ord_q 2` is even.
  **Hasse (1966): density 17/24.** So a positive proportion (7/24) of primes divides no
  `2^n + 1`.

Reading: with a constant multiplier the `+1` problem already fails on a positive-density set,
and the obstruction is a *parity* (2-adic) condition on the order of the multiplier. This is
the cleanest exactly-computable model of why EM's `+1` is hard and its `−1` twin is not, and
it lines up with three things on file:

* Frozen/Unfrozen, `MC ⟹ NoFrozen` (`euclid_systems_theory` §4);
* the 𝔽₅[X] counterexample (`not_ffMullinConjecture_five`), frozen by a constant field;
* the `{±1}` 2-adic component behind `CI(3 mod 4)` (§14, #177).

In each case `−1` is reachable only if the multipliers keep breaking the parity — the
subgroup they generate must contain `−1` mod `q`, infinitely often. Mersenne/Fermat is the
degenerate end where the obstruction is computable; MC needs the walk to stay unfrozen.

Note: §14 of the Euclid-systems memo cites Hasse/Lagarias only to dismiss them for the
least-factor class question ("wrong quantity"). The use here is different: Hasse's density is
the *exact obstruction in the frozen model*, not a tool for the orbit.

## 4. Candidate small result (not yet stated in Lean)

*Eventually-constant multiplier.* If the walk is `P_n = c · a^{n−n₀}` for `n ≥ n₀` (multiplier
eventually constant `a`), then the primes `q` it hits at `−1` infinitely often are exactly
those with `−c^{-1} ∈ ⟨a⟩ ⊂ (ℤ/q)^×`. For `c = 1, a = 2` this is Hasse's 17/24 set; in general
the density is a Chebotarev density in Kummer extensions `ℚ(ζ_m, a^{1/m}, c^{1/m})`, generically
positive and `< 1` (Hasse, Wiertelak, Moree's survey on Artin-type problems — check exact
hypotheses before citing). The Lean-sized piece is the elementary half: the
"`−1 ∈ ⟨a⟩` ⟺ `ord a` even" characterisation and that the missed set is non-empty (exhibit an
odd-order prime, e.g. `q = 7`, `ord_7 2 = 3`), making "MC ⟹ multipliers do not freeze" a
concrete, if weak, statement. The EM orbit itself never has a constant multiplier (multipliers
are distinct primes), so the content is the *model*, not a reduction.

*Status:* memo only. Not a dead end, not a route; an explanatory model for the sign asymmetry.
