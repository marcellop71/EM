# The Mertens function and the Mullin conjecture (2026-09-17)

Status: analysis note.  Only §4 has Lean content (`EM/ForMathlib/Mertens.lean`).  "Mertens" elsewhere in this
repository always means Mertens' *theorems* (`∑ 1/p`, `∏ (1 - 1/p)`, Mertens in APs);
this note is about the Mertens *function* `M(x) = ∑_{n ≤ x} μ(n)`.

## 0. Why M(x) was never mentioned

`M(x) = o(x)` (PNT) or `O(x^{1/2+ε})` (RH) is a statement about the zeros of ζ, averaged
over all integers.  MC concerns one doubly-exponentially sparse orbit; no cancellation of μ
over `[1, x]` constrains `minFac(prod n + 1)`.  This is the Marginal/Joint barrier again.
The only orbit-level μ-facts: `μ(prod n) = (-1)^n` (trivial) and `μ(prod n + 1)`, which
needs squarefreeness of `prod n + 1` (open, as for Sylvester's sequence).

Where μ does belong:

* **Alladi duality.**  `∑_{d ∣ n, d > 1} μ(d) f(P⁻(d)) = −f(P⁺(n))`, hence
  `∑_{n ≥ 2, P⁻(n) ≡ a (q)} μ(n)/n = −1/φ(q)`.  This is the *true* theorem of which the
  false PE (Dead End #160) was a misreading.  It is signed, so it cannot feed a
  coverage/positivity argument such as a.a. GenMC(q).
* **Effective Mertens-in-APs** (the next target after Session 317): its error term is
  controlled by the same zero-free-region input as `M(x; q, a) = o(x)`.

Parked corrections: the Alladi formula in `EM/Equidist/SieveTransfer.lean:34` is misstated
(it lacks the `1/n` weight; at `q = 1` it would read `−M(x) ~ x`); a dead-end entry
"Möbius-weighted population law is true but signed"; a paper remark disambiguating
Mertens' theorems from the Mertens function.

## 1. Function fields: M is trivial, and what that explains

`A = 𝔽_q[X]`, `ζ_A(u) = ∑ qⁿuⁿ = 1/(1 − qu)`, so `∑_f μ(f) u^{deg f} = 1 − qu`:

    ∑_{deg f = n} μ(f) = 1, −q, 0, 0, 0, …        M(n) = 1 − q   for all n ≥ 1.

*Spectral reason.*  `ζ_A` has no zeros (genus 0), so there are no oscillating terms
`x^ρ / (ρ ζ'(ρ))`.

*Elementary reason.*  The same identity `∑_{d ∣ f} μ(d) = [f = 1]`, summed over a box,
gives over ℤ

    ∑_{d ≤ x} μ(d) ⌊x/d⌋ = 1,

and over `A`, with `m_k = ∑_{deg f = k} μ(f)`,

    ∑_{k ≤ n} m_k q^{n−k} = 0     (n ≥ 1),

because the number of multiples of `d` in the degree-`n` box is *exactly* `q^{n − deg d}`:
the box `{deg < n}` is an `𝔽_q`-subspace, so reduction mod `d` is exactly equidistributed.
The recursion collapses to `m_n = 0` for `n ≥ 2`.  Over ℤ, `⌊x/d⌋ = x/d − {x/d}` and the
entire content of `M(x)` is the fractional parts: an interval is not a subgroup (the
archimedean place).  Roughly, PNT ⟺ `∑ μ(d) {x/d} = o(x)`.

So **"Mertens trivial" ⟺ "boxes are groups" ⟺ "every sieve count is exact"**.  The tails of
the seed-average programme (`TailAssembly`, `LemmaD`, `LemmaDBox`) are estimates of
`{X/d}`-type roundoff; over `A` that population law would hold with zero error at full
level of distribution.

In APs the function is not trivial but is RH-quality by Weil:
`[uⁿ] 1/L(u, χ) ≪ q^{n/2}`.  That is the precise sense of "the ANT is free".

*What it does not explain.*  FF-MC is false over `𝔽_5[X]` (`not_ffMullinConjecture_five`)
in the presence of a perfect population Mertens function.  Hence:

> **The 𝔽_5 screen.**  No bound on `M(x)` — not even RH — can imply MC by an argument that
> would transfer to `𝔽_5[X]`.  Any proof of MC must use something that distinguishes ℤ
> from `𝔽_5[X]`.

## 2. μ along the orbit: Stickelberger parity and the stable tower

**Stickelberger / Pellet.**  For `q` odd and `f ∈ 𝔽_q[X]` squarefree,

    μ(f) = (−1)^{deg f} · χ₂(disc f).

Möbius is a quadratic character, computable *without factoring*.  (Over ℤ, computing
`μ(n)` is believed to be as hard as factoring.)

**Discriminant recursion for the tower.**  `Φ(P) = P² + P`, `g_n = Φⁿ + 1 = g_{n−1} ∘ Φ`,
`D = deg g_{n−1} = 2^{n−1}`, critical point `−1/2`, critical value `Φ(−1/2) = −1/4`.  From
`disc f = (−1)^{N(N−1)/2} Res(f, f')` with `N = 2D`:

    Res(g∘Φ, (g'∘Φ)·Φ') = Res(g, g')² · 2^{N} · g(−1/4),
    disc(g_n) = (−1)^D · 4^D · disc(g_{n−1})² · (Φ^{n−1}(−1/4) + 1).

Check `n = 1`: `disc(X² + X + 1) = −3 = −4 · (3/4)`.  ✓.   For `n ≥ 2` the sign is `+`, so

    μ(E_n) = μ(g_n) = χ₂( Φ^{n−1}(−1/4) + 1 )      (n ≥ 2),     μ(E_1) = χ₂(−3).

This is exactly the non-square condition of `EM/FunctionField/StableTower.lean`: the
critical-orbit criterion *is* the Möbius parity of the Euclid numbers; Capelli upgrades
"odd number of factors" to "one factor".  Over `𝔽_5` the shifted critical orbit is
`3, 2, 3, 2, …`, all non-squares, so `μ(E_n) = −1` for every `n`:

    orbit Mertens sum       ∑_{n < N} μ(E_n) = −N        (no cancellation at all)
    population Mertens sum  ∑_{deg f = n} μ(f) = 0        (total cancellation)

— the Marginal/Joint barrier as an exact identity.  An *exceptional prime* is one where μ
is constantly `−1` along the tower.  Since the critical orbit is eventually periodic in
`𝔽_p`, `n ↦ μ(E_n)` is eventually periodic.  Over ℤ there is no discriminant formula, the
critical orbit escapes to infinity, and even `μ(s_n) ≠ 0` for Sylvester's sequence is open.

## 3. Candidate Lean targets

1. `ffMertens`: `∑_{deg f = n} μ(f) = 0` for `n ≥ 2` via the exact-box recursion (needs a
   Möbius on monic polynomials; Mathlib's `ArithmeticFunction` is ℕ-only).
2. The discriminant recursion for `g_n` (pure resultant identity, same spirit as
   `BackwardLevels.preimage_pair_discriminant`) + paper remark "tower condition = μ(E_n) = −1".
3. Stickelberger parity — probably not in Mathlib; state as a named hypothesis first.

## 4. Computing M(x) over ℤ

Lean: `EM/ForMathlib/Mertens.lean` (Mathlib-only, 0 sorry) — `mertens`, `sum_mertens_div`,
`sum_moebius_mul_div`, `mertens_eq_one_sub`, `abs_mertens_le`.

**The one identity.**  Summing `ζ * μ = 1` over `n ≤ N` in the two possible orders:

    (A)  ∑_{n ≤ N} M(⌊N/n⌋) = 1            (`sum_mertens_div`)
    (B)  ∑_{n ≤ N} μ(n) ⌊N/n⌋ = 1          (`sum_moebius_mul_div`)

(A) is the *algorithm*, (B) is the *obstruction*.

**(A) as algorithm.**  `M(N) = 1 − ∑_{2 ≤ n ≤ N} M(⌊N/n⌋)` (`mertens_eq_one_sub`).  The
quotient `⌊N/n⌋` takes at most `2√N` distinct values and the set
`Q(N) = {⌊N/n⌋}` is closed under `v ↦ ⌊v/m⌋` (since `⌊⌊N/n⌋/m⌋ = ⌊N/(nm)⌋`).  So `M` restricted
to `Q(N)` satisfies a *closed* triangular linear system of size `2√N`:

* naive memoised recursion: `O(N^{3/4})`;
* sieve μ up to `N^{2/3}`, recurse above: `O(N^{2/3})` (Deléglise–Rivat 1996, with the
  refinement `M(x) = M(u) − ∑_{m ≤ u} μ(m) ∑_{u/m < n ≤ x/m} M(x/(mn))`);
* Helfgott–Thompson 2021: `O(N^{3/5} (log N)^{3/5+ε})`, still elementary;
* analytic (Lagarias–Odlyzko contour method): `O(N^{1/2+ε})`.

None of these factors anything: M(N) is computed *without knowing a single μ(n) for
n > N^{2/3}*.  The sum is far cheaper than its terms.  (Contrast §2: over `𝔽_q[X]` the terms
are cheap too — Stickelberger — and the sum is free.)

**(B) as obstruction.**  Write `⌊N/n⌋ = N/n − {N/n}`:

    N · ∑_{n ≤ N} μ(n)/n  −  ∑_{n ≤ N} μ(n) {N/n}  =  1.

Everything non-trivial about μ on `[1, N]` lives in the sawtooth sum `∑ μ(n){N/n}`.  Over
`𝔽_q[X]` the sawtooth is identically zero (boxes are subgroups) and M collapses.  The sawtooth
`{N/n}` is exactly the error term in every interval sieve count `#{m ≤ N : d ∣ m} = N/d − {N/d}`
— i.e. the same object the seed-average tails (`LemmaD`, `LemmaDBox`, `TailAssembly`) bound
term-by-term with `|{·}| ≤ 1`.  The Mertens function is the statement that these roundoffs,
*weighted by μ*, cancel; a sieve that bounds them in absolute value cannot see that.  This is
the parity phenomenon in its plainest form.

**The explicit formula.**  Assuming simple zeros,
`M(x) = ∑_ρ x^ρ / (ρ ζ'(ρ)) − 2 + ∑_{k ≥ 1} (−1)^{k−1} (2π/x)^{2k} / ((2k)! k ζ(2k+1))`.
Odlyzko–te Riele (1985) disproved `|M(x)| < √x` from ~2000 zeros and lattice reduction, never
evaluating M near a counterexample (none is known below `10^{16}`; the first is expected
around `exp(1.59 · 10^{40})`).  Lesson for this project: a statement about μ was settled by
structure (zeros + simultaneous Diophantine approximation), not by tabulation.

**What "computing M" could give the Mullin programme — honest assessment.**

1. *Nothing on the orbit.*  `Q(N)` is the set of scales M needs; the EM orbit is not in the
   picture.  Marginal/Joint barrier, and the 𝔽_5 screen of §1 applies verbatim.
2. *A model of "sum cheaper than terms".*  The a.a. GenMC proof is of this type (population
   law without knowing any orbit).  The closure `Q(N) → Q(N)` under `v ↦ ⌊v/m⌋` is the
   integer shadow of the exact degree filtration in `𝔽_q[X]`.
3. *A sharper reading of our own error terms.*  If any tail in the seed-average programme is
   a μ-weighted sawtooth sum, bounding it by absolute values throws away exactly M-type
   cancellation; PNT-strength input (`∑ μ(n)/n = o(1)`) is what effective Mertens-in-APs
   would deliver.  Worth auditing `LemmaD`/`TailAssembly` for where `|μ| ≤ 1` is used.

**Possible Lean follow-ups** (all elementary): closure of the quotient set under `⌊·/m⌋`
(`Nat.div_div_eq_div_mul`), `#Q(N) ≤ 2√N`, the Deléglise–Rivat identity, and the Dirichlet
hyperbola method flagged as a TODO in Mathlib's `ArithmeticFunction/Misc.lean`.
