# Attribution verification: Cox–van der Poorten / Booker / Pollack–Treviño (second Euclid–Mullin sequence)

Run: R-Inverse, Task B0-followup. Literature-only verification, no Lean, no computation.
Sources fetched directly (full PDF text extracted) unless marked "could not verify."

## Q1. Citation for "5 never occurs in the second Euclid–Mullin sequence" — VERIFIED, essentially correct as proposed

> C. D. Cox and A. J. van der Poorten, *On a sequence of prime numbers*, Journal of the Australian
> Mathematical Society **8** (1968), 571–574.

This is **correct as stated**, confirmed independently by three sources:

1. The publisher record (Cambridge University Press, hosting JAMS):
   - Authors: C. D. Cox and A. J. Van Der Poorten
   - Title: "On a sequence of prime numbers"
   - Journal: Journal of the Australian Mathematical Society
   - Volume 8, **Issue 3**
   - Year: **1968** (online reissue dated 2009, original publication 1968)
   - Pages: 571–574
   - DOI: `10.1017/S1446788700006236`
   - [Cambridge Core record](https://www.cambridge.org/core/journals/journal-of-the-australian-mathematical-society/article/on-a-sequence-of-prime-numbers/6F219D48B279297B5B2B348B5F808DFB)

2. Pollack–Treviño, *The primes that Euclid forgot* (Amer. Math. Monthly 121 (2014), 433–437), reference [2]:
   > "C. D. Cox and A. J. van der Poorten, On a sequence of prime numbers, J. Austral. Math. Soc. 8 (1968) 571–574."

3. Clark–Watson, *On Generalizations of the Second Euclid-Mullin Sequence* (preprint), reference [3]:
   > "C.D. Cox and A.J. van der Poorten. On a sequence of prime numbers. Journal of the Australian Mathematical Society, 8:571–574, 1968."

One minor wrinkle: Clark–Watson's **body text** (not their bibliography) says "In 1967, Cox and van der Poorten [3] showed..." — a one-year discrepancy with their own reference list and with everyone else. This looks like a slip (possibly submission year vs. publication year) on Clark–Watson's part, not a real ambiguity in the record. The DOI-backed publisher record and both other independent citations agree on **1968**. Use 1968.

**Verdict: use the citation exactly as you proposed.** No corrections needed.

## Q2. Which primes did Cox–van der Poorten (1968) actually prove omitted?

**Verified** (quoted directly from Pollack–Treviño §1, who cite CvdP precisely for this claim):

> "The second Euclid–Mullin sequence was investigated by Cox and van der Poorten [2]. They showed that all
> of **5, 11, 13, 17, 19, 23, 29, 31, 37, 41, and 47** are missing and conjectured that in fact infinitely
> many primes fail to appear in (3)."

Equivalently (also directly quoted, Booker's paper via ar5iv render, and independently confirmed by
Clark–Watson): "apart from the first four terms 2, 3, 7 and 43, [the second sequence] omits all the primes
less than 53." Since the primes below 53 are {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47}, removing the four
that *are* terms (2,3,7,43) leaves exactly the eleven primes above — internally consistent across both
phrasings and both independent sources.

So the CvdP-1968 set is exactly: **{5, 11, 13, 17, 19, 23, 29, 31, 37, 41, 47}** — 11 primes, all < 53.

Against the list you supplied — "5, 11, 13, 17, 19, 23, 29, 30, 31, 37, 41, 47, 57, 59":
- **30 and 57 are not prime.** These are not in the CvdP result and I could find no source in which they
  appear as claimed omissions (unsurprising, since they aren't prime — likely corruption/typo in whatever
  secondary source you saw, e.g. a garbled OCR or a conflation with sequence *terms*, not omitted primes).
- **59 is prime but ≥ 53**, so it falls outside CvdP's stated range and is not covered by their 1968 result.
  One secondary source (aggregated search snippet, not independently verified against a primary text)
  states 59 **appears** as an actual term of the second Euclid–Mullin sequence (OEIS A000946) — i.e. 59 is
  not omitted at all. I could not independently confirm this against OEIS directly (A000946 fetch returned
  HTTP 403), so I flag this as **could not fully verify**, but it is consistent with the fact that 59 is
  not among CvdP's list and Booker/Pollack–Treviño give no explicit list of infinitely-many omitted primes
  (their arguments are existential/quantitative, not naming specific primes beyond CvdP's 11).

**Bottom line for Q2:** every prime in your list except 30, 57, 59 is confirmed as a Cox–van der Poorten
(1968) result. 30 and 57 should be dropped (not prime). 59 should be dropped from "known omitted primes"
— it is very likely a *term of the sequence*, not an omission, though I could not get a fully authoritative
source (OEIS itself) to confirm this directly. No later paper (Booker 2012, Pollack–Treviño 2014,
Clark–Watson) names any *specific* additional omitted prime beyond CvdP's original eleven — the later work
is purely an existence/infinitude result.

## Q3. Does the classical proof for 5 use the same argument as the Lean reconstruction?

**Partially verified, with an important nuance — could not access CvdP's primary text directly (paywalled JAMS 1968 issue), so the exact wording is inferred, not quoted.**

What I *can* verify directly, from Clark–Watson (who read the primary CvdP paper and are explicit about its method):

> "In their paper, Cox and van der Poorten showed that if certain primes appeared, the second Euclid-Mullin
> sequence would satisfy an inconsistent system of congruences. In his proof, Booker used this same
> essential idea to prove Cox and van der Poorten's conjecture."

So the **general shape** of CvdP's method — "assume the target prime divides some Q_n+1; derive a
congruence the value 1+q_1...q_{n-1} must satisfy; show that congruence is inconsistent with a
constraint the value provably satisfies" — is exactly the shape of the reconstructed Lean proof, and is
confirmed by a source that read the original paper.

I can also verify, from the fully-elementary reformulation in Pollack–Treviño / Clark–Watson, that the
**general machine** built on this idea for the family EML(1,c;2) (which includes the second Euclid–Mullin
sequence, c=1) literally uses, as one of its two defining congruence conditions on the auxiliary integer d:

> "d ≡ 1 (mod 4), d ≡ −1 (mod Q₁···Qᵣ)" — Clark–Watson Prop. 3.4(a), directly generalizing Pollack–Treviño's
> Prop. 5 for the r = 0 case (no other omitted primes assumed yet), where the same congruence pair appears.

And in the base proof (Pollack–Treviño Prop. 5, general case), the final contradiction step invokes exactly
the fact that **1 + q₁···qₙ₋₁ ≡ 3 (mod 4)** always (since q₁=2 and all other qᵢ are odd) — the identical
fact used in the Lean reconstruction (there phrased as Q_n ≡ 2 mod 4 ⟹ Q_n+1 ≡ 3 mod 4).

**The nuance:** the *general* Pollack–Treviño/Booker machine additionally needs a **quadratic-residue
condition** (d/p) = (−1/p) on top of the mod-4 condition, requiring either Burgess bounds (Booker) or the
elementary QR/QNR-run bounds (Pollack–Treviño), because in general the target prime p could be ≡ 3 (mod 4)
(e.g. 11, 19, 23, 31, 47 among CvdP's list), in which case p^c is *not* automatically excluded by parity mod
4 alone — you need the quadratic-residue machinery to rule out p^c ≡ 3 (mod 4) too.

**For 5 specifically**, 5 ≡ 1 (mod 4), so 5^c ≡ 1 (mod 4) for every c ≥ 0 — no quadratic-residue argument
is needed at all; the mod-4 clash alone (3 mod 4 vs. 1 mod 4) is a complete, self-contained proof. This is
*exactly* the reconstruction's argument. Since 5 is a "degenerate" case of the general machine (the
quadratic-character condition becomes vacuous/automatic), it is highly plausible — and consistent with
everything the secondary literature says about CvdP's method being "an inconsistent congruence system" —
that this is literally CvdP's original 1968 argument for 5. But I did not obtain the primary 1968 text
itself (behind the JAMS/Cambridge paywall) to quote it verbatim, so **I am reporting this as inferred from
a reliable secondary account (Clark–Watson) plus the internal logic of the general machine, not as a
verified quotation of CvdP's actual 1968 proof of the p=5 case.**

Also worth noting for your dichotomy write-up: this means the *specific* proof that kills 5 is a strictly
simpler special case that doesn't need the "construct an auxiliary d via CRT + quadratic-residue-run
existence" apparatus at all — it needs only the mod-4 parity fact plus "3 appears once, at step 1." This
matters for Q4/obstruction-family classification below.

## Q4. Booker's theorem: citation, and structure of the proof

### Citation — VERIFIED

> Andrew R. Booker, *On Mullin's second sequence of primes*, Integers **12A** (2012), article A4 (10 pages).
> DOI: `10.1515/integers-2012-0034`. arXiv: `1107.3318`.

Confirmed via arXiv abstract page (journal ref: Integers 12A, 2012, article A4) and via
`10.1515/integers-2012-0034` (De Gruyter). This is the special "Integers Conference 2011" volume, hence the
"12A" (not a plain "12") volume label — worth getting right in the bibliography.

Abstract, quoted directly: "We consider the second of Mullin's sequences of prime numbers related to
Euclid's proof that there are infinitely many primes. We show in particular that it omits infinitely many
primes, confirming a conjecture of Cox and van der Poorten."

### Structure of the proof — the key question

**Verified directly from primary sources** (Pollack–Treviño's full text, which restates Booker's structure
before giving their own elementary variant; and Clark–Watson, who also restate it):

Booker's proof is **not** a fixed propagating invariant (a single residue class / set of states, chosen in
advance, closed under the recursion, that the orbit provably stays inside forever and that is incompatible
with divisibility by the target prime). It is a **reductio-by-contradiction over a finite window, driven by
quadratic reciprocity plus an existence/counting input from analytic number theory**:

1. Fix a growing bound X. Assume for contradiction that *every* prime p ≤ X except a known finite excluded
   set Q₁,...,Qᵣ (the primes already proved omitted) appears somewhere in the sequence.
2. Let p be the *last* prime ≤ X to appear, as the n-th term. Since every smaller prime not in {Qᵢ} is
   already a term q₁,...,qₙ₋₁, the only possible prime factors of 1+q₁···qₙ₋₁ are Q₁,...,Qᵣ and p itself.
   So 1+q₁···qₙ₋₁ = Q₁^e₁···Qᵣ^eʳ p^e.
3. **Construct** (this is the non-invariant, non-elementary step) an auxiliary integer d ≤ X, via CRT,
   satisfying a fixed congruence mod 4·Q₁···Qᵣ *and* a prescribed quadratic-residue value (d/p) = (±1/p).
   Existence of such a small d requires either:
   - Burgess's bounds on short character sums (Booker's original proof), or
   - elementary bounds on the length of runs of consecutive quadratic residues/non-residues mod p, which
     Pollack–Treviño prove from scratch to give a fully elementary variant with weaker quantitative bounds.
4. Compute the Jacobi symbol (d / (1+q₁···qₙ₋₁)) **two different ways** — once by quadratic reciprocity
   (using that 1+q₁···qₙ₋₁ ≡ 3 mod 4) giving −1, once by multiplicativity over the known factorization
   Q₁^e₁···Qᵣ^eʳ p^e (using the *chosen* residue values of d mod each Qᵢ and mod p) giving +1. Contradiction.
5. This produces one new omitted prime below X for every X; since X can be taken arbitrarily large
   (X grows like 12²·(Q₁···Qᵣ)²), the omitted set is shown to be infinite by an escalating induction, not
   by exhibiting a single fixed invariant valid for all n at once.

So: **the mechanism is a quadratic-reciprocity/Jacobi-symbol sign-contradiction argument, wrapped in a
finite-window reductio, with a CRT + character-sum(or QR-run) existence step supplying the auxiliary
integer** — not a counting/pigeonhole argument in the classical sense, and not a "clever fixed starting
value" trick either. It genuinely needs an analytic-number-theory existence input (however elementary
Pollack–Treviño manage to make it).

### Is Booker's argument "inside" a propagating-invariant obstruction family?

This is the honest, structurally important answer for your dichotomy framing, verified against the primary
texts above:

- **The general Booker/Pollack–Treviño machine is *not* a pure propagating invariant.** It requires, at
  each escalation step, *constructing* a new auxiliary modulus/witness d via CRT and an existence lemma
  about quadratic residues — this is a genuinely different (and strictly more powerful) mechanism than
  fixing one closed, target-avoiding state set in advance and showing the orbit never leaves it. If your
  "obstruction family" is defined as (fixed residue-class / finite-state invariant, closed under the
  transition, avoiding the target), Booker's general argument for *arbitrary* omitted primes and for
  *infinitude* does not literally fit that mold as stated — it needs the extra CRT + QR-existence
  ingredient at each step.
- **However, the degenerate special case that kills specific primes p ≡ 1 (mod 4)** — including 5, and by
  the same mod-4 logic also 13, 17, 29, 37, 41 among CvdP's eleven (all ≡ 1 mod 4) — collapses to *exactly*
  a propagating invariant: the residue class "Q_n ≡ 2 (mod 4) for all n ≥ 1" is a genuine, fixed,
  closed-under-the-recursion invariant (multiplying by any odd prime preserves 2 mod 4), and it alone
  (combined with the one-time fact that 3 is used up at step 1) suffices to exclude any p ≡ 1 (mod 4) as
  soon as p ≠ the specific value the invariant permits. This sub-case genuinely is inside a
  propagating-invariant family, and it is (per Q3) very likely CvdP's own original mechanism for those
  primes.
- **For primes p ≡ 3 (mod 4)** among CvdP's list (11, 19, 23, 31, 47), the mod-4 invariant alone is *not*
  enough (p^c mod 4 depends on the parity of c), so either CvdP used a different, still ad hoc congruence
  invariant for each of these five (most likely — I could not verify the details, primary text
  inaccessible), or a small quadratic-residue argument specific to each. Either way, these are still
  finite, prime-specific, hand-verifiable arguments, unlike Booker's general infinitude machine.

**Recommendation for your framework:** the honest statement is that Booker's argument is *outside* a
narrowly-defined "fixed propagating invariant" family (it needs a constructive CRT+QR-existence step), but
the *individual prime* eliminations that CvdP first proved — 5 in particular, and plausibly the other
primes ≡ 1 mod 4 in their list — genuinely are simple propagating invariants and can honestly be classed
in that family. If you want Booker's full theorem to also count as "in the family," the family definition
would need to be broadened to something like "invariant constructed via CRT from a growing exclusion set,
verified via quadratic reciprocity" — which is a meaningfully different (and more permissive) definition
than a single fixed closed state set.

### Pollack–Treviño citation — VERIFIED

> Paul Pollack and Enrique Treviño, *The primes that Euclid forgot*, American Mathematical Monthly **121**,
> no. 5 (2014), 433–437.

Confirmed by direct fetch of the full PDF (`campus.lakeforest.edu/trevino/mullin-Monthly.pdf`), by the
paper's own author affiliation footer (Pollack: University of Georgia; Treviño: Lake Forest College), and
by Clark–Watson's bibliography (identical citation). Note the correct spelling is **Treviño** (with tilde
on the n, and accent on the i in some renderings — the paper itself uses "Treviño").

What Pollack–Treviño actually did (verified, quoted above in Q4): gave a **fully elementary replacement**
for the analytic-number-theory ingredient in Booker's proof (Burgess's character-sum bounds), substituting
self-contained elementary bounds on runs of consecutive quadratic residues/non-residues mod p (worse
quantitative constants, but no deep input beyond quadratic reciprocity and elementary counting). They did
**not** change the overall structure/mechanism described above — same CRT+reductio+Jacobi-symbol machine,
just with an elementary existence lemma standing in for Burgess.

## Q5. Is there an inverse-type theorem in the literature ("prime omitted ⟹ obstruction of classified type exists")?

**No literature found asserting this, in either direction, for either Euclid–Mullin sequence.** Searched
specifically for inverse/converse statements accompanying Booker (2012), Pollack–Treviño (2014), and
Clark–Watson's generalization (2018) — none of these papers, nor any citing paper found in this search,
states or conjectures a converse ("every omission arises from an obstruction of a specific classified
type"). All existing results are one-directional: exhibit specific obstructions (congruence/character
inconsistencies) that are *sufficient* to prove omission for a given target or to prove infinitude of
omissions; none characterizes *all* possible ways a prime could fail to appear, and none states a
structure theorem in the reverse direction. This is consistent with your expectation that this is the open
question you are posing as a genuine conjecture, not a known negative result — I found no paper explicitly
stating it as a **known** open problem either (i.e., I could not verify a citable "this converse is open"
remark in the literature; I can only report that no paper claims or proves it).

## Sources

- [Cambridge Core: Cox & van der Poorten, "On a sequence of prime numbers" (1968)](https://www.cambridge.org/core/journals/journal-of-the-australian-mathematical-society/article/on-a-sequence-of-prime-numbers/6F219D48B279297B5B2B348B5F808DFB) — DOI 10.1017/S1446788700006236
- [Pollack & Treviño, "The primes that Euclid forgot" (PDF, full text fetched)](https://campus.lakeforest.edu/trevino/mullin-Monthly.pdf)
- [Booker, "On Mullin's second sequence of primes", arXiv:1107.3318](https://arxiv.org/abs/1107.3318)
- [Booker, Integers 12A (2012), article A4 — De Gruyter record, DOI 10.1515/integers-2012-0034](https://www.degruyterbrill.com/document/doi/10.1515/integers-2012-0034/html)
- [Clark & Watson, "On Generalizations of the Second Euclid-Mullin Sequence" (PDF, full text fetched)](https://loridwatson.com/wp-content/uploads/2018/10/emls.pdf)
- [Wikipedia, "Euclid–Mullin sequence"](https://en.wikipedia.org/wiki/Euclid%E2%80%93Mullin_sequence) — low detail, not independently useful beyond confirming existence of the two theorems
- OEIS A000946 (second Euclid–Mullin sequence) — fetch blocked (HTTP 403); could not independently confirm the "59 appears as a term" claim against the primary OEIS entry.
