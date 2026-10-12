# Bounded review of rational-parameter and higher-weight extensions

Review date: 2026-10-11. This is a source and theorem-contract review of the supplied written arguments, not new research, a complete Lean audit, or independent external validation. No canonical manuscript was edited. The finite computations quoted below are archived reports; they were not rerun in this review.

## Verdict

The rational-parameter package contains a complete **written proof candidate** for weight three in its explicitly stated parameter range. The additional inverse-parameter degree argument and homogenization are present; they are not merely conjectured or inferred from finite tests. I found no substantive gap in that argument during this bounded review.

The general-weight and odd-alternatives packages contain several reusable theorems and genuine, narrowly scoped barriers. They do **not** contain a proof of irrationality of any individually prescribed odd weight at least five. The quantitative higher-weight deficit is a failure of the available denominator **upper bounds**, not a proved asymptotic lower bound for the true denominators and not an impossibility theorem for all constructions.

All project results below have status **written / internally reviewed**, unless specifically marked finite-only or unfinished. None should be described as a complete Lean proof on the strength of these sources. The separate Lean package was outside this review's assigned scope.

## Source keys

All paths below are relative to `archive://`.

| Key | Directory |
|---|---|
| R | `q_zeta_rational_parameter_checkpoint_2026-10-11/work/rational_q3/` |
| G | `q_zeta_general_weight_checkpoint_2026-10-11/work/general_weight/` |
| O | `q_zeta_odd_alternatives_checkpoint_2026-10-11/work/odd_alternatives/` |

The normalization throughout is the Lambert series

\[
Z_s(q)=\sum_{n\ge1}\frac{n^{s-1}q^n}{1-q^n}.
\]

It must not be confused with a differently normalized q-zeta function or with the ordinary Riemann zeta value.

## Rational parameter: precise result and dependencies

**R1 — Written irrationality candidate.** For coprime positive integers `a<b`, with `a/b <= 1/2` and

\[
\frac{\log a}{\log b}<\tau_0,
\qquad \tau_0=1-\frac{2889}{352\pi^2}
=0.168417899026381\ldots,
\]

the proposed theorem asserts that `Z_3(a/b)` is irrational. The strict inequality is essential to the stated cubic-decay argument. It implies the simpler sufficient condition `b>a^6`; in particular it covers `a=2,b=65`. It includes every reciprocal integer `a=1,b>=2`. Source: `R/proof.tex`, `thm:main`, `cor:six`, and the final proof; status explicitly recorded in `R/AUDIT.txt`.

The rational theorem should not silently be replaced by a stronger range derived by combining it with a different package's improved denominator constant. Such a combination is not the rational theorem actually assembled in this source.

**R2 — New inverse-parameter degree theorem.** For every positive integer `K`, with

\[
e_K=K(K^2-1)/2,\quad C_K(t)=\prod_{d\le K}\Phi_d(t)^{E_{K,d}},
\quad d_K=\deg C_K,
\]

the polynomial `A_K(t,X)=C_K(t)t^{-e_K} Delta_K(t,X)` lies in `Z[t,X]`, has `deg_t A_K <= d_K`, and has `deg_X A_K=K`. The exact characteristic identity in the Lagrange basis proves the degree bound by a limit at `t -> +infinity` with `K` fixed. Source: `R/proof.tex`, `lem:zero`, `prop:degree`, equation `eq:characteristic`. This is a substantive all-order written lemma, not just the symbolic `K<=5` check.

**R3 — Arithmetic certificate.** The displayed cyclotomic exponents clear coefficients, including the singular polynomial-moment correction, and give

\[
d_K=\frac{321}{64\pi^2}K^3+O(K^2\log K),\qquad
\log C_K(t)=d_K\log t+O_t(K^2\log K)
\]

for fixed real `t>1`. Source: `R/proof.tex`, `prop:cyclo`. In particular the high-cyclotomic-order proof does not use the false assertion `K-2<d`; it retains the rank correction `max(0,K-d-1)`.

**R4 — Real estimate and infinite nonvanishing.** For each fixed real `t>=2`, `log|Delta_K(t,Z_3(1/t))| <= -(log t)K^3/9+O_t(K^2)`; infinitely many determinants are nonzero for **every** fixed real `t>1`. Source: `R/proof.tex`, `prop:real`, `prop:nonzero`. The different ranges must be kept distinct. Nonvanishing is proved from a nonrational Cauchy transform and exterior-node rational interpolation; it does not require positivity or a numerical sign pattern.

**R5 — Rational specialization is accounted for.** The polynomial

\[
P_K(X)=a^{d_K}A_K(b/a,X)\in\mathbb Z[X]
\]

has degree `K`. Its cubic logarithmic upper coefficient at the target is exactly

\[
\frac{321}{64\pi^2}\log b-\frac{11}{18}\log(b/a).
\]

Its negativity is equivalent to the stated threshold. The proof pays the numerator-denominator cost `a^{d_K}` explicitly, then multiplies by `v^K` under a hypothetical rational value `u/v`. This closes the written argument; no missing rational-specialization denominator was identified.

The exact checks cover `a/b in {1/2,2/3,2/65,3/730}`, `K in {1,2,3,4,6,8,10,12}`, and a separate symbolic calculation for `K=1,...,5`. The `2/3` tests verify algebraic identities **outside** the irrationality range and cannot be listed as an irrationality result. Source: `R/verification.json`, `R/symbolic_verification.json`.

## General weight: supported reusable statements

Here `s>=2` is an integer fixed before `K` tends to infinity, and `q=1/p` with integer `p>=2`, unless a row specifies otherwise.

| ID | Supported statement and exact scope | Written source |
|---|---|---|
| G1 | The pure-target Euler functional has simple-pole moments `Z_s(q)-S_{s,a}` and polynomial moments `j^(s-1)/(p^j-1)`. The repeated-root basis proves real decay `-(log p)K^3/(3s)+O_{s,p}(K^2)`. The Cauchy-transform interpolation argument gives infinitely many nonzero determinants at the real target. | `G/extension_report.tex`, general construction and analytic proposition; `G/analytic.md` |
| G2 | For the square family `H=K`, all reduced coefficient denominators are coprime to `p`, and the gcd of reduced numerators is exactly `p^{e_K}`. The leading coefficient is `(-1)^{K(K-1)/2}p^{e_K}`. The congruence after division by `p^{e_K}` is that same sign times `X^K mod ell`, for every prime `ell|p`. The proof covers even and odd `s>=2`, with local center `X-(-1)^s Z_s^loc`. | `G/arithmetic/PROOF.md`, sections 2–4 |
| G3 | For each prime `ell|p` and each fixed `X in Q_ell`, infinitely many `K` have nonzero formal determinant evaluation. The composite-base critical valuation tie is handled by an invertible finite-field recurrence. | `G/arithmetic/PROOF.md`, section 5 |
| G4 | The sharpened cyclotomic **upper certificate** has cubic constant `C_s=[s+7/4+sum_{j>=1}(s+2j)^(-2)]/pi^2`. It is sufficient only if `C_s<1/2+1/(3s)`. It meets that inequality for `s=2,3` and misses it for every `s>=4`. At `s=5`, `C_5=1/8+5039/(900 pi^2)=0.692286049304...`, exceeding `17/30` by `0.125619382637...`. | `G/independent_denominators.md`; summarized in `G/extension_report.tex` |
| G5 | For arbitrary positive `H,K`, an integral numerator with constant coefficient one preserves the local content floor `p^{H(H+1)(K-1)/2}`. For `H=K` and numerators with degree-`j` coefficient divisible by `p^j`, exact p-primary content and an infinite local nonzero subsequence persist uniformly even when the numerator varies with `K`. This includes `V_N=prod_{m=1}^N(1-p^m x)^s` for arbitrary `N=N(K)`. | `G/arithmetic/NUMERATOR_CONTENT_NONVANISHING.md` |
| G6 | The early-node numerator `V_N` gives the proved real-exponent gain `N K(K-1)` on top of the baseline exponent. Its expanded polynomial-moment range must be included in any denominator analysis; the unweighted certificate cannot be reused unchanged. | `G/analytic.md`; `G/extension_report.tex`, alternative constructions |
| G7 | A denominator theorem is written for the unweighted family `1<=H<=K`. For `H=floor(alpha K)`, `0<alpha<=1`, the displayed certificate exceeds `alpha^2/2+1/(3s)` for every `s>=5`; positivity is proved by explicit polynomials, not numerical optimization. This only bars this certificate/content-floor pairing. | `G/parameters/REPORT.md`; `G/AUDIT.md` |

Weight one is excluded from the functional/content extension: its reciprocity has an extra constant term, and the supplied `p=2,K=3` example explicitly defeats the naive `p^{e_K}` content claim. Even-weight transcendence and existing weight-one results are literature background, not new project theorems. I did not perform a new external literature verification or a novelty search.

## Odd alternatives: supported theorems and barriers

| ID | Supported statement and exact scope | Written source |
|---|---|---|
| O1 | For fixed integer `s>=2` and integer `p>=2`, the positive tail determinant `H_{s,K}(X)=det[X-S_{s,i+j}]` is affine in `X`, is positive at `X=Z_s(1/p)` for every `K`, and has exact rate `log H = -K(K+1)(2K+1)log p/6 +(s-1)log(K!)+O_{s,p}(K)`. Its denominator certificate has rate `7s/pi^2`; the separately stated p-content floor in its proof is for odd `s`. These bounds do not prove irrationality. | `O/research_report.tex`, section 1; `O/loewner/REPORT.md`, section 3 |
| O2 | At complete block sizes `K=sM`, every finite `H>=0` has exact formal small-`q` leading term `delta=c_s^M q^{E_{K,s}}(1+O(q))`, where `c_s=(-1)^{s(s-1)/2}((s-1)!)^s` and `E=2 sum_{j<K}sum_{t<=j}ceil(t/s)`. This is a formal-order theorem; by itself it gives no fixed-`q=1/2` asymptotic. | `O/analytic/SHARPNESS_AND_ORDER.md`, sections 1–3 |
| O3 | For every integer `s>=2`, some `q_s in (0,1/4]` and positive `c_s^-,c_s^+` satisfy `(c_s^-)^K q^E <= |delta| <= (c_s^+)^K q^E` for all `K=sM`, all finite `H>=0`, and all `0<q<=q_s`. Constants are independent of `K,H`. This proves the exact cubic rate for sufficiently small fixed `q`, even for arbitrary `H=H_K`, but the proved threshold is not asserted to reach `q=1/2`. | `O/analytic/FIXED_SMALL_Q.md`; direct audit in `O/literature/FIXED_SMALL_Q_AUDIT.md` |
| O4 | For integer `s>=2`, a nontrivial fixed finite sum `P(z)+sum_a R_a(z)F_s(z^a)`, with rational functions over `C` and analytic at zero, cannot have Taylor coefficients satisfying `sum_{n<=N}|c_n|=O(N(log N)^nu)` for any fixed `nu>=0`. This obstructs the specified low-average-coefficient criterion for fixed rational filters and finite dilations; it does not rule out growing filters or general digit methods. | `O/root_pade/FILTER_DILATION_BARRIER.md`; `O/research_report.tex`, section 3 |
| O5 | If `V in Z[z,x]`, `deg_x V<=N`, and `V=0 mod (Phi_d(z),x^d-1)` for every `d<=N`, then `prod_{d<=N}Phi_d(z)` divides `z^{jN}V(z,z^{-j})` for every integer `j>=1`. At `p>=2`, a nonzero value has size at least that product divided by `p^{jN}`. For conditions imposed only at a fixed `p`, replace the product by the **lcm**. This bounds numerator values, not signed determinants or their derivatives. | `O/analytic/CRT_REAL_DICHOTOMY.md`; `O/crt_barrier_summary.tex` |
| O6 | Disjoint-pole Loewner determinants built from a fixed union of `2K` distinct poles differ from the corresponding common-denominator `K`-square determinant by a nonzero rational scalar. Their primitive integer polynomials agree up to sign. Partitioning the fixed pole set or changing either full basis cannot improve the primitive approximation. | `O/loewner/REPORT.md`, section 1 |
| O7 | The explicit dual purity projector eliminates lower periods exactly but gives a generating function with genuine order-`s` poles at every geometric node. It therefore does not retain a simple-atom mechanism for free. This is a result for the displayed projector, not every possible block or mixed construction. | `O/arithmetic/DUAL_PURITY_PROJECTOR.md`, sections 1–3 |
| O8 | For integer `p>=2`, odd `s>=3`, and `H>=2K-1`, the tall ordinary determinant is affine in `X` and has common p-content at least `p^{A(K-1)+B}`, with `A=H(H+1)/2`, `B=sum_{i=1}^{K-1}(H-2i)ceil(i/s)`. At `H=2K`, `B=K^3/(3s)+O_s(K^2)`. This is a lower bound, not exact content or nonvanishing. The audit observes that the same proof extends to even `s>=2`, but the assembled report states the narrower odd-weight version. | `O/parameters/TALL_CONTENT.md`; `O/analytic/TALL_CONTENT_AUDIT.md` |
| O9 | A separate denominator note establishes the available certificate for `K<=H<=2K`. At `H=2K,s=5`, even after O8 the decay/content budget is `32/15`, below the high-index certificate contribution `24/pi^2`. This is a limitation of those proved bounds. For `1<H/K<2`, the source does not claim a new all-coefficient extra-content formula. | `O/parameters/TALL_BUDGET.md`; `O/literature/ASSEMBLY_REVIEW.md` |

Additional written auxiliary results suitable for a detailed research inventory, but less central to the proposed focused paper, are the explicit positive q-binomial linear forms and their uncanceled multiplier budget (`O/loewner/REPORT.md`, section 2); exact partial-numerator capacity/decay and complete-block formal-order formulas (`O/analytic/PARTIAL_NUMERATOR.md`); and the symbolic degree restriction `deg_x V>=d+r-1` for combining `(1-zx)^r` with full cyclotomic vanishing, unless `Phi_d(z)` divides all coefficients (`O/research_report.tex`, section 2).

## Later-article result recovered from the ledger

**L1 — Written two-weight linear-independence extension.** For every integer `p` with `|p|>=2`, define

\[
\mathscr Z_s(p)=\sum_{n\ge1}\frac{n^{s-1}}{p^n-1}.
\]

The three numbers `1, mathscr Z_2(p), mathscr Z_3(p)` are asserted to be linearly independent over `Q`. Equivalently, every nonzero integer combination `a mathscr Z_2(p)+b mathscr Z_3(p)` is irrational. The source notation `Z_s(p)` uses the **inverse parameter** `p`, whereas earlier rows use `Z_s(q)`; both denote the same values when `q=1/p`.

Sources: `ledger-source://LINEAR_INDEPENDENCE_EXTENSION.md` and `ledger-source://AUDIT.md`, recovered by the parent from ledger commit `b1436ad`. Status: **written extension, internally mathematically audited, dependent on the baseline all-size determinant lemmas that it rechecks; not a complete Lean or externally validated theorem**. Per the user's requested article scope, this belongs in the future-results inventory, with its proof excluded from the focused weight-three manuscript.

The mixed functional `(a theta+b theta^2)` is pure in the whole target. Its tails retain pole order at most three, its local expansion uses the correct mixed-parity center `U=X-Z`, and its leading `X` coefficient remains nonzero even when `a+b=0`. The Cauchy transform has genuine third-order poles when `b!=0` and double poles otherwise, so the nonvanishing proof survives. For negative `p`, the real estimate explicitly includes `2^{K(K-1)}` to account for opposite-sign roots; this changes only quadratic logarithmic terms. Both the conservative denominator coefficient `385/(64 pi^2)` and the stronger `321/(64 pi^2)` remain below `11/18`.

No substantive gap was found in this bounded reading. An audit-only display in `AUDIT.md`, section 5, omits the plus sign between the `a` and `b` Cauchy-transform summands. The extension source and the immediately following principal-part formula contain the correct sum, so this is a transcription defect rather than a proof gap. The finite checks of 150 mixtures in the extension source and 448 polynomials / 2,240 coefficients in its audit are corroboration only. The argument does not add `Z_1`, prove algebraic independence, or concern ordinary zeta values.

## Claims that remain finite-only or unfinished

1. Finite denominator rates at `K=40`, positive normalized values in the various `s=5,p=2` grids, CRT lattice height reductions, factorization patterns, and all `|P(Z_s)|>1` interval enclosures describe only the recorded finite cases. They neither prove asymptotic growth nor exclude untested families.
2. The proposed high-cyclotomic-order **matching lower bound** in the final section of `G/independent_denominators.md` is explicitly unfinished: its Schur-complement coefficient argument has not been completed. It must not enter any theorem's proof assumptions or be called an actual-denominator asymptotic.
3. The reciprocal-value identity `z^N V_N(z,z^{-1})=prod_{d<=N}Phi_d(z)` and its degree pattern were checked for supplied representatives `N=2,...,10`. They are not proved for all `N`. The apparent anti-palindromic pattern already fails at `N=9,10`.
4. The fixed-small-`q` lower bound is not proved at `p=2`, does not cover every residue class of `K mod s`, and does not bound arithmetic cancellation.
5. None of the sources proves an individual `Z_5(1/p)` or `Z_7(1/p)` irrational, all rational-parameter weight-three irrationality, an irrationality measure, or ordinary zeta irrationality by taking `q -> 1`.

## Specific audit observations

The rational argument distinguishes the fixed-`K` limit used to determine polynomial degree from the uniform-in-`K` real determinant estimate; this avoids a common invalid exchange of limits. Its nonvanishing argument takes cross-products rather than dividing by interpolation denominators that could vanish. Its formal zero-place integrality, cyclotomic clearing, and homogenization fit together without an uncovered prime or degree cost.

The strongest small-`q` lemma has a genuine uniform proof: adjacent-block differences localize the normalized basis, the exceptional final basis function is treated separately, off-diagonal block norms decay with block distance, and an `O_s(q)` operator error yields singular-value bounds independent of size. It is substantially stronger than a finite symbolic expansion, but retains the stated restricted parameter range.

The tall-denominator documentation includes an explicit repair of an earlier domain mismatch: it uses double Cauchy–Binet on the full `H`-dimensional CRT form to bound smaller minors, rather than assuming the `H<=K` proof applies unchanged. The final assembled statement respects that repair.

No new substantive gap was identified in the focal rational theorem, the sharpened certificate comparison, the fixed-filter barrier, the CRT dichotomy, the uniform small-`q` proof, or the tall-content proof. This finding is a bounded mathematical review, not a claim that every auxiliary script, finite record, literature assertion, or formal proof obligation has been independently verified.
