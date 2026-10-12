# Results reserved for companion articles

**Scope boundary:** this repository's paper proves only the reciprocal-positive-integer weight-three statement. This inventory lists other written results and the exact evidence that supports their status. “Written proof” below means a complete research argument with internal audits; it does not mean external peer review, established priority, or a complete Lean proof.

The reciprocal-positive-integer weight-three theorem itself now has a completed Lean proof, recorded in [VERIFICATION.md](VERIFICATION.md). That formal result does not establish the additional claims below.

## Main companion statements

| ID | Statement | Parameter range | Status and source |
|---|---|---|---|
| FUT-LI | `1,Z₂(p),Z₃(p)` are Q-linearly independent, `Z_s(p)=Σ n^(s−1)/(p^n−1)` | Every integer `|p|≥2` | Complete written extension; fresh bounded source review found no substantive gap. [Mixed proof][mixed] |
| FUT-SIGNED | `Z₃(p)` is irrational for negative integer bases | Integers `p≤−2` | Corollary of FUT-LI; not an additional independent theorem. Negative nodes cost `2^(K(K−1))` in the real bound. [Mixed proof][mixed] |
| FUT-RATIONAL | `ζ_(a/b)(3)` is irrational | Coprime positive integers `a<b`, `a/b≤1/2`, `log a/log b < 1−2889/(352π²)` | Complete written extension in rational-parameter archive; [shared source][rational]. Its additional proof is a degree/homogenization argument. |
| FUT-RATIONAL-SIMPLE | Same assertion if `b>a⁶`; in particular `ζ_(2/65)(3)` | Coprime positive integers | Corollaries of FUT-RATIONAL, not separate discoveries. |
| FUT-BETA-LI | `1,B₁(p),B₂(p)` are Q-linearly independent, `B_s(p)=Σ n^(s−1)p^n/(p^(2n)+1)` | Integers `p≥2` | Complete written candidate and fresh bounded review. [Mixed q-beta proof][beta] |
| FUT-BETA2 | `B₂(p)` is irrational | Integers `p≥2` | Subsumed by FUT-BETA-LI; [original pure proof][beta2] also gives a separate argument. |

The rational parameter archive is `q_zeta_rational_parameter_checkpoint_2026-10-11.zip`; its canonical file is `work/rational_q3/proof.tex`. Its hash and the other source fingerprints are recorded in `provenance/source-manifest.json`. It is not included as a competing manuscript in the current paper directory.

## Supporting theorems for the companion treatment

| Result | Precise scope | Limitation |
|---|---|---|
| Inverse-parameter degree bound and homogenization | The normalized coefficient polynomial belongs to `Z[t,X]` and has `t`-degree at most the degree of its cyclotomic clearer | This is the extra arithmetic needed for rational `q`; the reciprocal case does not alone prove it |
| General-weight purity and real decay | Fixed integers `s≥2`, `p≥2`; `log|Δ_K|≤−K³ log p/(3s)+O(K²)` | Smallness before normalization is insufficient |
| General-weight content and nonvanishing | The same square-family base-prime factor `p^e_K`; infinitely many nonzero determinants at the actual real target | The formal `s=1` substitution has a different constant term and is not automatic |
| Sharper all-cluster denominator upper estimate | `C_s*=(s+7/4+Σ_(j≥1)(s+2j)^−2)/π²` | The sufficient comparison works at weights 2 and 3; its failure at higher weights is not a lower bound on the true primitive denominator |
| Varying-numerator local nonvanishing | Square family and the explicit divisibility hypotheses on numerator coefficients in the source proof | Not arbitrary unbounded numerators |
| Moving-denominator normality | Fixed differential functional with nonrational Cauchy transform and nested exterior interpolation nodes | Moving functionals/numerators require their own compatibility argument |
| Restricted construction barriers | Fixed-ratio, small-parameter and prescribed-CRT-basis bounds under the hypotheses in the reviewed source notes | Not a universal impossibility theorem for higher weights or alternate normalizations |

The longer 17-entry contract review is retained in `reviews/extensions.md` and `reviews/extensions_inventory.json`; it distinguishes ordinary all-index derivations, certificate-level barriers, finite tests, and unfinished arguments.

## Work that is still open

- Individual irrationality of higher odd `ζ_(1/p)(s)`, `s≥5`, is not proved by these packages.
- Arbitrary rational `q`, such as `2/3`, is outside FUT-RATIONAL.
- A proposed matching lower bound for actual higher-weight denominators remains unfinished; an upper estimate must not be relabeled as a sharp asymptotic.
- Classical `ζ(7)`, `β(4)`, and Euler–Gompertz irrationality were not solved by the cited alternative attempts. Their structural lemmas and negative screens belong in separate research records, not in this paper's theorem list.
- No effective irrationality measure or transcendence statement is obtained here.
- Formalizing the additional companion claims and obtaining external expert review remain future work. The current reciprocal-integer theorem's formalization is complete.

[mixed]: https://github.com/fikreab-s/the-math-research-ledger/blob/b1436ad117691f96abc5203c14b119555dabf7d1/problems/odd-zeta/computations/qzeta_extensions_20261011/audit/LINEAR_INDEPENDENCE_EXTENSION.md
[rational]: https://chatgpt.com/share/6acbb114-bf5c-83ea-8266-be9e1277b62c
[beta]: https://github.com/fikreab-s/the-math-research-ledger/blob/b19558937c91876d6330c8464871e146a820c909/problems/odd-zeta/computations/alternatives_20261011/qbeta-mixture/MIXTURE_EXTENSION.md
[beta2]: https://github.com/fikreab-s/the-math-research-ledger/blob/b19558937c91876d6330c8464871e146a820c909/problems/odd-zeta/computations/alternatives_20261011/qbeta2/PROOF_CANDIDATE.md
