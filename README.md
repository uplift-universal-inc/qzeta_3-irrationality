# Irrationality of q-zeta(3) at reciprocal integers

**Public byline:** uplift-universal-inc

**Current release scope:** the written proof and completed Lean formalization of

$$\zeta_{1/p}(3)=\sum_{n=1}^{\infty}\frac{n^2}{p^n-1}\notin\mathbb Q\qquad(p\in\mathbb Z,\ p\ge2).$$

Here `p` is any integer at least 2, **including composite integers**. This is the Lambert-series normalization of q-zeta.

This directory contains the focused paper, its explicit determinant construction, reproducible finite certificates, and a kernel-checked Lean development. The proofs of the companion irrationality and independence results are reserved for a separate article; this release lists their exact statements and sources in [FUTURE_RESULTS.md](docs/FUTURE_RESULTS.md).

The development includes an elementary second proof using Gaussian-binomial residue sums for the coefficient-content argument. It shares the determinant, real estimate, cyclotomic denominator clearing, and nonvanishing argument with the first proof. The final irrationality conclusion is assembled directly from the approximation criterion through this alternate arithmetic branch.

## Read the paper

- [Paper (PDF)](paper/main.pdf)
- [LaTeX source](paper/main.tex)
- [Current theorem inventory and proof map](docs/THEOREMS.md)
- [Historical sources and attribution](docs/ATTRIBUTION.md)
- [Verification status](docs/VERIFICATION.md)

The abstract identifies the target-specific contribution. The introduction places it alongside Apéry and Beukers, Krattenthaler–Rivoal–Zudilin, Jouhet–Mosaki, Prévost, Zudilin's earlier cubic-decay q-Hankel method, Uvarov, Krattenthaler, and the recent Fauzan construction. General Hankel methods and cubic decay are not presented as new inventions.

## Mathematical and formal status

| Item | Status of this release |
|---|---|
| Reciprocal-integer q-zeta(3) argument | Complete written research proof; fresh internal reviews found no blocking defect in the assigned proof steps |
| External expert review / publication | Not yet established |
| Finite certificates | Exact rational arithmetic and Arb intervals with an explicit infinite tail; replayed locally |
| Lean development | **Complete for the stated reciprocal-integer theorem**; zero production proof placeholders and zero custom axioms |
| Kernel verification | Build and transitive axiom audit passed; all audited declarations use only `propext`, `Classical.choice`, and `Quot.sound` |
| Priority / novelty | Target-specific contribution described; no unqualified first-proof priority claim |

Finite calculations support the formulas. The all-size Lean proof establishes the theorem for every `p≥2`; its explicit-series restatement is also audited. The independent comparator challenge retains one intentional statement-template placeholder, which is absent from the solution's dependency graph. The build and audit records are [formal-proof-run.log](certificates/formal-proof-run.log) and [kernel-axioms.log](certificates/kernel-axioms.log).

## Proof in five steps

1. A second Euler derivative gives rational polynomial moments and pure simple-pole tails of the target.
2. A triple-root basis yields real determinant decay with exponent `−K³ log(p)/9`.
3. Local expansions at every prime dividing `p` extract the full coefficient factor `p^(K(K²−1)/2)`.
4. Root-of-unity cluster bases, including the polynomial-moment rank correction, clear all remaining denominators. The refined cubic cost is `321/(64π²)`.
5. Moving-denominator rational interpolation gives infinitely many nonzero values. The margin `11/18 − 321/(64π²) > 0` contradicts rationality.

The paper retains the independently sufficient conservative cost `385/(64π²)` in its main proof and proves the stronger cost in Appendix A. This deliberate choice preserves the source proof and makes the improvement separately reviewable.

The Lean proof uses the Appendix A cyclotomic exponents with an elementary finite-sieve growth bound `107/192`. Its exact positive margin is `11/18−107/192=31/576`. It does not claim a formal proof of the sharper π-based asymptotic. The factorial determinant prefactor and other explicit proof substitutions are documented in [CORRESPONDENCE.md](lean/CORRESPONDENCE.md).

## Elementary second proof

For `K≥1` and integers `d≥0`, the alternate arithmetic identity, with `F_K(x)=∏_(a=1)^K(x−p^a)`, is

$$
\sum_{a=1}^K\frac{p^{ad}}{F_K'(p^a)}=
\begin{cases}
0,&0\le d<K-1,\\
p^{d-K+1}{d\brack K-1}_p,&d\ge K-1.
\end{cases}
$$

The Gaussian coefficients are defined by a finite integral Pascal recurrence. This supplies the monomial residue integrality used in `content_coeff_elementary`, replacing the original general residue-integrality argument. The exceptional reciprocal residue, finite truncations, and determinant normalization complete the coefficientwise base-prime factor.

`irrational_qzeta3_elementary` states the same irrationality result with the series written explicitly. Its growth lemma uses the sufficient cost `9/16`, with margin `11/18−9/16=7/144`. The first formal proof's sieve already proves the slightly stronger cost `107/192`; the new growth lemma follows by weakening that bound. The additional content is the Gaussian arithmetic branch and its direct final assembly, not an improved growth constant or a determinant-free construction.

See the paper's Appendix B, [PROOF_MAP.md](lean/PROOF_MAP.md), and the [retrieved source excerpts](provenance/elementary-second-proof-source.md). The shared conversation's linked Markdown attachments were unavailable; the implementation reconstructs the stated variant from the retrieved messages and the existing checked construction.

## Reproduce

Python 3.11+, `python-flint==0.9.0`, and a standard LaTeX installation are sufficient for the finite checks and paper.

```sh
python3 -m pip install -r requirements.txt
make check                 # exact arithmetic and normalization checks
make certificate           # p=2, K=60 rigorous interval replay
make paper                 # rebuild the PDF, including references
make formal-status         # source inventory: zero production placeholders
make formal-proof          # strict source gate, Lean build, transitive axiom audit
```

For Lean 4.34.1 and pinned Mathlib, see [lean/README.md](lean/README.md). To audit the actual theorem dependency after building:

```sh
cd lean
lake build QZeta3 QZeta3Audit.Solution
lake env lean QZeta3/Meta/AxiomsAudit.lean
```

`make formal-proof` is the strict completeness gate and passes for this development. A source scan or finite-test result alone does not establish formal completeness; the gate also checks the built theorem dependencies against the standard-axiom allowlist.

## What is coming

Separate written arguments with internal audits already exist for:

| Future article / release | Precise result |
|---|---|
| Signed bases and mixed weights | `1, Z₂(p), Z₃(p)` are Q-linearly independent for every integer `|p|≥2`, where `Z_s(p)=Σ n^(s−1)/(p^n−1)` |
| Rational parameters | Irrationality of `ζ_(a/b)(3)` in an explicit range, including coprime positive integers with `b>a⁶` |
| Character-twisted q-beta | Q-linear independence of `1, B₁(p), B₂(p)` for `p≥2`, where `B_s(p)=Σ n^(s−1)p^n/(p^(2n)+1)` |
| General determinant theory | All-weight purity, base-prime content, real-decay and nonvanishing lemmas; improved denominator estimates and carefully scoped barriers |

These rows describe internally reviewed written results, pending external review and formalization of their additional claims. Their proofs are not part of the present paper. The [future inventory](docs/FUTURE_RESULTS.md) distinguishes new claims, corollaries, structural lemmas, and open obligations.

**Outside the proved scope:** arbitrary rational `q`; individual odd q-zeta values of weight at least five; classical `ζ(7)`; transcendence; or an effective irrationality measure. Failed sufficient bounds do not prove impossibility of other constructions.

## Repository layout

| Directory | Scope |
|---|---|
| `paper/` | One canonical manuscript and its compiled PDF |
| `lean/` | Completed pinned reciprocal-integer Lean proof, with its original license and correspondence notes |
| `verification/` | Original construction engine and focused replay scripts; historical notes retain their original status |
| `certificates/` | Fresh replay records, explicit coefficient examples, and release-status JSON |
| `docs/` | Current and future theorem inventories, attribution, verification, and publication instructions |
| `reviews/` | Independent internal mathematical and editorial reviews with source fingerprints |
| `provenance/` | Original manuscript and source records; superseded claims remain marked as historical |

Subdirectory descriptions are subordinate to this release status. In particular, the original engine's numerical entry point omitted a tail enclosure: use the corrected `work/audit/` evaluators, as `make certificate` does.

## Attribution and release metadata

The manuscript and current citation metadata use the owner-approved public pen name **uplift-universal-inc**. See [ATTRIBUTION.md](docs/ATTRIBUTION.md) for scholarly predecessors, source-session contribution records, and AI disclosure. Historical source bylines and the imported Lean package's original citation and Apache-2.0 license are preserved. The manuscript/code outside that package have no newly assigned open-source license.

Repository: [uplift-universal-inc/qzeta3-irrationality](https://github.com/uplift-universal-inc/qzeta3-irrationality). The initial public snapshot contained the incomplete skeleton; this formal-completion update supplies its checked replacement. See [PUBLISHING.md](docs/PUBLISHING.md) for the publication record.
