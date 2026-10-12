# Verification record

This release contains a written mathematical proof, finite computational certificates, and a completed Lean proof of the reciprocal-integer main theorem. The strict build and transitive axiom audit pass. Independent internal reviews and kernel checking do not establish external expert acceptance or publication priority.

## Replayed computations

The following were run afresh in preparing this release, using Python 3.12.14 and python-flint 0.9.0. `make check` reruns the exact tests; `make certificate` reruns the interval certificate.

| Check | Fresh result | Record |
|---|---|---|
| Normalization and all-cluster formulas | 88 exact determinant cases; 62,500 finite cluster checks | `certificates/assembly-replay.log`, `verification/work/assembly_verification.json` |
| Independent base-prime arithmetic | 100 cases, including composite and prime-power bases; all passed | `certificates/arithmetic-replay.log`, `verification/work/fresh_arithmetic/checks.json` |
| Corrected denominator clearer | 40 coefficient-denominator cases and cluster exponents through K=400; all passed | `certificates/rank-replay.log`, `verification/work/denominator_repair/verification.json` |
| Explicit coefficient examples | 18 cases at p=2,3,6, K=1,...,6; each determinant polynomial checked at K+1 exact arguments | `certificates/coefficient-examples.json` |
| Rigorous real evaluation | p=2, K=60, primitive integer polynomial of degree 60; value interval excludes zero | `certificates/interval-replay.log`, `verification/work/audit/fast_K60.json` |

For the K=60 evaluation, the corrected Arb evaluator used 266,276 precision bits and 266,468 series terms, with an explicit enclosure of the infinite tail. Its reported value is approximately `−4.34518351412299664323688 × 10^−8968`, with radius at most `4.45 × 10^−8992`. The displayed decimal enclosure is abbreviated; the computation uses full precision internally. Replaying the script reconstructs the polynomial from exact rational entries before evaluation. The JSON is a replay record, not an independently kernel-checkable proof term.

The original `verification/source/zeta7-port/qhankel.py` constructs the exact determinant correctly, but its original numerical entry point truncates the infinite series without a tail enclosure. It is retained for source provenance. Use `verification/work/audit/fast_verify.py` for rigorous real certificates.

## Written proof review

- `reviews/analysis.md`: purity and convergence, the all-size real bound, moving-denominator nonvanishing, and final assembly, conditional on the arithmetic propositions.
- `reviews/arithmetic.md`: coefficientwise base-prime content, leading coefficient, all-size cyclotomic denominator control, polynomial-moment rank correction, and the stronger appendix.
- `reviews/extensions.md` and `reviews/qbeta.md`: separate bounded audits supporting the future-results inventory.
- `reviews/final-linear.md`: the final manuscript and scope review after editorial revision.

The reviews record source fingerprints and their exclusions. No blocking defect was found in the assigned current-proof obligations. This is substantial internal scrutiny, not a claim that AI review cannot overlook a mathematical error.

## Completed Lean verification

The project pins Lean 4.34.1 and Mathlib v4.34.1. `make formal-proof` runs a strict production-source scan, builds `QZeta3` and `QZeta3Audit.Solution`, prints the transitive theorem axioms, checks them against the standard-axiom allowlist, and verifies the second proof's required and excluded declaration dependencies. The combined gate passes.

| Check | Result | Record |
|---|---|---|
| Production-source scan | Zero proof placeholders; zero custom axioms | `certificates/formal-proof-run.log` |
| Pinned Lean build | Successful build of the library and explicit-series solution | `certificates/formal-proof-run.log` |
| Transitive axiom audit | All audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` | `certificates/kernel-axioms.log` |
| Verification manifest | Source hashes and machine-readable verification metadata | `certificates/kernel-verification.json` |
| Main theorem | `QZeta3.theorem11 (p : ℕ) (hp : 2 ≤ p) : Irrational (QZeta3.xi p)` | `lean/QZeta3/Frozen/Theorem11.lean` |
| Explicit-series theorem | Irrationality of `∑' n : ℕ, ((n : ℝ)+1)^2 / ((p : ℝ)^(n+1)−1)` under `2≤p` | `lean/QZeta3Audit/Solution.lean` |
| Elementary second proof | Same explicit-series target through Gaussian coefficient content and direct criterion assembly | `lean/QZeta3/ElementarySecondProof.lean` |
| Second-proof dependency audit | Gaussian/content/sieve/criterion branch present; first final theorem and original content branch excluded | `certificates/second-proof-dependencies.log` |

`summable_term` and `hasSum_xi` establish convergence of the defining series. The conclusion therefore concerns its genuine sum, including every composite integer base at least 2.

The original nine production placeholders are closed or replaced by sufficient proved statements. In particular, the former sharp totient asymptotic is replaced by a finite sieve using 2 and 3. The resulting cost is `107/192`, with exact margin `11/18−107/192=31/576>0`. The original Appendix A cyclotomic exponents are retained. The π-based sharp asymptotic is not claimed as an unconditional Lean theorem. The analytic prefactor is also replaced by a sufficient factorial bound; [CORRESPONDENCE.md](../lean/CORRESPONDENCE.md) records the differences.

The elementary second proof adds `GaussianIdentity`, `ElementaryContent`, and `ElementarySecondProof`. Its explicit-series theorem is `QZeta3.irrational_qzeta3_elementary`. It passes the standard-axiom audit. `Meta/SecondProofAudit.lean` also passes: the dependency graph uses the Gaussian arithmetic branch and excludes the original `theorem11`, `irrational_xi`, and `content_coeff_proved` route. These are dependency checks in addition to the ordinary standard-axiom audit. Sharing the determinant, analytic estimate, local cyclotomic clearing, nonvanishing argument, and supporting algebra is intentional.

The second growth theorem `log_CK_elementary_le` uses cost `9/16` and exact margin `7/144`. It follows from the existing stronger finite-sieve bound `107/192`. Accordingly, the elementary second proof introduces an alternative coefficient-content derivation and final assembly; it does not claim a new denominator improvement or an unrelated determinant-free proof.

The second presentation is reconstructed from the displayed messages preserved in [elementary-second-proof-source.md](../provenance/elementary-second-proof-source.md). The linked scratch Markdown attachments were not retrieved, and their contents are not claimed as audited. The direct scalar and integral candidates mentioned in those excerpts remain outside this formalization.

`QZeta3Audit/Challenge.lean` has one intentional placeholder solely to declare an independent Mathlib-only comparator statement. The separately compiled `Solution.lean` proves that statement without importing the challenge, and its transitive audit contains no `sorryAx`. The checked explicit-series restatement is not a claim that the external `leanprover/comparator` service was run.

The earlier failed build and original unavailable-Lake audit remain historical provenance. They describe the initial preparation environment and are superseded for current formal status by `formal-proof-run.log` and `kernel-axioms.log`. Historical review notes likewise describe the initial nine-gap snapshot; the current manuscript's formal-status paragraphs have been updated. A completed human statement-to-manuscript review and external mathematical peer review are not claimed.

## Document validation

The canonical TeX compiles twice with `pdflatex -halt-on-error`. Every rendered page is inspected for clipped formulas, missing references, unreadable typography, and layout defects. The document review record is `reviews/pdf-layout.md`. Bibliographical and mathematical claims are traceable through `docs/ATTRIBUTION.md` and the statement ledger in `docs/THEOREMS.md`.
