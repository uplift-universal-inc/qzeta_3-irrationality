# Editorial brief and release closure

The requested product is a repository and research paper focused on irrationality of the Lambert value zeta_(1/p)(3) for integer p at least 2. The audience is a number theorist familiar with determinants, local valuations and elementary analytic estimates. The release supplies a self-contained written argument with historical attribution and two related kernel-checked Lean proofs of the same target. The canonical manuscript is `paper/main.tex`; the current compiled result is 21 pages, including the elementary second presentation in Appendix B.

The supplied October 11 checkpoint is retained unchanged in `provenance/original-proof.tex`. The mathematical spine is purity, real decay, coefficientwise base-prime content, corrected cyclotomic clearing, infinite nonvanishing, and the rationality contradiction. The source's conservative constant is sufficient; its sharper appendix remains an optional strengthening. Other written results are inventoried in a short section and separate README table, with their proofs reserved for another article.

Appendix B replaces the general residue-integrality argument for coefficient content with a finite Gaussian-binomial calculation and gives a direct second irrationality assembly. It shares the determinant, real estimate, local cyclotomic clearing, nonvanishing theorem, and supporting algebra with the first proof. The second presentation is reconstructed from the retrieved messages in `provenance/elementary-second-proof-source.md`; their linked scratch Markdown attachments were unavailable. The first formal proof uses the elementary cost `107/192` and margin `31/576`; the second uses the weaker sufficient cost `9/16` and margin `7/144` from those messages.

## Statement contracts and review

`docs/THEOREMS.md` is the frozen current-statement ledger. All estimates are for fixed integer p at least 2 and all positive K; constants in O_p terms may depend on p. The integer polynomial, real bound and nonvanishing proposition concern the same determinant family. There is no claim uniform in a continuously varying q, no effective first nonzero index, and no irrationality measure. The proof does not depend on a companion theorem.

The original mathematical and editorial reviews below retain their source fingerprints and original scope. They are historical records of the first manuscript preparation, not new review reports for Appendix B.

| Packet | Direct inputs | Original mathematical review | Written-proof status |
|---|---|---|---|
| QZ3-PURE and REAL | Differential functional; triple-root monic basis; Hadamard inequality | `reviews/analysis.md` | Written, internally reviewed, typeset audited |
| QZ3-CONTENT | Local series translation; divided differences; exact leading coefficient | `reviews/arithmetic.md` | Written, internally reviewed, typeset audited |
| QZ3-DENOM and INTEGER | Cluster bases; fraction-field rank correction; cyclotomic products; CONTENT | `reviews/arithmetic.md` | Written, internally reviewed, typeset audited |
| QZ3-NONZERO | Pure moments; rational interpolation; infinitely many genuine poles | `reviews/analysis.md` | Written, internally reviewed, typeset audited |
| QZ3-MAIN | REAL, CONTENT, DENOM, INTEGER, NONZERO; positive rational margin certificate | Both reviews cover their assigned inputs; final assembly checked in analytic review | Written, internally reviewed, typeset audited |
| QZ3-SHARP | Exact upper-node vanishing; same fraction-field rank bound | `reviews/arithmetic.md` | Written, internally reviewed, typeset audited |
| Companion inventory | Immutable source records, not assumptions in QZ3-MAIN | `reviews/extensions.md`, `reviews/qbeta.md` | Listed for future article; review scope explicit |

During the original editorial pass, the primary editor alone edited the canonical TeX and independent reviewers were read-only for that file. No core proof formula was changed by that rewrite. Its final linear review and closed precision edits are recorded in `reviews/final-linear.md`; its PDF inspection and source fingerprint are recorded in `reviews/pdf-layout.md`. Those records are preserved and do not certify the later 21-page layout or the new Appendix B by implication. The current manuscript has been rebuilt and visually inspected in the second-proof release work.

## Current formal verification

`make formal-proof` passes for both routes. The production source contains no proof placeholders or custom axioms, and all audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. `QZeta3.theorem11` exports the first proof; `QZeta3.irrational_qzeta3_elementary` exports the second in explicit convergent-series notation. The separate comparator challenge retains its one intentional statement-template placeholder outside the solution dependency graph.

The current evidence is `certificates/formal-proof-run.log`, `certificates/kernel-axioms.log`, and `certificates/kernel-verification.json`. `certificates/second-proof-dependencies.log` additionally records that the second conclusion uses the Gaussian arithmetic branch and excludes the original final theorem and coefficient-content route. This checks a distinct arithmetic derivation and final assembly within the shared construction, not an unrelated determinant-free method.

`lean/CORRESPONDENCE.md` records the exact relationship to the paper, including the factorial analytic prefactor and sufficient rational growth estimates. The paper's sharper π-based asymptotic is not asserted as an unconditional formal theorem. Finite computations, formal verification, human statement review, and external peer review retain their separate scopes in `docs/VERIFICATION.md`.

## Publication envelope

The user authorized repository preparation and committing proofs/certificates under uplift-universal-inc, subsequently approved public publication, and selected **uplift-universal-inc** as the public pen name for the manuscript, citation metadata, README, and Git author name. The repository is public at `uplift-universal-inc/qzeta3-irrationality`; the formal-completion work uses the review branch `lean/complete-reciprocal-qzeta3`. `docs/PUBLISHING.md` records the initial publication and subsequent formal updates separately. The original blocked-remote preparation state is historical. External submission and a new open-source license are not part of this release.

The reciprocal-integer irrationality target is fully formalized through the two related proof routes. The manuscript remains a research draft without claimed external peer review, established novelty priority, or a completed human statement-to-manuscript audit. Companion claims remain outside this formalization.
