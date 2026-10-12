# Final linear review

Date: 12 October 2026. Read-only review of the complete `paper/main.tex`, `README.md`, `docs/THEOREMS.md`, and `docs/FUTURE_RESULTS.md`.

Inspected manuscript SHA256: `23f9163fc05b86aa74e811bb5cff592b5ccb2671f1f501b11fc06c62133d1647`.

Other inspected snapshots:

| File | SHA256 |
|---|---|
| `README.md` | `8a812c7ea8158a7bee88fa256a98d647895b29cb891d671ce388d5b5d0242a63` |
| `docs/THEOREMS.md` | `08e8e545108b50620d73f981bfa5c652b1bea313cb2b602ef0a5eab57c74f1c7` |
| `docs/FUTURE_RESULTS.md` | `0b8a8df859b7f03b4f037fe3dd0e59aa48f93faf2f767c6cc1200102ba3e85db` |

**Disposition:** no mathematical blocker or changed proof dependency found. Three small precision edits are recommended below. This review checks the final text against the preserved proof and supplied source/audit context; it is not a new external literature search, a fresh review of every companion proof, or a rebuild of the scripts/PDF/Lean package.

## Verified checks

- **FL-01 — Proof preservation; no defect.** After normalizing whitespace and the equivalent `\[...\]` / `equation*` displays, comparison from the differential-functional construction through the appendix finds no changes to the proof formulas or proof steps. Differences consist of the section title “primes dividing the base,” the explanatory nonvanishing lead-in, the main-proof heading, status wording, and the new companion/disclosure section. The original proof fingerprint matches the prior analytic review. In particular the polynomial-moment rank correction, coincident-zero treatment, conservative `385/(64π²)` assembly, and separate `321/(64π²)` appendix are retained.
- **FL-02 — Main scope and transitions; no defect.** The target normalization and all positive integer bases, including composite bases, are explicit. The introduction's nonpositive differential functional leads correctly to the separate interpolation argument. The abstract's refined constant is proved in the appendix; the body and README expressly explain why the main assembly retains the conservative constant. The paper does not transfer irrationality through `q→1` or claim arbitrary rational parameters, higher odd individual values, an irrationality measure, or transcendence.
- **FL-03 — Companion contracts; no defect.** All four files distinguish the present positive-base weight-three theorem from companion proofs. Their signed-base and mixed-weight statements match the supplied extension review; the rational inequality has the correct strict sign and `a/b≤1/2` restriction; `b>a⁶` and `2/65` are correctly identified as corollaries. The q-beta series and domain match the supplied q-beta review. General-weight statements retain `s≥2`; denominator upper estimates are not mislabeled as lower bounds, sharp asymptotics, or universal barriers. The unfinished matching lower bound is expressly excluded.
- **FL-04 — Attribution and status; no blocking overclaim.** The historical text assigns growing-degree determinants and cubic decay to predecessors, describes Fauzan as the motivating preprint, and treats Persiflage as historical/expository context. The supplied literature context supports the normalization, collective odd-weight result, even-weight distinction, and generalized q-logarithm antecedent. Companion references are identified as internal research records. No priority, publication, external endorsement, or complete Lean verification claim is made. Exact external bibliography metadata and theorem locators were not independently researched in this bounded pass.

## Precision findings

| ID | Severity | Exact evidence | Smallest change |
|---|---|---|---|
| FL-05 | Low, wording | Abstract: nonzero values “decay as `exp(-c_p K³+O_p(K² log K))`.” The proof establishes an upper bound, not a matching asymptotic. | Replace “decay as” with “are bounded by.” |
| FL-06 | Low, formal-status accuracy | `main.tex`, computations/formalization subsection: “its main theorem depends on nine remaining proof placeholders.” Nine is the count in the main library. The current assembly uses the proved degree upper bound rather than `leading_coeff`; the separate `purity` placeholder is also bypassed by the presently unproved `gram_det_eq`. The README already distinguishes library count from theorem axiom dependency. | Say “the main library contains nine remaining proof placeholders, and its main theorem depends on `sorryAx`,” or equivalent prose. Do not assert all nine are on the current dependency path. |
| FL-07 | Low, notation | `THEOREMS.md`, QZ3-DENOM: “Explicit `C_K` clears every coefficient in `Z[z,z^−1]`” conflates the specialized integer `C_K` with the symbolic cyclotomic product. | State that `∏_{d≤K} Φ_d(z)^{c_{K,d}}` clears `Δ_{K,z}` over `Z[z,z^−1]`, then separately give the growth of its specialization `C_K` at `z=p`. |

**FL-08 — Citation-locator reconciliation, nonblocking.** The manuscript gives Zudilin 2016 “Section 3, equation (8),” while the supplied general-weight `literature.md` describes the determinantal argument as Section 4. Both support the same antecedent. Use the parent editor's checked primary-source locator, if available; this review has not adjudicated the locator through external research. This is not evidence of an incorrect attribution or proof defect.

No canonical file was edited. These findings apply to the fingerprints above; later editorial fixes should be recorded separately rather than silently changing the reviewed snapshot.

## Closure addendum — 12 October 2026

Checked the final wording fixes after the manuscript date changed to **12 October 2026**. The revised snapshots are:

| File | SHA256 |
|---|---|
| `paper/main.tex` | `98fae72aed4f8ecee084d27c3bcece654084006ff3075491ac7590493e0f79e5` |
| `README.md` | `8a812c7ea8158a7bee88fa256a98d647895b29cb891d671ce388d5b5d0242a63` |
| `docs/THEOREMS.md` | `8fe5b43b7847e6c7e4053a8e768705ed9bddefeeee2e1566675c189c29c250fd` |
| `docs/FUTURE_RESULTS.md` | `0b8a8df859b7f03b4f037fe3dd0e59aa48f93faf2f767c6cc1200102ba3e85db` |

- **FL-05 resolved:** the abstract now says the nonzero values “are bounded in absolute value by” the displayed exponential.
- **FL-06 resolved:** the manuscript identifies nine placeholders as the main-library count and separately states the main theorem's `sorryAx` dependency. It now explicitly says a fresh kernel audit was not completed. This agrees with `provenance/original-lean-audit.txt`, which records `lake: command not found`, and the release verification note; no completed kernel audit is inferred from source inspection.
- **FL-07 resolved:** QZ3-DENOM now separates the symbolic cyclotomic product clearing `Δ_(K,z)` over `Z[z,z^−1][X]` from the growth of its specialization.
- **FL-08 resolved:** the manuscript now cites Section 4, equation (8). The parent editor supplied the primary-source check of [arXiv:1601.02688v2](https://arxiv.org/pdf/1601.02688v2): Section 4 starts on page 6 and equation (8) is on page 7. I checked the revised citation against that supplied verification; I did not repeat the external lookup.

All prior precision findings are closed. No blocking change remains from this linear review. The unchanged README and future-inventory fingerprints also confirm no intervening scope change in those files. No canonical file was edited by this reviewer.
