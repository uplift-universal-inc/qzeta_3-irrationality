# Q-beta source review for the future-results inventory

Reviewed source commit: `b19558937c91876d6330c8464871e146a820c909` (the supplied provenance identifier). Review scope: the four local documents below; no new literature or publication-status investigation and no rerun of cited computation scripts.

## Source fingerprints

Paths are relative to `sources/ledger/qbeta/`.

| Source | SHA256 |
|---|---|
| `qbeta2/PROOF_CANDIDATE.md` | `ea0b193954e83afa6f715eb4296df29397d28b3dced4e73dd120343129dcd588` |
| `qbeta-mixture/MIXTURE_EXTENSION.md` | `a1801b65806c8f6b20725fba32df62e3f427877336f9c64266218eb82ca5928f` |
| `qbeta2-audit/MIXTURE_FINAL_AUDIT.md` | `50139c5e7a01343858bdbc448d6a78a2aab452dcf44f28ccd02f7ac0735ba021` |
| `PARENT_REVIEW.md` | `4079bff38f5b9b4050484c744d094166db347734cd4aa4e6896d93838dc0bb26` |

## Findings

- **QB-01 — Exact statement and domain confirmed.** With the inventory notation
  \[
  \beta_{1/p}(s)=\sum_{n\ge1}\frac{n^{s-1}p^n}{p^{2n}+1},
  \]
  the pure candidate states that \(\beta_{1/p}(2)\) is irrational for **every integer \(p\ge2\)**. The mixed candidate states that \(1,\beta_{1/p}(1),\beta_{1/p}(2)\) are linearly independent over \(\mathbb Q\), separately for each such fixed \(p\). The documents use differing `B_2(1/p)` / `B_2(p)` labels, but their displayed sums agree. These are not statements for arbitrary real \(p\), simultaneous independence across different bases, ordinary Catalan's constant, or the limit \(q\to1\).

- **QB-02 — Full written candidate assemblies are present.** The pure document gives the functional and determinant construction, degree, coefficientwise prime and cyclotomic normalization, all-size decay, infinitely many nonzero actual determinants, and the final rationality contradiction. The mixed document gives the changed functional, arithmetic and analytic arguments, and an assembly using the pure document's fully written nonvanishing lemma. It proves irrationality of every nonzero integer mixture \(A\beta_{1/p}(1)+B\beta_{1/p}(2)\), with \(A\) even; scaling any rational relation by two makes that restriction harmless. Thus independence is a separately argued stronger candidate, not an inference from individual irrationality.

- **QB-03 — No definite load-bearing gap found in this bounded reading.** I checked the sensitive transitions against the supplied audit: (i) the mixed prime-adic constant \(-A/(2F_K(0))\) is explicitly retained and fits the worst entry valuation; (ii) the mixed zeroth-order functional subtracts \(f(0)\), and its early-node contributions are bounded by finite character sums; (iii) at orders \(4u\), local interpolation of the finite tails supplies a double zero in the pure case and a simple zero in the mixed case, producing the respective proper-part residue ranks, while the polynomial-quotient residue is separately included; (iv) the consecutive-singular-size argument obtains its cross-polynomial degree bound from the decay at infinity and uses exterior zeros without dividing by kernel-polynomial values at those nodes. These checks support the written chain but do not constitute formal verification or exhaustive external review. In particular, the local cyclotomic interpolation and residue-rank estimates remain the most specialized ingredients to have checked by an expert.

- **QB-04 — Claimed arithmetic margins close the stated argument.** The source normalization and decay give cubic margins \(1-1309/(150\pi^2)>0\) (pure) and \(1-244/(27\pi^2)>0\) (mixed). The degree is \(K\), so a hypothetical fixed rational denominator contributes only \(O(K)\) to the logarithm. The nonvanishing argument is all-index mathematics, not extrapolation from finite determinant computations. The cited computations are corroboration; their execution was not independently reproduced here.

- **QB-05 — Status must remain qualified.** The documents explicitly call these research candidates and disclaim external validation and established novelty. The final mixed audit expressly limits its own independent scope to analytic decay and nonvanishing, conditional on separately reviewed arithmetic; the parent review addresses that arithmetic. This supports “complete written proof candidate with internal audits,” not “externally verified theorem,” “published result,” or “new theorem” as a priority claim.

## Suggested inventory wording

1. **Reciprocal-integer q-beta irrationality.** For every integer \(p\ge2\), the candidate proves irrationality of \(\beta_{1/p}(2)=\sum_{n\ge1}np^n/(p^{2n}+1)\). Complete written proof candidate with internal audits; external expert review and novelty assessment remain outstanding.
2. **Stronger q-beta linear-independence extension.** For every integer \(p\ge2\), a separate candidate proves \(\mathbb Q\)-linear independence of \(1,\beta_{1/p}(1),\beta_{1/p}(2)\), with \(\beta_{1/p}(1)=\sum_{n\ge1}p^n/(p^{2n}+1)\). Complete written extension with internal audits; same status qualification. This subsumes the preceding irrationality statement and also implies irrationality of \(\beta_{1/p}(1)\).
