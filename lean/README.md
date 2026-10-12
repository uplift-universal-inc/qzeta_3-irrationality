# QZeta3

Lean 4 / Mathlib formalization of the moving-denominator Hankel argument for

```lean
theorem QZeta3.theorem11 (p : ℕ) (hp : 2 ≤ p) : Irrational (QZeta3.xi p)
```

The elementary second proof exports the same target in explicit series notation:

```lean
theorem QZeta3.irrational_qzeta3_elementary (p : ℕ) (hp : 2 ≤ p) :
  Irrational (∑' n : ℕ, ((n : ℝ) + 1) ^ 2 / ((p : ℝ) ^ (n + 1) - 1))
```

Here `xi p = ∑' n : ℕ, (n + 1)^2 / (p^(n + 1) - 1)` over the real numbers.
`hasSum_xi` proves convergence, so the statement concerns the genuine series
\(\sum_{n\ge1} n^2/(p^n-1)=\zeta_{1/p}(3)\), including composite integers `p ≥ 2`.

Lean and Mathlib are pinned to `v4.34.1` by `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`.

## Integration status

**Complete and kernel checked.** The full library and explicit-series solution
build successfully. All declarations in the transitive axiom audit use only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` remains. All
production proof placeholders, including `QZeta3.denominators_clear`, have
been replaced by proofs or sufficient proved substitutes. The main
irrationality statement is unchanged.

The reproducible gate is `make formal-proof` from the repository root. Its
records are [formal-proof-run.log](../certificates/formal-proof-run.log) and
[kernel-axioms.log](../certificates/kernel-axioms.log). The separate comparator
challenge still contains one intentional statement-template placeholder,
excluded from the solution's dependency graph, as explained below.
The elementary second proof passes the same build and standard-axiom audit;
its additional dependency check passes in
[second-proof-dependencies.log](../certificates/second-proof-dependencies.log).

| Layer | Main modules | Role and current status |
|---|---|---|
| Definitions and convergence | `Defs`, `Elementary`, `Consistency/Series` | Defines the actual series and determinant; proves summability, positivity, degree bound, and small exact consistency checks. |
| Functional and Gram identity | `Purity`, `Functional`, `WeightedMoments`, `GramIdentity`, `GramBasis` | Computes monomial and simple-pole moments, proves partial-fraction bookkeeping, and identifies the real Gram determinant with `DeltaR`. |
| Analytic determinant estimate | `AnalyticDeterminant`, `AnalyticWeight`, `AnalyticEntry`, `Analytic`, `Frozen/Prop21` | Triple-root polynomials, vanishing jets, weighted entry estimates, and a factorial determinant bound; `analytic_bound` is proved. |
| Arithmetic content | `Content`, `DividedDifferences`, `ContentProof`, `ContentTruncation`, `Leading`, `Frozen/Prop31` | Rational subring and finite-truncation arguments prove `content_coeff`; exact determinant algebra proves `leading_coeff` and `natDegree_Delta`. |
| Elementary arithmetic branch | `GaussianIdentity`, `ElementaryContent` | Finite integral Gaussian coefficients give exact monomial residue values; finite linearity, truncations, and shared determinant algebra prove `content_coeff_elementary`. |
| Local cyclotomic denominator bounds | `GenericMoments`, `GenericGram`, `CyclotomicLocal`, `LocalDeterminants`, `ClusterBasis`, `MovingClusterBasis`, `ClusterCounts`, `LowClusterEntries`, `HighClusterBasis`, `HighOrderLocal`, `PolynomialMomentRank`, `LocalClusterTransport` | Proves moving cluster bounds, integer row/column weights, exact residue counts, high-range cancellation, and the polynomial-moment rank correction. The public integrality theorem passes the transitive axiom audit. |
| Denominator descent and specialization | `GenericSpecialization`, `IntegerFractions`, `LocalPoleDescent`, `DenominatorDescent`, `Frozen/Prop41` | Connects generic rational-function calculations to integer Laurent expressions and evaluation at `p`; the public `denominators_clear` proof is now connected. |
| Growth of the clearing factor | `CyclotomicBounds`, `Denominators`, `TotientSieve`, `DenominatorSieve` | Proves a uniform cyclotomic logarithm bound and the sufficient cubic cost `107/192`; no unproved totient asymptotic is used. |
| Nonvanishing | `CauchyFunctional`, `CauchyAtInfinity`, `MomentDecay`, `CauchyExterior`, `CauchyPole`, `CauchyMeromorphic`, `CauchyNonrational`, `CauchyInterpolation`, `NonvanishingAlgebra`, `NonvanishingAnalytic`, `Nonvanishing`, `Frozen/Prop51` | Proves meromorphicity at infinity, genuine cubic poles, exclusion of rational germs, orthogonal interpolants, and infinitely many nonzero determinants. |
| Irrationality assembly | `Criterion`, `Asymptotics`, `Main`, `Frozen/Theorem11` | Combines integral polynomial values, cubic decay, and nonvanishing; the main theorem passes the transitive axiom audit. |
| Elementary second assembly | `ElementarySecondProof` | Uses Gaussian content, the sufficient growth cost `9/16`, and the approximation criterion directly; exports `irrational_xi_elementary` and `irrational_qzeta3_elementary`. |

Module names in this table are under `QZeta3/`. `CauchyDomain` additionally
proves convergence and analyticity of the moment series for `|u| < p`; the
nonvanishing proof only needs the smaller exterior domain supplied by
`CauchyExterior`.

## The growth estimate used by the formal proof

The cyclotomic exponents remain the manuscript's Appendix A exponents
`cApp K d`, including `5*(K-d)+3` in the high range. The formal proof uses

\[
\log C_K\le \frac{107}{192}K^3\log p+O_p(K^2\log K).
\]

This follows from an elementary sieve using the primes 2 and 3, with period-six
finite sums (`TotientSieve` and `DenominatorSieve`). The exact positive margin is

\[
\frac{11}{18}-\frac{107}{192}=\frac{31}{576}>0.
\]

`Main.irrational_xi` applies `log_CK_rational_le` and the general-cost decay
lemma `tendsto_pow_mul_epsK_of_cost`. The public sufficient estimate is
`log_CK_sieve_le`. The manuscript's sharper constant `321/(64*pi^2)` is **not
claimed as an unconditional growth theorem** in this development. The old
sharp-cost asymptotic wrappers remain valid conditional lemmas: they explicitly
assume that sharper input. See `CORRESPONDENCE.md` for all statement changes.

## The elementary second proof

`GaussianIdentity` defines `[n choose k]_p` by a finite Pascal recurrence in
natural numbers and proves the exact geometric residue identity. Finite
linearity then supplies polynomial residue integrality in `ElementaryContent`.
This replaces the first proof's general residue-integrality argument; the
exceptional reciprocal residue, finite tail estimates, and determinant
normalization share existing algebra.

`ElementarySecondProof` rebuilds coefficient integrality through
`PK_coeff_den_of_content` and applies `irrational_of_poly_approx` directly.
Its final proof does not invoke `theorem11`, `irrational_xi`, or the original
`content_coeff_proved` chain. `Meta/SecondProofAudit.lean` checks this dependency
distinction and requires the Gaussian branch to be present. Imports alone do
not establish this distinction; the audit follows declaration dependencies.

The second proof uses `log_CK_elementary_le` with cost `9/16`, giving
`11/18−9/16=7/144>0`. This cost follows by weakening the already proved
`107/192` estimate. Both proofs share the determinant, real bound, local
cyclotomic clearing, and nonvanishing theorem. The second is an elementary
variant of the same construction, with an alternate arithmetic branch, rather
than a determinant-free or unrelated independent method.

The source is the retrieved conversation excerpts in
`../provenance/elementary-second-proof-source.md`. The linked scratch Markdown
attachments were unavailable; their full contents have not been audited.

## Building and auditing

```bash
lake exe cache get
lake build QZeta3 QZeta3Audit.Solution
lake env lean QZeta3/Meta/AxiomsAudit.lean
lake env lean QZeta3/Meta/SecondProofAudit.lean
lake env lean QZeta3Audit/Solution.lean
```

Cache download requires network access. Without cached dependencies, Lake
builds the imported Mathlib modules from source. No Prove2Me, Palomar, or
TauCeti result is assumed by a proof: verification is performed by Lean's kernel
against the pinned Mathlib dependency.

The transitive audits of `QZeta3.theorem11`, `QZeta3.denominators_clear`, and
the explicit-series solution theorem contain only the permitted standard
axioms `propext`, `Classical.choice`, and `Quot.sound`. A successful build with
`sorry` warnings would be insufficient. The
repository includes `scripts/audit.sh` and `QZeta3/Meta/AxiomsAudit.lean` for
inspection; the audit distinguishes actual proof placeholders from
comments and from the separate comparator template.

## Independent comparator statement

`QZeta3Audit/Challenge.lean` imports Mathlib alone and declares the target with
one intentional statement-template `sorry`. `QZeta3Audit/Solution.lean`
independently declares the same theorem name and proves it from
`QZeta3.theorem11`; it does **not** import `Challenge`. These are separate
comparison environments, configured by `QZeta3Audit/comparator.json`.

The challenge placeholder is an explicit audit exception for the independent
statement template, not a permitted dependency of the solution. The solution's
axiom audit excludes `sorryAx`. Replacing the
challenge by an import of the solution would remove the independent statement
check. No custom axiom is introduced to replace either proof obligation.
The explicit-series solution is kernel checked; these records do not assert
a separate execution of the external `leanprover/comparator` service.

## Fidelity, provenance, and review

`CORRESPONDENCE.md` maps the manuscript's claims to Lean declarations and
records the sufficient rational growth substitute. `formalization.yaml`
records scope, provenance, and review status. The initial imported skeleton
was recorded as generated by Claude on 11 October 2026; the subsequent proof
completion work uses OpenAI Codex agents in ChatGPT Work.

Kernel checking establishes the formal propositions. Human review of the
statement-to-manuscript correspondence and external mathematical peer review
are separate tasks; neither is claimed here. The historical and novelty
claims of the manuscript are not certified by this Lean project.

License: Apache 2.0 (`LICENSE`).
