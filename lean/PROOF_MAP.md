# Proof map

The target statement is unchanged:

```lean
theorem QZeta3.theorem11 (p : ℕ) (hp : 2 ≤ p) :
  Irrational (QZeta3.xi p)
```

Here `xi p = ∑' n : ℕ, (n + 1)^2 / ((p : ℝ)^(n + 1) - 1)`;
`hasSum_xi` verifies convergence. Thus the theorem concerns
`ζ_{1/p}(3)` for every natural integer `p ≥ 2`, including composite bases.

The original library contained nine placeholders. Eight correspond to the
seven mathematical components below (purity and the Gram identity form one
component). The remaining placeholder, the sharp totient asymptotic, is
replaced by the sufficient elementary growth estimate described afterward.

| Original target | Formal proof route | Principal modules |
|---|---|---|
| `purity`, `gram_det_eq` | Absolutely convergent geometric sums, Euler derivatives, Lagrange partial fractions, and linearity of the moment functional identify the rational Hankel determinant with the real Gram determinant. | `Purity`, `Functional`, `DividedDifferences`, `GramIdentity` |
| `gram_det_le` | A monic triple-root polynomial basis, bounds on the weight and its first two Euler derivatives, geometric tail estimates, and the determinant permutation bound. | `AnalyticWeight`, `AnalyticDeterminant`, `AnalyticEntry`, `GeometricTail`, `GramBasis` |
| `leading_coeff` | Vandermonde factorization of the linear moment matrix and the product of derivatives of the nodal polynomial give the exact highest coefficient. | `Leading` |
| `content_coeff` | Finite geometric-series truncations replace the infinite local expansion. Divided differences, explicit residue denominator bounds, and a translated determinant establish denominator coprimality with the base. | `ContentProof`, `ContentTruncation`, `ResidueDenominators` |
| `denominators_clear` | Local rings of rational functions, moving root-of-unity cluster bases, integer row and column weights, upper-node cancellation, the rank correction for polynomial moments, and integer polynomial descent. Specialization at the integer base recovers the original rational determinant. | `CyclotomicLocal`, `MovingClusterBasis`, `ClusterCounts`, `HighClusterBasis`, `HighOrderLocal`, `LocalDeterminants`, `GenericGram`, `LocalGramBounds`, `IntegerFractions`, `LocalPoleDescent`, `DenominatorDescent`, `GenericEvaluation` |
| `log_cyclotomic_le` | Cyclotomic product estimates give `log Φ_d(p) ≤ φ(d) log p + 2`. | `CyclotomicBounds`, `Denominators` |
| `gram_frequently_ne_zero` | Singular moment matrices give interpolation identities. A nonzero meromorphic germ has finite Laurent order. The Cauchy transform has infinitely many nonzero cubic poles, so it cannot agree with a rational function near infinity. | `NonvanishingAlgebra`, `NonvanishingAnalytic`, `CauchyAtInfinity`, `CauchyExterior`, `CauchyPole`, `CauchyMeromorphic`, `CauchyNonrational`, `CauchyInterpolation`, `Nonvanishing` |

## Growth estimate used in the proof

The original unproved claim with cubic constant `321/(64π²)` is not a theorem
of this development. `TotientSieve` and `DenominatorSieve` instead use a finite
sieve at 2 and 3 to prove

```text
log C_K ≤ (107/192) K³ log p + O_p(K² log K).
```

The exact gap is

```text
11/18 - 107/192 = 31/576 > 0.
```

This is sufficient for `b^K ε_K → 0` for every positive integer `b`.
`Main.lean` uses `log_CK_rational_le` and the general
`tendsto_pow_mul_epsK_of_cost`; the public proposition is
`log_CK_sieve_le`. The original cyclotomic exponents `cApp` and the original
integrality target are retained. Conditional bookkeeping lemmas for an
arbitrary cubic cost, including the sharp constant, do not assert that the
sharp growth hypothesis has been proved.

The analytic bound retains the original skeleton's factorial determinant
prefactor. It contributes only a lower-order logarithmic term and does not
change the irrationality conclusion.

## Final dependency chain

`analytic_bound` + `content_coeff` + `denominators_clear` give integer
polynomials `PK` with controlled degree and small values at `xi p`.
`frequently_ne_zero` supplies arbitrarily large indices with nonzero values.
The sieve estimate supplies exponential decay. `irrational_of_poly_approx`
then proves `irrational_xi`, exported as `theorem11`.

## Elementary second proof

This branch proves the same statement using the same determinant construction.
Its arithmetic route is:

1. `gaussianRectangle` and `gaussianBinomial` define integral Gaussian
   coefficients by a finite Pascal recurrence. `gaussian_residue_identity`
   computes the residue of each nonnegative monomial; `geometricResidue_low`
   handles the vanishing range and `geometricResidue_reciprocal` the exceptional
   reciprocal exponent.
2. `gaussian_residue_integral` supplies `elementary_residue_sum_mem` by finite
   linearity. With finite geometric truncations and the shared determinant
   normalization, this gives `content_coeff_elementary`.
3. `PK_coeff_den_elementary` combines that content proof with the shared
   `denominators_clear` result, using `PK_coeff_den_of_content`.
4. `log_CK_elementary_le` weakens the already proved finite-sieve cost
   `107/192` to `9/16`. `elementary_cost_margin_eq` records the exact margin
   `7/144`, and `tendsto_pow_mul_epsK_elementary` supplies decay.
5. `irrational_xi_elementary_of_content` applies `irrational_of_poly_approx`
   directly using the shared real bound and nonvanishing theorem. Instantiating
   its content input gives `irrational_xi_elementary`, followed by the
   explicit-series theorem `irrational_qzeta3_elementary`.

`Meta/SecondProofAudit.lean` requires the Gaussian arithmetic branch to occur
in the final dependency graph and excludes the first `theorem11`,
`irrational_xi`, and original `content_coeff_proved` route. This verifies an
alternate content derivation and assembly, while retaining the common
determinant, analytic, denominator-clearing, nonvanishing, and supporting
algebra. It does not assert complete independence of the two methods.

The source excerpts are preserved in
`../provenance/elementary-second-proof-source.md`; their linked scratch
Markdown files were not retrieved. Appendix B of the paper gives the
reconstructed elementary presentation.

## Verification

The pinned toolchain is Lean 4.34.1 with Mathlib 4.34.1. The full build and
transitive audit pass. The build and audit commands are:

```bash
lake build QZeta3 QZeta3Audit.Solution
lake env lean QZeta3/Meta/AxiomsAudit.lean
lake env lean QZeta3/Meta/SecondProofAudit.lean
```

All audited declarations list only the usual Lean axioms `propext`,
`Classical.choice`, and `Quot.sound`; `sorryAx` is absent. The records are
`../certificates/formal-proof-run.log` and `../certificates/kernel-axioms.log`.
`make formal-proof` from the repository root also applies the source and axiom
allowlist gates and the second-proof dependency audit. That audit passes; its
record is `../certificates/second-proof-dependencies.log`.

`QZeta3Audit.Solution` checks the theorem in the original series notation
without importing the separate challenge template. The challenge's sole
intentional placeholder is outside the solution dependency graph. A separate
external comparator run is not claimed. The local runtime compatibility shim, when needed in the
hosted environment, changes process-path discovery only; it does not alter
Lean's kernel or theorem checking.
