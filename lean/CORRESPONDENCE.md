# Manuscript-to-Lean correspondence

Source: *A moving-denominator Hankel argument for the irrationality of
ζ_{1/p}(3)*, research proof candidate dated 11 October 2026. This table describes
the current formal proof architecture, including an explicit sufficient
substitute for the manuscript's sharper growth estimate.

Appendix B and the elementary second proof are reconstructed from the displayed
messages in the owner-supplied shared conversation, preserved in
`../provenance/elementary-second-proof-source.md`. The linked scratch Markdown
attachments were not retrieved. The second proof shares the construction and
major analytic/arithmetic infrastructure with the first.

**Completed formal proof:** every production-library proof placeholder has
been replaced by a proof or sufficient proved substitute, including the public
denominator-clearing theorem. The full library and explicit-series solution
build successfully. All audited declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`. The records are
`../certificates/formal-proof-run.log` and `../certificates/kernel-axioms.log`.
The second proof also passes the build and standard-axiom audit, together with
the dependency check recorded in `../certificates/second-proof-dependencies.log`.

| Manuscript item | Lean declarations | Implementation | Formal status |
|---|---|---|---|
| ξ_p = ζ_{1/p}(3) = ∑ n²/(pⁿ−1) | `term`, `xi`, `summable_term`, `hasSum_xi`, `xi_pos` | `Defs`, `Elementary` | Defined; convergence and positivity proved. |
| Theorem 1.1 | `irrational_xi`, `theorem11` | `Main`, `Frozen/Theorem11` | Proved; transitive axiom audit passes. |
| Independent target statement | `QZeta3Challenge.irrational_qzeta3` | Separate `QZeta3Audit/Challenge` and `QZeta3Audit/Solution` modules | Mathlib-only challenge template; the solution derives the same statement from the library and passes the transitive axiom audit. |
| Euler functional L(f) = ∑ θ²f(q^m) | `theta`, `Lfun` | `Purity`, `Functional` | Defined; summability and linearity established on the functions used in the proof. |
| Moments μ_j and partial sums S_a | `mu`, `Lpoly`, `S`, `Lfun_pow`, `hasSum_monomial` | `Defs`, `Elementary`, `Purity` | Proved moment identifications. |
| Lemma 1.2, simple-pole purity | `purity`, `hasSum_poleKernel` | `Purity` | Proved through absolutely convergent geometric-lattice sums. |
| Moving denominator D_K and Δ_K(X) | `DK`, `F`, `res`, `mConst`, `mLin`, `nrm`, `Delta`, `DeltaR` | `Defs`, `Functional`, `GramIdentity` | Defined; the Gram/determinant identity is proved. |
| A_K, e_K, and the analytic exponent b_K | `AK`, `eK`, `aj`, `bK`, `AK_cast`, `eK_cast`, `bK_ge` | `Defs`, `Elementary` | Exact casts and `9*bK K ≥ K^3-K` proved. |
| Proposition 2.1, all-size real bound | `gram_det_eq`, `gram_det_le`, `analytic_bound` | `GramIdentity`, `AnalyticDeterminant`, `AnalyticWeight`, `AnalyticEntry`, `Analytic`, `Frozen/Prop21` | Proved with the factorial prefactor stated below. |
| Proposition 3.1, coefficientwise content at primes dividing p | `content_coeff_proved`, `content_coeff` | `ContentProof`, `ContentTruncation`, `Frozen/Prop31` | Proved using the subring of rationals with denominator coprime to p and finite geometric truncations. |
| Proposition 3.1, leading coefficient | `leading_coeff_proved`, `leading_coeff`, `natDegree_Delta` | `Leading`, `Frozen/Prop31` | Exact leading coefficient and degree proved. |
| Proposition 4.1, local cyclotomic costs | Cluster bases, weighted determinant clearing, low/high-range entry estimates, polynomial-moment rank bounds | `ClusterBasis`, `MovingClusterBasis`, `ClusterCounts`, `LocalDeterminants`, `LowClusterEntries`, `HighClusterBasis`, `HighOrderLocal`, `PolynomialMomentRank`, `LocalClusterTransport` | Proved and connected to public integrality; transitive axiom audit passes. |
| Proposition 4.1, C_K Δ_K ∈ ℤ[1/p][X] | `denominators_clear` | `GenericSpecialization`, `IntegerFractions`, `LocalPoleDescent`, `DenominatorDescent`, `Frozen/Prop41` | Proved; transitive axiom audit passes. |
| Uniform cyclotomic logarithm estimate | `cyclotomic_error_bound`, `log_cyclotomic_le` | `CyclotomicBounds`, `Denominators` | Proved. |
| Exponent sum ∑ c_{K,d} = O(K² log K) | `cApp_le`, `sum_inv_le_one_add_log`, `sum_cApp_le` | `Denominators` | Proved. |
| Sufficient substitute for the sharper totient asymptotic | `sum_cApp_totient_rational_le`, `sum_cApp_totient_rational_asymptotic`, `log_CK_rational_le`, `log_CK_sieve_le` | `TotientSieve`, `DenominatorSieve`, `Frozen/Prop41` | Proved with cubic constant 107/192. |
| Cauchy transform 𝓕(z) | `cauchySeries`, `cauchyF`, `cauchyF_eq`, `theta_theta_inv_sub` | `CauchyAtInfinity`, `CauchyFunctional` | Defined and identified with the Euler functional. |
| Meromorphicity at infinity and interpolation error decay | `meromorphicAt_cauchySeries_inv`, `tendsto_cauchySeries_monomial_sub` | `CauchyAtInfinity`, `MomentDecay`, `CauchyInterpolation` | Proved using convergent moment power series and exact finite remainders. |
| Genuine poles and nonrationality of the Cauchy germ | `cauchySeries_nonrational` and its pole/continuation inputs | `CauchyExterior`, `CauchyPole`, `CauchyMeromorphic`, `CauchyNonrational` | Proved; rules out eventual equality to every rational function with nonzero denominator polynomial. |
| Proposition 5.1, infinitely many nonzero determinants | `gram_frequently_ne_zero`, `frequently_ne_zero` | `NonvanishingAlgebra`, `NonvanishingAnalytic`, `Nonvanishing`, `Frozen/Prop51` | Proved via orthogonal interpolants, stabilization, Laurent order, and root counting. |
| Integral approximation polynomials P_K | `PK`, `PK_coeff_den`, `den_eq_one_of_coprime` | `Main` | Assembly connected to the denominator-clearing proof. |
| Section 6, cubic decay | `epsK`, `log_pow_mul_epsK_le_of_cost`, `tendsto_pow_mul_epsK_of_cost` | `Asymptotics` | Proved for every supplied cost α < 11/18. |
| Section 6, irrationality criterion | `irrational_of_poly_approx`, `intVal`, `pow_mul_aeval_eq` | `Criterion` | Proved. |
| Small exact consistency checks | `xi_eq_tsum`, `Delta_one`, `eval_Delta_two_two` | `Consistency/Series` | Proved; these supplement, rather than replace, the all-index arguments. |
| Appendix B, finite Gaussian recurrence | `gaussianRectangle`, `gaussianBinomial`, `gaussianBinomial_pascal` | `GaussianIdentity` | Integral definition and finite Pascal identity. |
| Lemma B.1, geometric residue identity and exceptional reciprocal exponent | `gaussian_residue_identity`, `geometricResidue_low`, `geometricResidue_reciprocal`, `gaussian_residue_integral` | `GaussianIdentity` | Exact monomial residue formula and integrality. |
| Proposition B.2, alternate coefficient content | `elementary_residue_sum_mem`, `content_coeff_of_gaussian`, `content_coeff_elementary` | `ElementaryContent` | Uses Gaussian monomial residues, finite linearity, truncations, and shared determinant normalization. |
| Appendix B, elementary denominator cost | `sum_cApp_totient_elementary_asymptotic`, `log_CK_elementary_le` | `ElementarySecondProof` | Sufficient cost 9/16 follows from the existing stronger 107/192 sieve bound. |
| Appendix B, second rationality contradiction | `elementary_cost_margin_eq`, `irrational_xi_elementary`, `irrational_qzeta3_elementary` | `ElementarySecondProof` | Direct criterion assembly through the Gaussian arithmetic branch; exact margin 7/144. |

Unless qualified, declarations are in namespace `QZeta3`; generic arithmetic
lemmas are under `QZeta3.Generic`. Module paths in the table are under
`QZeta3/` except for the comparator files.

## Changes to the manuscript's proof presentation

1. **Determinant prefactor.** The formal analytic bound is
   `K! * (12*(2*K-1)^2)^K * p^(-b_K)`, using Mathlib's factorial determinant
   inequality, rather than the manuscript's Hadamard prefactor involving
   `sqrt K`. Both contribute only `O(K log K)` to the logarithm.
2. **The exponent b_K.** The proof uses the sufficient lower bound
   `9*bK K ≥ K^3-K`; it does not need the manuscript's residue-dependent closed
   formula for b_K.
3. **Growth constant and positive margin.** The exponents `cApp` are unchanged,
   but the proof of their summed cost is replaced by a finite sieve at 2 and 3.
   It proves the sufficient constant `107/192`, giving the exact margin
   `11/18 - 107/192 = 31/576 > 0`. The sharper `321/(64*pi^2)` asymptotic is not
   asserted unconditionally. `log_pow_mul_epsK_le` and `tendsto_pow_mul_epsK`
   retain that sharper cost only as an explicit hypothesis; the main theorem
   uses their general-cost versions and `log_CK_rational_le`.
4. **Arithmetic content.** Integrality at every prime dividing p is encoded as
   coprimality of the rational denominator with p. Finite truncations prove the
   required content statement without treating a formal p-adic limit as a
   black-box assumption.
5. **Combining denominator information.** The gluing lemma
   `den_eq_one_of_coprime` combines content with membership in ℤ[1/p]. A
   separate theorem asserting that C_K is coprime to p is unnecessary.
6. **Degree.** The exact equality `natDegree_Delta = K` is proved. The final
   irrationality criterion only needs the weaker bound `natDegree_Delta ≤ K`.
7. **Series indexing.** The defining sum uses `n+1`, avoiding the artificial
   `0/0` summand. Summability is established before the `tsum` is used in the
   number-theoretic theorem.
8. **Nonvanishing scope.** The formal statement is `∀ N, ∃ K ≥ N, Δ_K(ξ_p) ≠ 0`.
   It does not assert nonvanishing at every index, a sign pattern, or a density.
9. **Elementary second proof.** The Gaussian recurrence replaces the general
   residue-integrality argument for coefficient content. The final theorem
   applies the approximation criterion directly, rather than invoking the
   first irrationality theorem. Its cost `9/16` is obtained by weakening the
   first formal proof's stronger `107/192` bound. The real estimate, local
   cyclotomic clearing, nonvanishing, exceptional residue identity, finite
   truncation estimates, and determinant normalization are shared.

## Dependency distinction for the second proof

`Meta/SecondProofAudit.lean` passes its check of declaration dependencies of
`irrational_qzeta3_elementary`. It requires the Gaussian arithmetic branch and
excludes the first `theorem11`, `irrational_xi`, and original
`content_coeff_proved` chain. This check concerns proof dependencies, not the
presence of shared modules in the import graph. The second proof remains an
elementary variant of the same determinant construction; it is not claimed as
a determinant-free method or as a formalization of the source excerpts'
unrelated direct scalar and integral candidates.

## Comparator and review boundary

The independent comparator challenge intentionally contains one statement
placeholder. The solution is checked in a separate environment and has no
`sorryAx` dependency. This template exception is reported separately from the
completed library; no custom axiom replaces a proof obligation. The checked
solution is an explicit-series restatement; a separate execution of the
external comparator service is not claimed.

No claim of external peer review, novelty verification, or a completed human
statement audit is made. The present document records the implementation and
its explicit proof substitutions. The integrality bridge and main theorem
have passed the full build and transitive axiom checks.
