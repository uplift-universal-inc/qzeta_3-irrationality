# Theorems in the current paper

Domain throughout: `p` is an integer at least 2, `q=1/p`, and `K≥1`. All claims below have written proofs in `paper/main.tex`. Internal review is recorded separately from formal verification.

| ID | Result | Exact statement / purpose | Paper label |
|---|---|---|---|
| QZ3-MAIN | Irrationality | `Σ n²/(pⁿ−1)` is irrational for each fixed `p≥2` | `thm:main` |
| QZ3-PURE | Pure pole moments | `L((1−p^(−a)x)^−1)=ξ_p−S_a` for `L(f)=Σ(θ²f)(q^m)` | `lem:purity` |
| QZ3-REAL | All-size real bound | `|Δ_K(ξ_p)|≤[12(2K−1)²√K]^K p^(−b_K)`, `b_K=(K³+3K²−c_(K mod 3))/9`, `c=(0,4,2)` | `prop:analytic` |
| QZ3-CONTENT | Full base-prime content and degree | Every coefficient has valuation at least `v_ell(p)e_K` at `ell|p`; leading coefficient `(-1)^(K(K−1)/2)p^e_K`, `e_K=K(K²−1)/2` | `prop:content` |
| QZ3-DENOM | Cyclotomic clearing | The symbolic product `∏ Φ_d(z)^(c_K,d)` clears `Δ_(K,z)` into `Z[z,z^−1][X]`; its specialization obeys `log C_K(p)≤385 K³ log p/(64π²)+O_p(K² log K)` | `prop:denominators` |
| QZ3-INTEGER | Integer polynomials | `C_K p^(−e_K) Δ_K ∈ Z[X]`, degree exactly `K` | `cor:integer-polys` |
| QZ3-NONZERO | Infinite nonvanishing | `Δ_K(ξ_p)≠0` for infinitely many `K`, using a nonrational Cauchy transform | `prop:normality` |
| QZ3-SHARP | Stronger denominator bound | Replace the high-order cost `7(K−d)+3` by `5(K−d)+3`; total constant `321/(64π²)` | `prop:stronger` |

The main theorem depends on QZ3-PURE, REAL, CONTENT, DENOM, INTEGER, and NONZERO. QZ3-SHARP improves the margin but is not necessary for the conservative proof. It is included in this paper rather than deferred.

The rank estimate `rank B_d≤max(0,K−d−1)` is a proof-local step in QZ3-DENOM. It is over the fraction field; reduction modulo a root-of-unity parameter alone would not suffice. No polynomial quotient contribution is omitted.

## Quantitative margins

- Conservative: `11/18−385/(64π²) ≈ 0.001600865763 > 0`.
- Refined: `11/18−321/(64π²) ≈ 0.102922049405 > 0`.
- Rational lower certificate for the conservative margin, using `π>157/50`: `3487/3549456 > 0`.
- First formal proof's finite sieve: `11/18−107/192=31/576>0`.
- Elementary second proof: `11/18−9/16=7/144>0`.

These are exact expressions with descriptive decimals. The proof does not infer positivity from rounded numbers.

## Formal correspondence

The main irrationality theorem has a completed Lean proof. All declarations in the transitive audit, including `QZeta3.theorem11` and the explicit-series solution, use only `propext`, `Classical.choice`, and `Quot.sound`.

The formalization retains the appendix's cyclotomic exponents but proves their growth with the sufficient finite-sieve constant `107/192`, giving the exact positive margin `31/576`. It does not formalize the sharper π-based asymptotic in QZ3-DENOM or QZ3-SHARP. Its real bound uses a sufficient factorial prefactor in place of the manuscript's Hadamard prefactor. [CORRESPONDENCE.md](../lean/CORRESPONDENCE.md) records these substitutions and maps the arithmetic, convergence, nonvanishing, and final irrationality statements. See [VERIFICATION.md](VERIFICATION.md) for the build and audit evidence.

## Elementary second proof

Appendix B presents an alternate coefficient-content argument for the same determinant construction and irrationality target.

| Result | Exact statement / role | Lean declarations | Paper label |
|---|---|---|---|
| Gaussian residue identity | For `F_K(x)=∏_(a=1)^K(x−p^a)`, the residue sum `Σ p^(ad)/F_K′(p^a)` vanishes for `0≤d<K−1` and equals `p^(d−K+1)[d choose K−1]_p` otherwise | `gaussian_residue_identity`, `geometricResidue_low`, `gaussian_residue_integral` | `lem:gaussian-residue` |
| Exceptional residue | `Σ p^(−a)/F_K′(p^a)=−1/F_K(0)` | `geometricResidue_reciprocal` | `eq:gaussian-exceptional` |
| Gaussian coefficient content | Every coefficient of `p^(−e_K)Δ_K` has denominator coprime to `p` | `content_coeff_elementary` | `prop:elementary-content` |
| Elementary growth | `log C_K≤(9/16)K³ log p+O_p(K² log K)`, obtained from the stronger existing `107/192` sieve bound | `log_CK_elementary_le` | `eq:elementary-cost` |
| Alternate irrationality assembly | Same convergent series is irrational for all integers `p≥2`, through the Gaussian content proof and margin `7/144` | `irrational_xi_elementary`, `irrational_qzeta3_elementary` | Second proof of `thm:main` in `app:elementary` |

These declarations are in namespace `QZeta3` and pass the build and standard-axiom audit. The second proof applies the approximation criterion directly and does not invoke the first irrationality theorem or its original content theorem; the dependency audit verifies that distinction. It shares the real estimate, local cyclotomic clearing, nonvanishing theorem, and supporting determinant algebra. It is an elementary variant of the same construction, not an independent determinant-free method.
