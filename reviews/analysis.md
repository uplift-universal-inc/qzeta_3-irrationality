# Independent analytic review

Source: `archive://q_zeta3_checkpoint_2026-10-11/q_zeta3_proof_candidate_2026-10-11.tex`

SHA256: `78082f1dce9e37ef710e5f7fbc20423cbdb5633f6f0c69b3affc7cf225c21b5f`

Review scope: construction and purity; the all-size real determinant bound; infinitely many nonzero determinants; final irrationality assembly. I read the complete actual source, including the arithmetic sections and appendix, and did not use earlier reviews. For this bounded review I assume the coefficientwise arithmetic conclusions of `prop:content` and `prop:denominators` exactly as stated. I do not certify those arithmetic proofs, the optional stronger appendix, the bibliography, or novelty.

**Result:** no blocking mathematical defect found within this scope. The verified obligations below explain this conclusion; it is conditional on the stated arithmetic inputs, not a blanket validation of the manuscript or main theorem.

## ANA-001 — Construction, convergence, and purity

Severity: none; verified. Evidence: lines 92–152, `eq:functional`, `lem:purity`, `eq:formal-functional`, and `eq:Delta`.

For every analytic test function, the identity `theta^2 f(x) = x f'(x) + x^2 f''(x)` gives the concrete bound

\[
 |\mathcal L(f)|\le\frac q{1-q}\|f'\|_{[0,q]}
 +\frac{q^2}{1-q^2}\|f''\|_{[0,q]}.
\]

Thus the functional converges absolutely and is continuous for the needed uniform derivative limits. Also `xi_p` converges since its summand is at most `2 n^2 q^n`. In the purity calculation all double-series terms are nonnegative and their total is finite; reindexing `a+m=b` removes exactly `b=1,...,a`. The rational identity `g(q^b)=p^b(p^b+1)/(p^b-1)^3` gives exactly the displayed `S_a`, with no extra zeta values or missing constant. The moments of `1` and `x^j` follow directly.

Every `x^(i+j)/D_K(x)` has only the distinct simple poles `p,...,p^K`. Its unique polynomial-plus-pole decomposition therefore lies in the defined domain of `L_X`; substituting `X=xi_p` recovers the actual functional. This is a bilinear Gram matrix; positivity is neither asserted nor required.

Smallest repair: none required. The displayed continuity bound could optionally replace the shorter convergence explanation, but is not a missing hypothesis.

## ANA-002 — Derivative inequalities and all-size determinant bound

Severity: none; verified. Evidence: lines 191–264, `eq:jet-bounds`, `eq:weight-bounds`, and `eq:analytic-exact`.

The monic basis change has determinant one. For `m<R_j`, all three Euler jets of `B_j` vanish because the root multiplicity is three. At a surviving node, each root satisfies `rho>=q^(R_j)>=x`; a term produced by `u` successive derivatives has at least one factor `x/rho<=x/q^(R_j)` and every remaining replacement ratio is at most one. There are `j^u` labeled derivative choices. Hence the stated bound holds for `u=1,2`, including the separate zero-derivative case `j=0`.

The weight calculation is correct: `alpha<=4x/3`, `beta<=16x/9`, and `alpha^2<=8x/9` for `x<=1/2`, yielding `theta^2 W_K<= (8/3)e^(2/3)x`. With `R=max(R_i,R_j)` and `h=i+j`, the six terms in the second derivative of `B_i B_j W_K` have combined constants at most

\[
 e^{2/3}\bigl(i^2+2ij+j^2+\tfrac83(i+j)+\tfrac83\bigr),
\]

times `q^(a_i+a_j) q^(m-R)`. A derivative on `W_K` supplies `x<=x/q^R`; derivatives on either polynomial supply a factor no greater than `x/q^R`. The common factor is therefore legitimate even when the derivative falls on the polynomial with smaller `R_j`. For `R=0`, necessarily `i=j=0`, and the sum starts at `m=1`; its cost is still at most `(1-q)^(-1)`. The claimed constant 12 safely exceeds `(16/3)e^(2/3)`.

After extraction of row and column factors, Hadamard gives the exact displayed bound without a positivity assumption. Direct symbolic summation gives, for `K=3u+r`,

| r | `2 sum_(j<K) a_j` |
|---|---|
| 0 | `3u^3+3u^2` |
| 1 | `3u^3+6u^2+3u` |
| 2 | `3u^3+9u^2+8u+2` |

These are precisely `(K^3+3K^2-c_r)/9` for `(c_0,c_1,c_2)=(0,4,2)`, including `K=1`. The prefactor contributes only `O(K log K)`, so the stated cubic exponent and weaker `O_p(K^2)` remainder follow.

Smallest repair: none required.

## ANA-003 — Cauchy transform and interpolation with moving denominators

Severity: none; verified. Evidence: lines 639–693, `eq:cauchy` through `eq:exterior-zeros`.

Differentiating `1/(z-x)` twice with `theta` gives `x(z+x)/(z-x)^3`. The resulting series has a uniformly `O(q^m)` tail on each compact set away from `{0,q,q^2,...}`. Around an individual `q^m`, the other terms form an analytic function; the cubic coefficient `2q^(2m)` is nonzero. Thus there are infinitely many genuine poles. The domain is connected, so the identity theorem also excludes equality to a rational function merely as a germ at infinity. For `|z|>=2q`, the series is uniformly `O(z^(-2))`, establishing analyticity at infinity.

The numerator defining `T_(n,Q)` vanishes on `z=x`, so its polynomial division by `z-x` is exact and lowers its degree in `z` to at most `n-1`. Applying the fixed actual functional to its rational-in-`x` coefficients is legitimate. The resulting identity keeps the same `D_n` throughout; there is no unnoticed replacement by a fixed denominator.

For the asymptotic remainder one can avoid any interchange ambiguity by the exact identity

\[
 \frac1{z-x}=\sum_{j=0}^{n-1}\frac{x^j}{z^{j+1}}
 +\frac{x^n}{z^n(z-x)}.
\]

Orthogonality kills the first `n` terms. The continuity estimate in ANA-001 gives `R_(n,Q_n)=O(z^(-n-1))`, hence `E_n=D_n R_(n,Q_n)=O(z^(-1))`. The geometric-series justification in the source reaches the same result.

At `z=p^a`, `R_(n,Q_n)` is analytic as a function of `z`, since this point is separated from `[0,q]`. Its test function may have a repeated pole in the **x** variable when `a<=n`; that pole is outside `[0,q]` and is permitted for the actual functional. This step does not improperly invoke the simple-pole-only formal functional `L_X`. It follows that all `n` claimed exterior zeros hold.

Smallest repair: none required.

## ANA-004 — Consecutive singular sizes and coincident zeros

Severity: none; verified. Evidence: lines 695–707.

For singular sizes `n,n+1`, the polynomial cross-product is

\[
 V=T_{n+1}Q_n-T_nQ_{n+1}=Q_{n+1}E_n-Q_nE_{n+1}.
\]

The degree bounds `deg Q_n<=n-1`, `deg Q_(n+1)<=n`, together with `E_j=O(z^(-1))`, imply `deg V<=n-1`. The common nodes `p,...,p^n` are `n` distinct zeros of this polynomial. Therefore `V=0`, even if either or both `Q` polynomials vanish at some nodes. No value of a quotient at a zero denominator is used. This gives equality as rational functions for arbitrary choices of nonzero kernel vectors.

Smallest repair: none required.

## ANA-005 — Excluding an eventually singular tail

Severity: none; verified. Evidence: lines 709–730, `prop:normality`.

An eventually singular tail forces one common rational function `T/Q`. Reduction and coprimality imply `Q_n=U_n Q`, `T_n=U_n T` with each `U_n` nonzero; the case `T=0,Q=1` is covered. Nonrationality of the Cauchy transform implies the germ `E=FQ-T` is nonzero. Since it is meromorphic at infinity and `U_N E=O(z^(-1))`, it has a finite order `h>=1` there. In particular, `E=c z^(-h)(1+O(z^(-1)))` is nonzero beyond one fixed radius.

The same error condition for each `n` gives `deg U_n<=h-1`, independently of `n`. Choose an integer `a_0` such that `p^a` is beyond that radius for every `a>=a_0`. For `n>=max(N,a_0)`, exterior interpolation forces the single polynomial `U_n` to vanish at the `n-a_0+1` distinct nodes `p^(a_0),...,p^n`. Choosing `n-a_0+1>h-1` is the contradiction. Thus this is a bound on each individual polynomial's zeros, not an invalid inference from zeros distributed over varying polynomials.

Smallest repair: none required. The source's last three sentences already contain this argument; the explicit `a_0` formulation only makes its quantifiers more visible.

## ANA-006 — Conditional irrationality assembly

Severity: none; verified conditional on the arithmetic conclusions. Evidence: lines 614–626 and 735–773.

Assuming `prop:content` and `prop:denominators`, prime-by-prime integrality gives `P_K in Z[X]`; the leading coefficient establishes degree `K`. Positivity of `C_K` and nonzero `p^(-e_K)` preserve exactly the zero/nonzero status of `Delta_K(xi_p)`.

The cubic coefficient combines correctly as `385/(64 pi^2)-1/2-1/9=-epsilon`. The threshold is exactly `pi^2>315/32`; the quoted elementary bound `pi>157/50` suffices. Exact rational arithmetic confirms the displayed lower bound `3487/3549456` for `epsilon`. For fixed `p` and a hypothetical fixed denominator `b`, both `O_p(K^2 log K)` and `K log b` are `o(K^3)`. Consequently the displayed upper bound tends to zero along every unbounded subsequence, including the infinite set supplied by ANA-005. On that set `b^K P_K(a/b)` is a nonzero integer, giving the stated contradiction. No density or effective first nonzero size is needed.

Smallest repair: none required within this bounded scope.

## Review disposition

Blocking findings in the assigned analytic scope: **0**. Minor mathematical corrections required in that scope: **0**. The optional explanatory estimates above are not proposed as new hypotheses or repairs. Source was not edited. This report should be combined with an independent arithmetic review before assigning any status to the full proof.
