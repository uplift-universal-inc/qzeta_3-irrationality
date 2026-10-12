# Independent arithmetic review

Reviewed source: `q_zeta3_proof_candidate_2026-10-11.tex`.

SHA256: `78082f1dce9e37ef710e5f7fbc20423cbdb5633f6f0c69b3affc7cf225c21b5f`.

Scope: definitions and simple-pole moments (lines 92–171), coefficient content (266–364), cyclotomic denominators and integrality (366–626), and the stronger appendix (795–872). I derived the arithmetic steps from this TeX source without relying on the checkpoint's earlier audit verdicts. The real determinant estimate and eventual-nonvanishing argument are outside this review.

**Conclusion within that scope:** I found no arithmetic obstruction to the stated integer polynomials, including the appendix's denominator-growth constant **321/(64π²)**. The points below give the specific inference chains checked; this is not a verification of the whole irrationality theorem or a formal proof certification.

## Findings and evidence

### ARITH-001 — Coefficientwise content and exact degree

- Severity: none identified.
- Evidence: lines 289–343 give `S_a = −Z + H(p^a)`, with `Z` and every `c_j` integral in `Q_ell` for `ell | p`. The divided-difference identities yield precisely `M_0 = (X+Z)/F_K(0) + R_0` and `M_k = −(X+Z)h_{k−K} + R_k` for `k ≥ 1`. In `R_0`, the first nonzero summand has `j ≥ K`, so applying the divided difference to `H(t)/t` introduces no negative-power exception. All `R_k` are integral; the only potentially nonintegral matrix entry is `(0,0)`. Multiplication of its row by `p^{A_K}` therefore gives the coefficientwise lower bound `v_ell(det T) ≥ −v_ell(p) A_K`.
- Combining that bound with `Delta_K = (−1)^{K²} p^{A_K K} det T` gives exactly `e_K = A_K(K−1)`. The coefficient-of-`X` matrix has the isolated `(0,0)` entry and the stated anti-triangular remaining block, giving `[X^K]Delta_K = (−1)^{K(K−1)/2}p^{e_K}` (lines 345–363), including `K=1`.
- Smallest repair: none required for this step.

### ARITH-002 — Low cyclotomic orders

- Severity: none identified.
- Evidence: lines 415–426 construct a basis whose reduction is a CRT basis, so its determinant is a local unit. For an intracluster residue, `v(F'(z^a))=m−1` and the numerator contributes at least `j+k`; changing between `(x−z^a)^{-1}` and `(1−z^{-a}x)^{-1}` contributes only a local unit. Since `S_a` has pole order at most three, the proper-part bound is `j+k−m−2` (428–443). Polynomial quotients have degree at most `K−2`, integral coefficients, and at most a simple pole after applying moments.
- The chosen weights clear both parts coefficientwise in `X`. Summing them gives `f(m)=m²/4+2m+1` for even `m`, and `m²/4+2m+3/4` for odd `m`. With `sum m_r² ≤ K²/d+d/4`, the total is `K²/(4d)+2K+17d/16` (448–479). No polynomial moment is omitted here.
- Smallest repair: none required for this step.

### ARITH-003 — Polynomial-part rank is a fraction-field bound

- Severity: none identified; this is the central rank check.
- Evidence: lines 497–518 correctly retain the potentially singular moment `mu_d` in the range `d>K/2`. The degree argument makes every polynomial of degree at most `d` in the space `deg<K` radical, giving rank at most `max(0,K−d−1)` over the full fraction field, not merely in the special fiber.
- An independent explicit calculation strengthens this to equality. Write `lambda=(−1)^K z^{A_K}` and let `h_s=h_s(z,z²,…,z^K)`, with `h_s=0` for `s<0`. In the monomial basis,

  `B_d(x^i,x^j) = lambda h_{i+j−K−d}`.

  The rows/columns `i≤d` vanish. For `d≤K−2`, the remaining block on `x^{d+1},…,x^{K−1}` has size `r=K−d−1`; its reversed-column matrix is triangular with nonzero diagonal `lambda`. Thus its determinant is `±lambda^r`, proving `rank B_d=r`. For `d≥K−1` the whole form is zero.
- Nonnegative row/column powers preserve integrality and, over the ramified Laurent fraction field, preserve rank. Therefore the representation `A+tau^{-1}B` has an integral `B` of rank at most `r`; every column-expansion term with more than `r` columns from `B` vanishes exactly (520–535). A rank assertion only modulo `tau` would not justify this argument, but the manuscript does not make that weaker assertion.
- Smallest repair: none required. The displayed explicit formula could optionally be added to make the rank claim easier to audit.

### ARITH-004 — Stronger appendix's weights `(2,0)`

- Severity: none identified.
- Evidence: lines 819–845 use `G_1=V_a(x)(x−z^{a+d})` for `1≤a≤t=K−d<d`. Any proper-part entry involving `G_1` has identically zero upper-node residue. At the lower node, its one or two factors `z^a−z^{a+d}` cancel the unique vanishing factor of `F'(z^a)`; the lower moment `X−S_a` is analytic because `a<d`. Hence entries `(0,1),(1,0),(1,1)` are analytic, while `(0,0)` has pole order at most four. The basis replacement has triangular determinant one.
- Weights `(2,0)` clear that block at determinant cost four. There are `t` such blocks; the singleton `a=d` costs three and the remaining singletons cost zero. The same polynomial-rank argument adds at most `max(0,t−1)`, yielding `4t+3+max(0,t−1) ≤ 5t+3` (847–859). In particular, zero weights do not invalidate the polynomial-part argument: its singularity is retained separately as `tau^{-1}B`.
- Smallest repair: none required for this step.

### ARITH-005 — Localization really gives integer coefficients

- Severity: none identified.
- Evidence: lines 542–554 assert membership in `Z[z,z^{-1},(z^n−1)^{-1}:1≤n≤K]`. This follows without dividing by rational constants: polynomial division by `D` only inverts its monomial leading coefficient; partial fractions only invert products of differences `z^a−z^b`; polynomial moments use `j≤K−2`; and `S_a` uses indices at most `K`. All nonmonomial denominators therefore factor into the monic `Phi_d`, `d≤K`.
- The coefficientwise local orders at primitive roots bound the exponent of each irreducible cyclotomic denominator. Clearing these exponents leaves a Laurent polynomial with integer coefficients: monic division in `Z[z]` supplies the needed integrality, rather than merely membership in `Q[z,z^{-1}]`. No rational constant denominator can be concealed by the local complex calculation because none occurs in the starting localization.
- At `z=p`, the result lies in `Z[1/p][X]`. Combining integrality away from `p` with ARITH-001 at every prime dividing `p` proves `C_K p^{-e_K}Delta_K ∈ Z[X]`, and exactly the same argument applies to `C_K^{str}` (614–626, 858–859). Positivity and coprimality of the specialized cyclotomic product follow from `p≥2` and `Phi_d(0)=±1`.
- Smallest repair: none required for this step.

### ARITH-006 — Constants and asymptotic bookkeeping

- Severity: none identified.
- Evidence: using the three totient sums at lines 562–577, the low-order contributions, in units of `K³/π²`, are `3/4 + 3/2 + 17/64 = 161/64`. For high-order exponents `a(K−d)+3`, the cubic contribution is

  `a[3(1−1/4)−2(1−1/8)] = a/2`.

  Thus the conservative sum is `(161+224)/64=385/64`, and the stronger sum is `(161+160)/64=321/64` (579–611, 861–866). Ceilings, the constant three, and the floor at `K/2` have at most quadratic cost. The stated totient error terms give `O(K² log K)`.
- The product formula gives `log Phi_d(p)=phi(d)log p+O_p(1)` uniformly in `d`, since the absolute sum over all positive divisor candidates converges. Also `sum c_{K,d}=O(K² log K)`, so the accumulated specialization error has the claimed size. Finally, `p^{-e_K}` contributes `−(1/2)(log p)K³+O_p(K)`. Conditional on the separately stated analytic exponent `−(1/9)(log p)K³`, the appendix's final exponent is exactly `−(11/18−321/(64π²))(log p)K³+O_p(K² log K)`.
- Smallest repair: none required for this step.

## Limits

This review establishes no independent finding about the real determinant bound, the Cauchy-transform nonvanishing proof, novelty, citations, or Lean artifacts. It does not infer the theorem from finite examples. The arithmetic reasoning above is an all-`K` inspection of the cited manuscript, and its scoped result is that the claimed integer-polynomial construction and the `321/(64π²)` denominator-growth estimate are supported by the supplied arithmetic arguments.
