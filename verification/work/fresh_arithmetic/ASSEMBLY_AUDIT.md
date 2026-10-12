# Adversarial full-chain audit after the denominator repair

**Verdict: PASS.** As mathematical arguments, the repaired denominator estimate, full content lemma, analytic estimate, and nonvanishing argument do assemble into a proof that

\[
\sum_{n\ge1}\frac{n^2}{p^n-1}\notin\mathbb Q
\qquad\text{for each integer }p\ge2.
\]

I found no remaining gap in the stated chain. This is an independent internal audit, not a claim of external peer review or literature acceptance. The proof must use the repaired rank argument; the old assertion (d>K/2\Rightarrow K-2<d) is false and must not remain as a premise.

Reviewed inputs: `work/denominator_independent/PROOF.md`, `work/denominator_repair/PROOF.md`, `work/analytic/ANALYTIC_BOUND.md`, `work/normality.md`, and `work/valuation/PROOF.md`. My separate rederivation of the last input is in `AUDIT.md` in this directory.

The reviewed versions have these SHA-256 hashes:

| File | SHA-256 |
|---|---|
| `work/denominator_independent/PROOF.md` | `dcc1c3448c173ecbaa463339f0ba48e2cda69b85c85c6385ee9c2f7b0df8d121` |
| `work/denominator_repair/PROOF.md` | `c689a338fba415b982d202b0d0260daf61ba0231b251c5ddf1517e0297dd9220` |
| `work/analytic/ANALYTIC_BOUND.md` | `85fb52d0125ec6c4562b0bb08081a3f4a6baf680530aeb6681933a97dc5c648a` |
| `work/normality.md` | `455ae3804bf4960085e0d4b92ad72d1f7f00f0c9d9f853b6dd3257710f2f94c0` |
| `work/valuation/PROOF.md` | `a1654f2db877ed8cc7109e36e7019a334296c3a9d87b4688a1f88a30e6e1015a` |

## 1. The symbolic family is the correct real determinant

Fix (p\ge2), put (q=1/p), and define

\[
\alpha=\sum_{n\ge1}\frac{n^2}{p^n-1},\qquad
L(f)=\sum_{m\ge1}(x\,d/dx)^2f(q^m).
\]

Every rational function used here is analytic near ([0,q]), and its twice-Euler-differentiated value is (O(x)) near zero. Thus (L) is defined and convergent on the required functions. Direct geometric summation gives

\[
L(1)=0,\quad L(x^j)=\frac{j^2}{p^j-1},\quad
L((1-q^a x)^{-1})=\alpha-S_a,
\]

\[
S_a=\sum_{n=1}^a\frac{p^n(p^n+1)}{(p^n-1)^3}.
\]

In the last identity one can first use positive convergent double sums:

\[
\alpha=\sum_{m\ge1}g(q^m),\qquad
g(y)=\frac{y(1+y)}{(1-y)^3},
\]

and the pole moment is the tail starting at (m=a+1). Hence the formal polynomial determinant \(\Delta_K(X)\) is exactly the real determinant estimated analytically when evaluated at (X=\alpha). No independent or inconsistent meaning of (X) enters the chain.

## 2. The repaired denominator theorem survives the adversarial checks

Before any change of basis, every coefficient of \(\Delta_K(X)\), with (p) replaced by the indeterminate (z), is in

\[
\mathbb Z[z,z^{-1},(z^n-1)^{-1}:1\le n\le K].
\]

Indeed the simple-pole partial fractions use only node differences (z^a-z^b=z^b(z^{a-b}-1)); the polynomial moments have index at most (K-2), and (S_a) uses indices at most (K). There is no rational constant denominator in these formulas.

At a primitive (d)-th root of unity, the cluster basis is invertible over the local ring. This is a valuation assertion, so its determinant need only be a local unit, not exactly 1. The Chinese-remainder argument gives that unit property. The degree of every cluster-basis element is less than (K), so polynomial quotients still have degree at most (K-2).

The local valuation arguments are coefficientwise in (X). Equivalently one may work over the local coefficient ring with (X) an independent indeterminate. They are not estimates obtained only after choosing a special numerical value of (X).

For (d\le K/2), the weights

\[
w_j=\max\{1/2,(m+2)/2-j\}
\]

cover the simple poles from polynomial moments and the pole-part loss (j+k-m-2). The determinant scaling cost for a cluster is

\[
F(m)=\lfloor m^2/4\rfloor+2m+1.
\]

The balanced-cluster variance estimate yields the valid integer exponent

\[
e_d=\left\lceil\frac{K^2}{4d}+2K+\frac{17d}{16}\right\rceil.
\]

For (d>K/2), set (h=K-d). The quotient can contain the (x^d) moment; this is the missed term in the original argument. Its coefficient is the bilinear form

\[
B_d(f,g)=[x^d](fg/D_K)_+.
\]

For every polynomial (f) of degree at most (d) and every (g) of degree less than (K), the quotient has degree at most (d-1). Thus this entire ((d+1))-dimensional subspace belongs to the kernel, giving

\[
\operatorname{rank} B_d\le\max(0,K-d-1)=\max(0,h-1).
\]

This rank bound holds over the full local fraction field before specialization. It therefore persists after the cluster basis change and the row and column scalings; it does not assume that a low-rank residue matrix controls a potentially higher-rank analytic correction.

The weights (2,1) on double clusters, (3/2) on the singleton (a=d), and zero on the other singletons give cost (6h+3). After scaling, write the matrix as (A+\tau^{-1}B), with (A,B) integral and \(\operatorname{rank} B\le\max(0,h-1)\). Multilinearity proves that the polynomial \(\det(A+uB)\) has degree at most that rank in (u), so the extra pole order is at most \(\max(0,h-1)\). The valid convenient high-(d) exponent is consequently

\[
e_d=7(K-d)+3.
\]

Half-integer weights cause no loss: use the ramified local ring with (\sqrt\tau), and keep valuation normalized by (v(\tau)=1).

Local bounds at every primitive root remove each cyclotomic factor from the original rational-function denominator. Since those factors are monic and the starting expression has integer Laurent coefficients, Gauss's lemma gives

\[
C_K(z)\Delta_K(X)\in\mathbb Z[z,z^{-1}][X],
\quad C_K(z)=\prod_{d=1}^K\Phi_d(z)^{e_d}.
\]

The introduction of complex roots of unity in the proof does not introduce rational constants into this original expression. Possible common prime divisors of different integers \(\Phi_d(p)\) after specialization are harmless: the Laurent-polynomial identity is established before specialization.

## 3. Integrality after dividing by the content

Put (E=K(K^2-1)/2), and define

\[
\widetilde P_K(X)=\frac{C_K(p)}{p^E}\Delta_K(X).
\]

For a prime \(\ell\nmid p\), specialization of the Laurent-polynomial identity proves that (C_K(p)\Delta_K) has integral coefficients at \(\ell\), and division by (p^E) preserves integrality there.

For a prime \(\ell\mid p\), the content lemma proves coefficientwise

\[
v_\ell(\Delta_K)\ge v_\ell(p)E.
\]

Furthermore \(C_K(p)\) is a local unit because every \(\Phi_d(p)\) is congruent modulo \(\ell\) to its constant term (\pm1). Thus division by (p^E) again leaves integral coefficients. This proves

\[
\widetilde P_K\in\mathbb Z[X].
\]

Its degree is exactly (K), since the content calculation gives

\[
[X^K]\widetilde P_K=(-1)^{K(K-1)/2}C_K(p)\ne0.
\]

Primitivity is unnecessary for the rationality contradiction. One need not identify the exact denominator lcm or assert that this particular (C_K(p)) is minimal.

## 4. The asymptotic arithmetic budget has a strict positive margin

The standard totient sums follow directly from \(\varphi(n)=n\sum_{d\mid n}\mu(d)/d\):

\[
\sum_{d\le M}\frac{\varphi(d)}d=\frac6{\pi^2}M+O(\log M),\quad
\sum_{d\le M}\varphi(d)=\frac3{\pi^2}M^2+O(M\log M),
\]

\[
\sum_{d\le M}d\varphi(d)=\frac2{\pi^2}M^3+O(M^2\log M).
\]

The low-(d) exponent bound contributes at most (161/(64\pi^2)) to the (K^3) coefficient, and the high-(d) bound contributes (7/(2\pi^2)). Since

\[
\log\Phi_d(p)=\varphi(d)\log p+O_p(1),\qquad
\sum_{d\le K}e_d=O(K^2\log K),
\]

one obtains

\[
\log C_K(p)\le c(\log p)K^3+O_p(K^2\log K),
\qquad c=\frac{385}{64\pi^2}.
\]

The uniform (O_p(1)) for a single cyclotomic logarithm is valid: the error in its Möbius product is bounded by the convergent sum \(\sum_{j\ge1}|\log(1-p^{-j})|\).

The inequality

\[
\delta:=\frac{11}{18}-\frac{385}{64\pi^2}>0
\]

is rigorous, not a floating-point judgment. For example \(\pi>157/50\) gives

\[
\delta>\frac{3487}{3549456}>0.
\]

The sharper constant in the repaired note is not needed for this audit or the proof.

## 5. Analytic bound and nonvanishing rechecked

The analytic proof uses a monic polynomial basis, so its change-of-basis determinant is exactly one. Its triple roots kill all derivatives through order two at earlier lattice nodes. At later nodes the derivative bounds have a genuine summable factor (q^{m-R}). The rational weight and its first two Euler derivatives have bounds uniform in (K). Factoring row and column powers and applying Hadamard gives

\[
|\Delta_K(\alpha)|\le
p^{-J_K}\bigl[12(2K-1)^2\sqrt K\bigr]^K,
\]

\[
J_K=\frac{K^3+3K^2-c_{K\bmod3}}9,
\qquad(c_0,c_1,c_2)=(0,4,2).
\]

In particular the logarithm is at most \(-(\log p)K^3/9+O_p(K^2)\). There is no positivity or sign assumption on the determinant, and no truncated numerical zeta sum is used.

The moving-denominator nonvanishing proof also survives review. Its Cauchy transform has infinitely many genuine third-order poles and is not rational. A singular determinant provides a kernel polynomial and an error (E_n=FQ_n-P_n=O(z^{-1})) vanishing at (p,\ldots,p^n). For consecutive singular sizes, (P_{n+1}Q_n-P_nQ_{n+1}) has degree at most (n-1) and (n) distinct zeros, hence is identically zero. No division at a possibly vanishing interpolation denominator occurs.

An eventual singular tail would therefore give one fixed reduced rational approximant (P/Q). The multipliers (Q_n=U_nQ) would have uniformly bounded degree, because the fixed nonzero error (FQ-P) has finite order at infinity. But the errors at the unbounded exterior nodes force arbitrarily many zeros of (U_n), a contradiction. Hence the actual \(\Delta_K(\alpha)\), and thus \(\widetilde P_K(\alpha)\), are nonzero infinitely often.

Independently, the local arithmetic nonvanishing theorem suffices under the rationality hypothesis itself. The final proof can use either argument; it does not require both, nor a density estimate on the nonzero subsequence.

## 6. Final contradiction

Combining the established bounds gives

\[
\log|\widetilde P_K(\alpha)|
\le-\delta(\log p)K^3+O_p(K^2\log K).
\]

If \(\alpha=a/b\in\mathbb Q\), with (b\ge1), then

\[
b^K\widetilde P_K(a/b)\in\mathbb Z.
\]

For all sufficiently large (K), the displayed analytic bound implies

\[
|b^K\widetilde P_K(a/b)|<1.
\]

On the infinitely many sizes where the value is nonzero, this is impossible for an integer. Therefore \(\alpha\) is irrational.

All parameters are fixed except (K); the implicit constants may depend on (p). This proves the assertion separately for every integer (p\ge2), including prime powers and integers with several prime divisors. No uniform threshold in (p) is required.

## Audit conclusion

The repaired chain is mathematically complete on this review. The delicate points are the exact rank of the omitted polynomial moment, the coefficientwise rather than numerical cyclotomic valuation, and combining denominator clearing with (p)-primary content prime by prime. Each has a valid argument above. Numerical checks support the construction but are not used to close any infinite-(K) step.

## Optional stronger denominator version

I also reviewed the later `work/denominators/PROOF.md`, SHA-256 `67975e86e2b6aa94aeae0574df9d7081a080a739e08b0300c0c7ff9241103cc3`. Its moving-node improvement for (d>K/2) is valid. For a double cluster \(\{a,a+d\}\), use

\[
F_0=Q/Q_r,\qquad F_1=(Q/Q_r)(x-z^{a+d}).
\]

This has the same confluent-basis reduction, hence a unit change-of-basis determinant. In entries containing (F_1), the higher-node residue vanishes identically; at the lower node the numerator factor cancels the one colliding denominator factor, and (S_a) is regular because (a<d). Thus those pole-part entries are integral. Only the (00) entry can have pole order four. Weights (2,0) suffice, costing four per double cluster. The same exact polynomial-moment rank correction adds at most (h-1), giving the valid convenient bound (5h+3).

This changes the leading denominator bound from \(385/(64\pi^2)\) to \(321/(64\pi^2)\), increasing the positive cubic margin to approximately (0.1029220494\log p). The conservative proof above is already complete and does not depend on this stronger version. I audited only the weight-three assertion needed here; the optional final general-weight section is outside this assembly verdict.
