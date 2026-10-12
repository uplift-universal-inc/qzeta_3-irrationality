# All-order cyclotomic denominator bound for the unweighted q-Hankel determinant

**Status: complete independent proof of the denominator estimate below.** This does not by itself establish irrationality: the analytic decay, the p-primary common factor, and nonvanishing are separate inputs.

Let `z` be an indeterminate, K>=1, and s=3. Put

\[
Q(x)=\prod_{a=1}^K(x-z^a),\quad D(x)=\prod_{a=1}^K(1-z^{-a}x),
\]

and define the Q(z)[X]-valued functional on polynomials and simple poles by

\[
L(1)=0,\qquad L(x^j)=\frac{j^2}{z^j-1}\ (j\ge1),\qquad
L((1-z^{-a}x)^{-1})=X-S_a,
\]
\[
S_a=\sum_{n=1}^a\frac{z^n(z^n+1)}{(z^n-1)^3}.
\]

Let Delta_K(X)=det[L(x^{i+j}/D(x))]_{0<=i,j<K}. Its coefficients are rational functions of z whose denominators are products of powers of z and cyclotomic polynomials Phi_d(z), d<=K.

## Proposition

For d<=K/2 set

\[
E_d=\left\lceil\frac{K^2}{4d}+2K+\frac{17d}{16}\right\rceil.
\]

For K/2<d<=K set

\[
E_d=5(K-d)+3.
\]

Then

\[
\left(\prod_{d=1}^K\Phi_d(z)^{E_d}\right)\Delta_K(X)
\in\mathbb Z[z,z^{-1}][X].
\]

Consequently, at every integer p>=2, the part of the coefficient denominator coprime to p divides the positive integer

\[
D_K(p)=\prod_{d=1}^K\Phi_d(p)^{E_d},
\]

and, for fixed p,

\[
\log D_K(p)\le\frac{321}{64\pi^2}(\log p)K^3+O_p(K^2\log^2 K).
\]

The leading constant is 0.5081890617061005, which is strictly below 11/18 by 0.10292204940501071. Thus the analytic estimate -K^3 log(p)/9, together with a p-primary common factor of size p^{K(K^2-1)/2}, leaves a positive asymptotic margin.

## Local proof at a primitive d-th root of unity

Fix a primitive d-th root zeta and the valuation v=ord_{z=zeta}. Work over C[[z-zeta]]; this detects precisely the exponent of Phi_d in a rational function over Q(z).

Partition the nodes z^a into residue classes r modulo d. Let

\[
A_r=\{a\in[1,K]:a\equiv r\pmod d\},\quad m_r=|A_r|,
\quad Q_r(x)=\prod_{a\in A_r}(x-z^a).
\]

Use the following K polynomials as a basis of the polynomials of degree <K:

\[
F_{r,j}(x)=\frac{Q(x)}{Q_r(x)}(x-\zeta^r)^j,
\qquad 0\le j<m_r.
\]

The basis change has valuation zero. Indeed, at z=zeta its restriction modulo (x-zeta^r)^{m_r} is multiplication by a unit followed by the standard powers, and at every other cluster it vanishes to the full multiplicity. The Chinese remainder theorem proves independence modulo the uniformizer. Therefore the Gram determinant in this basis has exactly the same local valuation as Delta_K.

For any two basis polynomials, perform polynomial division plus simple partial fractions. The polynomial part has degree <=K-2 and coefficients analytic at zeta: the leading coefficient of D is a unit. Applying L to it gives valuation >=-1, because every j^2/(z^j-1) has at worst a simple pole.

The pole part is block diagonal in r. If r!=t, F_{r,j}F_{t,k}/D is already a polynomial (Q divides its numerator), so its pole part vanishes exactly. If r=t, the coefficient of the pole at x=z^a, a in A_r, has valuation at least

\[
j+k-(m_r-1).
\]

This follows directly by evaluating the numerator at z^a: its two powers (z^a-zeta^r) contribute j+k, while the derivative of Q at z^a has exactly m_r-1 colliding factors. All noncolliding factors are units. Since v(X-S_a)>=-3, the pole contribution has valuation at least

\[
j+k-m_r-2.
\]

For arbitrary d choose the nonnegative half-integer weight

\[
w_{r,j}=\max\{\tfrac12,\tfrac{m_r+2}{2}-j\}.
\]

Multiplying row and column (r,j) by a uniformizer to this power makes every entry integral. One may adjoin a square root of the uniformizer to make this literal; the resulting determinant bound is integral. The polynomial part is integral after scaling because every sum of two weights is >=1. The pole part is integral because

\[
w_{r,j}+w_{r,k}\ge m_r+2-j-k.
\]

Thus

\[
-v(\Delta_K)\le\sum_r F(m_r),\qquad
F(m)=\sum_{j=0}^{m-1}\max\{1,m+2-2j\}.
\]

An elementary summation gives

\[
F(m)=\begin{cases}m^2/4+2m+1,&m\text{ even},\\
m^2/4+2m+3/4,&m\text{ odd},\end{cases}
\]

including F(1)=3. Hence F(m)<=m^2/4+2m+1. Write K=td+r with 0<=r<d. There are r clusters of size t+1 and d-r of size t, so

\[
\sum_r m_r^2=K^2/d+r(1-r/d)\le K^2/d+d/4.
\]

Thus the determinant pole order is at most

\[
K^2/(4d)+2K+17d/16,
\]

which proves the bound E_d for d<=K/2 (in fact this particular bound holds at all d).

## Improvement when d>K/2

All clusters have size one or two, and there are exactly r=K-d clusters of size two.

First ignore the polynomial-moment term. In each size-two cluster {a,a+d}, with a<d, replace the previous basis by

\[
F_0=Q/Q_r,\qquad F_1=(Q/Q_r)(x-z^{a+d}).
\]

The basis change remains a local unit, since its reduction is the same confluent basis. The simple-pole coefficient at the higher node z^{a+d} vanishes identically for entries involving F_1. At the lower node z^a, the factor z^a-z^{a+d} has valuation one and cancels the single colliding factor in the partial-fraction denominator. Since S_a is analytic for a<d, the pole parts of F_0 F_1/D and F_1^2/D are analytic. Only the F_0^2/D entry can have a pole, of order at most four.

Therefore weights (2,0) clear the pole part for each size-two cluster, at determinant cost 4. For a singleton a<d, S_a is analytic and weight zero suffices. The only remaining singleton is a=d; it contributes at most a pole of order three, so weight 3/2 suffices. Cross-cluster pole terms are zero. Thus these nonnegative weights make the pole part integral at total determinant cost 4r+3.

The polynomial-moment term has degree at most K-2. Since 2d>K, its only possibly singular moment is mu_d=d^2/(z^d-1). Write this contribution as mu_d H_d(z). In the original monomial basis, the matrix H_d has entries zero unless

\[
i+j\ge K+d.
\]

Indeed, the quotient on dividing x^{i+j} by D has degree i+j-K. This support condition means its first d+1 rows vanish, hence

\[
\operatorname{rank}H_d\le\max\{0,K-d-1\}=\max\{0,r-1\}.
\]

The basis transformation preserves this rank. The subsequent row and column scalings have nonnegative weights, so the scaled coefficient matrix is analytic and has the same rank bound. Consequently the fully scaled Gram matrix is of the form

\[
A(t)+t^{-1}C(t),\qquad t=z-\zeta,
\]

with A and C analytic over the possibly ramified local ring and rank(C)<=max(0,r-1). Its determinant has valuation at least -max(0,r-1): expand by minors, noting that every minor of C of larger order vanishes. This rank argument concerns C(t) over the fraction field, not just its reduction modulo t.

Including this polynomial-moment loss gives

\[
-v(\Delta_K)\le4r+3+\max\{0,r-1\}\le5r+3.
\]

This proves the stated high-d bound. The allowance for the polynomial moment is essential: the assertion K-2<d does not follow from d>K/2.

## Returning to integer polynomials

The displayed initial formulas show that every coefficient of Delta_K belongs to the localization of Z[z] obtained by inverting z and the monic polynomials z^n-1, n<=K. The local bounds cancel every cyclotomic denominator. Gauss's lemma then yields an element of Z[z,z^{-1}][X]; no unaccounted constant denominators can appear. This proves the divisibility statement.

## Asymptotics

Use the elementary totient sums

\[
\sum_{d\le M}\frac{\varphi(d)}d=\frac6{\pi^2}M+O(\log M),\quad
\sum_{d\le M}\varphi(d)=\frac3{\pi^2}M^2+O(M\log M),
\]
\[
\sum_{d\le M}d\varphi(d)=\frac2{\pi^2}M^3+O(M^2\log M).
\]

The contribution d<=K/2 is at most

\[
\frac{161}{64\pi^2}K^3+O(K^2\log K),
\]

and that from K/2<d<=K is

\[
\frac5{2\pi^2}K^3+O(K^2\log K).
\]

Therefore sum E_d phi(d)<=321 K^3/(64 pi^2)+O(K^2 log K).
Finally log Phi_d(p)=phi(d) log p+O_p(tau(d)); summing the errors against E_d=O(K^2/d+K) gives O_p(K^2 log^2 K).

## Scope and checks

No finite computation or guessed pole pattern is needed in this proof. An exact finite check of ordinary coefficient denominators is supplied separately. The sharper observed local orders near 3K and 5(K-d)+2 are deliberately not used.

## General weight s (arithmetic statement only)

The same proof applies to every integer s>=1, with polynomial moments j^{s-1}/(z^j-1) and pure-tail pole values X-S_{s,a}, because S_{s,a} has poles of order at most s. For s=1 use the regularized functional with L(1)=0, as in the supplied program.

The general low-d weights are

\[
w_{r,j}=\max\{1/2,(m_r+s-1)/2-j\}.
\]

Their total doubled weight is bounded by

\[
F_s(m)=\sum_{j=0}^{m-1}\max\{1,m+s-1-2j\}
\le m+(m+s-1)^2/4.
\]

Thus admissible integer bounds are

\[
E_{s,d}=\left\lceil K^2/(4d)+(s+1)K/2+
\left(1/16+(s-1)^2/4\right)d\right\rceil
\quad(d\le K/2),
\]
\[
E_{s,d}=(s+2)(K-d)+s\quad(d>K/2).
\]

For the high-d bound use the same moving-node basis, with weight (s+1)/2 on F_0 and zero on F_1; the polynomial moment correction still has rank at most max(0,K-d-1).

For fixed s and p this gives

\[
\log D_{s,K}(p)\le
\frac{4s^2+48s+141}{64\pi^2}(\log p)K^3
+O_{s,p}(K^2\log^2 K).
\]

This is an all-K denominator theorem, not an irrationality assertion for all s. Separate decay and nonvanishing estimates are necessary for each weight. In particular this bound becomes too expensive at s=4 for the proposed determinant budget.
