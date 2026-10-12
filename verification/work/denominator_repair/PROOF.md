# Repaired all-order cyclotomic denominator estimate

Status: proved, with the omitted polynomial moment included explicitly. This note repairs the false inequality `K-2<d` in `work/denominators/PROOF.md`. It is only a denominator theorem; the other inputs to any irrationality argument require their own proofs.

## Statement

Use the unweighted, size-K construction of `source/zeta7-port/qhankel.py`, with s=3. For an indeterminate z, put

\[
 D(x)=\prod_{a=1}^K(1-z^{-a}x),\qquad
 Q(x)=\prod_{a=1}^K(x-z^a),
\]
\[
 L(1)=0,\quad L(x^j)=\frac{j^2}{z^j-1}\ (j\ge1),\quad
 L((1-z^{-a}x)^{-1})=X-S_a,
\]
\[
 S_a=\sum_{n=1}^a\frac{z^n(z^n+1)}{(z^n-1)^3},\qquad
 \Delta_K(X)=\det\bigl[L(x^{i+j}/D(x))\bigr]_{0\le i,j<K}.
\]

For d<=K/2, let r=floor(K/d), c=ceil(r/2), and set

\[
 E_d=(c+2)K+(1-c^2)d.
\]

For K/2<d<=K, let t=K-d and set

\[
 E_d=6t+3+\max(0,t-1).
\]

Then every E_d is a nonnegative integer and

\[
 \left(\prod_{d=1}^K\Phi_d(z)^{E_d}\right)\Delta_K(X)
 \in\mathbb Z[z,z^{-1}][X].
\]

For any fixed integer p>=2, define D_K(p)=product Phi_d(p)^{E_d}. It is coprime to p. The coefficient denominators of Delta_K at z=p, after deleting their p-primary parts, divide D_K(p). Moreover,

\[
 \log D_K(p)=\left(\frac18+\frac{19}{4\pi^2}+o(1)\right)
                  (\log p)K^3.
\]

The leading constant is 0.6062756223011044, below 11/18 by 0.0048354888100067.

A simpler bound, not requiring the infinite interval summation, is

\[
 \log D_K(p)\le\frac{385}{64\pi^2}(\log p)K^3+O_p(K^2\log K),
\]

whose leading constant 0.6095102453484382 also lies strictly below 11/18.

## 1. Local cluster basis

Fix a primitive d-th root of unity zeta and write tau=z-zeta. All valuations below are tau-adic, over C((tau))(X). Partition a=1,...,K into residue clusters A_r modulo d, with sizes m_r, and write

\[
 Q_r(x)=\prod_{a\in A_r}(x-z^a),\qquad
 F_{r,j}(x)=\frac{Q(x)}{Q_r(x)}(x-\zeta^r)^j,
 \quad 0\le j<m_r.
\]

These form an integral basis with unit change-of-basis determinant. At tau=0, each cluster's elements vanish to full multiplicity at every other cluster and form a basis modulo its own factor (x-zeta^r)^{m_r}. The Chinese remainder theorem proves the assertion.

Divide each F_{r,j}F_{s,k} by D and then take simple partial fractions. The polynomial part has degree at most K-2 and coefficients integral at tau=0. Its image under L has at worst a simple pole, since the polynomial moments are j^2/(z^j-1).

For r!=s the pole part vanishes identically: Q divides F_{r,j}F_{s,k}. Within a cluster of size m, the simple-pole coefficient at x=z^a has valuation at least j+k-(m-1), because its numerator contributes (z^a-zeta^r)^{j+k} and Q'(z^a) has precisely m-1 vanishing factors. Since X-S_a has pole order at most three, the resulting pole-part entry has valuation at least j+k-m-2.

## 2. General cluster weights

For each cluster of size m use nonnegative half-integer weights

\[
 w_j=\max\{1/2,(m+2)/2-j\},\quad 0\le j<m.
\]

Scaling row and column j by tau^{w_j} makes both the polynomial and pole parts integral. Work over C[[sqrt(tau)]] if necessary. Hence the determinant's pole order is at most

\[
 \sum_r F(m_r),\qquad
 F(m)=\sum_{j=0}^{m-1}\max\{1,m+2-2j\}.
\]

Explicitly,

\[
 F(m)=\begin{cases}m^2/4+2m+1,&m\text{ even},\\
                   m^2/4+2m+3/4,&m\text{ odd}.
       \end{cases}
\]

If r=floor(K/d), precisely K-rd clusters have size r+1 and the others have size r. Let c=ceil(r/2). Direct subtraction gives F(r+1)-F(r)=c+2 and F(r)-r(c+2)=1-c^2. Therefore

\[
 \sum_r F(m_r)=(c+2)K+(1-c^2)d=E_d,
\]

proving the asserted local bound for d<=K/2.

For the simpler global estimate, write f={K/d}. The exact variance identity is

\[
 \sum_r m_r^2=K^2/d+d f(1-f)\le K^2/d+d/4.
\]

Consequently,

\[
 E_d\le K^2/(4d)+2K+17d/16.
\]

## 3. Repair for d>K/2: the missed moment has small rank

Put t=K-d. There are t double clusters, with residues 1,...,t, and d-t singleton clusters. Use weights (2,1) on each double cluster. On the singleton a=d use weight 3/2; on all remaining singletons use weight zero. These weights make every pole-part entry integral and have total determinant cost 6t+3.

The polynomial quotient has degree <=K-2<2d. Its only possibly singular nonconstant moment is j=d. This moment is present when t>=2, and must not be omitted.

For polynomials f,g of degree <K, define the bilinear form

\[
 B_d(f,g)=[x^d]\,(fg/D)_+,
\]

where the subscript + is polynomial quotient. If deg(f)<=d, then deg(fg)<=K+d-1; hence the quotient has degree <d and B_d(f,g)=0. Thus B_d has rank at most

\[
 r_d=\max(0,K-d-1)=\max(0,t-1).
\]

This is an exact rank bound over C((tau)), and B_d has integral coefficients at tau=0. It remains valid in the cluster basis and after the nonnegative row and column scalings.

After those scalings the full matrix is A+tau^{-1}B, where A and B are integral over C[[sqrt(tau)]] and rank(B)<=r_d. Here B includes the analytic unit tau*d^2/(z^d-1). In the determinant's multilinear expansion, every term selecting more than r_d columns from B vanishes. Every remaining term has valuation at least -r_d. Therefore the determinant's total pole order before scaling is at most

\[
 6t+3+r_d=E_d.
\]

This proves the repaired high-d bound, including d=K (t=0) and d=K-1 (t=1).

## 4. Integral coefficients

The original partial-fraction and polynomial-division formulas put every coefficient in

\[
 \mathbb Z[z,z^{-1},(z^n-1)^{-1}:1\le n\le K].
\]

All inverted factors other than z are monic cyclotomic polynomials. The local bounds above cancel their exponents. Gauss's lemma leaves an element of Z[z,z^{-1}][X]; no rational constant denominators remain. Specializing z=p proves the claimed bound on denominators coprime to p. Since Phi_d(p) is congruent to its constant term +/-1 modulo every prime dividing p, D_K(p) is coprime to p.

## 5. Simple asymptotic bound

Use

\[
 \sum_{d\le M}\varphi(d)/d=6M/\pi^2+O(\log M),\quad
 \sum_{d\le M}\varphi(d)=3M^2/\pi^2+O(M\log M),
\]
\[
 \sum_{d\le M}d\varphi(d)=2M^3/\pi^2+O(M^2\log M).
\]

The low-d upper bound contributes at most 161K^3/(64pi^2)+O(K^2 log K). The high-d formula is 7(K-d)+2 except at d=K, an O(1) modification; its contribution is 7K^3/(2pi^2)+O(K^2 log K). Their sum is 385K^3/(64pi^2)+O(K^2 log K).

Finally,

\[
 \log\Phi_d(p)=\varphi(d)\log p+O_p(1)
\]

uniformly in d: use the cyclotomic product and bound the error by sum_{j>=1}|log(1-p^{-j})|<infinity. Since sum E_d=O(K^2 log K), the error remains O_p(K^2 log K).

## 6. Sharper exact leading constant

On K/(r+1)<d<=K/r, for each fixed r>=2, write A_r=ceil(r/2)+2 and B_r=1-ceil(r/2)^2. The totient sums give the interval's normalized limiting contribution

\[
 \frac1{\pi^2}\left[3A_r\left(\frac1{r^2}-\frac1{(r+1)^2}\right)
 +2B_r\left(\frac1{r^3}-\frac1{(r+1)^3}\right)\right].
\]

Passing to the infinite sum is justified by first fixing R, using these asymptotics for 2<=r<R, and bounding the omitted d<=K/R contribution by O(K^3/R). Indeed E_d<=C K^2/d there and phi(d)<=d.

Abel summation now gives

\[
 \sum_{r\ge2}A_r(r^{-2}-(r+1)^{-2})
 =3/4+\sum_{\substack{r\ge3\\r\ \mathrm{odd}}}r^{-2},
\]
\[
 \sum_{r\ge2}B_r(r^{-3}-(r+1)^{-3})
 =-\sum_{\substack{r\ge3\\r\ \mathrm{odd}}}r^{-2}.
\]

Thus the low-d limiting constant is

\[
 \pi^{-2}\left(9/4+\sum_{r\ge3,\ r\text{ odd}}r^{-2}\right)
 =\frac18+\frac5{4\pi^2}.
\]

Adding 7/(2pi^2) from the high-d range proves the stated constant 1/8+19/(4pi^2).

## Scope

This repairs the denominator step without asserting that its estimated pole orders are sharp. The positive margin against 11/18 is unconditional for this denominator calculation. It is not a proof that any determinant value is nonzero, nor a proof that the other claimed all-order estimates hold.
