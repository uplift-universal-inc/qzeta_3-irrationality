# Full content and arithmetic nonvanishing for the q-Hankel determinant

This note treats `qhankel.py` with `s=3, N=0, h=K`. It proves content and arithmetic nonvanishing for every integer p>=2. The p=2 argument is presented separately first, followed by the extension to general p. It does not prove a denominator-growth estimate or analytic decay.

## Definitions

Put r_a=p^a, A=K(K+1)/2, E=K(K^2-1)/2, and

F(x)=prod_{a=1}^K (x-r_a), D(x)=prod_{a=1}^K(1-x/r_a)=(-1)^K p^{-A}F(x).

The rational linear functional L_X on functions with these simple poles is defined by

- L_X(1)=0;
- L_X(x^j)=mu_j=j^2/(p^j-1) for j>=1;
- L_X(1/(1-x/r_a))=X-S_a,
  S_a=sum_{n=1}^a p^n(p^n+1)/(p^n-1)^3.

Set M_k(X)=L_X(x^k/F(x)), 0<=k<=2K-2. Then

Delta_K(X)=det[L_X(x^{i+j}/D)]_{i,j=0}^{K-1}
          =(-1)^{K^2}p^{AK} det[M_{i+j}(X)].

Write h_t=h_t(r_1,...,r_K) for complete homogeneous symmetric polynomials, with h_0=1 and h_t=0 for t<0. These are integers, and for a prime ell|p, setting r=v_ell(p), we have v_ell(h_t)>=rt for t>=0.

## A convergent local expansion for every moment

Fix a prime ell|p and work in Q_ell. Define

g(y)=y(1+y)/(1-y)^3,
Z=sum_{n>=1} g(p^n),
c_j=j^2 p^j/(1-p^j),
H(t)=sum_{j>=1}c_j t^j=sum_{n>=1}g(p^n t).

All these series converge at the stated arguments. In particular v_ell(c_j)>=rj and v_ell(Z)=r: the first summand has valuation r and all later summands have valuation >=2r.

The identity g(y^{-1})=-g(y) gives

S_a=-Z+H(r_a).

For each k>=0 divide x^k by F, and use its simple pole decomposition. Because

L_X(1/(x-r_a))=-(X-S_a)/r_a,

we obtain

M_k(X)=L_X(Q_k)-sum_a r_a^{k-1}(X-S_a)/F'(r_a),

where Q_k=0 for k<K, and Q_k=sum_{j=0}^{k-K}h_{k-K-j}x^j otherwise.

The standard divided-difference identities are

sum_a r_a^m/F'(r_a)=h_{m-K+1} for m>=0,
sum_a 1/(r_a F'(r_a))=-1/F(0).

Consequently, with U=X+Z and

R_k=sum_{j>=1} c_j h_{k+j-K}
    +sum_{j=1}^{k-K} mu_j h_{k-K-j},

where the second sum is empty for k<=K, the exact convergent identities are

M_0(X)=U/F(0)+R_0,
M_k(X)=-U h_{k-K}+R_k  (k>=1).

These hold also for k=0 because H(t)/t is analytic: all powers appearing in its divided difference have nonnegative exponents. Interchanging the finite divided difference and the convergent sum is legitimate.

Useful bounds valid for every ell|p:

- R_k is ell-integral for every k>=0;
- v_ell(R_k)>=r(K-k) for 0<=k<K;
- v_ell(R_{K-1})=r (the j=1 term is c_1, and all other terms have valuation >=3r);
- v_ell(R_K)>=2r;
- R_{K+1} is an ell-adic unit (its polynomial part is mu_1, and its infinite-series part has positive valuation).

For the exact R_{K-1} assertion, the j>=2 term c_j h_{j-1} has valuation at least r(2j-1)>=3r.

## Theorem 1: the full content gain is exact

Let T_K(X)=[M_{i+j}(X)]. For X an indeterminate, all entries other than (0,0) have coefficients in Z_ell. The (0,0) entry is U/F(0)+R_0, where v_ell(F(0))=rA. Thus multiplying row 0 by p^A makes the whole matrix integral over Z_ell[X]. Hence

v_ell(each coefficient of Delta_K)>=r(AK-A)=rE.

This handles the full polynomial-moment correction, not just the pure-pole term.

The coefficient B of X in T has B_00=1/F(0), B_{ij}=-h_{i+j-K} when i+j>=1, and h_negative=0. The row/column 0 entries outside (0,0) vanish. The lower (K-1)-square block is anti-triangular, with anti-diagonal entries -1. Therefore

coefficient of X^K in Delta_K=(-1)^{K(K-1)/2} p^E.

In particular equality holds in the coefficient-valuation bound for every prime divisor of p. Since the leading coefficient is the signed integer p^E, no other prime can divide the gcd of all reduced coefficient numerators. We conclude:

1. Every reduced coefficient denominator of Delta_K is coprime to p.
2. The gcd of all reduced coefficient numerators is exactly p^E.
3. If l_K is their denominator lcm, the primitive integral polynomial is P_K=l_K Delta_K/p^E, up to sign.

Moreover Delta_K/p^E is congruent to its signed leading monomial X^K modulo each prime ell|p. To see this, multiply row 0 of T by p^A. Its reduction has only the (0,0) entry, a unit times X. In the lower block, for i+j<K the entry is zero modulo ell; for i+j=K it is -X modulo ell; entries beyond this anti-diagonal may be nonzero, but do not change the anti-triangular determinant.

## Theorem 2: arithmetic nonvanishing for p=2

For every fixed X in Q_2, Delta_K(X) is nonzero for infinitely many positive integers K. In fact, if X != -Z, it is nonzero for all sufficiently large odd K; if X=-Z, it is nonzero for every K.

Case 1: v_2(X)<=0. The integral monic-up-to-sign polynomial Delta_K/p^E reduces to its leading monomial modulo 2. If v_2(X)=0 its value is a unit. If v_2(X)<0, its leading term has uniquely least valuation. Thus Delta_K(X) !=0 for every K.

Case 2: v_2(X)>=1 and U=X+Z !=0. Put t=v_2(U)>=1. Let K be odd, K>=3, and n=K-1. Consider the lower n-square block B=[M_{i+j}]_{i,j=1}^{K-1}; reverse its columns, giving entries M_{K+i-j}, 1<=i,j<=n. Write d=i-j.

- d<0: v_2(M_{K+d})>=-d, with equality 1 for d=-1;
- d=0: v_2(M_K)>=1;
- d=1: v_2(M_{K+1})=0;
- d>=2: v_2(M_{K+d})>=0.

For d=1 the polynomial term mu_1 is a unit, while -U h_1 and the convergent series are even. Attach the weight d/2 to every entry valuation. This adds zero to the valuation of each permutation product, because sum_i(i-sigma(i))=0.

Every weighted entry valuation is at least 1/2. Equality occurs only at d=-1 or d=1; all other entries have weighted valuation at least 1. Therefore the minimum-weight permutation must pair adjacent indices. On an even line of length n there is exactly one permutation with |i-sigma(i)|=1 for every i: (1 2)(3 4)...(n-1 n). Thus

v_2(det B)=n/2.

Now multiply row 0 of T by 2^A, obtaining T'. The (0,0) entry is a unit times U plus 2^A R_0. Since v_2(R_0)>=K, it has valuation t whenever A+K>t. Every entry in row 0 outside column 0 is divisible by 2^A, and all entries in other rows are integral. Thus the sum of permutation terms fixing 0 has valuation t+n/2; all other permutation terms have valuation at least A. If

A>t+(K-1)/2,

these two valuations are strictly separated and det T' !=0. The inequality holds for all sufficiently large odd K.

Case 3: X=-Z, so U=0. The matrix T now consists of R_{i+j}. Reverse all K columns. Its (i,j) entry is R_{K-1+i-j}, with 0<=i,j<K; write d=i-j. The bounds above imply

- d=0: valuation exactly 1;
- d<=-1: valuation at least 1-d;
- d=1: valuation at least 2;
- d>=2: valuation at least 0.

Attach weight 2d/3 to these valuations. The diagonal has weight exactly 1. Every off-diagonal weight is strictly greater than 1: for d<=-1 it is at least 1-d/3>1; for d=1 it is at least 8/3; for d>=2 it is at least 2d/3>=4/3. Since weights again sum to zero on permutation products, the identity permutation is the unique term of least valuation. Therefore

v_2(det T)=K,

which proves nonvanishing for every K. Equivalently,

v_2((Delta_K/2^E)(-Z))=A+K.

The cases exhaust Q_2 and in particular every rational X. This closes the arithmetic nonvanishing gap, conditional on no other analytic or denominator estimates.

## Theorem 3: extension of nonvanishing to every integer p>=2

Fix any prime ell|p and set r=v_ell(p)>=1. Define Z and U in Q_ell as above. For every fixed X in Q_ell, Delta_K(X) is nonzero for infinitely many K.

The case v_ell(X)<=0 follows from the leading-monomial reduction exactly as in Theorem 2. If U=0, the full reversed matrix proof is unchanged after multiplying all valuation bounds and weights by r: its determinant has valuation rK. Thus suppose v_ell(X)>=1 and U!=0, and put t=v_ell(U)>=1.

Take K odd and n=K-1 even. In the reversed lower block, whose entries are M_{K+d} for d=i-j, we have:

- d<=-1: valuation at least -rd, exactly r when d=-1;
- d=0: M_K=-U+R_K, with v_ell(R_K)>=2r;
- d=1: valuation zero;
- d>=2: valuation at least zero.

Attach weight rd/2, which sums to zero on all permutation products.

If t<r/2, the diagonal entry has valuation t, and every off-diagonal weighted valuation is at least r/2>t. Thus v_ell(det B)=nt.

If t>r/2, the diagonal has valuation at least min(t,2r)>r/2. Exactly the two first off-diagonals attain weighted valuation r/2. The unique adjacent-pair permutation gives v_ell(det B)=nr/2.

If t=r/2, necessarily r is even. Set u=U/ell^t mod ell and c=p/ell^r mod ell, both nonzero. Conjugate the reversed lower block by diag(ell^{it}) and divide every entry by ell^t. It is now integral and its reduction is the constant tridiagonal matrix with diagonal -u, superdiagonal c and subdiagonal -1. Indeed all further off-diagonals have adjusted valuation strictly greater than t before division, while M_K=-U+terms of valuation >=2r. Its n-square determinant D_n satisfies

D_0=1, D_1=-u, D_n=-u D_{n-1}+c D_{n-2} in F_ell.

The transition matrix [[-u,c],[1,0]] is invertible over the finite field. Starting from (D_0,D_{-1})=(1,0), its orbit is periodic; if T is a period, D_{2mT}=1 for every m>=1. Hence infinitely many even n have D_n nonzero, and for those n, v_ell(det B)=nt.

Finally multiply row 0 of T by p^A. The (0,0) entry has valuation t once r(A+K)>t. Every other entry in that row has valuation at least rA, and all remaining rows are integral. Thus the terms fixing 0 have valuation t+v_ell(det B), whereas all other terms have valuation at least rA. In each of the three cases, the former is O(K) and the latter is quadratic in K. Along the indicated infinite set of odd K, strict separation therefore proves nonvanishing for all sufficiently large K.

This proof requires neither rationality nor irrationality of the local constant Z. For the application to real irrationality, apply the statement only to a hypothetical fixed rational X, embedded in Q_ell.

## Scope and remaining work

Both the content theorem and p=2 nonvanishing above are proofs for all K or infinite K subsequences, not extrapolations from finite data. The exceptional local constant Z need not be proved irrational: its exact equality case is handled separately. The irrationality theorem for the real q-zeta value still requires a valid denominator-growth bound and a rigorous real smallness bound strong enough to survive normalization.
