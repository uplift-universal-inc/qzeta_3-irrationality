# Independent arithmetic audit of the q-Hermite determinant

**Verdict: PASS for the full coefficient content theorem and the stated local nonvanishing theorem.**

Audited source: `work/valuation/PROOF.md`, against the exact family in `source/zeta7-port/qhankel.py` with `s=3, N=0, h=K`. This audit does not certify the unrelated denominator-growth bound or assemble an irrationality theorem. No counterexample to the arithmetic statements was found.

## 1. Definitions and exact local moment expansion

Let (p\ge2) be any integer, (K\ge1), (r_a=p^a),

\[
A=K(K+1)/2,\qquad E=K(K^2-1)/2,\qquad
F(x)=\prod_{a=1}^K(x-r_a).
\]

The polynomial family in the engine is exactly

\[
\Delta_K(X)=(-1)^{K^2}p^{AK}\det[M_{i+j}(X)]_{0\le i,j<K},
\quad M_k(X)=L_X(x^k/F(x)),
\]

where (L_X(x^j)=j^2/(p^j-1)) for (j\ge1), (L_X(1)=0), and

\[
L_X((1-x/p^a)^{-1})=X-S_a,
\quad S_a=\sum_{n=1}^a\frac{p^n(p^n+1)}{(p^n-1)^3}.
\]

Fix a prime \(\ell\mid p\), and write \(r=v_\ell(p)\). Define

\[
g(y)=\frac{y(1+y)}{(1-y)^3},\quad
Z=\sum_{n\ge1}g(p^n),\quad
H(t)=\sum_{j\ge1}\frac{j^2p^j}{1-p^j}t^j.
\]

These are convergent local series at the required arguments. Expanding each geometric derivative gives

\[
H(p^a)=\sum_{n\ge1}g(p^{n+a}),\qquad
S_a=-Z+H(p^a).
\]

The sign is correct: the denominator in (g(p^n)) is ((1-p^n)^3), so (S_a=-\sum_{n\le a}g(p^n)). Also (v_\ell(Z)=r), since the first summand has valuation (r) and every later summand has valuation at least (2r).

Let (h_t=h_t(p,p^2,\ldots,p^K)), with (h_0=1) and (h_t=0) for (t<0). The integer coefficients of (h_t) and the node valuations give (v_\ell(h_t)\ge rt). Polynomial division and the divided-difference identities give, with (U=X+Z),

\[
M_0(X)=U/F(0)+R_0,\qquad
M_k(X)=-U h_{k-K}+R_k\quad(k\ge1),
\]

\[
R_k=\sum_{j\ge1}\frac{j^2p^j}{1-p^j}h_{k+j-K}
    +\sum_{j=1}^{k-K}\frac{j^2}{p^j-1}h_{k-K-j}.
\]

The second sum is empty when its upper index is less than 1. The (k=0) identity uses
\(\sum_a1/(r_aF'(r_a))=-1/F(0)\); no missing polynomial moment occurs because (L_X(1)=0).

All infinite-sum interchanges are legitimate: the divided difference is a finite sum, and the terms in each resulting series have valuations tending to infinity.

The decisive bounds follow without cancellation assumptions:

\[
R_k\in\mathbb Z_\ell,\quad
v_\ell(R_k)\ge r(K-k)\quad(0\le k<K),
\]

\[
v_\ell(R_{K-1})=r,\quad v_\ell(R_K)\ge2r,\quad
v_\ell(R_{K+1})=0.
\]

For the first equality the (j=1) series term has valuation (r), while all (j\ge2) terms have valuation at least (3r). For the last equality the polynomial part is (1/(p-1)), a local unit, while the remaining series has positive valuation.

## 2. Full polynomial content, including polynomial-moment corrections

Set (T=[M_{i+j}(X)]), and obtain (T') by multiplying row 0 by (p^A). Every coefficient of every entry of (T') belongs to \(\mathbb Z_\ell\). Indeed, the only possible local denominator in (T) occurs in (M_0), and (F(0)=(-1)^Kp^A). Thus

\[
\Delta_K/p^E=(-1)^{K^2}\det T'\in\mathbb Z_\ell[X].
\]

The coefficient-of-(X) matrix for (T) has only (1/F(0)) in row and column 0; its remaining block has anti-diagonal entries (-1), with zeros on the side (i+j<K). Directly accounting for the column reversal gives

\[
[X^K]\Delta_K(X)=(-1)^{K(K-1)/2}p^E.
\]

The proof therefore controls the entire determinant, not just its leading pure-pole term.

As \(\ell\mid p\) was arbitrary, every reduced coefficient denominator is coprime to (p), and every reduced numerator is divisible by (p^E). The displayed leading coefficient shows that the gcd of these reduced numerators is **exactly** (p^E).

If \(l_K\) is the lcm of the reduced coefficient denominators, then

\[
P_K(X)=l_K\Delta_K(X)/p^E
\]

is primitive integral, up to sign. To justify primitivity explicitly: for a prime dividing (l_K), a coefficient realizing the maximal denominator valuation becomes a unit after multiplication by (l_K); for a prime not dividing (l_Kp), the normalized leading coefficient is a unit. Primes dividing (p) also see that leading coefficient as a unit because (l_K\) is coprime to (p).

Reduction of (T') modulo \(\ell\) gives one nonzero entry, ((-1)^KX), in row 0. In the lower block, entries with (i+j<K) vanish and entries with (i+j=K) equal (-X). Consequently

\[
\Delta_K(X)/p^E\equiv(-1)^{K(K-1)/2}X^K\pmod\ell.
\]

## 3. Nonvanishing audit

The stronger conclusion in the audited note is correct: for each fixed (X\in\mathbb Q_\ell), infinitely many (K) satisfy \(\Delta_K(X)\ne0\).

If (v_\ell(X)\le0), the leading-monomial reduction proves nonvanishing for every (K).

If (U=X+Z=0), reverse all columns of (T). The entries become (R_{K-1+i-j}). Add (2r(i-j)/3) to each entry valuation. The diagonal then has weighted valuation exactly (r), and every off-diagonal entry has strictly larger weighted valuation. Since these added weights sum to zero in each permutation product, the identity is the unique least-valuation determinant term. Hence

\[
v_\ell(\det T)=rK,\qquad
v_\ell((\Delta_K/p^E)(-Z))=r(A+K).
\]

This includes (K=1) and avoids any assumption about the arithmetic nature of the local constant (Z).

Otherwise write (t=v_\ell(U)\ge1). For odd (K), set (n=K-1) and reverse the columns of the lower (n\times n) block. Its entries are (M_{K+i-j}). Adding (r(i-j)/2) to each valuation yields:

- if (t<r/2), a unique diagonal minimum and determinant valuation (nt);
- if (t>r/2), equality only on the two adjacent diagonals; because (n) is even, the unique admissible permutation is ((1\ 2)(3\ 4)\cdots(n-1\ n)), giving valuation (nr/2);
- if (t=r/2), a constant tridiagonal reduction after scaling, whose determinant obeys (D_n=-uD_{n-1}+cD_{n-2}), with (c\ne0) in the residue field.

For the last case, the invertible transition matrix has finite order (T_0) over the finite field, so (D_{2mT_0}=1). This supplies infinitely many even (n) with the required finite valuation. The conjugation can be written unambiguously as (DBD^{-1}/\ell^t), where (D=\operatorname{diag}(\ell^{it})); this is an exposition clarification, not a correction to the result.

Finally, in (T'), the ((0,0)) entry has valuation (t) for all sufficiently large (K). Terms fixing row/column 0 have valuation (t+O(K)), whereas terms not fixing 0 have valuation at least (rA\). Strict separation proves nonvanishing along the indicated infinite subsequence. For (p=2), (r=1) and integer (t\ge1), only the adjacent-pair case is needed; thus every sufficiently large odd (K) works when (U\ne0).

## 4. Independent finite checks

`check.py` tests 100 determinants: (K=1,\ldots,10) for

\[
p=2,3,4,6,8,9,12,16,25,36.
\]

For every determinant it checks the exact leading coefficient and numerator gcd, local leading-monomial reduction at **every** prime divisor of (p), direct rational matrix determinants at (X=0,1,2/3), all local moment expansions to a rigorously bounded local truncation error, and the exceptional-value valuation (r(A+K)). All checks pass; the machine-readable record is `checks.json`.

These computations are finite corroboration. The general proof is the local expansion and determinant valuation argument above.

## 5. Application boundary

Under a hypothetical rational value (\alpha=a/b\), this theorem ensures that (P_K(\alpha)\ne0) infinitely often, and hence \(|P_K(\alpha)|\ge b^{-K}\) there. A separately proved upper bound decaying like \(\exp(-cK^3)\), with (c>0), would contradict this. This audit supplies the content and nonvanishing inputs only; it does not establish that final real bound.
