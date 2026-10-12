# Fresh audit of analytic decay and moving-denominator normality

Date: 2026-10-11. This audit independently reconstructs the arguments in
`work/normality.md` and `work/analytic/ANALYTIC_BOUND.md`; it does not use the
earlier audit verdicts as evidence.

## Verdict

Both arguments are valid as stated for every integer `p >= 2`, with `q=1/p`.
They prove:

1. The actual real determinants are nonzero for infinitely many sizes.
2. Their absolute values satisfy the stated all-size bound, with exact
   cubic exponent `-(log p) K^3/9`.

These two results alone do not prove irrationality. The cyclotomic
denominator estimate is a separate input. During this audit, the original
denominator note was found to contain the false implication
`d>K/2 => K-2<d`; that flaw was reported immediately. The revised note has
now been independently audited below and its stronger repaired estimate
also passes.

## 1. The Cauchy transform and its singularities

For `theta=x d/dx`, direct differentiation gives

\[
\theta^2\frac1{z-x}=\frac{x(z+x)}{(z-x)^3}.
\]

Consequently

\[
F(z)=\sum_{m\ge1}\frac{q^m(z+q^m)}{(z-q^m)^3}.
\]

On any compact set avoiding `0,q,q^2,...`, all sufficiently late terms
are bounded by a constant times `q^m`, uniformly in `z`. The finitely many
remaining terms are analytic away from their displayed poles. Thus the
series is locally normally convergent on the asserted domain. Near
`z=q^m`, only the term with this index is singular, and its expansion is

\[
2q^{2m}(z-q^m)^{-3}+q^m(z-q^m)^{-2}.
\]

The coefficient of the third-order pole is nonzero. Therefore `F` has
infinitely many genuine poles and is not rational. At infinity the series
has a convergent expansion beginning with a `z^{-2}` term, so it is
analytic at infinity and `O(z^{-2})`.

## 2. Polynomial identity attached to a singular determinant

Let `D_n(x)=prod_{a=1}^n(1-q^a x)` and let `Q` be any polynomial of degree
at most `n-1`. The numerator

\[
Q(z)D_n(x)-D_n(z)Q(x)
\]

is a polynomial in `x,z` and vanishes on `z=x`; hence division by `z-x`
is exact in the polynomial ring. Its degree in `z` after division is at
most `n-1`. Dividing by `D_n(x)` leaves coefficients analytic near the
support `[0,q]`, so applying `L` coefficientwise produces a genuine
polynomial `P_{n,Q}(z)` of degree at most `n-1`.

Linearity, with the external quantities held constant under `L`, proves
exactly

\[
F(z)Q(z)-P_{n,Q}(z)
=D_n(z)L\left(\frac{Q(x)}{(z-x)D_n(x)}\right).
\]

If `H_n` is singular, its kernel supplies a nonzero such `Q` satisfying

\[
L(x^jQ(x)/D_n(x))=0\quad(0\le j<n).
\]

The expansion of `1/(z-x)` at infinity therefore makes the transform on
the right `O(z^{-n-1})`. Since `D_n` has degree `n`, the error
`E_n=FQ-P_n` is `O(z^{-1})`. The transform is analytic at every `p^a`, so
`E_n(p^a)=0` for `a<=n`.

There is no hidden divergence from constants here: for each function
analytic near `[0,q]`, `theta^2 f(x)=O(x)` as `x->0`. Consequently the
defining sum of `L` converges. The geometric expansion and both
derivatives converge uniformly on `|z|>r>q`, justifying the moment
expansion.

## 3. Consecutive singular sizes

For singular sizes `n,n+1`, the polynomial

\[
W=P_{n+1}Q_n-P_nQ_{n+1}
  =Q_{n+1}E_n-Q_nE_{n+1}
\]

has growth at most `O(z^{n-1})`, using `deg Q_n<=n-1`,
`deg Q_{n+1}<=n`, and the errors `O(z^{-1})`. It consequently has degree
at most `n-1`, although the individual product degrees can be larger.
Both errors vanish at `p,...,p^n`, providing `n` distinct roots of `W`.
Thus `W=0`. This step never divides by a kernel polynomial at an
interpolation node, so coincident zeros cause no problem.

## 4. Excluding an eventual singular tail

If every determinant from size `N` onward vanished, the preceding
identity would make all rational functions `P_n/Q_n` identical. Choose
their common reduced representation `P/Q`. Coprimality implies
`P_n=U_nP`, `Q_n=U_nQ` for nonzero polynomial multipliers `U_n`.

The error `E=FQ-P` is nonzero because `F` is nonrational. Since
`U_NE=O(z^{-1})`, the meromorphic function `E` has at infinity a zero of
some finite positive order `t`. Its leading Laurent term then implies
both:

* `deg U_n<=t-1`, because `U_nE=O(z^{-1})`;
* `E(z)!=0` outside a sufficiently large circle.

For each large exterior node `p^a`, the equation `U_n(p^a)E(p^a)=0`
forces a zero of `U_n`, whenever `a<=n`. As `n` grows this exceeds its
fixed degree bound. The contradiction proves infinitely many nonzero
determinants. The proof permits `P=0` and does not assume rationality of
the target zeta value.

## 5. Uniform jet and weight bounds

For the monic polynomials

\[
P_j(x)=\prod_{t=1}^j(x-q^{\lceil t/3\rceil}),\qquad
A_j=\sum_{t=1}^j\lceil t/3\rceil,\qquad R_j=\lceil j/3\rceil,
\]

all derivatives through order two vanish at lattice nodes with index
`m<R_j`, owing to triple roots. At `x=q^m`, `m>=R_j`, each root `rho`
satisfies `x<=rho`, and every differentiated linear factor contributes
`x` instead of at most `rho`. There are exactly `j^u` labeled choices
in the iterated product rule for `u=1,2`. This proves

\[
|P_j(x)|\le q^{A_j},\qquad
|\theta^uP_j(x)|\le j^u q^{A_j}x/q^{R_j}.
\]

For `j=0`, positive derivatives are zero, so the endpoint is harmless.
The product bounds for `W_K=1/D_K` are uniform in `K`:

\[
W_K\le e^{2/3},\quad
|\theta W_K|\le(4/3)e^{2/3}x,\quad
|\theta^2W_K|\le(8/3)e^{2/3}x.
\]

Indeed `1-q^a x>=3/4`, `sum q^a<=1`, and `x<=1/2`. For the last
inequality use `theta^2 W=W(a^2+b)`,
`a<=4x/3`, `b<=16x/9`, and `x^2<=x/2`.

For indices `i,j`, take `R=max(R_i,R_j)` and `d=i+j`. Every surviving
term in `theta^2(P_iP_jW)` contains at least one differentiated factor.
After removing `q^{A_i+A_j}x/q^R`, a valid bound for the remaining
coefficient is

\[
e^{2/3}\bigl(d^2+(8/3)d+8/3\bigr)
\le(8/3)e^{2/3}(d+1)^2.
\]

Summing `q^{m-R}` from `m=max(1,R)` costs at most two. Thus the stated
constant `12` is valid, since `(16/3)e^{2/3}<12`.

## 6. Exact exponent and determinant estimate

The monic basis change has determinant one. Extracting `q^{A_i}` from
row `i` and `q^{A_j}` from column `j`, and applying Hadamard, gives

\[
|\Delta_K|\le
q^{2\sum_{j=0}^{K-1}A_j}
\left[12(2K-1)^2\sqrt K\right]^K.
\]

Writing `j=3a+r`, `0<=r<3`, directly yields

\[
A_j=3a(a+1)/2+r(a+1),\qquad
2\sum_{j<K}A_j=\frac{K^3+3K^2-c_{K\bmod3}}9,
\]

where `(c_0,c_1,c_2)=(0,4,2)`. Summing the three residue classes proves
the exact formula; a finite arithmetic check also confirmed the defining
sum for sizes `1,...,300`. The proof does not rely on that check.

The prefactor has logarithm `O(K log K)`. The resulting leading decay is
therefore `-(log p)K^3/9`, as claimed. The same jet construction with root
multiplicity `s` validates the note's fixed-weight extension `s>=2`,
whose leading constant is `1/(3s)`. It makes no arithmetic claim for those
other weights.

## Assembly limit

If independent arithmetic work gives denominator cost
`(c+o(1))K^3 log p` and removable content `p^{K(K^2-1)/2}`, these validated
results allow any `c<11/18`. Nonvanishing along an infinite subsequence
suffices for the rationality contradiction. No lower bound on the
density of that subsequence is required.

## Independent reconstruction of the proposed denominator repair

The following checks the repair communicated by the coordinating agent,
independently of any revised note.

For `K/2<d<=K`, write `h=K-d`. At a primitive `d`-th root of unity,
the polynomial part of `fg/D_K`, for `deg f,deg g<K`, has degree at most
`K-2<2d`. Its only possibly singular polynomial moment is consequently
the coefficient of `x^d`. The residue is a nonzero scalar multiple of
the bilinear form

\[
 B_d(f,g)=[x^d]\operatorname{Quotient}(f(x)g(x),D_K(x))
 \quad\text{at the root of unity}.
\]

In the monomial basis, if either index `i<=d`, then for every `j<K`,
the quotient of `x^{i+j}` by `D_K` has degree at most `d-1`. Therefore
the first `d+1` rows and columns of this residue matrix are zero, and

\[
\operatorname{rank} B_d\le\max(0,K-d-1)=\max(0,h-1).
\]

The cluster basis is invertible over the local ring, so this rank bound
persists after specialization. Apply the original cluster weights:
`2,1` on each of the `h` double clusters, `3/2` on singleton `a=d`, and
zero on the remaining singletons. The partial-fraction contributions
become integral. For polynomial-moment contributions, every entry with
at least one positive weight is also integral because the smallest
positive weight is one. Only the zero-weight singleton block can retain
a simple pole. Its residue is a restriction of `B_d`, with rank at most
`max(0,h-1)`.

A matrix of the form `t^{-1}C+A(t)`, with `A` integral and constant
`rank C=r`, has determinant pole order at most `r`: constant invertible
row operations concentrate the nonzero rows of `C` into `r` rows, and
multiplying those rows by `t` makes the whole matrix integral. This
remains valid over the ramified local ring used for the half-integer
weight. Thus a valid total high-`d` exponent is

\[
6h+3+\max(0,h-1)\le 7h+3.
\]

For the low-`d` range, let the cluster sizes be `m_r`. Writing
`K=ad+b`, `0<=b<d`, gives exactly

\[
\sum_r m_r^2=K^2/d+b(1-b/d)\le K^2/d+d/4.
\]

Together with `F(m)<=m^2/4+2m+1`, this yields the valid exponent

\[
E_d=\left\lceil K^2/(4d)+2K+17d/16\right\rceil
\quad(d\le K/2).
\]

Using the totient asymptotics already stated in the denominator note,
the low range contributes `161/(64 pi^2)` and the high range contributes
`7/(2 pi^2)` to the coefficient of `K^3 log p`. Their sum is

\[
\frac{385}{64\pi^2}=0.6095102453484382\ldots
<\frac{11}{18}=0.6111111111111111\ldots.
\]

The positive margin is `0.00160086576267293...`; at `p=2` it becomes
`0.00110963558985169...` in the cubic logarithmic decay rate. It is small
but strictly positive, and suffices asymptotically. This independent
reconstruction validates the stated repair, provided the final note uses
these exponents and the rank argument rather than the incorrect degree
inequality in its original version.

## Final revised denominator note: stronger repair passed

The revised `work/denominators/PROOF.md` was subsequently read in full.
It improves the conservative repair above by moving one cluster basis
root with the upper node. For a double cluster `{a,a+d}`, set

\[
F_0=Q/Q_r,\qquad F_1=(Q/Q_r)(x-z^{a+d}).
\]

The change from the previous confluent basis has determinant one within
the block, so the full basis change remains a unit. In the simple-pole
part of an entry involving `F_1`, the residue at the higher node
`z^{a+d}` vanishes identically. At the lower node `z^a`, the factor
`z^a-z^{a+d}` cancels the single colliding factor in the partial-fraction
denominator. The remaining tail `S_a` is analytic because `a<d`. Thus both
mixed and `F_1^2` pole-part entries are analytic. Only the `F_0^2` entry
can have a pole, whose order is at most four.

Weights `(2,0)` therefore clear each double cluster at cost four.
Singleton `a=d` still costs three, and other singletons cost zero. The
polynomial moment matrix has the same exact rank bound proved above.
Indeed it is slightly cleaner to factor its entire coefficient matrix
`H_d(z)`, of rank at most `max(0,h-1)` over the local fraction field, and
apply the low-rank determinant expansion after scaling. Every selected
minor of that matrix larger than this rank vanishes identically, so at
most `max(0,h-1)` factors of the simple pole can contribute to any
nonzero determinant term.

This proves

\[
-v_{\Phi_d}(\Delta_K)\le4h+3+\max(0,h-1)\le5h+3.
\]

The revised high-range totient contribution is consequently
`5/(2 pi^2)`, and the total denominator constant is

\[
\frac{321}{64\pi^2}=0.5081890617061005\ldots.
\]

The resulting margin below `11/18` is
`0.1029220494050107...`. The revised bound is rigorously stronger than
the conservative repair; neither numerical pole-pattern extrapolation
nor cancellation between independently estimated matrix entries is
required. The revised note's localization and totient-asymptotic steps
also pass this audit.

The note's general-weight denominator formulas are consistent with the
same argument: replace the fourth-order double-cluster pole by order
`s+1`, retain the polynomial-moment rank loss, and obtain
`E_high=(s+2)(K-d)+s`. This remains an arithmetic estimate and does not
assert irrationality for all weights.
