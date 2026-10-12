# Independent mathematical reviews

These checks are mathematical reviews, not Lean verification.

## Full content and p=2 nonvanishing

Reviewed `work/valuation/PROOF.md` containing the local moment expansion

    M_0=U/F(0)+R_0,
    M_k=-U h_{k-K}+R_k (k>=1), U=X+Z.

The divided-difference signs, convergence, and stated R_k bounds check out.
The leading coefficient is exactly signed p^{K(K^2-1)/2}; scaling row 0
establishes the full coefficient content. No gap found in these arguments.

For p=2 and U!=0, the reversed lower block has weighted entry valuations
>=1/2 after adding (i-j)/2. Only its two adjacent diagonals can attain
equality, and for even dimension their unique perfect matching is the
adjacent transposition permutation. The stated determinant valuation
(K-1)/2 follows. Scaling the first row by 2^{K(K+1)/2} then separates
the corner-cofactor term from every permutation crossing row 0.

For U=0, adding 2(i-j)/3 makes every off-diagonal valuation strictly
larger than the diagonal valuation 1. The identity term uniquely attains
valuation K. This handles the exact exceptional local value X=-Z and
does not assume Z is irrational.

## Denominator proof correction and repair

The first denominator draft incorrectly inferred K-2<d from d>K/2.
This was identified during this independent review and reported to the
authors before assembly. The polynomial moment mu_d can indeed occur.

The repair was obtained independently by the denominator author and this
reviewer: the coefficient matrix of mu_d has rank at most K-d-1, because
in the monomial basis it is supported where i+j>=K+d. Thus the extra
simple pole costs at most max(0,K-d-1) in the determinant, even after
the nonnegative row and column weighting. Rank is invariant under basis
change, and determinant(A+u B) has degree at most rank(B) in u.

The low-d bound can simultaneously be sharpened using

    sum_r m_r^2 = K^2/d + d f(1-f) <= K^2/d+d/4,
    f={K/d}.

With the original size-two weights this already yields the valid leading
constant 385/(64 pi^2)=0.6095102453..., below 11/18. Thus the repair
does not merely reduce the gap; it preserves a positive margin.

## Further high-d improvement

The normality reviewer suggested replacing the second vector in a
two-node cluster {a,a+d} by

    F_1=(Q/Q_r)(x-z^{a+d}), F_0=Q/Q_r.

This kills the pole at the high node exactly. The low-node S_a is analytic
because a<=K-d<d. Consequently the mixed and (1,1) pole entries are
analytic, while only the (0,0) entry can have order four. Weights (2,0)
give cost four per double cluster. This review finds the cancellation
valid. Together with the preceding rank correction and low-d variance
bound, it yields the improved constant 321/(64 pi^2).

## Proposed general-p nonvanishing extension

Let ell|p, r=v_ell(p), t=v_ell(U)>0. The same reversed lower block has
off-diagonal minima r and 0 at d=-1 and d=+1 respectively. Weight by
r d/2. If t<r/2 the diagonal is uniquely minimal; if t>r/2 the even-
dimension adjacent matching is uniquely minimal.

At the critical case 2t=r, set tau=ell^t and multiply the entry of offset
d by tau^d, then divide the whole matrix by tau. Modulo ell the result
is tridiagonal, with diagonal -u=-U/tau, upper diagonal c=p/tau^2,
and lower diagonal -1. Both u,c are nonzero in the residue field, and
the coefficients do not depend on K. Its determinants satisfy

    D_0=1, D_1=-u, D_n=-u D_{n-1}+c D_{n-2}.

Two consecutive terms cannot both vanish since c is a unit. Hence
infinitely many lower-block dimensions have nonzero reduction. The
first-row separation then completes the same nonvanishing argument.
The exact U=0 case uses weights 2r d/3 and is unchanged. This extension
was sent to the valuation author for full incorporation and review.
