# Nonvanishing of infinitely many moving-denominator Hankel determinants

## Statement
Fix an integer p>=2, q=1/p. Put

- theta=x d/dx;
- L(f)=sum_{m>=1} theta^2 f(q^m);
- D_n(x)=prod_{a=1}^n (1-q^a x);
- H_n=[L(x^{i+j}/D_n(x))]_{0<=i,j<n}.

Then det H_n is nonzero for infinitely many n. No rationality hypothesis on the q-zeta value, p-adic argument, or fixed sign pattern is required.

This is an analytic/algebraic statement. It does not by itself provide the denominator/size bounds necessary for irrationality.

## Cauchy transform
Define for |z|>q

F(z)=L(1/(z-x))
    =sum_{m>=1} q^m(z+q^m)/(z-q^m)^3.

This converges locally normally away from {0,q,q^2,...}; it is analytic at infinity and is O(z^{-2}). Each z=q^m is a genuine pole of order three, with leading Laurent coefficient 2q^{2m} !=0, since all other terms are analytic near that point. Therefore F is not rational.

For every fixed n and polynomial Q of degree <=n-1, define

R_{n,Q}(z)=L(Q(x)/((z-x)D_n(x))),
P_{n,Q}(z)=L((Q(z)D_n(x)-D_n(z)Q(x))/((z-x)D_n(x))).

P_{n,Q} is a polynomial in z: its displayed numerator vanishes at z=x, so the factor z-x divides it identically; the remaining coefficients are rational functions of x with poles only at p,...,p^n, where L is well-defined. The identity

F(z)Q(z)-P_{n,Q}(z)=D_n(z)R_{n,Q}(z)

holds. If Q is in the kernel of H_n, then

L(x^j Q(x)/D_n(x))=0,  j=0,...,n-1.

Expanding 1/(z-x) at infinity gives R_{n,Q}(z)=O(z^{-n-1}), and hence

E_{n,Q}(z):=F(z)Q(z)-P_{n,Q}(z)=O(z^{-1}).

Moreover, R_{n,Q} is analytic at each p^a, since every p^a lies outside the support {q^m}. Thus E_{n,Q}(p^a)=0 for all a<=n.

## Consecutive singular determinants force the same rational approximant
Suppose det H_n=det H_{n+1}=0. Choose nonzero polynomial kernel vectors Q_n,Q_{n+1} with degrees <=n-1,n, and write P_n=P_{n,Q_n}, P_{n+1}=P_{n+1,Q_{n+1}}.

The polynomial

W(z)=P_{n+1}(z)Q_n(z)-P_n(z)Q_{n+1}(z)
    =Q_{n+1}(z)E_n(z)-Q_n(z)E_{n+1}(z)

is O(z^{n-1}) at infinity, because both E's are O(z^{-1}). Therefore deg W<=n-1. It vanishes at the n distinct nodes p,...,p^n, because E_n and E_{n+1} both vanish there. Consequently W=0, and P_n/Q_n=P_{n+1}/Q_{n+1} as rational functions. This remains true even if either denominator vanishes at an interpolation node; no cancellation at nodes was assumed.

## An infinite singular tail is impossible
Assume det H_n=0 for every n>=N. By the preceding step all P_n/Q_n equal one fixed reduced rational function P/Q, with Q!=0 and gcd(P,Q)=1. Thus

Q_n=U_n Q, P_n=U_n P

for nonzero polynomials U_n. Put E=FQ-P. Because F is not rational, E is not identically zero. Since E_N=U_N E=O(z^{-1}), E has a finite positive order t at infinity:

E(z)=c z^{-t}+O(z^{-t-1}), c!=0, t>=1.

For every n, E_n=U_n E=O(z^{-1}), so deg U_n<=t-1. The same Laurent expansion supplies a radius R such that E(z)!=0 for |z|>R. For every a<=n with p^a>R, E_n(p^a)=0 consequently forces U_n(p^a)=0. As n increases there are arbitrarily many such distinct nodes, contradicting deg U_n<=t-1.

This proves infinitely many det H_n!=0.

## General scope and analytic justifications
The argument works for any Cauchy-transform functional L whose support is contained in a compact disk, whose transform F is analytic at infinity and nonrational, and for nested simple exterior poles t_a escaping to infinity. Take D_n(x)=prod_{a<=n}(x-t_a) or any nonzero scalar multiple. The q-functional satisfies these hypotheses as shown above.

Termwise operations are valid here without distribution theory: for f analytic around [0,q], theta^2 f(x)=O(x) near x=0. Every rational function used above is analytic around [0,q]. Thus the sums defining L converge absolutely, locally uniformly in the external parameter z away from [0,q]. The geometric-series expansion at infinity may be differentiated twice in x and summed termwise on any |z|>r>q. This gives the required moment expansion and all stated O bounds.

Status: elementary proof derived 2026-10-11; independently audited line by line by the nonvanishing agent. No external theorem is invoked.
