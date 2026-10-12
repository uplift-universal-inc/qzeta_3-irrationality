# All-size analytic bound for the q-Hermite determinant

Let 0<q<=1/2, K>=1, theta=x d/dx,

    W_K(x)=1/prod_{a=1}^K (1-q^a x),
    L(f)=sum_{m>=1} theta^2 f(q^m),
    Delta_K=det[L(x^{i+j}W_K)]_{0<=i,j<K}.

This note proves the bound

    |Delta_K| <= [12(2K-1)^2 sqrt(K)]^K q^{E_K},

where

    E_K=(K^3+3K^2-c_r)/9,
    r=K mod 3, (c_0,c_1,c_2)=(0,4,2).

In particular,

    log|Delta_K| <= -(log(1/q))/9 K^3 + O_q(K^2).

The assertion permits Delta_K=0; it does NOT prove nonvanishing. It doubles
the cubic constant of the 1/18 sketch in the supplied report.

## Monic basis and jets

Set

    P_j(x)=prod_{t=1}^j (x-q^{ceil(t/3)}), P_0=1,
    R_j=ceil(j/3), A_j=sum_{t=1}^j ceil(t/3).

The basis change from x^j to P_j is unit triangular and hence leaves the
Gram determinant unchanged.

For m<R_j, P_j has a triple zero at x=q^m. Thus all theta^u P_j(q^m),
0<=u<=2, vanish. For m>=R_j, put x=q^m. Each root rho of P_j satisfies
x<=rho; therefore |x-rho|<=rho. For u>=1, theta^u(x-rho)=x. The Leibniz
rule then gives, for u=1,2,

    |P_j(x)| <= q^{A_j},
    |theta^u P_j(x)| <= j^u q^{A_j} x/q^{R_j}.

For u=2, there are j terms differentiating one factor twice and j(j-1)
terms differentiating two different factors once. Every differentiated
factor contributes x/rho<=1, and at least one such factor contributes at
most x/q^{R_j}. This proves the displayed bounds including their constants.
For j=0 the positive-order derivatives vanish.

## Uniform bounds on the rational weight

For 0<=x<=q<=1/2, let

    a(x)=theta log W_K=sum_{a<=K} q^a x/(1-q^a x),
    b(x)=theta^2 log W_K=sum_{a<=K} q^a x/(1-q^a x)^2.

Elementary geometric-series bounds yield

    1<=W_K<=exp(2/3),
    a(x)<=(4/3)x, b(x)<=(16/9)x,
    |theta W_K|<=(4/3)exp(2/3)x,
    |theta^2 W_K|<=(8/3)exp(2/3)x.

Indeed, log W_K <= sum q^a x/(1-q^a x) <= (4/3)x<=2/3,
and theta^2 W_K=W_K(a^2+b), with x^2<=x/2.

## Matrix-entry estimate and summation

Fix i,j, set R=max(R_i,R_j), and expand theta^2(P_i P_j W_K)
by the Leibniz rule. Every summand vanishes at x=q^m for m<R.
For m>=max(1,R), apply the preceding jet estimates. Every summand has
at least one derivative, so its bound contains the decaying factor
x/q^R. (For two or more such factors, the additional ones are <=1.)
Consequently

    |theta^2(P_i P_j W_K)(q^m)|
      <= (8/3)exp(2/3)(i+j+1)^2
         q^{A_i+A_j} q^{m-R}.

Since sum_{m>=max(1,R)}q^{m-R}<=1/(1-q)<=2,

    |L(P_i P_j W_K)| <= 12(i+j+1)^2 q^{A_i+A_j}.

The number 12 is a rounded-up universal constant; the calculation gives
(16/3)exp(2/3)<12.

## Determinant bound

Factor q^{A_i} from row i and q^{A_j} from column j. Each normalized
entry has absolute value at most 12(2K-1)^2. Hadamard's inequality gives

    |Delta_K| <= q^{2 sum_{j=0}^{K-1} A_j}
                [12(2K-1)^2 sqrt(K)]^K.

For j=3a+r, 0<=r<3,

    A_j=3a(a+1)/2+r(a+1).

Summing this identity gives the stated exact E_K.

## Consequence for the arithmetic budget

If a separate proof establishes coefficient content divisible by
p^{K(K^2-1)/2} (p=1/q) and odd denominator cost
log l_K <= (c+o(1))K^3, then the present analytic estimate allows

    c < (1/2+1/9)log p = (11/18)log p.

For p=2 this is approximately 0.4235899436755221, improving the report's
0.38508 threshold. Neither the full-polynomial content claim nor an
adequate denominator theorem is established by this note.

## Audit caution

The supplied evaluator zeta_q sums finitely many terms and returns the
ball for that finite sum without adding the omitted positive tail.
Its printed intervals are therefore not certified enclosures of zeta_q.
This is separate from the analytic estimate above, which uses no numeric
evaluation and proves an all-K bound directly.

## Extension to every fixed weight s>=2

Replace theta^2 by theta^{s-1} and choose

    P_j(x)=prod_{t=1}^j(x-q^{ceil(t/s)}),
    A_{j,s}=sum_{t=1}^j ceil(t/s), R_{j,s}=ceil(j/s).

All jets of orders 0,...,s-1 vanish at earlier lattice nodes. For a
surviving node and 1<=u<=s-1, the repeated Leibniz rule has j^u terms
(each of u labelled derivative applications chooses a factor). Thus

    |theta^u P_j(q^m)| <= j^u q^{A_{j,s}} q^{m-R_{j,s}}.

For fixed u, all theta^u W_K are bounded uniformly in K and q<=1/2,
and for u>=1 their bounds contain a factor x. This follows by expanding
theta^u log W_K=sum_{a>=1,n>=1} n^{u-1}q^{an}x^n and applying the
finite-order product rule to W_K=exp(log W_K).

The same summation and Hadamard argument proves

    |Delta_{K,s}| <= [C_s(2K-1)^{s-1} sqrt(K)]^K
                     q^{2 sum_{j<K} A_{j,s}},

with a finite constant C_s independent of K and q<=1/2. Since
A_{j,s}=j^2/(2s)+O_s(j), this gives

    log|Delta_{K,s}| <= -(log(1/q))/(3s) K^3 + O_s(K^2).

This extends the analytic mechanism to every fixed s>=2. It does not
extend the arithmetic budget or prove any new irrationality theorem.
The regularized s=1 functional requires separate treatment: subtracting
f(0) adds a rank-one issue and the positive-order-derivative summation
argument above does not apply literally.
