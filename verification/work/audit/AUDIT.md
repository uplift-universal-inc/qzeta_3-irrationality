# Independent certificate audit

## Findings

The numerical determinant decay is real in the tested range. The exact integer polynomials supplied for K=2,...,6 reproduce exactly. Independent primitive normalization agrees with the source normalization. The new evaluator encloses the entire infinite Lambert series with an explicit tail bound and checks that the resulting Arb interval excludes zero.

The claimed sign law is false. With exactly the sign normalization used by the source:

- K=7: P_7(zeta) = [-5.28263237950699341117733e-7 +/- 3.15e-31], although K=1 mod 3.
- K=9: P_9(zeta) = [3.07839880750537509681907e-19 +/- 4.82e-43], although K=0 mod 3.

K=2 already contradicts a global modulo-3 rule; K=7 is the first contradiction in the reported K>=6 range. The even-index samples in the source conceal this error. Complete enumeration through K=30 is in `sign_scan.jsonl`. K=6,...,30 instead follows the empirical modulo-6 rule: positive for residues 2,3,4 and negative for 5,0,1. This is finite evidence only and is not a nonvanishing theorem.

The first three polynomials are:

- P_1(X)=X-6.
- P_2(X)=-(X-6)(27X-182).
- P_3(X)=211204892-96808998X+14771322X^2-750141X^3.

Thus P_1 and P_2 do share a rational root, 6. P_3(6)=88040. FLINT exact factorization finds P_3,...,P_7 irreducible, but this proves nothing for unbounded K.

## Numerical repair

The source `zeta_q` returns an interval for a finite sum without adding the infinite tail. The source also tests `Pz == 0` instead of interval containment of zero. Both issues are fixed in `audit_qhankel.py`. Repairing them does not change the verified signs or displayed decay constants.

For r=s-1 and truncation at N, set rho=((N+2)/(N+1))^r/p < 1. Then

    0 < sum_{n>N} n^r/(p^n-1)
      <= (N+1)^r p^(-N-1) / ((1-p^(-N-1))(1-rho)).

The proof is the geometric ratio bound for n^r p^-n, together with 1/(1-p^-n)<=1/(1-p^(-N-1)). Every arithmetic operation in the actual enclosure is outward-rounded Arb arithmetic. The tail interval is added before evaluating P by Horner's rule. We explicitly assert `not value.contains(0)`.

## Primitive normalization

Let rational coefficients be c_i=a_i/b_i in lowest terms, let L=lcm b_i, and g=gcd a_i. The source divides the integer coefficients L*c_i by g. This is correct: for a prime dividing L, a coefficient with maximal denominator valuation gives an integer coefficient with valuation zero, so neither g nor the cleared polynomial's content has that prime. For any other prime, the minimum valuation of cleared coefficients equals the minimum valuation of the a_i. The new code nevertheless recomputes the content directly from all cleared integer coefficients and checks equality.

## s=1 regularization

The regularized functional is consistent if written explicitly as

    L_1(f) = sum_{m>=1} (f(p^-m)-f(0)).

For a simple pole f(x)=1/(1-p^-a x), its regularized value is exactly the pure tail zeta_q(1)-sum_{n<=a}p^-n/(1-p^-n). Constants are annihilated and monomial moments agree with the code. The unregularized sum would diverge.

## Scope

The certificates establish finite nonvanishing, not infinitely many nonzero values. Finite cubic decay does not prove a uniform cubic upper bound. In particular this audit does not close the irrationality proof or claim an extension to all s.

## Exact all-K degree identity

Write B_ij=sum_a d_a p^{a(i+j)}, with d_a=prod_{b!=a}(1-p^{a-b})^-1. By Vandermonde factorization,

    det B = (-1)^(K(K-1)/2) p^(K(K^2-1)/2).

Each unordered pair a<b contributes

    (p^b-p^a)^2 / ((1-p^(a-b))(1-p^(b-a))) = -p^(a+b).

Summing a+b over all pairs gives K(K^2-1)/2. Consequently Delta_K has degree exactly K, for all s and p, when N=0. This is polynomial nonzeroness, not nonzeroness after substituting zeta. It also proves that the rational-coefficient numerator gcd has no prime factor outside the factors of p.

## Fast independent summation

`fast_verify.py` additionally uses the exact identity

    zeta_q(s) = sum_{n>=1} sigma_(s-1)(n) p^(-n).

A divisor sieve computes all coefficients through N exactly, and integer Horner evaluation yields the exact prefix numerator. The bound sigma_(s-1)(n)<=n^s gives tail at most

    (N+1)^s p^(-N-1) / (1-((N+2)/(N+1))^s/p).

This enclosure was cross-checked against the original Lambert-term enclosure for s=1,...,5 at 400 bits before use at larger K. It avoids repeated high-precision divisions and is mathematically independent of the truncation scheme in the uploaded harness.

## Final high-order reproduction

The independent divisor-sieve enclosure certifies, at K=60 and p=2,

    P_60(zeta_q(3)) = [-4.34518351412299664323688e-8968 +/- 4.45e-8992],
    log(abs(P_60(zeta_q(3)))) / 60^3 = -0.0955931205832272.

Evaluation used 266276-bit Arb precision and an exact series prefix through N=266468. Complete metadata is in `fast_K60.json`. This confirms the reported finite decay; it supplies no asymptotic proof.
