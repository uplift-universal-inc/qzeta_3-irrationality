"""
q-analogue of the Fauzan/Hermite Hankel construction for zeta_q(s), q = 1/p.

zeta_q(s) = sum_{n>=1} n^{s-1} q^n/(1-q^n) = sum_{n>=1} g_s(q^n),  g_s(y) = sum_{k>=1} k^{s-1} y^k = y rho_s(y)/(1-y)^s.

Functional on rational functions f(x) with simple poles at x = p^a:   L_s(f) = sum_{m>=1} (theta^{s-1} f)(q^m),  theta = x d/dx.
  L_s(x^k)            = k^{s-1} q^k/(1-q^k) = k^{s-1}/(p^k-1)   (k>=1),  L_s(1) = 0 for s>=2 (= zeta_q(1)-type divergent for s=1: we regularize L_1(1)=0)
  L_s(1/(1-q^a x))    = sum_{n>a} g_s(q^n) = X - S_a,   S_a = sum_{n<=a} g_s(q^n),  X = zeta_q(s).
Matrix:  G_ij = L_s( W(x) x^{i+j} / D_K(x) ),  D_K = prod_{a=1}^K (1 - q^a x),  W = prod_{a<=N} (1-q^a x)^e,  h = K - N.
Delta(X) = det G.  Report log|P(zeta_q(s))| for the primitive integer polynomial P, and the sign.
"""
import sys, time, math
from math import gcd, lcm
from flint import fmpq, fmpz, fmpq_poly, fmpz_poly, fmpq_mat, arb, ctx

def eulerian_g(s, y):
    """g_s(y) = sum_k k^{s-1} y^k exactly for rational y (|y|<1): y rho_s(y)/(1-y)^s via Eulerian numbers."""
    m = s - 1
    # Eulerian numbers A(m, j), sum_k k^m y^k = sum_j A(m,j) y^{j+1} / (1-y)^{m+1}
    A = [[fmpq(0)]*(m+1) for _ in range(m+1)]
    A[0][0] = fmpq(1)
    for n in range(1, m+1):
        for j in range(n+1):
            A[n][j] = (j+1)*A[n-1][j] + (n-j)*(A[n-1][j-1] if j >= 1 else fmpq(0))
    num = fmpq(0)
    for j in range(m+1):
        num += A[m][j] * y**(j+1)
    return num / (1-y)**(m+1)

def entries_q(s, p, K, N, e, h):
    q = fmpq(1, p)
    # pole set: a = N+1..K (poles at x = p^a); W vanishes at a<=N
    # D_K(x) = prod_{a=1}^K (1 - q^a x); work with monic-in-x scaled version: (1 - q^a x) = -q^a (x - p^a)
    # Partial fractions of W x^k / D_K with W = prod_{a<=N} (1 - q^a x)^e:
    #   = polynomial part + sum_{a>N} c_a(k) / (1 - q^a x),  c_a(k) = [W x^k (1 - q^a x)/D_K] at x = p^a
    S = {}
    acc = fmpq(0)
    for n in range(1, K+1):
        acc += eulerian_g(s, q**n)
        S[n] = acc
    base = {}
    for a in range(N+1, K+1):
        pa = fmpq(p)**a
        num = fmpq(1)
        for b in range(1, N+1):
            num *= (1 - q**b * pa)**e
        den = fmpq(1)
        for b in range(1, K+1):
            if b != a:
                den *= (1 - q**b * pa)
        base[a] = num/den
    # polynomial part: W x^k // D_K  (as polynomials in x over Q)
    Wq = fmpq_poly([1])
    for b in range(1, N+1):
        Wq *= fmpq_poly([1, -q**b])**e
    Dq = fmpq_poly([1])
    for b in range(1, K+1):
        Dq *= fmpq_poly([1, -q**b])
    E = 2*h - 1
    a_list, b_list = [], []
    for k in range(E):
        Pk = (Wq * fmpq_poly([0]*k + [1])) // Dq
        ak = fmpq(0)
        for j in range(1, Pk.degree()+1):
            ak += Pk[j] * fmpq(j)**(s-1) / (fmpz(p)**j - 1)
        bk = fmpq(0)
        for a in range(N+1, K+1):
            c = base[a] * fmpq(p)**(a*k)
            bk += c
            ak += -c * S[a]
        a_list.append(ak); b_list.append(bk)
    return a_list, b_list

def det_poly(h, a, b):
    A = fmpq_mat(h, h, [a[i+j] for i in range(h) for j in range(h)])
    B = fmpq_mat(h, h, [b[i+j] for i in range(h) for j in range(h)])
    detB = B.det()
    C = -(B.inv() * A)
    return C.charpoly() * detB

def zeta_q(s, p, prec):
    ctx.prec = prec
    tot = arb(0)
    n = 1
    while True:
        term = arb(n)**(s-1) / (arb(p)**n - 1)
        tot += term
        if n > 50 and n*math.log(p) > prec*0.7 + 10:
            break
        n += 1
    return tot

def run_q(s, p, K, N, e, label=""):
    t0 = time.time()
    h = K - N
    a, b = entries_q(s, p, K, N, e, h)
    Delta = det_poly(h, a, b)
    deg = Delta.degree()
    g = 0; l = 1
    for i in range(deg+1):
        c = Delta[i]; g = gcd(g, int(c.p)); l = lcm(l, int(c.q))
    P = fmpz_poly([int(c.p) * (l // int(c.q)) // g for c in [Delta[i] for i in range(deg+1)]])
    maxbits = max(abs(int(P[i])).bit_length() for i in range(deg+1))
    prec = maxbits + 4*K*K*int(math.log2(p)+1) + 4000
    z = zeta_q(s, p, prec)
    Pz = arb(0); zp = arb(1)
    for i in range(deg+1):
        Pz += arb(int(P[i]))*zp; zp *= z
    if Pz == 0:
        print(f"s={s} p={p} K={K} N={N} e={e} h={h} {label}: P(zeta_q) contains 0 at precision {prec} (inconclusive)")
        return None
    logP = float(abs(Pz).log())
    sgn = '+' if Pz > 0 else '-'
    # natural scale: the q-lcm cost grows like K^3 for a size-K matrix; report per K^2 and per K^3
    print(f"s={s} p={p} K={K:3d} N={N:2d} e={e} h={h:3d} {label:18s} | log|P(zeta_q)| = {logP:12.2f}   /K^2={logP/K**2:+9.4f}  /K^3={logP/K**3:+8.4f}  sign={sgn}  maxbits={maxbits}  ({time.time()-t0:.0f}s)", flush=True)
    return logP

if __name__ == "__main__":
    s = int(sys.argv[1]); p = int(sys.argv[2])
    for spec in sys.argv[3:]:
        K, N, e = map(int, spec.split(':'))
        run_q(s, p, K, N, e)
