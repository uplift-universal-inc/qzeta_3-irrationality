"""Independent finite arithmetic audit. The all-K argument is in AUDIT.md."""
from pathlib import Path
import sys, json, math

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'source/zeta7-port'))
from qhankel import entries_q, det_poly, fmpq, fmpq_mat

def v(n, ell):
    n = int(n)
    if not n:
        return math.inf
    t = 0
    while n % ell == 0:
        n //= ell
        t += 1
    return t

def vq(q, ell):
    return v(q.p, ell) - v(q.q, ell)

def primes(n):
    out = []
    d = 2
    while d*d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out

def h_values(p, K, count):
    h = [1]+[0]*count
    for a in range(1, K+1):
        r = p**a
        for j in range(1, count+1):
            h[j] += r*h[j-1]
    return h

def residue(q, modulus):
    return int(q.p)*pow(int(q.q), -1, modulus) % modulus

rows = []
for p in [2, 3, 4, 6, 8, 9, 12, 16, 25, 36]:
    for K in range(1, 11):
        aa, bb = entries_q(3, p, K, 0, 1, K)
        polynomial = det_poly(K, aa, bb)
        E, A = K*(K*K-1)//2, K*(K+1)//2
        normalized = [polynomial[j]/fmpq(p)**E for j in range(K+1)]
        assert normalized[-1] == (-1)**(K*(K-1)//2)
        gcd = 0
        for c in polynomial:
            gcd = math.gcd(gcd, int(c.p))
        assert gcd == p**E
        # Independently check the coefficient polynomial by exact evaluation.
        for X in [fmpq(0), fmpq(1), fmpq(2, 3)]:
            direct = fmpq_mat(K,K,[aa[i+j]+bb[i+j]*X
                                  for i in range(K) for j in range(K)]).det()
            assert direct == polynomial(X)
        local = []
        for ell in primes(p):
            r = v(p,ell)
            assert all(vq(c,ell) >= 1 for c in normalized[:-1])
            # Recover the local series at every matrix moment, independently
            # of the exact partial-fractions engine.
            J = A+2*K+20
            h = h_values(p,K,J+K)
            z = sum((fmpq(p**j*(1+p**j), (1-p**j)**3)
                     for j in range(1,J+1)), fmpq(0))
            for k in range(2*K-1):
                R = sum((fmpq(j*j*p**j,1-p**j)*h[k+j-K]
                         for j in range(1,J+1) if k+j >= K), fmpq(0))
                R += sum((fmpq(j*j,p**j-1)*h[k-K-j]
                          for j in range(1,k-K+1)), fmpq(0))
                for X in [fmpq(0), fmpq(1), fmpq(2,3)]:
                    U = X+z
                    approx = U/fmpq((-1)**K*p**A)+R if k == 0 else R-(U*h[k-K] if k >= K else 0)
                    exact = (aa[k]+bb[k]*X)/fmpq((-1)**K*p**A)
                    # Z truncation error is >=r(J+1), and dividing by F(0)
                    # loses rA. R truncation error is >=r(2J+2+k-K).
                    guaranteed = r*(J+1-A) if k == 0 else r*(J+1)
                    assert vq(exact-approx,ell) >= guaranteed
            # High-precision exceptional-local-value certificate.
            predicted = r*(A+K)
            mod = ell**(predicted+8)
            zz = 0
            for j in range(1,predicted+9):
                y = pow(p,j,mod)
                zz = (zz+y*(1+y)*pow(pow(1-y,3,mod),-1,mod)) % mod
            val = 0
            for c in reversed(normalized):
                val = (val*(-zz)+residue(c,mod)) % mod
            assert v(val,ell) == predicted
            local.append(dict(ell=ell, r=r, exceptional_value_valuation=predicted))
        rows.append(dict(p=p,K=K,content=p**E,local=local))

out = Path(__file__).with_name('checks.json')
out.write_text(json.dumps(dict(status='passed',determinant_count=len(rows),rows=rows),indent=2)+'\n')
print(json.dumps(dict(status='passed',determinant_count=len(rows),output=str(out))))
