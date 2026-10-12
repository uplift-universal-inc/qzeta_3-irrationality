"""Exact independent checks of PROOF.md against the supplied qhankel engine.

This verifies finite instances only; the proof is in PROOF.md.
"""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'source/zeta7-port'))
from qhankel import entries_q, det_poly, fmpq


def valuation(n, ell=2):
    n = int(n)
    if n == 0:
        return None
    e = 0
    while n % ell == 0:
        n //= ell
        e += 1
    return e


def qvaluation(q, ell=2):
    if q == 0:
        return None
    return valuation(q.p, ell) - valuation(q.q, ell)


def rational_mod(q, modulus):
    return int(q.p) * pow(int(q.q), -1, modulus) % modulus


def zlocal_mod(p, modulus, count):
    z = 0
    pn = 1
    for _ in range(count):
        pn = pn * p % modulus
        z += pn * (1 + pn) * pow(pow(1 - pn, 3, modulus), -1, modulus)
        z %= modulus
    return z


def evaluate_mod(poly, x, modulus):
    v = 0
    for c in reversed(poly):
        v = (v*x + rational_mod(c, modulus)) % modulus
    return v


rows = []
for p, ell, power, maxk in [(2, 2, 1, 32), (3, 3, 1, 16), (4, 2, 2, 14), (8,2,3,10), (16,2,4,10)]:
    for K in range(1, maxk+1):
        a, b = entries_q(3, p, K, 0, 1, K)
        delta = det_poly(K, a, b)
        E = K*(K*K-1)//2
        A = K*(K+1)//2
        poly = [delta[i] / fmpq(p)**E for i in range(K+1)]
        assert poly[-1] == (-1)**(K*(K-1)//2)
        assert all(qvaluation(c, ell) is None or qvaluation(c, ell) >= 0 for c in poly)
        assert all(qvaluation(c, ell) is None or qvaluation(c, ell) >= 1 for c in poly[:-1])
        # Exceptional U=0 prediction, using enough local digits for a strict certificate.
        expected = power*(A+K)
        digits = expected + 16
        modulus = ell**digits
        z = zlocal_mod(p, modulus, digits)
        value = evaluate_mod(poly, -z, modulus)
        assert valuation(value, ell) == expected, (p, K, valuation(value, ell), expected)
        item = dict(p=p, K=K, leading_coefficient_verified=True,
                    content_valuation=power*E,
                    exceptional_normalized_value_valuation=expected)
        if p == 2 and K % 2 and K >= 3:
            generic = []
            for numerator, denominator in [(2,1),(6,1),(10,1),(4,1),(12,1),(2,3)]:
                x = fmpq(numerator, denominator)
                xm = rational_mod(x, modulus)
                t = valuation((xm+z) % modulus)
                if A > t + (K-1)//2:
                    actual = valuation(evaluate_mod(poly, xm, modulus))
                    assert actual == t+(K-1)//2, (p,K,x,t,actual)
                    generic.append(dict(X=str(x), t=t, value_valuation=actual))
            item['generic_odd_K_checks'] = generic
        elif K % 2 and K >= 3:
            generic = []
            for x in (fmpq(2), fmpq(4), fmpq(8), fmpq(16)):
                xm = rational_mod(x, modulus)
                t = valuation((xm+z) % modulus, ell)
                n = K-1
                if 2*t == power:
                    u = ((xm+z) // ell**t) % ell
                    c = (p // ell**power) % ell
                    previous, current = 0, 1
                    for _ in range(n):
                        previous, current = current, (-u*current+c*previous) % ell
                    if current == 0:
                        continue
                    expected_generic = K*t
                elif 2*t < power:
                    expected_generic = K*t
                else:
                    expected_generic = t+n*power//2
                if power*A > expected_generic:
                    actual = valuation(evaluate_mod(poly, xm, modulus), ell)
                    assert actual == expected_generic, (p,K,x,t,actual,expected_generic)
                    generic.append(dict(X=str(x), t=t, value_valuation=actual))
            item['general_p_odd_K_checks'] = generic
        rows.append(item)

target = Path(__file__).with_name('verification.json')
target.write_text(json.dumps(dict(status='passed', rows=rows), indent=2)+'\n')
print(json.dumps(dict(status='passed', determinant_count=len(rows), output=str(target))))
