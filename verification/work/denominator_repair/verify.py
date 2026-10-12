"""Finite consistency checks for the repaired denominator theorem.

The proof is in PROOF.md; these computations are not used as all-order proof.
"""
import importlib.util
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("qh", ROOT / "source/zeta7-port/qhankel.py")
qh = importlib.util.module_from_spec(spec)
spec.loader.exec_module(qh)


def exponents(K):
    out = []
    for d in range(1, K + 1):
        if 2 * d <= K:
            r = K // d
            c = (r + 1) // 2
            E = (c + 2) * K + (1 - c * c) * d
        else:
            t = K - d
            E = 6 * t + 3 + max(0, t - 1)
        out.append(E)
    return out


def cyclotomic_values(p, K):
    vals = [0]
    for n in range(1, K + 1):
        den = math.prod(vals[d] for d in range(1, n) if n % d == 0)
        assert (p**n - 1) % den == 0
        vals.append((p**n - 1) // den)
    return vals[1:]


def F(m):
    return sum(max(1, m + 2 - 2 * j) for j in range(m))


rows = []
for K in range(1, 401):
    ee = exponents(K)
    for d in range(1, K // 2 + 1):
        r, rem = divmod(K, d)
        exact = (d - rem) * F(r) + rem * F(r + 1)
        assert ee[d - 1] == exact
        # Rational arithmetic form of the variance-based bound.
        assert 16 * d * exact <= 4 * K * K + 32 * K * d + 17 * d * d

for p in (2, 3):
    for K in range(1, 21):
        a, b = qh.entries_q(3, p, K, 0, 1, K)
        Delta = qh.det_poly(K, a, b)
        coeffs = [Delta[i] for i in range(K + 1)]
        lcm = math.lcm(*(int(v.q) for v in coeffs))
        denominator_bound = math.prod(v**e for v, e in zip(cyclotomic_values(p, K), exponents(K)))
        assert math.gcd(lcm, p) == 1
        assert denominator_bound % lcm == 0
        rows.append({"p": p, "K": K, "denominator_bits": lcm.bit_length(),
                     "bound_bits": denominator_bound.bit_length(), "divides": True})
        print(json.dumps(rows[-1]), flush=True)

(Path(__file__).parent / "verification.json").write_text(json.dumps({
    "status": "all_checks_passed", "exact_cluster_exponents_checked_through_K": 400,
    "coefficient_denominator_divisibility": rows,
    "conservative_constant": 385 / (64 * math.pi**2),
    "sharper_constant": 1 / 8 + 19 / (4 * math.pi**2),
    "budget": 11 / 18,
}, indent=2) + "\n")
