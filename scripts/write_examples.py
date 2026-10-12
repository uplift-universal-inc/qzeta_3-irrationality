"""Write small exact coefficient certificates; these are finite checks only."""
from pathlib import Path
import hashlib
import json
import math
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "verification/source/zeta7-port"))
from qhankel import entries_q, det_poly, fmpq, fmpq_mat

rows = []
for p in (2, 3, 6):
    for K in range(1, 7):
        aa, bb = entries_q(3, p, K, 0, 1, K)
        delta = det_poly(K, aa, bb)
        exponent = K * (K * K - 1) // 2
        assert delta.degree() == K
        assert delta[K] == (-1) ** (K * (K - 1) // 2) * p ** exponent
        # K+1 distinct exact values determine a degree-at-most-K polynomial.
        for x in range(K + 1):
            matrix = fmpq_mat(K, K, [aa[i+j] + x*bb[i+j]
                                    for i in range(K) for j in range(K)])
            assert matrix.det() == delta(x)
        den = math.lcm(*(int(c.q) for c in delta))
        ints = [int(c * den) for c in delta]
        content = math.gcd(*ints)
        primitive = [c // content for c in ints]
        assert math.gcd(*primitive) == 1
        rows.append({"p": p, "K": K, "coefficient_order": "ascending",
                     "delta_rational_coefficients": [str(c) for c in delta],
                     "common_denominator": str(den),
                     "cleared_integer_content": str(content),
                     "primitive_integer_coefficients": [str(c) for c in primitive],
                     "base_content_exponent": exponent,
                     "direct_determinant_evaluations": K + 1})
result = {"status": "passed", "scope": "18 finite exact examples, not an all-size proof",
          "engine_sha256": hashlib.sha256((ROOT / "verification/source/zeta7-port/qhankel.py").read_bytes()).hexdigest(),
          "cases": rows}
out = ROOT / "certificates/coefficient-examples.json"
out.write_text(json.dumps(result, indent=2) + "\n")
print(f"Passed {len(rows)} exact coefficient examples; wrote {out.relative_to(ROOT)}")
