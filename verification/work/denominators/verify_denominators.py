"""Exact finite regression checks for the proved cyclotomic denominator bound.
These supplement, and do not replace, the proof in PROOF.md.
"""
import json, math, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'source' / 'zeta7-port'))
from qhankel import entries_q, det_poly

def phi_values(p, K):
    values = {}
    for d in range(1, K+1):
        values[d] = (p**d - 1) // math.prod(values[e] for e in range(1, d) if d % e == 0)
    return values

def bound(K, d):
    if 2*d <= K:
        num, den = 4*K*K + 32*K*d + 17*d*d, 16*d
        return (num + den - 1)//den
    return 5*(K-d)+3

rows=[]
for p in [2,3,4,5]:
    values = phi_values(p, 24)
    for K in range(1,25):
        a,b=entries_q(3,p,K,0,1,K)
        Delta=det_poly(K,a,b)
        ell=math.lcm(*(int(c.q) for c in Delta))
        residue=1%ell
        for d in range(1,K+1):
            residue=residue*pow(values[d],bound(K,d),ell)%ell
        ok=(residue==0)
        assert ok,(p,K)
        rows.append({'p':p,'K':K,'denominator_bits':ell.bit_length(),'denominator_bound_divisible':ok})
    print(f'p={p}: all K=1..24 passed',flush=True)
result={'status':'passed','cases':len(rows),'bound_constant':321/(64*math.pi**2),
        'margin_11_over_18':11/18-321/(64*math.pi**2),'rows':rows}
Path(__file__).with_name('verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='rows'}))
