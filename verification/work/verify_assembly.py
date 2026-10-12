"""Finite exact checks of the repaired all-size proof; not its proof."""
import sys, json, math, time
from pathlib import Path
from fractions import Fraction
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source/zeta7-port'))
import qhankel

def ceilfrac(a,b):return (a+b-1)//b
def exponents(K):
    return [ceilfrac(4*K*K+32*K*d+17*d*d,16*d) if 2*d<=K else 7*(K-d)+3 for d in range(1,K+1)]
def phis(p,K):
    ans=[1]
    for d in range(1,K+1):
        a=p**d-1
        for e in range(1,d):
            if d%e==0:a//=ans[e]
        ans.append(a)
    return ans

def check(p,K):
    a,b=qhankel.entries_q(3,p,K,0,1,K)
    D=qhankel.det_poly(K,a,b)
    E=K*(K*K-1)//2
    factors=phis(p,K)
    C=math.prod(factors[d]**exponents(K)[d-1] for d in range(1,K+1))
    C_strong=math.prod(factors[d]**(exponents(K)[d-1] if 2*d<=K else 5*(K-d)+3) for d in range(1,K+1))
    den=math.lcm(*(int(c.q) for c in D))
    content=math.gcd(*(int(c.p) for c in D))
    assert C%den==0
    assert C_strong%den==0
    assert content==p**E
    assert all((c*C/p**E).q==1 for c in D)
    assert all((c*C_strong/p**E).q==1 for c in D)
    assert D[K]==(-1)**(K*(K-1)//2)*p**E
    return dict(p=p,K=K,denominator_divides_bound=True,stronger_denominator_divides_bound=True,content_exact=True,integral_normalized_polynomial=True,degree=K)

rows=[]
for p,Kmax in [(2,30),(3,16),(4,12),(5,12),(6,10),(9,8)]:
    for K in range(1,Kmax+1):rows.append(check(p,K))

weight_checks=0
for K in range(1,501):
    for d in range(1,K//2+1):
        h,t=divmod(K,d)
        F=lambda m:sum(max(1,m+2-2*j) for j in range(m))
        exact=(d-t)*F(h)+t*F(h+1)
        assert exact<=exponents(K)[d-1]
        weight_checks+=1
out=dict(status='all finite checks passed',scope='Finite consistency evidence, not a substitute for the all-size written proofs.',exact_determinants=len(rows),cluster_weight_checks=weight_checks,denominator_constant=385/(64*math.pi**2),positive_margin=11/18-385/(64*math.pi**2),stronger_denominator_constant=321/(64*math.pi**2),stronger_positive_margin=11/18-321/(64*math.pi**2),rational_positive_margin_using_pi_gt_157_over_50=str(Fraction(11,18)-Fraction(385,64)/Fraction(157,50)**2),checks=rows)
(ROOT/'work/assembly_verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))
