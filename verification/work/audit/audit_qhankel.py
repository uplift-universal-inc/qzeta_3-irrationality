"""Independent rigorous-tail and primitive-content audit of uploaded qhankel.py.
All JSON logarithms are approximate displays of outward-rounded Arb enclosures.
The determinant polynomial and its primitive normalization use exact FLINT rationals.
"""
import importlib.util,json,math,time,sys
from pathlib import Path
from flint import fmpz_poly,arb,ctx
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('qhankel',ROOT/'source/zeta7-port/qhankel.py')
q=importlib.util.module_from_spec(spec);spec.loader.exec_module(q)

def enclosure(s,p,prec):
    """Sum Lambert series and enclose positive infinite tail by geometric ratio.
    For f_n=n^(s-1)*p^-n, f_(n+1)/f_n <= rho=(1+1/(N+1))^(s-1)/p
    at n>=N+1. Also (1-p^-n)^-1 <= (1-p^-(N+1))^-1.
    """
    ctx.prec=prec
    # Summation extends far enough that the enclosure error is below roundoff.
    N=math.ceil((prec+64)*math.log(2)/math.log(p))+32*(s+1)
    total=arb(0)
    for n in range(1,N+1):
        total+=arb(n)**(s-1)/(arb(p)**n-1)
    rho=(arb(N+2)/arb(N+1))**(s-1)/p
    tail=arb(N+1)**(s-1)*arb(p)**(-N-1)/((1-arb(p)**(-N-1))*(1-rho))
    assert rho<1
    # Symmetric enclosure suffices; includes total plus every possible positive tail.
    return total+arb(0,tail),N,tail

def audit(s,p,K):
    t=time.time()
    a,b=q.entries_q(s,p,K,0,1,K)
    D=q.det_poly(K,a,b)
    den=math.lcm(*(int(x.q) for x in D))
    integer=[int(x.p)*(den//int(x.q)) for x in D]
    content=math.gcd(*integer)
    P=fmpz_poly([x//content for x in integer])
    old_g=math.gcd(*(int(x.p) for x in D))
    assert old_g==content
    assert math.gcd(*(int(x) for x in P))==1
    bits=max(abs(int(x)).bit_length() for x in P)
    prec=bits+8*K*K+256
    z,N,tail=enclosure(s,p,prec)
    val=arb(0)
    for c in reversed(list(P)): val=val*z+int(c)
    if val.contains(0):
        prec*=2;z,N,tail=enclosure(s,p,prec)
        val=arb(0)
        for c in reversed(list(P)):val=val*z+int(c)
    assert not val.contains(0),(s,p,K)
    row=dict(s=s,p=p,K=K,degree=P.degree(),primitive=True,
        original_normalization_correct=(old_g==content),nonzero_certified=True,
        sign=1 if val>0 else -1,precision_bits=prec,series_terms=N,
        tail_bound=tail.str(18),zeta_enclosure=z.str(24),value_enclosure=val.str(24),
        logabs=float(abs(val).log()),logabs_per_K3=float(abs(val).log())/K**3,
        log_den_per_K3=math.log(den)/K**3,log_content_per_K3=math.log(content)/K**3,
        content_v2=(content&-content).bit_length()-1,seconds=time.time()-t)
    if K<=6:row['coefficients']=[str(int(x)) for x in P]
    return row

if __name__=='__main__':
    specs=[tuple(map(int,x.split(':'))) for x in sys.argv[1:]] or [(3,2,k) for k in [1,2,3,4,5,6,8,12,16,24]]+[(s,2,12) for s in [1,2,4,5]]+[(3,p,12) for p in [3,5]]
    out=ROOT/'work/audit/results.jsonl'
    with out.open('w') as f:
        for s,p,K in specs:
            row=audit(s,p,K);f.write(json.dumps(row)+'\n');f.flush()
            print(json.dumps({k:row[k] for k in ['s','p','K','value_enclosure','logabs_per_K3','content_v2','seconds']}),flush=True)
