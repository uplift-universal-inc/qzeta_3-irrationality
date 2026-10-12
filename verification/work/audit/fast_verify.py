"""Exact Lambert-series coefficient summation, avoiding high-precision division per term."""
import sys,math,time,json
from pathlib import Path
from flint import arb,ctx
sys.path.insert(0,str(Path(__file__).parent))
import audit_qhankel as a

def fast_enclosure(s,p,prec):
    ctx.prec=prec
    N=math.ceil((prec+64)*math.log(2)/math.log(p))+32*(s+1)
    # sigma_(s-1)(n) <= n^s for all s>=1 suffices for the tail.
    sigma=[0]*(N+1)
    for d in range(1,N+1):
        w=d**(s-1)
        for n in range(d,N+1,d):sigma[n]+=w
    total=0
    for n in range(1,N+1):total=p*total+sigma[n]
    series=arb(total)/(arb(p)**N)
    rho=(arb(N+2)/arb(N+1))**s/p
    tail=arb(N+1)**s*arb(p)**(-N-1)/(1-rho)
    assert rho<1
    return series+arb(0,tail),N,tail

if __name__=='__main__':
    # Check independent representations against one another at modest precision.
    for s in range(1,6):
        x,_,_=a.enclosure(s,2,400);y,_,_=fast_enclosure(s,2,400)
        assert x.overlaps(y)
    a.enclosure=fast_enclosure
    K=int(sys.argv[1]) if len(sys.argv)>1 else 60
    row=a.audit(3,2,K)
    Path(__file__).with_name(f'fast_K{K}.json').write_text(json.dumps(row,indent=2))
    print(json.dumps({k:row[k] for k in ['K','value_enclosure','logabs_per_K3','precision_bits','series_terms','seconds']}),flush=True)
