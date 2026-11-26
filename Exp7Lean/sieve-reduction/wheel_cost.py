"""Conservative counts for alternative CRT wheels, using the actual roots.
Run from repo root: python Exp7Lean/sieve-reduction/wheel_cost.py ladder.txt Exp7Lean/sieve-reduction/robust26.txt
SymPy root generation is used only for this external cost model, not as a proof.
"""
import math,json,sys
from sympy import sqrt_mod, primerange
from pathlib import Path
base,*rows=Path(sys.argv[1]).read_text().splitlines();base=int(base);rows=[tuple(map(int,r.split())) for r in rows]
robust=[tuple(map(int,r.split()[:3])) for r in Path(sys.argv[2]).read_text().splitlines() if r.strip()]
wheels=[tuple(primerange(3,n+1)) for n in (11,13,17,19,23)]
ps=list(primerange(701,4298))

def run(rob,unified,period):
    totals=[dict(last_prime=w[-1],modulus=math.prod(w),blocks_upper=0,bits_upper=0,roots=0,max_block_bits=0,partial_roots=0) for w in wheels]
    yy=active=0
    for p in ps:
        S=4*p**7
        Q=max([base]+[q for X,q in rows if X<=p]+([q for T,X,q in robust if T<=p] if rob else []))
        Y=math.isqrt(S//Q);yy+=Y;active+=bool(Y)
        good={l:sum(pow((x*x-S)%l,(l-1)//2,l)==l-1 for x in range(l)) for l in wheels[-1]}
        for y in range(1,Y+1):
            m=period*y*y;X=math.isqrt(S-Q*y*y)
            rs=sorted(set(int(r)%m for r in sqrt_mod((S-3*y*y)%(8*y*y),8*y*y,all_roots=True)))
            for r in rs:
                if r>X:continue
                assert (r*r-(S-3*y*y))%(8*y*y)==0
                T=(X-r)//m+1;q0=(S-r*r)//(y*y)
                for w,d in zip(wheels,totals):
                    if unified:
                        ls=w;A=math.prod(good[l] if y%l else sum(pow((-q0+2*r*period*t+period**2*y*y*t*t)%l,(l-1)//2,l)==l-1 for t in range(l)) for l in ls)
                    else:
                        ls=[l for l in w if y%l];A=math.prod(good[l] for l in ls)
                    W=math.prod(ls);N=(T+W-1)//W
                    d['blocks_upper']+=min(A,T);d['bits_upper']+=A*N
                    d['roots']+=1;d['max_block_bits']=max(d['max_block_bits'],N);d['partial_roots']+=T<W
    return dict(robust=rob,unified=unified,root_period=period,active_primes=active,y_count=yy,totals=totals)
if __name__=='__main__':print(json.dumps([run(False,False,8),run(False,False,2),run(False,True,2),run(True,True,2)],indent=2))
