"""Exact-integer Python prototype of Lean-style packed search certificates.
Run from repository root:
python Exp7Lean/sieve-reduction/packed_multi.py ladder.txt 2767 17 skip 4
python Exp7Lean/sieve-reduction/packed_multi.py ladder.txt 2767 17 all 1
The output is a benchmark, not a formal certificate. Requires sympy.
"""
import json,sys,math,time
from functools import lru_cache
from multiprocessing import Pool
from pathlib import Path
from sympy import primerange,sqrt_mod

def tiled(b,l,n):
    width=l
    while width<n:
        b|=b<<width;width*=2
    return b

def one(args):
    p,y,S,Q,wmax,skip,ps=args
    m=8*y*y; xmax=math.isqrt(S-Q*y*y)
    roots=sqrt_mod((S-3*y*y)%m,m,all_roots=True)
    counts=dict(y=y,roots=0,blocks=0,bits=0,ands=0,and_bits=0,max_block=0,max_eliminator=0,survivors=[])
    used=[l for l in ps if not (skip and y%l==0)]
    residue={l:tuple(pow(a,(l-1)//2,l)==l-1 for a in range(l)) for l in used}
    wheel=[l for l in used if l<=wmax];tail=[l for l in used if l>wmax]
    W=math.prod(wheel)
    for r in roots:
        r=int(r)
        if r>xmax:continue
        counts['roots']+=1
        T=(xmax-r)//m+1
        q0=(S-r*r)//(y*y)
        def good(l,t):return residue[l][(-q0+16*r*t+64*y*y*t*t)%l]
        rs=[0];w=1
        for l in wheel:
            allowed=[t for t in range(l) if good(l,t)]
            inv=pow(w,-1,l)
            rs=[u+w*((a-u)*inv%l) for u in rs for a in allowed]
            w*=l
            if not rs:break
        if not rs:continue
        assert w==W
        N=(T+W-1)//W
        counts['max_block']=max(counts['max_block'],N)
        @lru_cache(None)
        def pattern(l):
            b=sum(1<<k for k in range(l) if good(l,W*k))
            return tiled(b,l,N+l),pow(W,-1,l)
        @lru_cache(maxsize=max(8,min(512,64000000//max(1,N))))
        def shift(l,phase):return pattern(l)[0]>>phase
        for rho in rs:
            if rho>=T:continue
            n=(T-1-rho)//W+1
            a=(1<<n)-1
            counts['blocks']+=1;counts['bits']+=n
            for l in tail:
                pat,inv=pattern(l)
                a &= shift(l,(rho*inv)%l)
                counts['ands']+=1;counts['and_bits']+=n
                if not a:
                    counts['max_eliminator']=max(l,counts['max_eliminator']);break
            while a:
                b=a&-a;k=b.bit_length()-1;a^=b
                t=rho+W*k;x=r+m*t;q=(S-x*x)//(y*y)
                counts['survivors'].append([p,y,x,q])
        pattern.cache_clear();shift.cache_clear()
    return counts

def main():
    base,*rows=Path(sys.argv[1]).read_text().splitlines();base=int(base);rows=[tuple(map(int,r.split())) for r in rows]
    p=int(sys.argv[2]);wmax=int(sys.argv[3]) if len(sys.argv)>3 else 17;skip=len(sys.argv)>4 and sys.argv[4]=='skip';jobs=int(sys.argv[5]) if len(sys.argv)>5 else 1
    S=4*p**7;Q=max([base]+[q for X,q in rows if X<=p]);Y=math.isqrt(S//Q)
    ps=list(primerange(3,p));start=time.monotonic()
    tasks=[(p,y,S,Q,wmax,skip,ps) for y in range(1,Y+1)]
    if jobs>1:
        with Pool(jobs) as pool: out=list(pool.imap_unordered(one,tasks,chunksize=1))
    else:out=list(map(one,tasks))
    result=dict(p=p,Qlo=Q,ymax=Y,wheel=wmax,skip=skip,jobs=jobs,elapsed_s=time.monotonic()-start,**{k:sum(d[k] for d in out) for k in ['roots','blocks','bits','ands','and_bits']},max_block=max((d['max_block'] for d in out),default=0),max_eliminator=max((d['max_eliminator'] for d in out),default=0),survivors=[s for d in out for s in d['survivors']],per_y=sorted(out,key=lambda d:d['y']))
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
