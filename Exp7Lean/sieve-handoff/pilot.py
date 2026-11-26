"""Prototype packed-bit certificate for p=701, y=1 (not a Lean proof)."""
from math import isqrt
from time import monotonic
from hashlib import sha256
from json import dumps
P=701; S=4*P**7; Q=31*10**19
assert isqrt(S//Q)==1
X=isqrt(S-Q); T=(X+1)//2 # x=2t+1, 0<=t<T
assert T>0 and 2*(T-1)+1<=X<2*T+1
# The wheel is small enough to be verified by finite enumeration in Lean.
wheel=(3,5,7,11,13,17)
W=1
for l in wheel: W*=l
ps=[l for l in range(3,P,2) if all(l%d for d in range(2,isqrt(l)+1))]
def good(x,l): return pow((x*x-S)%l,(l-1)//2,l)==l-1
rs=[r for r in range(W) if all(good(2*r+1,l) for l in wheel)]
def repeat(mask,l,n):
    # concatenate a whole number of copies using exact geometric series
    k=(n+l-1)//l
    return mask*((1<<(k*l))-1)//((1<<l)-1)
# Per l, cache masks for phase r mod l, using t=r+W*k.
N=(T+W-1)//W
patterns={}
for l in ps:
    if l in wheel: continue
    base=sum(1<<k for k in range(l) if good(2*W*k+1,l))
    # phase in k shifts by r/W mod l; extend at least l extra bits
    patterns[l]=(repeat(base,l,N+l),pow(W,-1,l))
start=monotonic(); counts={}; tested=0; max_used=0; survivors=[]
for r in rs:
    if r>=T:continue
    n=(T-1-r)//W+1
    a=(1<<n)-1
    for l,(pat,inv) in patterns.items():
        a &= pat >> (r*inv%l)
        if not a:
            counts[l]=counts.get(l,0)+1; max_used=max(max_used,l);break
    if a:survivors.append((r,a.bit_count()))
    tested+=n
assert not survivors
print(dumps(dict(p=P,y=1,xmax=X,tcount=T,wheel=W,wheel_primes=wheel,wheel_residues=len(rs),positions_after_wheel=tested,zero_survivors=True,last_prime_needed=max_used,elimination_histogram=counts,elapsed_s=monotonic()-start),indent=2))
