from fractions import Fraction as F
from math import comb
# Machin: pi=16 atan(1/5)-4 atan(1/239); alternating series enclosure.
def atan_bounds(d, n=40):
    a=sum((F((-1)**k,(2*k+1)*d**(2*k+1)) for k in range(n)),F(0))
    b=a+F((-1)**n,(2*n+1)*d**(2*n+1))
    return min(a,b),max(a,b)
a,b=atan_bounds(5); c,d=atan_bounds(239)
pi=(16*a-4*d,16*b-4*c)
# log 2 = 2 sum_{k>=0} 1/((2k+1)*3^(2k+1)).
m=80; l=2*sum((F(1,(2*k+1)*3**(2*k+1)) for k in range(m)),F(0))
u=l+2*F(1,(2*m+1)*3**(2*m+1))*F(9,8)
# Euler-Maclaurin harmonic expansion, enveloping remainder <= next term.
# gamma=H_N-log N-1/(2N)+sum B_{2k}/(2k*N^(2k)) + remainder.
N=128; B=[F(1)]
for k in range(1,23): B.append(-sum((comb(k+1,j)*B[j] for j in range(k)),F(0))/F(k+1))
g=sum((F(1,k) for k in range(1,N+1)),F(0))-F(1,2*N)+sum((B[2*k]/(2*k*N**(2*k)) for k in range(1,11)),F(0))
r=abs(B[22]/(22*N**22))
gamma=(g-7*u-r,g-7*l+r)
S=10**30
for name,(lo,hi),a,b in [('pi',pi,3141592653589793238462643383279,3141592653589793238462643383280),('gamma',gamma,577215664901532860606512090082,577215664901532860606512090083)]:
    assert F(a,S)<=lo<=hi<=F(b,S),(name,float(lo),float(hi))
    print(name,'certified 30-decimal enclosure',a,b,flush=True)
