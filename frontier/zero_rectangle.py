"""Outward-rounded local zero-obstruction pilot. Requires mpmath, sympy.
Run with no arguments to check all four rows, or X Qmin Qmax for one row.
This is external numerical verification, not a Lean theorem.
"""
from mpmath import iv
from sympy import primerange
import json,sys
from fractions import Fraction as F
from math import comb
iv.dps=45
I=iv.mpf
aa=F(99,200);bb=F(1,200);nn=2*aa-2*bb
shifts={}
for c,k in zip((-1,4,-6,4,-1),(-2*aa,-aa,F(0),aa,2*aa)):
    for d,j in ((1,k-2*bb),(-2,k),(1,k+2*bb)):
        shifts[j]=shifts.get(j,0)+c*d
breaks=sorted({F(0),F(1),*(j for j in shifts if 0<j<1)})
def rat(x):return I(x.numerator)/I(x.denominator)
bp=list(map(rat,breaks));polys=[]
for lo in breaks[:-1]:
    cs=[F(0)]*4
    for j,c in shifts.items():
        if j<=lo:
            for k in range(4):cs[k]+=c*comb(3,k)*(-j)**(3-k)/(24*bb*bb*nn)
    polys.append(list(map(rat,cs)))
def cosh(t):return (iv.exp(t)+iv.exp(-t))/2
def sinh(t):return (iv.exp(t)-iv.exp(-t))/2
scale=10**6
def enclose(z):
    def floor_endpoint(w):
        sign,man,exp,_=w._mpi_[0]; num=(-1 if sign else 1)*man*scale
        return (num<<exp) if exp>=0 else num//(1<<(-exp))
    return [floor_endpoint(z.a),-floor_endpoint(-z.b)]
def check(X,Qmin,Qmax):
    assert 4*X**7<Qmin<=Qmax
    L=iv.log(I(X)); b=L/200; a=L/2-b; N=2*a-2*b
    assert 2*b<a
    def f(u):
        t=u/L;vals=[]
        for j,cs in enumerate(polys):
            if t.b<bp[j].a or t.a>bp[j+1].b:continue
            z=I(0)
            for c in reversed(cs):z=z*t+c
            vals.append(z)
        assert vals
        return vals[0] if len(vals)==1 else I([min(z.a for z in vals),max(z.b for z in vals)])
    assert f(I(0)).a<=1<=f(I(0)).b
    P=I(0);terms=0
    for p in map(int,primerange(2,X)):
        n=p;sign=-1
        while n<X:
            P+=2*sign*iv.log(I(p))*f(iv.log(I(n)))/iv.sqrt(I(n))
            terms+=1;n*=p;sign=-sign
    J=14/(3*N)
    gamma=I(['0.577215664901532860606512090082','0.577215664901532860606512090083'])
    const=iv.log(iv.pi)+gamma-iv.pi/2+3*iv.log(I(2))
    margin=P-J+const-iv.log(I(Qmax))
    D=I(1)/100;T=I(1000)
    A=(2*a*sinh(D*L/2))**2/N
    B=(4*sinh(D*L/2)+2*a*D*cosh(D*L/2))**2/N
    C=4*(1+cosh(a/2))**2*cosh(b/2)**2/(N*b*b)
    Z=iv.log(I(Qmax))+4
    low=(A+B)*Z;high=C*(1+T*T)/T**4*Z
    residual=margin-low-high
    assert residual.a>0
    return dict(X=X,Qmin=str(Qmin),Qmax=str(Qmax),terms=terms,delta='1/100',height=1000,scale=scale,prime_sum=enclose(P),J_upper_enclosure=enclose(J),margin=enclose(margin),weighted_zero_mass_upper_enclosure=enclose(Z),low_zero_loss_upper_enclosure=enclose(low),high_zero_loss_upper_enclosure=enclose(high),residual=enclose(residual),status='positive interval margin; analytic derivation requires review and Lean formalization')
if __name__=='__main__':
    rows=[tuple(map(int,sys.argv[1:]))] if len(sys.argv)>1 else [(19000,39*10**29,10**32),(30000,10**32,10**40),(100000,10**40,10**60),(1000000,10**60,10**162)]
    assert all(a[2]==b[1] for a,b in zip(rows,rows[1:]))
    print(json.dumps([check(*row) for row in rows],indent=2))
