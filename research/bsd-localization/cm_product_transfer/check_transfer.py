#!/usr/bin/env python3
"""Exact cubic Euler transfer from an undepleted CM product to the DL input."""
from __future__ import annotations
import argparse
import itertools
import json
from pathlib import Path
import sympy as sp

HERE=Path(__file__).resolve().parent
ZERO=(0,0,0)
ONE=(1,0,0)
XI=(0,1,0)


def add(a,b,m):return tuple((x+y)%m for x,y in zip(a,b))
def scale(a,c,m):return tuple(c*x%m for x in a)
def mul(a,b,m):
    t=[0]*5
    for i,x in enumerate(a):
        for j,y in enumerate(b):t[i+j]+=x*y
    return ((t[0]+t[3]-t[4])%m,(t[1]+2*t[3]-t[4])%m,(t[2]-t[3]+3*t[4])%m)


def inv(a,m):
    # The fixed cubic is irreducible modulo5, so every nonzero residue
    # has a unique inverse. Lift it by Newton's identity, with exact
    # modular arithmetic and a final full-precision check.
    v=next(b for b in itertools.product(range(5),repeat=3) if mul(a,b,5)==ONE)
    q=5
    while q<m:
        q=min(q*q,m)
        v=mul(v,add(scale(ONE,2,q),scale(mul(a,v,q),-1,q),q),q)
    assert mul(a,v,m)==ONE
    return v


def mm(A,B,m):
    return [[add(mul(A[i][0],B[0][j],m),mul(A[i][1],B[1][j],m),m) for j in range(2)] for i in range(2)]


def smul(A,c,m):return [[mul(x,c,m) for x in row] for row in A]
def madd(A,B,m):return [[add(a,b,m) for a,b in zip(x,y)] for x,y in zip(A,B)]
def det(A,m):return add(mul(A[0][0],A[1][1],m),scale(mul(A[0][1],A[1][0],m),-1,m),m)
def const(n,m):return (n%m,0,0)
def valuation(a):
    assert any(a)
    answer=0
    while all(x%5==0 for x in a):
        answer+=1;a=tuple(x//5 for x in a)
    return answer


def compute():
    U,c,t=sp.symbols('U c t')
    R=(U**2-(c+1/c)*U+1)/(U*(U-(c+1/c)/2))
    average=(U/(U-c)+U/(U-1/c))/2
    assert sp.cancel(R*average-1)==0
    charpoly=U**2+3*U+5
    D=t*t+6*t+20
    N=5*t*t+18*t+25
    reduced=2*(6*U*(t+1)+5*t*t+33*t+58)/(5*D)
    difference=sp.together((U**2-t*U+1)/(U*(U-t/2))-reduced)
    assert sp.rem(sp.fraction(difference)[0],charpoly,U)==0
    inverse=5*(t*t+3*t+8)/(2*N)-3*(t+1)*U/N
    assert sp.rem(sp.fraction(sp.together(reduced*inverse-1))[0],charpoly,U)==0
    normD=int(sp.resultant(t**3+t*t-2*t-1,D,t))
    normN=int(sp.resultant(t**3+t*t-2*t-1,N,t))
    assert (normD,normN)==(6329,8737)

    f=json.loads((HERE.parent/'local_crystalline/result.json').read_text())
    m=f['modulus'];assert m==5**8
    F=[[const(x,m) for x in row] for row in f['frobenius_matrix']]
    I=[[ONE,ZERO],[ZERO,ONE]]
    Umat=smul(madd(F,smul(I,const(3,m),m),m),const(-1,m),m)
    tau=(1,m-1,m-1)
    tau2=mul(tau,tau,m)
    assert add(add(mul(tau2,tau,m),tau2,m),add(scale(tau,-2,m),const(-1,m),m),m)==ZERO
    d=add(add(tau2,scale(tau,6,m),m),const(20,m),m)
    n=add(add(scale(tau2,5,m),scale(tau,18,m),m),const(25,m),m)
    tau1=add(tau,ONE,m)
    scalar=add(add(scale(tau2,5,m),scale(tau,33,m),m),const(58,m),m)
    fiveR=smul(madd(smul(Umat,scale(tau1,6,m),m),smul(I,scalar,m),m),scale(inv(d,m),2,m),m)
    scalar2=add(add(tau2,scale(tau,3,m),m),const(8,m),m)
    Rinv=smul(madd(smul(I,scale(scalar2,5,m),m),smul(Umat,scale(tau1,-6,m),m),m),inv(scale(n,2,m),m),m)
    assert mm(fiveR,Rinv,m)==mm(Rinv,fiveR,m)==smul(I,const(5,m),m)
    assert mm(fiveR,Umat,m)==mm(Umat,fiveR,m)
    assert valuation(det(fiveR,m))==1
    assert min(valuation(x) for row in fiveR for x in row if any(x))==0
    assert valuation(det(Rinv,m))==1
    assert det(fiveR,m)==mul(scale(n,20,m),inv(d,m),m)

    alpha=2
    for digits in range(1,8):
        q=5**digits
        alpha=next(alpha+j*q for j in range(5) if ((alpha+j*q)**2+3*(alpha+j*q)+5)%(5*q)==0)
    beta=(-3-alpha)%m
    slope=[]
    for lam in (alpha,beta):
        value=mul(scale(add(scale(tau1,6*lam,m),scalar,m),2,m),inv(d,m),m)
        slope.append(value)
    assert valuation(slope[0])==1 and valuation(slope[1])==0
    return {'status':'PASS','coefficient_field_polynomial':[-1,-2,1,1],
            'tau_in_xi_basis':[1,-1,-1],'D_norm':normD,'N_norm':normN,
            'matrix_modulus':m,'five_times_R_matrix':fiveR,'inverse_R_matrix':Rinv,
            'five_times_R_eigenvalues_U_alpha_beta':slope,
            'five_times_R_eigenvalue_valuations':[1,0],
            'R_eigenvalue_valuations_U_alpha_beta':[0,-1],
            'R_inverse_is_integral':True,'worst_case_digit_loss':1,
            'lattice_scope':'U-stable (equivalently F-stable on E) integral lattice; any coordinate comparison has its own denominator cost',
            'scope':'Exact Euler transfer for proper E projections, given the CM cohomology identities in README. No raw q-series projection or arithmetic regulator comparison is inferred.'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check',action='store_true');p.add_argument('--write',action='store_true')
    args=p.parse_args();r=compute()
    # JSON normalizes tuples to arrays before certificate equality.
    r=json.loads(json.dumps(r))
    if args.check:assert r==json.loads((HERE/'transfer-result.json').read_text())
    if args.write:(HERE/'transfer-result.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(r,indent=2,sort_keys=True))


if __name__=='__main__':main()
