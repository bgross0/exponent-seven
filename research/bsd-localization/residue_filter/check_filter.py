#!/usr/bin/env python3
"""Exact arithmetic certificate for the U5^2-1 residue filter at level389."""
import argparse
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent


def mm(a,b,m):
    return [[sum(a[i][k]*b[k][j] for k in range(2))%m for j in range(2)] for i in range(2)]


def plus(a,b,m):
    return [[(a[i][j]+b[i][j])%m for j in range(2)] for i in range(2)]


def scale(a,c,m):
    return [[c*x%m for x in row] for row in a]


def det(a,m):
    return (a[0][0]*a[1][1]-a[0][1]*a[1][0])%m


def projective(a,b,p):
    if a%p:
        return b*pow(a,-1,p)%p
    assert b%p
    return p


def act(A,line,p):
    a,b=(0,1) if line==p else (1,line)
    return projective(A[0][0]*a+A[0][1]*b,A[1][0]*a+A[1][1]*b,p)


def compute():
    # j=0 supersingular curve at5, with trace0 and therefore pi^2=[-5].
    points=1+sum((y*y-x**3-1)%5==0 for x in range(5) for y in range(5))
    assert points==6
    ell=389
    T=[[0,-1],[1,-1]]
    I=[[1,0],[0,1]]
    assert mm(mm(T,T,ell),T,ell)==I
    assert all(act(T,line,ell)!=line for line in range(ell+1))
    unused=set(range(ell+1));orbits=[]
    while unused:
        a=min(unused);b=act(T,a,ell);c=act(T,b,ell)
        orbit={a,b,c}
        assert len(orbit)==3 and act(T,c,ell)==a
        orbits.append(sorted(orbit));unused-=orbit
    assert len(orbits)==130
    # q-Frobenius on the pair (j=0 curve, cyclic389 subgroup) squares
    # to a scalar on its torsion, hence each geometric point is F25-rational.
    # This finite orbit certificate checks the degree of the supersingular divisor.
    source=json.loads((ROOT.parent/"local_crystalline/result.json").read_text())
    F=source["frobenius_matrix"]
    modulus=source["modulus"]
    assert modulus==5**8 and F==[[285070,163221],[276685,105552]]
    assert (F[0][0]+F[1][1])%modulus==(-3)%modulus
    assert det(F,modulus)==5
    assert plus(plus(mm(F,F,modulus),scale(F,3,modulus),modulus),scale(I,5,modulus),modulus)==[[0,0],[0,0]]
    U=scale(plus(F,scale(I,3,modulus),modulus),-1,modulus)
    assert mm(U,F,modulus)==scale(I,5,modulus)
    R=plus(mm(U,U,modulus),scale(I,-1,modulus),modulus)
    assert R==scale(plus(F,I,modulus),3,modulus)
    assert det(R,modulus)==27
    inverse=scale(plus(F,scale(I,2,modulus),modulus),-pow(9,-1,modulus),modulus)
    assert mm(R,inverse,modulus)==mm(inverse,R,modulus)==I
    # Verify exact polynomial identities over Z[X]/(X^2+3X+5), with
    # X representing F. (X+1)(-X-2)=3; (X+3)^2-1=3(X+1).
    def multiply(a,b):
        c0=a[0]*b[0]-5*a[1]*b[1]
        c1=a[0]*b[1]+a[1]*b[0]-3*a[1]*b[1]
        return (c0,c1)
    assert multiply((1,1),(-2,-1))==(3,0)
    square=multiply((-3,-1),(-3,-1))
    assert (square[0]-1,square[1])==(3,3)
    return {
        'status':'PASS',
        'prime':5,'level':389,
        'j0_curve_point_count_F5':points,
        'j0_curve_frobenius_trace':0,
        'cyclic389_subgroups':390,
        'automorphism_orbit_size':3,
        'supersingular_divisor_degree':len(orbits),
        'supersingular_field_of_definition':'F25',
        'rational_cusps':2,
        'proper_cohomology_dimension':64,
        'residue_quotient_dimension':131,
        'open_cohomology_dimension':195,
        'residue_annihilator':'U5^2-1',
        'U5_on_E':'-F-3I',
        'filter_on_E':'3(F+I)',
        'filter_determinant_on_E':27,
        'inverse_filter_on_E':'-(F+2I)/9',
        'inverse_filter_digit_loss':0,
        'digit_loss_lattice':'an F_E-stable integral lattice; changing from a merely Hecke-stable lattice has a separate denominator cost',
        'matrix_modulus':modulus,
        'F_matrix':F,
        'U_matrix':U,
        'filter_matrix':R,
        'inverse_filter_matrix':inverse,
        'projection_formula':'Pi_E(proper(z))=-(F_E+2I)/9 * P_E((U5^2-1)z)',
        'coefficient_convention':'geometric Q5-linear Frobenius extended L-linearly; do not apply unramified Frobenius to external coefficients',
        'scope':'Exact residue and elliptic filter arithmetic, using the geometric residue sequence and Frobenius interpretation explained in README. No reduction of a new overconvergent input or nonzero logarithm is computed.'
    }


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check',action='store_true');p.add_argument('--write',action='store_true')
    args=p.parse_args();r=compute()
    if args.check:assert r==json.loads((ROOT/'result.json').read_text())
    if args.write:(ROOT/'result.json').write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(r,indent=2,sort_keys=True))


if __name__=='__main__':main()
