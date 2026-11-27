#!/usr/bin/env python3
"""Verify E433 finite CM/theta witnesses without importing the generator.

Class polynomials are reconstructed with rigorous FLINT/Arb balls.
All subsequent certificate checks use only exact integer arithmetic.
Published CM and theta comparison theorems remain mathematical inputs.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from math import comb, gcd, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parent
Q = 433
NONRESIDUE = 5


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(x, y, modulus):
    return ((x[0]+y[0]) % modulus, (x[1]+y[1]) % modulus)


def mul(x, y, modulus):
    return ((x[0]*y[0]+NONRESIDUE*x[1]*y[1]) % modulus,
            (x[0]*y[1]+x[1]*y[0]) % modulus)


def evaluate(coeffs, x, modulus):
    value = (0, 0)
    for c in reversed(coeffs):
        term = (c, 0) if isinstance(c, int) else c
        value = add(mul(value, x, modulus), term, modulus)
    return value


def product_from_roots(roots, modulus):
    coefficients = [(1, 0)]
    for x in roots:
        result = [(0, 0)]*(len(coefficients)+1)
        for i, c in enumerate(coefficients):
            result[i] = add(result[i], mul(c, (-x[0],-x[1]), modulus), modulus)
            result[i+1] = add(result[i+1], c, modulus)
        coefficients = result
    return coefficients


def phi2_coefficients(x, modulus):
    x2 = mul(x, x, modulus)
    x3 = mul(x2, x, modulus)
    def lin(*terms):
        return tuple(sum(c*z[i] for c,z in terms) % modulus for i in range(2))
    return [lin((1,x3),(-162000,x2),(8748000000,x),(-157464000000000,(1,0))),
            lin((1488,x2),(40773375,x),(8748000000,(1,0))),
            lin((-1,x2),(1488,x),(-162000,(1,0))), (1,0)]


def rank_mod(matrix, p):
    rows = [[int(v) % p for v in row] for row in matrix]
    rank = 0
    for col in range(len(rows[0])):
        pivot = next((j for j in range(rank,len(rows)) if rows[j][col]), None)
        if pivot is None:
            continue
        rows[rank],rows[pivot] = rows[pivot],rows[rank]
        inv = pow(rows[rank][col],-1,p)
        rows[rank] = [x*inv % p for x in rows[rank]]
        for j in range(rank+1,len(rows)):
            c = rows[j][col]
            rows[j] = [(a-c*b) % p for a,b in zip(rows[j],rows[rank])]
        rank += 1
    return rank


def class_polynomial(discriminant):
    from flint import acb, acb_poly, arb, ctx
    forms = []
    for a in range(1,isqrt(abs(discriminant)//3)+1):
        for b in range(-a,a+1):
            n = b*b-discriminant
            if n % (4*a):
                continue
            c = n//(4*a)
            if c < a or gcd(gcd(a,b),c) != 1:
                continue
            if b < 0 and (c == a or abs(b) == a):
                continue
            forms.append((a,b,c))
    with ctx.workprec(16384):
        root = arb(-discriminant).sqrt()
        polynomial = acb_poly([1])
        for a,b,c in forms:
            j = (acb(-b,root)/(2*a)).modular_j()
            polynomial *= acb_poly([-j,1])
        exact = polynomial.unique_fmpz_poly()
        require(exact is not None,'Class polynomial coefficients not uniquely isolated')
        coefficients = list(map(int,exact.coeffs()))
    require(len(coefficients)==len(forms)+1,'Class number/degree mismatch')
    return coefficients


def hash_coefficients(coefficients):
    return hashlib.sha256(json.dumps(coefficients,separators=(',',':')).encode()).hexdigest()


def valuation(x, bound=80):
    if x == 0:
        return bound
    v = 0
    while x % Q == 0:
        x //= Q
        v += 1
    return v


def pair_valuation(x):
    return min(map(valuation,x))


def supersingular(data):
    require(pow(NONRESIDUE,(Q-1)//2,Q)==Q-1,'Extension is not a field')
    js = [tuple(j) for j in data['supersingular_j']]
    roots = [tuple(r) for r in data['deuring_roots']]
    require(all(len(x)==2 and all(type(c) is int and 0<=c<Q for c in x)
                for x in js+roots),'Noncanonical finite-field element')
    require(len(js)==len(set(js))==36,'Incorrect supersingular vertex count')
    degree = (Q-1)//2
    require(len(roots)==len(set(roots))==degree,'Incomplete Deuring roots')
    polynomial = [comb(degree,k)**2 % Q for k in range(degree+1)]
    derived = set()
    for r in roots:
        require(evaluate(polynomial,r,Q)==(0,0),'Invalid Deuring root')
        r2 = mul(r,r,Q)
        u = add(add(r2,(-r[0],-r[1]),Q),(1,0),Q)
        numerator = mul(mul(u,u,Q),u,Q)
        denominator = mul(r2,mul((1-r[0],-r[1]),(1-r[0],-r[1]),Q),Q)
        a,b = denominator
        z = pow((a*a-NONRESIDUE*b*b) % Q,-1,Q)
        result = mul(numerator,(a*z % Q,-b*z % Q),Q)
        derived.add((256*result[0] % Q,256*result[1] % Q))
    require(derived==set(js),'Supersingular list does not match Deuring roots')
    matrix = data['T2_matrix']
    require(len(matrix)==36 and all(len(row)==36 for row in matrix),'Wrong Brandt shape')
    for j,row in zip(js,matrix):
        require(all(type(n) is int and 0<=n<=3 for n in row) and sum(row)==3,'Bad edge counts')
        neighbors = [js[i] for i,n in enumerate(row) for _ in range(n)]
        require(product_from_roots(neighbors,Q)==phi2_coefficients(j,Q),'Bad modular polynomial factorization')
    vector = data['primitive_eigenfunction']
    require(len(vector)==36 and gcd(*vector)==1,'Nonprimitive function')
    require(data['T2_eigenvalue']==-1,'Wrong declared eigenvalue')
    require(all(sum(row[j]*vector[j] for j in range(36))==-vector[i]
                for i,row in enumerate(matrix)),'Wrong eigenfunction')
    rank = rank_mod([[matrix[i][j]+int(i==j) for j in range(36)] for i in range(36)],101)
    require(rank==35,'Eigenline not isolated over Q')
    points = 1+sum((y*y+x*y-x*x*x-1) % 2==0 for x in range(2) for y in range(2))
    require(3-points==-1,'Curve T2 mismatch')
    values = dict(zip(js,vector))
    require(all(values[(a,-b % Q)]==values[(a,b)] for a,b in js),'Wrong Frobenius action')
    return values,{'supersingular_vertices':36,'complete_Deuring_roots':216,'T2_rank_mod101':rank,
                  'rational_eigenline_dimension':1}


def cm_witness(data,coefficients,values):
    degree = len(coefficients)-1
    require(data['class_number']==degree,'Wrong root count metadata')
    require(data['class_polynomial_sha256']==hash_coefficients(coefficients),'Wrong class polynomial')
    lifts = data['root_lifts']
    require(len(lifts)==degree and all(len(r)==2 and all(type(x) is int for x in r) for r in lifts),'Bad lifts')
    require(data['root_precision']==4,'Unreviewed root precision')
    m = Q**4
    roots = [(a % m,b % m) for a,b in lifts]
    require(len(set(roots))==degree,'Root balls not disjoint')
    derivative = [i*coefficients[i] for i in range(1,len(coefficients))]
    hensel = []
    for r in lifts:
        h = pair_valuation(evaluate(coefficients,r,Q**80))
        s = pair_valuation(evaluate(derivative,r,Q**80))
        require(h>2*s and h-s>=4,'Insufficient strong Hensel precision')
        hensel.append([h,s])
    require(hensel==data['hensel_valuations'],'Incorrect Hensel receipt')
    graph = [[j for j,y in enumerate(roots) if evaluate(phi2_coefficients(x,m),y,m)==(0,0)] for x in roots]
    require(all(len(row)==2 for row in graph),'Horizontal neighbors not isolated')
    require(all(i in graph[j] for i,row in enumerate(graph) for j in row),'Nonsymmetric CM graph')
    require(graph==data['horizontal_T2_graph'],'Stored graph mismatch')
    cycle = data['generator_cycle']
    require(sorted(cycle)==list(range(degree)),'Cycle is not a permutation')
    require(all(cycle[(i+1)%degree] in graph[cycle[i]] for i in range(degree)),'Invalid generator cycle')
    weights = [values[(roots[i][0] % Q,roots[i][1] % Q)] for i in cycle]
    require(weights==data['CM_values'],'Wrong CM values')
    result = {'D':data['discriminant'],'classes':degree,'class_polynomial_sha256':hash_coefficients(coefficients),
              'max_derivative_valuation':max(s for h,s in hensel),'sum':sum(weights)}
    if degree==7:
        require(sum(weights)==0 and len(set(weights))>1,'Trivial or auxiliary toric test failed')
        result['CM_values'] = weights
    else:
        grouped = [sum(weights[j::5]) for j in range(5)]
        coefficients = [sum(grouped[j]*comb(j,k) for j in range(5)) for k in range(5)]
        require(grouped==data['grouped_coefficients'],'Wrong grouped coefficients')
        require(coefficients==data['raw_T_coefficients'],'Wrong exact moments')
        require([c % 5 for c in coefficients]==data['raw_T_coefficients_mod5'],'Wrong reduced moments')
        require(coefficients[:2]==[0,0] and coefficients[2] % 5!=0,'Quadratic certificate failed')
        result.update({'grouped_coefficients':grouped,'raw_T_coefficients':coefficients,
                       'quadratic_coefficient_mod5':coefficients[2] % 5})
    return result


def verify(data,polynomials):
    require(data['curve']=={'label':'433.a1','ainvs':[1,0,0,0,1],'conductor':433},'Wrong curve')
    require(data['reduction_field']=={'prime':433,'nonresidue':5},'Wrong reduction field')
    require(data['iwasawa_prime']==5,'Wrong Iwasawa prime')
    values,ss = supersingular(data['supersingular'])
    require([c['discriminant'] for c in data['CM']]==[-71,-44375],'Wrong CM discriminants')
    results = [cm_witness(c,polynomials[c['discriminant']],values) for c in data['CM']]
    return {'status':'PASS','curve':'433.a1','supersingular':ss,'CM':results,
            'class_polynomial_working_bits':16384,
            'scope':'Rigorous class-polynomial reconstruction and exact finite Brandt, Hensel, CM-cycle and theta-moment witnesses. Published arithmetic interpretation remains a written argument.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,default=ROOT/'certificate.json')
    parser.add_argument('--check',type=Path)
    parser.add_argument('--write',type=Path)
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text())
    polynomials = {d:class_polynomial(d) for d in (-71,-44375)}
    result = verify(data,polynomials)
    result['certificate_sha256'] = hashlib.sha256(args.certificate.read_bytes()).hexdigest()
    if args.check:
        require(result==json.loads(args.check.read_text()),'Fresh result differs from saved receipt')
    if args.write:
        args.write.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
