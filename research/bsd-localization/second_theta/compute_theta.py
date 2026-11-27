#!/usr/bin/env python3
"""Generate exact finite CM/theta witnesses for E433; verify separately."""
from __future__ import annotations
import argparse
import hashlib
import json
from math import comb, gcd, isqrt, lcm
from pathlib import Path
import time
from flint import acb, acb_poly, arb, ctx, fq_default_ctx, fq_default_poly_ctx, fmpz_mod_poly_ctx
import sympy as sp

Q, D = 433, 5
FIELD = fq_default_ctx(modulus=fmpz_mod_poly_ctx(Q)([-D, 0, 1]))
POLYS = fq_default_poly_ctx(FIELD)

def add(x,y,m):
    return ((x[0]+y[0])%m,(x[1]+y[1])%m)

def mul(x,y,m):
    return ((x[0]*y[0]+D*x[1]*y[1])%m,(x[0]*y[1]+x[1]*y[0])%m)

def scale(c,x,m):
    return (c*x[0]%m,c*x[1]%m)

def inverse(x,m):
    z=pow((x[0]*x[0]-D*x[1]*x[1])%m,-1,m)
    return (x[0]*z%m,-x[1]*z%m)

def evaluate(coefficients,x,m):
    value=(0,0)
    for c in reversed(coefficients):
        value=add(mul(value,x,m),(c,0) if isinstance(c,int) else c,m)
    return value

def valuation(x,bound):
    if not x:return bound
    n=0
    while n<bound and x%Q==0:
        x//=Q;n+=1
    return n

def pair_v(x,bound):
    return min(valuation(x[0],bound),valuation(x[1],bound))

def reduced_forms(discriminant):
    forms=[]
    for a in range(1,isqrt(-discriminant//3)+1):
        for b in range(-a,a+1):
            n=b*b-discriminant
            if n%(4*a):continue
            c=n//(4*a)
            if c<a or gcd(a,gcd(b,c))!=1:continue
            if (abs(b)==a or a==c) and b<0:continue
            forms.append((a,b,c))
    return forms

def class_polynomial(discriminant,bits=16384):
    forms=reduced_forms(discriminant)
    with ctx.workprec(bits):
        root=arb(-discriminant).sqrt()
        js=[(acb(-b,root)/(2*a)).modular_j() for a,b,c in forms]
        poly=acb_poly.from_roots(js).unique_fmpz_poly()
        if poly is None:raise ValueError('Insufficient complex ball precision')
        result=list(map(int,poly.coeffs()))
        assert len(result)==len(forms)+1
        return result

def canonical_hash(coeffs):
    return hashlib.sha256(json.dumps(coeffs,separators=(',',':')).encode()).hexdigest()

def residue_roots(coefficients):
    poly=POLYS([FIELD(list(c)) if isinstance(c,(list,tuple)) else FIELD(c) for c in coefficients])
    return sorted((tuple(map(int,x.to_list())),int(m)) for x,m in poly.roots())

def phi2_coeffs(x,m):
    x2=mul(x,x,m);x3=mul(x2,x,m)
    return [
        add(add(add(x3,scale(-162000,x2,m),m),scale(8748000000,x,m),m),(-157464000000000%m,0),m),
        add(add(scale(1488,x2,m),scale(40773375,x,m),m),(8748000000%m,0),m),
        add(add(scale(-1,x2,m),scale(1488,x,m),m),(-162000%m,0),m),(1,0)]

def supersingular_certificate():
    n=(Q-1)//2
    deuring=residue_roots([comb(n,k)**2%Q for k in range(n+1)])
    assert len(deuring)==n and all(m==1 for x,m in deuring)
    def jvalue(x):
        z=FIELD(list(x))
        return tuple(map(int,(FIELD(256)*(1-z+z*z)**3/(z*z*(1-z)**2)).to_list()))
    js=sorted(set(jvalue(x) for x,m in deuring));assert len(js)==36
    lookup={j:i for i,j in enumerate(js)};matrix=[]
    for j in js:
        row=[0]*len(js)
        for root,m in residue_roots(phi2_coeffs(j,Q)):row[lookup[root]]+=m
        assert sum(row)==3
        matrix.append(row)
    kernel=(sp.Matrix(matrix)+sp.eye(len(js))).nullspace()
    assert len(kernel)==1,('T2 does not isolate the desired eigenline',len(kernel))
    den=lcm(*(int(c.q) for c in kernel[0]));values=[int(den*c) for c in kernel[0]]
    divisor=gcd(*values);values=[v//divisor for v in values]
    if next(v for v in values if v)<0:values=[-v for v in values]
    assert all(values[lookup[(a,-b%Q)]]==values[i] for i,(a,b) in enumerate(js))
    return {'deuring_roots':[x for x,m in deuring],'supersingular_j':js,'T2_matrix':matrix,
            'T2_eigenvalue':-1,'primitive_eigenfunction':values}

def shifted(coefficients,r,digits):
    """Compute G(r+qZ) at known coefficient precision and divide its content."""
    modulus=Q**digits;out=[(0,0)]
    for c in reversed(coefficients):
        nxt=[(0,0)]*(len(out)+1)
        for i,x in enumerate(out):
            nxt[i]=add(nxt[i],mul(r,x,modulus),modulus)
            nxt[i+1]=add(nxt[i+1],scale(Q,x,modulus),modulus)
        nxt[0]=add(nxt[0],c,modulus)
        while len(nxt)>1 and nxt[-1]==(0,0):nxt.pop()
        out=nxt
    content=min(pair_v(c,digits) for c in out);assert content<digits
    divisor=Q**content
    return [(a//divisor,b//divisor) for a,b in out],digits-content

def simple_hensel(coeffs,root,digits):
    derivative=[scale(i,c,Q**digits) for i,c in enumerate(coeffs)][1:];n=1
    while n<digits:
        n=min(2*n,digits);m=Q**n
        delta=mul(evaluate(coeffs,root,m),inverse(evaluate(derivative,root,m),m),m)
        root=add(root,scale(-1,delta,m),m)
    return root

def lift_all(coeffs,working_digits=24):
    m=Q**working_digits;coeffs=[(c%m,0) for c in coeffs];results=[]
    def descend(g,digits,origin,factor):
        assert digits>=6,'Increase discovery precision'
        for r,multiplicity in residue_roots(g):
            if multiplicity==1:
                z=simple_hensel(g,r,digits)
                results.append((origin[0]+factor*z[0],origin[1]+factor*z[1]))
            else:
                h,remaining=shifted(g,r,digits)
                descend(h,remaining,(origin[0]+factor*r[0],origin[1]+factor*r[1]),factor*Q)
    descend(coeffs,working_digits,(0,0),1)
    assert len(results)==len(coeffs)-1
    return sorted(results)

def cm_certificate(discriminant,coeffs,ss,digits=4):
    lifts=lift_all(coeffs);m=Q**digits;roots=[(a%m,b%m) for a,b in lifts]
    assert len(set(roots))==len(roots)
    derivative=[i*c for i,c in enumerate(coeffs)][1:];hensel=[]
    for x in lifts:
        s=pair_v(evaluate(derivative,x,Q**80),80);h=pair_v(evaluate(coeffs,x,Q**80),80)
        assert h>2*s and h-s>=digits,(h,s)
        hensel.append([h,s])
    graph=[[j for j,y in enumerate(roots) if evaluate(phi2_coeffs(x,m),y,m)==(0,0)] for x in roots]
    assert all(len(row)==2 for row in graph),list(map(len,graph))
    assert all(i in graph[j] for i,row in enumerate(graph) for j in row)
    cycle=[0,min(graph[0])]
    while len(cycle)<len(roots):
        nxt=[i for i in graph[cycle[-1]] if i!=cycle[-2]]
        assert len(nxt)==1 and nxt[0] not in cycle
        cycle.append(nxt[0])
    assert 0 in graph[cycle[-1]]
    values=dict(zip(map(tuple,ss['supersingular_j']),ss['primitive_eigenfunction']))
    weights=[values[(roots[i][0]%Q,roots[i][1]%Q)] for i in cycle]
    data={'discriminant':discriminant,'class_number':len(roots),'root_precision':digits,
          'class_polynomial_sha256':canonical_hash(coeffs),'root_lifts':lifts,'hensel_valuations':hensel,
          'horizontal_T2_graph':graph,'generator_cycle':cycle,'CM_values':weights}
    if discriminant==-44375:
        grouped=[sum(weights[j::5]) for j in range(5)]
        moments=[sum(grouped[j]*comb(j,k) for j in range(5)) for k in range(5)]
        data.update({'grouped_coefficients':grouped,'raw_T_coefficients':moments,
                     'raw_T_coefficients_mod5':[c%5 for c in moments]})
    return data

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('certificate.json'))
    args=parser.parse_args();t=time.perf_counter();ss=supersingular_certificate()
    print(json.dumps({'stage':'Brandt','vertices':len(ss['supersingular_j']),'seconds':time.perf_counter()-t}),flush=True)
    cms=[]
    for disc in (-71,-44375):
        cm=cm_certificate(disc,class_polynomial(disc),ss);cms.append(cm)
        print(json.dumps({'stage':'CM','D':disc,'classes':cm['class_number'],'sum':sum(cm['CM_values']),
                          'grouped':cm.get('grouped_coefficients'),'moments_mod5':cm.get('raw_T_coefficients_mod5'),
                          'max_derivative_valuation':max(s for h,s in cm['hensel_valuations']),
                          'seconds':time.perf_counter()-t}),flush=True)
    data={'curve':{'label':'433.a1','ainvs':[1,0,0,0,1],'conductor':433},
          'reduction_field':{'prime':Q,'nonresidue':D},'iwasawa_prime':5,
          'class_polynomial_working_bits':16384,'supersingular':ss,'CM':cms,
          'scope':'Exact finite arithmetic; theta interpretation and exact lower vanishing are separate mathematical inputs.'}
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'output':str(args.output),'seconds':time.perf_counter()-t}),flush=True)

if __name__=='__main__':main()
