#!/usr/bin/env python3
"""Cubic trace of the undepleted CM product Q=h(-s)*V389(h(s)).

The proper E projection of this input is related to the previously saved
depleted input by the explicit matrix in README.md. Raw q-series are not
identified with de Rham classes by this computation.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import resource
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "trace_scaling"))
import cubic_trace as ct
import selected_trace as st


def reflect(jet, modulus):
    """Substitute W -> -W+W^2 modulo W^3."""
    a,b,c=jet
    return a, st.cm.scale(b,-1,modulus), st.cm.add(b,c,modulus)


def naive_product(g, n, modulus):
    result=[st.cm.ZERO]*3
    for j in range(1,(n-1)//389+1):
        i=n-389*j
        hminus=reflect(tuple(st.conjugate(col[i],modulus) for col in g),modulus)
        hplus=tuple(st.conjugate(col[j],modulus) for col in g)
        for order in range(3):
            for a in range(order+1):
                result[order]=st.cm.add(result[order],st.cm.mul(hminus[a],hplus[order-a],modulus),modulus)
    return [ct.to_cubic(row,modulus) for row in result]


def build(bound=6825,digits=12):
    assert bound>=6 and 1<=digits<=27
    started=time.perf_counter()
    modulus=5**digits
    raw_bound=71*bound
    ring=ct.PackedCubic(modulus)
    logs=st.UnitLogs(digits)
    g,counts=st.cm_table(raw_bound-389,2,digits,ring,logs)
    # Preserve the short, positive-weight second factor before overwriting
    # the table with reflected negative-weight first-factor coefficients.
    small=[]
    for j in range(1,(raw_bound-1)//389+1):
        gj=tuple(col[j] for col in g)
        if any(gj):
            hj=tuple(ring.pack(st.conjugate(ring.unpack(x),modulus)) for x in gj)
            small.append((389*j,hj))
    for n in range(len(g[0])):
        if not any(col[n] for col in g):
            continue
        h=tuple(st.conjugate(ring.unpack(col[n]),modulus) for col in g)
        reflected=reflect(h,modulus)
        for col,row in zip(g,reflected):col[n]=ring.pack(row)
    table_seconds=time.perf_counter()-started
    targets=sorted(set(range(1,bound+1))|{71*n for n in range(1,bound+1)})
    output=[[[0]*3 for _ in range(bound+1)] for _ in range(3)]
    digest=hashlib.sha256()
    pairs=0
    for m in targets:
        raw=[[0]*3 for _ in range(3)]
        for shift,hj in small:
            if shift>=m:break
            i=m-shift
            hi=tuple(col[i] for col in g)
            if not any(hi):continue
            product=ring.averaged_jet_product(hi,hj)
            for order in range(3):
                for r in range(3):raw[order][r]+=product[order][r]
            pairs+=1
        raw=[[x%modulus for x in row] for row in raw]
        digest.update(st.canonical_bytes([m,raw]))
        destinations=[]
        if m<=bound:destinations.append(m)
        if m%71==0:destinations.append(m//71)
        for n in destinations:
            for order in range(3):
                output[order][n]=[(a+b)%modulus for a,b in zip(output[order][n],raw[order])]

    reference_path=HERE.parent/'reflected_pilot/cm-weight-jets.json.gz'
    reference_bytes=reference_path.read_bytes()
    assert hashlib.sha256(reference_bytes).hexdigest()=='5054b565231b63457eba413dfcb3e74eb0970891a6dfbc7a91375bdff57857d3'
    reference=json.loads(gzip.decompress(reference_bytes))
    b=reference['branches']['2']
    reference_g=[b['g_base'],b['g_weight_derivative'],b['g_weight_coefficient_2']]
    overlap=min(bound,reference['q_precision']['largest_coefficient']//71)
    checkmod=min(modulus,reference['coefficient_ring']['modulus'])
    checks=0
    for n in range(overlap+1):
        a=naive_product(reference_g,n,checkmod)
        b=naive_product(reference_g,71*n,checkmod)
        for order in range(3):
            expected=tuple((x+y)%checkmod for x,y in zip(a[order],b[order]))
            assert tuple(x%checkmod for x in output[order][n])==expected,('independent product overlap',order,n)
            checks+=1

    result={
        'schema':'E389-Kminus71-undepleted-cubic-trace-v1',
        'scope':'Raw averaged ordinary CM product and exact finite overlap checks; no proper projection or arithmetic class computed.',
        'source_case':'omega=2; Q=h(-s)*V389(h(s)); h has inverse order-seven class character',
        'averaging':'(1+sigma)/2, sigma(zeta)=zeta^-1',
        'trace':'Tr71 Q=Q+U71 Q',
        'coefficient_ring':{'p':5,'digits':digits,'modulus':modulus,'basis':['1','xi','xi^2'],'polynomial_ascending':[-1,-2,1,1]},
        'q_precision':{'largest_coefficient':bound,'remainder':f'O(q^{bound+1})'},
        'weight_coordinate':'W=6^s-1',
        'orders':['constant','coefficient of W','coefficient of W^2'],
        'averaged_trace_orders_0_1_2':output,
        'elliptic_transfer':{'tau':'1-xi-xi^2','U_polynomial':'U^2+3U+5','R':'(U^2-tau*U+1)/(U*(U-tau/2))','meaning':'Pi(H)=R(U)Pi(Qplus); not an identity of raw q-series'},
        'counts':{**counts,'selected_product_indices':len(targets),'shared_jet_products':pairs,'raw_q_bound':raw_bound,'selected_raw_sha256':digest.hexdigest()},
        'verification':{'pinned_CM_gzip_sha256':hashlib.sha256(reference_bytes).hexdigest(),'independent_naive_overlap_bound':overlap,'overlap_modulus':checkmod,'cubic_vector_coefficients_checked':checks}
    }
    performance={'table_and_reflection_seconds':round(table_seconds,6),'generation_and_checks_seconds':round(time.perf_counter()-started,6),'peak_RSS_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    return result,performance


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--bound',type=int,default=6825)
    p.add_argument('--digits',type=int,default=12)
    p.add_argument('--check',action='store_true')
    p.add_argument('--output',type=Path,default=HERE/'cubic-product-6825-12.json.gz')
    p.add_argument('--receipt',type=Path,default=HERE/'product-result.json')
    args=p.parse_args()
    result,performance=build(args.bound,args.digits)
    raw=st.canonical_bytes(result)
    compressed=st.deterministic_gzip(raw)
    receipt={'status':'PASS','bound':args.bound,'digits':args.digits,'compressed_bytes':len(compressed),'uncompressed_bytes':len(raw),'gzip_sha256':hashlib.sha256(compressed).hexdigest(),'uncompressed_sha256':hashlib.sha256(raw).hexdigest(),'performance':performance,'verification':result['verification'],'counts':result['counts']}
    if args.check:
        assert args.output.read_bytes()==compressed,'saved undepleted product differs'
    else:
        args.output.write_bytes(compressed)
        args.receipt.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))


if __name__=='__main__':main()
