#!/usr/bin/env python3
"""Exact finite checks supporting the conditional CM-tail theorem.

This does not infer a Banach-space bound from finite q-series. The analytic
premise and mathematical proofs are stated separately in README.md.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import sys


sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PINNED = ROOT / "reflected_pilot/cm-weight-jets.json.gz"
PINNED_SHA256 = "5054b565231b63457eba413dfcb3e74eb0970891a6dfbc7a91375bdff57857d3"


def floor_log5(n):
    assert n >= 1
    k = 0
    while n >= 5:
        n //= 5
        k += 1
    return k


def ceil_fraction(x):
    return -((-x.numerator) // x.denominator)


def numerator_bound(i, jet=2):
    return max(0, ceil_fraction(Fraction(20*i-58, 25))-2*jet)


def reduced_bound(i, jet=2):
    assert i >= 3
    return numerator_bound(i, jet)-floor_log5(i-1)


def tail_bound(retained, jet=2):
    """The theorem reduces the infinite minimum to these two indices."""
    assert retained >= 2
    first = retained+1
    next_breakpoint = 5**(floor_log5(first-1)+1)+1
    return min(reduced_bound(first, jet), reduced_bound(next_breakpoint, jet))


def valuation_arithmetic():
    radius = Fraction(4, 25)
    delta = 1-6*radius
    assert delta == Fraction(1, 25)
    log_terms = [5**a*delta-a for a in range(8)]
    assert min(log_terms) == -1 and log_terms[2] == -1
    # For a>=3 the consecutive difference increases and is already positive.
    assert 4*5**3*delta-1 > 0
    ratio_delta = Fraction(1, 5)
    ratio_log_terms = [5**a*ratio_delta-a for a in range(8)]
    assert min(ratio_log_terms) == 0 and ratio_log_terms[1] == 0
    assert 4*5*ratio_delta-1 > 0
    min_index = (Fraction(1, 1)/(4*radius)).numerator // (Fraction(1, 1)/(4*radius)).denominator
    assert min_index == 1
    ordinary_input = -radius*min_index
    ordinary_output = ordinary_input-1
    product_output = 2*ordinary_output
    assert ordinary_output == -Fraction(29, 25)
    assert product_output == -Fraction(58, 25)
    # G^j through order2: v(j1)=1, v(j2)=3, v(logG)>=-1.
    operator_jet_bounds = [0, 1-1, min(3-1, 2*(1-1))]
    assert operator_jet_bounds == [0, 0, 0]
    # Unit norm alone constrains the index attaining the minimum.
    assert 4*radius*1 <= 1 < 4*radius*2
    # Check the exact two-point minimum against all indices through the
    # following six complete logarithmic blocks; later block minima grow.
    checked = 0
    limit = 5**6+1
    suffix_min = {}
    best = None
    for i in range(limit, 2, -1):
        value = reduced_bound(i)
        best = value if best is None else min(best, value)
        if i <= 257:
            suffix_min[i-1] = best
    for retained in range(2, 257):
        assert tail_bound(retained) == suffix_min[retained]
        checked += 1
    assert Fraction(4, 5)*(5-1) > 1
    table = [{'retained_pole_order':n, 'pole_reduced_tail_digits':tail_bound(n)}
             for n in (10,12,15,17,20,22)]
    assert [r['pole_reduced_tail_digits'] for r in table] == [2,4,6,8,10,12]
    cutoffs = []
    for requested in (1,2,4,6,8,12):
        for further_loss in (0,1,2,3):
            n = next(n for n in range(2,200)
                     if tail_bound(n) >= requested+further_loss)
            cutoffs.append({'requested_digits':requested,
                            'further_loss_digits':further_loss,
                            'retained_pole_order':n,
                            'tail_digits_before_further_loss':tail_bound(n)})
    return {
        'radius':str(radius), 'output_radius':'4/5',
        'G_minus_one_valuation':str(delta),
        'log_G_valuation_lower_bound':-1,
        'weight_rescaling':'W=25*w',
        'operator_jet_valuation_lower_bounds':operator_jet_bounds,
        'CM_jet_output_norm_valuation':str(ordinary_output),
        'product_jet_output_norm_valuation':str(product_output),
        'second_W_coefficient_bound':'max(0,ceil((20*i-58)/25)-4)',
        'pole_reduction_loss':'floor(log_5(i-1))',
        'finite_tail_minimum_regressions':checked,
        'tail_table':table, 'cutoffs':cutoffs,
    }


def load_cm():
    spec = importlib.util.spec_from_file_location(
        'cm_tail_source', ROOT/'reflected_pilot/cm_weight_jets.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def euler_identities():
    raw = PINNED.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == PINNED_SHA256
    data = json.loads(gzip.decompress(raw))
    cm = load_cm()
    modulus = data['coefficient_ring']['modulus']
    bound = data['q_precision']['largest_coefficient']
    digits = data['coefficient_ring']['digits']
    assert modulus == 5**12 and bound == 4096
    log6 = cm.log5_unit(6, digits+1)
    nu = (cm.log5_unit(389,digits+1)//5)*pow(log6//5,-1,modulus) % modulus

    def jet_product(a,b):
        result=[]
        for j in range(3):
            out=[cm.ZERO]*(bound+1)
            for k in range(j+1):
                term=cm.multiply_series(a[k],b[j-k],modulus)
                out=[cm.add(x,y,modulus) for x,y in zip(out,term)]
            result.append(out)
        return result

    def scalar_product(a,scalar):
        out=[]
        for j in range(3):
            out.append([tuple(sum(scalar[k]*a[j-k][n][r]
                                  for k in range(j+1))%modulus for r in range(6))
                        for n in range(bound+1)])
        return out

    report=[]
    for embedding,c_exp in ((2,3),(4,4)):
        branch=data['branches'][str(embedding)]
        g=[branch['g_base'],branch['g_weight_derivative'],branch['g_weight_coefficient_2']]
        h=[[cm.conjugate(c,modulus) for c in row] for row in g]
        h_minus=[h[0], [cm.scale(c,-1,modulus) for c in h[1]],
                 [cm.add(a,b,modulus) for a,b in zip(h[1],h[2])]]
        c=cm.zeta(c_exp,modulus)
        eigen_product=[cm.ZERO]*3
        for j in range(3):
            for k in range(j+1):
                eigen_product[j]=cm.add(eigen_product[j],cm.mul(h_minus[k][5],h[j-k][5],modulus),modulus)
        assert eigen_product == [c,cm.ZERO,cm.ZERO]
        q_a=jet_product(h_minus,[cm.shift_series(row,389) for row in h])
        q_b=jet_product([cm.shift_series(row,389) for row in h_minus],h)
        q_b=scalar_product(q_b,[1, -nu, cm.choose2(-nu,modulus)])
        for placement,q,key in (
                ('A',q_a,'g_depleted_times_V389_h'),
                ('B',q_b,'V389_g_depleted_times_h')):
            original=branch['raw_de_rham_input_cross_oldforms'][key]
            checks=nonzero=wrong_c_rejections=0
            wrong_c=cm.zeta((c_exp+1)%7,modulus)
            for j in range(3):
                for n in range(bound//5+1):
                    rhs=cm.add(q[j][5*n],cm.scale(cm.mul(c,q[j][n],modulus),-1,modulus),modulus)
                    lhs=tuple(original[j][5*n])
                    assert lhs == rhs, (embedding,placement,j,n)
                    checks += 1
                    nonzero += lhs != cm.ZERO
                    wrong=cm.add(q[j][5*n],cm.scale(cm.mul(wrong_c,q[j][n],modulus),-1,modulus),modulus)
                    wrong_c_rejections += wrong != lhs
            assert nonzero > 0 and wrong_c_rejections > 0
            # Trace commutes with U: all coefficients supported by this
            # independent raw archive have the correct (1+U71) identity.
            trace_checks=0
            for j in range(3):
                for n in range(bound//(5*71)+1):
                    lhs=cm.add(original[j][5*n],original[j][5*71*n],modulus)
                    rhs=cm.add(
                        cm.add(q[j][5*n],q[j][5*71*n],modulus),
                        cm.scale(cm.mul(c,cm.add(q[j][n],q[j][71*n],modulus),modulus),-1,modulus),modulus)
                    assert lhs==rhs
                    trace_checks+=1
            report.append({'embedding':embedding,'placement':placement,
                           'c_zeta_exponent':c_exp,
                           'raw_vector_coefficients_checked':checks,
                           'nonzero_coefficients_checked':nonzero,
                           'wrong_c_coefficients_rejected':wrong_c_rejections,
                           'trace_vector_coefficients_checked':trace_checks})
    return {'source_sha256':PINNED_SHA256,'modulus':modulus,
            'source_q_bound':bound,'U_identity_output_q_bound':bound//5,
            'trace_U_identity_output_q_bound':bound//(5*71),
            'nu389_modulus':nu,
            'formula':'U5(original)=(U5-c)Q; c=zeta^3 for omega2 and zeta^4 for omega4',
            'branches':report}


def compute():
    return {'status':'PASS', 'valuation_arithmetic':valuation_arithmetic(),
            'exact_euler_identity':euler_identities(),
            'scope':'Finite exact coefficient identities and tail-inequality arithmetic. The quantitative theorem is conditional on the Coleman fixed-weight family realization (CF) and the specified integral geometric models in README. No new projected elliptic vector, global regulator comparison, or Lean verification is computed.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    result=compute()
    path=HERE/'result.json'
    if args.check:
        assert result==json.loads(path.read_text()), 'Saved result differs'
    if args.write:
        path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
