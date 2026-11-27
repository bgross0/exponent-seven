#!/usr/bin/env python3
"""Reject corrupt witnesses at the independent E433 verifier's trust boundary."""
from __future__ import annotations

import argparse
from copy import deepcopy
import json
from pathlib import Path

from verify_theta import ROOT, class_polynomial, require, verify


def replace(data, path, value):
    for key in path[:-1]:
        data = data[key]
    data[path[-1]] = value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', type=Path)
    parser.add_argument('--write', type=Path)
    args = parser.parse_args()
    data = json.loads((ROOT/'certificate.json').read_text())
    polynomials = {d: class_polynomial(d) for d in (-71,-44375)}
    require(verify(data,polynomials)['status']=='PASS','Valid baseline rejected')
    first_root = data['supersingular']['deuring_roots'][0]
    corruptions = [
        ('noncanonical_field_residue', ['supersingular','deuring_roots',0],
         [first_root[0]+433,first_root[1]]),
        ('invalid_Deuring_root', ['supersingular','deuring_roots',0], [0,0]),
        ('invalid_Brandt_row', ['supersingular','T2_matrix',0], [0]*36),
        ('nonprimitive_eigenfunction', ['supersingular','primitive_eigenfunction'],
         [2*x for x in data['supersingular']['primitive_eigenfunction']]),
        ('wrong_class_polynomial', ['CM',1,'class_polynomial_sha256'], '0'*64),
        ('invalid_Hensel_lift', ['CM',1,'root_lifts',0],
         [data['CM'][1]['root_lifts'][0][0]+1,data['CM'][1]['root_lifts'][0][1]]),
        ('false_horizontal_edge', ['CM',1,'horizontal_T2_graph',0], [0,0]),
        ('nonpermutation_cycle', ['CM',1,'generator_cycle',1],
         data['CM'][1]['generator_cycle'][0]),
        ('wrong_CM_value', ['CM',1,'CM_values',0], data['CM'][1]['CM_values'][0]+1),
        ('wrong_quotient_coefficient', ['CM',1,'grouped_coefficients',0], 1),
        ('wrong_quadratic_moment', ['CM',1,'raw_T_coefficients',2], 2),
    ]
    rejected = []
    for name,path,value in corruptions:
        bad = deepcopy(data)
        replace(bad,path,value)
        try:
            verify(bad,polynomials)
        except ValueError as error:
            rejected.append({'case':name,'reason':str(error)})
        else:
            raise AssertionError(f'Corruption accepted: {name}')
    result = {'status':'PASS','valid_baseline_accepted':True,
              'corruptions_rejected':len(rejected),'rejections':rejected,
              'scope':'Adversarial checks of finite witness validation; no geometric or arithmetic comparison theorem is tested here.'}
    if args.check:
        require(result==json.loads(args.check.read_text()),'Rejection receipt changed')
    if args.write:
        args.write.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
