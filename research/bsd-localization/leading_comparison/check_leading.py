#!/usr/bin/env python3
"""Exact coordinate checks for the reduced second-order comparison target.

This does not evaluate the new de Rham vector or prove a reciprocity law.
"""
import argparse
import importlib.util
import json
from math import comb
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
spec = importlib.util.spec_from_file_location("cm_jets", ROOT / "reflected_pilot/cm_weight_jets.py")
cm = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cm)


def add(a, b, m):
    return tuple((x+y) % m for x, y in zip(a, b))


def scale(a, b, m):
    return tuple(x*b % m for x in a)


def mul(a, b, m):
    c = [0]*5
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    for k in (4, 3):
        # xi^3 = 1+2xi-xi^2.
        c[k-3] += c[k]
        c[k-2] += 2*c[k]
        c[k-1] -= c[k]
    return tuple(x % m for x in c[:3])


def determinant(a):
    return (a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])
            -a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])
            +a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))


def inverse(a, m):
    cols = [mul(a, tuple(int(i == j) for i in range(3)), m) for j in range(3)]
    mat = [list(row) for row in zip(*cols)]
    det = determinant(mat)
    assert det % 5
    out = []
    for j in range(3):
        b = [row[:] for row in mat]
        for i in range(3):
            b[i][j] = int(i == 0)
        out.append(determinant(b)*pow(det, -1, m) % m)
    out = tuple(out)
    assert mul(a, out, m) == (1, 0, 0)
    return out


def fmul(a, b, m):
    """Multiply in the cubic ring[F]/(F^2+3F+5)."""
    bd = mul(a[1], b[1], m)
    return (add(mul(a[0], b[0], m), scale(bd, -5, m), m),
            add(add(mul(a[0], b[1], m), mul(a[1], b[0], m), m),
                scale(bd, -3, m), m))


def compute():
    digits = 12
    modulus = 5**digits
    bigmod = 5**(digits+1)
    omega = cm.lift_root(2, 5, digits+1)
    log6 = cm.log5_unit(6, digits+1)
    logratio = (cm.log5_unit(10+omega, digits+1)
                - cm.log5_unit(11-omega, digits+1)) % bigmod
    delta = logratio//5 * pow(7*(log6//5), -1, modulus) % modulus
    # A one-digit-higher computation independently checks the precision margin.
    omega_hi = cm.lift_root(2, 5, digits+2)
    logratio_hi = (cm.log5_unit(10+omega_hi, digits+2)
                   - cm.log5_unit(11-omega_hi, digits+2)) % (5**(digits+2))
    delta_hi = logratio_hi//5 * pow(7*(cm.log5_unit(6,digits+2)//5), -1, bigmod) % bigmod
    assert delta_hi % modulus == delta
    assert delta == 52766382 and delta % 5 == 2
    assert 10*10+10+18 == 2**7
    omega2 = cm.lift_root(0, 2, 7)
    assert (10+omega2) % 128 == 0 and (11-omega2) % 2 == 1
    assert (10+omega)*(11-omega) % bigmod == 128
    # The opposite embedding and reversed horizontal cycle change only the sign.
    delta_conjugate = (-logratio) % bigmod // 5 * pow(7*(log6//5),-1,modulus) % modulus
    assert (delta+delta_conjugate) % modulus == 0

    inputs = json.loads((ROOT / "p5/inputs.json").read_text())
    raw = inputs["raw_Gamma1_coefficients"]
    raw_jet = [sum(raw[i]*comb(i,j) for i in range(j,len(raw))) for j in range(3)]
    assert raw_jet == [0, -20, -34]
    raw_second = raw_jet[2] % 5
    alpha = cm.unit_root(2)
    regularized_second = raw_second * pow(alpha,-2,5) % 5
    weight_second = regularized_second * delta**2 % 5
    assert (raw_second,regularized_second,weight_second) == (1,4,1)

    c = json.loads((ROOT / "de_rham_strategy/result.json").read_text())
    fdata = json.loads((ROOT / "local_crystalline/result.json").read_text())
    m = c["modulus"]
    F = fdata["frobenius_matrix"]
    cinv = c["inverse_conversion"]
    one, zero, tau = (1,0,0), (0,0,0), (1,m-1,m-1)
    H = (scale(add(scale(one,-2,m),scale(tau,-10,m),m),pow(3,-1,m),m),
         scale(add(scale(one,11,m),tau,m),pow(3,-1,m),m))
    # E(F)=(1-F)^2(1-tau*F+F^2); 1-F^2=6+3F.
    euler = fmul(fmul((one,scale(one,-1,m)),(one,scale(one,-1,m)),m),
                 (scale(one,-4,m),add(scale(tau,-1,m),scale(one,-3,m),m)),m)
    assert fmul(H,(scale(one,6,m),scale(one,3,m)),m) == euler
    homega = [add(H[0],scale(H[1],F[0][0],m),m), scale(H[1],F[1][0],m)]
    stab = [add(scale(homega[0],row[0],m),scale(homega[1],row[1],m),m) for row in cinv]
    bad_ratio = mul(stab[1],inverse(stab[0],m),m)
    assert all(x % 5 == 0 for x in bad_ratio)
    assert tuple(x % 5 for x in homega[0]) == one
    assert tuple(x % 5 for x in homega[1]) == zero
    # The PR annihilator is a different line in these coordinates.
    # Compute Z(F)omega=(20-13F)omega/45 with the source guard digit.
    fm = fdata["modulus"]
    z0 = ((20-13*F[0][0]) % fm)//5 * pow(9,-1,m) % m
    z1 = ((-13*F[1][0]) % fm)//5 * pow(9,-1,m) % m
    assert (z0,z1) == (13133,32916)
    assert z0 % 5 == 3 and z1 % 5 == 1

    # Exact no-go model: P=diag(1,t), y_B=(t^2,B*t).
    # For fixed analytic L2=(1,r), M_B=[[1,0],[r-B,1]] is invertible,
    # preserves the known ordinary row, and M_B P(y_B)=t^2*(1,r).
    models = []
    for r in (0,1,7):
        for B in (0,1,5):
            M = [[1,0],[r-B,1]]
            l2 = [1, M[1][0]+B]
            bad_line = [1,r-B]
            determinant_pair = l2[0]*bad_line[1]-l2[1]*bad_line[0]
            assert l2 == [1,r] and determinant_pair == -B
            models.append({'r':r,'finite_log':B,'comparison':M,'bad_line':bad_line})

    return {'status':'PASS',
        'cm_norm_two_coordinate':{'digits':digits,'modulus':modulus,
          'omega_mod_5_power_13':omega,'delta':delta,'delta_mod5':delta%5,
          'formula':'(log(10+omega)-log(11-omega))/(7*log(6))',
          'linear_odd_parameter_scale_for_a_equals_2_omega':delta,
          'unoriented_norm_two_cycle_sign':'delta or -delta; the quadratic transport is unchanged',
          'quadratic_coordinate_scale_mod5':delta**2%5,
          'raw_quadratic_residue_mod5':raw_second,
          'regularized_norm_two_theta_residue_mod5':regularized_second,
          'regularized_theta_after_CM_weight_substitution_mod5':weight_second,
          'normalization_scope':'Uses supplied primitive quaternionic sign and norm-two cycle; other normalizations may multiply by a unit.'},
        'DL_Euler_candidate':{'modulus':m,'cubic_basis':['1','xi','xi^2'],
          'tau':'zeta^3+zeta^4=1-xi-xi^2',
          'polynomial':'E(F)/(1-F^2)=((-2-10*tau)+(11+tau)*F)/3',
          'omega_eta_coordinates':homega,'stabilized_coordinates':stab,
          'critical_over_ordinary':bad_ratio,
          'critical_over_ordinary_mod5':[x%5 for x in bad_ratio],
          'arithmetic_line_comparison_proved':False},
        'PR_annihilator_line':{'omega_eta_coordinates_mod_5_power_7':[z0,z1],
          'coordinates_mod5':[z0%5,z1%5],
          'not_the_same_line_as_DL_candidate_mod5':True},
        'shear_countermodels':models,
        'scope':'Exact CM parameter transport, theta-residue transport, DL Euler candidate-line algebra, and insufficiency models. The ordinary order-two result is a theorem-based deduction in README using the supplied theta identification. No critical second coefficient, bad-line reciprocity comparison, or nonzero reflected logarithm is computed.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    out=json.loads(json.dumps(compute()))
    if args.check:
        assert out==json.loads((HERE/'result.json').read_text())
    if args.write:
        (HERE/'result.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
