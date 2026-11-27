#!/usr/bin/env python3
"""Independent finite checks for the CM weight reflection and depletion identities.

Analytic-family and de Rham assertions are proved in the accompanying notes;
finite coefficients alone do not prove an identity of infinite families.
"""
import argparse
from fractions import Fraction
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
PACKAGE = ROOT.parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(PACKAGE/'elliptic_projection'))
from manin import PrimeManin, add_sparse

spec = importlib.util.spec_from_file_location('cm_weight_jets', PACKAGE/'reflected_pilot/cm_weight_jets.py')
cm = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cm)

PAIRS = [
    ('g_depleted_times_V389_h', 'both_depleted_g_times_V389_h'),
    ('V389_g_depleted_times_h', 'both_depleted_V389_g_times_h'),
]


def normalized_log389(digits):
    modulus = 5**digits
    a = cm.log5_unit(389, digits+1)
    b = cm.log5_unit(6, digits+1)
    assert a % 5 == b % 5 == 0 and b % 25 != 0
    return a//5*pow(b//5, -1, modulus) % modulus


def vector(v, modulus):
    return tuple(int(x) % modulus for x in v)


def check_arrays(branches, bound, digits):
    modulus, nu = 5**digits, normalized_log389(digits)
    reflection = depletion = conjugation = 0
    differences = {}
    for branch in ('2', '4'):
        cases = branches[branch]
        A = cases[PAIRS[0][1]]
        B = cases[PAIRS[1][1]]
        for n in range(bound+1):
            a = [vector(j[n],modulus) for j in A]
            b = [vector(j[n],modulus) for j in B]
            # iota(W)=(1+W)^(-1)-1=-W+W^2+O(W^3).
            assert a[0] == b[0]
            assert cm.scale(a[1],-1,modulus) == cm.add(b[1],cm.scale(b[0],nu,modulus),modulus)
            right = cm.add(cm.add(b[2],cm.scale(b[1],nu,modulus),modulus),
                           cm.scale(b[0],cm.choose2(nu,modulus),modulus),modulus)
            assert cm.add(a[1],a[2],modulus) == right
            reflection += 3
        differences[branch] = {}
        for single, both in PAIRS:
            # U5(single-both)=0, including its three weight coefficients.
            for j in range(3):
                for n in range(0, bound+1, 5):
                    assert cases[single][j][n] == cases[both][j][n]
                    depletion += 1
            n0 = next((n for n in range(bound+1)
                       if any(cases[single][j][n] != cases[both][j][n] for j in range(3))), None)
            assert n0 is not None and n0 % 5 != 0
            differences[branch][single] = n0
    # The second CM embedding is the exact coefficient-field conjugate.
    for name in branches['2']:
        for j in range(3):
            for n in range(bound+1):
                assert vector(branches['4'][name][j][n],modulus) == cm.conjugate(
                    vector(branches['2'][name][j][n],modulus),modulus)
                conjugation += 1
    return {
        'bound': bound, 'digits': digits, 'nu389_modulus': nu,
        'reflection_vector_identities': reflection,
        'U5_depletion_vector_identities': depletion,
        'embedding_conjugation_vector_identities': conjugation,
        'first_nonzero_depletion_difference_q_index': differences,
    }


def cubic_average(v, modulus):
    """Return (v+sigma(v))/2 in basis 1,xi,xi^2, xi=zeta+zeta^-1."""
    averaged = cm.scale(cm.add(vector(v,modulus),cm.conjugate(vector(v,modulus),modulus),modulus),
                        pow(2,-1,modulus),modulus)
    assert averaged[1] == 0 and averaged[2] == averaged[5] and averaged[3] == averaged[4]
    a = (averaged[0]-2*averaged[2]+averaged[3]) % modulus
    b = -averaged[3] % modulus
    c = (averaged[2]-averaged[3]) % modulus
    reconstructed = ((a-b+2*c)%modulus,0,(-b+c)%modulus,-b%modulus,-b%modulus,(-b+c)%modulus)
    assert reconstructed == averaged
    return [a,b,c]


def reduced_inputs(traced):
    modulus=traced['coefficient_ring']['modulus']
    bound=traced['q_precision']['largest_coefficient']
    xi=cm.add(cm.zeta(1,modulus),cm.zeta(-1,modulus),modulus)
    xi2=cm.mul(xi,xi,modulus)
    xi3=cm.mul(xi2,xi,modulus)
    assert cm.add(cm.add(xi3,xi2,modulus),cm.scale(xi,-2,modulus),modulus)==cm.zeta(0,modulus)
    # The cubic has no root mod5, hence is irreducible there.
    assert all((x**3+x*x-2*x-1)%5 for x in range(5))
    jet=traced['common_traces_orders_0_1_2']['2']['both_depleted_g_times_V389_h']
    return {
        'schema':'E389-CM-single-cubic-trace-v1',
        'source':'../tame_trace_compute/traces.json',
        'source_sha256':'4117034c9ef61b5cc09d81e4c42f3449624e82216b12e5e639cc25107541148a',
        'construction':'coefficient-wise (TrXi_both_A + sigma(TrXi_both_A))/2',
        'coefficient_ring':{'p':5,'digits':5,'modulus':modulus,
                            'generator':'xi=zeta7+zeta7^-1',
                            'minimal_polynomial_low_to_high':[-1,-2,1,1],
                            'basis':['1','xi','xi^2']},
        'q_bound':bound,
        'weight_coordinate':'W=6^(kappa-1)-1',
        'taylor_orders':[0,1,2],
        'coefficients':[[cubic_average(v,modulus) for v in order] for order in jet],
        'trace_and_coefficient_reduction_digit_loss':0,
        'preserved_object':'proper E-cohomology projection of the traced input',
        'not_preserved':'raw q-series of each of the original eight inputs',
        'scope':'One representative for the common projected class, justified by depletion exactness, Fricke389 symmetry, and the Rankin-Cohen primitive in analytic_target_audit. This finite artifact is not itself a projected de Rham vector or nonvanishing certificate.'
    }


def exact_fricke_certificate():
    module = PrimeManin(389, exact=True)
    def w(z):
        if z is None:
            return Fraction(0)
        if z == 0:
            return None
        return -1/(389*z)
    images = []
    for i in range(390):
        a,b = module.lift_endpoints(i)
        images.append(module.reduce(module.path(w(a),w(b))))
    for relation in module.relations:
        row = {}
        for i,a in relation.items():
            for j,b in images[i].items():
                add_sparse(row,j,a*b,0)
        assert not row
    W = [[images[i].get(j,0) for i in module.free] for j in range(65)]
    witness = json.loads((PACKAGE/'elliptic_projection/witness.json').read_text())
    E = [[Fraction(v) for v in row] for row in witness['E']]
    assert module.free == witness['basis_free_manin_indices']
    for i in range(65):
        for j in range(2):
            assert sum(W[i][k]*E[k][j] for k in range(65)) == -E[i][j]
    for i in range(65):
        for j in range(65):
            assert sum(W[i][k]*W[k][j] for k in range(65)) == int(i == j)
    p = 389
    legendre_sum = 0
    for x in range(p):
        v = (1+4*(x**3+x*x-2*x)) % p
        symbol = pow(v,(p-1)//2,p)
        legendre_sum += -1 if symbol == p-1 else symbol
    a389 = -legendre_sum
    assert a389 == 1
    return {
        'modular_curve_level':389,
        'verified_all_manin_relations':len(module.relations),
        'fricke_matrix_involutive':True,
        'fricke_on_full_E_factor':-1,
        'singular_fiber_point_count_mod389':p+1-a389,
        'a389':a389,
    }


def compute():
    raw_bytes = gzip.decompress((PACKAGE/'reflected_pilot/cm-weight-jets.json.gz').read_bytes())
    assert hashlib.sha256(raw_bytes).hexdigest() == '80b2b0f5ba32d6a3d45ebb828c21e5bf043226cfd4290b72dd9d81ed8ae830ba'
    raw = json.loads(raw_bytes)
    trace_bytes = (PACKAGE/'tame_trace_compute/traces.json').read_bytes()
    assert hashlib.sha256(trace_bytes).hexdigest() == '4117034c9ef61b5cc09d81e4c42f3449624e82216b12e5e639cc25107541148a'
    traced = json.loads(trace_bytes)
    branches = {b:raw['branches'][b]['raw_de_rham_input_cross_oldforms'] for b in ('2','4')}
    reduced = reduced_inputs(traced)
    output = {
        'status':'PASS',
        'cubic_input_reduction':{
            'file':'reduced_trace_inputs.json',
            'coefficient_field_degree':3,
            'number_of_input_families':1,
            'q_bound':128,
            'taylor_orders':[0,1,2],
            'scalar_residues':3*3*129,
            'original_eight_input_scalar_residues':8*6*3*129,
            'representation_size_reduction_factor':16,
            'cubic_polynomial_irreducible_mod5':True,
            'division_by_two_is_5_adic_unit':True,
        },
        'raw':check_arrays(branches,4096,12),
        'traced':check_arrays(traced['common_traces_orders_0_1_2'],128,5),
        'exact_fricke':exact_fricke_certificate(),
        'identities':{
            'weight_involution':'iota(W)=(1+W)^(-1)-1',
            'raw_both_depleted_reflection':'A(iota(W))=(1+W)^nu389*B(W)',
            'depletion_difference':'U5(Xi_single-Xi_both)=0',
            'opposite_embedding':'sigma(zeta7)=zeta7^(-1)',
            'normalized_projected_evenness':'C(s)=389^(s/2)*Pi_E([A_s]); C(-s)=C(s)',
            'zero_base_consequence':'Pi_E([A_0])=0 implies the entire first projected weight coefficient is zero',
        },
        'scope':'Exact finite arithmetic and exact elliptic Fricke sign. Analytic reflection, U5-kernel exactness and base-zero hypotheses are justified in the accompanying mathematical notes, not inferred from finite q-expansions. No second projected coefficient or nonzero global logarithm is computed.',
    }
    return output, reduced


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    result,reduced=compute()
    if args.check:
        assert result == json.loads((ROOT/'result.json').read_text())
        assert reduced == json.loads((ROOT/'reduced_trace_inputs.json').read_text())
    if args.write:
        (ROOT/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
        (ROOT/'reduced_trace_inputs.json').write_text(json.dumps(reduced,sort_keys=True,separators=(',',':'))+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
