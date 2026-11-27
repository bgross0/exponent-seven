#!/usr/bin/env python3
"""Meaningful format, precision, and field-arithmetic checks for the contract."""

from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import unittest

from certificate_checker import CertificateError, check_certificate, is_irreducible


HERE = Path(__file__).resolve().parent


def fixture(name="certificate-example.json"):
    return json.loads((HERE / name).read_text())


class CertificateTests(unittest.TestCase):
    def test_generic_nontrivial_precision(self):
        result = check_certificate(fixture())
        self.assertEqual(result["status"], "CERTIFIED_DISTINCT")
        self.assertEqual(result["determinant_residue"], [7, 0])
        self.assertEqual(result["determinant_valuation"], 1)

    def test_existing_pilot_finite_adapter(self):
        result = check_certificate(fixture("pilot-line-certificate.json"))
        self.assertEqual(result["status"], "CERTIFIED_DISTINCT")
        self.assertEqual(result["determinant_residue"], [75, 0, 0])
        self.assertEqual(result["determinant_valuation"], 2)

    def test_insufficient_precision_is_inconclusive(self):
        data = fixture()
        data["ring"]["precision"] = 1
        for key in ("analytic", "exceptional"):
            data[key]["coordinates"] = [[x % 7 for x in c] for c in data[key]["coordinates"]]
        result = check_certificate(data)
        self.assertEqual(result["status"], "INCONCLUSIVE")
        self.assertIsNone(result["determinant_valuation"])
        self.assertEqual(result["determinant_valuation_lower_bound"], 1)

    def test_coincident_residues_do_not_certify_equality(self):
        data = fixture()
        data["exceptional"] = deepcopy(data["analytic"])
        result = check_certificate(data)
        self.assertEqual(result["status"], "INCONCLUSIVE")
        self.assertNotIn("equal", result)

    def test_unit_field_rescaling_preserves_separation(self):
        data = fixture()
        # Multiply (1,theta) by 1+theta, using theta^2=-1.
        data["analytic"]["coordinates"] = [[1, 1], [342, 1]]
        result = check_certificate(data)
        self.assertEqual(result["determinant_residue"], [7, 7])
        self.assertEqual(result["determinant_valuation"], 1)

    def test_integral_common_basis_change(self):
        data = fixture()
        # Apply [[1,1],[1,2]], determinant1, to both vectors.
        for key in ("analytic", "exceptional"):
            a, b = data[key]["coordinates"]
            data[key]["coordinates"] = [
                [(ai + bi) % 343 for ai, bi in zip(a, b)],
                [(ai + 2 * bi) % 343 for ai, bi in zip(a, b)],
            ]
        self.assertEqual(check_certificate(data)["determinant_residue"], [7, 0])

    def test_degree_one_coefficient_field(self):
        data = fixture()
        data["ring"]["modulus_polynomial"] = [0, 1]
        data["analytic"]["coordinates"] = [[1], [0]]
        data["exceptional"]["coordinates"] = [[0], [1]]
        self.assertEqual(check_certificate(data)["determinant_residue"], [1])

    def test_irreducible_counts(self):
        # Independent known counts (p^d-p)/d for d=2,3 and
        # (p^4-p^2)/4 for d=4; this exercises composite degrees too.
        for p, counts in ((3, {1: 3, 2: 3, 3: 8, 4: 18}),
                          (5, {1: 5, 2: 10, 3: 40, 4: 150})):
            for degree, expected in counts.items():
                count = sum(is_irreducible(list(c) + [1], p)
                            for c in product(range(p), repeat=degree))
                self.assertEqual(count, expected, (p, degree))

    def test_repeated_factor_rejected(self):
        self.assertFalse(is_irreducible([-1, 0, 0, 1], 3))

    def test_invalid_inputs_rejected(self):
        mutations = {
            "composite prime": lambda d: d["ring"].update(p=9),
            "zero precision": lambda d: d["ring"].update(precision=0),
            "reducible field": lambda d: d["ring"].update(modulus_polynomial=[-1, 0, 1]),
            "nonmonic field": lambda d: d["ring"].update(modulus_polynomial=[1, 0, 2]),
            "different basis": lambda d: d["analytic"].update(basis_id="different"),
            "missing coordinate": lambda d: d["analytic"].update(coordinates=[[1, 0]]),
            "wrong field degree": lambda d: d["analytic"].update(coordinates=[[1], [0]]),
            "nonprimitive vector": lambda d: d["analytic"].update(coordinates=[[7, 0], [0, 7]]),
            "zero vector": lambda d: d["analytic"].update(coordinates=[[0, 0], [0, 0]]),
            "negative residue": lambda d: d["analytic"].update(coordinates=[[-1, 0], [0, 1]]),
            "oversized residue": lambda d: d["analytic"].update(coordinates=[[343, 0], [0, 1]]),
            "Boolean residue": lambda d: d["analytic"].update(coordinates=[[True, 0], [0, 1]]),
            "different error ideal": lambda d: d.update(error_ideal="unknown"),
            "missing binding": lambda d: d["source_bindings"].update(precision=""),
        }
        for label, mutate in mutations.items():
            with self.subTest(label=label):
                data = fixture()
                mutate(data)
                with self.assertRaises(CertificateError):
                    check_certificate(data)


if __name__ == "__main__":
    unittest.main(verbosity=2)
