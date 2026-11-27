"""Adversarial certificate checks: corrupted input must be rejected."""

import copy
import json
from pathlib import Path
import unittest

import verify_certificate as checker

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    return json.loads((ROOT / "data" / name).read_text())


class RejectMalformedCertificates(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ss = load("supersingular-389.json")
        cls.cm = load("cm-jet-p5.json")
        cls.coeffs = load("H-minus44375-coeffs.json")
        cls.lifts = load("CM-minus44375-lifts32.json")
        cls.lookup = dict(zip(map(tuple, cls.ss["supersingular_j"]), cls.ss["primitive_eigenvectors"][0]))

    def test_wrong_isogeny_multiplicity(self):
        data = copy.deepcopy(self.ss)
        row = data["brandt_T2_function_matrix"][0]
        occupied = next(i for i, v in enumerate(row) if v)
        row[occupied] -= 1
        row[(occupied + 1) % len(row)] += 1
        with self.assertRaisesRegex(ValueError, "factorization"):
            checker.verify_supersingular(data)

    def test_incomplete_cm_cycle(self):
        data = copy.deepcopy(self.cm)
        data["class_generator_cycle"][1] = data["class_generator_cycle"][0]
        with self.assertRaisesRegex(ValueError, "permutation"):
            checker.verify_jet(self.coeffs, self.lifts, data, self.lookup)

    def test_forged_nonzero_residue(self):
        data = copy.deepcopy(self.cm)
        data["raw_quadratic_jet_mod5"][2] = 2
        with self.assertRaisesRegex(ValueError, "residues"):
            checker.verify_jet(self.coeffs, self.lifts, data, self.lookup)

    def test_insufficient_hensel_precision(self):
        low_precision_lifts = [[a % (389 ** 6), b % (389 ** 6)] for a, b in self.lifts]
        with self.assertRaisesRegex(ValueError, "Hensel precision"):
            checker.verify_hensel(self.coeffs, low_precision_lifts)

    def test_duplicate_root_balls(self):
        lifts = copy.deepcopy(self.lifts)
        lifts[1] = lifts[0]
        with self.assertRaisesRegex(ValueError, "disjoint"):
            checker.verify_hensel(self.coeffs, lifts)

    def test_altered_class_polynomial(self):
        coeffs = self.coeffs.copy()
        coeffs[0] += 1
        with self.assertRaisesRegex(ValueError, "Hensel precision"):
            checker.verify_hensel(coeffs, self.lifts)

    def test_modular_zero_is_not_exact_vanishing(self):
        # All these series have the same degree-two jet modulo 5.
        polynomials = [[5, 0, 1], [0, 5, 1], [0, 0, 1]]
        jets = [[c % 5 for c in f] for f in polynomials]
        orders = [next(i for i, c in enumerate(f) if c) for f in polynomials]
        self.assertEqual(jets, [[0, 0, 1]] * 3)
        self.assertEqual(orders, [0, 1, 2])

    def test_prime_two_needs_extra_level(self):
        self.assertNotEqual(__import__("math").comb(2, 2) % 2, 0)
        self.assertEqual(__import__("math").comb(4, 2) % 2, 0)


if __name__ == "__main__":
    unittest.main()
