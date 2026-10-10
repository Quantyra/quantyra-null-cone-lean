"""Deterministic fixtures before S047's frozen evaluation."""
import unittest
from fractions import Fraction as F

from marked_volume import Interval
from quantum_measurement import (baseline_box, joint_loglikelihood,
                                 marginal_intervals, probabilities, project_box)


class ModelTests(unittest.TestCase):
    def test_confounded_full_records(self):
        self.assertEqual(probabilities(F(2, 5), F(3, 4), F(1, 2)),
                         probabilities(F(3, 5), F(1, 2), F(3, 4)))
        point = Interval(F(3, 10), F(3, 10))
        efficiency = Interval(F(1, 2), F(1))
        r = project_box(point, point, efficiency, efficiency)
        self.assertEqual((r.lower, r.upper), (F(2, 5), F(3, 5)))

    def test_known_efficiencies_and_state_boundary(self):
        for p in (F(0), F(1, 3), F(1)):
            rp, rm, _ = probabilities(p, F(2, 3), F(3, 4))
            intervals = tuple(Interval(x, x) for x in (rp, rm, F(2, 3), F(3, 4)))
            result = project_box(*intervals)
            self.assertEqual((result.lower, result.upper), (p, p))
            self.assertEqual(result, baseline_box(*intervals))

    def test_empty_calibration_and_projection_fallback(self):
        full = Interval(F(0), F(1))
        low = Interval(F(0), F(1, 4))
        self.assertEqual(project_box(full, full, low, full).fallback,
                         "empty_calibration")
        high = Interval(F(9, 10), F(1))
        self.assertEqual(project_box(high, high, full, full).fallback,
                         "empty_projection")
        self.assertEqual(project_box(high, high, full, full),
                         baseline_box(high, high, full, full))

    def test_zero_blocks_and_invalid_full_record(self):
        report = project_box(*marginal_intervals(0, 0, 0, 0, 0, 0))
        self.assertEqual((report.lower, report.upper), (F(0), F(1)))
        with self.assertRaises(ValueError):
            marginal_intervals(4, 3, 2, 1, 0, 0)

    def test_likelihood_gradient_independent_finite_difference(self):
        import numpy as np
        x = np.array([.4, .6, .8])
        counts = (10, 2, 5, 8, 5, 6)
        _, gradient = joint_loglikelihood(x, counts)
        for j in range(3):
            step = np.zeros(3)
            step[j] = 1e-6
            numeric = (joint_loglikelihood(x+step, counts)[0]
                       -joint_loglikelihood(x-step, counts)[0])/2e-6
            self.assertAlmostEqual(float(gradient[j]), numeric, places=6)

    def test_independent_tail_horner_against_direct_polynomial(self):
        from math import comb
        from audit_quantum_measurement_study import cdf_numerator
        for n in range(7):
            for k in range(n+1):
                for numerator in range(8):
                    expected = sum(comb(n, j)*numerator**j*(7-numerator)**(n-j)
                                   for j in range(k+1))
                    self.assertEqual(cdf_numerator(n, k, numerator, 7-numerator), expected)


if __name__ == "__main__":
    unittest.main()
