"""Deterministic correctness fixtures; no evaluation sample generation."""
import copy
from fractions import Fraction as F
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parent))
import numpy as np
from geometric_pair import (GRID, L, C, K, P0, PMAX, BASE_RADIUS, pair_probability,
    inverse_bracket, estimate, verify_report, relation_count, reference_relation_count,
    exact_log_certificate)
from run_geometric_pair_study import flat_transform, plan, protocol
from audit_geometric_pair_study import time_sorted_count, interval


class GeometricPairTests(unittest.TestCase):
    def test_constants_and_inverse(self):
        self.assertEqual(K, F(225225, 54952))
        self.assertEqual(pair_probability(0), P0)
        self.assertEqual(pair_probability(F(1, 2)), PMAX)
        self.assertTrue(exact_log_certificate())
        for k in range(101):
            theta = F(k, 200)
            lo, hi = inverse_bracket(pair_probability(theta))
            self.assertLessEqual(lo, theta)
            self.assertGreaterEqual(hi, theta)
            self.assertLessEqual(hi-lo, F(1, 2**48))

    def test_reports_and_mutations(self):
        for n in (0, 1, 2, 3, 128, 512, 2048, 33338, 74606):
            count = n*(n-1)//2
            for r in sorted({0, count, int(P0*count), int(PMAX*count)}):
                report = estimate(n, r)
                self.assertTrue(verify_report(report))
                wrong = copy.deepcopy(report); wrong['radius'] = '-1'
                self.assertFalse(verify_report(wrong))
                if n >= 2:
                    wrong = copy.deepcopy(report); wrong['raw']['b_upper'] = '0'
                    self.assertFalse(verify_report(wrong))
                    wrong = copy.deepcopy(report); wrong['raw']['lo'] = '3/4'
                    self.assertFalse(verify_report(wrong))
        self.assertEqual(estimate(2048, 0)['branch'], 'midpoint')
        self.assertEqual(estimate(33338, 0)['branch'], 'inverse')
        self.assertLessEqual(F(estimate(74606, 0)['radius']), F(1, 40))

    def test_invalid_counts(self):
        for n, r in ((-1, 0), (3, 4), (3, -1), (True, 0), (3, 1.0)):
            with self.assertRaises(ValueError): estimate(n, r)

    def test_exact_chronology_and_labels(self):
        q = GRID
        # Timelike, exact-null and one-grid-step spacelike/timelike distinctions.
        for x, expected in ((q//2, 0), (q//2-1, 1), (q//2+1, 0)):
            a = np.array([[-q//2, 0, 0], [0, x, 0]], dtype=np.int64)
            self.assertEqual(relation_count(a), expected)
        a = np.array([(t, x, y) for t in range(-3*q//4, q, q//4)
            for x in range(-3*q//4, q, q//4) for y in range(-3*q//4, q, q//4)
            if abs(t) < q and x*x+y*y < (q-abs(t))**2], dtype=np.int64)
        expected = reference_relation_count(a)
        self.assertEqual(time_sorted_count(a), expected)
        for block in (1, 7, 512):
            self.assertEqual(relation_count(a, block), expected)
        self.assertEqual(relation_count(a[::-1]), expected)
        self.assertEqual(relation_count(a[:, [0, 2, 1]]), expected)
        self.assertEqual(relation_count(a*np.array([1, -1, 1])), expected)
        self.assertEqual(relation_count(np.zeros((0, 3), dtype=np.int64)), 0)

    def test_grid_guards(self):
        for a in (np.array([[GRID, 0, 0]], dtype=np.int64),
                  np.array([[0, GRID, 0]], dtype=np.int64), np.zeros((2, 3)),
                  np.array([[2**62, 0, 0]], dtype=np.int64)):
            with self.assertRaises(ValueError): relation_count(a)

    def test_frozen_plan_and_sampler_map(self):
        groups = plan(protocol())
        self.assertEqual(len(groups), 23)
        cases = [c for g in groups for c in g['cases']]
        self.assertEqual(len(cases), 550)
        self.assertEqual(len({c['id'] for c in cases}), 550)
        self.assertEqual(len({tuple(c['seed']) for c in cases}), 550)
        a = flat_transform(np.array([[.25, .875, .25, 0., 0.],
                                     [.75, 0., .25, 0., 0.]]))
        np.testing.assert_allclose(a, [[-.5, .25, 0.], [0., .5, 0.]], atol=1e-15)
        self.assertEqual(interval(32, 32)[1], 1.)
        self.assertAlmostEqual(interval(32, 32)[0], .025**(1/32))


if __name__ == '__main__':
    unittest.main()
