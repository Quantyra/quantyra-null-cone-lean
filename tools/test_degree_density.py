"""Finite branch audit, exhaustive small realizable orders and corruptions."""
from copy import deepcopy
from fractions import Fraction as F
from itertools import permutations
from math import isqrt
import unittest

from degree_density import constant_certificate, estimate, verify
from finite_data_core import InvalidOrder
from degree_density_models import class_audit, coefficients, density, truth_cells, metrics
from audit_degree_density_practical import exact_truth, metric


class DegreeDensityTests(unittest.TestCase):
    def test_polynomial_extrema_and_global_orientation(self):
        self.assertEqual(len(class_audit()), 4)
        for family, c in [('fgm', F(-1, 2)), ('asymmetric', F(1, 4)), ('boundary8', F(1, 8)), ('legendre4', F(1, 16))]:
            avg, lo, hi = truth_cells(8, family, c)
            self.assertEqual((avg, lo, hi), exact_truth({'family': family, 'coefficient': str(c), 'grid': 8}))
            self.assertEqual(sum(avg)/64, 1)
            for i in range(8):
                for j in range(8):
                    for x in range(5):
                        for y in range(5):
                            value = density(F(4*i+x, 32), F(4*j+y, 32), family, c)
                            self.assertLessEqual(lo[8*i+j], value)
                            self.assertLessEqual(value, hi[8*i+j])
            actual = metrics([1]*64, [F(1, 2)]*64, [F(3, 2)]*64, F(1, 2), (avg, lo, hi), 8)
            self.assertEqual(actual, metric([1]*64, [F(1, 2)]*64, [F(3, 2)]*64, F(1, 2), (avg, lo, hi), 8))
            self.assertTrue(actual['joint_density_coverage'])
            self.assertEqual(F(actual['quotient_sup_error']), abs(c))
        # Neither single orientation succeeds, even if a cellwise choice could.
        truth = ([1]*4, [F(1, 2), F(3, 2), F(1, 2), F(3, 2)], [F(1, 2), F(3, 2), F(1, 2), F(3, 2)])
        got = metrics([F(1, 2)]*4, [F(1, 2)]*4, [F(1, 2), F(3, 2), F(3, 2), F(1, 2)], 1, truth, 2)
        self.assertFalse(got['joint_density_coverage'])

    def test_baseline_interface_on_fixed_order(self):
        from finite_data import estimate as baseline, verify_report
        import json
        order = {'n': 4, 'relations': [[0, 2], [0, 3], [1, 3]]}
        report = baseline(order, k=2)
        reloaded = json.loads(json.dumps(report, default=str))
        self.assertTrue(verify_report(reloaded))
        self.assertTrue(verify(order, estimate(order)))

    def test_all_supported_constants_and_retained_shell_budgets(self):
        cases = 0
        for n in range(2, 4097):
            cert = constant_certificate(n)
            self.assertLess(cert['mesh_upper_bound'], 65536)
            # Independent integer square check for the supplied upper mesh.
            b = cert['mesh_upper_bound']
            self.assertLessEqual(4*b*b, n)
            self.assertGreater(4*(b+1)*(b+1), n)
            for m in range(1, isqrt(n)+1):
                self.assertGreaterEqual(F(6*32, m), 3)
                cases += 1
        self.assertEqual(cases, 172767)

    def test_small_orders_and_relabeling(self):
        for n in range(2, 6):
            for second in permutations(range(n)):
                ranks = {v: i for i, v in enumerate(second)}
                relations = [[i, j] for i in range(n) for j in range(i+1, n) if ranks[i] < ranks[j]]
                for rel in [relations, [[n-1-i, n-1-j] for i, j in relations]]:
                    order = {'n': n, 'relations': rel}
                    a = estimate(order)
                    self.assertTrue(verify(order, a))
                    self.assertEqual((a['density'], a['radius'], a['lower'], a['upper']), ('1', '1/2', '1/2', '3/2'))

    def test_invalid_inputs(self):
        cases = [
            {'n': 2, 'relations': [[0, 0]]},
            {'n': 2, 'relations': [[0, 1], [1, 0]]},
            {'n': 3, 'relations': [[0, 1], [1, 2]]},
            {'n': 2, 'relations': [[0, 1], [0, 1]]},
            {'n': 2, 'relations': [[0, True]]},
            {'n': 1, 'relations': []},
            {'n': 4097, 'relations': []},
            # Standard example S_3 has dimension three.
            {'n': 6, 'relations': [[i, 3+j] for i in range(3) for j in range(3) if i != j]},
        ]
        for order in cases:
            with self.assertRaises((ValueError, InvalidOrder)):
                estimate(order)

    def test_report_corruptions(self):
        order = {'n': 3, 'relations': [[0, 1], [0, 2], [1, 2]]}
        report = estimate(order)
        mutations = [lambda a: a.update(radius='1/3'), lambda a: a.update(upper='7/4'),
                     lambda a: a['constants'].update(mesh_upper_bound=100),
                     lambda a: a['first'].reverse(), lambda a: a['inclusive_first_ranks'].reverse(),
                     lambda a: a.update(resource_fallback=True), lambda a: a.update(n=4)]
        for mutate in mutations:
            a = deepcopy(report); mutate(a)
            with self.assertRaises((ValueError, InvalidOrder)):
                verify(order, a)


if __name__ == '__main__':
    unittest.main()
