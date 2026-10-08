"""Independent exhaustive combinatorics and rational LP/certificate tests."""
import copy
import json
import unittest
from unittest.mock import patch
from types import SimpleNamespace
from fractions import Fraction as F
from itertools import permutations, combinations
from finite_data_core import (order_rows, realizer, ranks, certify_realizer,
                              forcing_certificate, verify_forcing_certificate,
                              calibration, calibration_radius, exp_negative_upper, InvalidOrder,
                              verify_split_calibration_fields, _round_failure_upper, corner_counts)
from finite_data_lp import model, solve, verify_bounds, dual_lower_bound
from finite_data import estimate, verify_report
from benchmark_finite_data import cdf_errors, truth_cell_ranges


def permutation_order(second):
    n = len(second)
    pos = ranks(second)
    return order_rows(n, [(i, j) for i in range(n) for j in range(n)
                          if i < j and pos[i] < pos[j]])


def brute_realizers(rows):
    """Independently enumerate first orders and derive the complementary one."""
    n = len(rows)
    for first in permutations(range(n)):
        x = ranks(first)
        if any(x[u] >= x[v] for u in range(n) for v in range(n) if rows[u] & (1 << v)):
            continue
        second_relation = [[bool(rows[u] & (1 << v)) or
                            (u != v and not rows[u] & (1 << v) and
                             not rows[v] & (1 << u) and x[u] > x[v])
                            for v in range(n)] for u in range(n)]
        indegrees = [sum(second_relation[u][v] for u in range(n)) for v in range(n)]
        if sorted(indegrees) != list(range(n)):
            continue
        second = sorted(range(n), key=indegrees.__getitem__)
        y = ranks(second)
        if all(second_relation[u][v] == (y[u] < y[v]) for u in range(n) for v in range(n)):
            yield list(first), second


class CDFEncodingTests(unittest.TestCase):
    def test_lean_density_matrix_residual_and_band_fixtures(self):
        # Literal expectations match DensityReportFixtures.lean, including row order.
        counts = corner_counts([0, 1, 2], [0, 1, 2], 2)
        self.assertEqual(counts, [[0, 0, 0], [0, 1, 1], [0, 1, 3]])
        lp = model(counts, 3, F(1, 10))
        expected_a = [
            [0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0], [0,0,0,0],
            [0,0,0,0], [0,0,0,0], [1,0,0,0], [-1,0,0,0], [1,1,0,0], [-1,-1,0,0],
            [0,0,0,0], [0,0,0,0], [1,0,1,0], [-1,0,-1,0], [1,1,1,1], [-1,-1,-1,-1],
            [1,0,-1,0], [-1,0,1,0], [1,-1,0,0], [-1,1,0,0],
            [0,1,0,-1], [0,-1,0,1], [0,0,1,-1], [0,0,-1,1]]
        expected_b = ([F(2, 5)]*8 + [F(26, 15), F(-14, 15)]*2 + [F(2, 5)]*2 +
                      [F(26, 15), F(-14, 15), F(22, 5), F(-18, 5)] + [F(1)]*8)
        self.assertEqual(lp['A'], expected_a)
        self.assertEqual(lp['b'], expected_b)
        self.assertEqual(lp['E'], [[1,1,0,0], [0,0,1,1], [1,0,1,0], [0,1,0,1]])
        self.assertEqual(lp['d'], [F(2)]*4)
        y, z, c = [F(0)]*26, [F(1, 3), 0, 0, F(-1, 5)], [1, 0, 0, 0]
        y[8] = F(-1)
        residual = [F(c[j])-sum(row[j]*v for row, v in zip(lp['A'], y))-
                    sum(row[j]*v for row, v in zip(lp['E'], z)) for j in range(4)]
        self.assertEqual(residual, [F(5, 3), F(-2, 15), 0, F(1, 5)])
        self.assertEqual(dual_lower_bound(lp, c, y, z), F(-11, 15))
        # All corner excesses are checked, including zero/full prefixes.
        excess = max([F(0)] + [abs(F(p*q, 4)-F(counts[p][q], 3))-F(1, 10)
                              for p in range(3) for q in range(3)])
        self.assertEqual(excess, F(1, 15))
        self.assertEqual(min(F(1), 8*F(1, 10)*4+4*excess*4+F(2, 2)), 1)
        y[8] = F(1)
        with self.assertRaises(ValueError):
            dual_lower_bound(lp, c, y, z)

    def test_lean_permutation_and_inclusive_corner_fixtures(self):
        # Matches CDFReportFixtures.lean; vertex 2 is at zero-based position 0.
        self.assertEqual([value-1 for value in ranks([2, 0, 1])], [1, 2, 0])
        counts = corner_counts([0, 1, 2], [0, 1, 2], 3)
        self.assertEqual(counts[1][1], 1)  # exact grid tie is included
        self.assertEqual(counts[0][3], 0)
        self.assertEqual(counts[3][3], 3)


class RealizerTests(unittest.TestCase):
    def test_exhaustive_five_point_realizers_and_rank_certificate(self):
        count = 0
        for latent_second in permutations(range(5)):
            rows = permutation_order(latent_second)
            first, second = realizer(rows)
            certify_realizer(rows, first, second)
            cert = forcing_certificate(rows, first)
            verify_forcing_certificate(rows, first, cert)
            chosen = [ranks(first), ranks(second)]
            for a, b in brute_realizers(rows):
                count += 1
                other = [ranks(a), ranks(b)]
                # One common swap must control both coordinates at every vertex.
                self.assertTrue(any(all(abs(chosen[c][i]-other[c ^ swap][i]) <=
                                             cert['unresolved_degrees'][i]
                                             for c in range(2) for i in range(5))
                                    for swap in (0, 1)))
        self.assertEqual(count, 771)

    def test_all_natural_five_point_posets(self):
        edges = list(combinations(range(5), 2))
        checked = 0
        for mask in range(1 << len(edges)):
            try:
                rows = order_rows(5, [edge for i, edge in enumerate(edges) if mask & (1 << i)])
            except InvalidOrder:
                continue
            possible = next(brute_realizers(rows), None) is not None
            try:
                first, second = realizer(rows)
            except InvalidOrder:
                self.assertFalse(possible)
            else:
                self.assertTrue(possible)
                certify_realizer(rows, first, second)
            checked += 1
        self.assertEqual(checked, 357)

    def test_six_point_permutations(self):
        for second in permutations(range(6)):
            rows = permutation_order(second)
            first, recovered = realizer(rows)
            certify_realizer(rows, first, recovered)

    def test_invalid_and_dimension_three(self):
        for n, rel in [(2, [(0, 0)]), (2, [(0, 1), (1, 0)]),
                       (3, [(0, 1), (1, 2)]), (2, [(0, 1), (0, 1)]),
                       (2, [(False, 1)]), (0, []), (2, [(0, 2)])]:
            with self.assertRaises(InvalidOrder):
                order_rows(n, rel)
        crown = order_rows(6, [(i, 3+j) for i in range(3) for j in range(3) if i != j])
        with self.assertRaises(InvalidOrder):
            realizer(crown)


class LPTests(unittest.TestCase):
    def test_solver_failure_keeps_conservative_coverage(self):
        with patch('scipy.optimize.linprog', return_value=SimpleNamespace(success=False, status=1)):
            report = estimate({'n': 4, 'relations': [[0, 2], [0, 3], [1, 3]]}, 2)
        self.assertEqual(report['bands']['status'], 'solver_failed_conservative_fallback')
        self.assertEqual(report['bands']['point_lower'], [F(1, 2)]*4)
        self.assertEqual(report['bands']['point_upper'], [F(3, 2)]*4)
        self.assertEqual(report['bands']['histogram_error_upper'], 1)
        self.assertTrue(verify_report(json.loads(json.dumps(report, default=str))))
        for field, value in [('cell_lower', F(1)), ('cell_upper', F(1)),
                             ('point_lower', F(1)), ('point_upper', F(1))]:
            changed = copy.deepcopy(report)
            changed['bands'][field][0] = value
            with self.assertRaisesRegex(ValueError, 'whole density range'):
                verify_report(changed)

    def test_continuum_diagnostics_include_one_sided_limits(self):
        report = {'input': {'n': 4}, 'first': [0, 1, 2, 3], 'second': [0, 1, 2, 3]}
        self.assertEqual(cdf_errors(report, 'flat', 0), [0.25, 0.25])
        for family, c in [('fgm', F(1, 2)), ('asymmetric', F(1, 4))]:
            averages, lows, highs = truth_cell_ranges(8, family, c)
            for avg, low, high in zip(averages, lows, highs):
                self.assertLessEqual(low, avg)
                self.assertLessEqual(avg, high)
                self.assertLessEqual(max(avg-low, high-avg), F(2, 8))

    def test_exact_population_corners_and_corrupted_certificate(self):
        lp = model([[0, 0, 0], [0, 9, 16], [0, 16, 32]], 32, F(0))
        result = solve(lp)
        self.assertTrue(verify_bounds(lp, result))
        truth = [F(9, 8), F(7, 8), F(7, 8), F(9, 8)]
        for lo, value, hi in zip(result['cell_lower'], truth, result['cell_upper']):
            self.assertLessEqual(lo, value)
            self.assertLessEqual(value, hi)
            self.assertLess(hi-lo, F(1, 10**8))
        altered = copy.deepcopy(result)
        altered['certificates'][0]['lower_bound'] += F(1, 100)
        with self.assertRaises(ValueError):
            verify_bounds(lp, altered)

    def test_exact_two_by_two_optima_with_radius(self):
        lp = model([[0, 0, 0], [0, 9, 16], [0, 16, 32]], 32, F(1, 100))
        result = solve(lp)
        # Every marginal-feasible 2x2 matrix is [t,2-t;2-t,t].
        lo, hi = F(1, 2), F(3, 2)
        for row, rhs in zip(lp['A'], lp['b']):
            slope = row[0]+row[3]-row[1]-row[2]
            intercept = 2*(row[1]+row[2])
            if slope > 0:
                hi = min(hi, (rhs-intercept)/slope)
            elif slope < 0:
                lo = max(lo, (rhs-intercept)/slope)
            else:
                self.assertLessEqual(intercept, rhs)
        for index, (actual_lo, actual_hi) in enumerate(zip(result['cell_lower'], result['cell_upper'])):
            expected_lo, expected_hi = (lo, hi) if index in (0, 3) else (2-hi, 2-lo)
            self.assertLessEqual(actual_lo, expected_lo)
            self.assertLessEqual(expected_hi, actual_hi)
            self.assertLess(expected_lo-actual_lo, F(1, 10**8))
            self.assertLess(actual_hi-expected_hi, F(1, 10**8))

    def test_arbitrary_nonstationary_duals_still_bound_feasible_truth(self):
        lp = model([[0, 0, 0], [0, 9, 16], [0, 16, 32]], 32, F(0))
        truth = [F(9, 8), F(7, 8), F(7, 8), F(9, 8)]
        y = [-F(i % 7, 13) for i in range(len(lp['A']))]
        z = [F(i-2, 7) for i in range(len(lp['E']))]
        for cell in range(4):
            objective = [int(i == cell) for i in range(4)]
            self.assertLessEqual(dual_lower_bound(lp, objective, y, z), truth[cell])
        y[0] = F(1)
        with self.assertRaises(ValueError):
            dual_lower_bound(lp, [1, 0, 0, 0], y, z)

    def test_report_round_trip_and_adversarial_changes(self):
        report = estimate({'n': 4, 'relations': [[0, 2], [0, 3], [1, 3]]}, 2)
        decoded = json.loads(json.dumps(report, default=str))
        self.assertTrue(verify_report(decoded))
        for field in ('cdf', 'rank', 'band', 'realizer'):
            changed = copy.deepcopy(decoded)
            if field == 'cdf':
                changed['confidence']['cdf_radius'] = '0'
            elif field == 'rank':
                changed['confidence']['rank_certificate']['trim_cutoff'] = -1
            elif field == 'band':
                changed['bands']['point_lower'][0] = '3/2'
            else:
                changed['first'] = list(reversed(changed['first']))
            with self.assertRaises((ValueError, KeyError)):
                verify_report(changed)

    def test_calibration_is_outward_and_valid(self):
        for delta in [F(1, 20), F(1, 100)]:
            cal = calibration(512, delta)
            raw = 2*(cal['q']+1)**2*exp_negative_upper(2*512*cal['epsilon']**2)
            self.assertLessEqual(raw, cal['failure_upper'])
            self.assertLessEqual(cal['failure_upper'], delta)

    def test_split_calibration_failure_allocation_and_prior_improvement(self):
        for n in (512, 3072, 4096):
            for delta in (F(1, 20), F(1, 100)):
                cal = calibration(n, delta, 'split-dkw')
                self.assertEqual(cal['marginal_budget']+cal['joint_budget'], delta)
                for name, prefactor in [('marginal', 4), ('joint', 2*(cal['q']+1)**2)]:
                    raw = prefactor*exp_negative_upper(2*n*cal[name+'_epsilon']**2)
                    self.assertLessEqual(raw, cal[name+'_failure_upper'])
                    self.assertLessEqual(cal[name+'_failure_upper'], cal[name+'_budget'])
                self.assertLessEqual(cal['failure_upper'], delta)
                self.assertLess(calibration_radius(cal, 'split-dkw'),
                                calibration_radius(calibration(n, delta), 'grid'))
        self.assertLess(calibration_radius(calibration(3072, F(1, 20), 'split-dkw'), 'split-dkw'), F(1, 8))
        # Cached calibration values cannot be poisoned by a returned mutable dict.
        cal['q'] = 1
        self.assertNotEqual(calibration(4096, F(1, 100), 'split-dkw')['q'], 1)

    def test_both_report_methods_and_corrupted_split_calibration(self):
        order = {'n': 4, 'relations': [[0, 2], [0, 3], [1, 3]]}
        for method in ('grid', 'split-dkw'):
            report = json.loads(json.dumps(estimate(order, 2, calibration_method=method), default=str))
            self.assertTrue(verify_report(report))
            if method == 'grid':
                del report['calibration_method']
                self.assertTrue(verify_report(report))
            else:
                for key in ('method', 'marginal_epsilon', 'joint_epsilon', 'marginal_budget',
                            'joint_budget', 'marginal_failure_upper', 'joint_failure_upper'):
                    changed = copy.deepcopy(report)
                    changed['confidence']['calibration'][key] = 'grid' if key == 'method' else '0'
                    with self.assertRaises(ValueError):
                        verify_report(changed)

    def test_split_extreme_budget_uses_deterministic_fallback(self):
        report = estimate({'n': 1, 'relations': []}, 1, F(1, 10**100))
        self.assertEqual(report['confidence']['cdf_radius'], 1)
        self.assertEqual(report['confidence']['failure_upper'], 0)
        self.assertTrue(verify_report(json.loads(json.dumps(report, default=str))))
        for method, delta in [('unknown', F(1, 20)), ('split-dkw', F(0)), ('split-dkw', F(1))]:
            with self.assertRaises(ValueError):
                calibration(64, delta, method)

    def test_independent_split_checker_rejects_nontrivial_budget_failure(self):
        # A fabricated low-radius calibration has exact rounding but fails its
        # claimed probability budgets; checking rounding alone is insufficient.
        n, q, epsilon, budget = 1, 100, F(1, 10), F(1, 40)
        marginal = min(F(1), 4*exp_negative_upper(2*n*epsilon**2))
        joint = min(F(1), 2*(q+1)**2*exp_negative_upper(2*n*epsilon**2))
        rounded_m, rounded_j = (_round_failure_upper(raw, budget) for raw in (marginal, joint))
        cal = {'method': 'split-dkw', 'q': q, 'requested_delta': 2*budget,
               'marginal_epsilon': epsilon, 'joint_epsilon': epsilon,
               'marginal_budget': budget, 'joint_budget': budget,
               'marginal_failure_upper': rounded_m, 'joint_failure_upper': rounded_j,
               'failure_upper': min(F(1), rounded_m+rounded_j)}
        with self.assertRaisesRegex(ValueError, 'exceeds its budget'):
            verify_split_calibration_fields(n, cal)
        # Raising the joint tolerance forces radius one; exact but over-budget
        # calibration is then sound as a deterministic fallback.
        cal['joint_epsilon'] = F(1)
        raw = min(F(1), 2*(q+1)**2*exp_negative_upper(2*n))
        cal['joint_failure_upper'] = _round_failure_upper(raw, budget)
        cal['failure_upper'] = min(F(1), rounded_m+cal['joint_failure_upper'])
        self.assertTrue(verify_split_calibration_fields(n, cal))
        cal['joint_failure_upper'] -= F(1, 10**12)
        with self.assertRaisesRegex(ValueError, 'rounded split failure'):
            verify_split_calibration_fields(n, cal)


if __name__ == '__main__':
    unittest.main()
