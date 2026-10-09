"""Probability, orientation and rejection checks for the S031 candidates."""
import copy
import itertools
import math
import tempfile
import unittest
from pathlib import Path
from fractions import Fraction as F
from finite_data_core import order_rows, forcing_certificate, certify_realizer, ranks
from finite_data_local_mass import (binomial_cdf_integer, binomial_lower,
    count_brackets, estimate, verify_report, calibration, verify_calibration)


class LocalMassTests(unittest.TestCase):
    def test_integer_tail_against_definition(self):
        for n in range(1, 13):
            for p in (F(0), F(1, 7), F(1, 2), F(6, 7), F(1)):
                for x in range(-1, n+1):
                    a, b = binomial_cdf_integer(n, x, p)
                    exact = sum(F(math.comb(n, t))*p**t*(1-p)**(n-t)
                                for t in range(max(0, min(n, x)+1)))
                    self.assertEqual(F(a, b), exact)

    def test_finite_binomial_coverage_and_monotonicity(self):
        alpha = F(1, 40)
        for n in range(1, 13):
            lo = [binomial_lower(n, x, alpha, 1024) for x in range(n+1)]
            hi = [1-lo[n-x] for x in range(n+1)]
            self.assertEqual(lo, sorted(lo))
            self.assertEqual(hi, sorted(hi))
            for p in (F(0), F(1, 17), F(1, 3), F(1, 2), F(16, 17), F(1)):
                bad = sum(F(math.comb(n, x))*p**x*(1-p)**(n-x)
                          for x in range(n+1) if not lo[x] <= p <= hi[x])
                self.assertLessEqual(bad, 2*alpha)

    def test_every_small_realizer_has_one_alignment(self):
        # All 24 permutation orders, all 576 possible pairs of realizers.
        n, k = 4, 3
        perms = list(itertools.permutations(range(n)))
        for second in perms:
            true_x, true_y = ranks(range(n)), ranks(second)
            rel = [(i, j) for i in range(n) for j in range(n)
                   if true_x[i] < true_x[j] and true_y[i] < true_y[j]]
            rows = order_rows(n, rel)
            for a in perms:
                for b in perms:
                    try:
                        certify_realizer(rows, list(a), list(b))
                    except ValueError:
                        continue
                    cert = forcing_certificate(rows, list(a))
                    bracket = count_brackets(a, b, cert['unresolved_degrees'], k, F(0))
                    aligned = []
                    for x, y in ((true_x, true_y), (true_y, true_x)):
                        counts = [sum(i*n < k*x[t] <= (i+1)*n and
                                      j*n < k*y[t] <= (j+1)*n for t in range(n))
                                  for i in range(k) for j in range(k)]
                        ax, ay = ranks(a), ranks(b)
                        rank_ok = all(max(abs(ax[t]-x[t]), abs(ay[t]-y[t])) <=
                                      cert['unresolved_degrees'][t] for t in range(n))
                        aligned.append(rank_ok and all(l <= c <= u for l, c, u in
                            zip(bracket['lower_counts'], counts, bracket['upper_counts'])))
                    self.assertTrue(any(aligned))

    def test_boundaries_and_empty_erosions(self):
        # n=4 normalized ranks include right boundary 1; k=2 internal boundary .5.
        bracket = count_brackets([0, 1, 2, 3], [3, 2, 1, 0], [0]*4, 2, F(0))
        self.assertEqual(bracket['lower_counts'], [0, 2, 2, 0])
        self.assertTrue(all(x <= y for x, y in zip(bracket['lower_counts'], bracket['upper_counts'])))
        bracket = count_brackets([0, 1], [1, 0], [1, 1], 4, F(1))
        self.assertEqual(bracket['lower_counts'], [0]*16)
        self.assertEqual(bracket['upper_counts'], [2]*16)
        full = count_brackets([0, 1], [1, 0], [1, 1], 1, F(1))
        self.assertEqual(full['lower_counts'], [2])

    def test_calibration_budget_corruption(self):
        for variant in ('bernstein', 'binomial'):
            cal = dict(calibration(3072, 8, F(1, 20), variant))
            verify_calibration(3072, 8, F(1, 20), cal)
            cal['marginal_epsilon'] = F(0)
            with self.assertRaises(ValueError):
                verify_calibration(3072, 8, F(1, 20), cal)

    def test_report_corruption_rejected(self):
        n = 12
        second = [7, 1, 9, 2, 11, 4, 0, 6, 8, 3, 10, 5]
        y = ranks(second)
        order = {'n': n, 'relations': [(i, j) for i in range(n) for j in range(n)
                                     if i < j and y[i] < y[j]]}
        for variant in ('bernstein', 'binomial'):
            report = estimate(order, 2, variant=variant)
            self.assertTrue(verify_report(report))
            edits = [lambda r: r['brackets']['lower_counts'].__setitem__(0, 11),
                     lambda r: r['mass']['lower'].__setitem__(0, F(1)),
                     lambda r: r['bands']['point_upper'].__setitem__(0, F(1)),
                     lambda r: r['bands']['histogram'].__setitem__(0, F(0)),
                     lambda r: r['bands'].__setitem__('histogram_error_upper', F(0)),
                     lambda r: r['bands']['certificates'][0].__setitem__('lower_bound', F(9))]
            for edit in edits:
                corrupt = copy.deepcopy(report)
                edit(corrupt)
                with self.assertRaises((ValueError, KeyError)):
                    verify_report(corrupt)

    def test_shared_artifact_hash_and_size_rejection(self):
        from run_finite_data_feasibility import artifact, read_artifact
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder)/'shared.json.gz'
            first = artifact(path, {'data': [1, 2, 3]})
            self.assertEqual(first, artifact(path, {'data': [1, 2, 3]}))
            with self.assertRaises(ValueError):
                artifact(path, {'data': [3, 2, 1]})
            with self.assertRaises(ValueError):
                read_artifact(path, 2)


if __name__ == '__main__':
    unittest.main()
