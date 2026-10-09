"""Independent small exact laws, boundary inputs and adversarial quantile proposals."""
import itertools
import sys
import unittest
from fractions import Fraction as F
from math import comb
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/"tools"))
from marked_volume import (Interval, analytic_interval, binomial_tail_numerator,
                           exact_interval, marked_count, retention_interval, verify_interval)


class MarkedVolumeTests(unittest.TestCase):
    def test_tail_against_independent_formula_and_enumerated_bits(self):
        for n in range(7):
            for m in range(5):
                p = F(m, 4)
                weights = [F(comb(n, k))*p**k*(1-p)**(n-k) for k in range(n+1)]
                bitweights = [F(0)]*(n+1)
                for bits in itertools.product((False, True), repeat=n):
                    k = sum(bits)
                    bitweights[k] += p**k*(1-p)**(n-k)
                self.assertEqual(weights, bitweights)
                self.assertEqual(sum(weights), 1)
                for k in range(n+1):
                    self.assertEqual(F(binomial_tail_numerator(n,k,m,4,True),4**n),sum(weights[k:]))
                    self.assertEqual(F(binomial_tail_numerator(n,k,m,4,False),4**n),sum(weights[:k+1]))

    def test_fixed_flags_and_invalid_observations(self):
        rows = [(True,True),(False,True),(True,False),(False,False)]
        self.assertEqual(marked_count(rows),(1,4))
        self.assertEqual(marked_count(reversed(rows)),(1,4))
        for invalid in [[(None,True)],[(1,True)],[(True,)]]:
            with self.assertRaises(ValueError):
                marked_count(invalid)

    def test_exact_coverage_small_laws(self):
        for n in (0,1,2,8,16):
            intervals = [exact_interval(k,n) for k in range(n+1)]
            for k,report in enumerate(intervals):
                self.assertTrue(verify_interval(k,n,report))
            for numerator in range(17):
                p=F(numerator,16)
                coverage=sum(F(comb(n,k))*p**k*(1-p)**(n-k)
                             for k,c in enumerate(intervals) if c.lower<=p<=c.upper)
                self.assertGreaterEqual(coverage,F(19,20))

    def test_proposal_is_not_trusted(self):
        exact_interval.cache_clear()
        with patch('scipy.stats.beta.ppf',return_value=.9),patch('scipy.stats.beta.isf',return_value=.95):
            c=exact_interval(3,10)
            self.assertTrue(c.fallback)
            self.assertTrue(verify_interval(3,10,c))
        exact_interval.cache_clear()
        with patch('scipy.stats.beta.ppf',return_value=float('nan')):
            self.assertTrue(exact_interval(3,10).fallback)
        exact_interval.cache_clear()
        self.assertFalse(verify_interval(3,10,Interval(F(1,2),F(1,2))))

    def test_composition_and_analytic_edge_cases(self):
        for n in (0,1,10,1024):
            for x in range(n+1):
                c=analytic_interval(x,n)
                self.assertEqual(retention_interval(c,F(1)),c)
        for r in (F(1),F(5,4),F(2)):
            c=retention_interval(Interval(F(1,2),F(1,2)),r)
            self.assertEqual(c.upper-c.lower,(r-1)/(r+1))
        with self.assertRaises(ValueError):
            exact_interval(1,0)
        with self.assertRaises(ValueError):
            retention_interval(Interval(F(0),F(1)),F(1,2))


if __name__=='__main__':
    unittest.main()
