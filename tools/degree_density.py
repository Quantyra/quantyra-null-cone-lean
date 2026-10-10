"""Bounded, exact specialization of the accepted S032 degree estimator.

Supports 2 <= n <= 4096, the existing dense order API's range. Throughout
that range the accepted construction selects the flat branch, independently
of the input. No nonflat histogram implementation or improved bound is claimed.
The realizer is still constructed and checked to reject unsupported orders.
"""
import argparse
from fractions import Fraction as F
import json
from math import isqrt
from pathlib import Path

from finite_data_core import order_rows, realizer, certify_realizer, ranks


MAX_N = 4096


def constant_certificate(n):
    if type(n) is not int or not 2 <= n <= MAX_N:
        raise ValueError('degree specialization requires integer 2 <= n <= 4096')
    # log(n) >= log(2) > 1/2, so floor(sqrt(n/(8 log n))) <= floor(sqrt(n/4)).
    bound = isqrt(n // 4)
    assert bound < 65536
    return {'n': n, 'log_lower_bound': '1/2', 'mesh_upper_bound': bound,
            'active_mesh_threshold': 65536, 'accepted_branch': 'flat',
            'radius': '1/2', 'full_square_band': ['1/2', '3/2']}


def estimate(order):
    cert = constant_certificate(order['n'])
    rows = order_rows(order['n'], order['relations'])
    first, second = realizer(rows)
    report = {'schema': 'degree-specialization-v1', 'n': order['n'],
              'first': first, 'second': second,
              'inclusive_first_ranks': ranks(first), 'inclusive_second_ranks': ranks(second),
              'constants': cert, 'density': '1', 'radius': '1/2',
              'lower': '1/2', 'upper': '3/2',
              'status': 'accepted_deterministic_flat_branch',
              'resource_fallback': False,
              'interpretation': 'Full closed-square original-K coverage, one global identity/transpose. '
                                'The density output is label invariant; certificate permutations are not.'}
    verify(order, report)
    return report


def verify(order, report):
    rows = order_rows(order['n'], order['relations'])
    if report['schema'] != 'degree-specialization-v1' or report['n'] != order['n']:
        raise ValueError('wrong report schema or size')
    if report['constants'] != constant_certificate(order['n']):
        raise ValueError('incorrect branch certificate')
    certify_realizer(rows, report['first'], report['second'])
    if report['inclusive_first_ranks'] != ranks(report['first']) or report['inclusive_second_ranks'] != ranks(report['second']):
        raise ValueError('incorrect inclusive ranks')
    for field, value in [('density', 1), ('radius', F(1, 2)), ('lower', F(1, 2)), ('upper', F(3, 2))]:
        if F(report[field]) != value:
            raise ValueError('incorrect flat specialization output')
    if report['status'] != 'accepted_deterministic_flat_branch' or report['resource_fallback'] is not False:
        raise ValueError('incorrect branch/fallback disposition')
    return True


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input', type=Path); ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    if args.output.exists():
        ap.error('choose a new output file')
    if args.input.stat().st_size > 64*1024**2:
        ap.error('input exceeds 64 MiB')
    order = json.loads(args.input.read_text(encoding='utf-8'))
    report = estimate(order)
    with args.output.open('x', encoding='utf-8', newline='\n') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    print('PASS: exact flat branch, full-square band, pairwise realizer and inclusive ranks')


if __name__ == '__main__':
    main()
