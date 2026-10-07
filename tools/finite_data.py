"""CLI for order-only finite reconstruction and independently verified LP bands."""
import argparse
import json
import sys
from fractions import Fraction as F
from pathlib import Path
from finite_data_core import (order_rows, realizer, certify_realizer, confidence,
                              corner_counts, verify_forcing_certificate, calibration, calibration_radius)
from finite_data_lp import model, solve, verify_bounds


def histogram_violation(histogram, counts, n, k, radius):
    return max([F(0)]+[abs(sum(F(histogram[i*k+j]) for i in range(p) for j in range(q))
                            / (k*k)-F(counts[p][q], n))-radius
                       for p in range(k+1) for q in range(k+1)])


def estimate(order, k=4, delta=F(1, 20), calibration_method='split-dkw'):
    if type(k) is not int or not 1 <= k <= 16:
        raise ValueError('estimation grid must be an integer in [1,16]')
    rows = order_rows(order['n'], order['relations'])
    first, second = realizer(rows)
    conf = confidence(first, second, rows, delta, calibration_method)
    counts = corner_counts(first, second, k)
    lp = model(counts, len(rows), conf['cdf_radius'])
    result = solve(lp)
    violation = histogram_violation(result['histogram'], counts, len(rows), k, conf['cdf_radius'])
    result['corner_violation'] = violation
    result['histogram_error_upper'] = min(F(1), 8*conf['cdf_radius']*k*k+
                                          4*violation*k*k+F(2, k))
    if result['status'] != 'certified_outer_bounds':
        result['histogram_error_upper'] = F(1)
    report = {'schema': 1, 'input': order, 'grid': k, 'delta': F(delta),
              'calibration_method': calibration_method,
              'first': first, 'second': second, 'confidence': conf, 'bands': result,
              'interpretation': 'Simultaneous coverage in K under one global identity/transpose; '
                                'ordinary mathematical guarantee, not Lean certification.'}
    verify_report(report)
    return report


def verify_report(report):
    if report['schema'] != 1:
        raise ValueError('unsupported report schema')
    order = report['input']
    rows = order_rows(order['n'], order['relations'])
    first, second = report['first'], report['second']
    certify_realizer(rows, first, second)
    conf = report['confidence']
    verify_forcing_certificate(rows, first, conf['rank_certificate'])
    method = report.get('calibration_method', 'grid')
    expected_cal = calibration(len(rows), F(report['delta']), method)
    actual_cal = conf['calibration']
    for key, value in expected_cal.items():
        if (actual_cal[key] != value if isinstance(value, str) else F(actual_cal[key]) != value):
            raise ValueError('incorrect confidence calibration')
    expected_radius = min(F(1), F(conf['rank_certificate']['trim_budget'])+
                          calibration_radius(expected_cal, method))
    expected_failure = F(0) if expected_radius == 1 else expected_cal['failure_upper']
    if F(conf['cdf_radius']) != expected_radius or F(conf['failure_upper']) != expected_failure:
        raise ValueError('incorrect confidence radius/probability')
    counts = corner_counts(first, second, report['grid'])
    lp = model(counts, len(rows), expected_radius)
    result = report['bands']
    verify_bounds(lp, result)
    if len(result['histogram']) != report['grid']**2 or any(
            not F(1, 2) <= F(v) <= F(3, 2) for v in result['histogram']):
        raise ValueError('invalid histogram')
    violation = histogram_violation(result['histogram'], counts, len(rows), report['grid'], expected_radius)
    error = min(F(1), 8*expected_radius*report['grid']**2+
                4*violation*report['grid']**2+F(2, report['grid']))
    if result['status'] != 'certified_outer_bounds':
        error = F(1)
    if F(result['corner_violation']) != violation or F(result['histogram_error_upper']) != error:
        raise ValueError('incorrect histogram residual/error')
    return True


def read_json(path, limit=64*1024*1024):
    if path.stat().st_size > limit:
        raise ValueError('JSON exceeds the supported size limit')
    return json.loads(path.read_text(encoding='utf-8'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    reconstruct = commands.add_parser('estimate')
    reconstruct.add_argument('input', type=Path)
    reconstruct.add_argument('--output', type=Path, required=True)
    reconstruct.add_argument('--grid', type=int, default=4)
    reconstruct.add_argument('--delta', default='1/20')
    reconstruct.add_argument('--calibration', choices=['grid', 'split-dkw'], default='split-dkw')
    check = commands.add_parser('verify')
    check.add_argument('input', type=Path)
    args = parser.parse_args()
    try:
        if args.command == 'verify':
            verify_report(read_json(args.input, limit=512*1024*1024))
            print('PASS: realizer, forcing witnesses, confidence calibration and rational LP bounds')
        else:
            if args.output.exists():
                raise ValueError('output already exists; choose a new path')
            report = estimate(read_json(args.input), args.grid, F(args.delta), args.calibration)
            args.output.parent.mkdir(parents=True, exist_ok=True)
            payload = json.dumps(report, default=str, separators=(',', ':'))+'\n'
            if len(payload.encode('utf-8')) > 512*1024*1024:
                raise ValueError('certificate report exceeds the verification size limit')
            args.output.write_text(payload, encoding='utf-8')
            print(json.dumps({'status': report['bands']['status'],
                              'cdf_radius': str(report['confidence']['cdf_radius']),
                              'failure_upper': str(report['confidence']['failure_upper']),
                              'histogram_error_upper': str(report['bands']['histogram_error_upper']),
                              'output': str(args.output)}))
    except (ValueError, TypeError, KeyError, IndexError, OSError) as exc:
        parser.exit(2, 'Error: '+str(exc)+'\n')


if __name__ == '__main__':
    main()
