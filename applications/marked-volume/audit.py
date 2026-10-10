"""Independent retained-artifact checks; no sampling, Lean, or overwritten receipt."""
import argparse
from collections import Counter
from fractions import Fraction as F
import gzip
import hashlib
import json
from math import comb, exp
from pathlib import Path
import subprocess
import time
import sys

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.set_int_max_str_digits(20000)
D = 10**10


def load(p):
    b = p.read_bytes()
    return json.loads(gzip.decompress(b) if p.suffix == '.gz' else b)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def geometry(e, r, pattern):
    coefficients = {(0, 0): 1+e, (1, 0): -2*e, (0, 1): -2*e, (1, 1): 4*e}
    z = a = total = target = F(0)
    for i in range(4):
        for j in range(4):
            bounds = [F(i, 4), F(i+1, 4), F(j, 4), F(j+1, 4)]
            mass = F(0)
            for (u, v), c in coefficients.items():
                mass += c*(bounds[1]**(u+1)-bounds[0]**(u+1))/(u+1)*(bounds[3]**(v+1)-bounds[2]**(v+1))/(v+1)
            inside = i in (0, 1) and j in (0, 1)
            low = (pattern == 'inside_low' and inside or pattern == 'inside_high' and not inside or
                   pattern == 'checker4' and (i+j) % 2 == 0 or pattern == 'stripes4' and i % 2 == 0)
            w = 1/r if low else F(1)
            total += mass; z += w*mass
            if inside: target += mass; a += w*mass
    assert total == 1 and target == F(1, 4)+e/16
    return target, a/z, z


def report_table(n, r, bank, method):
    result = []
    for lo, hi in bank[n]:
        if method in ('quantyra', 'aronow_lee_cp'):
            lo, hi = lo/(r+(1-r)*lo), hi/(hi+(1-hi)/r)
        if method == 'known_range': lo, hi = F(1, 8), F(3, 8)
        result.append((max(F(1, 8), lo), min(F(3, 8), hi)))
    return result


def audit_metrics(n, theta, target, r, bank, observed, protocol):
    # Independent closed combination formula, rather than the runner's recurrence.
    a, d = theta.numerator, theta.denominator
    weights = [comb(n, k)*a**k*(d-a)**(n-k) for k in range(n+1)]
    denominator = d**n
    assert sum(weights) == denominator
    for method, got in observed.items():
        c = e = u = wl = wh = el = eh = 0
        decisions = {nom: Counter() for nom in protocol['nominated_volumes']}
        for (lo, hi), weight in zip(report_table(n, r, bank, method), weights):
            empty = lo > hi
            w = F(0) if empty else hi-lo
            mid = F(1, 4) if empty else (lo+hi)/2
            err = abs(mid-target)
            c += weight*(lo <= target <= hi); e += weight*empty
            u += weight*(not empty and w <= F(protocol['useful_width']))
            wf = w*D; ef = err*D
            x, rem = divmod(wf.numerator, wf.denominator); wl += weight*x; wh += weight*(x+(rem != 0))
            x, rem = divmod(ef.numerator, ef.denominator); el += weight*x; eh += weight*(x+(rem != 0))
            for nom, counts in decisions.items():
                bottom, top = F(nom)-F(protocol['decision_tolerance']), F(nom)+F(protocol['decision_tolerance'])
                inside = bottom <= target <= top
                accept = not empty and bottom <= lo <= hi <= top
                reject = not empty and (hi < bottom or lo > top)
                correct = accept and inside or reject and not inside
                wrong = empty or accept and not inside or reject and inside
                counts['correct'] += weight*correct; counts['wrong'] += weight*wrong
                counts['unresolved'] += weight*(not correct and not wrong)
        expected = {'coverage': F(c, denominator), 'empty': F(e, denominator), 'useful': F(u, denominator)}
        for key, x in expected.items(): assert F(got[key]) == x, key
        assert list(map(F, got['mean_width'])) == [F(wl, D*denominator), F(wh, D*denominator)]
        assert list(map(F, got['mean_midpoint_error'])) == [F(el, D*denominator), F(eh, D*denominator)]
        assert F(got['mean_width'][1])-F(got['mean_width'][0]) <= F(1, D)
        for nom, counts in decisions.items():
            assert sum(counts.values()) == denominator
            for key, value in counts.items(): assert F(got['decisions'][nom][key]) == F(value, denominator)
        if method != 'ignore_bias_diagnostic':
            assert expected['coverage'] >= F(19, 20)
            assert all(F(v['wrong']) <= F(1, 20) for v in got['decisions'].values())


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('output'); args = ap.parse_args()
    out = (ROOT/args.output).resolve()
    assert out.is_relative_to((ROOT/'applications/marked-volume/evidence').resolve())
    assert not (out/'artifact-audit.json').exists(), 'Audit receipt already exists'
    start = time.perf_counter()
    freeze = load(out/'freeze.json'); summary = load(out/'summary.json')
    assert summary['status'] == 'PASS' and not (out/'failure.json').exists()
    p = load(ROOT/'applications/marked-volume/protocol.json')
    for name, expected in freeze['sources'].items():
        committed = subprocess.check_output(['git', 'show', freeze['commit']+':'+name], cwd=ROOT)
        assert sha(committed) == expected
        assert committed == (ROOT/name).read_bytes(), name
    bank = {row['n']: [(F(a), F(b)) for a, b in row['endpoints']] for row in load(ROOT/p['calibration_bank'])}
    strata = load(out/'strata.json.gz'); trials = load(out/'trials.json.gz'); witnesses = load(out/'witnesses.json.gz')
    assert len(strata) == 132 and len(trials) == 8448 and len(witnesses) == 132
    expected_cases = {(phase, e, r, pattern, n) for phase in ['known', 'withheld']
                      for e in p[phase]['epsilons'] for r in p[phase]['ratios']
                      for pattern in p[phase]['patterns'] for n in p['sizes']}
    assert Counter((s['phase'], s['epsilon'], s['R'], s['pattern'], s['n']) for s in strata) == Counter(expected_cases)
    groups = {s['id']: [] for s in strata}
    assert set(groups) == set(range(132))
    for t in trials: groups[t['stratum']].append(t)
    for s in strata:
        n, r, e = s['n'], F(s['R']), F(s['epsilon'])
        target, theta, z = geometry(e, r, s['pattern'])
        assert [target, theta, z] == [F(s[k]) for k in ['volume', 'theta', 'retained_mass']]
        audit_metrics(n, theta, target, r, bank, s['metrics'], p)
        g = groups[s['id']]
        assert sorted(t['replicate'] for t in g) == list(range(64))
        assert sum(t['count'] for t in g) == s['total_count']
        assert all(0 <= t['count'] <= n and n <= t['generated'] <= t['proposals'] <= 64*n and
                   t['drawn'] >= t['proposals'] for t in g)
        rad = F(s['sampling_radius'])
        assert 2*132*exp(-2*n*64*float(rad*rad)) <= .01
        assert s['sampling_diagnostic_pass'] and abs(F(s['total_count'], n*64)-theta) <= rad
        assert time.perf_counter()-start <= 1800, 'audit runtime ceiling'
        if s['id'] % 12 == 0: print('audit_strata', s['id']+1, flush=True)
    assert sorted(w['stratum'] for w in witnesses) == list(range(132))
    for w in witnesses:
        s = strata[w['stratum']]; trial = next(t for t in groups[s['id']] if t['replicate'] == 0)
        uv = np.array(w['coordinates'], dtype='<f8')
        assert uv.shape == (s['n'], 2) and np.all((0 <= uv) & (uv < 1))
        assert sha(uv.tobytes()) == trial['coordinates_sha256']
        points = np.vstack(([[0., 0.], [.5, .5]], uv))
        tt, xx = (points[:, 0]+points[:, 1])/2, (points[:, 0]-points[:, 1])/2
        chronology = tt[None, :]-tt[:, None] > abs(xx[None, :]-xx[:, None])
        assert sha(np.packbits(chronology).tobytes()) == trial['relation_sha256']
        assert int(np.count_nonzero(chronology[0, 2:] & chronology[2:, 1])) == trial['count']
    gate = [s for s in strata if s['phase'] == 'withheld' and s['n'] == 1024 and F(s['R']) <= F(5, 4)]
    def correct(m): return sum(F(d['correct']) for d in m['decisions'].values())/2
    absolute = all(F(s['metrics']['quantyra']['useful']) >= F(4, 5) and correct(s['metrics']['quantyra']) >= F(4, 5) for s in gate)
    assert len(gate) == 27 and summary['gate_strata'] == 27 and summary['absolute_utility_pass'] == absolute
    assert all(s['metrics']['quantyra'] == s['metrics']['aronow_lee_cp'] for s in strata)
    assert not summary['additionality_pass'] and summary['decision'] == 'park_operational_candidate'
    controls = load(out/'controls.json')
    assert controls['negative_controls_rejected'] == 5 and controls['zero_sample_cases'] == 4
    assert controls['binomial_certificates'] == 1348
    for name, expected in freeze['preserved'].items(): assert sha((ROOT/name).read_bytes()) == expected, name
    names = ['freeze.json', 'controls.json', 'strata.json.gz', 'trials.json.gz', 'witnesses.json.gz', 'summary.json']
    result = {'status': 'PASS', 'strata': 132, 'all_possible_counts_recomputed': True,
              'metric_rows': 528, 'exact_valid_coverage_rows': 396, 'trial_records': 8448,
              'lorentz_coordinate_witnesses': 132, 'frozen_source_identities': len(freeze['sources']),
              'preexisting_files_preserved': len(freeze['preserved']),
              'absolute_utility_pass': absolute, 'additionality_pass': False,
              'decision': summary['decision'], 'audit_seconds': time.perf_counter()-start,
              'artifact_sha256': {name: sha((out/name).read_bytes()) for name in names},
              'audit_source_sha256': sha(Path(__file__).read_bytes()),
              'limits': 'Checks all exact model-law metrics and 132 saved coordinate witnesses; not a proof of floating sampler semantics or real detector validity.'}
    (out/'artifact-audit.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(result), flush=True)


if __name__ == '__main__': main()
