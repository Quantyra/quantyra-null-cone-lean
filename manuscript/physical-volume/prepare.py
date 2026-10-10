"""Extract existing evidence and a formal map; never invoke Lean or sample data.

Run --write once after a reviewed change; default mode verifies frozen outputs.
Run from an ordinary Git checkout with Python 3.13 (standard library only).
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PROOF = '354fa1f8dc8746328077041ef79d3621837f99e7'
BASELINE = '1085d086dd77d50f59114cad5cb0d8f0a35520c9'
RUN = 'space-volumerate-acceptance-20261010T023105Z-5d08cf'
GCP = ROOT / 'evidence/gcp' / RUN
PILOT = ROOT / 'evidence/marked-volume/pilot-1'
FINITE = ROOT / 'evidence/volumerate/finite-v1/attempt-2'
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: json.loads(p.read_text(encoding='utf-8'))
git = lambda *args: subprocess.check_output(['git', *args], cwd=ROOT)

# These associations are semantic review decisions, not inferred from names.
CLAIMS = {
 'prop:geometry': ('Density normalization and interval range; metric determinant and timelike straight-segment interpretation are elementary prose, not additional exported endpoints.', [
  'null_interval_rectangle', 'physical_marked_volume_range']),
 'thm:main': ('Exact strict radii, full marked-order law, global detector bounds, arbitrary independent probability seed; R in [1,2], n positive.', [
  'physical_volume_joint_rate', 'physical_volume_joint_rate_lower', 'fixed_marked_physical_volume_rate_upper',
  'sampled_marked_order_fraction', 'full_marked_order_fraction_hoeffding', 'membership_count_eq_binomial']),
 'prop:finite-thinning': ('Unconditional submeasure equalities precede division; conditioning requires positive count mass. Independent generated count only.', [
  'detected_submeasure', 'retained_subset_law', 'retained_ordered_pattern_law',
  'retained_count_submeasure_law', 'retained_count_conditional_law',
  'mixed_retained_submeasure_series', 'mixed_retained_conditional_law']),
 'prop:poisson': ('Finite Poisson generation, including zero intensity, and nonnegative measurable real h; nonnormalized physical units are elementary rescaling.', [
  'poisson_retained_submeasure_law', 'poisson_retained_count_law', 'poisson_retained_laplace_functional']),
 'prop:stopping': ('Almost-sure termination and actual first-n tuple law; Lean retains a finite terminal-pattern sum. The negative-binomial cardinality is proved in prose.', [
  'iid_positive_event_infinite', 'ae_stream_retained_count_surjective', 'stopped_retained_submeasure',
  'stopped_retained_conditional_law', 'stopped_retained_iid_law']),
 'prop:selection': ('Global detector bounds specialized to a=1/R, b=1. Transform monotonicity and bias, not geometric identified-set sharpness.', [
  'retention_mass_identification', 'retained_physical_identification', 'retention_lower_mono',
  'retention_upper_mono', 'retention_interval_composition', 'retention_lower_bias', 'retention_upper_bias']),
 'thm:report': ('Real endpoint coverage theorem; executable tables use rational delta/endpoints. Known-range intersection is an elementary event inclusion. Process specializations are accepted for rational tables; the real-table statement follows by the same proved tuple laws.', [
  'finite_upper_tail_pvalue', 'finite_lower_tail_pvalue', 'binomial_tail_interval_coverage',
  'retained_binomial_report_coverage', 'InDensityClass.retained_marked_binomial_coverage',
  'mixed_physical_report_coverage', 'InDensityClass.stopped_physical_report_coverage',
  'marked_hoeffding_95', 'retained_marked_volume_95']),
 'prop:certificate': ('Exact binomial numerator and integer check soundness; no kernel certification of Python/SciPy execution.', [
  'binomial_mass_integer_identity', 'binomial_upper_integer_check', 'binomial_lower_integer_check',
  'binomial_numerator_recurrence', 'binomial_numerator_division', 'binomial_report_check_sound']),
 'lem:testing': ('Finite observation space, arbitrary common independent seed, total variation two-point inequality; scalar disjoint balls instantiated at the accepted thresholds.', [
  'finite_seed_event_bound', 'finite_seed_two_point_lower_bound', 'finite_randomized_scalar_obstruction',
  'identical_law_randomized_scalar_obstruction']),
 'lem:family': ('Admitted smooth polynomial densities, target integral, actual coordinate likelihood and second moment.', [
  'calibration_density_in_class', 'calibration_marked_volume', 'calibration_sample_withDensity',
  'calibration_likelihood_integral', 'calibration_product_divergence']),
 'lem:sampling': ('Actual full marked-order law contraction with unit detector; finite divergence bound; strict a_n/128 radius and 3/8 failure.', [
  'volume_sampling_power_bound', 'volume_sampling_divergence_bound',
  'full_marked_sampling_TV_bound', 'physical_volume_sampling_rate_lower']),
 'lem:detector': ('Global clamped detector, equal accepted submeasure and full laws, strict b_R/64 radius and 1/2 failure. R>1, R<=2.', [
  'calibration_detector_bounds', 'calibration_detector_on_diamond', 'calibration_detected_submeasure',
  'calibration_full_marked_law_equal', 'physical_volume_detector_rate_lower',
  'calibration_pattern_submeasure_equal', 'calibration_stopped_submeasure_equal',
  'calibration_mixed_marked_equal']),
 'prop:empty': ('Anchor relations remain in the zero-sample Dirac observation. Strict 1/128 obstruction; deterministic 1/8 upper error.', [
  'physical_marked_volume_range', 'no_data_physical_volume_error',
  'empty_full_marked_law', 'no_data_physical_volume_obstruction']),
}

def extract_map():
    capture, receipt = read(GCP/'capture-manifest.json'), read(GCP/'receipt.json')
    assert receipt['acceptance'] and receipt['exit'] == receipt['owned_warnings'] == 0
    assert receipt['compile_host'] == 'GCP' and receipt['audited_exports'] == 797
    assert receipt['source_verified_before_and_after'] and receipt['dependency_identities_before_and_after']
    assert sha((GCP/'inputs.tar.gz').read_bytes()) == read(GCP/'input-archive.json')['sha256']
    with tarfile.open(GCP/'inputs.tar.gz') as archive:
        data = {m.name: archive.extractfile(m).read() for m in archive.getmembers() if m.isfile()}
    assert set(data) == set(capture['source']) and len(data) == 198
    names = list(data)
    batch = subprocess.check_output(
        ['git', 'cat-file', '--batch'], cwd=ROOT,
        input=''.join(PROOF+':'+name+'\n' for name in names).encode())
    offset = 0
    for name in names:
        assert sha(data[name]) == capture['source'][name], name
        end = batch.index(b'\n', offset)
        header = batch[offset:end].split()
        assert header[1] == b'blob', (name, header)
        size = int(header[2])
        assert batch[end+1:end+1+size] == data[name], ('proof commit', name)
        offset = end+size+2
        if name.startswith('QuantyraNullCone/') or name in {'lean-toolchain','lake-manifest.json','lakefile.toml'}:
            assert (ROOT/name).read_bytes().replace(b'\r\n', b'\n') == data[name], ('current proof dependency', name)
    assert offset == len(batch)
    audit = (GCP/'logs/audit.stdout.txt').read_text(encoding='utf-8')
    reports = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit))
    reports.update((name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", audit))
    assert len(reports) == 797 and 'PASS: proof sources and final Lean dependency reports' in audit
    for name, axioms in reports.items():
        assert set(x.strip() for x in axioms.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'}, name
    for p in (GCP/'logs').glob('*.txt'):
        assert not re.search(r'warning:|error:|sorryAx|unsolved goals', p.read_text(encoding='utf-8'))
    assert 'Build completed successfully (3097 jobs)' in (GCP/'logs/build.stdout.txt').read_text(encoding='utf-8')
    cleanup = read(GCP/'cleanup.json')
    assert cleanup['final_state'] == 'TERMINATED' and cleanup['stop_verified']
    assert cleanup['no_other_lean_work'] and cleanup['acceptance_collected_before_shutdown']
    declarations = {}
    for path, body in data.items():
        if path.startswith('QuantyraNullCone/') and path.endswith('.lean'):
            for name in re.findall(r'^theorem ([\w.]+)', body.decode(), re.M):
                declarations[name] = path
    claims = []
    for label, (scope, exports) in CLAIMS.items():
        entries = []
        for short in exports:
            name = 'QuantyraNullCone.'+short
            assert name in reports and short in declarations, name
            pattern = r'^'+re.escape(name)+r'(?:\.\{[^}]*\})?(?=\s|\{|\()'
            start = re.search(pattern, audit, re.M)
            assert start, name
            rest = audit[start.start():]
            stop = re.search(r"\n(?:QuantyraNullCone\.|'QuantyraNullCone\.|PASS:)", rest)
            exact_type = rest[:stop.start() if stop else len(rest)].strip()
            path = declarations[short]
            entries.append({'name': name, 'source': path, 'source_sha256': sha(data[path]),
                            'accepted_type': exact_type, 'axioms': reports[name]})
        claims.append({'label': label, 'reviewed_scope': scope, 'exports': entries})
    tex = (HERE/'interval-volume-detection.tex').read_text(encoding='utf-8')
    theorem_labels = set(re.findall(r'\\label\{((?:thm|prop|lem):[^}]+)\}', tex))
    assert theorem_labels == set(CLAIMS), (theorem_labels, set(CLAIMS))
    return {'proof_commit': PROOF, 'gcp_run': RUN, 'captured_sources': 198, 'audited_exports': 797,
            'toolchain': data['lean-toolchain'].decode().strip(),
            'archive_sha256': sha((GCP/'inputs.tar.gz').read_bytes()), 'claims': claims}

def extract_tables():
    cells = read(PILOT/'cells.json')
    pilot = []
    for ratio in ['1','11/10','5/4','3/2','2']:
        vals = [max(c['mean_width_full_law'] for c in cells if c['n']==1024 and c['R']==ratio and c['method']==method)
                for method in ['exact_tail_certified_binomial', 'analytic_hoeffding']]
        pilot.append([ratio, *vals])
    assert len(cells) == 1200 and sum(c['coverage_rational'] is not None for c in cells) == 600
    valid = [c for c in cells if c['method'] != 'binomial_ignoring_bias_diagnostic']
    assert abs(min(c['coverage_full_law'] for c in valid)-0.9510711635475115)<1e-12
    exact_min = min(Fraction(c['coverage_rational']) for c in valid if c['coverage_rational'] is not None)
    assert round(float(exact_min),6) == 0.966807
    geometry = read(PILOT/'geometry.json')
    assert [g['coverage'] for g in geometry] == [0.935,0.955,0.965,1.0]
    assert all(g['trials']==200 and g['n']==1024 for g in geometry)
    summary = read(FINITE/'summary.json')
    assert summary['status']=='PASS' and summary['coverage_cells']==1656 and summary['interval_cells']==1108
    assert summary['paired_width_counts']=={'equal':376,'joint_wider':732}
    assert round(float(Fraction(summary['minimum_exact_coverage'])),8)==0.96288634
    intervals = read(FINITE/'intervals.json')
    finite = []
    for ratio in ['1','5/4','2']:
        row = [r for r in intervals if r['n']==1024 and r['k']==256 and r['R']==ratio]
        assert len(row)==1
        finite.append([ratio, *[float(Fraction(row[0]['methods'][m]['width'])) for m in [
            'transformed_exact_binomial','transformed_hoeffding','joint_rate','known_range']]])
    def table(rows, columns, caption, label, digits):
        lines = ['\\begin{table}[htbp]', '\\centering', '\\begin{tabular}{'+'r'*len(columns)+'}',
                 '\\toprule', ' & '.join(columns)+r' \\', '\\midrule']
        for ratio, *vals in rows:
            lines.append(f'{float(Fraction(ratio)):g} & '+' & '.join(f'{v:.{digits}f}' for v in vals)+r' \\')
        lines += ['\\bottomrule', '\\end{tabular}', '\\caption{'+caption+'}',
                  '\\label{'+label+'}', '\\end{table}', '']
        return '\n'.join(lines)
    return {
     'pilot-widths.tex': table(pilot, ['$R$','Certified binomial','Analytic'],
       'Original pilot: worst expected widths on its prescribed generic-probability grid at $n=1024$. The no-data width is one.', 'tab:pilot',5),
     'finite-widths.tex': table(finite, ['$R$','Certified binomial','Hoeffding','Joint rate','Known range'],
       'Separate geometric study: realized widths at $n=1024$, $K=256$, after intersection with the known range.', 'tab:finite',6),
     'table-data.json': json.dumps({'pilot_worst_expected_widths':pilot,'finite_realized_widths':finite,
       'exact_small_n_pilot_minimum':str(exact_min), 'new_samples':0},indent=2)+'\n'}

def evidence_paths():
    paths = set()
    for folder in [PILOT, FINITE, FINITE.parent/'attempt-1']:
        paths.update(p for p in folder.rglob('*') if p.is_file())
    for name in ['capture-manifest.json','receipt.json','cleanup.json','input-archive.json','inputs.tar.gz',
                 'exit-code','run.sh','logs/build.stdout.txt','logs/build.stderr.txt',
                 'logs/audit.stdout.txt','logs/audit.stderr.txt']:
        paths.add(GCP/name)
    for folder in [PILOT,FINITE]:
        freeze = read(folder/'freeze.json')
        # Each generation keeps its original key spelling; the whole freeze is preserved.
        for key in ['sources','source_sha256','source_hashes','committed_source_sha256']:
            for name, digest in freeze.get(key,{}).items():
                assert (ROOT/name).is_file(), name
                assert sha((ROOT/name).read_bytes().replace(b'\r\n',b'\n'))==digest, ('frozen source',name)
                paths.add(ROOT/name)
    for name in ['notes/marked-volume-protocol.json','notes/marked-volume-pilot-result.md',
                 'notes/physical-volume-finite-protocol.json','notes/physical-volume-finite-validation.md',
                 'notes/physical-volume-selection-comparison.md','notes/physical-volume-joint-certification.md',
                 'notes/independent-thinning-process.md','notes/physical-volume-calibration-rate.md',
                 'tools/marked_volume.py','tools/benchmark_marked_volume.py','tools/run_marked_volume_pilot.py',
                 'checks/validate_volume_rate_finite.py','checks/audit_volume_rate_finite.py',
                 'checks/test_marked_volume.py','LICENSE','LICENSES/CC-BY-4.0.txt']:
        if (ROOT/name).is_file(): paths.add(ROOT/name)
    return sorted(paths)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    mapped=extract_map()
    outputs={'formal-map.json':json.dumps(mapped,ensure_ascii=False,indent=2)+'\n', **extract_tables()}
    hashes={p.relative_to(ROOT).as_posix():sha(p.read_bytes()) for p in evidence_paths()}
    outputs['evidence-manifest.json']=json.dumps({'baseline_commit':BASELINE,'proof_commit':PROOF,'files':hashes},indent=2)+'\n'
    for name, body in outputs.items():
        if args.write: (HERE/name).write_text(body,encoding='utf-8',newline='\n')
        else: assert (HERE/name).read_bytes()==body.encode(), ('regeneration mismatch',name)
    allow={'.gitattributes','README.md','notes/manuscript-portfolio.md'}
    changes=git('diff','--name-status',BASELINE).decode().splitlines()
    assert all(line.startswith('A\t') or line.split('\t')[-1] in allow for line in changes), 'Protected baseline changed'
    print(json.dumps({'status':'PASS','claims':len(mapped['claims']),
      'mapped_exports':len({e['name'] for c in mapped['claims'] for e in c['exports']}),
      'captured_sources_verified':198,'formal_audit_exports_verified':797,
      'evidence_files':len(hashes),'baseline_preserved':BASELINE,'new_samples':0,'new_lean_invocations':0}))

if __name__=='__main__': main()
