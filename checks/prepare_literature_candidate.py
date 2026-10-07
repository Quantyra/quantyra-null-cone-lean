"""Prepare a review-only source bundle; performs no publication/network writes."""
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT/'manuscript/deposit/literature-candidate'
SOURCE = ROOT/'manuscript/working'
DEST.mkdir(parents=True, exist_ok=True)
if (DEST/'published-record.json').exists():
    raise RuntimeError('preserve published packages')
metadata = json.loads((ROOT/'manuscript/deposit/v0.3.0/zenodo-metadata.json').read_text())
metadata['version'] = '0.3.1'
metadata['description'] = ('<p>Proposed literature revision of the published 0.3.0 preprint by '
    'Daniel Eric Fredriksen, Quantyra Inc. It credits Winkler\'s 1985 existential '
    'coordinate forcing and the stronger flat-model twin/swap recovery in the '
    'dimension-two paper (PDF 1991, publisher 1990). The candidate contribution '
    'is narrowed to explicit occupied-grid quantification and the uniform '
    'nonconstant-density inverse modulus. Originality remains provisional; '
    'structural/citation gaps are disclosed.</p><p>The seven mathematical '
    'statement environments and accepted Lean proof sources are unchanged. '
    'The original inverse, all-law identifiability and directed labeled/unlabeled '
    'law equivalence retain their exact-source GCP verification; logarithmic-grid '
    'and proper-time consequences remain prose. Developed with OpenAI Codex '
    'assistance; open-source informal review and downstream testing, with no '
    'specialist/adoption gate. CC-BY-4.0.</p>')
(DEST/'proposed-zenodo-metadata.json').write_text(json.dumps(metadata, indent=2)+'\n', encoding='utf-8', newline='\n')


def portable_bytes(path):
    return path.read_bytes() if path.suffix == '.pdf' else path.read_text(encoding='utf-8').encode('utf-8')


payload = {f'working/{name}': portable_bytes(SOURCE/name) for name in
           ['finite-causal-order-reconstruction.tex', 'finite-causal-order-reconstruction.pdf',
            'prepare_literature_revision.py', 'README.md']}
payload['finite-causal-order-reconstruction.tex'] = portable_bytes(ROOT/'manuscript/finite-causal-order-reconstruction.tex')
payload['LICENSES/CC-BY-4.0.txt'] = portable_bytes(ROOT/'LICENSES/CC-BY-4.0.txt')
payload['proposed-zenodo-metadata.json'] = (DEST/'proposed-zenodo-metadata.json').read_bytes()
manifest = {'state': 'review_only_not_published', 'proposed_version': '0.3.1',
            'baseline_doi': '10.5281/zenodo.23214579',
            'finalization_required': ['explicit publication selection',
                                      'reserve next version in existing manuscript family',
                                      'finalize version and new DOI labels; compile/review all pages',
                                      'freeze exact final package, upload/publish and verify downloads'],
            'files': {name: {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
                      for name, data in payload.items()}}
manifest_data = (json.dumps(manifest, indent=2)+'\n').encode()
(DEST/'manifest.json').write_bytes(manifest_data)
payload['manifest.json'] = manifest_data
bundle = DEST/'literature-revision-review-source.zip'
with zipfile.ZipFile(bundle, 'w', compression=zipfile.ZIP_DEFLATED) as archive:
    for name, data in sorted(payload.items()):
        info = zipfile.ZipInfo(name, date_time=(2026, 10, 7, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = 0o100644 << 16
        archive.writestr(info, data)
with zipfile.ZipFile(bundle) as archive:
    assert archive.testzip() is None
    assert all(archive.read(name) == data for name, data in payload.items())
receipt = {'state': manifest['state'], 'bundle': bundle.name,
           'bytes': bundle.stat().st_size, 'sha256': hashlib.sha256(bundle.read_bytes()).hexdigest(),
           'members_verified': len(payload)}
(DEST/'bundle.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(receipt))
