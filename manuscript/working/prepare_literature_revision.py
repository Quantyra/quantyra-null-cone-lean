"""Prepare an unpublished literature revision; preserve the published files."""
from pathlib import Path
import re
import hashlib
import json

HERE = Path(__file__).resolve().parent
baseline = HERE.parent / 'finite-causal-order-reconstruction.tex'
old = baseline.read_text(encoding='utf-8')
new = old.replace(r'\date{7 October 2026 \quad Preprint, version 0.3.0}',
                  r'\date{7 October 2026 \\ Unpublished literature revision of version 0.3.0}')
new = new.replace(r'\textbf{Manuscript DOI:} version 0.3.0,',
                  r'\textbf{Revision status:} unpublished; no new DOI.\\' + '\n' +
                  r'\textbf{Published baseline DOI:} version 0.3.0,')
start = new.index('The present draft concerns an explicit finite inverse modulus')
end = new.index('The result concerns geometric inference', start)
new = new[:start] + r'''The present draft concerns an explicit finite inverse modulus for a
fixed, regular, two-dimensional class. Orientation forcing and modular
decomposition are established methods~\cite{KlavikZeman}. Winkler's
\emph{Random orders}, Theorem~7 and its proof, use existential poset
configurations to recover finite coordinate-order patterns up to axes
in the infinite box-dense setting~\cite{Winkler1985}. In the flat
two-dimensional random model, the typical-event argument in
\emph{Random orders of dimension 2}, Section~II and the proof of
Theorem~4.3, leaves only disjoint adjacent twin transpositions and one
global axis exchange~\cite{Winkler}. It follows that every realizer has
rank error at most one after that exchange, a stronger flat-model
conclusion than our $30rn$ estimate. Exact unique realizability is
unnecessary for this recovery.

Our candidate contribution is narrower: explicit deterministic
occupied-grid quantification and its uniform statistical use over the
nonconstant positive Lipschitz class, leading to a finite
law-to-coefficient inverse modulus. The independent uniform-permutation
counting in Winkler's finite model does not immediately give this
uniform conclusion for dependent coordinate rankings. We have not
located an equivalent or directly implying inverse bound in the
inspected literature. The full-text comparison and its remaining
structural/citation gaps are recorded in the repository; originality
remains provisional, with no certified priority claim.

''' + new[end:]
new = new.replace('is the explicit restricted inverse estimate and its approximate\n'
                  'realizer-rigidity ingredient; publication-level originality assessment\n'
                  'remains open.',
                  'is the explicit restricted inverse estimate and the occupied-grid\n'
                  'quantification supporting its uniform use over nonconstant densities.\n'
                  'Earlier qualitative forcing and stronger flat-model rank recovery are\n'
                  'credited above; broader priority assessment remains provisional.')
new = new.replace(r'\bibitem{Winkler} P. Winkler,',
                  r'''\bibitem{Winkler1985} P. Winkler, \emph{Random orders},
Order \textbf{1}, 317--331 (1985).
\url{https://doi.org/10.1007/BF00582738}.
\bibitem{Winkler} P. Winkler,''')
new = new.replace(r'Order \textbf{7}, 329--339.',
                  r'Order \textbf{7}, 329--339 (PDF dated 1991; publisher metadata 1990).')
pattern = r'\\begin\{(theorem|lemma|proposition|corollary)\}.*?\\end\{\1\}'
statements = re.findall(pattern, old, re.S)
assert len(statements) == 7
assert [m.group() for m in re.finditer(pattern, old, re.S)] == [
    m.group() for m in re.finditer(pattern, new, re.S)]
assert 'has not yet been\ncompared' not in new and new != old
out = HERE / baseline.name
out.write_text(new, encoding='utf-8', newline='\n')
print(json.dumps({'unchanged_mathematical_environments': len(statements),
                  'published_source_sha256': hashlib.sha256(baseline.read_bytes()).hexdigest(),
                  'working_source_sha256': hashlib.sha256(out.read_bytes()).hexdigest()}, indent=2))
