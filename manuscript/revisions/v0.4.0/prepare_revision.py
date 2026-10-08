"""Prepare the unpublished post-certification revision from frozen manuscript 0.3.1."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / 'manuscript/deposit/v0.3.1/finite-causal-order-reconstruction.tex'
OUT = Path(__file__).resolve().parent
s = BASE.read_text(encoding='utf-8')

def replace(old, new):
    global s
    assert s.count(old) == 1, old
    s = s.replace(old, new)

replace(r'\date{7 October 2026 \\ version 0.3.1}',
        r'\date{8 October 2026 \\ version 0.4.0 --- unpublished review candidate}')
replace('rank error at most $30rn$. Lean~4 proofs now cover this finite theorem,\n'
        'the original inverse estimate, and all-size identifiability, including\n'
        'the probability and analytic bridges and equality of labeled and\n'
        'unlabeled order-law total variation. The logarithmic-grid improvement\n'
        'and proper-time comparison remain ordinary mathematical proofs.',
        'rank error at most $30rn$. Lean~4 proofs cover this finite theorem,\n'
        'both inverse estimates, all-size identifiability, and the proper-time\n'
        'comparison for actual absolutely continuous future curves. They include\n'
        'the probability and analytic bridges, equality of labeled and unlabeled\n'
        'order-law total variation, and one orientation shared by all endpoint pairs.')
replace('\\textbf{Manuscript DOI:} version 0.3.1,',
        '\\textbf{Draft status:} unpublished version 0.4.0; no DOI assigned.\\\\\n'
        '\\textbf{Published baseline DOI:} version 0.3.1,')
replace('continuum bridges formalized for the original estimate. The logarithmic\n'
        'grid choice and its resulting rate are not yet formalized.',
        'continuum bridges formalized for the original estimate. The logarithmic\n'
        'grid choice, its probability bounds and the complete all-$N$ rate are\n'
        'now formalized; see Section~\\ref{sec:formal}.')
replace('\\end{itemize}\n\nLean~4.30.0',
        '\\item \\path{LogGridRate.lean} and \\path{ImprovedInverse.lean} prove\n'
        'the logarithmic-grid probability estimate and the exact constant-130\n'
        'inverse, including small-$N$ and high-TV branches. The exports are\n'
        '\\path{InDensityClass.full_inverse_logarithmic} and its actual unlabeled-law\n'
        'counterpart \\path{InDensityClass.full_inverse_logarithmic_unlabeled}.\n'
        '\\item \\path{ProperTime.lean} defines actual absolutely continuous\n'
        'future curves, their length integrals and the endpoint time-separation\n'
        'supremum, with zero for an empty curve class. It proves the comparison\n'
        'and both inverse-law consequences with one global orientation for\n'
        'every endpoint pair; the target length inequality is not assumed.\n'
        '\\end{itemize}\n\nLean~4.30.0')
start=s.index('The exact proof and evidence revision is\n')
end=s.index('\\section{Discussion and research provenance}',start)
s=s[:start]+r'''The accepted proof/evidence revision is
\href{https://github.com/Quantyra/quantyra-null-cone-lean/tree/74c1f743d085c63b45ac2bf30008ad5d29b98fbc}{\texttt{74c1f743d085c63b45ac2bf30008ad5d29b98fbc}}.
Authoritative verification ran on GCP under identifier
\path{space-lorentz-acceptance-20261008T071627Z-221cd8}.
The complete root build passed 3001 jobs and all 295 selected exact-type
and axiom audits, with zero compiler warnings or added axioms.
This audit includes separate finite-data and higher-dimensional modules;
the count does not mean that this paper contains 295 mathematical results.
Exact source hashes were checked before and after execution, as were
all nine pinned dependency revisions and their tracked trees.
The \href{https://github.com/Quantyra/quantyra-null-cone-lean/tree/74c1f743d085c63b45ac2bf30008ad5d29b98fbc/evidence/gcp/space-lorentz-acceptance-20261008T071627Z-221cd8}{retained evidence}
contains immutable inputs, manifests, raw logs and the acceptance receipt.
Earlier 68-, 78-, 90- and 219-export acceptances remain preserved.
The audited dependencies use only \texttt{propext},
\texttt{Classical.choice} and \texttt{Quot.sound}; no additional axioms
or admitted proofs are introduced. Every development and acceptance
Lean invocation ran on GCP; hosted CI is supplementary.
Reproduction and statement-to-source mappings are in
\path{INTEGRITY.md} and \path{notes/lean-verification.md}.

Both the logarithmic inverse and proper-time consequence in this paper
are now formally verified. Supplementary finite checks remain useful
for detecting particular implementation errors; universal mathematical
claims are supported by the kernel-checked proofs. Kernel checking does
not establish originality, optimality or the adequacy of the model.

\subsection{Related certified work outside the main theorem}
The same repository now contains a separately scoped one-order
finite-data procedure. Its formalization connects implication-forced
ranks, sharp DKW calibration, canonical rational linear programs,
dual residual checks, cell and point bands, histogram error and a
conservative fallback. The main full-report theorem bounds
accepted-output failure under the original density class and a fixed
pre-sampling calibration budget, using one orientation for every field.
It does not assert coverage conditional on acceptance, certify the
entire Python runtime, or authorize data-selected probability budgets.
Current tested density bands remain full range; useful practical
density inference has not been established. The detailed statistical
procedure is kept separate from this inverse-law paper.

A genuine $2+1$-dimensional Lorentzian counterexample is also certified
separately. On the diamond $|t|+\sqrt{x^2+y^2}<1$, an explicit smooth
conformal automorphism transports flat volume to a distinct smooth
normalized density satisfying the selected bounds and Euclidean
Lipschitz constraint. Actual iid coupling gives identical finite
directed-order laws at every size. The densities nevertheless have
positive coordinate supremum distance modulo spatial $O(2)$.
The formalization also derives the metric pullback: these metrics
are isometric. The obstruction therefore concerns the proposed
coordinate gauge, rather than new physical nonidentifiability or a
higher-dimensional inverse rate. The explicit construction and proof
map are in \path{notes/higher-dimensional-certification.md}; its
full exposition is reserved for a separate technical paper.

'''+s[end:]
replace('the class, finding sharper or optimal rates, controlling derivatives,\n'
        'and formalizing the logarithmic-grid and proper-time consequences are\n'
        'separate questions. This draft',
        'the class, finding sharper or optimal rates, controlling derivatives,\n'
        'obtaining informative finite-data density confidence, and selecting a\n'
        'valid higher-dimensional gauge with a stability theorem remain separate\n'
        'questions. The logarithmic-grid and proper-time certification tasks\n'
        'are complete. This draft')
pattern=r'\\begin\{(theorem|lemma|proposition|corollary)\}.*?\\end\{\1\}'
old=re.findall(pattern,BASE.read_text(encoding='utf-8'),re.S)
blocks=lambda t:[m.group() for m in re.finditer(pattern,t,re.S)]
assert len(old)==7 and blocks(s)==blocks(BASE.read_text(encoding='utf-8'))
assert not re.search(r'remain prose|not yet formalized|remain ordinary|optional future work',s)
(OUT/'finite-causal-order-reconstruction.tex').write_text(s,encoding='utf-8',newline='\n')
print('Prepared unpublished 0.4.0; all seven mathematical statement environments unchanged.')
