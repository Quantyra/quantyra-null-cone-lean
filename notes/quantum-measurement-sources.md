# S047 primary-source and conditional field screen

2026-10-10. Relevant full proofs were inspected before freezing the
[loss-only qubit candidate](quantum-measurement-model.md). This is a bounded
comparison, not an exhaustive priority search. Source PDFs remain private;
the [source inventory](../evidence/quantum-measurement/source-inventory.json)
records their URLs, editions and hashes without redistributing article bytes.

## Detector and inference sources

**Lundeen et al., 2009**, [journal article](https://doi.org/10.1038/nphys1133).
All four published pages, including Methods, were read from the author's
institutional copy. Known probe states determine linear Born probabilities;
physical POVM constraints and regularization address detector reconstruction.
The worked optical detector is not our qubit loss-only detector. Its trusted
probe assumptions explain why calibration must be specified. It does not
give our finite four-binomial coverage claim. The six-page 0807.2444v1 was
retained as supporting provenance; no complete edition-equivalence claim is
made.

**Keith et al., 2018**, [latest listed arXiv v2](https://arxiv.org/abs/1803.08245v2),
and the [APS accepted edition](https://link.aps.org/accepted/10.1103/PhysRevA.98.042318).
Read the model, joint likelihood, identifiability and observable bounds,
bootstrap discussion (Sections II-VI), and Appendix C stopping argument in
full. Known preparations and unitaries constrain an unknown measurement
transition matrix. Fixing the loss-only structural zeros reduces that
likelihood to our three count blocks. Alternation is separately concave,
without a guaranteed joint global optimum. Informationally incomplete data
can bound observable expectations without determining the full state.
Section VI explicitly limits bootstrap accuracy near boundaries; these
intervals are not a uniform finite 95% comparator. Appendix B coarse-graining
is not reused. The accepted edition's relevant stopping formula was compared;
no bytewise equivalence to the final published article is claimed.

There is a sign problem in the printed C2-C3 concavity bound in both reviewed
editions: a concave f satisfies `f(y)-f(x) <= grad(f)(x).(y-x)`.
For `f(q)=log(q), x=1/2, y=1`, reversing this displacement makes the right
side -1 although the left side is positive. The current
[official NIST code](https://github.com/usnistgov/state_meas_tomo/blob/d0188c9245ee1872089425fe29cd5430de4b314a/partial_tomography/tomography.py#L328)
uses the negative-log-likelihood gradient and computes the correctly signed
linear gap. Thus this bounded printed-formula finding is not evidence of
that sign error in the implementation. The source comparison is static;
the original package was not executed.

**Wang, Scholz and Renner, 2019**,
[Confidence Polytopes in Quantum State Tomography](https://arxiv.org/abs/1808.09988).
Read Theorem 1, the state-space formulation and the complete Appendix A proof
and intersection lemma in the ten-page v1. The proof reduces Born outcome
counts to binomial tails, uses the Clopper-Pearson construction and a union
bound, then obtains convenient outer regions using a Chernoff bound. This
establishes relevant finite-confidence prior art for a known POVM. It does
not treat our independently estimated efficiency intervals as deterministic
known quantities. Adding a separate calibration error budget and projecting
the resulting nuisance box is an elementary transfer of these generic ideas,
not evidence of a new quantum confidence principle.

**Aronow and Lee, 2013**, [article and supplement comparison](physical-volume-selection-comparison.md).
S046 already inspected the purchased article and all supplementary proofs.
The binary bounded-selection transform applies to detections-only data.
Its population interval is not itself a finite confidence procedure, and it
does not justify discarding the informative no-click count when benchmarking
the full-record model. The accepted generic binomial confidence construction
supplies the necessary sampling calibration. No repeat source purchase or
duplicated numerical comparator is required.

## Conditional causal-set field branch

**Johnston, 2009**, [latest listed v2](https://arxiv.org/abs/0909.0944v2).
All four pages were read, including the finite causal matrix construction,
commutator, spectral choice of two-point function and Feynman propagator.
The distinct earlier retarded continuum-limit proof cited there was not
reviewed here and is not imported as a theorem. **Bombelli et al., 1987**,
[Space-time as a causal set](https://doi.org/10.1103/PhysRevLett.59.521), remains
a metadata-level foundational pointer at this checkpoint. No step below
relies on an unread proof from it; no empirical or continuum-limit claim
follows from that pointer.

Screen one entry of a massive retarded scalar propagator on a finite causal
set sprinkled in a fixed 1+1 Minkowski diamond with marked endpoints. Use
the topologically ordered strict causal matrix C (future in a fixed matrix
orientation), known mass m and known sprinkling density lambda. No boundary
reflections are added. The causal retarded inverse is fixed by this finite
matrix; no vacuum choice is needed for this retarded quantity. Comparing
Feynman functions would additionally require a state prescription and is
outside this screen. Use absolute error of the marked matrix entry, bounded
by the Euclidean operator norm. For fixed C the 1+1 construction is

    K(gamma) = (1/2) C (I + gamma C)^(-1),
    gamma = m^2/(2 lambda).

Nilpotence makes the inverse a finite polynomial. The resolvent identity
gives, with R(gamma)=(I+gamma C)^(-1),

    ||K(gamma)-K(gamma')||
      <= (1/2)|gamma-gamma'| ||C||^2 ||R(gamma)|| ||R(gamma')||.

This is a conditional algebraic bound for the same observed matrix and
labels. Its constants may grow with matrix size. Given that full matrix and
the scale already, the propagator is directly computable; density
reconstruction is not needed to compute it. The existing geometric loss
does not by itself match sampled matrix entries, control near-null changes
in C, supply missing scale, or bound these resolvents. Poisson sprinkling,
thinning and observation of the complete marked order would have to be
specified together to bridge those gaps.

Disposition of the screen: keep a substantive field study behind a separate
story requiring that missing observation/stability bridge. The present
inequality is not such a bridge and is not a quantum-gravity prediction.
No field simulation or new field formalization is commissioned here.

## Contribution assessment at the source gate

The candidate has a precise full-record observation law, a simple confounding
example without calibration, and a usable route to finite confidence. Its
interval is algebraically identical to generic exact-binomial nuisance-box
projection. The sources establish detector calibration, joint likelihood,
partial identification and finite quantum confidence precedents. A scoped
formal transfer could be reusable; no new statistical advantage or physical
phenomenon is identified. The bounded evaluation will test implementation
and cost, not attempt to manufacture a distinction by changing the baseline's
information.

Remaining to-do list: bounded qubit evaluation and applicable certification;
field follow-up remains gated on a distinct stability/observation argument.
