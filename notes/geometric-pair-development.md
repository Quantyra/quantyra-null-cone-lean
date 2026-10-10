# Restricted confidence theorem: current development checkpoint

S042, 2026-10-10. **Targeted GCP development now passes for the actual pair
probability and restricted geometric inverse, together with family membership
and the sharper forward bound.** Incremental cache reuse is verified.
The complete finite-confidence theorem remains under development. Full
acceptance is still the preceding 1,165-report campaign; S042 remains at three
of five criteria and S043 remains gated.

The [ordinary theorem and investment audit](geometric-pair-audit.md) remains
the milestone specification. This checkpoint records subsequent development;
it does not promote the uncompleted confidence theorem to an accepted result.
Root imports and the central acceptance audit are unchanged.

## Mathematical progress

[LorentzTimeMoments.lean](../QuantyraNullCone/LorentzTimeMoments.lean) derives
the actual time pushforward of Lebesgue measure restricted to the original
diamond. Spatial disk sections give the normalized time distribution and
`E[t^2]=1/10`, `E[t^4]=1/35`. These are integral identities for the existing
sampling measure, without an assumed marginal law.

[LorentzTimeFamily.lean](../QuantyraNullCone/LorentzTimeFamily.lean) proves
that `rho_theta=1+theta*(t^2-1/10)`, `theta in [0,1/2]`, belongs to the original
smooth density class. It proves normalization, bounds `[19/20,29/20]`, the
required Lipschitz bound, and `E[(t^2-1/10)^2]=13/700`.

[LorentzTimeEnvelope.lean](../QuantyraNullCone/LorentzTimeEnvelope.lean) uses
a shorter rational integral proof of the ordinary audit's sufficient bound:

    g(t)=t^2-1/10+2*max(0,1/10-(9/10)*t^2),
    |t^2-1/10| <= g(t),    integral_(-1)^1 g(t) dt = 5/9.

The split points are `-1/3` and `1/3`. The primitive is Lipschitz on `[-1,1]`;
composition with the actual AC time coordinate, the a.e. chain rule and the
fundamental theorem give the required curve integral estimate. No curve
reparametrization or unproved substitution law is assumed.

[LorentzTimeGeometry.lean](../QuantyraNullCone/LorentzTimeGeometry.lean)
then proves

    geometricDistortion3(rho_theta,rho_phi) <= (3/20)*|theta-phi|.

It uses the actual AC weighted lengths, their time-separation suprema, and the
accepted common-density coupling on profile quotients. A difference-of-cubes
argument gives the weight constant `27/100` without differentiating real
powers. For unmatched mass, the rational pointwise bound
`|f| <= (10/3)*f^2+3/40` gives `E|f| <= 23/168 < 3/20` from the actual second
moment. This replaces the ordinary audit's Cauchy–Schwarz calculation while
retaining its stated sufficient constant. No sharpness claim is made.

The subsequent interval and pair integration is now proved against the actual
sampling measure. [LorentzBoost.lean](../QuantyraNullCone/LorentzBoost.lean)
constructs an explicit rational Lorentz boost, proves its determinant and
Lebesgue-volume preservation, and proves preservation of strict chronology.
The interval map sends the original diamond to the chronological interval
between arbitrary strictly related endpoints. Its volume is
`V*(T/2)^3`, where `T=sqrt(-lorentzSquare(q-p))`.

Actual spatial reflections, coordinate exchange and radial integration give
zero means and mixed moments, `E[t^2]=1/10` and
`E[x^2]=E[y^2]=3/20`. Transporting these moments proves the future interval's
conditional shape mean

    M(t,r) = (7+18*t+11*t^2)/40 + 3*r^2/80.

[LorentzIntervalMoments.lean](../QuantyraNullCone/LorentzIntervalMoments.lean)
then gives the actual density-measure probability of the future of each
interior point. No interval-volume or covariance formula is assumed.

The proved light-cone substitution `t=1-a-b`, `r=b-a` maps
`0<a<b<1` to the radial diamond and contributes the normalized factor
`6*(b-a)`. The future flat volume is `(a*b)^(3/2)`.
[LorentzTriangleMoments.lean](../QuantyraNullCone/LorentzTriangleMoments.lean)
proves the general monomial integral from the real-power primitive.
[LorentzPairIntegral.lean](../QuantyraNullCone/LorentzPairIntegral.lean)
expands the finite polynomial and integrates its coefficients exactly.

[LorentzPairProbability.lean](../QuantyraNullCone/LorentzPairProbability.lean)
connects this integral to the product measure, the original two-sample law,
and the event `code 0 1 = true` in the original order law:

    q(theta) = 4/35 + (36/1925)*theta - (151/375375)*theta^2.

[LorentzPairConditioning.lean](../QuantyraNullCone/LorentzPairConditioning.lean)
proves the comparable-pair probability `p(theta)=2*q(theta)`, using symmetry
and disjointness of the two strict orientations. It proves

    (13738/375375)*|theta-phi| <= |p(theta)-p(phi)|,
    d_G(theta,phi) <= (225225/54952)*|p(theta)-p(phi)|.

Consequently, equality of the original two-point order laws identifies the
parameter within this restricted family. This is a quantitative population
statement; a finite observation still needs the concentration and inverse
estimator proof. It is not full-class conditioning or a physical detector
model.

## Verification and efficiency

The current combined target is `QuantyraNullCone.LorentzPairConditioning`.
GCP run [`space-pair3-dev22-20261010T123035Z-433904`](../evidence/gcp/space-pair3-dev22-20261010T123035Z-433904/receipt.json)
passes with zero warnings. Its 56 new printed axiom reports use only
`propext`, `Classical.choice` and `Quot.sound`. The final incremental build
took 10 seconds, excluding transport, compression and collection.
The [current artifact validator](../evidence/geometric-gauge/pair-integral-development/verify-development.py)
and [retained result](../evidence/geometric-gauge/pair-integral-development/development-validation.json)
check the exact new sources, standard axiom reports, all preceding mathematical
inputs unchanged, and all 16 terminal development outcomes from dev7 through
dev22. Failed intermediate captures and the earlier successful build with
linter warnings remain preserved. This validator only checks artifacts;
all compiler invocations ran on GCP.

The [current shutdown receipt](../evidence/gcp/space-pair3-dev22-20261010T123035Z-433904/cleanup.json)
records the instance ownership established by dev7, collected outcomes,
the verified retained successful cache, and task-owned shutdown. The accepted
1,165-report campaign, published manuscripts and frozen studies are unchanged.

The preceding family/geometric checkpoint remains preserved:

GCP run [`space-pair3-dev6-20261010T114526Z-23f3f2`](../evidence/gcp/space-pair3-dev6-20261010T114526Z-23f3f2/receipt.json)
passes the combined target, 2,981 jobs, with zero warnings. All 21 new printed
axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
[Artifact validation](../evidence/geometric-gauge/pair-campaign-development/development-validation.json)
checks the immutable archive, all 243 captured source files, all 239 preceding
inputs unchanged, and the 11 collected campaign outcomes. There are 209 Lean
inputs. The [validation script](../evidence/geometric-gauge/pair-campaign-development/verify-development.py)
performs local artifact checks only; it invokes no compiler. The five failed
development captures and their diagnostics remain preserved. The passing
target took 18 seconds of build time, excluding cloud control and collection.

The first two cache probes passed compilation but failed to retain their
RAM-only cache between SSH sessions. Their evidence is preserved. The fixed
route stores a compressed task-owned checkpoint on the persistent disk and
extracts it into a fresh run-specific RAM directory. It verifies the archive
hash, toolchain, dependency identities and source snapshots, uses an exclusive
cache lock, and replaces the checkpoint only after a successful target build.
Every submitted source archive and terminal outcome remains immutable.

The [cache checker](../tools/check_gcp_incremental_cache.py) and its
[retained result](../evidence/geometric-gauge/pair-campaign-development/cache-validation.json)
verify three controlled persistent-cache runs:

| Run | Result | Build time |
| --- | --- | ---: |
| `space-pair3-cache3-20261010T112429Z-c7e358` | Seed checkpoint | 69 seconds |
| `space-pair3-cache4-20261010T112716Z-93b105` | Unchanged replay; all 489 tracked artifact hashes and timestamps retained | 3 seconds |
| `space-pair3-cache5-20261010T113018Z-7b7d8a` | Probe edit rebuilds exactly the probe and its dependent module | 8 seconds |

Times exclude transport, compression, extraction and evidence collection;
they are not a general wall-clock speedup guarantee. Probe modules exist only
inside the immutable test captures, not in the project source tree. The
successful geometric target supplied that checkpoint, 39,025,530
bytes, SHA-256 `c522380755bae196b8f635b09c05de925fe852b03196714516032abe659e8a0f`.

All Lean/Lake invocations were on the established GCP instance. The
[shutdown receipt](../evidence/gcp/space-pair3-dev6-20261010T114526Z-23f3f2/cleanup.json)
records ownership, no other Lean work, collected outcomes and the verified
persistent cache before stopping the task-owned instance. Earlier accepted
proofs, manuscripts and frozen studies are unchanged.
The first cleanup SSH process returned a nonzero Windows process code after
printing its checks; its outcome remains retained. A separately recorded
successful preflight retry precedes the stop operation.

## Next decisive work

The actual pair integral, original order-law bridge and geometric inverse
conditioning now pass targeted GCP compilation. Reuse these results without
repeating their source comparison or cache probes.

Prove the original order-only pair statistic's permutation representation,
its dependence-aware Bernstein bound, and measurable clipped inverse. Connect
them to the geometric bound in one finite-confidence endpoint. Register the
complete batch in the root and central audit and run full GCP acceptance at
that milestone. The existing quantitative assessment and its practical-utility
limitation remain in force; this development result is not an S043 go decision.

Remaining to-do list: complete the all-pairs finite-confidence endpoint,
perform full GCP acceptance, and record the S043 go/park decision.
