# Restricted confidence theorem: current development checkpoint

S042, 2026-10-10. **Targeted GCP development passes for the actual restricted
family and the sharper geometric bound.** Incremental cache reuse is verified.
The complete finite-confidence theorem remains under development. Full
acceptance is still the preceding 1,165-report campaign; S042 remains at three
of five criteria and S043 remains gated.

The [ordinary theorem and investment audit](geometric-pair-audit.md) remains
the milestone specification. This checkpoint records subsequent development;
it does not promote the uncompleted pair-law or confidence steps to accepted
results. Root imports and the central acceptance audit are unchanged.

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

## Verification and efficiency

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
successful geometric target now supplies the next cache checkpoint, 39,025,530
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

Continue with the actual pair integral: future-interval volume and moments
under the explicit Lorentz transformation, followed by the radial/light-cone
integrals. Reuse the accepted determinant and coordinate-volume results and
the newly proved actual time moments. An endpoint that assumes the pair law
does not discharge this obligation.

Then prove the original order-only pair statistic's permutation representation,
its dependence-aware Bernstein bound, and measurable clipped inverse. Connect
them to the geometric bound in one finite-confidence endpoint. Register the
complete batch in the root and central audit and run full GCP acceptance at
that milestone. The existing quantitative assessment and its practical-utility
limitation remain in force; this development result is not an S043 go decision.

Remaining to-do list: certify the actual pair law and complete finite-confidence
endpoint, perform full GCP acceptance, and record the S043 go/park decision.
