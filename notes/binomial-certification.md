# Exact binomial intervals for marked physical volume

S041 / S040, 2026-10-09. This note connects the [ordinary statistical proof](marked-volume-finite-data.md), the [frozen pilot](marked-volume-pilot-result.md) and the formal exact-tail report checker. GCP acceptance and repository delivery are recorded in the accompanying verification receipt; a source definition or Python check alone is not Lean acceptance.

## GCP acceptance

Run `space-binomial-recovery-acceptance-20261009T213645Z-07b480` passed the full root build with **3,042 jobs and 577 type/axiom reports**, including all 45 new exports below. It used Lean 4.30.0 and pinned mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` on `quantyra-lean-builder-01`, `us-central1-a`, project `quantyra-lean-cert-20260915`. There were zero warnings and only the standard axioms. All 154 captured source identities and pinned dependencies were checked before and after; the [custody verifier result](../evidence/binomial/formal-verification.json) also matches every accepted source to its working bytes and staged Git blob.

The earlier submission lost access before launch. Recovery confirmed its exact remote workspace absent, then launched a fresh immutable run with identical sources and dependencies. The [recovery disposition](../evidence/gcp/space-binomial-acceptance-20261009T201747Z-0d2576/recovery-disposition.json) preserves that distinction. Failed development logs remain intact. No local Lean invocation or new pilot sample was used. [Acceptance receipt](../evidence/gcp/space-binomial-recovery-acceptance-20261009T213645Z-07b480/receipt.json).

After preserving the accepted evidence and checking that no other Lean work was running, the task-owned VM was stopped. Its final state was verified as `TERMINATED`; the [cleanup receipt](../evidence/gcp/space-binomial-recovery-acceptance-20261009T213645Z-07b480/cleanup.json) records ownership and the terminal observation.

## Complete observation and coverage argument

Let S be a measurable subset of a probability space `(Omega,mu)`, and sample n independent points. For the physical specialization, S is the chronological interval between two independently fixed marked endpoints, and mu is normalized metric volume or its explicitly normalized retained-event law. For each sampled point the input is the conjunction of the two exact chronological anchor flags. It is invariant under relabeling the unmarked sample events. The anchors are additional marked observations; their latent coordinates are used by the simulator only, not passed to the estimator. This is not the unmarked full-density experiment of S036.

Write theta=mu(S). For a specific membership bit vector with k true entries, independence gives atom probability `theta^k (1-theta)^(n-k)`. The set of all vectors with k true bits is in bijection with k-element subsets of n labels, so its cardinality is `choose(n,k)`. Summing those disjoint atoms proves the complete count law, including n=0 and theta=0,1. No normal approximation, asymptotic independence or overlapping-suborder argument is used.

To compare two parameters theta<=eta, use the same n iid uniform random variables and threshold each at the two parameters. Every theta-success is an eta-success, so the count is ordered pointwise. Upper count tails increase with the parameter; lower tails decrease. The formal construction proves this coupling and identifies its law with that of the actual measured membership count.

For any probability measure on a finite ordered set, the chance that the realized upper-tail probability is at most alpha is at most alpha. If the rejection region is nonempty, take its smallest element: the entire region is contained in that element's upper tail, whose probability is at most alpha. The lower-tail statement uses the largest element. This proof also handles atoms and conservative coverage.

Now let each count k produce rational endpoints L(k), U(k). Require `0<=L(k)<=U(k)<=1`. The lower endpoint is accepted if it is zero or the upper binomial tail at parameter L(k) is at most delta/2. The upper endpoint is accepted if it is one or the lower binomial tail at parameter U(k) is at most delta/2. If L(k)>theta, monotonicity implies that the true upper-tail probability is at most delta/2; the analogous statement holds when U(k)<theta. The two rejection regions have combined probability at most delta. No monotonicity of the numerical endpoint algorithm in k is assumed.

These guards are a mathematical report-checker contract. The executable Clopper-Pearson approximation satisfies the contract after its integer checks. The no-data interval `[0,1]` satisfies it for every n, including zero. Outward rounding and fallback are safe because the guards are checked on the actual returned rational endpoints. Coverage does not assume that an unverified float root is exact. The independent pilot audit additionally locates each exact root within one 1/65,536 grid step of its outward endpoint; that diagnostic is not needed by the universal coverage proof.

## Integer arithmetic correspondence

For a rational trial parameter m/d with `0<=m<=d` and d>0, the mass numerator for count j is

    choose(n,j) * m^j * (d-m)^(n-j),

with common denominator `d^n`. Summing the appropriate numerators and cross-multiplying against a positive rational tail budget is equivalent to the rational-tail guard. For 0<m<d and j<n, the next numerator is the exact integer quotient

    current * (n-j) * m / ((j+1)*(d-m)).

The proof uses `choose(n,j+1)*(j+1)=choose(n,j)*(n-j)` and the corresponding power identities. The executable checks the division remainder rather than tolerating inexact division. At m=0 or m=d it returns the appropriate deterministic atom directly. This gives a direct correspondence between the formal finite sums and the tested Python recurrence. Python, SciPy and the runtime are not compiled by Lean; the universal mathematical checker and recurrence are the formal statements.

## Physical composition and limits

Under retention probabilities between a and b, the detected interval mass theta and physical volume v obey the already certified bounds

    theta / (R-(R-1)*theta) <= v <= R*theta / (1+(R-1)*theta),  R=b/a.

The increasing endpoint transforms therefore carry the exact-tail confidence interval to physical volume with the same failure budget. The formal theorem uses the actual marked-code pushforward of iid samples from the normalized retained measure, derives its binomial count law, and proves coverage of the physical target. It does not replace the separate proof that an independently thinned generated process has that conditional iid law; that construction remains in S040, together with the complete S038 observational-equivalence counterexample.

This direct functional result needs no density reconstruction, coordinate recovery, metric derivative bounds or proper-time approximation. Its matching error is zero under the declared fixed marked endpoints and exact chronology; endpoint selection after inspecting the evaluation sample is excluded. Its numerical calibration is the rational report guard. It reports a dimensionless volume fraction; absolute volume and time still need external physical scale information. The known-geometry pilot and baselines are unchanged, and no new data are drawn during certification.

The contribution is the fully connected observation, detection and executable-calibration guarantee, with exact proof and retained numerical evidence. Exact binomial confidence intervals themselves are established Clopper-Pearson methods, as documented in the ordinary proof's primary-source comparison. No new field validation, shortest-interval optimality or general higher-dimensional metric-reconstruction claim follows.

## Ordinary-to-formal map

| Obligation | Formal endpoint or component | Boundary |
| --- | --- | --- |
| Actual iid observations give the binomial count law | `membership_law_atom`, `bit_count_fiber_card`, `membership_count_atom`, `marked_count_eq_binomial` in `BinomialObservation.lean` | Measurable interval and genuine iid product law; all sample sizes and probability endpoints. |
| Uniform coupling and exact inversion | `threshold_count_mono`, `binomial_upper_tail_mono`, `binomial_lower_tail_antitone`; `finite_upper_tail_pvalue`, `finite_lower_tail_pvalue`, `binomial_tail_interval_coverage` | Finite atomic tails, with no asymptotic approximation or endpoint monotonicity assumption. |
| Rational returned report | `binomial_report_coverage`, `marked_binomial_report_coverage`; `binomial_report_check_sound` | Every count's returned endpoints must pass the mathematical report contract. |
| Integer implementation arithmetic | `binomial_mass_integer_identity`, upper/lower integer identities and checks, `binomial_numerator_recurrence`, `binomial_numerator_division` | Exact formulas for finite sums and recurrence; Python loop execution is independently tested, not a compiled Lean program. |
| Detection calibration | `retained_binomial_report_coverage` composed with accepted `retained_physical_identification` | Known deterministic positive bounds on the retention weight; no instrument calibration claim. |
| Original geometry and matching | `null_interval_rectangle`, `null_interval_measurable`, `InDensityClass.marked_binomial_coverage`, `InDensityClass.retained_marked_binomial_coverage` in `BinomialGeometry.lean` | Actual original-class normalized density measure and strict null chronology, fixed marked endpoints. |
| Label invariance and implementation count | `bit_count_relabel`, `bounded_bit_count_relabel`, `marked_fraction_bit_count` | Event permutations preserve the count and report; endpoint roles remain marked. |
| Valid and invalid examples | Four theorems in `BinomialFixtures.lean` | Zero and one sample, accepted conservative report, rejected narrow and reversed reports; kernel-checked proofs without `native_decide`. |

Matching error is zero because the same two fixed marked anchors define the observed flags and target set. Estimation error is the exact finite binomial-tail failure budget. Known detection calibration is an interval transform, not a vanishing statistical error. Numerical endpoint error is outward and coverage-safe by the guard; the retained full tables separately certify the one-grid-step approximation. Unknown endpoint matching, uncertain external retention bounds, missing chronology and absolute-scale recovery need additional assumptions and are excluded from this completed functional target.

The existing frozen artifact audit validates all n+1 endpoints for each n in `{0,64,256,1024}` (1,348 intervals total), and its 2,688 inward-neighbor rejections locate every nontrivial exact root to one grid step. Those large tables were checked with exact Python integers; they are not claimed to have been individually reduced by the Lean kernel. The theorem proves the universal contract their checks implement.

Remaining to-do list: S040's process construction and full confounding endpoint; S039, S042–S044 and S046 remain selected in the planning roadmap. S041's final requirement/delivery audit is maintained there.
