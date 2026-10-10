# Admissible geometric confounding under independent detection

2026-10-09 (Hawaii), S040. Full GCP acceptance now covers the remaining geometric confounding endpoints of the [ordinary process proof](independent-thinning-process.md). It extends accepted [finite detection](thinning-certification.md), [random counts and Poisson laws](thinning-process-certification.md), [Laplace functional](thinning-laplace-certification.md) and [actual first-n sampling](thinning-stopped-certification.md). No published manuscript or frozen pilot changed.

## Concrete models

For 0<=epsilon<=1/2 set f(t)=2t-1 and rho_epsilon(u,v)=1+epsilon*f(u)*f(v). The formal proof establishes the original `InDensityClass`: global polynomial smoothness, density bounds [1/2,3/2] on the diamond, Euclidean Lipschitz constant 2, and both uniform marginals. It does not substitute the product norm or a weaker density class.

Compare flat density 1 with rho_epsilon. The flat detector is the constant 1-epsilon. Define the other detector globally by

    pi_epsilon(x) = (1-epsilon)/max(1-epsilon, min(1+epsilon, rho_epsilon(x))).

It is continuous and lies in [(1-epsilon)/(1+epsilon),1] everywhere. On the diamond it equals (1-epsilon)/rho_epsilon. Both actual accepted submeasures, constructed from generated locations and independent uniform marks, equal (1-epsilon) times flat diamond area. Their acceptance means are 1-epsilon and their normalized retained laws are identical flat probability measures. Epsilon=1/4 gives the original S038 pair, with common detector bounds [3/5,1] and flat detector 3/4.

## Complete observations and actual experiments

`MarkedOrder` records every directed chronological relation among n sampled points and any finite collection of common fixed anchors: sample-sample, sample-anchor, anchor-sample and anchor-anchor. The finite quotient identifies exactly sample permutations; every anchor role is fixed. Both maps are measurable, and the quotient observation is invariant under sample relabeling. Time reversal and different anchor identities are not identified.

The accepted equality covers the full marked matrix and its quotient by applying the proved equality of coordinate laws. It also covers every common measurable function of retained coordinates. The proof explicitly connects the concrete models to the actual uniform-mark channel and the existing stopped experiment.

`ConfoundingProcess` proves equal probabilities for every original retention pattern, and equal retained-coordinate submeasures on those pattern fibers. It proves equal finite generated-count submeasures, equal arbitrary independent count mixtures, and equal count-dependent observations. Thus generated counts with a common fixed or Poisson law, including a known generation intensity and empty outcomes, do not remove this ambiguity. The count-bearing full marked-order map is explicitly constructed. Each stopping-prefix submeasure also agrees, so observing the first-n stopping prefix does not resolve it. These are actual process pushforwards; iid retained sampling and observational equivalence are derived.

Rejected locations, observed detector values, adaptive anchors, correlated detection and geometry-dependent stopping are additional experiments outside these statements. The accepted Poisson Laplace endpoint remains real-valued nonnegative measurable testing; no extra extended-real test claim is introduced here.

## Distinct physical targets

| Target | Certified separation |
| --- | --- |
| Open interval between (0,0) and (1/2,1/2) | Flat volume 1/4; alternative volume 1/4+epsilon/16. At epsilon=1/4 these are 1/4 and 17/64. |
| Density coefficient, allowing global coordinate transpose | `coefficientDeviation` and `conformalDistance` both equal epsilon. |
| Actual AC-curve maximal proper time, (0,0) to (1,1) | At epsilon=1/4 the alternative exceeds the flat value sqrt(2) by more than sqrt(2)/30. |

The proper-time proof uses the existing `FutureCurve.length` and `timeSeparation`. Cauchy-Schwarz bounds every flat curve and the diagonal attains sqrt(2). For the alternative, the formal proof uses the slightly stronger elementary bound sqrt(1+x)>=1+4x/9 on [0,1/2]. Integration gives diagonal length at least sqrt(2)*(1+4*epsilon/27); epsilon=1/4 then supplies the strict stated gap. The squared-profile integral is exactly 1/3. Closure anchors follow the original curve convention and supply no clock measurement.

## Arbitrarily randomized estimation

The general testing theorem permits any measurable observation space and any common independent probability seed. Equal observation laws and disjoint measurable success events imply that at least one model has failure probability at least 1/2. This is proved from the actual product measure, not assumed as a testing axiom.

Concrete full marked-order corollaries use the physical targets above. Any common scalar radius with 2*r<epsilon/16 fails for physical volume, and any density radius with 2*r<epsilon fails for the existing transpose-aware `DensityEstimateGood` criterion. At epsilon=1/4 these include every radius below 1/128 and 1/8 respectively. Proper-time radii with 2*r<=sqrt(2)/30 also fail. The event is strict scalar error exceeding r, or the complement of the stated density success event. Generic scalar corollaries cover actual mixed-count and stopped experiments; an explicit mixed-count marked-volume corollary is included.

This is an explicit geometric instance of established detection confounding, not a claim that generic thinning or two-point testing is new. Additional retained data cannot eliminate this ambiguity under the declared unknown-detector class. The result is compatible with the bias-aware intervals: those retain a calibration term.

## Ordinary-to-formal map

| Ordinary obligation | Accepted modules and endpoints |
| --- | --- |
| Admissible polynomial alternatives | `ConfoundingGeometry`: original-class membership, marginals, smoothness and Euclidean bounds. |
| Globally valid detectors | `ConfoundingDetector`: continuity, probability range, diamond agreement and product cancellation. |
| Actual accepted and retained laws | `ConfoundingLaw`: accepted submeasure, acceptance mean, flat retained law and actual stopped-observation equality. |
| All marked chronology, only sample labels discarded | `MarkedOrder`, `ConfoundingMarked`: measurable maps, exact quotient relation, full law equality. |
| Patterns, counts and first-n prefix information | `ConfoundingProcess`: actual pattern/count/stopping submeasures, arbitrary count mixtures and count-bearing marked observations. |
| Physical target separation | `ConfoundingTargets`, `ConfoundingTime`: actual mass, existing density quotient and actual AC-curve time separation. |
| Arbitrary independent randomization | `ConfoundingMarked`, `ConfoundingTesting`: general disjoint-success proof, scalar and density consequences, actual mixed/stopped scalar experiments. |

## Acceptance and custody

GCP run `space-confounding-acceptance-20261010T012022Z-a9c580` passed 3,088 full-root build jobs and **743 exact type/axiom reports**, including 70 new theorems in nine modules. All 187 captured source identities match the archive, current files and staged Git blobs. Pinned dependencies were checked before and after; there were zero warnings and only `propext`, `Classical.choice` and `Quot.sound`.

Lean 4.30.0 and mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` ran on `quantyra-lean-builder-01`, `us-central1-a`, project `quantyra-lean-cert-20260915`. [Receipt](../evidence/gcp/space-confounding-acceptance-20261010T012022Z-a9c580/receipt.json), [source/axiom custody result](../evidence/confounding/formal-verification.json), [verification script](../checks/verify_confounding_acceptance.py). Development failures and transport retries are retained. Compilation used isolated ephemeral GCP RAM caches with persistent source archives and raw logs; other campaigns and the reusable accepted disk cache were preserved. No workstation Lean invocation occurred.

After collection and a no-other-Lean-work check, the task-owned VM was stopped and verified `TERMINATED` at `2026-10-10T01:28:12.292881+00:00`. [Cleanup](../evidence/gcp/space-confounding-acceptance-20261010T012022Z-a9c580/cleanup.json). The unchanged frozen pilot, existing proof baseline except root/audit integration, and all manuscript/DOI artifacts pass custody checks. No new samples were drawn.

## Decision

Continue bounded-bias marked-volume inference. S041 supplies accepted finite calibration and a passing frozen pilot; this result closes the process/confounding proof obligations. Unrestricted unknown detection cannot identify the physical targets in this experiment. S044 must still justify its operational measurement model and run a separately frozen fair comparison; no physical detector or resource-management advantage has been validated.

S046 may reuse this family and the complete observation maps, but still needs its uniform-in-R detector specialization, sampling lower bound, joint upper/lower endpoint, remaining primary-proof comparison and manuscript disposition. This delivery does not certify the S046 minimax theorem or change published PDFs.

Remaining to-do list: none for this confounding certification; S039, S042-S044 and S046 remain selected in the dedicated planning repository.
