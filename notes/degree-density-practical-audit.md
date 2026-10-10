# Degree estimator implementation and finite-constant audit

S039, 2026-10-09 (Hawaii). The accepted degree estimator is **exactly flat throughout the existing dense implementation's range 2<=n<=4096**. This is an implementation/constant audit, not the completed feasibility study. The bounded pilot and its fresh paired comparisons remain required. No evaluation samples have been generated for S039.

## Exact bounded specialization

The accepted definitions are `degreeOuterMesh`, `DegreeUseHistogram` and `degreeRadius` in [DegreeRateNumbers.lean](../QuantyraNullCone/DegreeRateNumbers.lean), and `selectedDegreeDensity` in [DegreeEstimator.lean](../QuantyraNullCone/DegreeEstimator.lean). Their [GCP acceptance](fourth-root-certification.md) remains unchanged. For n>=2, log(n)>=log(2)>1/2. Thus

    floor(sqrt(n/(8 log n))) <= floor(sqrt(n/4)) <= 32, for n<=4096.

The first active-branch requirement is mesh>=65536. The bounded implementation can therefore select the exact flat branch without evaluating floating logarithms or approximating the inactive histogram. Its density is one on the entire closed square; error radius is 1/2 and band [1/2,3/2]. Original-K bounds make that band's coverage deterministic. This is a specialization of the accepted estimator, not a new uniformly faster statistical rate.

[degree_density.py](../tools/degree_density.py) rejects n outside this documented range. It does not implement the active, enormous-n histogram branch. An API limit is not a theorem about all computational methods. The program checks the complete strict transitive order, uses the existing deterministic implication-class realizer, and independently checks both permutations against every input pair. Inclusive ranks are exactly 1 through n. Unsupported non-two-dimensional orders and malformed input are rejected; no input repair is performed.

Certificate permutations depend on the supplied vertex enumeration. The mathematical output is constant and hence exactly invariant under relabeling and global transpose, without relying on those permutations being canonical. A future nonflat implementation must implement the accepted quotient selector or prove another suitable invariant rule; deterministic label-dependent selection alone would not suffice. This audit does not claim to solve efficient canonical labeling.

Full-square interpolation here is exact constant extension, including boundaries. There is no finite-grid-to-continuum approximation. The flat branch is a mathematical branch, not a software/resource failure. A timeout or checker failure must remain separately recorded and cannot be converted into a successful experiment.

## Reworking the retained finite bound

Before choosing any numerical experiment, check whether parameter tuning within the *displayed accepted proof budget* can make it informative. Its simultaneous occupancy event requires every m-by-m cell occupied, so m^2<=n is necessary for any sample satisfying that event. At n<=4096 this gives m<=64, even if the original conservative logarithmic choice is abandoned.

The same proof controls recovered-coordinate error by s=32/m. For a cell of side ell<=1, its displayed shell-error term is 6s/ell>=192/m>=3. That term alone already exceeds radius 1/2. The remaining terms are nonnegative. Consequently tuning m, histogram width, the concentration split or a sharper binomial tail cannot make **this retained proof expression** certify radius below 1/2 in the supported range. The planned exact finite audit checks every integer n and every occupancy-feasible m in that range.

This calculation diagnoses the available certificate, not the actual estimator error or an information-theoretic barrier. New geometric rank constants, a different proof or estimator, more economical order representation, another target or a justified restricted class might behave differently. The nominal active-branch conditions additionally imply m>291600 from 270/sqrt(m)<1/2, long before considering the final constant 650. Increasing the current dense API's ceiling modestly cannot bridge that gap. No sharpened theorem endpoint is asserted.

These findings justify a bounded negative feasibility evaluation of the literal construction and argue against a parameter-only revised candidate based on the same proof terms. They do not justify skipping the requested paired pilot, its stress cases, independent report validation or measured computation costs.

## Stress models and evaluation preparation

The [protocol](degree-density-practical-protocol.json) includes the existing FGM and asymmetric polynomial models, plus two smooth product perturbations with coefficient c. For the boundary case, f(t)=(1-t)^8-t^8 has integral zero, absolute value at most one, and derivative magnitude 8((1-t)^7+t^7)<=8. With c=1/8 the density range lies in [7/8,9/8] and squared gradient is at most two. For the oscillatory case, f(t)=P4(2t-1), where P4(x)=(35x^4-30x^2+3)/8. Its extrema occur at x=0, +/-sqrt(3/7), +/-1 and have values 3/8, -3/7, 1. Its derivative extrema give absolute derivative at most 10 on [-1,1], hence at most 20 in t. With c=1/16 the squared density-gradient bound is 25/8<4. Both factors integrate exactly to zero, so each density has uniform marginals. Polynomial smoothness is immediate.

The exact evaluator computes cell extrema at endpoints and these critical values, plus exact antiderivatives for cell averages. A separate closed-form implementation checks the same values. Tests cover 4,095 supported n, 172,767 occupancy-feasible mesh choices, all 152 rank-permutation orders of sizes two through five in both original and reversed labels, invalid orders, altered certificates, polynomial extrema and the retained baseline interface on a fixed order. These are mechanical fixtures and finite constant checks, not pilot samples.

The planned confirmation undercoverage test has n=128 per target stratum and rejects nominal 95% coverage at 13 or more failures. Exact binomial arithmetic gives per-stratum size approximately 0.012066, below the allocated 0.025, and power approximately 0.957410 at actual coverage 85%. Both strata therefore have family size at most 0.05 by the union bound. The two-replicate pilot instead reports its broad exact binomial intervals and cannot establish 95% coverage empirically. Full-K confidence comes from the stated mathematical bounds.

Use fresh paired observations for the literal estimator, flat no-data baseline and retained split-DKW certified method. Include flat/nonflat original-K cases, asymmetric global-orientation checks, boundary-localized and oscillatory smooth densities, label permutation checks and deliberately misspecified controls. No latent coordinates may enter any estimator. Report exact full-square error where polynomial extrema permit it, simultaneous width, coverage uncertainty, mathematical-branch and software-failure rates, relation-construction cost and process memory.

The literal candidate's guaranteed width and equality to the flat baseline are already deterministic consequences of its source. A pilot can validate implementation and measure costs but cannot discover an improvement in those quantities. A conditional larger coverage experiment must have prespecified power and fresh seeds; it is warranted only if a separately justified revised candidate first passes the useful-width/improvement gate. No revision, evaluation sample or new theorem is silently substituted for the current candidate.

The six implementation test groups pass, including the retained baseline's serialized-report interface. The runner and separate artifact audit are prepared for the frozen protocol. Their complete source commit must be pushed before sampling; neither this note nor its unit checks claim pilot completion.

Remaining to-do list: push the complete freeze, execute the paired pilot, independently audit retained artifacts and deliver S039's bounded feasibility decision. S039 remains incomplete.
