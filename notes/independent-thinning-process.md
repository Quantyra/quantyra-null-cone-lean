# Independent detection and the retained observation experiment

2026-10-09, S040. This ordinary proof connects the generated-event model to the iid retained law used by the [accepted physical-volume guarantee](binomial-certification.md). It also supplies the complete observational conclusion for the [S038 confounding example](physical-observation-identifiability.md). **These process and confounding endpoints still require GCP Lean certification.** No new experiment, manuscript or physical detector validation is claimed.

## Generated events and actual retention

Let `(X,mu)` be a probability space with a measurable event-location space, and let `pi:X -> [0,1]` be measurable. Write

    alpha(B) = integral_B pi dmu,
    Z = alpha(X) > 0,
    nu(B) = alpha(B)/Z.

For the selected channel, known bounds `0<a<=pi<=b<=1` imply `a<=Z<=b`. Thus `nu` is a probability measure and is exactly the `retainedMeasure mu pi` already used in `MarkedThinning.lean`. Measurability of the detector is required for its interpretation as a random channel, even though some earlier analytic bounds need only integrability.

Generate iid locations `X_1,...,X_N` with law `mu` and independent iid uniforms `U_1,...,U_N` on `[0,1]`, independent of the locations. Retain event `i` precisely when `U_i<pi(X_i)`. The kept locations are listed in their original generation-index order. This order is only a convenient measurable representation; no spatial or temporal sorting is performed. A later observation map can discard all sample labels.

For measurable `B`, Tonelli's theorem on the actual location/uniform product space gives

    Pr{X_i in B, U_i<pi(X_i)}
      = integral_B length([0,pi(x))) dmu(x)
      = alpha(B),
    Pr{U_i>=pi(X_i)} = 1-Z.

Endpoints of the uniform interval have zero measure, so the strict retention comparison also handles `pi=0` and `pi=1`. Independence of the pairs `(X_i,U_i)` gives all subsequent factorizations. Retention indicators are iid Bernoulli `Z` after integrating locations; an indicator need not be independent of its own location.

## Conditioning on an arbitrary retained subset and count

Fix `N`, an index subset `I={i_1<...<i_n}`, and measurable sets `B_1,...,B_n`. Let `K_I` be the event that exactly the indices in `I` are retained. Independence and the one-event calculation give

    Pr{K_I, X_i1 in B_1, ..., X_in in B_n}
      = (1-Z)^(N-n) product_j alpha(B_j)
      = Z^n (1-Z)^(N-n) product_j nu(B_j).       (1)

This holds for every subset, including the empty subset, with empty products and zeroth powers equal to one. Where `Pr(K_I)>0`, dividing by that probability proves that the ordered retained tuple conditional on this precise pattern has law `nu^n`. A pi-lambda argument extends equality on measurable rectangles to equality of the product measures. Zero-probability patterns require no conditional-law assertion.

Let `M` be the retained count and `Y` the retained tuple. Summing (1) over the `choose(N,n)` disjoint subsets yields the actual joint law

    Pr{M=n, Y in B_1 x ... x B_n}
      = choose(N,n) Z^n (1-Z)^(N-n) product_j nu(B_j).       (2)

Consequently `M~Binomial(N,Z)` and, whenever `Pr(M=n)>0`, `Y | M=n ~ nu^n`. This is the law of selected locations, not merely a proof about the event that all generated locations are accepted. It includes `n=0` and `Z=1`; in the latter case only `M=N` has positive probability.

If the generated count `N` has an arbitrary independent distribution `q_N`, condition first on `N` and sum (2). The factors depending on the locations remain `nu^n` for every `N>=n`. Conditional on any positive-probability retained count `M=n`, the retained tuple therefore still has law `nu^n`. This proof requires an independently generated count; a location-dependent stopping rule is not covered by that statement.

## Fixed retained sample size and Poisson generation

The pilot samples until it has a prescribed number of retained events. This can be justified separately. For an infinite iid sequence of event/uniform pairs, let `T_n` be the generation index of the nth acceptance. For `n>=1`, sum (1) over patterns with `n` acceptances among `1,...,N`, the last at `N`. There are `choose(N-1,n-1)` such patterns, so

    Pr{T_n=N, first n retained locations in B_1 x ... x B_n}
      = choose(N-1,n-1) Z^n (1-Z)^(N-n) product_j nu(B_j).

Because `Z>0`, there are infinitely many acceptances almost surely. For example, the probability of no further success after any fixed index is `lim_k (1-Z)^k=0`; the countable union of events of a last success also has probability zero. Thus `T_n` is finite almost surely. Summing the preceding identity over `N` proves that the first `n` retained locations have law `nu^n`. For `n=0` use the empty tuple. This justifies rejection sampling with a fixed retained count; stopping based on observed geometry or reported uncertainty would need a different argument.

For the physical Poisson model, suppose `N~Poisson(kappa)` independently, where the generated metric volume has been normalized to one. Substituting `q_N=exp(-kappa) kappa^N/N!` in (2), writing `N=n+r`, and summing nonnegative terms gives

    Pr{M=n, Y in B_1 x ... x B_n}
      = exp(-kappa) (kappa Z)^n/n!
          * sum_r (kappa(1-Z))^r/r! * product_j nu(B_j)
      = exp(-kappa Z) (kappa Z)^n/n! * product_j nu(B_j).    (3)

Thus the complete retained experiment consists of a Poisson `kappa Z` count and, conditional on that count, iid locations from `nu`. For non-normalized finite metric volume `V`, use generated mean `kappa V` and `mu=dvol_g/V`; the retained intensity measure is `kappa pi dvol_g`.

Equation (3) determines the full random finite counting measure, not just its first moment. Indeed for any nonnegative measurable `h`, condition on the retained count and sum its Poisson series to obtain

    E exp(-sum_retained h(Y_i))
      = exp(kappa * integral pi(x) (exp(-h(x))-1) dmu(x)).

This identity also covers repeated locations on an atomic space when they are represented with multiplicity. Our geometric density laws are atomless. We derive the finite Poisson experiment directly rather than treating a thinning theorem as a new assumption.

## Marked observations and the accepted confidence guarantee

Fix the anchors independently of the evaluation sample. For measurable strict chronology `C`, a complete marked observation can be represented by the Boolean matrix of `C` on all sample points and all fixed anchors. It includes sample-sample and anchor-sample relations, not only membership in one interval. Quotient by permutations of sample indices that leave each anchor role fixed. The finite Boolean matrix map and quotient map are measurable. Any identical additional randomized observation channel can be incorporated with an independent seed.

Equality of the retained tuple laws implies equality after each of these maps. In particular, conditional on `M=n`, or for the first `n` retained events, the membership code for fixed anchors `p,q` has exactly the `markedIntervalLaw (retainedMeasure mu pi) n C p q` used in the accepted binomial theorem. This supplies its physical generative interpretation.

Let every returned rational endpoint pair pass `BinomialReportValid n delta L U`. The accepted theorem then gives failure probability at most `delta` for the transformed physical-volume interval under every positive-probability retained-count conditioning. With a separately valid report for each count, the same bound holds unconditionally by summing over the count law. A count-dependent budget bounded by `delta` is also valid. No independence among overlapping suborders, post-sample anchor selection or missing-relation model is introduced.

## Complete admissible confounding example

On the null square let `f(t)=2t-1`, and define

    rho_0(u,v)=1,
    rho_1(u,v)=1+f(u)f(v)/4,
    pi_0(u,v)=3/4,
    pi_1(u,v)=3/(4 rho_1(u,v)).

Both densities are smooth on a neighborhood. On the square, `|f|<=1`, so `3/4<=rho_1<=5/4`. Since `integral_0^1 f=0`, both coordinate marginals and total mass are exactly one. The gradient of `rho_1` is `(f(v)/2,f(u)/2)`, whose Euclidean norm is at most `sqrt(1/2)`. Integrating the gradient along each segment in the convex square gives a Lipschitz constant below 2. Thus both models belong to the original class K, without adding a uniform higher-derivative assumption. The detectors are measurable and satisfy `3/5<=pi_j<=1`.

Pointwise `pi_j rho_j=3/4`. Therefore both accepted submeasures `alpha_j` equal `3/4` times flat area measure, both `Z_j=3/4`, and both retained probability measures are flat uniform. Equations (1)-(3) imply identical laws for every fixed generated count, every independently mixed generated count, every fixed retained count, the first n retained events, and the full retained Poisson process. Count information does not remove this example, even if the physical generation intensity is known. Detected original index patterns also have the same joint law if those indices are recorded; rejected locations or observed detector values are extra data not covered by the equivalence.

The physical metrics `g_rho=-rho(du tensor dv+dv tensor du)` have the same strict chronology because each is a positive conformal multiple of the flat metric. Hence the entire marked relation matrix has the same law, for any common finite set of fixed anchors, as does its sample-unlabeled quotient. This is a physical metric/detection ambiguity; the equality is not obtained by assuming the two target values coincide or by discarding informative sample-sample relations.

For `p=(0,0)` and `q=(1/2,1/2)`, the marked open interval is `(0,1/2)^2`. Since `integral_0^(1/2) f=-1/4`, its physical normalized volumes are

    v_0=1/4,    v_1=1/4+(1/4)(-1/4)^2=17/64.

Both detected interval probabilities are `1/4`, but the physical targets differ by `1/64`. The densities have sup distance `1/4`; both are invariant under coordinate transpose, so the same separation holds in the original transpose quotient.

There is also a proper-time separation with common closure anchors `(0,0)` and `(1,1)`. For the flat metric, Cauchy-Schwarz bounds every admissible absolutely continuous future-curve length by `sqrt(2)` and the diagonal attains it. For `rho_1`, the diagonal alone has length

    sqrt(2) integral_0^1 sqrt(1+(2t-1)^2/4) dt.

For `0<=x<=1/4`, the nonnegative quantities satisfy `sqrt(1+x)>=1+2x/5`, strictly for `x>0`: subtracting the squares gives `x/5-4x^2/25>0` when `x>0` in this range. Integrating and using `integral_0^1 (2t-1)^2=1/3` shows that this diagonal length is strictly greater than `sqrt(2)(1+1/30)`. Thus the maximal proper time differs from the flat value by more than `sqrt(2)/30`. Closure endpoints have the same declared curve convention as the earlier proper-time result; they supply no clock reading to the estimator.

## Randomized-estimation obstruction

Let the observation have the common law `P` just proved. Give any estimator an arbitrary independent seed with probability law `Q`. The joint input law is the same product `P x Q` under both models. If targets have distance `Delta`, success sets with radii `r_0,r_1` are disjoint whenever `r_0+r_1<Delta`, by the triangle inequality. Assuming measurable success events, their probabilities sum to at most one. Therefore at least one model has failure probability at least one half. The argument works for arbitrary seed spaces and for the full retained-process observation, not merely finite-valued deterministic estimates.

Consequently no estimator can have confidence strictly greater than one half under both admissible models at common radius below `1/128` for interval volume, below `1/8` for the transpose-quotient density loss, or below `sqrt(2)/60` for the marked proper-time target. These obstructions hold for every sample size and known generation intensity. They are compatible with S041: its bias-aware interval retains a nuisance contribution and does not assert point identification from an unknown detector. The example lies within the common bounds `[3/5,1]`, hence ratio `5/3`; it does not establish the uniform-in-ratio minimax theorem selected for S046 or sharpness of the general identification bounds inside K.

## Ordinary-to-formal obligations and disposition

| Proof endpoint | Existing accepted support | Remaining formal construction |
| --- | --- | --- |
| Actual independent detection | Normalized retained measure and positivity in `MarkedThinning.lean` | Location/uniform product channel, accepted submeasure, exact subset pattern identity (1). |
| Count-conditioned iid law | Membership/binomial finite product machinery | Measurable retained-tuple extraction, count fiber sum (2), conditional product law including positive-probability edge cases. |
| Sampling until n and finite Poisson process | Mathlib finite/countable product and Poisson probability tools | Almost-sure termination, first-n retained law, independent count mixture and series identity (3). |
| Physical report coverage | `retained_binomial_report_coverage` and original geometric specialization | Pushforward equality from the generated experiment; optional count mixture by total probability. |
| Admissible confounding | Original K, measure and chronology definitions | Polynomial class membership, valid compensating detectors, actual retained-law equality, full marked observation and quotient equality. |
| Distinct geometric targets | Existing AC-curve proper-time framework | Exact quarter-volume values, quotient density separation, flat maximal length and strict nonflat diagonal bound. |
| Randomized impossibility | Existing finite-seed testing theorem supplies the finite-data route | General common-law disjoint-success result and actual scalar/density/proper-time instantiations. |

Every remaining item is an ordinary proof above, not an already accepted Lean endpoint. The formal implementation must establish these concrete models and distributions; a theorem conditional on an assumed iid retained law or an assumed equal-observation conclusion would leave the main S040 obligation unresolved. No new sampling evaluation is needed for the process identity itself, and the frozen S041 pilot must remain unchanged.

Continue bounded-bias interval inference. Unrestricted unknown detection cannot identify the physical targets even with unlimited retained observations. Advance the S044 comparison only with the declared calibration and observation assumptions; operational applicability still needs an independently justified measurement model. This is a standard thinning mechanism and an explicit geometric specialization of familiar confounding, with no claim of a new generic Poisson-thinning theorem.

Remaining to-do list: implement and GCP-certify the complete process and confounding endpoints above, compose with accepted S041, verify delivery, and finish the S040 decision audit. S039, S042-S044 and S046 remain selected in planning.
