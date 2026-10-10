# Joint endpoint continuity of actual weighted proper time

S042 component, 2026-10-09 (Hawaii). **Full GCP acceptance passes: 967 exact type/axiom reports, including 48 new results, with zero warnings.** S042 remains incomplete and S043 remains gated.

## Direct construction and quantitative comparison

The four new modules retain the coordinatewise absolutely continuous curve class and the weighted-length supremum defined in [the proper-time component](geometric-proper-time-certification.md). They implement the direct endpoint perturbation from [the ordinary representation note](geometric-diamond-representation.md#direct-ac-endpoint-perturbation-route-ordinary).

[LorentzCurveControl.lean](../QuantyraNullCone/LorentzCurveControl.lean) proves that the integral of a future-cone-valued derivative has future-causal increments on every subinterval. This follows from the AC fundamental theorem and the norm bound for a vector integral; the general lemma assumes no diamond containment or endpoint causality. For an admissible curve, its time coordinate is therefore nondecreasing and lies between the endpoint times. Flat proper speed is superadditive on the future cone, by applying the Euclidean triangle inequality to the lifts `(proper speed,spatial velocity)`.

[LorentzCurvePerturbation.lean](../QuantyraNullCone/LorentzCurvePerturbation.lean) constructs an adjusted curve directly in its original parameter. Let `A=q-p`, `B=q'-p'`, `0<=k<=1`, and suppose the residual `e=B-k*A` is future causal. For a timelike source increment, set

    theta(t) = (c_t(t)-p_t)/(q_t-p_t),
    g(t) = p' + k*(c(t)-p) + theta(t)*e.

The proof establishes coordinatewise AC, the new endpoints and the actual derivative `k*c' + (c'_t/(q_t-p_t))*e`. Its terms are future causal. The subinterval theorem gives `p'<=g(t)<=q'`, and causal convexity puts the entire curve in the original closed diamond when the target endpoints belong to it. This also handles boundary endpoints and intervals on which the original time coordinate is constant.

The point displacement and proper speed satisfy

    |g(t)-c(t)| <= |p'-p| + |B-A| + 4*(1-k),
    speed(g') >= k*speed(c')   almost everywhere.

If the weight values along g and c differ by at most `delta>=0`, integrating gives `L_w(g)>=k*L_w(c)-2*delta`. The constant two is the previously accepted flat-length bound on this diamond. These estimates use the actual weighted integrals.

[LorentzEndpointBounds.lean](../QuantyraNullCone/LorentzEndpointBounds.lean) supplies the causal residual and passes the length estimates to the actual suprema, including the inserted zero. If both endpoint increments have timelike margin at least `a>0`, `0<=eta<=1`, and `2*|B-A|<=eta*a`, choose `k=1-eta`. Uniform weight variation by at most delta over the displayed displacement scale yields

    |tau_w(p',q')-tau_w(p,q)| <= 2*hi*eta + 2*delta.

This is a quantitative forward comparison at timelike pairs. It requires no maximizing curve and no change of parameter.

## Continuity, including the boundary

[LorentzTimeContinuity.lean](../QuantyraNullCone/LorentzTimeContinuity.lean) combines the comparison with uniform continuity of the weight on the compact diamond. Near a timelike pair the timelike margin stays positive, so eta and the weight error can be chosen arbitrarily small. At all other pairs, the already accepted comparison `0<=tau_w<=hi*tau_flat` and the globally continuous formula

    tau_flat(p,q) = sqrt(max(T-|A_x|,0)*max(T+|A_x|,0))

give convergence to zero. The resulting theorem is joint continuity on the full product of closed diamonds, followed by uniform continuity there and an explicit corollary for the original normalized density weight `(rho/V)^(1/3)`.

The proof applies to any positive continuous bounded weight in the existing class, including continuous limits used in the ordinary compactness argument. The chosen route does not require reparametrization equivalence, a compact family of maximizing curves or a smoothness assumption on the weight.

## Verification and remaining scope

There are 48 new named type/axiom checks: 16 control lemmas, 14 curve-perturbation lemmas, 10 endpoint estimates and eight continuity results. The seventh development run, `space-control3-dev7-20261010T064258Z-6e7ca2`, passes 2,950 jobs, all 48 new standard-axiom reports and zero warnings. The initial 14-result control build also passed; the five intervening terminal development failures are retained. The successful development SSH process returned a local transport failure after printing remote exit zero, and a separate collection confirmed its successful receipt.

Proof commit `98725c9da11762007c97384990de7f5f4b8a3c44` was pushed before full acceptance. Run `space-control3-acceptance-20261010T064532Z-20d5ee` passes all 3,108 root jobs and 967 named reports. Its [receipt](../evidence/gcp/space-control3-acceptance-20261010T064532Z-20d5ee/receipt.json) and [independent delivery verification](../evidence/gcp/space-control3-acceptance-20261010T064532Z-20d5ee/delivery-verification.json) confirm the immutable archive, all 209 captured files (175 Lean inputs), raw committed blobs and normalized local sources agree. Source and pinned dependency identities are checked before and after execution; all theorem axioms are limited to `propext`, `Classical.choice` and `Quot.sound`. The earlier 919 audit statements remain verbatim, and all earlier mathematical modules are unchanged. Input archive SHA-256: `48d540481c57973bd80e99f23d44ff99900d269d75bbbb08bc0363005587a8e4`. The acceptance SSH process also returned a local transport failure after remote exit zero; a separate observation and evidence collection verified terminal success. All Lean/Lake execution was remote GCP-only.

The [cleanup receipt](../evidence/gcp/space-control3-acceptance-20261010T064532Z-20d5ee/cleanup.json) verifies original task ownership, no other Lean work, evidence collection before shutdown and final state `TERMINATED` at `2026-10-10T06:50:28.014911+00:00`.

Joint endpoint continuity is one ingredient of the geometric representation. The quotient topology and full measure support, the Jacobian/isometry action, coupling-loss properties and the restricted pair-law/randomized-label confidence construction remain separate obligations. The endpoint estimate is a forward continuity result, not an inverse guarantee from finite order data. S042's whole-story criteria remain two of five complete.

The next proposed construction is the image of `p -> (tau_w(p,·),tau_w(·,p))` in the product of continuous-function spaces on C. The intended proof uses continuity of currying, compactness of C and the sup metric on continuous functions. The accepted profile classification identifies its fibers exactly as equal points or two waist points. A continuous surjection from compact C to this metric image would be a quotient map, giving the required topology and a route to continuous descent of time separation. This implementation route still needs its own formal proofs, followed by full measure support and the loss properties; it does not change the intended boundary identification.

Remaining to-do list: quotient topology/support, gauge/loss and finite-confidence proofs for S042; then gated S043 and queued S047. S048 remains proposed separately.
