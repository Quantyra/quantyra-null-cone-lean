# Compact time-profile quotient and full sampling support

S042 component, 2026-10-09 (Hawaii). The 37-result GCP development build passes; full repository acceptance is pending. S042 remains incomplete and S043 remains gated.

## Exact topological realization

[LorentzTimeQuotient.lean](../QuantyraNullCone/LorentzTimeQuotient.lean) realizes the intended boundary quotient as the image of

    p -> (tau_w(p, .), tau_w(., p))

in the product of the two continuous-function spaces on the closed diamond C, with their sup metrics. The weight belongs to the existing positive continuous bounded class. Joint endpoint continuity proves that this profile map is continuous by currying. Its image is a compact metric space, and its continuous surjective projection from C is a closed quotient map. The earlier numerical-profile classification shows that two projected points agree exactly when the original points agree or both lie on the waist circle W. This supplies the quotient topology of C/W directly. The auxiliary metric supplies that topology; the coupling-distortion loss between measured geometries remains a separate construction.

Time separation is defined using selected representatives, and an exact identity proves independence of those choices:

    quotientTime(projection(p), projection(q)) = tau_w(p,q).

The product projection is also a closed quotient map. The identity therefore proves joint continuity of quotient time, followed by uniform continuity on the compact product. It remains nonnegative, bounded by twice the upper weight bound, and zero on the diagonal. Strict positivity between projected points is exactly the original chronology. The reverse triangle is proved for two consecutive positive time separations. Incoming and outgoing time profiles distinguish every pair of quotient points, and every time superlevel set is compact. These statements include the original normalized density weight `(rho/V)^(1/3)`.

The positivity condition in the quotient reverse triangle is explicit. Null causal incidence is not asserted to descend through the waist identification. Earlier causal reverse-triangle results on the original closed diamond remain unchanged.

## The original law and full support

[LorentzQuotientMeasure.lean](../QuantyraNullCone/LorentzQuotientMeasure.lean) pulls the existing density measure back along the measurable inclusion of C, then pushes it forward through the quotient projection. Mapping the intermediate measure back to the ambient space gives exactly the original `densityMeasure3 rho`. The probability mass is one, and the quotient measure's application to measurable sets is the original closed-diamond measure of their preimages.

The support argument first proves `closure(D)=C` by explicit radial contraction. Every ambient open set meeting C therefore meets D in a nonempty open set of positive Lebesgue measure. The original density lower bound gives domination by one half of the flat normalized measure. Consequently every nonempty relatively open subset of C has positive density mass. A continuous surjection transfers this property to the quotient, including neighborhoods of the collapsed waist. The construction does not replace the sampling law or assume that a measure-zero boundary can be discarded topologically.

## Verification

The audit adds 37 named type/axiom checks: 24 quotient and time-separation results, followed by 13 closure, measure transport and support results. All earlier 967 audit statements and mathematical modules are preserved. The third immutable GCP development build passes 2,962 jobs and all 37 named reports. The first run stopped at a library theorem-name mismatch in the uniform-continuity corollary; the second stopped at namespace/argument mismatches in measure transport. Both failures are retained. The third SSH process returned a local transport error after printing remote terminal exit zero; separate evidence collection verifies the remote outcome. Full acceptance and source-custody details remain pending. No Lean/Lake command runs locally.

## Remaining scope

These results discharge the compact time-profile quotient, continuous descent, point distinction, compact superlevels and full probability support for the selected model. The general Jacobian/isometry action and coupling-distortion loss properties still require proofs. The sup metric on this representation is not itself the selected statistical loss. Exact finite sample/order transport and the restricted pair-conditioning/confidence construction also remain open. No finite-order inverse guarantee follows solely from this representation.

Remaining to-do list: gauge/loss properties, restricted pair-law and finite-confidence proofs for S042; then gated S043 and queued S047. S048 remains proposed separately.
