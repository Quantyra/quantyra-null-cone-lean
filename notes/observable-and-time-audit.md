# Order labels and proper time comparison

2026-10-06, E002/S005. These elementary mathematical arguments complete two specification checks. They are not part of the compiled finite rank theorem and carry no novelty claim.

## Labels supply no extra information in these laws

Fix k. The labeled order law from k iid events is invariant under every permutation of the event indices. Let O be an orbit under relabeling, so O corresponds to an unlabeled directed poset isomorphism class. Every labeled order in O has the same probability, namely p_O/|O|, where p_O is the unlabeled orbit mass.

For a second exchangeable law with orbit masses q_O, the labeled total variation is

`(1/2) sum_O sum_(P in O) |p_O/|O| - q_O/|O|| = (1/2) sum_O |p_O-q_O|`.

The right side is exactly unlabeled total variation. Therefore labeled and unlabeled finite-law TV distances agree at every k, and so do their Delta_N values. The inverse theorem can equivalently be stated using unlabeled order laws. It does not obtain information from event labels. The equivalence is specific to these exchangeable laws; it does not apply to arbitrary distributions on labeled orders. Unlabeled means order-preserving isomorphism, not identification with the time-reversed dual order.

## Proper time coefficient bound

Suppose rho,sigma>=1/2 and let delta=||rho-sigma||_infinity. At every point,

`|sqrt(2rho)-sqrt(2sigma)| = 2|rho-sigma|/(sqrt(2rho)+sqrt(2sigma)) <= delta`,

because the denominator is at least two. For an absolutely continuous future curve gamma=(u,v) from p to q, derivatives are nonnegative almost everywhere. Cauchy-Schwarz gives

`integral sqrt(u'v') <= sqrt((q_u-p_u)(q_v-p_v)) <= 1`.

Thus `|L_rho(gamma)-L_sigma(gamma)| <= delta`. With the K upper density bound each curve length is at most sqrt(3), so both suprema are finite. The sets of monotone admissible curves depend only on the common causal cones. Taking suprema over that same set yields

`|tau_rho(p,q)-tau_sigma(p,q)| <= delta`

for causally related endpoints, including closure endpoints under the stated endpoint convention. For incomparable endpoints both time separations are zero under the usual convention.

Coordinate interchange sends each admissible curve to one with swapped endpoints and leaves the product u'v' unchanged. Selecting the identity or swap attaining d_conf consequently bounds the uniform discrepancy of corresponding time separations by d_conf. Combined with the derived inverse rate, this gives the same bound `100(N^(-1/12)+Delta_N)` for that endpoint-matched proper-time error. It controls neither curvature nor derivatives of the metric.

2026-10-07 scope update: the order-only selector and observable-TV CDF separation are now GCP verified in `OrderSelector.lean` and `FiniteTV.lean`. Their observed law is the labeled directed-order code law defined in `Model.lean`. The exchangeability and labeled/unlabeled TV equivalence above still require a formal bridge before claiming the complete original unlabeled-observable theorem. Proper-time formalization remains a separately selectable consequence. Quantyra uses open-source, decentralized informal review and downstream use/testing; specialist review is not a required publication or workflow gate.

Remaining to-do list: formal label-law equivalence for the full inverse theorem; optional proper-time formalization; record actual public feedback, use and testing when available.

2026-10-07 later scope update: `InverseRate.lean` now proves the original all-N coefficient estimate and `Identifiability.lean` its all-law consequence on the square, with exact GCP acceptance. These exports use the actual labeled directed-order laws. The labeled/unlabeled equivalence above is still a prose bridge; proper-time formalization remains optional. The archived manuscript 0.2.0 formal-scope text predates these software proofs.

Remaining to-do list: formal label-law equivalence and final scope reconciliation; optional proper-time formalization and recording actual public feedback.
