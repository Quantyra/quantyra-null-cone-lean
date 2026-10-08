# Remaining sharp-DKW finite probability contract

S024 implementation contract after [analytic acceptance](dkw-analytic-certification.md). These probability statements are not yet Lean proved. The target remains the actual sharp two-sided `2*exp(-2*n*e^2)` under iid uniform sampling, and then the existing original-K split-DKW coverage. A weaker union bound is not a replacement.

## Finite bins and likelihood

Use `n>0`, `q>0`, profiles `Fin n -> Fin q`, scored by `x.val+1`. The uniform profile law assigns mass `1/q^n`. For `1<=k<=q`, let `C_k` count scores at most k and

`M_k=(1+lambda)^(-n)*(1+lambda*q/k)^C_k`, with lambda positive.

Prove `M_q=1`, nonnegativity, and terminal mean `E M_1=1`. For factorization, write `M_1=(1+lambda)^(-n)*product_i f(score_i)` where `f(1)=1+lambda*q` and all other f values are one. Mathlib's pinned `Finset.prod_univ_sum`/`sum_prod_piFinset` provide the finite product-of-sums identity.

At threshold k reveal `max(score_i,k)`. A revealed atom is a Cartesian product: each coordinate revealed as k allows bins 1..k; each coordinate above k allows just its known score. If the atom has c unresolved coordinates, prove its cardinal is `k^c` and the sum of terminal likelihood over it is `(1+lambda)^(-n)*(k+lambda*q)^c`. Dividing by `q^n` proves exactly

`E[1_atom*M_1] = P(atom)*M_k(atom)`.

The needed cardinal/sum facts cover k=q and k=1. They must be proved from the actual finite bin representation, not assumed as a conditional-law premise.

## Maximal bound from first crossings

For a positive threshold B, partition the crossing event by the largest k with `M_k>=B` (the first crossing as k descends). Prove that each part depends only on the revealed state at k: every `C_j` for j>=k is determined by that state. Thus each part is a union of complete revealed atoms. Sum the proved atom identity over each part. The parts are pairwise disjoint and exhaust the crossing event, so

`B*P(crossing) <= E[1_crossing*M_1] <= E M_1 = 1`.

This is a direct finite Ville/Doob proof. An abstract helper may assume an atom identity, but the actual-bin export must derive it. No maximal inequality or desired probability bound may become an assumption in the final iid theorem.

Apply the accepted analytic barrier to the same lambda for ALL k. If `C_k/n-k/q>e`, then `t=k/q` lies in `(0,1-e)` and `M_k>exp(2*n*e^2)`. Prove this with actual log/power identities and n positivity. The positive grid tail is at most `exp(-2*n*e^2)`. Reflect bins by `Fin.rev`; the reflected count at q-k equals n-C_k exactly, giving the negative tail and the two-sided factor two. The support endpoints have zero error. Require e>=0 in the full concentration export; e=0 and e>=1 have separate trivial branches.

## Uniform samples, dense grids and actual K

Quantize each actual uniform X by the ceiling bin, taking zero as a null endpoint case. Prove the bin pushforward is uniform from the actual interval masses and the profile pushforward is the iid finite law. Inclusive grid CDF counts agree exactly with ceiling-bin counts, including positive grid ties.

For dyadic q, prove the nested grid events have the same probability bound. Their union equals the real-threshold strict deviation event on supported samples: positive deviations use nearby grid points above the threshold; negative deviations use grid points below. Empirical monotonicity and continuity of the population uniform CDF suffice. Establish measurability through the countable grid union and pass by continuity of measure. Do not assume a supremum event is measurable without this bridge.

Finally transport each actual-K coordinate sample vector to the uniform product law using the accepted marginal and iid identities. The two coordinates of a sampled point may be dependent. Combine their sharp tails with the actual joint-grid Hoeffding union, rational exponential/ceiling allocations, and the proved conditional all-cutoff CDF theorem. This must match the current executable calibration and report representation.

Remaining to-do list: all finite probability/transport contracts above; density cell/point/histogram/report suite; final S024 acceptance; S025.
