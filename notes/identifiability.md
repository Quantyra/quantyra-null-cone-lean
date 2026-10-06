# Identifiability from all finite abstract orders

2026-10-06. Proof draft for E002/S005. This specializes established kernel-equivalence machinery; it is not claimed as a new theorem. Independent review and Lean verification remain outstanding.

## Statement

For continuous positive probability densities rho and sigma on the square, both with uniform coordinate marginals, equality of all finite labeled sampled product-order laws implies rho = sigma or rho(u,v) = sigma(v,u). The numerical Lipschitz bound and smoothness in K are unnecessary for this qualitative statement. Conversely these two alternatives give equal laws.

## Imported result

[Janson, Poset limits and exchangeable random posets, Theorem 7.1(iv),(ix)](https://arxiv.org/html/0902.0306) identifies equal finite laws of almost twinfree Borel order kernels through a measure-preserving bijection outside null sets, preserving the kernel almost everywhere. It does not assert an everywhere order isomorphism; the following bridge supplies that step for this model.

## 1. Profiles distinguish interior points

Work on I = (0,1)^2, whose complement has measure zero. Write P_x = (0,x_1) times (0,x_2) and F_x = (x_1,1) times (x_2,1). For a measure mu with positive continuous density, define

`d_mu(x,y) = mu(P_x symmetric_difference P_y) + mu(F_x symmetric_difference F_y)`.

This is a metric on I. Distinct lower rectangles differ on a positive-area open rectangle: if x_1 < y_1, choose the first coordinate between them and the second below min(x_2,y_2); the other differing-coordinate case is symmetric. Positivity gives positive measure. Thus the kernel is almost twinfree.

Profiles are continuous in Euclidean coordinates even on the closed square: symmetric differences are contained in strips of total area at most |x_1-y_1| + |x_2-y_2| for each of P and F. A density upper bound M gives d_mu <= 2M times that sum.

If d_mu(x_n,x) tends to zero with x interior, then x_n tends to x in Euclidean coordinates. To see this, extract any subsequential limit z in the compact closed square. Continuity gives equal profiles at z and x. A boundary z has either an empty past or an empty future, whereas both masses are positive at x. An interior z must equal x by rectangle separation. All subsequential limits are therefore x.

Do not call d_mu a metric on the entire closed square: (1,0) and (0,1) have identical empty profiles.

## 2. Extend the almost-everywhere bijection

Janson supplies f between conull subsets of I. Fubini permits restriction to a conull subset S where both incoming and outgoing kernel rows agree almost everywhere under f. Apply the inverse correspondence too and intersect the good sets. For every x,y in S, integration of those rows proves

`d_mu(x,y) = d_nu(f(x),f(y))`,

and preserves separately the past and future masses. S and f(S) are Euclidean dense because the densities are positive.

For x in I choose x_n in S tending to x. The images are profile-Cauchy. Extract a Euclidean subsequential limit z in the closed square. Its past and future masses are the respective limits for x, both positive, so z is interior. Profile continuity and separation show every subsequential limit equals z; hence f(x_n) converges. Interleaving two approximating sequences proves that z is independent of the choice. This defines an extension F on I. Repeating the construction for the inverse gives mutually inverse continuous maps. Profile continuity proves F remains an isometry and agrees with f on S.

## 3. Recover the weak product order everywhere

For interior x,y, positivity and a rectangle witness give

`mu(P_x setminus P_y) = 0 iff x_1 <= y_1 and x_2 <= y_2`.

The good-row correspondence preserves this quantity on S. Its dependence on x,y is continuous in coordinates, so approximation and continuity of F preserve it on all I. The inverse does too. Therefore F is an automorphism of the weak product order.

## 4. Classify automorphisms without assuming coordinate rankings

For comparable x <= y, the order interval [x,y] is a chain exactly when x_1 = y_1 or x_2 = y_2. If both inequalities are strict, the cross-corners (x_1,y_2) and (y_1,x_2) are incomparable. If a coordinate is equal, the remaining coordinate totally orders the interval.

Call a set a fiber chain when every two of its points are comparable and their order interval is a chain. Its maximal sets are precisely full horizontal and vertical fibers. Indeed a pair of distinct points must share one coordinate; any third point sharing a coordinate with each must share that same coordinate. Maximality fills the fiber.

An order automorphism permutes these maximal sets. Distinct horizontal fibers are disjoint, whereas every horizontal fiber intersects every vertical one. Thus all horizontal fibers have the same image type, and all vertical fibers have the other type. The map consequently has the form F(u,v) = (a(u),b(v)), or the coordinate-swapped form. Bijectivity and order preservation make a,b increasing bijections of (0,1), hence homeomorphisms.

## 5. Uniform marginals fix the remaining gauge

F pushes mu to nu because it agrees almost everywhere with the original measure-preserving map. In the first case the first marginal is the law of a(U), with U uniform, and must itself be uniform. For every t in (0,1), P(a(U) <= a(t)) = t, while uniformity makes the same probability a(t). Thus a(t)=t. Similarly b(t)=t. The swapped case gives the coordinate swap. Equality of the resulting measures implies equality of their continuous densities on the interior and then, by continuity, on the closed square. The converse is obtained by coupling samples through the identity or swap.

## What this does not establish

No finite-N rate follows from this argument. The kernel-equivalence input has no quantitative bound here, and the profile argument is qualitative. Smooth K is not closed under uniform limits; any later compactness argument must use its Lipschitz closure and verify continuity of finite-order laws. Even a correct compactness argument supplies only an unspecified modulus, which does not meet S005's main research criterion.

Candidate substantive Lean target: the product-order automorphism classification, followed by uniform-marginal gauge rigidity. Freeze its exact library statement after the quantitative route is decided; do not present the entire all-law theorem as formally verified by proving only this component.

Remaining to-do list: independent proof audit; explicit inverse rate or obstruction; exact novelty comparison of that result; selected Lean statement and compiled proof.
