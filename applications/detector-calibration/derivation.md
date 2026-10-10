# Discrete recovery: an ordinary consistency calculation

Consider independent pulses, each containing one photon with probability b and otherwise none. Conditional on age j pulses since the last registered click, the click probability is h_j = q r_j, q = b eta_0, with deterministic recovery 0 <= r_j <= 1. A click resets the age to zero; a missed photon does not reset it. No dark counts, afterpulses, multiphoton pulses, illumination fluctuations or other memory are included. Assume r_j >= c > 0 eventually and q > 0.

Let W be the positive-integer inter-click waiting time. By multiplying conditional failure probabilities,

    S_0 = 1,
    S_k = P(W > k) = product_{j=1}^k (1 - q r_j),
    P(W=j) = S_{j-1} q r_j,
    E W = sum_{k=0}^infinity S_k.

The eventual lower hazard bounds this sum by a finite geometric tail. Renewal cycles are independent under the stated source/reset assumptions. One click per cycle therefore gives stationary click probability per pulse p = 1 / E W. Equivalently, the age distribution at a trial is a_j = p S_{j-1}; it sums to one and its total hazard is p, since sum S_{j-1} q r_j telescopes to one. This is established survival/renewal reasoning, not a new theorem of statistical physics. The continuous-illumination analogue is explicit in Krause and Walenta (2025), equations 4-11; their Poisson illumination law is different from the pulsed Bernoulli law here.

If r_j = 1 for j >= m, then

    E W = sum_{k=0}^{m-2} S_k + S_{m-1}/q.

The implementation returns this finite sum plus analytic tail. If the true monotone recovery only satisfies 1-epsilon <= r_j <= 1 for j >= m, retain the exact prefix and bound the tail between S_{m-1}/q and S_{m-1}/[q(1-epsilon)]. Invert the two positive mean bounds in reverse order for a rigorous arithmetic formula for p (floating-point evaluation itself is not interval-certified). This controls recovery-tail truncation, not physical model error.

For d fully blind pulses followed by full recovery, W = d + Geometric(q) and

    p = q/(1+d q),              q = p/(1-d p).

The inverse requires p < 1/d when d > 0, and q <= 1 restricts p <= 1/(d+1). The d=1 instance agrees with the zero-dark-count specialization in Lopez et al. (2020), equation 4 and appendix A.1.

Replacing the actual age probabilities p S_{j-1} by geometric weights p(1-p)^(j-1) instead leads to p = q(1-p)^d. These equations agree for d=0,1, but do not generally agree for d>=2. At d=2, q=1/2, renewal gives p=1/4; the geometric equation gives p=2-sqrt(3). If the true measured p=1/4 is inverted with the geometric equation, it returns q=4/9 instead of 1/2. A threshold at 19/40 would classify the true input as below threshold incorrectly. This is an exact counterexample inside this idealized model, not an experimental outcome or a claim of advantage over classical renewal inference.

Georgieva et al.'s deposited `get_readiness` uses the geometric age weights. Its recovery scaling uses the negative one-quarter power and does give R(t_dead+t_reset)=0.95. A possible discrepancy in the printed recovery scaling is therefore not an error in that code's 95% convention. Use the code convention consistently in both comparisons. Its 0.999 recovery cutoff is a separate approximation; compare both matched cutoff and converged tails before assigning a difference to age weights.

Increasing any recovery r_j or q decreases each survival probability and hence increases p. Thus, valid simultaneous recovery bounds can be propagated monotonically. Producing such bounds from a physical histogram requires its acquisition law and exposure/normalization information; a plotted normalized correlation curve alone does not establish them.

Remaining to-do list: independently check this calculation numerically, inspect the physical data's predictive compatibility, and develop a decision benefit beyond this established renewal correction.
