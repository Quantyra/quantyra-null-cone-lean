# Does recovery dependence change a range decision?

S049, 2026-10-10. The recovery diagnostic identifies a predictive discrepancy.
The next necessary consequence is a range change large enough to matter.
This development screen uses a 0.2 mm correction threshold, one fifth of a
declared 1 mm follow-up error tolerance. A later study would require 95%
reliability and at least 20% lower squared-error risk than the strongest
eligible comparator at a 10,000-period acquisition budget. The present long
development fits do not evaluate that final requirement.

## Likelihood and the quantitative question

Write `lambda(phi)=a f(phi-tau)+b`. In age cell j, consider intensity
`g_j lambda(phi)`, using the complete recorded event history to define age.
Let `N_j` count events, `T_j` be time at risk, and
`B_j(tau)=integral_cell f(phi(t)-tau) dt`. Then

`ell = sum_events log(lambda(phi_i)) + sum_j N_j log(g_j)
       - sum_j g_j [a B_j(tau)+b T_j]`.

The event histories and exposures may be dependent. This is their intensity
likelihood, not an assumption that histogram cells are independent Poisson
samples. For fixed `(a,tau,b)`, the unconstrained nonnegative maximizing
factor is `g_j=N_j/[a B_j+b T_j]`. Zero event cells have maximizing factor
zero and zero profile contribution. Fix `g=1` after 205 ns to identify the
amplitude scale. This supplies a flexible, established profile-likelihood
comparator; profiling nuisance rates is not a novel statistical principle.

The hard-cutoff model is another instance of this likelihood. Its cutoff
supremum occurs at the smallest compatible gap (within the allowed interval),
because increasing the cutoff removes negative integrated intensity without
removing any event term until it crosses an observed gap. Guarded likelihood
keeps contributions only above a fixed age but retains every observation as
a history reset. It is a partial likelihood, not a simulated acquisition.

The earlier recovery residual changes range only through its projection onto
the range score after amplitude/background adjustment. Consequently compare
the actual fitted delays; a large count log-score improvement is insufficient.
Require a correction at least 0.2 mm, in a consistent direction in both halves
and both pulse-background conventions, relative to both native discrete joint
likelihood and continuous hard-cutoff likelihood before advancing this
correction as a route to the intended decision. The flexible and guarded
methods might already supply any useful correction; distinct method value
would still require comparison with them.

## Exact exposure integration and coordinate alignment

Let F be the calibrated pulse CDF on its compact support and let
`A(t)=floor(t/P)+F(t mod P)` be its periodic antiderivative. Each live segment
`[l,r]` contributes `A(r-tau)-A(l-tau)` to B. Reducing endpoints modulo P
leaves an integer number of full periods and a signed sum of CDF values.
Aggregate equal endpoint phases and use prefix sums outside the pulse support.
This changes computation, not the objective. The executable checks the full
compressed sum against direct interval antiderivatives, including wrapped
pulses. It also checks analytic likelihood gradients against differences.

Native and coarse discrete comparisons reconstruct the exact free-running
integer-bin exposures under the stated discrete model. A detection closes the
following D bins. The largest supported D is at most the minimum observed
index gap minus one. Count every active bin through the next detection bin,
including censoring at the fixed analysis boundary.

Use centered phase bins for comparison with the point-timestamp convention.
The upstream pulse-mass function integrates over left-edge bin coordinates,
so subtract half a bin from its delay to return to the centered convention.
Without this explicit origin conversion a nominal half-bin offset could be
mistaken for a recovery effect. The pulse's trimmed calibration origin is
arbitrary; differences in delay, not absolute target distance, are reported.

## Comparators and limits

The unmodified robust pilot and one-step functions, pulse model and likelihood
score come from the pinned MIT-licensed
[Jorgensen implementation](https://github.com/FredericJorgensen/dead-time-event-estimation/tree/d63dc5d8e2395ff1104a81946b989c4345d0baab).
Source byte hashes are checked before import. Joint likelihood uses SciPy
optimization with the same source score. The reader's centered coordinates,
supported cutoff fit and optimization backend are explicit adaptations; this
is not a reproduction claim for the authors' complete published experiment.
Three nearby starts are numerical safeguards, not a proof of a global optimum.
Solver status, score residuals and individual solutions are retained.

The low-flux fit uses a provisional 150 ns guard. Its validity needs a bound
on electronics dead time plus any hidden detector recovery; no such bound is
certified here. This fit is a separate physical observation, not established
ground truth. The two pulse backgrounds are sensitivity choices, not a
calibration confidence set. Point-timestamp likelihood and binned likelihood
have different quantization assumptions. Recovery, pulse drift, timewalk,
additive afterpulsing and recording completeness remain physical questions.

All outcomes beyond the existing first-million-frame prefixes stay reserved.
No Lean certification, physical coverage guarantee or practical superiority
is inferred from a fitted delay difference alone.

Remaining to-do list: establish a consequential and comparative range benefit,
validate observation/calibration assumptions, then confirm it on the reserve.
