import QuantyraNullCone.LorentzBoundary
import QuantyraNullCone.LorentzUnlabeled
import QuantyraNullCone.VolumeRateEmpty
import QuantyraNullCone.VolumeRateExperiment
import QuantyraNullCone.ConfoundingTesting
import QuantyraNullCone.ThinningStoppedCoverage
import QuantyraNullCone.ThinningLaplace
import QuantyraNullCone.ThinningMixedCoverage
import QuantyraNullCone.ThinningCoverage
import QuantyraNullCone.BinomialGeometry
import QuantyraNullCone.MarkedThinning
import QuantyraNullCone.MarkedVolume
import QuantyraNullCone.Realizer
import QuantyraNullCone.Grid
import QuantyraNullCone.Counts
import QuantyraNullCone.Bridges
import QuantyraNullCone.Cumulative
import QuantyraNullCone.Model
import QuantyraNullCone.Measures
import QuantyraNullCone.DensityCDF
import QuantyraNullCone.GridAccuracy
import QuantyraNullCone.Sampling
import QuantyraNullCone.Coordinates
import QuantyraNullCone.Concentration
import QuantyraNullCone.GoodSamples
import QuantyraNullCone.ProbabilityRate
import QuantyraNullCone.DensityInterpolation
import QuantyraNullCone.OrderSelector
import QuantyraNullCone.FiniteTV
import QuantyraNullCone.Transpose
import QuantyraNullCone.InverseRate
import QuantyraNullCone.Identifiability
import QuantyraNullCone.Exchangeability
import QuantyraNullCone.QuotientTV
import QuantyraNullCone.Unlabeled
import QuantyraNullCone.LogGridRate
import QuantyraNullCone.ImprovedInverse
import QuantyraNullCone.ProperTime
import QuantyraNullCone.FiniteFoundation
import QuantyraNullCone.FiniteFixtures
import QuantyraNullCone.DKWFiniteTail
import QuantyraNullCone.SplitCalibration
import QuantyraNullCone.CDFReportFixtures
import QuantyraNullCone.DensityFeasibility
import QuantyraNullCone.DensityReportFixtures
import QuantyraNullCone.LorentzIsometry
import QuantyraNullCone.DegreeProbability
import QuantyraNullCone.DegreeCellBias
import QuantyraNullCone.DegreeLaw
import QuantyraNullCone.LowerBound
import QuantyraNullCone.LogLowerBound

/-!
Quantyra finite-order reconstruction.

The selected theorem is specified in notes/lean-target.md.
The selected deterministic finite rank reconstruction theorem is proved in Bridges.
The coordinate/rank identity and deterministic cumulative sandwich are also proved.
The probability modules extend the original grid reconstruction rate.
The density interpolation module proves the original cubic coefficient/CDF bound.
The order-only selector and finite-law TV argument prove CDF orbit separation.
The original all-N coefficient inverse bound and all-law identifiability are proved
for both actual labeled directed-order laws and their unlabeled isomorphism classes.
Iid exchangeability and the exact labeled/unlabeled TV equivalence are proved.
The logarithmic-grid all-N inverse and actual absolutely continuous proper-time
comparison are proved, including one global orientation for every endpoint pair.
Finite-data forcing/rank, LP residual checking, rounding and conditional CDF
foundations and the sharp-DKW analytic likelihood barrier are proved. Finite-bin
likelihood, maximal and sharp counting-law tail bounds are proved separately;
continuous uniform and original-K marginal DKW, joint-grid failure and exact
rational split-calibration checker soundness are proved. The order-only CDF
report checker, integer corner/permutation encoding, measurable coverage and
deterministic radius-one fallback are proved. Actual cell mean restrictions,
all-point expansion and conditional rounded-histogram error are proved. The
executable LP matrix, rational density report checker and actual full-report
probability guarantee are connected under one shared density orientation.
The genuine 2+1 Lorentzian model includes actual Euclidean volume and chronology,
Cartesian smooth automorphisms, their derivatives and Jacobians, actual density
transport/class membership and equality of every finite directed order law.
The explicit conformal gauge has positive coordinate distance modulo spatial O(2),
while its metric is isometric to the flat metric. This is a coordinate gauge
obstruction, and does not prove new physical nonidentifiability or inverse rates.
S032 adds degree trimming, deep-point retention, shifted-cell count/error lemmas
and actual iid fixed-mass concentration. The full fourth-root upper guarantee
uses a single measurable estimator of actual unlabeled directed orders, including
the explicit mesh, full-square clamping and flat-output branches. Its actual-law
distance corollary follows from the same estimator. Lower-bound components
construct the original-K alternatives, exact quotient separation, one-point
Gaussian divergence and testing with arbitrary independent random seeds.
The actual iid product likelihood, squared divergence identity and data processing
to unlabeled order laws give the full finite lower risk. For n >= 16 every
measurable estimator, with arbitrary independent randomization, has strict error
above n^(-1/4)/6 with probability above 1/4 under an original-class density.
S036 closes the logarithmic gap in the same class: for n >= 2^64 every
eligible independently randomized estimator has strict error above
(log n/n)^(1/4)/8192 with probability at least 1/2 under some density.
The certified uniform 95% minimax radius is sandwiched between this lower
radius and min(1/2,650*(log n/n)^(1/4)), for every probability seed space.
-/
