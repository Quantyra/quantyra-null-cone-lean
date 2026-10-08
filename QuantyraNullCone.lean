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
executable LP matrix and full density report probability bridges remain open.
-/
