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
The separately selectable proper-time consequence retains its prose scope status.
-/
