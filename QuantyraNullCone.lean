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

/-!
Quantyra finite-order reconstruction.

The selected theorem is specified in notes/lean-target.md.
The selected deterministic finite rank reconstruction theorem is proved in Bridges.
The coordinate/rank identity and deterministic cumulative sandwich are also proved.
The probability modules extend the original grid reconstruction rate.
The density interpolation module proves the original cubic coefficient/CDF bound.
Observable-law separation and the all-N inverse assembly remain separate unfinished
stages of the full spacetime inverse theorem.
-/
