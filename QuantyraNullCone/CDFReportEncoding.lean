import QuantyraNullCone.CDFReport
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup

namespace QuantyraNullCone

/-- Decode a vertex permutation to zero-based vertex positions by exact list indexing.
    Clipping only makes the function total for rejected, non-permutation inputs. -/
def permutationPositions {n : ℕ} (hn : 0 < n) (permutation : Fin n → Fin n)
    (vertex : Fin n) : Fin n :=
  ⟨min (n - 1) ((List.ofFn permutation).idxOf vertex),
    lt_of_le_of_lt (min_le_left _ _) (Nat.sub_lt hn (by decide))⟩

theorem permutation_positions_inverse {n : ℕ} (hn : 0 < n)
    (permutation : Fin n → Fin n) (hPerm : Function.Injective permutation) (j : Fin n) :
    permutationPositions hn permutation (permutation j) = j := by
  have hNodup := List.nodup_ofFn.mpr hPerm
  have hIdx : (List.ofFn permutation).idxOf (permutation j) = j.val := by
    simpa using List.get_idxOf hNodup ⟨j.val, by simp⟩
  apply Fin.ext
  change min (n - 1) ((List.ofFn permutation).idxOf (permutation j)) = j.val
  rw [hIdx]
  apply min_eq_right
  exact Nat.le_sub_one_of_lt j.isLt

theorem permutation_positions_injective {n : ℕ} (hn : 0 < n)
    (permutation : Fin n → Fin n) (hPerm : Function.Injective permutation) :
    Function.Injective (permutationPositions hn permutation) := by
  have hSurj := Finite.surjective_of_injective hPerm
  intro u v hPos
  obtain ⟨i, rfl⟩ := hSurj u
  obtain ⟨j, rfl⟩ := hSurj v
  rw [permutation_positions_inverse hn permutation hPerm i,
    permutation_positions_inverse hn permutation hPerm j] at hPos
  exact congrArg permutation hPos

/-- The Python one-based rank loop agrees with the formal predecessor rank. -/
theorem permutation_rank_decode {n : ℕ} (hn : 0 < n)
    (permutation : Fin n → Fin n) (hPerm : Function.Injective permutation) (j : Fin n) :
    rank (fun u v => permutationPositions hn permutation u < permutationPositions hn permutation v)
      (permutation j) = j.val + 1 := by
  rw [rank_position_eq _ (permutation_positions_injective hn permutation hPerm),
    permutation_positions_inverse hn permutation hPerm]

/-- The integer cross-products used by Python corner_counts; no real arithmetic. -/
def reportCornerIndices {n : ℕ} (R : CDFReport n) (k p q : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => k * ((R.first i).val + 1) ≤ p * n ∧
    k * ((R.second i).val + 1) ≤ q * n)

def reportCornerCount {n : ℕ} (R : CDFReport n) (k p q : ℕ) : ℕ :=
  (reportCornerIndices R k p q).card

theorem normalized_position_corner_iff {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (position : Fin n) (p : ℕ) :
    ((position.val + 1 : ℝ) / n ≤ (p : ℝ) / k) ↔ k * (position.val + 1) ≤ p * n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_div_iff₀ hnR hkR]
  norm_cast
  rw [Nat.mul_comm]

/-- Inclusive runtime integer counts equal the actual all-threshold CDF at grid corners. -/
theorem CDFReport.corner_CDF {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (R : CDFReport n) (p q : ℕ) :
    R.cdf ((p : ℝ) / k) ((q : ℝ) / k) = (reportCornerCount R k p q : ℝ) / n := by
  have hSet : rectangleCount (fun i => ((R.first i).val + 1 : ℝ) / n)
      (fun i => ((R.second i).val + 1 : ℝ) / n) ((p : ℝ) / k) ((q : ℝ) / k) =
      reportCornerIndices R k p q := by
    ext i
    simp only [rectangleCount, reportCornerIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr (normalized_position_corner_iff hn hk (R.first i) p)
      (normalized_position_corner_iff hn hk (R.second i) q)
  change _ / (n : ℝ) = _
  rw [hSet]
  rfl

theorem CDFReport.corner_CDF_rational {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (R : CDFReport n) (p q : ℕ) :
    R.cdf ((p : ℝ) / k) ((q : ℝ) / k) = ((reportCornerCount R k p q : ℚ) / n : ℚ) := by
  simpa using R.corner_CDF hn hk p q

#print axioms permutation_positions_inverse
#print axioms permutation_rank_decode
#print axioms CDFReport.corner_CDF
#print axioms CDFReport.corner_CDF_rational

end QuantyraNullCone
