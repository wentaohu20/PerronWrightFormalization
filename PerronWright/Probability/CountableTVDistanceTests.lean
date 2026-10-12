import PerronWright.Probability.CountableVariationTopology
import PerronWright.Probability.FiniteIrreducibleCountableMarkLocal

/-! # Bounded actual variation-distance component tests

The distance is that of the genuine atomic ell-one probability marks.
The finite sum identities apply to the actual component tuples, with no
compactness condition on the countable mark space.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section

namespace PerronWright.CountableVariationMarks

theorem dist_le_two (p q : VariationMark) : dist p q ≤ 2 := by
  calc
    dist p q = dist (encoding p) (encoding q) := (isometry_encoding.dist_eq p q).symm
    _ ≤ ‖encoding p‖ + ‖encoding q‖ := dist_le_norm_add_norm _ _
    _ = 2 := by rw [norm_encoding, norm_encoding]; norm_num

def distanceTest (p : VariationMark) : (Fin 1 → VariationMark) → ℝ :=
  fun ν ↦ dist (ν 0) p

theorem continuous_distanceTest (p : VariationMark) : Continuous (distanceTest p) :=
  (continuous_apply 0).dist continuous_const

@[simp] theorem distanceTest_self (p : VariationMark) : distanceTest p (fun _ ↦ p) = 0 :=
  dist_self p

theorem distanceTest_nonneg (p : VariationMark) (ν : Fin 1 → VariationMark) :
    0 ≤ distanceTest p ν := dist_nonneg

theorem distanceTest_le_two (p : VariationMark) (ν : Fin 1 → VariationMark) :
    distanceTest p ν ≤ 2 := dist_le_two _ _

end PerronWright.CountableVariationMarks

namespace PerronWright.CountableVariationComponentCounts

open CountableVariationMarks

theorem markedCount_distance_nonneg {n : ℕ} (x : Fin n → ℕ) (G : SimpleGraph (Fin n))
    (k r : Fin 1 → ℕ) (p : VariationMark) :
    0 ≤ markedCount x G k r (distanceTest p) := by
  exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)

theorem markedCount_distance_le_twice_count {n : ℕ} (x : Fin n → ℕ)
    (G : SimpleGraph (Fin n)) (k r : Fin 1 → ℕ) (p : VariationMark) :
    markedCount x G k r (distanceTest p) ≤ 2 * (ComponentCounts.count G k r : ℝ) := by
  calc
    markedCount x G k r (distanceTest p) ≤
        ∑ _c : ComponentCounts.GoodComponentTuples G k r, (2 : ℝ) :=
      Finset.sum_le_sum (fun _ _ ↦ dist_le_two _ _)
    _ = 2 * (ComponentCounts.count G k r : ℝ) := by
      simp [ComponentCounts.count, mul_comm]

theorem markedCount_distance_triangle {n : ℕ} (x : Fin n → ℕ)
    (G : SimpleGraph (Fin n)) (k r : Fin 1 → ℕ) (p q : VariationMark) :
    markedCount x G k r (distanceTest p) ≤
      markedCount x G k r (distanceTest q) +
        dist q p * (ComponentCounts.count G k r : ℝ) := by
  calc
    markedCount x G k r (distanceTest p) ≤
        ∑ c : ComponentCounts.GoodComponentTuples G k r,
          (distanceTest q (fun i ↦ ofProbability (EmpiricalTypeMarks.componentMark x (c.val i))) +
            dist q p) := Finset.sum_le_sum (fun _ _ ↦ dist_triangle _ _ _)
    _ = markedCount x G k r (distanceTest q) +
        dist q p * (ComponentCounts.count G k r : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp [markedCount, ComponentCounts.count, mul_comm]

end PerronWright.CountableVariationComponentCounts
