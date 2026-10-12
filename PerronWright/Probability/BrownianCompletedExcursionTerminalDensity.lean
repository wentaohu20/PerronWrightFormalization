import PerronWright.Probability.BrownianMinimumFutureReturnDensity
import PerronWright.Probability.BrownianEntranceKernelLaplace
import PerronWright.Probability.BrownianKilledFreeEntranceGeometry
import PerronWright.Probability.BrownianEntranceOrderedTimeLaw
import PerronWright.Probability.BrownianPositiveBridgeMultiPointOrderedLaw

/-! # Literal terminal hitting factor of the completed entrance excursion

The terminal factor is the actual first-passage density, not a Gaussian
endpoint density. The already proved source normalization and return density
make its entrance--killed--hitting chain exactly the genuine continuous
entrance excursion density times the lifetime density. Every height is
covered, including the zero-density nonpositive terminal heights.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedExcursionTerminalDensity

open BrownianKilledBoundaryEntrance BrownianFirstPassageDensityGeometry
open BrownianMinimumFutureReturnDensity BrownianEntranceKernelLaplace
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalOrderedTimes
open BrownianPositiveBridgeMultiPointEntrance BrownianKilledFreeEntranceGeometry
open BrownianEntranceFiniteDimensionalFamily BrownianEntranceOrderedTimeLaw
open BrownianPositiveBridgeMultiPointOrderedLaw

theorem entrance_eq_twice_passage_all_heights (t : ℝ≥0) (z : ℝ) :
    entrance t z = ENNReal.ofReal 2 * BrownianFirstPassageDensityGeometry.density z t := by
  by_cases hz : 0 < z
  · simpa only [Real.toNNReal_coe] using entrance_eq_twice_passage_density (t : ℝ) z hz
  · have hn : densityReal z (t : ℝ) ≤ 0 := by
      by_cases ht : 0 < t
      · rw [densityReal, indicator_of_mem (show (t : ℝ) ∈ Ioi (0 : ℝ) from ht)]
        exact mul_nonpos_of_nonpos_of_nonneg
          (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hz) (by positivity))
          (gaussianPDFReal_nonneg _ _ _)
      · rw [densityReal_eq_zero_of_nonpos z t (le_of_not_gt ht)]
    simp only [entrance, entranceReal,
      indicator_of_notMem (show z ∉ Ioi (0 : ℝ) from hz), ENNReal.ofReal_zero,
      BrownianFirstPassageDensityGeometry.density, ENNReal.ofReal_eq_zero.mpr hn, mul_zero]

theorem lifetime_normalization_real (T : ℝ≥0) (hT : 1 < T) :
    (2 / (T : ℝ)) * gaussianPDFReal 0 T 0 =
      2 * Real.sqrt (2 / Real.pi) * (1 / (2 * (T : ℝ) * Real.sqrt T)) := by
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have ht : (0 : ℝ) < T := lt_trans (by norm_num) hT
  have hs : Real.sqrt (2 / Real.pi) * Real.sqrt (2 * Real.pi * (T : ℝ)) =
      2 * Real.sqrt T := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / Real.pi)]
    have he : (2 / Real.pi) * (2 * Real.pi * (T : ℝ)) = 4 * (T : ℝ) := by
      field_simp
      ring
    rw [he, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hs0 : Real.sqrt (2 * Real.pi * (T : ℝ)) ≠ 0 := by positivity
  have ht0 : Real.sqrt (T : ℝ) ≠ 0 := by positivity
  simp only [gaussianPDFReal, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    neg_zero, zero_div, Real.exp_zero, mul_one]
  field_simp
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hs.symm

theorem lifetime_normalization (T : ℝ≥0) (hT : 1 < T) :
    ENNReal.ofReal ((2 / (T : ℝ)) * gaussianPDFReal 0 T 0) =
      returnDensity T * (ENNReal.ofReal 2 * ENNReal.ofReal (Real.sqrt (2 / Real.pi))) := by
  rw [lifetime_normalization_real T hT]
  simp only [returnDensity,
    indicator_of_mem (show (T : ℝ) ∈ Ioi (1 : ℝ) from hT)]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (2 / Real.pi)),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ac_rfl

theorem terminal_hitting_density_eq_lifetime_entrance (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hT : 1 < sampleTime gaps (n + 2)) (v : BrownianKilledFiniteDimensionalDensityCoordinates.FreeVector (n + 1)) :
    entranceJoint n gaps v * BrownianFirstPassageDensityGeometry.density (v (Fin.last n))
        (gaps (n + 1)) / ENNReal.ofReal (Real.sqrt (2 / Real.pi)) =
      returnDensity (sampleTime gaps (n + 2)) * entranceProduct n gaps v := by
  have hr0 : returnDensity (sampleTime gaps (n + 2)) ≠ 0 := by
    simp only [returnDensity, indicator_of_mem
      (show (sampleTime gaps (n + 2) : ℝ) ∈ Ioi (1 : ℝ) from hT)]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hrTop : returnDensity (sampleTime gaps (n + 2)) ≠ ∞ := ENNReal.ofReal_ne_top
  have htwo0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
  rw [entranceProduct_eq_factors n gaps (lt_trans (by norm_num) hT) v,
    entrance_eq_twice_passage_all_heights (gaps (n + 1)) (v (Fin.last n)),
    lifetime_normalization _ hT]
  change _ = returnDensity (sampleTime gaps (n + 2)) *
    (entranceJoint n gaps v * (ENNReal.ofReal 2 *
      BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) (gaps (n + 1))) /
        (returnDensity (sampleTime gaps (n + 2)) *
          (ENNReal.ofReal 2 * ENNReal.ofReal (Real.sqrt (2 / Real.pi)))))
  have hm (a b c : ℝ≥0∞) : a * (b / c) = a * b / c := by
    simp only [div_eq_mul_inv, mul_assoc]
  rw [hm]
  rw [show returnDensity (sampleTime gaps (n + 2)) *
      (entranceJoint n gaps v * (ENNReal.ofReal 2 *
        BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) (gaps (n + 1)))) =
      returnDensity (sampleTime gaps (n + 2)) *
        (ENNReal.ofReal 2 * (entranceJoint n gaps v *
          BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) (gaps (n + 1)))) by ac_rfl,
    ENNReal.mul_div_mul_left _ _ hr0 hrTop,
    ENNReal.mul_div_mul_left _ _ htwo0 ENNReal.ofReal_ne_top]

theorem ordered_terminal_hitting_lintegral (T : ℝ≥0) (hT : 1 < T) (n : ℕ)
    (times : Fin (n + 3) → ℝ≥0) (hs : StrictMono times) (hzero : times 0 = 0)
    (hfinal : times (Fin.last (n + 2)) = T)
    (H : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ v, (entranceJoint n (orderedGaps (n + 2) times) v *
      BrownianFirstPassageDensityGeometry.density (v (Fin.last n))
        (orderedGaps (n + 2) times (n + 1)) /
          ENNReal.ofReal (Real.sqrt (2 / Real.pi))) * H v) =
      returnDensity T * (∫⁻ f, H (orderedEval (n + 1) times f)
        ∂BrownianEntranceContinuousRealization.pathLaw T (lt_trans (by norm_num) hT)) := by
  have htime := sampleTime_orderedGaps (n + 2) times hs.monotone hzero (Fin.last (n + 2))
  simp only [Fin.val_last, hfinal] at htime
  have hm : Measurable (fun v : (Fin (n + 1) → ℝ) ↦
      entranceProduct n (orderedGaps (n + 2) times) v * H v) :=
    (measurable_entranceProduct n (orderedGaps (n + 2) times)).mul hH
  rw [pathLaw_ordered_entrance_lintegral T (lt_trans (by norm_num) hT) n times hs hzero hfinal H hH,
    ← lintegral_const_mul _ hm]
  apply lintegral_congr
  intro v
  rw [terminal_hitting_density_eq_lifetime_entrance n _ (by rwa [htime]) v, htime, mul_assoc]

end PerronWright.BrownianCompletedExcursionTerminalDensity
