import PerronWright.Probability.BrownianSurvivalEntranceScaling
import PerronWright.Probability.BrownianEntranceKernelLaplace
import PerronWright.Probability.BrownianMinimumWindowSurvivalBounds

/-! # Actual unit-duration free entrance mass

The entrance mass is computed from the genuine first-passage level
integral. Every ordered tuple has the same mass by uniqueness of the
actual surviving Brownian constant-test limit, not by a mass premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFreeEntranceUnitMass

open BrownianPathLaw ContinuousPathFirstPassage BrownianKilledBoundaryEntrance
open BrownianKilledFreeEntranceTests BrownianSurvivalEntranceScaling
open BrownianKilledFiniteDimensionalOrderedTimes BrownianKilledFiniteDimensionalDensityCoordinates

theorem lintegral_unit_entrance_mass :
    (∫⁻ y : ℝ, entrance 1 y) = ENNReal.ofReal (Real.sqrt (2/Real.pi)) := by
  calc
    _ = ∫⁻ y in Ioi (0 : ℝ), entrance 1 y := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro y
      by_cases hy : 0 < y
      · exact (indicator_of_mem hy _).symm
      · simp only [entrance,entranceReal,Set.indicator,mem_Ioi,hy,if_false,ENNReal.ofReal_zero]
    _ = ENNReal.ofReal 2*(∫⁻ y in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density y 1) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      simpa only [Real.toNNReal_one] using
        BrownianEntranceKernelLaplace.entrance_eq_twice_passage_density 1 y hy
    _ = _ := by
      rw [BrownianMinimumWindowSurvivalBounds.passage_level_mass 1 zero_lt_one,
        Real.sqrt_one,mul_one,← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have h2 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
      have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
      field_simp
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem freeEntranceLaw_unit_mass (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hzero : times 0 = 0)
    (hlast : times (Fin.last (n+1)) = 1) :
    freeEntranceLaw n (orderedGaps (n+1) times) univ =
      ENNReal.ofReal (Real.sqrt (2/Real.pi)) := by
  have ht := actual_relative_ordered_test_tendsto n times hstrict hzero 1 zero_lt_one
    (BoundedContinuousFunction.const _ (1 : ℝ)) (fun _ ↦ zero_le_one)
  simp only [BoundedContinuousFunction.const_apply',ENNReal.ofReal_one,lintegral_const,
    Measure.restrict_apply_univ,mul_one,NNReal.coe_one,Real.sqrt_one,inv_one,one_mul,hlast] at ht
  have hm := BrownianKilledGlobalEntranceTests.normalized_survival_path_mass_tendsto 1 zero_lt_one
  rw [lintegral_unit_entrance_mass] at hm
  exact tendsto_nhds_unique ht hm

end PerronWright.BrownianFreeEntranceUnitMass
