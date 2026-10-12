import PerronWright.Probability.BrownianKilledGlobalEntranceTests

/-! # Genuine global nonnegative killed entrance tests

This converts the proved real bounded continuous endpoint limits to the
nonnegative integral convention used by the actual minimum disintegration.
The conversion uses actual finite killed laws and proved entrance finite
mass, not an additional convergence premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledGlobalEntranceNonnegativeTests

open BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance
open BrownianKilledGlobalEntranceTests

theorem normalized_law_nonnegative_test_tendsto (T : ℝ≥0) (hT : 0 < T)
    (G : (ℝ × ℝ) →ᵇ ℝ) (hG : ∀ p, 0 ≤ G p) :
    Tendsto (fun a : ℝ ↦ (∫⁻ y, ENNReal.ofReal (G (a,y)) ∂law a T)/ENNReal.ofReal a)
      (𝓝[>] 0) (𝓝 (∫⁻ y, entrance T y*ENNReal.ofReal (G (0,y)))) := by
  have hm (a : ℝ) : Measurable (fun y : ℝ ↦ G (a,y)) :=
    G.continuous.measurable.comp (measurable_const.prodMk measurable_id)
  have hi (a : ℝ) : Integrable (fun y : ℝ ↦ G (a,y)) (law a T) :=
    (integrable_const ‖G‖).mono' (hm a).aestronglyMeasurable
      (Eventually.of_forall (fun _ ↦ G.norm_coe_le_norm _))
  have hientrance : Integrable (fun y : ℝ ↦ entranceReal T y*G (0,y)) :=
    (integrable_entranceReal T hT).mul_bdd (hm 0).aestronglyMeasurable
      (Eventually.of_forall (fun _ ↦ G.norm_coe_le_norm _))
  have he : ENNReal.ofReal (∫ y, entranceReal T y*G (0,y)) =
      ∫⁻ y, entrance T y*ENNReal.ofReal (G (0,y)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hientrance
      (Eventually.of_forall (fun y ↦ mul_nonneg (entranceReal_nonneg T y) (hG _)))]
    exact lintegral_congr (fun y ↦ ENNReal.ofReal_mul (entranceReal_nonneg T y))
  have ht := ENNReal.tendsto_ofReal (normalized_law_bounded_continuous_test_tendsto T hT G)
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [ENNReal.ofReal_div_of_pos ha,
    ofReal_integral_eq_lintegral_ofReal (hi a) (Eventually.of_forall (fun _ ↦ hG _))]

end PerronWright.BrownianKilledGlobalEntranceNonnegativeTests
