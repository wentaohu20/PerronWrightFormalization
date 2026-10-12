import PerronWright.Probability.BrownianKilledFiniteDimensionalDensity
import PerronWright.Probability.BrownianPositiveBridgeFiniteDimensionalDensity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! # Pointwise convolution of the genuine absorbing Brownian density

The actual deterministic-time killed semigroup first identifies the
Lebesgue density almost everywhere. Continuity of the actual last-kernel
integral upgrades that identity to every exit point. No convolution or
Markov identity is supplied as an assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledDensityConvolution

open BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel
open BrownianPositiveBridgeFiniteDimensionalDensity
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalLaw
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalDensity
open BrownianPathLaw ContinuousPathFirstPassage

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

theorem law_eq_withDensity_last_integral (a : ℝ) (s t : ℝ≥0) (ht : 0 < t) :
    law a (s+t) = volume.withDensity (fun y ↦ ∫⁻ x, density x t y ∂law a s) := by
  have hF : Measurable (fun y : ℝ ↦ ∫⁻ x, density x t y ∂law a s) :=
    (measurable_joint_density t).lintegral_prod_left'
  ext B hB
  rw [law_composition a s t hB,withDensity_apply _ hB]
  simp_rw [law_eq_withDensity_all _ t ht,withDensity_apply _ hB]
  exact lintegral_lintegral_swap (measurable_joint_density t).aemeasurable

theorem density_last_integral (a : ℝ) (s t : ℝ≥0) (ht : 0 < t) (y : ℝ) :
    (∫⁻ x, density x t y ∂law a s) = density a (s+t) y := by
  have hT : 0 < s+t := ht.trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s))
  have hF : Continuous (fun y : ℝ ↦ ∫⁻ x, density x t y ∂law a s) := by
    simpa only [add_zero] using continuous_last_kernel_integral (law a s) t ht 0
  have he : (fun y : ℝ ↦ ∫⁻ x, density x t y ∂law a s) =ᵐ[volume] density a (s+t) := by
    apply (withDensity_eq_iff_of_sigmaFinite hF.measurable.aemeasurable
      (measurable_density a (s+t)).aemeasurable).mp
    rw [← law_eq_withDensity_last_integral a s t ht,law_eq_withDensity_all a (s+t) hT]
  exact congrFun (Measure.eq_of_ae_eq he hF (continuous_density_exit a (s+t))) y

theorem density_convolution (a : ℝ) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) (y : ℝ) :
    (∫⁻ x, density a s x*density x t y) = density a (s+t) y := by
  have hm : Measurable (fun x : ℝ ↦ density x t y) := by
    simpa only [Function.comp_def,id_eq] using
      (measurable_joint_density t).comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ ↦ y)))
  rw [← density_last_integral a s t ht y,law_eq_withDensity_all a s hs,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_density a s) hm]
  rfl

theorem freeTupleLaw_last_marginal (a : ℝ) (gaps : ℕ → ℝ≥0) (n : ℕ) :
    (freeTupleLaw a gaps n).map (lastState n a) = law a (sampleTime gaps n) := by
  rw [freeTupleLaw,Measure.map_map (continuous_lastState n a).measurable
    (continuous_dropInitial n).measurable]
  have hm : (actualTupleLaw 0 a gaps n).map (lastState n a ∘ dropInitial n) =
      (actualTupleLaw 0 a gaps n).map (fun v ↦ v (Fin.last n)) := by
    apply Measure.map_congr
    rw [actualTupleLaw_eq_chainLaw]
    filter_upwards [chainLaw_initial_ae a gaps n] with v hv
    exact lastState_dropInitial n a v hv
  rw [hm,actualTupleLaw,zero_sub,Measure.map_map (measurable_pi_apply _)
    (continuous_endpointTuple n a gaps).measurable,law]
  congr 1
  funext f
  simp only [Function.comp_def,endpointTuple,Fin.val_last,add_comm]

theorem jointDensity_exit_integral (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+1, 0 < gaps j) (y : ℝ) :
    (∫⁻ v : FreeVector n, jointDensity n a gaps v*density (lastState n a v) (gaps n) y) =
      density a (sampleTime gaps (n+1)) y := by
  have he : Measurable (fun x : ℝ ↦ density x (gaps n) y) := by
    simpa only [Function.comp_def,id_eq] using (measurable_joint_density (gaps n)).comp
      (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ ↦ y)))
  have hv : Measurable (fun v : FreeVector n ↦ density (lastState n a v) (gaps n) y) := by
    simpa only [Function.comp_def] using he.comp (continuous_lastState n a).measurable
  calc
    _ = ∫⁻ v, density (lastState n a v) (gaps n) y ∂volume.withDensity (jointDensity n a gaps) := by
      simpa only [Pi.mul_apply] using
        (lintegral_withDensity_eq_lintegral_mul volume (measurable_jointDensity n a gaps) hv).symm
    _ = ∫⁻ v, density (lastState n a v) (gaps n) y ∂freeTupleLaw a gaps n := by
      rw [freeTupleLaw_eq_withDensity n a ha gaps (fun j hj ↦ hgaps j (Nat.lt_succ_of_lt hj))]
    _ = ∫⁻ x, density x (gaps n) y ∂law a (sampleTime gaps n) := by
      rw [← freeTupleLaw_last_marginal a gaps n,lintegral_map he (continuous_lastState n a).measurable]
    _ = _ := by rw [density_last_integral a _ _ (hgaps n (Nat.lt_succ_self n)),sampleTime_succ]

theorem jointDensity_exit_integral_ne_top (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+1, 0 < gaps j) (y : ℝ) :
    (∫⁻ v : FreeVector n, jointDensity n a gaps v*density (lastState n a v) (gaps n) y) ≠ ∞ := by
  rw [jointDensity_exit_integral n a ha gaps hgaps y]
  exact ENNReal.ofReal_ne_top

end PerronWright.BrownianKilledDensityConvolution
