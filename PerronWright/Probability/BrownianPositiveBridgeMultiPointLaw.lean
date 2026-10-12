import PerronWright.Probability.BrownianPositiveBridgeMultiPointSource
import PerronWright.Probability.BrownianPositiveBridgeMultiPointOrthants

/-! # Full multi-point density of the actual conditioned positive bridge

This is an equality of actual probability measures. The Gaussian
entrance/internal/exit product is derived from the actual killed path
law and genuine pinned endpoint disintegration, without a bridge Markov
or positive-excursion identity assumption.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeMultiPointLaw

open BrownianPathLaw BrownianKilledFiniteDimensionalCoordinates
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalDensity
open BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeFiniteDimensionalLaw BrownianPositiveBridgeMultiPointCoordinates
open BrownianPositiveBridgeMultiPointSource BrownianPositiveBridgeMultiPointOrthants

theorem measurable_lastExit (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0) :
    Measurable (fun v : FreeVector n ↦ density (lastState n a v) (gaps n) a) := by
  have hp : Measurable (fun v : FreeVector n ↦ (lastState n a v,a)) :=
    (continuous_lastState n a).measurable.prodMk measurable_const
  simpa only [Function.comp_def] using (measurable_joint_density (gaps n)).comp hp

theorem exitIntegral_zero_eq_product (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hprev : ∀ j < n, 0 < gaps j) (cuts : FreeVector n) :
    exitIntegral n a gaps cuts 0 =
      ∫⁻ v in orthant n cuts, jointDensity n a gaps v*density (lastState n a v) (gaps n) a := by
  have hp : Measurable (fun x : ℝ ↦ (x,a)) := measurable_id.prodMk measurable_const
  have hm : Measurable (fun x : ℝ ↦ density x (gaps n) a) := by
    simpa only [Function.comp_def] using (measurable_joint_density (gaps n)).comp hp
  rw [exitIntegral,zero_add,exitHeadLaw,lintegral_map hm (continuous_lastState n a).measurable,
    headLaw,freeTupleLaw_eq_withDensity n a ha gaps hprev,
    setLIntegral_withDensity_eq_setLIntegral_mul volume (measurable_jointDensity n a gaps)
      (measurable_lastExit n a gaps) (measurableSet_orthant n cuts)]
  rfl

theorem multiDensity_orthant_integral (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hprev : ∀ j < n, 0 < gaps j) (cuts : FreeVector n) :
    (∫⁻ v in orthant n cuts, multiDensity n a gaps v) =
      (normalization a (sampleTime gaps (n+1)))⁻¹*exitIntegral n a gaps cuts 0/
        gaussianPDF 0 (sampleTime gaps (n+1)) 0 := by
  rw [exitIntegral_zero_eq_product n a ha gaps hprev cuts]
  simp only [multiDensity,div_eq_mul_inv]
  have hprod : Measurable (fun v : FreeVector n ↦ jointDensity n a gaps v*density (lastState n a v) (gaps n) a) :=
    (measurable_jointDensity n a gaps).mul (measurable_lastExit n a gaps)
  have hconst : Measurable (fun v : FreeVector n ↦ (normalization a (sampleTime gaps (n+1)))⁻¹*
      (jointDensity n a gaps v*density (lastState n a v) (gaps n) a)) := measurable_const.mul hprod
  calc
    _ = (∫⁻ v in orthant n cuts, (normalization a (sampleTime gaps (n+1)))⁻¹*
        (jointDensity n a gaps v*density (lastState n a v) (gaps n) a))*
          (gaussianPDF 0 (sampleTime gaps (n+1)) 0)⁻¹ := lintegral_mul_const _ hconst
    _ = _ := by rw [lintegral_const_mul _ hprod]

theorem multiPointLaw_eq_withDensity (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hprev : ∀ j < n, 0 < gaps j) (hgap : 0 < gaps n) :
    (positiveBridgeLaw a (sampleTime gaps (n+1))).map (internalEval n gaps) =
      volume.withDensity (multiDensity n a gaps) := by
  let : IsProbabilityMeasure (positiveBridgeLaw a (sampleTime gaps (n+1))) :=
    positiveBridgeLaw_isProbability a ha _ (finalTime_pos n gaps hgap)
  let μ := (positiveBridgeLaw a (sampleTime gaps (n+1))).map (internalEval n gaps)
  have : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (continuous_internalEval n gaps).measurable.aemeasurable
  apply measure_eq_of_orthants n μ
  intro cuts
  rw [Measure.map_apply (continuous_internalEval n gaps).measurable (measurableSet_orthant n cuts),
    positiveBridgeLaw_orthant n a ha gaps hgap cuts,withDensity_apply _ (measurableSet_orthant n cuts),
    multiDensity_orthant_integral n a ha gaps hprev cuts]

theorem multiPoint_lintegral (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hprev : ∀ j < n, 0 < gaps j) (hgap : 0 < gaps n)
    (Φ : FreeVector n → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ g, Φ (internalEval n gaps g) ∂positiveBridgeLaw a (sampleTime gaps (n+1))) =
      ∫⁻ v, multiDensity n a gaps v*Φ v := by
  rw [← lintegral_map hΦ (continuous_internalEval n gaps).measurable,
    multiPointLaw_eq_withDensity n a ha gaps hprev hgap,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_multiDensity n a gaps) hΦ]
  rfl

theorem multiDensity_integral_eq_one (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hprev : ∀ j < n, 0 < gaps j) (hgap : 0 < gaps n) :
    (∫⁻ v, multiDensity n a gaps v) = 1 := by
  let : IsProbabilityMeasure (positiveBridgeLaw a (sampleTime gaps (n+1))) :=
    positiveBridgeLaw_isProbability a ha _ (finalTime_pos n gaps hgap)
  simpa only [mul_one,lintegral_one,measure_univ] using
    (multiPoint_lintegral n a ha gaps hprev hgap (fun _ ↦ 1) measurable_const).symm

theorem multiDensity_eq_zero_of_nonpos_coordinate (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0)
    (v : FreeVector n) (i : Fin n) (hi : v i ≤ 0) : multiDensity n a gaps v = 0 := by
  simp only [multiDensity,jointDensity_eq_zero_of_nonpos_coordinate n a gaps v i hi,
    zero_mul,mul_zero,ENNReal.zero_div]

end PerronWright.BrownianPositiveBridgeMultiPointLaw
