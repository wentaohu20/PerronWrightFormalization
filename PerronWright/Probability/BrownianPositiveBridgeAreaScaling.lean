import PerronWright.Probability.BrownianPositiveBridgeDilationLaw
import PerronWright.Probability.BrownianBridgeMinimumAreaDilation

/-! # Genuine positive-bridge area law and its exact duration scaling

The area is the literal integral of the actual conditioned positive path.
Its law, every nonnegative Borel test and the moment/Laplace scaling follow
from the proved whole-path dilation. No limiting excursion or Wright
moment identity is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeAreaScaling

open BrownianPathLaw BrownianPathDilationLaw BrownianBridgeCyclicArea
open BrownianPositiveBridgeConditioning BrownianPositiveBridgeDilationLaw
open BrownianBridgeMinimumAreaDilation

theorem pathArea_brownianDilation (T : ℝ≥0) (hT : 0 < T) (g : Path) :
    pathArea T (brownianDilation T g) = (T : ℝ)^(3/2 : ℝ)*pathArea 1 g := by
  rw [brownianDilation,pathArea_dilatePath T hT,duration_mul_sqrt_eq_rpow T hT]

def areaLaw (a : ℝ) (T : ℝ≥0) : Measure ℝ := (positiveBridgeLaw a T).map (pathArea T)

theorem areaLaw_isProbability (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    IsProbabilityMeasure (areaLaw a T) := by
  let := positiveBridgeLaw_isProbability a ha T hT
  exact Measure.isProbabilityMeasure_map (measurable_pathArea T).aemeasurable

theorem ae_pathArea_positive (a : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ g ∂positiveBridgeLaw a T, 0 < pathArea T g := by
  filter_upwards [ae_positiveBridgeLaw_strictly_positive a T] with g hg
  apply intervalIntegral.integral_pos (show (0 : ℝ) < T from hT)
    ((continuous_path g).comp continuous_real_toNNReal).continuousOn
  · intro r hr
    exact (hg (Real.toNNReal r) (Real.toNNReal_le_iff_le_coe.mpr hr.2)).le
  · refine ⟨(T : ℝ)/2,⟨by positivity,by linarith [show (0 : ℝ) < T from hT]⟩,?_⟩
    exact hg (Real.toNNReal ((T : ℝ)/2)) (Real.toNNReal_le_iff_le_coe.mpr (by linarith [T.property]))

theorem ae_areaLaw_positive (a : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ A ∂areaLaw a T, 0 < A := by
  exact (ae_map_iff (measurable_pathArea T).aemeasurable measurableSet_Ioi).mpr
    (ae_pathArea_positive a T hT)

theorem areaLaw_duration_scaling (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    areaLaw (Real.sqrt (T : ℝ)*a) T =
      (areaLaw a 1).map (fun A ↦ (T : ℝ)^(3/2 : ℝ)*A) := by
  unfold areaLaw
  rw [positiveBridgeLaw_duration_scaling T hT a,
    Measure.map_map (measurable_pathArea T) (measurable_brownianDilation T),
    Measure.map_map (by fun_prop) (measurable_pathArea 1)]
  congr 1
  funext g
  exact pathArea_brownianDilation T hT g

theorem lintegral_area_duration_scaling (T : ℝ≥0) (hT : 0 < T) (a : ℝ)
    (Φ : ℝ → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ g, Φ (pathArea T g) ∂positiveBridgeLaw (Real.sqrt (T : ℝ)*a) T) =
      ∫⁻ g, Φ ((T : ℝ)^(3/2 : ℝ)*pathArea 1 g) ∂positiveBridgeLaw a 1 := by
  rw [positiveBridgeLaw_duration_scaling T hT a,
    lintegral_map (f := fun g : Path ↦ Φ (pathArea T g))
      (hΦ.comp (measurable_pathArea T)) (measurable_brownianDilation T)]
  exact lintegral_congr (fun g ↦ by rw [pathArea_brownianDilation T hT])

theorem lintegral_abs_area_pow_duration_scaling (T : ℝ≥0) (hT : 0 < T) (a : ℝ) (n : ℕ) :
    (∫⁻ g, ENNReal.ofReal (|pathArea T g|^n) ∂positiveBridgeLaw (Real.sqrt (T : ℝ)*a) T) =
      ENNReal.ofReal (((T : ℝ)^(3/2 : ℝ))^n) *
        ∫⁻ g, ENNReal.ofReal (|pathArea 1 g|^n) ∂positiveBridgeLaw a 1 := by
  rw [lintegral_area_duration_scaling T hT a (fun A : ℝ ↦ ENNReal.ofReal (|A|^n)) (by fun_prop)]
  calc
    _ = ∫⁻ g, ENNReal.ofReal (((T : ℝ)^(3/2 : ℝ))^n)*ENNReal.ofReal (|pathArea 1 g|^n)
        ∂positiveBridgeLaw a 1 := by
      apply lintegral_congr
      intro g
      rw [abs_mul,mul_pow,ENNReal.ofReal_mul (by positivity)]
      congr 2
      congr 1
      exact abs_of_nonneg (by positivity)
    _ = _ := lintegral_const_mul _ (((measurable_pathArea 1).abs.pow_const n).ennreal_ofReal)

theorem integral_area_pow_duration_scaling (T : ℝ≥0) (hT : 0 < T) (a : ℝ) (n : ℕ) :
    (∫ g, pathArea T g^n ∂positiveBridgeLaw (Real.sqrt (T : ℝ)*a) T) =
      ((T : ℝ)^(3/2 : ℝ))^n * ∫ g, pathArea 1 g^n ∂positiveBridgeLaw a 1 := by
  rw [positiveBridgeLaw_duration_scaling T hT a,
    integral_map (measurable_brownianDilation T).aemeasurable
      ((measurable_pathArea T).pow_const n).aestronglyMeasurable]
  simp_rw [pathArea_brownianDilation T hT,mul_pow]
  exact integral_const_mul _ _

theorem lintegral_exp_neg_area_duration_scaling (T : ℝ≥0) (hT : 0 < T) (a u : ℝ) :
    (∫⁻ g, ENNReal.ofReal (Real.exp (-u*pathArea T g)) ∂positiveBridgeLaw (Real.sqrt (T : ℝ)*a) T) =
      ∫⁻ g, ENNReal.ofReal (Real.exp (-(u*(T : ℝ)^(3/2 : ℝ))*pathArea 1 g))
        ∂positiveBridgeLaw a 1 := by
  rw [lintegral_area_duration_scaling T hT a (fun A : ℝ ↦ ENNReal.ofReal (Real.exp (-u*A))) (by fun_prop)]
  apply lintegral_congr
  intro g
  congr 2
  ring

end PerronWright.BrownianPositiveBridgeAreaScaling
