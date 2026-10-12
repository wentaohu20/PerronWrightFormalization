import PerronWright.Probability.BrownianEntranceAreaOrderedIntegral
import PerronWright.Probability.BrownianEntranceProductLaplace

/-! # The genuine entrance-area duration Laplace integral

The actual area time cube is sorted, then duration and internal times
are changed to positive gaps. The literal density normalization cancels
before genuine edgewise Tonelli and Laplace evaluation. No area-duration
transform identity is an input.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianEntranceAreaDurationLaplace

open BrownianEntranceAreaOrderedIntegral BrownianAreaTimeSimplex BrownianAreaTimeGaps
open BrownianPositiveBridgeAreaMomentLimits BrownianPositiveBridgeAreaTimeMoments
open BrownianEntranceAreaGammaTransform BrownianEntranceProductGeometry
open BrownianEntranceProductLaplace PositiveTimeConvolutionLaplace
open BrownianKilledFiniteDimensionalDensityCoordinates

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

def heatLaplaceWeight (p T : ℝ) : ℝ≥0∞ :=
  laplaceWeight p T*ENNReal.ofReal (boundaryHeatCoefficient (Real.toNNReal T))

theorem measurable_heatLaplaceWeight (p : ℝ) : Measurable (heatLaplaceWeight p) := by
  have hG : Measurable (fun T : ℝ ↦ gaussianPDFReal 0 (Real.toNNReal T) 0) :=
    measurable_uncurry_gaussianPDFReal.comp
      (measurable_const.prodMk (measurable_id.real_toNNReal.prodMk measurable_const))
  exact (measurable_laplaceWeight p).mul
    (((measurable_const.div measurable_id.real_toNNReal.coe_nnreal_real).mul hG).ennreal_ofReal)

theorem heatLaplaceWeight_ne_top (p T : ℝ) : heatLaplaceWeight p T ≠ ∞ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem actual_entrance_duration_laplace (n : ℕ) (p : ℝ) (hp : 0 < p) :
    (∫⁻ T : ℝ in Ioi 0, heatLaplaceWeight p T*entranceAreaMoment (Real.toNNReal T) (n+1)) =
      ((n+1).factorial : ℝ≥0∞)*∫⁻ v : FreeVector (n+1),
        transformedNumerator n p v*heightWeight n v := by
  let F : (ℝ × (Fin (n+1) → ℝ)) → ℝ≥0∞ := fun q ↦
    heatLaplaceWeight p q.1*plainMoment n q
  have hF : Measurable F :=
    ((measurable_heatLaplaceWeight p).comp measurable_fst).mul (measurable_plainMoment n)
  have htime (T : ℝ) :
      heatLaplaceWeight p T*entranceAreaMoment (Real.toNNReal T) (n+1) =
        ((n+1).factorial : ℝ≥0∞)*∫⁻ τ : Fin (n+1) → ℝ,
          {r | StrictMono r}.indicator (fun r ↦ F (T,r)) τ ∂timeCube (Real.toNNReal T) (n+1) := by
    rw [entranceAreaMoment_eq_factorial_ordered]
    have hnn (r : Fin (n+1) → ℝ) :
        plainMoment n ((Real.toNNReal T : ℝ),r) = plainMoment n (T,r) := by
      simp only [plainMoment,plainGaps,Real.toNNReal_coe]
    simp_rw [hnn]
    calc
      _ = ((n+1).factorial : ℝ≥0∞)*(heatLaplaceWeight p T*
          ∫⁻ τ : Fin (n+1) → ℝ, {r | StrictMono r}.indicator
            (fun r ↦ plainMoment n (T,r)) τ ∂timeCube (Real.toNNReal T) (n+1)) := by ac_rfl
      _ = _ := by
        congr 1
        rw [← lintegral_const_mul' _
          (fun τ : Fin (n+1) → ℝ ↦ {r | StrictMono r}.indicator (fun r ↦ plainMoment n (T,r)) τ)
          (heatLaplaceWeight_ne_top p T)]
        apply lintegral_congr
        intro τ
        by_cases hτ : StrictMono τ
        · simp only [indicator_of_mem (show τ ∈ {r | StrictMono r} from hτ),F]
        · simp only [indicator_of_notMem (show τ ∉ {r | StrictMono r} from hτ),mul_zero]
  calc
    _ = ∫⁻ T : ℝ in Ioi 0, ((n+1).factorial : ℝ≥0∞)*
        ∫⁻ τ : Fin (n+1) → ℝ, {r | StrictMono r}.indicator (fun r ↦ F (T,r)) τ
          ∂timeCube (Real.toNNReal T) (n+1) := lintegral_congr htime
    _ = ((n+1).factorial : ℝ≥0∞)*∫⁻ T : ℝ in Ioi 0,
        ∫⁻ τ : Fin (n+1) → ℝ, {r | StrictMono r}.indicator (fun r ↦ F (T,r)) τ
          ∂timeCube (Real.toNNReal T) (n+1) :=
      lintegral_const_mul' _ _ (by finiteness)
    _ = ((n+1).factorial : ℝ≥0∞)*∫⁻ σ : Fin (n+2) → ℝ in positiveGaps (n+2),
        F (∑ i, σ i,Fin.init (cumulativeTimes (n+2) σ)) := by
      congr 1
      exact lintegral_duration_timeCube_eq_positive_gaps (n+1) F hF
    _ = ((n+1).factorial : ℝ≥0∞)*∫⁻ σ : Fin (n+2) → ℝ in positiveGaps (n+2),
        laplaceWeight p (∑ i, σ i)*(∫⁻ v, rawNumerator n σ v*heightWeight n v) := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_positiveGaps (n+2))] with σ hσ
      dsimp only [F,heatLaplaceWeight]
      rw [mul_assoc,normalization_plainMoment_positive_gaps n σ hσ]
    _ = _ := by rw [weighted_rawNumerator_laplace n p hp (measurable_heightWeight n)]

theorem ofReal_boundaryMomentIntegrand (n : ℕ) (p T : ℝ) (hT : 0 < T) :
    ENNReal.ofReal (boundaryMomentIntegrand (n+1) p T) =
      heatLaplaceWeight p T*entranceAreaMoment (Real.toNNReal T) (n+1) := by
  have hβ : 0 ≤ boundaryHeatCoefficient (Real.toNNReal T) :=
    mul_nonneg (div_nonneg (by norm_num) (Real.toNNReal T).coe_nonneg)
      (gaussianPDFReal_nonneg _ _ _)
  unfold boundaryMomentIntegrand heatLaplaceWeight laplaceWeight
  rw [ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) hβ),
    ENNReal.ofReal_mul (Real.exp_nonneg _),
    ENNReal.ofReal_toReal (entranceAreaMoment_lt_top _ (Real.toNNReal_pos.mpr hT) _).ne]

end PerronWright.BrownianEntranceAreaDurationLaplace
