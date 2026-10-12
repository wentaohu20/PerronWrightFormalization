import PerronWright.Probability.BrownianEntranceDurationScaling
import PerronWright.Probability.BrownianPositiveBridgeAreaLawIdentification
import PerronWright.Probability.BrownianPositiveBridgeAreaScaling

/-! # The actual entrance area law has duration power three-halves

The area is the existing literal path integral. Its genuine probability
law and arbitrary Borel test scaling follow from the proved whole-path
law scaling. Integrability is transported exactly; nonnegative Laplace
tests are integrable by the actual nonnegative path support. No positive
exponential-moment or Wright-area identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceAreaScaling

open BrownianPathLaw BrownianPathDilationLaw BrownianBridgeCyclicArea
open BrownianEntranceContinuousRealization BrownianEntranceDurationScaling
open BrownianPositiveBridgeAreaScaling
open BrownianPositiveBridgeAreaLawIdentification

theorem areaLaw_duration_scaling (T : ℝ≥0) (hT : 0 < T) :
    entranceAreaLaw T hT = (entranceAreaLaw 1 zero_lt_one).map (fun A ↦ (T : ℝ)^(3/2 : ℝ)*A) := by
  unfold entranceAreaLaw
  rw [pathLaw_duration_scaling T hT,
    Measure.map_map (measurable_pathArea T) (measurable_brownianDilation T),
    Measure.map_map (by fun_prop) (measurable_pathArea 1)]
  congr 1
  exact funext (pathArea_brownianDilation T hT)

theorem lintegral_area_duration_scaling (T : ℝ≥0) (hT : 0 < T)
    (Φ : ℝ → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ f, Φ (pathArea T f) ∂pathLaw T hT) =
      ∫⁻ f, Φ ((T : ℝ)^(3/2 : ℝ)*pathArea 1 f) ∂pathLaw 1 zero_lt_one := by
  rw [lintegral_duration_scaling T hT (fun f ↦ Φ (pathArea T f))
    (hΦ.comp (measurable_pathArea T))]
  exact lintegral_congr (fun f ↦ by rw [pathArea_brownianDilation T hT])

theorem integrable_area_duration_scaling_iff (T : ℝ≥0) (hT : 0 < T)
    (Φ : ℝ → ℝ) (hΦ : Measurable Φ) :
    Integrable (fun f ↦ Φ (pathArea T f)) (pathLaw T hT) ↔
      Integrable (fun f ↦ Φ ((T : ℝ)^(3/2 : ℝ)*pathArea 1 f)) (pathLaw 1 zero_lt_one) := by
  rw [integrable_duration_scaling_iff T hT (fun f ↦ Φ (pathArea T f))
    (hΦ.comp (measurable_pathArea T))]
  simp only [pathArea_brownianDilation T hT]

theorem integral_area_duration_scaling (T : ℝ≥0) (hT : 0 < T)
    (Φ : ℝ → ℝ) (hΦ : Measurable Φ) :
    (∫ f, Φ (pathArea T f) ∂pathLaw T hT) =
      ∫ f, Φ ((T : ℝ)^(3/2 : ℝ)*pathArea 1 f) ∂pathLaw 1 zero_lt_one := by
  rw [integral_duration_scaling T hT (fun f ↦ Φ (pathArea T f))
    (hΦ.comp (measurable_pathArea T))]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro f
  change Φ (pathArea T (brownianDilation T f)) = Φ ((T : ℝ)^(3/2 : ℝ)*pathArea 1 f)
  rw [pathArea_brownianDilation T hT]

theorem ae_pathArea_nonnegative (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw T hT, 0 ≤ pathArea T f := ae_entrance_pathArea_nonneg T hT

theorem ae_areaLaw_nonnegative (T : ℝ≥0) (hT : 0 < T) : ∀ᵐ A ∂entranceAreaLaw T hT, 0 ≤ A :=
  (ae_map_iff (measurable_pathArea T).aemeasurable measurableSet_Ici).mpr (ae_pathArea_nonnegative T hT)

theorem lintegral_abs_area_pow_duration_scaling (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫⁻ f, ENNReal.ofReal (|pathArea T f|^n) ∂pathLaw T hT) =
      ENNReal.ofReal (((T : ℝ)^(3/2 : ℝ))^n) *
        ∫⁻ f, ENNReal.ofReal (|pathArea 1 f|^n) ∂pathLaw 1 zero_lt_one := by
  rw [lintegral_area_duration_scaling T hT (fun A : ℝ ↦ ENNReal.ofReal (|A|^n)) (by fun_prop)]
  calc
    _ = ∫⁻ f, ENNReal.ofReal (((T : ℝ)^(3/2 : ℝ))^n)*ENNReal.ofReal (|pathArea 1 f|^n)
        ∂pathLaw 1 zero_lt_one := by
      apply lintegral_congr
      intro f
      rw [abs_mul,mul_pow,ENNReal.ofReal_mul (by positivity)]
      congr 2
      congr 1
      exact abs_of_nonneg (by positivity)
    _ = _ := lintegral_const_mul _ (((measurable_pathArea 1).abs.pow_const n).ennreal_ofReal)

theorem integral_area_pow_duration_scaling (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ f, pathArea T f^n ∂pathLaw T hT) =
      ((T : ℝ)^(3/2 : ℝ))^n * ∫ f, pathArea 1 f^n ∂pathLaw 1 zero_lt_one := by
  rw [integral_area_duration_scaling T hT (fun A : ℝ ↦ A^n) (by fun_prop)]
  simp_rw [mul_pow]
  exact integral_const_mul _ _

theorem entranceAreaMoment_duration_scaling (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    BrownianPositiveBridgeAreaMomentLimits.entranceAreaMoment T n =
      ENNReal.ofReal (((T : ℝ)^(3/2 : ℝ))^n) *
        BrownianPositiveBridgeAreaMomentLimits.entranceAreaMoment 1 n := by
  rw [← entrance_abs_area_moment_eq_time_kernel_integral T hT n,
    lintegral_abs_area_pow_duration_scaling T hT n,
    entrance_abs_area_moment_eq_time_kernel_integral 1 zero_lt_one n]

theorem entranceAreaMoment_real_duration_scaling (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (BrownianPositiveBridgeAreaMomentLimits.entranceAreaMoment T n).toReal =
      ((T : ℝ)^(3/2 : ℝ))^n *
        (BrownianPositiveBridgeAreaMomentLimits.entranceAreaMoment 1 n).toReal := by
  rw [← entrance_area_real_moment_eq_time_kernel_integral T hT n,
    integral_area_pow_duration_scaling T hT n,
    entrance_area_real_moment_eq_time_kernel_integral 1 zero_lt_one n]

theorem integrable_area_pow_duration_scaling_iff (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    Integrable (fun f ↦ pathArea T f^n) (pathLaw T hT) ↔
      Integrable (fun f ↦ pathArea 1 f^n) (pathLaw 1 zero_lt_one) := by
  rw [integrable_area_duration_scaling_iff T hT (fun A : ℝ ↦ A^n) (by fun_prop)]
  simp_rw [mul_pow]
  exact integrable_const_mul_iff (IsUnit.mk0 _ (pow_ne_zero n (ne_of_gt (Real.rpow_pos_of_pos hT _)))) _

theorem integrable_exp_neg_area (T : ℝ≥0) (hT : 0 < T) (u : ℝ) (hu : 0 ≤ u) :
    Integrable (fun f ↦ Real.exp (-u*pathArea T f)) (pathLaw T hT) := by
  let := pathLaw_isProbability T hT
  apply (integrable_const (1 : ℝ)).mono'
    (((measurable_pathArea T).const_mul (-u)).exp.aestronglyMeasurable)
  filter_upwards [ae_pathArea_nonnegative T hT] with f hf
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) hf)

theorem lintegral_exp_neg_area_duration_scaling (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (∫⁻ f, ENNReal.ofReal (Real.exp (-u*pathArea T f)) ∂pathLaw T hT) =
      ∫⁻ f, ENNReal.ofReal (Real.exp (-(u*(T : ℝ)^(3/2 : ℝ))*pathArea 1 f))
        ∂pathLaw 1 zero_lt_one := by
  rw [lintegral_area_duration_scaling T hT (fun A : ℝ ↦ ENNReal.ofReal (Real.exp (-u*A))) (by fun_prop)]
  exact lintegral_congr (fun _ ↦ by congr 2; ring)

theorem integral_exp_neg_area_duration_scaling (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (∫ f, Real.exp (-u*pathArea T f) ∂pathLaw T hT) =
      ∫ f, Real.exp (-(u*(T : ℝ)^(3/2 : ℝ))*pathArea 1 f) ∂pathLaw 1 zero_lt_one := by
  rw [integral_area_duration_scaling T hT (fun A : ℝ ↦ Real.exp (-u*A)) (by fun_prop)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro f
  change Real.exp (-u*((T : ℝ)^(3/2 : ℝ)*pathArea 1 f)) =
    Real.exp (-(u*(T : ℝ)^(3/2 : ℝ))*pathArea 1 f)
  congr 1
  ring

end PerronWright.BrownianEntranceAreaScaling
