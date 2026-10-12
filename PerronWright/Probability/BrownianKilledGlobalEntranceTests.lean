import PerronWright.Probability.BrownianPositiveBridgeGaussianBounds

/-! # Genuine killed boundary limits for global bounded continuous tests

A small positive starting point admits one integrable Gaussian envelope
on the whole positive half-line. Thus the actual killed endpoint laws,
divided by their starting point, converge against global bounded
continuous tests, including tests depending continuously on the start.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledGlobalEntranceTests

open BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance
open BrownianPositiveBridgeGaussianBounds

theorem integrable_envelopeReal (δ T : ℝ≥0) (hT : 0 < T) :
    Integrable (envelopeReal δ T) := by
  have hb : 0 < (4*(T : ℝ))⁻¹ := by positivity
  have hi := (integrable_mul_exp_neg_mul_sq hb).norm.const_mul (envelopeCoefficient δ)
  apply hi.mono' (measurable_envelopeReal δ T).aestronglyMeasurable
  apply Eventually.of_forall
  intro y
  rw [Real.norm_eq_abs,abs_of_nonneg (envelopeReal_nonneg δ T y)]
  unfold envelopeReal
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  have he : -(4*(T : ℝ))⁻¹*y^2 = -y^2/(4*(T : ℝ)) := by ring
  simp only [he,mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (max_le (le_abs_self y) (abs_nonneg y)) (Real.exp_pos _).le)
      (envelopeCoefficient_nonneg δ)

theorem normalized_law_real_test_eq_density (a : ℝ) (ha : 0 < a)
    (T : ℝ≥0) (hT : 0 < T) (G : ℝ → ℝ) :
    (∫ y, G y ∂law a T)/a = ∫ y, densityReal a T y/a*G y := by
  rw [law_eq_withDensity a ha T hT,
    integral_withDensity_eq_integral_toReal_smul (measurable_density a T)
      (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [density,ENNReal.toReal_ofReal (densityReal_nonneg a ha T hT _),smul_eq_mul]
  rw [div_eq_mul_inv,← integral_mul_const]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y ↦ by ring)

theorem normalized_law_bounded_continuous_test_tendsto (T : ℝ≥0) (hT : 0 < T)
    (G : (ℝ × ℝ) →ᵇ ℝ) :
    Tendsto (fun a : ℝ ↦ (∫ y, G (a,y) ∂law a T)/a) (𝓝[>] 0)
      (𝓝 (∫ y, entranceReal T y*G (0,y))) := by
  have hm (a : ℝ) : AEStronglyMeasurable
      (fun y : ℝ ↦ densityReal a T y/a*G (a,y)) volume :=
    (((measurable_densityReal a T).div_const a).mul
      (G.continuous.measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  have hb : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ᵐ y : ℝ,
      ‖densityReal a T y/a*G (a,y)‖ ≤ envelopeReal T T y*‖G‖ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with a ha ha1
    exact Eventually.of_forall (fun y ↦ by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg
        (div_nonneg (densityReal_nonneg a ha T hT y) ha.le)]
      exact mul_le_mul (densityReal_div_start_le_envelope a ha ha1.le T T T hT le_rfl le_rfl y)
        (G.norm_coe_le_norm _) (norm_nonneg _) (envelopeReal_nonneg T T y))
  have hi := (integrable_envelopeReal T T hT).mul_const ‖G‖
  have hl : ∀ᵐ y : ℝ, Tendsto (fun a : ℝ ↦ densityReal a T y/a*G (a,y))
      (𝓝[>] 0) (𝓝 (entranceReal T y*G (0,y))) := Eventually.of_forall (fun y ↦
    (densityReal_div_start_tendsto T hT y).mul (G.continuous.tendsto _ |>.comp
      (tendsto_id.mono_left nhdsWithin_le_nhds |>.prodMk_nhds tendsto_const_nhds)))
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun y ↦ envelopeReal T T y*‖G‖) (Eventually.of_forall hm) hb hi hl
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (normalized_law_real_test_eq_density a ha T hT (fun y ↦ G (a,y))).symm

theorem integrable_entranceReal (T : ℝ≥0) (hT : 0 < T) : Integrable (entranceReal T) := by
  apply (integrable_envelopeReal T T hT).mono' (measurable_entranceReal T).aestronglyMeasurable
  apply Eventually.of_forall
  intro y
  rw [Real.norm_eq_abs,abs_of_nonneg (entranceReal_nonneg T y)]
  apply le_of_tendsto (densityReal_div_start_tendsto T hT y)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with a ha ha1
  exact densityReal_div_start_le_envelope a ha ha1.le T T T hT le_rfl le_rfl y

theorem lintegral_entrance_ne_top (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ y, entrance T y) ≠ ∞ := by
  unfold entrance
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_entranceReal T hT)
    (Eventually.of_forall (entranceReal_nonneg T))]
  exact ENNReal.ofReal_ne_top

theorem normalized_survival_mass_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun a : ℝ ↦ law a T univ/ENNReal.ofReal a) (𝓝[>] 0)
      (𝓝 (∫⁻ y, entrance T y)) := by
  have h := normalized_law_bounded_continuous_test_tendsto T hT
    (BoundedContinuousFunction.const (ℝ × ℝ) (1 : ℝ))
  simp only [BoundedContinuousFunction.const_apply',integral_const,smul_eq_mul,mul_one] at h
  have he : ENNReal.ofReal (∫ y, entranceReal T y) = ∫⁻ y, entrance T y :=
    ofReal_integral_eq_lintegral_ofReal (integrable_entranceReal T hT)
      (Eventually.of_forall (entranceReal_nonneg T))
  have ht := ENNReal.tendsto_ofReal h
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [ENNReal.ofReal_div_of_pos ha,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem normalized_survival_path_mass_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun a : ℝ ↦ BrownianPathLaw.pathLaw (ContinuousPathFirstPassage.survival (-a) T)/
      ENNReal.ofReal a) (𝓝[>] 0) (𝓝 (∫⁻ y, entrance T y)) := by
  apply (normalized_survival_mass_tendsto T hT).congr
  intro a
  have hm : Measurable (fun f : BrownianPathLaw.Path ↦ f T+a) :=
    ((BrownianPathLaw.continuous_eval T).add continuous_const).measurable
  rw [law,Measure.map_apply hm MeasurableSet.univ,preimage_univ,
    Measure.restrict_apply_univ]

end PerronWright.BrownianKilledGlobalEntranceTests
