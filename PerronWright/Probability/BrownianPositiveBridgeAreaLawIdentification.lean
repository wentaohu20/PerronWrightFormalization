import PerronWright.Probability.WeakContinuousMomentIdentification
import PerronWright.Probability.BrownianPositiveBridgeAreaMomentLimits
import PerronWright.Probability.BrownianPositiveBridgeAreaMomentTails
import PerronWright.Probability.BrownianPositiveBridgePathConvergence
import PerronWright.Probability.BrownianPositiveBridgeAreaScaling
import PerronWright.Probability.ContinuousPathAreaContinuity

/-! # The literal time-kernel moments are genuine entrance-path area moments

Actual path weak convergence transfers bounded continuous truncations.
The genuine positive-bridge high moments control their remainder. This
identifies every kernel time-integral moment with the constructed continuous
entrance path's actual area law, and proves its finiteness and tail control.
No standard-excursion, Vervaat, or Wright identity is asserted.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeAreaLawIdentification

open BrownianPathLaw BrownianBridgeCyclicArea BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeAreaMomentBounds BrownianPositiveBridgeAreaMomentLimits
open BrownianPositiveBridgeAreaMomentTails BrownianPositiveBridgeWeakClusterSupport
open BrownianPositiveBridgePathConvergence ContinuousPathAreaContinuity
open WeakContinuousMomentIdentification

def entranceAreaLaw (T : ℝ≥0) (hT : 0 < T) : Measure ℝ :=
  (BrownianEntranceContinuousRealization.pathLaw T hT).map (pathArea T)

theorem entranceAreaLaw_isProbability (T : ℝ≥0) (hT : 0 < T) :
    IsProbabilityMeasure (entranceAreaLaw T hT) := by
  let := BrownianEntranceContinuousRealization.pathLaw_isProbability T hT
  exact Measure.isProbabilityMeasure_map (measurable_pathArea T).aemeasurable

theorem ae_entrance_pathArea_nonneg (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂BrownianEntranceContinuousRealization.pathLaw T hT, 0 ≤ pathArea T f := by
  let C : Set Path := {f | 0 ≤ pathArea T f}
  have hc : IsClosed C := isClosed_le continuous_const (continuous_pathArea T)
  have hm : ∀ᶠ a : ℝ in 𝓝[>] 0, (bridgeProbability T hT a : Measure Path) C = 1 := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [bridgeProbability_toMeasure T hT a ha]
    let := positiveBridgeLaw_isProbability a ha T hT
    apply (mem_ae_iff_prob_eq_one hc.measurableSet).mp
    change ∀ᵐ f ∂positiveBridgeLaw a T, 0 ≤ pathArea T f
    simpa only [pow_one] using ae_area_pow_nonneg a T 1
  have he := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    (tendsto_positiveBridgeProbability T hT) hc
  rw [Filter.limsup_congr hm,limsup_const] at he
  have hmass : (entranceProbability T hT : Measure Path) C = 1 := le_antisymm prob_le_one he
  let := BrownianEntranceContinuousRealization.pathLaw_isProbability T hT
  change C ∈ ae (BrownianEntranceContinuousRealization.pathLaw T hT)
  exact (mem_ae_iff_prob_eq_one hc.measurableSet).mpr hmass

theorem entrance_abs_area_moment_eq_time_kernel_integral (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    (∫⁻ f : Path, ENNReal.ofReal (|pathArea T f|^d)
      ∂BrownianEntranceContinuousRealization.pathLaw T hT) = entranceAreaMoment T d := by
  let h : Path → ℝ := fun f ↦ |pathArea T f|^d
  have hc : Continuous h := (continuous_pathArea T).abs.pow d
  have h0 : ∀ f, 0 ≤ h f := fun _ ↦ by dsimp [h]; positivity
  let C := (areaBound T (2*d)).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hsquare : ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ f, ENNReal.ofReal (h f^2) ∂(bridgeProbability T hT a : Measure Path)) ≤ ENNReal.ofReal C := by
    filter_upwards [self_mem_nhdsWithin,eventually_area_moment_bound T hT (2*d)] with a ha hb
    rw [bridgeProbability_toMeasure T hT a ha,ENNReal.ofReal_toReal (areaBound_lt_top T hT (2*d)).ne]
    simpa only [h,← pow_mul,Nat.mul_comm] using hb
  have hactual : Tendsto (fun a : ℝ ↦ ∫⁻ f, ENNReal.ofReal (h f)
      ∂(bridgeProbability T hT a : Measure Path)) (𝓝[>] 0) (𝓝 (entranceAreaMoment T d)) := by
    apply (actual_area_moment_tendsto T hT d).congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [bridgeProbability_toMeasure T hT a ha]
    apply lintegral_congr_ae
    filter_upwards [ae_area_pow_nonneg a T 1] with f hf
    simp only [pow_one] at hf
    simp only [h,abs_of_nonneg hf]
  exact target_lintegral_eq_of_square_bound_and_actual_limit (bridgeProbability T hT)
    (entranceProbability T hT) (tendsto_positiveBridgeProbability T hT) h hc h0 C hC hsquare
    (entranceAreaMoment T d) hactual

theorem entrance_abs_area_pow_integrable (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    Integrable (fun f : Path ↦ |pathArea T f|^d) (BrownianEntranceContinuousRealization.pathLaw T hT) := by
  refine ⟨((measurable_pathArea T).abs.pow_const d).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ ↦ by positivity))).mpr
  rw [entrance_abs_area_moment_eq_time_kernel_integral T hT d]
  exact entranceAreaMoment_lt_top T hT d

theorem entrance_area_moment_eq_time_kernel_integral (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    (∫⁻ f : Path, ENNReal.ofReal (pathArea T f^d)
      ∂BrownianEntranceContinuousRealization.pathLaw T hT) = entranceAreaMoment T d := by
  rw [← entrance_abs_area_moment_eq_time_kernel_integral T hT d]
  apply lintegral_congr_ae
  filter_upwards [ae_entrance_pathArea_nonneg T hT] with f hf
  rw [abs_of_nonneg hf]

theorem entrance_area_pow_integrable (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    Integrable (fun f : Path ↦ pathArea T f^d) (BrownianEntranceContinuousRealization.pathLaw T hT) := by
  apply (entrance_abs_area_pow_integrable T hT d).mono'
    ((measurable_pathArea T).pow_const d).aestronglyMeasurable
  exact ae_of_all _ (fun f ↦ by simp only [Real.norm_eq_abs,abs_pow,le_refl])

theorem entrance_area_real_moment_eq_time_kernel_integral (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    (∫ f : Path, pathArea T f^d ∂BrownianEntranceContinuousRealization.pathLaw T hT) =
      (entranceAreaMoment T d).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae
    ((ae_entrance_pathArea_nonneg T hT).mono (fun _ hf ↦ pow_nonneg hf d))
    ((measurable_pathArea T).pow_const d).aestronglyMeasurable,
    entrance_area_moment_eq_time_kernel_integral T hT d]

theorem entrance_areaLaw_moment_eq_time_kernel_integral (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    (∫⁻ A : ℝ, ENNReal.ofReal (A^d) ∂entranceAreaLaw T hT) = entranceAreaMoment T d := by
  rw [entranceAreaLaw,lintegral_map (by fun_prop) (measurable_pathArea T)]
  exact entrance_area_moment_eq_time_kernel_integral T hT d

theorem entrance_areaLaw_pow_integrable (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    Integrable (fun A : ℝ ↦ A^d) (entranceAreaLaw T hT) := by
  rw [entranceAreaLaw]
  exact (integrable_map_measure (by fun_prop) (measurable_pathArea T).aemeasurable).mpr
    (entrance_area_pow_integrable T hT d)

theorem entrance_areaLaw_real_moment_eq_time_kernel_integral (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    (∫ A : ℝ, A^d ∂entranceAreaLaw T hT) = (entranceAreaMoment T d).toReal := by
  rw [entranceAreaLaw,integral_map (measurable_pathArea T).aemeasurable (by fun_prop)]
  exact entrance_area_real_moment_eq_time_kernel_integral T hT d

def entranceAreaProbability (T : ℝ≥0) (hT : 0 < T) : ProbabilityMeasure ℝ :=
  (entranceProbability T hT).map (measurable_pathArea T).aemeasurable

def sourceAreaProbability (T : ℝ≥0) (hT : 0 < T) (a : ℝ) : ProbabilityMeasure ℝ :=
  (bridgeProbability T hT a).map (measurable_pathArea T).aemeasurable

theorem entranceAreaProbability_toMeasure (T : ℝ≥0) (hT : 0 < T) :
    (entranceAreaProbability T hT : Measure ℝ) = entranceAreaLaw T hT := rfl

theorem sourceAreaProbability_toMeasure (T : ℝ≥0) (hT : 0 < T) (a : ℝ) (ha : 0 < a) :
    (sourceAreaProbability T hT a : Measure ℝ) = BrownianPositiveBridgeAreaScaling.areaLaw a T := by
  change (bridgeProbability T hT a : Measure Path).map (pathArea T) = _
  rw [bridgeProbability_toMeasure T hT a ha]
  rfl

theorem tendsto_sourceAreaProbability (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (sourceAreaProbability T hT) (𝓝[>] 0) (𝓝 (entranceAreaProbability T hT)) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous (bridgeProbability T hT)
    (entranceProbability T hT) (tendsto_positiveBridgeProbability T hT) (continuous_pathArea T)

theorem tendsto_actual_area_moments_to_entrance_moments (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    Tendsto (fun a : ℝ ↦ ∫ f : Path, pathArea T f^d ∂positiveBridgeLaw a T) (𝓝[>] 0)
      (𝓝 (∫ f : Path, pathArea T f^d ∂BrownianEntranceContinuousRealization.pathLaw T hT)) := by
  rw [entrance_area_real_moment_eq_time_kernel_integral T hT d]
  exact actual_area_real_moment_tendsto T hT d

theorem entrance_area_tail_moment_bound (T : ℝ≥0) (hT : 0 < T) (n : ℕ) {B : ℝ} (hB : 0 < B) :
    (∫⁻ f : Path in {f : Path | B ≤ |pathArea T f|}, ENNReal.ofReal (|pathArea T f|^n)
      ∂BrownianEntranceContinuousRealization.pathLaw T hT) ≤ entranceAreaMoment T (n+1)/ENNReal.ofReal B := by
  calc
    _ ≤ ∫⁻ f : Path in {f : Path | B ≤ |pathArea T f|},
        ENNReal.ofReal (|pathArea T f|^(n+1))/ENNReal.ofReal B
        ∂BrownianEntranceContinuousRealization.pathLaw T hT := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_area_tail T B)] with f hf
      exact area_tail_power_le_succ T n hB f hf
    _ ≤ ∫⁻ f : Path, ENNReal.ofReal (|pathArea T f|^(n+1))/ENNReal.ofReal B
        ∂BrownianEntranceContinuousRealization.pathLaw T hT := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := by
      simp only [div_eq_mul_inv]
      rw [lintegral_mul_const _ (((measurable_pathArea T).abs.pow_const (n+1)).ennreal_ofReal),
        entrance_abs_area_moment_eq_time_kernel_integral T hT (n+1)]

theorem entrance_area_moment_tails_vanish (T : ℝ≥0) (hT : 0 < T) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ (∫⁻ f : Path in {f : Path | B ≤ |pathArea T f|},
      ENNReal.ofReal (|pathArea T f|^n) ∂BrownianEntranceContinuousRealization.pathLaw T hT) ≤ ENNReal.ofReal ε := by
  let C := (entranceAreaMoment T (n+1)).toReal
  let B : ℝ := C/ε+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hr : C/B ≤ ε := by
    apply (div_le_iff₀ hB).mpr
    dsimp [B]
    rw [mul_add,mul_div_cancel₀ _ hε.ne',mul_one]
    exact le_add_of_nonneg_right hε.le
  refine ⟨B,hB,(entrance_area_tail_moment_bound T hT n hB).trans ?_⟩
  rw [← ENNReal.ofReal_toReal (entranceAreaMoment_lt_top T hT (n+1)).ne,
    ← ENNReal.ofReal_div_of_pos hB]
  exact ENNReal.ofReal_le_ofReal hr

end PerronWright.BrownianPositiveBridgeAreaLawIdentification
