import PerronWright.Probability.BrownianSurvivalCylinderCoordinates
import PerronWright.Probability.BrownianMinimumFuturePrefixTests
import PerronWright.Probability.BrownianMinimumFutureWholeLaw
import PerronWright.Probability.BrownianNormalizedSurvivalWholeLaw

/-! # Actual whole-future cylinder entrance limits

The prefix coordinates have the proved actual entrance limit. The true
fresh Brownian path after the survival horizon is retained and integrated
using domination by the genuine normalized survival mass. No whole-path
weak convergence is inferred from finite-dimensional convergence.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianSurvivalWholeCylinderTests

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianSurvivalCylinderCoordinates BrownianEntranceProjectiveFamily
open BrownianMinimumFutureEntranceSource BrownianMinimumFuturePrefixTests
open BrownianMinimumFutureWholeLaw BrownianNormalizedSurvivalWholeLaw
open BrownianSurvivalEntranceScaling BrownianMinimumWindowSurvivalBounds
open BrownianKilledFreeEntranceNonnegativeTests BrownianKilledFreeEntranceTests
open BrownianKilledFiniteDimensionalOrderedTimes
open BrownianPathDilationLaw

private def wholeEval {n : ℕ} (σ : Fin n → ℝ≥0) (f : Path) : Fin n → ℝ := fun i ↦ f (σ i)

private theorem continuous_wholeEval {n : ℕ} (σ : Fin n → ℝ≥0) : Continuous (wholeEval σ) :=
  continuous_pi (fun _ ↦ continuous_eval _)

private def cylinder {n : ℕ} (σ : Fin n → ℝ≥0) (G : (Fin n → ℝ) →ᵇ ℝ) : Path →ᵇ ℝ :=
  G.compContinuous ⟨wholeEval σ,continuous_wholeEval σ⟩

private theorem prefixSample_past {n : ℕ} (σ : Fin n → ℝ≥0) (f : Path) :
    prefixSample σ (pastPath 1 f) = prefixSample σ f := by
  funext i
  have ht : sortedTimes 1 (interiorSamples σ) i.succ ≤ 1 := by
    exact ((sortedTimes_strictMono 1 zero_lt_one (interiorSamples σ)).monotone
      (Fin.le_last _)).trans_eq (sortedTimes_last 1 (interiorSamples σ))
  change f (min (sortedTimes 1 (interiorSamples σ) i.succ) 1) = _
  rw [min_eq_left ht]
  rfl

private def prefixTest {n : ℕ} (σ : Fin n → ℝ≥0) (G : (Fin n → ℝ) →ᵇ ℝ) (h : Path) :
    (Fin ((interiorSamples (clampedTimes σ)).card+1) → ℝ) →ᵇ ℝ :=
  G.compContinuous ⟨fun v ↦ spliceFill σ (v,h),
    (continuous_spliceFill σ).comp (continuous_id.prodMk continuous_const)⟩

private def prefixKernel {n : ℕ} (σ : Fin n → ℝ≥0) (G : (Fin n → ℝ) →ᵇ ℝ)
    (δ : ℝ) (h : Path) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal ((cylinder σ G) (splicePath 1 (p,h)))
    ∂(normalizedSurvivalLaw δ 1).map (pastPath 1)

private theorem prefixKernel_eq_samples {n : ℕ} (σ : Fin n → ℝ≥0)
    (G : (Fin n → ℝ) →ᵇ ℝ) (δ : ℝ) (h : Path) :
    prefixKernel σ G δ h =
      (∫⁻ f in survival (-δ) 1,
        ENNReal.ofReal (prefixTest σ G h (prefixSample (clampedTimes σ) f)) ∂pathLaw)/
          ENNReal.ofReal δ := by
  have hm : Measurable (fun p : Path ↦ ENNReal.ofReal
      ((cylinder σ G) (splicePath 1 (p,h)))) :=
    ((cylinder σ G).continuous.measurable.comp ((measurable_splicePath 1).comp
      (measurable_id.prodMk measurable_const))).ennreal_ofReal
  rw [prefixKernel,lintegral_map hm (measurable_pastPath 1),normalizedSurvivalLaw,
    lintegral_smul_measure,smul_eq_mul]
  rw [div_eq_mul_inv,mul_comm]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae
    isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
  have he := spliceFill_sample σ (pastPath 1 f) h
    (by simpa only [pastPath_eval,min_eq_left (show (0 : ℝ≥0) ≤ 1 from zero_le)] using hf)
  rw [prefixSample_past] at he
  change ENNReal.ofReal (G (wholeEval σ (splicePath 1 (pastPath 1 f,h)))) =
    ENNReal.ofReal (G (spliceFill σ (prefixSample (clampedTimes σ) f,h)))
  rw [he]
  rfl

private theorem sourceKernel_eq_samples {n : ℕ} (σ : Fin n → ℝ≥0)
    (G : (Fin n → ℝ) →ᵇ ℝ) (h : Path) :
    (∫⁻ p, ENNReal.ofReal ((cylinder σ G) (splicePath 1 (p,h)))
      ∂unitSourceLaw.map (pastPath 1)) =
        ∫⁻ f, ENNReal.ofReal (prefixTest σ G h (prefixSample (clampedTimes σ) f)) ∂unitSourceLaw := by
  have hm : Measurable (fun p : Path ↦ ENNReal.ofReal
      ((cylinder σ G) (splicePath 1 (p,h)))) :=
    ((cylinder σ G).continuous.measurable.comp ((measurable_splicePath 1).comp
      (measurable_id.prodMk measurable_const))).ennreal_ofReal
  rw [lintegral_map hm (measurable_pastPath 1)]
  apply lintegral_congr_ae
  filter_upwards [ae_unitSourceLaw_initial_zero] with f hf
  have he := spliceFill_sample σ (pastPath 1 f) h
    (by simpa only [pastPath_eval,min_eq_left (show (0 : ℝ≥0) ≤ 1 from zero_le)] using hf)
  rw [prefixSample_past] at he
  change ENNReal.ofReal (G (wholeEval σ (splicePath 1 (pastPath 1 f,h)))) =
    ENNReal.ofReal (G (spliceFill σ (prefixSample (clampedTimes σ) f,h)))
  rw [he]
  rfl

private theorem prefixKernel_tendsto {n : ℕ} (σ : Fin n → ℝ≥0)
    (G : (Fin n → ℝ) →ᵇ ℝ) (hG : ∀ v, 0 ≤ G v) (h : Path) :
    Tendsto (fun δ : ℝ ↦ prefixKernel σ G δ h) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ∫⁻ p, ENNReal.ofReal ((cylinder σ G) (splicePath 1 (p,h)))
          ∂unitSourceLaw.map (pastPath 1))) := by
  let J := interiorSamples (clampedTimes σ)
  let times := sortedTimes 1 J
  let GG := prefixTest σ G h
  have hGG : ∀ v, 0 ≤ GG v := fun v ↦ hG _
  have ht := actual_unshifted_ordered_nonnegative_test_tendsto J.card times
    (sortedTimes_strictMono 1 zero_lt_one J) (sortedTimes_zero 1 J)
    (GG.compContinuous ⟨Prod.snd,continuous_snd⟩) (fun q ↦ hGG q.2)
  simp only [BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk] at ht
  have hs := unitSource_prefix_nonnegative_test J.card times
    (sortedTimes_strictMono 1 zero_lt_one J) (sortedTimes_zero 1 J) (sortedTimes_last 1 J) GG hGG
  have hc : ENNReal.ofReal (Real.sqrt (2/Real.pi)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity))
  rw [sourceKernel_eq_samples]
  have hm : (ENNReal.ofReal (Real.sqrt (2/Real.pi)))*
      (∫⁻ f, ENNReal.ofReal (prefixTest σ G h (prefixSample (clampedTimes σ) f)) ∂unitSourceLaw) =
      ∫⁻ v, ENNReal.ofReal (GG v) ∂freeEntranceLaw J.card (orderedGaps (J.card+1) times) := by
    change ENNReal.ofReal (Real.sqrt (2/Real.pi))*
      (∫⁻ f, ENNReal.ofReal (GG (fun i ↦ f (times i.succ))) ∂unitSourceLaw) = _
    rw [hs,mul_comm,ENNReal.div_mul_cancel hc ENNReal.ofReal_ne_top]
  rw [hm]
  apply ht.congr
  intro δ
  rw [prefixKernel_eq_samples]
  rw [show times (Fin.last (J.card+1)) = 1 from sortedTimes_last 1 J]
  rfl

private theorem measurable_prefixKernel {n : ℕ} (σ : Fin n → ℝ≥0)
    (G : (Fin n → ℝ) →ᵇ ℝ) (δ : ℝ) (hδ : 0 < δ) : Measurable (prefixKernel σ G δ) := by
  let := normalized_survival_isFinite δ hδ 1
  let : IsFiniteMeasure ((normalizedSurvivalLaw δ 1).map (pastPath 1)) :=
    Measure.isFiniteMeasure_map (normalizedSurvivalLaw δ 1) (pastPath 1)
  have hm : Measurable (fun q : Path × Path ↦ ENNReal.ofReal
      ((cylinder σ G) (splicePath 1 (q.2,q.1)))) :=
    ((cylinder σ G).continuous.measurable.comp ((measurable_splicePath 1).comp
      (measurable_snd.prodMk measurable_fst))).ennreal_ofReal
  exact hm.lintegral_prod_right'

theorem actual_unit_survival_cylinder_tendsto {n : ℕ} (σ : Fin n → ℝ≥0)
    (G : (Fin n → ℝ) →ᵇ ℝ) (hG : ∀ v, 0 ≤ G v) :
    Tendsto (fun δ : ℝ ↦
      ∫⁻ f, ENNReal.ofReal (G (fun i ↦ f (σ i))) ∂normalizedSurvivalLaw δ 1)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ∫⁻ g, ENNReal.ofReal (G (fun i ↦ g (σ i))) ∂unitSourceLaw)) := by
  let C : ℝ≥0∞ := ENNReal.ofReal
    (‖G‖*BrownianKilledSurvivalMoment.survivalCoefficient)
  have hm : ∀ᶠ δ : ℝ in 𝓝[>] 0, Measurable (prefixKernel σ G δ) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact measurable_prefixKernel σ G δ hδ
  have hb : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ h ∂pathLaw, prefixKernel σ G δ h ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact Eventually.of_forall (fun h ↦ by
      rw [prefixKernel_eq_samples]
      have htest (f : Path) : ENNReal.ofReal
          (prefixTest σ G h (prefixSample (clampedTimes σ) f)) ≤ ENNReal.ofReal ‖G‖ :=
        ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (G.norm_coe_le_norm _))
      calc
        _ ≤ ENNReal.ofReal ‖G‖*(pathLaw (survival (-δ) 1)/ENNReal.ofReal δ) :=
          normalized_survival_test_bound δ 1 ‖G‖ _ htest
        _ ≤ ENNReal.ofReal ‖G‖*ENNReal.ofReal BrownianKilledSurvivalMoment.survivalCoefficient :=
          mul_le_mul' le_rfl (by simpa only [NNReal.coe_one,Real.sqrt_one,div_one] using
            normalized_survival_path_mass_bound δ hδ 1 zero_lt_one)
        _ = C := (ENNReal.ofReal_mul (norm_nonneg _)).symm)
  have hfin : (∫⁻ _h : Path, C ∂pathLaw) ≠ ⊤ := by
    simp only [lintegral_const,measure_univ,mul_one]
    exact ENNReal.ofReal_ne_top
  have ht := tendsto_lintegral_filter_of_dominated_convergence (μ := pathLaw)
    (fun _ ↦ C) hm hb hfin (Eventually.of_forall (prefixKernel_tendsto σ G hG))
  have hj : Measurable (fun q : Path × Path ↦ ENNReal.ofReal
      ((cylinder σ G) (splicePath 1 (q.1,q.2)))) :=
    ((cylinder σ G).continuous.measurable.comp (measurable_splicePath 1)).ennreal_ofReal
  have hs : Measurable (fun h : Path ↦ ∫⁻ p,
      ENNReal.ofReal ((cylinder σ G) (splicePath 1 (p,h))) ∂unitSourceLaw.map (pastPath 1)) :=
    hj.lintegral_prod_left'
  rw [lintegral_const_mul _ hs] at ht
  let : IsProbabilityMeasure (unitSourceLaw.map (pastPath 1)) :=
    Measure.isProbabilityMeasure_map (measurable_pastPath 1).aemeasurable
  rw [← lintegral_lintegral_swap hj.aemeasurable,
    ← actual_source_whole_lintegral (cylinder σ G).continuous.measurable.ennreal_ofReal] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  let := normalized_survival_isFinite δ hδ 1
  let : IsFiniteMeasure ((normalizedSurvivalLaw δ 1).map (pastPath 1)) :=
    Measure.isFiniteMeasure_map (normalizedSurvivalLaw δ 1) (pastPath 1)
  change (∫⁻ h, prefixKernel σ G δ h ∂pathLaw) =
    ∫⁻ f, ENNReal.ofReal ((cylinder σ G) f) ∂normalizedSurvivalLaw δ 1
  rw [normalized_survival_whole_lintegral δ hδ 1
      (cylinder σ G).continuous.measurable.ennreal_ofReal,
    lintegral_lintegral_swap hj.aemeasurable]
  rfl

theorem actual_survival_cylinder_tendsto (T : ℝ≥0) (hT : 0 < T)
    {n : ℕ} (σ : Fin n → ℝ≥0) (G : (Fin n → ℝ) →ᵇ ℝ) (hG : ∀ v, 0 ≤ G v) :
    Tendsto (fun δ : ℝ ↦
      ∫⁻ f, ENNReal.ofReal (G (fun i ↦ f (σ i))) ∂normalizedSurvivalLaw δ T)
      (𝓝[>] 0) (𝓝 ((ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ENNReal.ofReal (1/Real.sqrt (T : ℝ)))*
          ∫⁻ g, ENNReal.ofReal (G (fun i ↦ brownianDilation T g (σ i))) ∂unitSourceLaw)) := by
  let σ' : Fin n → ℝ≥0 := fun i ↦ σ i/T
  let GG : (Fin n → ℝ) →ᵇ ℝ := G.compContinuous
    ⟨fun v i ↦ Real.sqrt (T : ℝ)*v i,
      continuous_pi (fun i ↦ continuous_const.mul (continuous_apply i))⟩
  have hGG : ∀ v, 0 ≤ GG v := fun v ↦ hG _
  have ht := (actual_unit_survival_cylinder_tendsto σ' GG hGG).comp
    (positive_scale_parameter_tendsto T hT)
  have ht' := ENNReal.Tendsto.const_mul
    (a := (ENNReal.ofReal (Real.sqrt (T : ℝ)))⁻¹) ht
    (Or.inr (ENNReal.inv_ne_top.mpr
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr hT))))
  have htarget : (ENNReal.ofReal (Real.sqrt (T : ℝ)))⁻¹ *
      (ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ∫⁻ g, ENNReal.ofReal (GG (fun i ↦ g (σ' i))) ∂unitSourceLaw) =
      (ENNReal.ofReal (Real.sqrt (2/Real.pi))*ENNReal.ofReal (1/Real.sqrt (T : ℝ)))*
        ∫⁻ g, ENNReal.ofReal (G (fun i ↦ brownianDilation T g (σ i))) ∂unitSourceLaw := by
    have hinv : ENNReal.ofReal (1/Real.sqrt (T : ℝ)) =
        (ENNReal.ofReal (Real.sqrt (T : ℝ)))⁻¹ := by
      rw [one_div]
      exact ENNReal.ofReal_inv_of_pos (Real.sqrt_pos.mpr hT)
    rw [hinv]
    change (ENNReal.ofReal (Real.sqrt (T : ℝ)))⁻¹*
      (ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ∫⁻ g, ENNReal.ofReal (G (fun i ↦ Real.sqrt (T : ℝ)*g (σ i/T))) ∂unitSourceLaw) = _
    ac_rfl
  rw [htarget] at ht'
  apply ht'.congr
  intro δ
  have hF : Measurable (fun f : Path ↦ ENNReal.ofReal (G (fun i ↦ f (σ i)))) :=
    (G.continuous.measurable.comp (continuous_wholeEval σ).measurable).ennreal_ofReal
  have hscale : normalizedSurvivalLaw δ T = (ENNReal.ofReal (Real.sqrt (T : ℝ)))⁻¹ •
      (normalizedSurvivalLaw (δ/Real.sqrt (T : ℝ)) 1).map (brownianDilation T) := by
    simpa only [mul_one] using normalizedSurvivalLaw_duration_scaling T 1 hT δ
  rw [hscale,
    lintegral_smul_measure,smul_eq_mul,lintegral_map hF (measurable_brownianDilation T)]
  rfl

end PerronWright.BrownianSurvivalWholeCylinderTests
