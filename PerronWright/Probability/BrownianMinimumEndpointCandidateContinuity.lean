import PerronWright.Probability.BrownianEntranceKernelLaplace
import PerronWright.Probability.BrownianPositiveBridgeGaussianBounds
import PerronWright.Probability.BrownianMinimumWindowSurvivalBounds

/-! # Genuine endpoint continuity of the minimum candidate

The passage-time/level source has finite mass, proved from the actual
passage density and its integrable inverse-square-root time bound. Away
from the terminal time, the actual entrance kernel has one uniform
Gaussian bound. Dominated convergence therefore proves endpoint
continuity, rather than supplying it as a pinning-law interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumEndpointCandidateContinuity

open BrownianFirstPassageDensityGeometry BrownianKilledBoundaryEntrance
open BrownianFirstPassageEndpointGeometry BrownianPositiveBridgeGaussianBounds
open BrownianMinimumWindowSurvivalBounds

theorem continuous_entranceReal (t : ℝ≥0) : Continuous (entranceReal t) := by
  have he : entranceReal t = fun y : ℝ ↦ 2*max y 0/(t : ℝ)*gaussianPDFReal 0 t y := by
    funext y
    by_cases hy : 0 < y
    · simp only [entranceReal,indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy),max_eq_left hy.le]
    · simp only [entranceReal,indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy),
        max_eq_right (le_of_not_gt hy),mul_zero,zero_div,zero_mul]
  rw [he]
  unfold gaussianPDFReal
  fun_prop

theorem continuous_entrance (t : ℝ≥0) : Continuous (entrance t) :=
  ENNReal.continuous_ofReal.comp (continuous_entranceReal t)

theorem entrance_le_envelopeSup (δ t T : ℝ≥0) (hδ : 0 < δ)
    (hδt : δ ≤ t) (htT : t ≤ T) (y : ℝ) :
    entrance t y ≤ ENNReal.ofReal (envelopeSup δ T) := by
  have ht : 0 < t := hδ.trans_le hδt
  have hT : 0 < T := ht.trans_le htT
  apply ENNReal.ofReal_le_ofReal
  apply (le_of_tendsto (densityReal_div_start_tendsto t ht y) ?_).trans
    (envelopeReal_le_sup δ T hT y)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
    with a ha ha1
  exact densityReal_div_start_le_envelope a ha ha1.le δ t T hδ hδt htT y

private def sourceBase (T : ℝ≥0) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) (T : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))

private def sourceDensity (q : ℝ × ℝ) : ℝ≥0∞ := density q.2 q.1

private theorem measurable_sourceDensity : Measurable sourceDensity := by
  change Measurable (fun q : ℝ × ℝ ↦ ENNReal.ofReal
    (if 0 < q.1 then q.2/(q.1*Real.sqrt q.1)*gaussianPDFReal 0 1 (-q.2/Real.sqrt q.1) else 0))
  apply Measurable.ennreal_ofReal
  apply Measurable.ite (measurableSet_lt measurable_const measurable_fst) _ measurable_const
  fun_prop

private def sourceMeasure (T : ℝ≥0) : Measure (ℝ × ℝ) :=
  (sourceBase T).withDensity sourceDensity

private theorem ae_source_domain (T : ℝ≥0) :
    ∀ᵐ q ∂sourceMeasure T, q.1 ∈ Ioo (0 : ℝ) (T : ℝ) ∧ q.2 ∈ Ioi (0 : ℝ) := by
  have hb : ∀ᵐ q ∂sourceBase T, q.1 ∈ Ioo (0 : ℝ) (T : ℝ) ∧ q.2 ∈ Ioi (0 : ℝ) :=
    (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)).and
      (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi))
  rw [sourceMeasure,ae_withDensity_iff measurable_sourceDensity]
  exact hb.mono (fun _ h _ ↦ h)

private theorem sourceMeasure_univ_ne_top (T : ℝ≥0) (hT : 0 < T) :
    sourceMeasure T univ ≠ ⊤ := by
  have hlevel (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (T : ℝ)) :
      (∫⁻ a in Ioi (0 : ℝ), density a s) ≤
        ENNReal.ofReal ((Real.sqrt (T : ℝ)/Real.sqrt (2*Real.pi))*timeMajorant T s) := by
    rw [passage_level_mass s hs.1]
    apply ENNReal.ofReal_le_ofReal
    have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs.1
    have hrem : 0 < Real.sqrt ((T : ℝ)-s) := Real.sqrt_pos.mpr (sub_pos.mpr hs.2)
    have hpi : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have he : 1/(Real.sqrt (2*Real.pi)*Real.sqrt s) =
        (Real.sqrt ((T : ℝ)-s)/Real.sqrt (2*Real.pi))*timeMajorant T s := by
      unfold timeMajorant
      field_simp
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (timeMajorant_nonneg T s)
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by linarith [hs.1])) hpi.le
  have hmass : sourceMeasure T univ =
      ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ∫⁻ a in Ioi (0 : ℝ), density a s := by
    rw [sourceMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact lintegral_prod _ measurable_sourceDensity.aemeasurable
  have hb : sourceMeasure T univ ≤
      ENNReal.ofReal (Real.sqrt (T : ℝ)/Real.sqrt (2*Real.pi))*
        ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ENNReal.ofReal (timeMajorant T s) := by
    rw [hmass,← lintegral_const_mul _ (measurable_timeMajorant T).ennreal_ofReal]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact hlevel s hs
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_timeMajorant_ne_top T hT)) hb

private def testIntegrand (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ)
    (z : ℝ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  entrance (remainingTime T q.1) (q.2+z)*ENNReal.ofReal (Φ (Real.toNNReal q.1,-q.2,q.2+z))

private theorem measurable_joint_testIntegrand (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) :
    Measurable (fun q : ℝ × (ℝ × ℝ) ↦ testIntegrand T Φ q.1 q.2) := by
  have he : Measurable (fun q : ℝ × (ℝ × ℝ) ↦ entrance (remainingTime T q.2.1) (q.2.2+q.1)) :=
    BrownianEntranceKernelLaplace.measurable_joint_entrance.comp
      (by fun_prop : Measurable (fun q : ℝ × (ℝ × ℝ) ↦ ((T : ℝ)-q.2.1,q.2.2+q.1)))
  exact he.mul ((Φ.continuous.measurable.comp
    (by fun_prop : Measurable (fun q : ℝ × (ℝ × ℝ) ↦
      (Real.toNNReal q.2.1,-q.2.2,q.2.2+q.1)))).ennreal_ofReal)

def candidate (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
    density a s*entrance (remainingTime T s) (a+z)*ENNReal.ofReal (Φ (Real.toNNReal s,-a,a+z))

theorem measurable_joint_integrand (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) :
    Measurable (fun q : ℝ × (ℝ × ℝ) ↦ density q.2.2 q.2.1*
      entrance (remainingTime T q.2.1) (q.2.2+q.1)*
        ENNReal.ofReal (Φ (Real.toNNReal q.2.1,-q.2.2,q.2.2+q.1))) := by
  have h := (measurable_sourceDensity.comp
      (measurable_snd : Measurable (Prod.snd : ℝ × (ℝ × ℝ) → ℝ × ℝ))).mul
    (measurable_joint_testIntegrand T Φ)
  convert h using 1
  funext q
  exact mul_assoc _ _ _

private theorem candidate_eq_source (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (z : ℝ) :
    candidate T Φ z = ∫⁻ q, testIntegrand T Φ z q ∂sourceMeasure T := by
  have hm : Measurable (testIntegrand T Φ z) := by
    simpa only [Function.comp_def] using
      (measurable_joint_testIntegrand T Φ).comp
        (measurable_const.prodMk measurable_id : Measurable (fun q : ℝ × ℝ ↦ (z,q)))
  rw [sourceMeasure,lintegral_withDensity_eq_lintegral_mul (sourceBase T) measurable_sourceDensity
    hm,
    sourceBase,lintegral_prod]
  · apply lintegral_congr
    intro s
    apply lintegral_congr
    intro a
    change density a s*entrance (remainingTime T s) (a+z)*
      ENNReal.ofReal (Φ (Real.toNNReal s,-a,a+z)) =
        density a s*(entrance (remainingTime T s) (a+z)*ENNReal.ofReal (Φ (Real.toNNReal s,-a,a+z)))
    exact mul_assoc _ _ _
  · exact (measurable_sourceDensity.mul hm).aemeasurable

private theorem integrand_uniform_bound (T b : ℝ≥0) (hb : b < T)
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ)
    (hcut : ∀ t : ℝ≥0, b ≤ t → ∀ m y, Φ (t,m,y) = 0) (z : ℝ) :
    ∀ᵐ q ∂sourceMeasure T, testIntegrand T Φ z q ≤
      ENNReal.ofReal (envelopeSup (Real.toNNReal ((T : ℝ)-(b : ℝ))) T)*ENNReal.ofReal ‖Φ‖ := by
  filter_upwards [ae_source_domain T] with q hq
  by_cases hqcut : b ≤ Real.toNNReal q.1
  · simp only [testIntegrand,hcut _ hqcut,ENNReal.ofReal_zero,mul_zero,zero_le]
  · have hqbelow : q.1 < (b : ℝ) := by
      have he := Real.coe_toNNReal q.1 hq.1.1.le
      have hc : (Real.toNNReal q.1 : ℝ) < b := lt_of_not_ge hqcut
      rwa [he] at hc
    have hδ : 0 < Real.toNNReal ((T : ℝ)-(b : ℝ)) :=
      Real.toNNReal_pos.mpr (sub_pos.mpr (show (b : ℝ) < T from hb))
    have hδt : Real.toNNReal ((T : ℝ)-(b : ℝ)) ≤ remainingTime T q.1 :=
      Real.toNNReal_le_toNNReal (by linarith)
    have htT : remainingTime T q.1 ≤ T := by
      calc
        _ ≤ Real.toNNReal (T : ℝ) := Real.toNNReal_le_toNNReal (sub_le_self _ hq.1.1.le)
        _ = T := Real.toNNReal_coe
    have hΦ : ENNReal.ofReal (Φ (Real.toNNReal q.1,-q.2,q.2+z)) ≤ ENNReal.ofReal ‖Φ‖ := by
      apply ENNReal.ofReal_le_ofReal
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm _)
    exact mul_le_mul' (entrance_le_envelopeSup _ _ _ hδ hδt htT _) hΦ

theorem candidate_ne_top (T b : ℝ≥0) (hb : b < T) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ)
    (hcut : ∀ t : ℝ≥0, b ≤ t → ∀ m y, Φ (t,m,y) = 0) (z : ℝ) :
    candidate T Φ z ≠ ⊤ := by
  rw [candidate_eq_source]
  have hh := lintegral_mono_ae (integrand_uniform_bound T b hb Φ hcut z)
  rw [lintegral_const] at hh
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (sourceMeasure_univ_ne_top T ((show 0 ≤ b from zero_le).trans_lt hb))) hh

theorem candidate_tendsto (T b : ℝ≥0) (hb : b < T) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ)
    (hcut : ∀ t : ℝ≥0, b ≤ t → ∀ m y, Φ (t,m,y) = 0) (z₀ : ℝ) :
    Tendsto (candidate T Φ) (𝓝 z₀) (𝓝 (candidate T Φ z₀)) := by
  have hm (z : ℝ) : Measurable (testIntegrand T Φ z) := by
    simpa only [Function.comp_def] using
      (measurable_joint_testIntegrand T Φ).comp
        (measurable_const.prodMk measurable_id : Measurable (fun q : ℝ × ℝ ↦ (z,q)))
  have hlim : ∀ᵐ q ∂sourceMeasure T, Tendsto (fun z : ℝ ↦ testIntegrand T Φ z q)
      (𝓝 z₀) (𝓝 (testIntegrand T Φ z₀ q)) := by
    apply Eventually.of_forall
    intro q
    have he := (continuous_entrance (remainingTime T q.1)).tendsto (q.2+z₀) |>.comp
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ q.2) (𝓝 z₀) (𝓝 q.2)).add tendsto_id)
    have hΦ := ENNReal.tendsto_ofReal (Φ.continuous.tendsto (Real.toNNReal q.1,-q.2,q.2+z₀) |>.comp
      ((by fun_prop : Continuous (fun z : ℝ ↦ (Real.toNNReal q.1,-q.2,q.2+z))).tendsto z₀))
    exact ENNReal.Tendsto.mul he (Or.inr ENNReal.ofReal_ne_top) hΦ (Or.inr ENNReal.ofReal_ne_top)
  have hfin : (∫⁻ _q,
      ENNReal.ofReal (envelopeSup (Real.toNNReal ((T : ℝ)-(b : ℝ))) T)*ENNReal.ofReal ‖Φ‖
        ∂sourceMeasure T) ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (sourceMeasure_univ_ne_top T ((show 0 ≤ b from zero_le).trans_lt hb))
  have h := tendsto_lintegral_filter_of_dominated_convergence (μ := sourceMeasure T)
    (fun _q ↦ ENNReal.ofReal (envelopeSup (Real.toNNReal ((T : ℝ)-(b : ℝ))) T)*ENNReal.ofReal ‖Φ‖)
    (Eventually.of_forall hm) (Eventually.of_forall (integrand_uniform_bound T b hb Φ hcut)) hfin hlim
  simpa only [← candidate_eq_source] using h

end PerronWright.BrownianMinimumEndpointCandidateContinuity
