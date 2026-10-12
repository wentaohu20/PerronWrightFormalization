import PerronWright.Probability.BrownianBridgeMinimumEndpointContinuity
import PerronWright.Probability.BrownianMinimumEndpointMeasure
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # Genuine bridge--Gaussian minimum endpoint test disintegration

The actual Brownian minimum density and actual independent bridge endpoint
law give the same endpoint-weighted minimum integral. The pinned minimum
test is continuous at endpoint zero by the proved unique bridge minimum.
No conditional distribution identity is supplied as a premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumEndpointPinningGeometry

open BrownianPathLaw ContinuousPathLeastMinimum BrownianMinimumEndpointMeasure
open BrownianFirstPassageBridgeLaw BrownianBridgeMinimumEndpointContinuity
open BrownianMinimumEndpointTests ContinuousPathMinimumFutureBandAverage
open BrownianFirstPassageEndpointGeometry BrownianKilledBoundaryEntrance

private theorem minimumValue_congr_prefix (T : ℝ≥0) (f g : Path)
    (h : ∀ t : ℝ≥0, t ≤ T → f t = g t) : minimumValue T f = minimumValue T g := by
  unfold minimumValue
  congr 1
  apply image_congr
  intro t ht
  exact h t ht.2

private theorem leastMinimizer_congr_prefix (T : ℝ≥0) (f g : Path)
    (h : ∀ t : ℝ≥0, t ≤ T → f t = g t) : leastMinimizer T f = leastMinimizer T g := by
  have hv := minimumValue_congr_prefix T f g h
  unfold leastMinimizer
  congr 1
  ext t
  by_cases ht : t ≤ T
  · simp only [minimizingTimes,mem_inter_iff,mem_Icc,zero_le,true_and,ht,and_true,mem_ofPred_eq]
    rw [h t ht,hv]
  · simp only [minimizingTimes,mem_inter_iff,mem_Icc,ht,and_false,false_and]

theorem minimumTriple_stoppedPath (T : ℝ≥0) (f : Path) :
    minimumTriple T (BrownianEndpointDriftTilt.stoppedPath T f) = minimumTriple T f := by
  have h (t : ℝ≥0) (ht : t ≤ T) : BrownianEndpointDriftTilt.stoppedPath T f t = f t := by
    rw [BrownianEndpointDriftTilt.stoppedPath_eval,min_eq_left ht]
  simp only [minimumTriple,leastMinimizer_congr_prefix T _ _ h,
    minimumValue_congr_prefix T _ _ h,h T le_rfl]

def pinnedTest (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ g, ENNReal.ofReal (Φ (minimumTriple T (reconstruct T (g,z)))) ∂pinnedLaw T

theorem measurable_pinnedTest (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) :
    Measurable (pinnedTest T Φ) := by
  have hm : Measurable (fun p : ℝ × Path ↦
      ENNReal.ofReal (Φ (minimumTriple T (reconstruct T (p.2,p.1))))) :=
    (Φ.continuous.measurable.comp ((measurable_minimumTriple T).comp
      ((measurable_reconstruct T).comp measurable_swap))).ennreal_ofReal
  exact hm.lintegral_prod_right'

private theorem integral_pinnedTest (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ)
    (hΦ : ∀ p, 0 ≤ Φ p) (z : ℝ) :
    ENNReal.ofReal (∫ g, Φ (minimumTriple T (reconstruct T (g,z))) ∂pinnedLaw T) =
      pinnedTest T Φ z := by
  have hm : AEStronglyMeasurable (fun g : Path ↦
      Φ (minimumTriple T (reconstruct T (g,z)))) (pinnedLaw T) :=
    (Φ.continuous.measurable.comp ((measurable_minimumTriple T).comp
      ((measurable_reconstruct T).comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
  exact ofReal_integral_eq_lintegral_ofReal
    ((integrable_const ‖Φ‖).mono' hm (Eventually.of_forall (fun g ↦ Φ.norm_coe_le_norm _)))
    (Eventually.of_forall (fun g ↦ hΦ _))

theorem pinnedTest_tendsto (T : ℝ≥0) (hT : 0 < T)
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p) :
    Tendsto (pinnedTest T Φ) (𝓝 0)
      (𝓝 (∫⁻ g, ENNReal.ofReal (Φ (minimumTriple T g)) ∂pinnedLaw T)) := by
  have ht := pinned_minimum_test_tendsto T hT (endpointTest T Φ)
  simp_rw [endpointTest_minimumPoint] at ht
  have he : ENNReal.ofReal (∫ g, Φ (minimumTriple T g) ∂pinnedLaw T) =
      ∫⁻ g, ENNReal.ofReal (Φ (minimumTriple T g)) ∂pinnedLaw T := by
    exact ofReal_integral_eq_lintegral_ofReal
      ((integrable_const ‖Φ‖).mono'
        (Φ.continuous.measurable.comp (measurable_minimumTriple T)).aestronglyMeasurable
        (Eventually.of_forall (fun g ↦ Φ.norm_coe_le_norm _)))
      (Eventually.of_forall (fun g ↦ hΦ _))
  have h := ENNReal.continuous_ofReal.tendsto _ |>.comp ht
  change Tendsto (fun z ↦ ENNReal.ofReal
    (∫ g, Φ (minimumTriple T (reconstruct T (g,z))) ∂pinnedLaw T)) _
    (𝓝 (ENNReal.ofReal (∫ g, Φ (minimumTriple T g) ∂pinnedLaw T))) at h
  rw [he] at h
  exact h.congr (integral_pinnedTest T Φ hΦ)

theorem actual_endpoint_weighted_minimum_density (T : ℝ≥0) (hT : 0 < T)
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z, H z*pinnedTest T Φ z ∂gaussianReal 0 T) =
      ∫⁻ s in Ioo 0 (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          ∫⁻ y, entrance (remainingTime T s) y*H (y-a)*ENNReal.ofReal (Φ (Real.toNNReal s,-a,y)) := by
  let Ψ : (ℝ≥0 × ℝ × ℝ) → ℝ≥0∞ :=
    fun p ↦ H (p.2.1+p.2.2)*ENNReal.ofReal (Φ p)
  have hΨ : Measurable Ψ :=
    (hH.comp (measurable_snd.fst.add measurable_snd.snd)).mul Φ.continuous.measurable.ennreal_ofReal
  have hp : Measurable (fun p : Path × ℝ ↦ H p.2*
      ENNReal.ofReal (Φ (minimumTriple T (reconstruct T p)))) :=
    (hH.comp measurable_snd).mul
      (Φ.continuous.measurable.comp ((measurable_minimumTriple T).comp
        (measurable_reconstruct T))).ennreal_ofReal
  have hj : Measurable (fun f : Path ↦ (BrownianBridgeAreaTiltPathLaw.stoppedBridgePath T f,f T)) :=
    (BrownianBridgeAreaTiltPathLaw.measurable_stoppedBridgePath T).prodMk (continuous_eval T).measurable
  calc
    _ = ∫⁻ z, ∫⁻ g, H z*ENNReal.ofReal (Φ (minimumTriple T (reconstruct T (g,z))))
        ∂pinnedLaw T ∂gaussianReal 0 T := by
      apply lintegral_congr
      intro z
      exact (lintegral_const_mul _ (Φ.continuous.measurable.comp
        ((measurable_minimumTriple T).comp ((measurable_reconstruct T).comp
          (measurable_id.prodMk measurable_const)))).ennreal_ofReal).symm
    _ = ∫⁻ p, H p.2*ENNReal.ofReal (Φ (minimumTriple T (reconstruct T p)))
        ∂(pinnedLaw T).prod (gaussianReal 0 T) := (lintegral_prod_symm _ hp.aemeasurable).symm
    _ = ∫⁻ f, H (f T)*ENNReal.ofReal (Φ (minimumTriple T f)) ∂pathLaw := by
      rw [← bridge_endpoint_jointLaw T hT,lintegral_map hp hj]
      apply lintegral_congr
      intro f
      rw [reconstruct_bridge_endpoint,minimumTriple_stoppedPath]
    _ = ∫⁻ f, Ψ (minimumTriple T f) ∂pathLaw := by
      apply lintegral_congr
      intro f
      simp only [Ψ,minimumTriple]
      rw [show minimumValue T f+(f T-minimumValue T f) = f T by ring]
    _ = _ := by
      rw [actual_minimum_endpoint_borel_density T hT Ψ hΨ]
      apply lintegral_congr
      intro s
      apply lintegral_congr
      intro a
      congr 1
      apply lintegral_congr
      intro y
      simp only [Ψ,neg_add_eq_sub,mul_assoc]

theorem eq_at_zero_of_ae_eq_of_tendsto {f g : ℝ → ℝ≥0∞} {a b : ℝ≥0∞}
    (ha : Tendsto f (𝓝 0) (𝓝 a)) (hb : Tendsto g (𝓝 0) (𝓝 b))
    (hfg : f =ᵐ[volume] g) : a = b := by
  apply tendsto_nhds_unique_of_frequently_eq ha hb
  exact mem_closure_iff_frequently.mp ((Measure.dense_of_ae hfg) 0)

end PerronWright.BrownianMinimumEndpointPinningGeometry
