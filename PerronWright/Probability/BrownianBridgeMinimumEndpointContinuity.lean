import PerronWright.Probability.ContinuousPathMinimumFutureBandAverage
import PerronWright.Probability.BrownianBridgeUniqueMinimum
import PerronWright.Probability.BrownianFirstPassageBridgeLaw
import PerronWright.Probability.ContinuousPathUniqueMinimumContinuity

/-! # Actual minimum tests are continuous in the pinned bridge endpoint

The reconstructed path is the actual independent bridge--Gaussian
representation. Its minimum selector is continuous almost everywhere
because the genuine pinned bridge has a proved unique minimum. Bounded
convergence then proves endpoint continuity of whole-future minimum
tests. No conditional minimum law or endpoint-continuity premise is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeMinimumEndpointContinuity

open BrownianPathLaw ContinuousPathLeastMinimum ContinuousPathMinimumFutureBandAverage
open ContinuousPathUniqueMinimumContinuity BrownianFirstPassagePastFibers
open BrownianFirstPassageBridgeLaw BrownianBridgeUniqueMinimum BrownianBridgeCyclicPath
open BrownianBridgeMinimumShift BrownianPinnedBridge BrownianBridgeAreaTiltPathLaw

theorem continuousAt_minimumPoint_of_unique (T : ℝ≥0) (f : Path)
    (hunique : ∀ t : ℝ≥0, t ≤ T → f t = minimumValue T f → t = leastMinimizer T f) :
    ContinuousAt (minimumPoint T) f := by
  have hm := continuousAt_leastMinimizer_of_unique T f hunique
  exact hm.prodMk ((continuous_minimumValue T).continuousAt.prodMk
    (continuous_joint_futurePath.continuousAt.comp (hm.prodMk continuousAt_id)))

theorem ae_stoppedBridge_unique_minimum (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, ∀ t : ℝ≥0, t ≤ T →
      stoppedBridgePath T f t = minimumValue T (stoppedBridgePath T f) →
      t = leastMinimizer T (stoppedBridgePath T f) := by
  filter_upwards [ae_closedBridge_unique_minimum T hT,ae_closedBridge_eq_bridge T] with f hu he
  have hp : stoppedBridgePath T f = stoppedClosedBridgePath T f := by
    apply ContinuousMap.ext
    intro t
    exact (he (min t T)).symm
  intro t ht hmin
  rw [hp] at hmin ⊢
  change t = bridgeMinimumTime T f
  apply hu t ht
  change closedBridge T (min t T) f = bridgeMinimumValue T f at hmin
  simpa only [min_eq_left ht] using hmin

def reconstructedMinimumPoint (T : ℝ≥0) (z : ℝ) (f : Path) : ℝ≥0 × ℝ × Path :=
  minimumPoint T (reconstruct T (stoppedBridgePath T f,z))

theorem measurable_joint_reconstructedMinimumPoint (T : ℝ≥0) :
    Measurable (fun p : ℝ × Path ↦ reconstructedMinimumPoint T p.1 p.2) :=
  (measurable_minimumPoint T).comp ((measurable_reconstruct T).comp
    (((measurable_stoppedBridgePath T).comp measurable_snd).prodMk measurable_fst))

theorem ae_reconstructed_minimumPoint_tendsto (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pathLaw, Tendsto (fun z : ℝ ↦ reconstructedMinimumPoint T z f) (𝓝 0)
      (𝓝 (minimumPoint T (stoppedBridgePath T f))) := by
  filter_upwards [ae_stoppedBridge_unique_minimum T hT] with f hf
  have hr := (continuous_reconstruct T).tendsto (stoppedBridgePath T f,0) |>.comp
    (tendsto_const_nhds.prodMk_nhds tendsto_id)
  have hz : reconstruct T (stoppedBridgePath T f,0) = stoppedBridgePath T f := by
    apply ContinuousMap.ext
    intro t
    change reconstruct T (stoppedBridgePath T f,0) t = stoppedBridgePath T f t
    simp only [reconstruct_eval,mul_zero,add_zero]
  rw [hz] at hr
  exact (continuousAt_minimumPoint_of_unique T _ hf).tendsto.comp hr

theorem actual_reconstructed_minimum_test_tendsto (T : ℝ≥0) (hT : 0 < T)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) :
    Tendsto (fun z : ℝ ↦ ∫ f, Ψ (reconstructedMinimumPoint T z f) ∂pathLaw) (𝓝 0)
      (𝓝 (∫ f, Ψ (minimumPoint T (stoppedBridgePath T f)) ∂pathLaw)) := by
  have hm (z : ℝ) : AEStronglyMeasurable (fun f : Path ↦
      Ψ (reconstructedMinimumPoint T z f)) pathLaw :=
    (Ψ.continuous.measurable.comp ((measurable_joint_reconstructedMinimumPoint T).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  have hb : ∀ᶠ z : ℝ in 𝓝 0, ∀ᵐ f ∂pathLaw,
      ‖Ψ (reconstructedMinimumPoint T z f)‖ ≤ ‖Ψ‖ :=
    Eventually.of_forall (fun z ↦ Eventually.of_forall (fun f ↦ Ψ.norm_coe_le_norm _))
  have hl : ∀ᵐ f ∂pathLaw, Tendsto (fun z : ℝ ↦ Ψ (reconstructedMinimumPoint T z f))
      (𝓝 0) (𝓝 (Ψ (minimumPoint T (stoppedBridgePath T f)))) := by
    filter_upwards [ae_reconstructed_minimumPoint_tendsto T hT] with f hf
    exact Ψ.continuous.tendsto _ |>.comp hf
  exact tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall hm)
    hb (integrable_const ‖Ψ‖) hl

theorem pinned_minimum_test_tendsto (T : ℝ≥0) (hT : 0 < T)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) :
    Tendsto (fun z : ℝ ↦ ∫ g, Ψ (minimumPoint T (reconstruct T (g,z))) ∂pinnedLaw T)
      (𝓝 0) (𝓝 (∫ g, Ψ (minimumPoint T g) ∂pinnedLaw T)) := by
  have ht := actual_reconstructed_minimum_test_tendsto T hT Ψ
  have hc (z : ℝ) : (∫ g, Ψ (minimumPoint T (reconstruct T (g,z))) ∂pinnedLaw T) =
      ∫ f, Ψ (reconstructedMinimumPoint T z f) ∂pathLaw := by
    rw [pinnedLaw]
    exact integral_map (measurable_stoppedBridgePath T).aemeasurable
      (show AEStronglyMeasurable (fun g : Path ↦ Ψ (minimumPoint T (reconstruct T (g,z))))
        (pathLaw.map (stoppedBridgePath T)) from
      (Ψ.continuous.measurable.comp ((measurable_minimumPoint T).comp
        ((measurable_reconstruct T).comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable)
  have hzero : (∫ g, Ψ (minimumPoint T g) ∂pinnedLaw T) =
      ∫ f, Ψ (minimumPoint T (stoppedBridgePath T f)) ∂pathLaw := by
    rw [pinnedLaw]
    exact integral_map (measurable_stoppedBridgePath T).aemeasurable
      (show AEStronglyMeasurable (fun g : Path ↦ Ψ (minimumPoint T g))
        (pathLaw.map (stoppedBridgePath T)) from
        (Ψ.continuous.measurable.comp (measurable_minimumPoint T)).aestronglyMeasurable)
  rw [hzero]
  exact ht.congr (fun z ↦ (hc z).symm)

end PerronWright.BrownianBridgeMinimumEndpointContinuity
