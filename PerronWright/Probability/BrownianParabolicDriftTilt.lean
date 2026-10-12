import PerronWright.Probability.BrownianParabolicDriftTiltGeometry

/-! # Genuine finite-horizon parabolic change of Brownian path law

The true bridge-area tilt and the true independent endpoint tilt combine
under reconstruction. Thus the stopped parabolic law has the literal
exponential Radon--Nikodym weight, without a Girsanov assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicDriftTilt

open BrownianPathLaw BrownianPinnedBridgeArea BrownianBridgeCyclicArea
open BrownianFirstPassageBridgeLaw BrownianBridgeAreaTiltPathLaw
open BrownianParabolicDriftTiltGeometry

private theorem map_withDensity_pullback {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) {f : α → β} (hf : Measurable f)
    {w : β → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity (fun x ↦ w (f x))).map f = (μ.map f).withDensity w := by
  apply Measure.ext_of_lintegral _
  intro Φ hΦ
  rw [lintegral_map hΦ hf]
  change (∫⁻ a, (Φ ∘ f) a ∂μ.withDensity (w ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul μ (hw.comp hf) (hΦ.comp hf),
    lintegral_withDensity_eq_lintegral_mul (μ.map f) hw hΦ,
    lintegral_map (hw.mul hΦ) hf]
  rfl

private theorem independent_score_coordinates (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    IndepFun (area T) (fun f : Path ↦ (lambda-(T : ℝ)/2)*f T) pathLaw := by
  simpa only [Function.comp_def,id_eq] using (area_independent_endpoint T hT).comp
    measurable_id (measurable_id.const_mul (lambda-(T : ℝ)/2))

theorem hasGaussianLaw_actual_score (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    HasGaussianLaw (score lambda T) pathLaw := by
  have he : score lambda T = fun f : Path ↦ area T f+(lambda-(T : ℝ)/2)*f T :=
    funext (score_eq_bridge_endpoint lambda T hT)
  rw [he]
  exact iIndepFun.hasGaussianLaw_fun_add (hasLaw_area T hT).hasGaussianLaw
    (gaussianReal_const_mul (isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T)
      (lambda-(T : ℝ)/2)).hasGaussianLaw (independent_score_coordinates lambda T hT)

theorem integral_actual_score (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    (∫ f : Path, score lambda T f ∂pathLaw) = 0 := by
  have he : score lambda T = fun f : Path ↦ area T f+(lambda-(T : ℝ)/2)*f T :=
    funext (score_eq_bridge_endpoint lambda T hT)
  rw [he,integral_add (hasLaw_area T hT).hasGaussianLaw.integrable
    ((isBrownian_pathLaw.toIsPreBrownianReal.integrable_eval T).const_mul _),
    integral_area T hT,integral_const_mul,isBrownian_pathLaw.toIsPreBrownianReal.integral_eval]
  ring

theorem variance_actual_score (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    Var[score lambda T;pathLaw] = energy lambda T := by
  have he : score lambda T = fun f : Path ↦ area T f+(lambda-(T : ℝ)/2)*f T :=
    funext (score_eq_bridge_endpoint lambda T hT)
  rw [he,(independent_score_coordinates lambda T hT).variance_fun_add
    (hasLaw_area T hT).hasGaussianLaw.memLp_two
    ((gaussianReal_const_mul (isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T)
      (lambda-(T : ℝ)/2)).hasGaussianLaw.memLp_two),
    variance_area T hT,variance_const_mul,
    (isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T).variance_eq,
    variance_id_gaussianReal,energy_eq_bridge_endpoint_variance]
  ring

theorem hasLaw_actual_score (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    HasLaw (score lambda T) (gaussianReal 0 (Real.toNNReal (energy lambda T))) pathLaw := by
  refine ⟨(measurable_score lambda T).aemeasurable,?_⟩
  rw [(hasGaussianLaw_actual_score lambda T hT).map_eq_gaussianReal,
    integral_actual_score lambda T hT,variance_actual_score lambda T hT]

theorem pinnedLaw_withDensity_bridgeArea (T : ℝ≥0) (hT : 0 < T) :
    (pinnedLaw T).withDensity (bridgeDensity T) = (pinnedLaw T).map (bridgeShift T) := by
  have hw := BrownianBridgeAreaTiltPathLaw.pathLaw_areaTilt_eq_shift T hT 1
  rw [BrownianPinnedBridgeAreaTilt.tiltedAreaLaw_eq_withDensity T hT 1] at hw
  have hleft : pathLaw.withDensity (fun f ↦ bridgeDensity T (stoppedBridgePath T f)) =
      pathLaw.withDensity (fun f ↦ ENNReal.ofReal (Real.exp (area T f-(T : ℝ)^3/24))) := by
    congr 1
    funext f
    simp only [bridgeDensity,pathArea_stoppedBridgePath]
  have hmap := map_withDensity_pullback pathLaw (measurable_stoppedBridgePath T)
    (measurable_bridgeDensity T)
  rw [hleft] at hmap
  change _ = (pinnedLaw T).withDensity (bridgeDensity T) at hmap
  have hright : (pinnedLaw T).map (bridgeShift T) = pathLaw.map (shiftedBridgePath T 1) := by
    rw [pinnedLaw,Measure.map_map (measurable_bridgeShift T) (measurable_stoppedBridgePath T)]
    rfl
  rw [hright]
  rw [← hmap]
  simpa only [one_mul,one_pow,mul_one] using hw

theorem gaussian_withDensity_endpoint (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    (gaussianReal 0 T).withDensity (endpointDensity lambda T) =
      (gaussianReal 0 T).map (fun z ↦ z+(lambda-(T : ℝ)/2)*(T : ℝ)) := by
  let d := lambda-(T : ℝ)/2
  have hw := BrownianEndpointDriftTilt.weighted_pathLaw_eq_drift T hT d
  have hp := congrArg (Measure.map (fun f : Path ↦ f T)) hw
  have hmap := map_withDensity_pullback pathLaw (continuous_eval T).measurable
    (measurable_endpointDensity lambda T)
  have hl : BrownianEndpointDriftTilt.endpointDensity T d =
      fun f : Path ↦ endpointDensity lambda T (f T) := rfl
  rw [hl,hmap,(isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T).map_eq,
    Measure.map_map (continuous_eval T).measurable (BrownianEndpointDriftTilt.measurable_driftPath T d)] at hp
  have hr : (fun f : Path ↦ f T) ∘ (BrownianEndpointDriftTilt.driftPath T d) =
      (fun z : ℝ ↦ z+d*(T : ℝ)) ∘ (fun f : Path ↦ f T) := by
    funext f
    simp only [BrownianEndpointDriftTilt.driftPath_eval,min_self,Function.comp_def]
  rw [hr,← Measure.map_map (by fun_prop) (continuous_eval T).measurable,
    (isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T).map_eq] at hp
  exact hp

theorem density_weighted_bridge_endpoint_jointLaw (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    (pathLaw.withDensity (density lambda T)).map (fun f : Path ↦ (stoppedBridgePath T f,f T)) =
      ((pinnedLaw T).map (bridgeShift T)).prod
        ((gaussianReal 0 T).map (fun z ↦ z+(lambda-(T : ℝ)/2)*(T : ℝ))) := by
  have hf : Measurable (fun f : Path ↦ (stoppedBridgePath T f,f T)) :=
    (measurable_stoppedBridgePath T).prodMk (continuous_eval T).measurable
  have hw : Measurable (fun p : Path × ℝ ↦ bridgeDensity T p.1*endpointDensity lambda T p.2) :=
    ((measurable_bridgeDensity T).comp measurable_fst).mul
      ((measurable_endpointDensity lambda T).comp measurable_snd)
  have he : density lambda T =
      fun f : Path ↦ bridgeDensity T (stoppedBridgePath T f)*endpointDensity lambda T (f T) :=
    funext (density_eq_bridge_endpoint_product lambda T hT)
  rw [he,map_withDensity_pullback pathLaw hf hw,bridge_endpoint_jointLaw T hT,
    ← prod_withDensity (measurable_bridgeDensity T) (measurable_endpointDensity lambda T),
    pinnedLaw_withDensity_bridgeArea T hT,gaussian_withDensity_endpoint lambda T hT]

/-- Actual full stopped continuous-path Borel law, not just finite tests. -/
theorem actual_stopped_parabolic_law_eq_weighted (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (stoppedParabolicPath lambda T) =
      (pathLaw.withDensity (density lambda T)).map (BrownianEndpointDriftTilt.stoppedPath T) := by
  have hj := density_weighted_bridge_endpoint_jointLaw lambda T hT
  have h := congrArg (Measure.map (reconstruct T)) hj
  rw [Measure.map_map (measurable_reconstruct T)
    ((measurable_stoppedBridgePath T).prodMk (continuous_eval T).measurable)] at h
  have hl : (reconstruct T) ∘ (fun f : Path ↦ (stoppedBridgePath T f,f T)) =
      BrownianEndpointDriftTilt.stoppedPath T := funext (reconstruct_bridge_endpoint T)
  rw [hl,Measure.map_prod_map (pinnedLaw T) (gaussianReal 0 T)
    (measurable_bridgeShift T) (by fun_prop),
    Measure.map_map (measurable_reconstruct T)
      ((measurable_bridgeShift T).prodMap (by fun_prop)),
    ← bridge_endpoint_jointLaw T hT,
    Measure.map_map ((measurable_reconstruct T).comp
      ((measurable_bridgeShift T).prodMap (by fun_prop)))
      ((measurable_stoppedBridgePath T).prodMk (continuous_eval T).measurable)] at h
  have hr : ((reconstruct T) ∘ Prod.map (bridgeShift T)
      (fun z ↦ z+(lambda-(T : ℝ)/2)*(T : ℝ))) ∘
      (fun f : Path ↦ (stoppedBridgePath T f,f T)) = stoppedParabolicPath lambda T :=
    funext (reconstruct_shift_eq_stoppedParabolic lambda T hT)
  rw [hr] at h
  exact h.symm

theorem lintegral_actual_parabolic_eq_weighted (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    {Φ : Path → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ f : Path, Φ (stoppedParabolicPath lambda T f) ∂pathLaw) =
      ∫⁻ f : Path, density lambda T f*Φ (BrownianEndpointDriftTilt.stoppedPath T f) ∂pathLaw := by
  rw [← lintegral_map hΦ (measurable_stoppedParabolicPath lambda T),
    actual_stopped_parabolic_law_eq_weighted lambda T hT,
    lintegral_map hΦ (BrownianEndpointDriftTilt.measurable_stoppedPath T)]
  exact lintegral_withDensity_eq_lintegral_mul pathLaw (measurable_density lambda T)
    (hΦ.comp (BrownianEndpointDriftTilt.measurable_stoppedPath T))

theorem lintegral_actual_parabolic_density (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ f : Path, density lambda T f ∂pathLaw) = 1 := by
  have h := lintegral_actual_parabolic_eq_weighted lambda T hT
    (Φ := fun _ ↦ (1 : ℝ≥0∞)) measurable_const
  simpa only [mul_one,lintegral_one,measure_univ] using h.symm

theorem actual_parabolic_density_isProbability (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    IsProbabilityMeasure (pathLaw.withDensity (density lambda T)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    lintegral_actual_parabolic_density lambda T hT]

end PerronWright.BrownianParabolicDriftTilt
