import PerronWright.Probability.BrownianParabolicDriftTilt
import PerronWright.Probability.BrownianPathReflectionLaw

/-! # Actual parabolic first-passage survival and endpoint density

The finite-horizon killed endpoint law is a genuine Gaussian density
times the area-weighted constrained Brownian bridge mass. No conditional
bridge or first-passage density is postulated.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianParabolicFirstPassageDensity

open BrownianPathLaw BrownianFirstPassageBridgeLaw ContinuousPathFirstPassage
open BrownianBridgeAreaTiltPathLaw BrownianBridgeCyclicArea
open BrownianParabolicDriftTiltGeometry BrownianParabolicDriftTilt

def bridgeAreaMass (level : ℝ) (T : ℝ≥0) (z : ℝ) : ℝ≥0∞ :=
  ((pinnedLaw T).withDensity (bridgeDensity T)) (bridgeConstraint level T z)

theorem measurable_bridgeAreaMass (level : ℝ) (T : ℝ≥0) :
    Measurable (bridgeAreaMass level T) := by
  exact measurable_measure_prodMk_right
    ((measurable_reconstruct T) (measurableSet_survival level T))

def endpointKernel (lambda level : ℝ) (T : ℝ≥0) (z : ℝ) : ℝ≥0∞ :=
  endpointDensity lambda T z*bridgeAreaMass level T z

theorem measurable_endpointKernel (lambda level : ℝ) (T : ℝ≥0) :
    Measurable (endpointKernel lambda level T) :=
  (measurable_endpointDensity lambda T).mul (measurable_bridgeAreaMass level T)

theorem parabolic_survival_endpoint_probability (lambda level : ℝ) (T : ℝ≥0) (hT : 0 < T)
    {B : Set ℝ} (hB : MeasurableSet B) :
    pathLaw ((stoppedParabolicPath lambda T) ⁻¹' survivalEndpointEvent level T B) =
      ∫⁻ z in B, endpointKernel lambda level T z ∂gaussianReal 0 T := by
  let A : Set (Path × ℝ) := {p | reconstruct T p ∈ survival level T ∧ p.2 ∈ B}
  have hA : MeasurableSet A :=
    ((measurable_reconstruct T) (measurableSet_survival level T)).inter (measurable_snd hB)
  have hj : Measurable (fun f : Path ↦ (stoppedBridgePath T f,f T)) :=
    (measurable_stoppedBridgePath T).prodMk (continuous_eval T).measurable
  have he : (fun f : Path ↦ (stoppedBridgePath T f,f T)) ⁻¹' A =
      survivalEndpointEvent level T B := by
    ext f
    simp only [A,survivalEndpointEvent,mem_preimage,mem_ofPred_eq,mem_inter_iff,
      reconstruct_bridge_endpoint,stopped_mem_survival_iff]
  have hstop : (BrownianEndpointDriftTilt.stoppedPath T) ⁻¹' survivalEndpointEvent level T B =
      survivalEndpointEvent level T B := by
    ext f
    simp only [survivalEndpointEvent,mem_preimage,mem_inter_iff,stopped_mem_survival_iff,
      BrownianEndpointDriftTilt.stoppedPath_eval,min_self]
  have hJ := density_weighted_bridge_endpoint_jointLaw lambda T hT
  rw [← pinnedLaw_withDensity_bridgeArea T hT,← gaussian_withDensity_endpoint lambda T hT] at hJ
  calc
    _ = (pathLaw.map (stoppedParabolicPath lambda T)) (survivalEndpointEvent level T B) := by
      rw [Measure.map_apply (measurable_stoppedParabolicPath lambda T)
        (measurableSet_survivalEndpointEvent level T hB)]
    _ = (pathLaw.withDensity (density lambda T)) (survivalEndpointEvent level T B) := by
      rw [actual_stopped_parabolic_law_eq_weighted lambda T hT,
        Measure.map_apply (BrownianEndpointDriftTilt.measurable_stoppedPath T)
          (measurableSet_survivalEndpointEvent level T hB),hstop]
    _ = ((pathLaw.withDensity (density lambda T)).map
        (fun f : Path ↦ (stoppedBridgePath T f,f T))) A := by
      rw [Measure.map_apply hj hA,he]
    _ = (((pinnedLaw T).withDensity (bridgeDensity T)).prod
        ((gaussianReal 0 T).withDensity (endpointDensity lambda T))) A := by rw [hJ]
    _ = ∫⁻ z in B, bridgeAreaMass level T z
        ∂(gaussianReal 0 T).withDensity (endpointDensity lambda T) := by
      rw [Measure.prod_apply_symm hA,← lintegral_indicator hB]
      apply lintegral_congr
      intro z
      have hzset : (fun g : Path ↦ (g,z)) ⁻¹' A =
          if z ∈ B then bridgeConstraint level T z else ∅ := by
        ext g
        by_cases hz : z ∈ B <;> simp [A,bridgeConstraint,hz]
      rw [hzset]
      by_cases hz : z ∈ B
      · simp only [if_pos hz,indicator_of_mem hz,bridgeAreaMass]
      · simp only [if_neg hz,indicator_of_notMem hz,measure_empty]
    _ = _ := setLIntegral_withDensity_eq_setLIntegral_mul (gaussianReal 0 T)
      (measurable_endpointDensity lambda T) (measurable_bridgeAreaMass level T) hB

theorem actual_parabolic_firstPassage_endpoint_probability
    (lambda level : ℝ) (T : ℝ≥0) (hT : 0 < T) {B : Set ℝ} (hB : MeasurableSet B) :
    pathLaw {f : Path | (T : ℝ≥0∞) < firstPassage level (stoppedParabolicPath lambda T f) ∧
      f T+lambda*(T : ℝ)-(T : ℝ)^2/2 ∈ B} =
      ∫⁻ z in B, endpointKernel lambda level T z ∂gaussianReal 0 T := by
  have he : (stoppedParabolicPath lambda T) ⁻¹' survivalEndpointEvent level T B =
      {f : Path | (T : ℝ≥0∞) < firstPassage level (stoppedParabolicPath lambda T f) ∧
        f T+lambda*(T : ℝ)-(T : ℝ)^2/2 ∈ B} := by
    ext f
    change (stoppedParabolicPath lambda T f ∈ survival level T ∧
      stoppedParabolicPath lambda T f T ∈ B) ↔ _
    rw [mem_survival_iff_firstPassage]
    have hx : stoppedParabolicPath lambda T f T = f T+lambda*(T : ℝ)-(T : ℝ)^2/2 := by
      change f (min T T)+lambda*(min T T : ℝ≥0)-(min T T : ℝ≥0)^2/2 = _
      rw [min_self]
    rw [hx]
    rfl
  rw [← he]
  exact parabolic_survival_endpoint_probability lambda level T hT hB

theorem stoppedParabolicPath_eq_stopped_actual_drift (lambda : ℝ) (T : ℝ≥0) (f : Path) :
    stoppedParabolicPath lambda T f =
      BrownianEndpointDriftTilt.stoppedPath T (BrownianPathReflectionLaw.driftPath lambda f) := by
  apply ContinuousMap.ext
  intro t
  rfl

theorem actual_fullDriver_firstPassage_endpoint_probability
    (lambda level : ℝ) (T : ℝ≥0) (hT : 0 < T) {B : Set ℝ} (hB : MeasurableSet B) :
    pathLaw {f : Path | (T : ℝ≥0∞) < firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) ∧
      f T+lambda*(T : ℝ)-(T : ℝ)^2/2 ∈ B} =
      ∫⁻ z in B, endpointKernel lambda level T z ∂gaussianReal 0 T := by
  have he : {f : Path | (T : ℝ≥0∞) < firstPassage level (stoppedParabolicPath lambda T f) ∧
      f T+lambda*(T : ℝ)-(T : ℝ)^2/2 ∈ B} =
      {f : Path | (T : ℝ≥0∞) < firstPassage level (BrownianPathReflectionLaw.driftPath lambda f) ∧
        f T+lambda*(T : ℝ)-(T : ℝ)^2/2 ∈ B} := by
    ext f
    simp only [mem_ofPred_eq,← mem_survival_iff_firstPassage,
      stoppedParabolicPath_eq_stopped_actual_drift,stopped_mem_survival_iff]
  rw [← he]
  exact actual_parabolic_firstPassage_endpoint_probability lambda level T hT hB

def killedEndpointLaw (lambda level : ℝ) (T : ℝ≥0) : Measure ℝ :=
  ((pathLaw.map (stoppedParabolicPath lambda T)).restrict (survival level T)).map (fun f : Path ↦ f T)

theorem killedEndpointLaw_eq_gaussian_withDensity
    (lambda level : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    killedEndpointLaw lambda level T = (gaussianReal 0 T).withDensity (endpointKernel lambda level T) := by
  ext B hB
  rw [killedEndpointLaw,Measure.map_apply (continuous_eval T).measurable hB,
    Measure.restrict_apply ((continuous_eval T).measurable hB),
    Measure.map_apply (measurable_stoppedParabolicPath lambda T)
      (((continuous_eval T).measurable hB).inter (measurableSet_survival level T)),
    withDensity_apply _ hB]
  simpa only [survivalEndpointEvent,inter_comm] using
    parabolic_survival_endpoint_probability lambda level T hT hB

theorem killedEndpointLaw_eq_volume_withDensity
    (lambda level : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    killedEndpointLaw lambda level T = volume.withDensity
      (fun z ↦ gaussianPDF 0 T z*endpointKernel lambda level T z) := by
  rw [killedEndpointLaw_eq_gaussian_withDensity lambda level T hT,
    gaussianReal_of_var_ne_zero 0 (ne_of_gt hT),
    ← withDensity_mul volume (measurable_gaussianPDF 0 T) (measurable_endpointKernel lambda level T)]
  rfl

end PerronWright.BrownianParabolicFirstPassageDensity
