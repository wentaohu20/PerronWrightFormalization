import PerronWright.Probability.ContinuousPathFirstPassage
import PerronWright.Probability.BrownianEndpointDriftTilt
import PerronWright.Probability.BrownianPinnedBridgeFiniteLaw
import PerronWright.Probability.BrownianBridgeAreaTiltPathLaw

/-! # Actual first-passage events as constrained bridge--Gaussian integrals

The full compact-open stopped bridge and the endpoint have a genuine
independent product law. Literal reconstruction identifies the stopped
Brownian path law, and hence first-passage survival events, with integrals
of actual pinned-bridge path constraints against the endpoint Gaussian.
The proved endpoint tilt supplies the corresponding drift identities.
No positive-excursion law, Palm deletion, or strong-Markov input is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageBridgeLaw

open BrownianPathLaw BrownianGaussianSkeleton BrownianPinnedBridge
open BrownianPinnedBridgeFiniteLaw BrownianBridgeAreaTiltPathLaw
open ContinuousPathFirstPassage

def pinnedLaw (T : ℝ≥0) : Measure Path := pathLaw.map (stoppedBridgePath T)

instance pinnedLaw_isProbability (T : ℝ≥0) : IsProbabilityMeasure (pinnedLaw T) :=
  Measure.isProbabilityMeasure_map (measurable_stoppedBridgePath T).aemeasurable

/-- This is independence of the actual continuous bridge path and endpoint,
in their genuine path Borel sigma algebra, proved from indexed independence. -/
theorem bridge_endpoint_jointLaw (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (fun f : Path ↦ (stoppedBridgePath T f,f T)) =
      (pinnedLaw T).prod (gaussianReal 0 T) := by
  let e := Prod.map rationalEval (id : ℝ → ℝ)
  have he : MeasurableEmbedding e :=
    rationalEval_measurableEmbedding.prodMap MeasurableEmbedding.id
  have hj : Measurable (fun f : Path ↦ (stoppedBridgePath T f,f T)) :=
    (measurable_stoppedBridgePath T).prodMk (continuous_eval T).measurable
  apply he.map_injective
  rw [Measure.map_map he.measurable hj,
    ← Measure.map_prod_map (pinnedLaw T) (gaussianReal 0 T)
      continuous_rationalEval.measurable measurable_id,Measure.map_id,
    pinnedLaw,Measure.map_map continuous_rationalEval.measurable (measurable_stoppedBridgePath T)]
  exact finite_endpoint_jointLaw_eq_prod T hT
    (fun q : RationalTime ↦ min (rationalTimeReal q) T) (fun _ ↦ min_le_right _ _)

theorem stoppedBridge_independent_endpoint (T : ℝ≥0) (hT : 0 < T) :
    IndepFun (stoppedBridgePath T) (fun f : Path ↦ f T) pathLaw := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_stoppedBridgePath T).aemeasurable (continuous_eval T).measurable.aemeasurable).mpr
  rw [(isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval T).map_eq]
  exact bridge_endpoint_jointLaw T hT

def reconstruct (T : ℝ≥0) (p : Path × ℝ) : Path :=
  ⟨fun t ↦ p.1 t+(min t T : ℝ≥0)/(T : ℝ)*p.2,
    (continuous_path p.1).add
      (((NNReal.continuous_coe.comp (continuous_id.min continuous_const)).div_const (T : ℝ)).mul
        continuous_const)⟩

@[simp] theorem reconstruct_eval (T t : ℝ≥0) (p : Path × ℝ) :
    reconstruct T p t = p.1 t+min (t : ℝ) (T : ℝ)/(T : ℝ)*p.2 := by
  change p.1 t+(min t T : ℝ≥0)/(T : ℝ)*p.2 = _
  rw [NNReal.coe_min]

theorem continuous_reconstruct (T : ℝ≥0) : Continuous (reconstruct T) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_fst.fst.eval continuous_snd).add
    (((NNReal.continuous_coe.comp (continuous_snd.min continuous_const)).div_const (T : ℝ)).mul
      continuous_fst.snd)

theorem measurable_reconstruct (T : ℝ≥0) : Measurable (reconstruct T) :=
  (continuous_reconstruct T).measurable

theorem reconstruct_bridge_endpoint (T : ℝ≥0) (f : Path) :
    reconstruct T (stoppedBridgePath T f,f T) = BrownianEndpointDriftTilt.stoppedPath T f := by
  apply ContinuousMap.ext
  intro t
  change bridge T (min t T) f+(min t T : ℝ≥0)/(T : ℝ)*f T = f (min t T)
  unfold bridge
  ring

theorem stoppedPathLaw_eq_bridgeGaussian (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (BrownianEndpointDriftTilt.stoppedPath T) =
      ((pinnedLaw T).prod (gaussianReal 0 T)).map (reconstruct T) := by
  rw [← bridge_endpoint_jointLaw T hT,
    Measure.map_map (measurable_reconstruct T)
      ((measurable_stoppedBridgePath T).prodMk (continuous_eval T).measurable)]
  congr 1
  exact (funext (reconstruct_bridge_endpoint T)).symm

/-- Exact Tonelli identity for every nonnegative Borel stopped-path test. -/
theorem lintegral_stoppedPath_eq_bridgeGaussian (T : ℝ≥0) (hT : 0 < T)
    {Ψ : Path → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ f, Ψ (BrownianEndpointDriftTilt.stoppedPath T f) ∂pathLaw) =
      ∫⁻ z, ∫⁻ g, Ψ (reconstruct T (g,z)) ∂pinnedLaw T ∂gaussianReal 0 T := by
  rw [← lintegral_map hΨ (BrownianEndpointDriftTilt.measurable_stoppedPath T),
    stoppedPathLaw_eq_bridgeGaussian T hT,lintegral_map hΨ (measurable_reconstruct T)]
  exact lintegral_prod_symm _ (hΨ.comp (measurable_reconstruct T)).aemeasurable

theorem stopped_mem_survival_iff (level : ℝ) (T : ℝ≥0) (f : Path) :
    BrownianEndpointDriftTilt.stoppedPath T f ∈ survival level T ↔ f ∈ survival level T := by
  simp only [mem_survival_iff]
  constructor <;> intro h t ht
  · simpa only [BrownianEndpointDriftTilt.stoppedPath_eval,min_eq_left ht] using h t ht
  · simpa only [BrownianEndpointDriftTilt.stoppedPath_eval,min_eq_left ht] using h t ht

def bridgeConstraint (level : ℝ) (T : ℝ≥0) (z : ℝ) : Set Path :=
  {g | reconstruct T (g,z) ∈ survival level T}

theorem mem_bridgeConstraint_iff (level : ℝ) (T : ℝ≥0) (z : ℝ) (g : Path) :
    g ∈ bridgeConstraint level T z ↔
      ∀ t : ℝ≥0, t ≤ T → level < g t+(t : ℝ)/(T : ℝ)*z := by
  change reconstruct T (g,z) ∈ survival level T ↔ _
  rw [mem_survival_iff]
  constructor <;> intro h t ht
  · simpa only [reconstruct_eval,min_eq_left (show (t : ℝ) ≤ T from ht)] using h t ht
  · simpa only [reconstruct_eval,min_eq_left (show (t : ℝ) ≤ T from ht)] using h t ht

theorem measurableSet_bridgeConstraint (level : ℝ) (T : ℝ≥0) (z : ℝ) :
    MeasurableSet (bridgeConstraint level T z) :=
  ((measurable_reconstruct T).comp (measurable_id.prodMk measurable_const))
    (measurableSet_survival level T)

theorem measurable_bridgeConstraint_probability (level : ℝ) (T : ℝ≥0) :
    Measurable (fun z : ℝ ↦ pinnedLaw T (bridgeConstraint level T z)) := by
  exact measurable_measure_prodMk_right
    ((measurable_reconstruct T) (measurableSet_survival level T))

def survivalEndpointEvent (level : ℝ) (T : ℝ≥0) (B : Set ℝ) : Set Path :=
  survival level T ∩ (fun f : Path ↦ f T) ⁻¹' B

theorem measurableSet_survivalEndpointEvent (level : ℝ) (T : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) : MeasurableSet (survivalEndpointEvent level T B) :=
  (measurableSet_survival level T).inter ((continuous_eval T).measurable hB)

theorem survival_endpoint_probability (level : ℝ) (T : ℝ≥0) (hT : 0 < T)
    {B : Set ℝ} (hB : MeasurableSet B) :
    pathLaw (survivalEndpointEvent level T B) =
      ∫⁻ z in B, pinnedLaw T (bridgeConstraint level T z) ∂gaussianReal 0 T := by
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
  calc
    _ = (pathLaw.map (fun f : Path ↦ (stoppedBridgePath T f,f T))) A := by
      rw [Measure.map_apply hj hA,he]
    _ = ((pinnedLaw T).prod (gaussianReal 0 T)) A := by rw [bridge_endpoint_jointLaw T hT]
    _ = ∫⁻ z, pinnedLaw T ((fun g : Path ↦ (g,z)) ⁻¹' A) ∂gaussianReal 0 T :=
      Measure.prod_apply_symm hA
    _ = _ := by
      rw [← lintegral_indicator hB]
      apply lintegral_congr
      intro z
      have hzset : (fun g : Path ↦ (g,z)) ⁻¹' A =
          if z ∈ B then bridgeConstraint level T z else ∅ := by
        ext g
        by_cases hz : z ∈ B <;> simp [A,bridgeConstraint,hz]
      rw [hzset]
      by_cases hz : z ∈ B
      · simp only [if_pos hz,indicator_of_mem hz]
      · simp only [if_neg hz,indicator_of_notMem hz,measure_empty]

/-- Exact genuine first-passage survival/endpoint formula; the bridge
probabilities on the right are actual path-law constraint probabilities. -/
theorem firstPassage_survival_endpoint_probability (level : ℝ) (T : ℝ≥0) (hT : 0 < T)
    {B : Set ℝ} (hB : MeasurableSet B) :
    pathLaw {f : Path | (T : ℝ≥0∞) < firstPassage level f ∧ f T ∈ B} =
      ∫⁻ z in B, pinnedLaw T (bridgeConstraint level T z) ∂gaussianReal 0 T := by
  have he : {f : Path | (T : ℝ≥0∞) < firstPassage level f ∧ f T ∈ B} =
      survivalEndpointEvent level T B := by
    ext f
    simp only [mem_ofPred_eq,survivalEndpointEvent,mem_inter_iff,mem_preimage,
      mem_survival_iff_firstPassage]
  rw [he]
  exact survival_endpoint_probability level T hT hB

theorem firstPassage_survival_probability (level : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | (T : ℝ≥0∞) < firstPassage level f} =
      ∫⁻ z, pinnedLaw T (bridgeConstraint level T z) ∂gaussianReal 0 T := by
  simpa only [mem_univ,and_true,setLIntegral_univ] using
    firstPassage_survival_endpoint_probability level T hT MeasurableSet.univ

theorem stoppedBridge_driftPath (T : ℝ≥0) (hT : 0 < T) (u : ℝ) (f : Path) :
    stoppedBridgePath T (BrownianEndpointDriftTilt.driftPath T u f) = stoppedBridgePath T f := by
  have hne : (T : ℝ) ≠ 0 := ne_of_gt (show 0 < (T : ℝ) from hT)
  apply ContinuousMap.ext
  intro t
  change bridge T (min t T) (BrownianEndpointDriftTilt.driftPath T u f) = bridge T (min t T) f
  unfold bridge
  have hmin : ((min t T : ℝ≥0) : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast (min_le_right t T)
  rw [BrownianEndpointDriftTilt.driftPath_eval,BrownianEndpointDriftTilt.driftPath_eval,
    min_eq_left hmin,min_self]
  field_simp [hne]
  ring

/-- Endpoint weighting leaves the actual whole pinned bridge law unchanged
and shifts its independent endpoint to the true Gaussian mean uT. -/
theorem tilted_bridge_endpoint_jointLaw (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (BrownianEndpointDriftTilt.tiltedLaw T u).map
      (fun f : Path ↦ (stoppedBridgePath T f,f T)) =
      (pinnedLaw T).prod (gaussianReal (u*(T : ℝ)) T) := by
  have hj : Measurable (fun f : Path ↦ (stoppedBridgePath T f,f T)) :=
    (measurable_stoppedBridgePath T).prodMk (continuous_eval T).measurable
  have ha : Measurable (fun z : ℝ ↦ z+u*(T : ℝ)) := measurable_id.add_const _
  have hm : Measurable (Prod.map (id : Path → Path) (fun z : ℝ ↦ z+u*(T : ℝ))) :=
    measurable_id.prodMap ha
  rw [BrownianEndpointDriftTilt.pathLaw_endpointTilt_eq_drift T hT u,Measure.map_map hj
    (BrownianEndpointDriftTilt.measurable_driftPath T u)]
  have he : (fun f : Path ↦ (stoppedBridgePath T f,f T)) ∘
      BrownianEndpointDriftTilt.driftPath T u =
      Prod.map (id : Path → Path) (fun z : ℝ ↦ z+u*(T : ℝ)) ∘
        (fun f : Path ↦ (stoppedBridgePath T f,f T)) := by
    funext f
    simp only [Function.comp_def,Prod.map_apply,id_eq,stoppedBridge_driftPath T hT,
      BrownianEndpointDriftTilt.driftPath_eval,min_self]
  rw [he,← Measure.map_map hm hj,bridge_endpoint_jointLaw T hT,
    ← Measure.map_prod_map (pinnedLaw T) (gaussianReal 0 T) measurable_id ha,
    Measure.map_id,gaussianReal_map_add_const,zero_add]

theorem tilted_firstPassage_survival_endpoint_probability
    (level : ℝ) (T : ℝ≥0) (hT : 0 < T) (u : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (BrownianEndpointDriftTilt.tiltedLaw T u)
      {f : Path | (T : ℝ≥0∞) < firstPassage level f ∧ f T ∈ B} =
      ∫⁻ z in B, pinnedLaw T (bridgeConstraint level T z) ∂gaussianReal (u*(T : ℝ)) T := by
  let A : Set (Path × ℝ) := {p | reconstruct T p ∈ survival level T ∧ p.2 ∈ B}
  have hA : MeasurableSet A :=
    ((measurable_reconstruct T) (measurableSet_survival level T)).inter (measurable_snd hB)
  have hj : Measurable (fun f : Path ↦ (stoppedBridgePath T f,f T)) :=
    (measurable_stoppedBridgePath T).prodMk (continuous_eval T).measurable
  have he : (fun f : Path ↦ (stoppedBridgePath T f,f T)) ⁻¹' A =
      {f : Path | (T : ℝ≥0∞) < firstPassage level f ∧ f T ∈ B} := by
    ext f
    change (reconstruct T (stoppedBridgePath T f,f T) ∈ survival level T ∧ f T ∈ B) ↔
      ((T : ℝ≥0∞) < firstPassage level f ∧ f T ∈ B)
    rw [reconstruct_bridge_endpoint,stopped_mem_survival_iff,mem_survival_iff_firstPassage]
  calc
    _ = ((BrownianEndpointDriftTilt.tiltedLaw T u).map
      (fun f : Path ↦ (stoppedBridgePath T f,f T))) A := by
      rw [Measure.map_apply hj hA,he]
    _ = ((pinnedLaw T).prod (gaussianReal (u*(T : ℝ)) T)) A := by
      rw [tilted_bridge_endpoint_jointLaw T hT u]
    _ = ∫⁻ z, pinnedLaw T ((fun g : Path ↦ (g,z)) ⁻¹' A) ∂gaussianReal (u*(T : ℝ)) T :=
      Measure.prod_apply_symm hA
    _ = _ := by
      rw [← lintegral_indicator hB]
      apply lintegral_congr
      intro z
      have hzset : (fun g : Path ↦ (g,z)) ⁻¹' A =
          if z ∈ B then bridgeConstraint level T z else ∅ := by
        ext g
        by_cases hz : z ∈ B <;> simp [A,bridgeConstraint,hz]
      rw [hzset]
      by_cases hz : z ∈ B
      · simp only [if_pos hz,indicator_of_mem hz]
      · simp only [if_neg hz,indicator_of_notMem hz,measure_empty]

theorem drift_firstPassage_survival_endpoint_probability
    (level : ℝ) (T : ℝ≥0) (hT : 0 < T) (u : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    pathLaw {f : Path | (T : ℝ≥0∞) < firstPassage level (BrownianEndpointDriftTilt.driftPath T u f) ∧
      f T+u*(T : ℝ) ∈ B} =
      ∫⁻ z in B, pinnedLaw T (bridgeConstraint level T z) ∂gaussianReal (u*(T : ℝ)) T := by
  have hE : MeasurableSet {f : Path | (T : ℝ≥0∞) < firstPassage level f ∧ f T ∈ B} := by
    have he : {f : Path | (T : ℝ≥0∞) < firstPassage level f ∧ f T ∈ B} =
        survivalEndpointEvent level T B := by
      ext f
      simp only [mem_ofPred_eq,survivalEndpointEvent,mem_inter_iff,mem_preimage,
        mem_survival_iff_firstPassage]
    rw [he]
    exact measurableSet_survivalEndpointEvent level T hB
  have h := tilted_firstPassage_survival_endpoint_probability level T hT u hB
  rw [BrownianEndpointDriftTilt.pathLaw_endpointTilt_eq_drift T hT u,
    Measure.map_apply (BrownianEndpointDriftTilt.measurable_driftPath T u) hE] at h
  have he : BrownianEndpointDriftTilt.driftPath T u ⁻¹'
      {f : Path | (T : ℝ≥0∞) < firstPassage level f ∧ f T ∈ B} =
      {f : Path | (T : ℝ≥0∞) < firstPassage level (BrownianEndpointDriftTilt.driftPath T u f) ∧
        f T+u*(T : ℝ) ∈ B} := by
    ext f
    change ((T : ℝ≥0∞) < firstPassage level (BrownianEndpointDriftTilt.driftPath T u f) ∧
      BrownianEndpointDriftTilt.driftPath T u f T ∈ B) ↔
      ((T : ℝ≥0∞) < firstPassage level (BrownianEndpointDriftTilt.driftPath T u f) ∧
        f T+u*(T : ℝ) ∈ B)
    rw [BrownianEndpointDriftTilt.driftPath_eval,min_self]
  rw [he] at h
  exact h

theorem ae_firstPassage_pos (level : ℝ) (hlevel : level < 0) :
    ∀ᵐ f : Path ∂pathLaw, 0 < firstPassage level f := by
  filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
  by_contra h
  have hm := (firstPassage_le_iff_minimum level f 0).mp (le_of_not_gt h)
  simp only [ContinuousPathReflection.runningMinimum_zero,hf] at hm
  exact (not_le_of_gt hlevel) hm

theorem ae_finite_firstPassage_exact_level (level : ℝ) (hlevel : level < 0) :
    ∀ᵐ f : Path ∂pathLaw, firstPassage level f ≠ ⊤ →
      f (firstPassage level f).toNNReal = level := by
  filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
  intro hfin
  exact firstPassage_exact_level level f (hf ▸ hlevel) hfin

end PerronWright.BrownianFirstPassageBridgeLaw
