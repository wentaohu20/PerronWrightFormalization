import PerronWright.Probability.BrownianPositiveBridgeMultiPointCoordinates

/-! # Actual multi-coordinate bridge--killed endpoint disintegration

All internal coordinates are retained in the genuine killed head law.
The last exit density is integrated against that actual head law, and
the proved bridge/endpoint product identifies the pinned constraints.
Monotonicity and continuous exit densities identify every endpoint.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeMultiPointSource

open BrownianPathLaw ContinuousPathFirstPassage BrownianKilledSemigroup
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalLaw
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalDensity
open BrownianPositiveKilledEndpoint BrownianPositiveKilledKernel BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeFiniteDimensionalSource BrownianPositiveBridgeFiniteDimensionalOnePoint
open BrownianPositiveBridgeMultiPointCoordinates BrownianBridgeSurvivalPointwise

theorem transitionLaw_sub_event_density (a x : ℝ) (t : ℝ≥0) (ht : 0 < t)
    {B : Set ℝ} (hB : MeasurableSet B) :
    transitionLaw 0 t x ((fun y : ℝ ↦ y-a) ⁻¹' B) = ∫⁻ z in B, density x t (z+a) := by
  have hm : Measurable (fun y : ℝ ↦ y-a) := by fun_prop
  have he := transitionLaw_shift a (x-a) t
  rw [sub_add_cancel] at he
  rw [transitionLaw_zero_eq_law,← Measure.map_apply hm hB,← he,
    transitionLaw_apply_density a (x-a) t ht hB,sub_add_cancel]

theorem endpointLaw_eq_exitIntegral_density (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0)
    (hgap : 0 < gaps n) (cuts : FreeVector n) :
    endpointLaw a (sampleTime gaps (n+1)) (internalTimes n gaps) cuts =
      volume.withDensity (BrownianPositiveBridgeMultiPointCoordinates.exitIntegral n a gaps cuts) := by
  ext B hB
  let D : Set (EndpointVector n × ℝ) :=
    {p | dropInitial n p.1 ∈ orthant n cuts ∧ p.2-a ∈ B}
  have hD : MeasurableSet D :=
    (((continuous_dropInitial n).comp continuous_fst).measurable (measurableSet_orthant n cuts)).inter
      ((measurable_snd.sub_const a) hB)
  have he : (fun f : Path ↦ f (sampleTime gaps (n+1))) ⁻¹' B ∩
      (survival (-a) (sampleTime gaps (n+1)) ∩
        {f | ∀ i : Fin n, cuts i < f (min (internalTimes n gaps i) (sampleTime gaps (n+1)))+a}) =
      {f : Path | f ∈ survival (0-a) (sampleTime gaps (n+1)) ∧
        (endpointTuple n a gaps f,a+f (sampleTime gaps (n+1))) ∈ D} := by
    ext f
    simp only [D,orthant,mem_inter_iff,mem_preimage,mem_ofPred_eq,zero_sub]
    have hv : (∀ i : Fin n, cuts i < f (min (internalTimes n gaps i) (sampleTime gaps (n+1)))+a) ↔
        ∀ i : Fin n, cuts i < dropInitial n (endpointTuple n a gaps f) i := by
      apply forall_congr'
      intro i
      rw [min_eq_left (internalTimes_le_final n gaps i)]
      change (cuts i < f (sampleTime gaps (i.val+1))+a) ↔
        cuts i < a+f (sampleTime gaps i.succ.val)
      simp only [Fin.val_succ,add_comm a]
    rw [hv]
    have hf : a+f (sampleTime gaps (n+1))-a = f (sampleTime gaps (n+1)) := by ring
    rw [hf]
    tauto
  rw [endpointLaw,Measure.map_apply (continuous_eval _).measurable hB,
    Measure.restrict_apply ((continuous_eval _).measurable hB),he,
    ← actualNextPairLaw_apply 0 a gaps n hD,actualNextPairLaw_eq_compProd,
    Measure.compProd_apply hD,actualTupleLaw_eq_chainLaw,withDensity_apply _ hB]
  have hJ : Measurable (fun p : FreeVector n × ℝ ↦ density (lastState n a p.1) (gaps n) (p.2+a)) := by
    have hp : Measurable (fun p : FreeVector n × ℝ ↦ (lastState n a p.1,p.2+a)) :=
      ((continuous_lastState n a).measurable.comp measurable_fst).prodMk (measurable_snd.add_const a)
    have hc := (measurable_joint_density (gaps n)).comp hp
    simpa only [Function.comp_def] using hc
  let F : FreeVector n → ℝ≥0∞ := fun v ↦ ∫⁻ z in B, density (lastState n a v) (gaps n) (z+a)
  have hF : Measurable F := hJ.lintegral_prod_right'
  calc
    _ = ∫⁻ v, (orthant n cuts).indicator F (dropInitial n v) ∂chainLaw 0 a gaps n := by
      apply lintegral_congr_ae
      filter_upwards [chainLaw_initial_ae a gaps n] with v hv
      have hset : (fun y : ℝ ↦ (v,y)) ⁻¹' D =
          if dropInitial n v ∈ orthant n cuts then (fun y : ℝ ↦ y-a) ⁻¹' B else ∅ := by
        ext y
        by_cases hcut : dropInitial n v ∈ orthant n cuts <;> simp [D,hcut]
      rw [hset,endpointKernel_apply]
      by_cases hcut : dropInitial n v ∈ orthant n cuts
      · rw [if_pos hcut,indicator_of_mem hcut,transitionLaw_sub_event_density a _ _ hgap hB,
          ← lastState_dropInitial n a v hv]
      · rw [if_neg hcut,measure_empty,indicator_of_notMem hcut]
    _ = ∫⁻ v in orthant n cuts, F v ∂freeTupleLaw a gaps n := by
      rw [freeTupleLaw_eq_chain_map,setLIntegral_map (measurableSet_orthant n cuts) hF
        (continuous_dropInitial n).measurable,← lintegral_indicator
          ((continuous_dropInitial n).measurable (measurableSet_orthant n cuts))]
      apply lintegral_congr
      intro v
      by_cases hv : dropInitial n v ∈ orthant n cuts
      · rw [indicator_of_mem hv,indicator_of_mem (show v ∈ dropInitial n ⁻¹' orthant n cuts from hv)]
      · rw [indicator_of_notMem hv,indicator_of_notMem (show v ∉ dropInitial n ⁻¹' orthant n cuts from hv)]
    _ = ∫⁻ z in B, ∫⁻ v, density (lastState n a v) (gaps n) (z+a) ∂headLaw n a gaps cuts := by
      exact lintegral_lintegral_swap (μ := headLaw n a gaps cuts) (ν := volume.restrict B) hJ.aemeasurable
    _ = ∫⁻ z in B, BrownianPositiveBridgeMultiPointCoordinates.exitIntegral n a gaps cuts z := by
      apply setLIntegral_congr_fun hB
      intro z _
      have hm : Measurable (fun x : ℝ ↦ density x (gaps n) (z+a)) := by
        have hp : Measurable (fun x : ℝ ↦ (x,z+a)) := measurable_id.prodMk measurable_const
        simpa only [Function.comp_def] using (measurable_joint_density (gaps n)).comp hp
      rw [BrownianPositiveBridgeMultiPointCoordinates.exitIntegral,exitHeadLaw,
        lintegral_map hm (continuous_lastState n a).measurable]

theorem probability_eq_exitRatio (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0)
    (hgap : 0 < gaps n) (cuts : FreeVector n) (z : ℝ) :
    probability a (sampleTime gaps (n+1)) (internalTimes n gaps) cuts z =
      BrownianPositiveBridgeMultiPointCoordinates.exitRatio n a gaps cuts z := by
  have hT := finalTime_pos n gaps hgap
  let p := probability a (sampleTime gaps (n+1)) (internalTimes n gaps) cuts
  have hp : Measurable p := measurable_probability _ _ _ _
  have hd := (endpointLaw_eq_bridge_density a _ hT (internalTimes n gaps) cuts).symm.trans
    (endpointLaw_eq_exitIntegral_density n a gaps hgap cuts)
  rw [gaussianReal_of_var_ne_zero 0 (ne_of_gt hT),← withDensity_mul volume
    (measurable_gaussianPDF 0 (sampleTime gaps (n+1))) hp] at hd
  have hae : (fun z ↦ gaussianPDF 0 (sampleTime gaps (n+1)) z*p z) =ᵐ[volume]
      BrownianPositiveBridgeMultiPointCoordinates.exitIntegral n a gaps cuts :=
    (withDensity_eq_iff_of_sigmaFinite
      ((measurable_gaussianPDF 0 (sampleTime gaps (n+1))).mul hp).aemeasurable
      (BrownianPositiveBridgeMultiPointCoordinates.continuous_exitIntegral n a gaps hgap cuts).measurable.aemeasurable).mp hd
  have hratio : p =ᵐ[volume] BrownianPositiveBridgeMultiPointCoordinates.exitRatio n a gaps cuts := by
    filter_upwards [hae] with w hw
    have hpos : gaussianPDF 0 (sampleTime gaps (n+1)) w ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr
      (gaussianPDFReal_pos 0 _ w (ne_of_gt hT))
    have hfin : gaussianPDF 0 (sampleTime gaps (n+1)) w ≠ ∞ := ENNReal.ofReal_ne_top
    unfold BrownianPositiveBridgeMultiPointCoordinates.exitRatio
    rw [← hw,mul_comm,ENNReal.mul_div_cancel_right hpos hfin]
  exact congrFun (monotone_eq_of_ae_eq volume (monotone_probability a _ (internalTimes n gaps) cuts)
    (BrownianPositiveBridgeMultiPointCoordinates.continuous_exitRatio n a gaps hgap cuts) hratio) z

theorem positiveBridgeLaw_orthant (n : ℕ) (a : ℝ) (ha : 0 < a) (gaps : ℕ → ℝ≥0)
    (hgap : 0 < gaps n) (cuts : FreeVector n) :
    positiveBridgeLaw a (sampleTime gaps (n+1)) ((internalEval n gaps) ⁻¹' orthant n cuts) =
      (BrownianPositiveBridgeFiniteDimensionalLaw.normalization a (sampleTime gaps (n+1)))⁻¹*
        BrownianPositiveBridgeMultiPointCoordinates.exitIntegral n a gaps cuts 0/
          gaussianPDF 0 (sampleTime gaps (n+1)) 0 := by
  have he : (internalEval n gaps) ⁻¹' orthant n cuts = lowerCuts (internalTimes n gaps) cuts := rfl
  rw [he,positiveBridgeLaw_lowerCuts a ha _ (finalTime_pos n gaps hgap),
    probability_eq_exitRatio n a gaps hgap cuts 0]
  unfold BrownianPositiveBridgeMultiPointCoordinates.exitRatio BrownianPositiveBridgeFiniteDimensionalLaw.normalization
  simp only [div_eq_mul_inv,mul_assoc]

end PerronWright.BrownianPositiveBridgeMultiPointSource
