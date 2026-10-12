import PerronWright.Probability.BrownianBridgeMinimumTimeConditioning
import PerronWright.Probability.BrownianBridgeUniformSmallTime
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Genuine small-minimum-time conditioned bridge weak limit

The actual conditioning on the minimum time in (0,ε] has the proved
inverse uniform-product representation. Fixed-product dominated
convergence and genuine joint cyclic continuity show that these laws
converge to the actual minimum-shift law. This is a different conditioning
from the above-negative-barrier positive bridge, so no Vervaat identity
is inferred.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeMinimumTimeWeakLimit

open BrownianPathLaw BrownianBridgeMinimumShift BrownianBridgeMinimumReconstruction
open BrownianBridgeMinimumOccupationBias BrownianBridgeMinimumTimeConditioning
open BrownianBridgeCyclicPath BrownianBridgeCycleKernel BrownianCircleUniformTime
open BrownianBridgeUniformSmallTime

theorem cyclicBridgePath_terminal_offset (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    cyclicBridgePath T hT T f = stoppedClosedBridgePath T f := by
  apply ContinuousMap.ext
  intro t
  change closedBridge T (cycleTime T T (min t T)) f-closedBridge T T f = _
  rw [closedBridge_endpoint T hT f,sub_zero]
  by_cases hz : min t T = 0
  · rw [hz,cycleTime_zero T T le_rfl,closedBridge_endpoint T hT f]
    change (0 : ℝ) = closedBridge T (min t T) f
    rw [hz,closedBridge_zero]
  · have hp : 0 < min t T := pos_iff_ne_zero.mpr hz
    have hn : ¬ T+min t T ≤ T := by linarith
    rw [cycleTime,if_neg hn,add_tsub_cancel_left]
    rfl

theorem cyclicBridgePath_terminal_minimumShift (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    cyclicBridgePath T hT T (minimumShiftPath T hT f) = minimumShiftPath T hT f := by
  rw [cyclicBridgePath_terminal_offset]
  apply ContinuousMap.ext
  intro t
  change closedBridge T (min t T) (minimumShiftPath T hT f) = minimumShiftPath T hT f t
  rw [closedBridge_eq_of_endpoints T _ _ (minimumShiftPath_zero T hT f)
    (minimumShiftPath_endpoint T hT f)]
  rcases le_total t T with ht | ht
  · rw [min_eq_left ht]
  · rw [min_eq_right ht,minimumShiftPath_endpoint,
      minimumShiftPath_stopped T hT f t ht]

def unitPairLaw (T : ℝ≥0) (hT : 0 < T) : Measure (ℝ × Path) :=
  (intervalUniform 1).prod (minimumShiftLaw T hT)

theorem unitPairLaw_isProbability (T : ℝ≥0) (hT : 0 < T) :
    IsProbabilityMeasure (unitPairLaw T hT) := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  unfold unitPairLaw
  infer_instance

def smallTimePath (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (p : ℝ × Path) : Path :=
  inversePath T hT (ε*p.1,p.2)

theorem continuous_smallTimePath (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) :
    Continuous (smallTimePath T hT ε) :=
  (continuous_inversePath T hT).comp ((continuous_fst.const_mul ε).prodMk continuous_snd)

def mixtureLaw (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) : Measure Path :=
  (unitPairLaw T hT).map (smallTimePath T hT ε)

theorem mixtureLaw_isProbability (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) :
    IsProbabilityMeasure (mixtureLaw T hT ε) := by
  let := unitPairLaw_isProbability T hT
  exact Measure.isProbabilityMeasure_map (continuous_smallTimePath T hT ε).measurable.aemeasurable

theorem mixtureLaw_eq_actual_smallMinimumLaw (T : ℝ≥0) (hT : 0 < T) (ε : ℝ)
    (hε : 0 < ε) (hεT : ε ≤ (T : ℝ)) : mixtureLaw T hT ε = smallMinimumLaw T ε := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  rw [smallMinimumLaw_eq_inverse_uniform_product T hT ε hε hεT]
  unfold mixtureLaw unitPairLaw
  change (((intervalUniform 1).prod (minimumShiftLaw T hT)).map
    (inversePath T hT ∘ Prod.map (fun s : ℝ ↦ ε*s) id)) = _
  rw [← Measure.map_map (continuous_inversePath T hT).measurable
    ((measurable_const_mul ε).prodMap measurable_id),
    ← Measure.map_prod_map _ _ (measurable_const_mul ε) measurable_id,
    intervalUniform_one_map_mul ε hε,Measure.map_id]

theorem mixtureLaw_zero (T : ℝ≥0) (hT : 0 < T) :
    mixtureLaw T hT 0 = minimumShiftLaw T hT := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hc : MeasurableSet {e : Path | cyclicBridgePath T hT T e = e} :=
    (isClosed_eq
      ((BrownianBridgeMinimumShiftContinuity.continuous_joint_cyclicBridgePath T hT).comp
        (continuous_const.prodMk continuous_id)) continuous_id).measurableSet
  have he : ∀ᵐ e ∂minimumShiftLaw T hT, cyclicBridgePath T hT T e = e := by
    apply (ae_map_iff (measurable_minimumShiftPath T hT).aemeasurable hc).mpr
    exact ae_of_all _ (cyclicBridgePath_terminal_minimumShift T hT)
  have hp : ∀ᵐ p ∂unitPairLaw T hT, smallTimePath T hT 0 p = p.2 := by
    have hs : (unitPairLaw T hT).map Prod.snd = minimumShiftLaw T hT := by
      rw [unitPairLaw,Measure.map_snd_prod,measure_univ,one_smul]
    rw [← hs] at he
    have he' := (ae_map_iff measurable_snd.aemeasurable hc).mp he
    filter_upwards [he'] with p hp
    simpa only [smallTimePath,inversePath,zero_mul,reverseTime,sub_zero,Real.toNNReal_coe] using hp
  rw [mixtureLaw,Measure.map_congr hp,unitPairLaw,Measure.map_snd_prod,measure_univ,one_smul]

def mixtureProbability (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) : ProbabilityMeasure Path :=
  ⟨mixtureLaw T hT ε,mixtureLaw_isProbability T hT ε⟩

def minimumShiftProbability (T : ℝ≥0) (hT : 0 < T) : ProbabilityMeasure Path :=
  ⟨minimumShiftLaw T hT,inferInstance⟩

theorem tendsto_mixtureProbability (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (mixtureProbability T hT) (𝓝 0) (𝓝 (minimumShiftProbability T hT)) := by
  have hz : mixtureProbability T hT 0 = minimumShiftProbability T hT :=
    Subtype.ext (mixtureLaw_zero T hT)
  rw [← hz]
  apply ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mpr
  intro Ψ
  let := unitPairLaw_isProbability T hT
  have hΨ : Measurable (fun f ↦ (Ψ f : ℝ≥0∞)) :=
    ENNReal.continuous_coe.measurable.comp Ψ.continuous.measurable
  have he (ε : ℝ) : (∫⁻ f, (Ψ f : ℝ≥0∞) ∂mixtureLaw T hT ε) =
      ∫⁻ p, (Ψ (smallTimePath T hT ε p) : ℝ≥0∞) ∂unitPairLaw T hT :=
    lintegral_map hΨ (continuous_smallTimePath T hT ε).measurable
  change Tendsto (fun ε ↦ ∫⁻ f, (Ψ f : ℝ≥0∞) ∂mixtureLaw T hT ε) (𝓝 0)
    (𝓝 (∫⁻ f, (Ψ f : ℝ≥0∞) ∂mixtureLaw T hT 0))
  simp_rw [he]
  apply tendsto_lintegral_filter_of_dominated_convergence (fun _ ↦ (nndist Ψ 0 : ℝ≥0∞))
  · exact Eventually.of_forall (fun ε ↦ hΨ.comp (continuous_smallTimePath T hT ε).measurable)
  · exact Eventually.of_forall (fun ε ↦ ae_of_all _ (fun p ↦
      ENNReal.coe_le_coe.mpr (BoundedContinuousFunction.NNReal.upper_bound Ψ _)))
  · rw [lintegral_const,measure_univ,mul_one]
    exact ENNReal.coe_ne_top
  · apply ae_of_all
    intro p
    have hp : Continuous (fun ε : ℝ ↦ smallTimePath T hT ε p) :=
      (continuous_inversePath T hT).comp ((continuous_id.mul_const p.1).prodMk continuous_const)
    exact ((ENNReal.continuous_coe.comp Ψ.continuous).comp hp).continuousAt.tendsto

theorem tendsto_actual_smallMinimumLaw_bounded_integral (T : ℝ≥0) (hT : 0 < T)
    (Ψ : Path →ᵇ ℝ) :
    Tendsto (fun ε : ℝ ↦ ∫ f, Ψ f ∂smallMinimumLaw T ε) (𝓝[>] 0)
      (𝓝 (∫ f, Ψ f ∂minimumShiftLaw T hT)) := by
  have he : Tendsto (fun ε : ℝ ↦ ∫ f, Ψ f ∂mixtureLaw T hT ε) (𝓝[>] 0)
      (𝓝 (∫ f, Ψ f ∂minimumShiftLaw T hT)) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (tendsto_mixtureProbability T hT) Ψ).mono_left nhdsWithin_le_nhds
  have hlt : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < (T : ℝ) :=
    (tendsto_id.mono_right nhdsWithin_le_nhds).eventually_lt_const hT
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin,hlt] with ε hε hεT
  rw [mixtureLaw_eq_actual_smallMinimumLaw T hT ε hε hεT.le]

def smallMinimumProbability (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) : ProbabilityMeasure Path :=
  if h : 0 < ε ∧ ε ≤ (T : ℝ) then
    ⟨smallMinimumLaw T ε,smallMinimumLaw_isProbability T hT ε h.1 h.2⟩
  else minimumShiftProbability T hT

theorem smallMinimumProbability_toMeasure (T : ℝ≥0) (hT : 0 < T) (ε : ℝ)
    (hε : 0 < ε) (hεT : ε ≤ (T : ℝ)) :
    (smallMinimumProbability T hT ε : Measure Path) = smallMinimumLaw T ε := by
  have hv : 0 < ε ∧ ε ≤ (T : ℝ) := ⟨hε,hεT⟩
  simp only [smallMinimumProbability,dif_pos hv]
  rfl

theorem tendsto_actual_smallMinimumProbability (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (smallMinimumProbability T hT) (𝓝[>] 0)
      (𝓝 (minimumShiftProbability T hT)) := by
  apply ((tendsto_mixtureProbability T hT).mono_left nhdsWithin_le_nhds).congr'
  have hlt : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < (T : ℝ) :=
    (tendsto_id.mono_right nhdsWithin_le_nhds).eventually_lt_const hT
  filter_upwards [self_mem_nhdsWithin,hlt] with ε hε hεT
  apply Subtype.ext
  change mixtureLaw T hT ε = (smallMinimumProbability T hT ε : Measure Path)
  rw [smallMinimumProbability_toMeasure T hT ε hε hεT.le,
    mixtureLaw_eq_actual_smallMinimumLaw T hT ε hε hεT.le]

end PerronWright.BrownianBridgeMinimumTimeWeakLimit
