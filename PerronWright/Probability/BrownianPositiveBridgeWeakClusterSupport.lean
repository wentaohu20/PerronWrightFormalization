import PerronWright.Probability.BrownianPositiveBridgePathTightness
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.DiracProba

/-! # Actual positive-bridge weak clusters have zero stopped endpoints

The moving endpoint Dirac laws are treated by weak convergence, not by
setwise convergence. Closed stopped support passes through portmanteau.
All input path laws are the genuine conditioned pinned-bridge laws.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeWeakClusterSupport

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianPositiveBridgeStoppedSupport

/-- A total probability-valued version of the actual positive-endpoint law.
The irrelevant nonpositive parameters are assigned a Dirac law. -/
def bridgeProbability (T : ℝ≥0) (hT : 0 < T) (a : ℝ) : ProbabilityMeasure Path :=
  if ha : 0 < a then ⟨positiveBridgeLaw a T,positiveBridgeLaw_isProbability a ha T hT⟩
  else diracProba (ContinuousMap.const _ 0)

theorem bridgeProbability_toMeasure (T : ℝ≥0) (hT : 0 < T) (a : ℝ) (ha : 0 < a) :
    (bridgeProbability T hT a : Measure Path) = positiveBridgeLaw a T := by
  simp only [bridgeProbability,dif_pos ha,ProbabilityMeasure.coe_mk]

theorem bridgeProbability_endpoint_map (T : ℝ≥0) (hT : 0 < T) (a : ℝ) (ha : 0 < a)
    (t : ℝ≥0) (ht : t = 0 ∨ t = T) :
    (bridgeProbability T hT a).map (continuous_eval t).measurable.aemeasurable = diracProba a := by
  apply Subtype.ext
  change (bridgeProbability T hT a : Measure Path).map (fun f ↦ f t) = Measure.dirac a
  rw [bridgeProbability_toMeasure T hT a ha]
  have he : (fun f : Path ↦ f t) =ᵐ[positiveBridgeLaw a T] (fun _ ↦ a) := by
    filter_upwards [ae_positiveBridgeLaw_endpoints a T hT] with f hf
    rcases ht with rfl | rfl
    · exact hf.1
    · exact hf.2
  rw [Measure.map_congr he,Measure.map_const]
  let := positiveBridgeLaw_isProbability a ha T hT
  simp only [measure_univ,one_smul]

theorem ae_weak_cluster_stopped {ι : Type*} {L : Filter ι} [L.NeBot]
    (T : ℝ≥0) (hT : 0 < T) (a : ι → ℝ)
    (ha : Tendsto a L (𝓝[>] 0)) (μ : ProbabilityMeasure Path)
    (hμ : Tendsto (fun i ↦ bridgeProbability T hT (a i)) L (𝓝 μ)) :
    ∀ᵐ f ∂(μ : Measure Path), ∀ t, f t = f (min t T) := by
  have hpos : ∀ᶠ i in L, 0 < a i := ha.eventually self_mem_nhdsWithin
  have hm : ∀ᶠ i in L,
      (bridgeProbability T hT (a i) : Measure Path) (stoppedPaths T) = 1 := by
    filter_upwards [hpos] with i hi
    rw [bridgeProbability_toMeasure T hT (a i) hi]
    let := positiveBridgeLaw_isProbability (a i) hi T hT
    exact (mem_ae_iff_prob_eq_one (measurableSet_stoppedPaths T)).mp
      (ae_positiveBridgeLaw_stopped (a i) T)
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ
    (isClosed_stoppedPaths T)
  rw [Filter.limsup_congr hm,limsup_const] at hlim
  have hmass : (μ : Measure Path) (stoppedPaths T) = 1 :=
    le_antisymm prob_le_one hlim
  exact (mem_ae_iff_prob_eq_one (measurableSet_stoppedPaths T)).mpr hmass

theorem weak_cluster_endpoint_map {ι : Type*} {L : Filter ι} [L.NeBot]
    (T : ℝ≥0) (hT : 0 < T) (a : ι → ℝ)
    (ha : Tendsto a L (𝓝[>] 0)) (μ : ProbabilityMeasure Path)
    (hμ : Tendsto (fun i ↦ bridgeProbability T hT (a i)) L (𝓝 μ))
    (t : ℝ≥0) (ht : t = 0 ∨ t = T) :
    μ.map (continuous_eval t).measurable.aemeasurable = diracProba 0 := by
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun i ↦ bridgeProbability T hT (a i)) μ hμ (continuous_eval t)
  have hdirac : Tendsto (fun i ↦ diracProba (a i)) L (𝓝 (diracProba 0)) :=
    continuous_diracProba.continuousAt.tendsto.comp (ha.mono_right nhdsWithin_le_nhds)
  have he : (fun i ↦ (bridgeProbability T hT (a i)).map
      (continuous_eval t).measurable.aemeasurable) =ᶠ[L] (fun i ↦ diracProba (a i)) := by
    filter_upwards [ha.eventually self_mem_nhdsWithin] with i hi
    exact bridgeProbability_endpoint_map T hT (a i) hi t ht
  exact tendsto_nhds_unique hmap (hdirac.congr' he.symm)

theorem ae_weak_cluster_endpoint_zero {ι : Type*} {L : Filter ι} [L.NeBot]
    (T : ℝ≥0) (hT : 0 < T) (a : ι → ℝ)
    (ha : Tendsto a L (𝓝[>] 0)) (μ : ProbabilityMeasure Path)
    (hμ : Tendsto (fun i ↦ bridgeProbability T hT (a i)) L (𝓝 μ))
    (t : ℝ≥0) (ht : t = 0 ∨ t = T) : ∀ᵐ f ∂(μ : Measure Path), f t = 0 := by
  have he := congrArg ProbabilityMeasure.toMeasure
    (weak_cluster_endpoint_map T hT a ha μ hμ t ht)
  change (μ : Measure Path).map (fun f ↦ f t) = Measure.dirac 0 at he
  apply (ae_map_iff (continuous_eval t).measurable.aemeasurable
    (measurableSet_eq_fun measurable_id measurable_const)).mp
  rw [he]
  exact (ae_dirac_iff (measurableSet_eq_fun measurable_id measurable_const)).mpr rfl

theorem ae_weak_cluster_stopped_zero {ι : Type*} {L : Filter ι} [L.NeBot]
    (T : ℝ≥0) (hT : 0 < T) (a : ι → ℝ)
    (ha : Tendsto a L (𝓝[>] 0)) (μ : ProbabilityMeasure Path)
    (hμ : Tendsto (fun i ↦ bridgeProbability T hT (a i)) L (𝓝 μ)) :
    ∀ᵐ f ∂(μ : Measure Path), ∀ t, T ≤ t → f t = 0 := by
  filter_upwards [ae_weak_cluster_stopped T hT a ha μ hμ,
    ae_weak_cluster_endpoint_zero T hT a ha μ hμ T (Or.inr rfl)] with f hs hz
  intro t ht
  rw [hs t,min_eq_right ht,hz]

end PerronWright.BrownianPositiveBridgeWeakClusterSupport
