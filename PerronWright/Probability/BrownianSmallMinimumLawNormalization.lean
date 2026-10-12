import PerronWright.Probability.BrownianBridgeMinimumTimeConditioning
import PerronWright.Probability.ContinuousTimeCutoff

/-! # Literal small-minimum bridge normalization and cutoff restriction

The actual minimum-time event has its proved uniform probability. These
identities retain that exact normalization and remove a concrete continuous
cutoff on the event where it is identically one.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianSmallMinimumLawNormalization

open BrownianPathLaw BrownianFirstPassageBridgeLaw BrownianBridgeMinimumTimeConditioning
open BrownianBridgeMinimumShift ContinuousPathLeastMinimum

theorem ae_pinned_bridgeMinimumTime_eq_leastMinimizer (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ f ∂pinnedLaw T, bridgeMinimumTime T f = leastMinimizer T f := by
  filter_upwards [BrownianPositiveBridgeConditioning.ae_pinnedLaw_endpoints_zero T hT,
    BrownianPositiveBridgeStoppedSupport.ae_pinnedLaw_stopped T] with f he hs
  have hc : BrownianBridgeCyclicPath.stoppedClosedBridgePath T f = f := by
    apply ContinuousMap.ext
    intro t
    change BrownianBridgeCyclicPath.closedBridge T (min t T) f = f t
    rw [BrownianBridgeMinimumReconstruction.closedBridge_eq_of_endpoints T _ f he.1 he.2,← hs t]
  rw [bridgeMinimumTime,hc]

theorem actual_smallMinimum_lintegral_restrict (T : ℝ≥0) (hT : 0 < T)
    (ε : ℝ) (hε : 0 < ε) (hεT : ε ≤ (T : ℝ)) (Ψ : Path → ℝ≥0∞) :
    (∫⁻ f, Ψ f ∂smallMinimumLaw T ε) =
      (ENNReal.ofReal ε)⁻¹*ENNReal.ofReal (T : ℝ)*
        ∫⁻ f in minimumTimeEvent T ε, Ψ f ∂pinnedLaw T := by
  rw [smallMinimumLaw,ProbabilityTheory.cond,lintegral_smul_measure,smul_eq_mul,
    minimumTimeEvent_probability T hT ε hε hεT]
  have hT0 : ENNReal.ofReal (T : ℝ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hT)
  rw [ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top)
    (Or.inl (ENNReal.inv_ne_top.mpr hT0)),inv_inv]
  ac_rfl

theorem timeCutoff_restricted_lintegral (T : ℝ≥0) (hT : 0 < T) (r : ℝ≥0) (ε : ℝ)
    (hεr : Real.toNNReal ε ≤ r) (κ : ℝ≥0 →ᵇ ℝ)
    (hone : ∀ t, t ≤ r → κ t = 1) (Ψ : Path → ℝ≥0∞) :
    (∫⁻ f in minimumTimeEvent T ε,
      ENNReal.ofReal (κ (leastMinimizer T f))*Ψ f ∂pinnedLaw T) =
        ∫⁻ f in minimumTimeEvent T ε, Ψ f ∂pinnedLaw T := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_minimumTimeEvent T ε),
    ae_restrict_of_ae (ae_pinned_bridgeMinimumTime_eq_leastMinimizer T hT)] with f hf he
  change (bridgeMinimumTime T f : ℝ) ∈ Ioc 0 ε at hf
  rw [he] at hf
  have ht : leastMinimizer T f ≤ Real.toNNReal ε :=
    NNReal.le_toNNReal_of_coe_le hf.2
  rw [hone _ (ht.trans hεr),ENNReal.ofReal_one,one_mul]

theorem positive_time_restricted_indicator (T ε : ℝ) (hεT : ε < T)
    (F : ℝ → ℝ≥0∞) :
    (∫⁻ s in Ioo 0 T, (Ioc (0 : ℝ) ε).indicator F s) =
      ∫⁻ s in Ioc (0 : ℝ) ε, F s := by
  have hsub : Ioc (0 : ℝ) ε ⊆ Ioo 0 T := fun s hs ↦ ⟨hs.1,hs.2.trans_lt hεT⟩
  rw [lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr hsub]

end PerronWright.BrownianSmallMinimumLawNormalization
