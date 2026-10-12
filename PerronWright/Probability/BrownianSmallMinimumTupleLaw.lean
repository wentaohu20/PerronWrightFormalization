import PerronWright.Probability.BrownianMinimumTuplePinningMeasure
import PerronWright.Probability.BrownianMinimumTupleSmallTime
import PerronWright.Probability.BrownianSmallMinimumLawNormalization
import PerronWright.Probability.BrownianSmallMinimumEntranceNormalization
import PerronWright.Probability.BrownianPositiveTimeAveraging

/-! # Actual small-minimum-time bridge finite-dimensional limit

The proved pinned Borel density applies to the literal conditioning event,
using a concrete continuous cutoff that equals one there. Actual uniform
minimum-time probability, the passage contraction and positive-time
averaging give the normalized entrance probability density. Ordinary path
observations are recovered by adding back the literal minimum height.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianSmallMinimumTupleLaw

open BrownianPathLaw BrownianFirstPassageBridgeLaw BrownianBridgeMinimumTimeConditioning
open BrownianMinimumFutureCoordinateMeasure BrownianMinimumTuplePinningMeasure
open BrownianMinimumTupleSmallTime BrownianMinimumTupleEndpointGeometry
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFreeEntranceGeometry
open BrownianSmallMinimumLawNormalization BrownianSmallMinimumEntranceNormalization
open BrownianPositiveBridgeMultiPointEntrance ContinuousPathLeastMinimum

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

private theorem restricted_density (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ)
    (ε : ℝ) (hεsmall : ε < (times 0/4 : ℝ≥0)) :
    gaussianPDF 0 (times (Fin.last (n+1))) 0*
      (∫⁻ f in minimumTimeEvent (times (Fin.last (n+1))) ε,
        ENNReal.ofReal (Φ (originalTriple (n+1) times f))
          ∂pinnedLaw (times (Fin.last (n+1)))) =
      ∫⁻ s in Ioc (0 : ℝ) ε, levelDensity n times Φ s := by
  let T := times (Fin.last (n+1))
  let r : ℝ≥0 := times 0/4
  let b : ℝ≥0 := times 0/2
  have hT : 0 < T := hfirst.trans_le (hstrict.monotone (Fin.zero_le _))
  have hrb : r < b := by
    apply NNReal.coe_lt_coe.mp
    change (times 0 : ℝ)/4 < (times 0 : ℝ)/2
    exact div_lt_div_of_pos_left (show 0 < (times 0 : ℝ) from hfirst) (by norm_num) (by norm_num)
  have hb : b < times 0 := div_lt_self hfirst (by norm_num)
  obtain ⟨κ,hκ,hone,hcut⟩ := ContinuousTimeCutoff.exists_timeCutoff r b hrb
  let Ψ : (ℝ≥0 × ℝ × FreeVector (n+2)) → ℝ≥0∞ := fun p ↦
    if (p.1 : ℝ) ∈ Ioc 0 ε then ENNReal.ofReal (Φ p) else 0
  have hΨ : Measurable Ψ := Measurable.ite
    ((NNReal.continuous_coe.measurable.comp measurable_fst) measurableSet_Ioc)
    Φ.continuous.measurable.ennreal_ofReal measurable_const
  have he := actual_pinned_weighted_borel_density n times hstrict b hb κ
    (fun t ↦ (hκ t).1) hcut Ψ hΨ
  have hl : (∫⁻ f, ENNReal.ofReal (κ (leastMinimizer T f))*Ψ (originalTriple (n+1) times f)
      ∂pinnedLaw T) =
      ∫⁻ f in minimumTimeEvent T ε, ENNReal.ofReal (κ (leastMinimizer T f))*
        ENNReal.ofReal (Φ (originalTriple (n+1) times f)) ∂pinnedLaw T := by
    rw [← lintegral_indicator (measurableSet_minimumTimeEvent T ε)]
    apply lintegral_congr_ae
    filter_upwards [ae_pinned_bridgeMinimumTime_eq_leastMinimizer T hT] with f hf
    have ht : (originalTriple (n+1) times f).1 = leastMinimizer T f := rfl
    simp only [Ψ,ht,minimumTimeEvent,Set.mem_ofPred_eq,hf,Set.indicator]
    split_ifs <;> simp
  rw [hl,timeCutoff_restricted_lintegral T hT r ε
    (Real.toNNReal_le_iff_le_coe.mpr hεsmall.le) κ hone] at he
  have hr : (∫⁻ s in Ioo 0 (T : ℝ), ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*∫⁻ v : FreeVector (n+1),
        entranceJoint (n+1) (BrownianMinimumTupleEndpointGeometry.residualGaps n times s)
          (Fin.snoc v a)*ENNReal.ofReal (κ (Real.toNNReal s))*Ψ (Real.toNNReal s,-a,Fin.snoc v a)) =
      ∫⁻ s in Ioo 0 (T : ℝ), (Ioc (0 : ℝ) ε).indicator (levelDensity n times Φ) s := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hcoe : (Real.toNNReal s : ℝ) = s := Real.coe_toNNReal s hs.1.le
    by_cases hsi : s ∈ Ioc (0 : ℝ) ε
    · have hsr : Real.toNNReal s ≤ r :=
        Real.toNNReal_le_iff_le_coe.mpr (hsi.2.trans hεsmall.le)
      simp only [Ψ,hcoe,hsi,if_pos,hone _ hsr,ENNReal.ofReal_one,mul_one,
        Set.indicator_of_mem hsi]
      rfl
    · have hz (a : ℝ) (v : FreeVector (n+1)) : Ψ (Real.toNNReal s,-a,Fin.snoc v a) = 0 := by
        change (if (Real.toNNReal s : ℝ) ∈ Ioc 0 ε then
          ENNReal.ofReal (Φ (Real.toNNReal s,-a,Fin.snoc v a)) else 0) = 0
        rw [hcoe,if_neg hsi]
      simp only [hz,mul_zero,lintegral_zero,Set.indicator_of_notMem hsi]
  rw [hr,positive_time_restricted_indicator (T : ℝ) ε
    (hεsmall.trans (by
      have h4 : times 0/4 < times 0 := div_lt_self hfirst (by norm_num)
      exact h4.trans_le (hstrict.monotone (Fin.zero_le _))))] at he
  exact he

theorem actual_smallMinimum_original_test_tendsto (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+2)) →ᵇ ℝ) :
    Tendsto (fun ε : ℝ ↦ ∫⁻ f, ENNReal.ofReal (Φ (originalTriple (n+1) times f))
      ∂smallMinimumLaw (times (Fin.last (n+1))) ε) (𝓝[>] 0)
      (𝓝 (∫⁻ v : FreeVector (n+1), entranceProduct n (fixedGaps n times) v*
        ENNReal.ofReal (Φ (0,0,Fin.snoc v 0)))) := by
  let T := times (Fin.last (n+1))
  have hT : 0 < T := hfirst.trans_le (hstrict.monotone (Fin.zero_le _))
  have hp0 : gaussianPDF 0 T 0 ≠ 0 := ne_of_gt (gaussianPDF_pos 0 (ne_of_gt hT) 0)
  have hc : ENNReal.ofReal (T : ℝ)*(gaussianPDF 0 T 0)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hp0)
  have ht := BrownianPositiveTimeAveraging.normalized_positive_lintegral_right_tendsto
    (levelDensity n times Φ) (measurable_levelDensity n times Φ) _
      (levelDensity_limit_ne_top n times hstrict hfirst Φ)
      (levelDensity_tendsto n times hstrict hfirst Φ)
  have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (T : ℝ)*(gaussianPDF 0 T 0)⁻¹)
    ht (Or.inr hc)
  rw [normalized_joint_test_lintegral n times hstrict hfirst
    (fun v ↦ ENNReal.ofReal (Φ (0,0,Fin.snoc v 0)))] at h
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < (times 0/4 : ℝ≥0) :=
    (tendsto_id.mono_right nhdsWithin_le_nhds).eventually_lt_const (by positivity)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,hsmall] with ε hε hεsmall
  have hεT : ε ≤ (T : ℝ) := hεsmall.le.trans (by
    exact (div_le_self (zero_le : (0 : ℝ≥0) ≤ times 0) (by norm_num)).trans
      (hstrict.monotone (Fin.zero_le _)))
  rw [actual_smallMinimum_lintegral_restrict T hT ε hε hεT]
  have he := restricted_density n times hstrict hfirst Φ ε hεsmall
  have hr : (∫⁻ f in minimumTimeEvent T ε, ENNReal.ofReal (Φ (originalTriple (n+1) times f))
      ∂pinnedLaw T) = (gaussianPDF 0 T 0)⁻¹*∫⁻ s in Ioc (0 : ℝ) ε, levelDensity n times Φ s := by
    rw [← he,← mul_assoc,ENNReal.inv_mul_cancel hp0 gaussianPDF_ne_top,one_mul]
  rw [hr]
  ac_rfl

theorem actual_smallMinimum_ordered_test_tendsto (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0) (Ψ : FreeVector (n+1) →ᵇ ℝ≥0) :
    Tendsto (fun ε : ℝ ↦ ∫⁻ f, (Ψ (fun i ↦ f (times i.castSucc)) : ℝ≥0∞)
      ∂smallMinimumLaw (times (Fin.last (n+1))) ε) (𝓝[>] 0)
      (𝓝 (∫⁻ v : FreeVector (n+1), entranceProduct n (fixedGaps n times) v*(Ψ v : ℝ≥0∞))) := by
  let F : FreeVector (n+1) →ᵇ ℝ :=
    ⟨⟨fun v ↦ (Ψ v : ℝ),NNReal.continuous_coe.comp Ψ.continuous⟩,Ψ.map_bounded'⟩
  let H : (ℝ≥0 × ℝ × FreeVector (n+2)) → FreeVector (n+1) :=
    fun p i ↦ p.2.2 i.castSucc+p.2.1
  have hH : Continuous H := continuous_pi (fun i ↦
    ((continuous_apply i.castSucc).comp continuous_snd.snd).add continuous_snd.fst)
  let Φ := F.compContinuous ⟨H,hH⟩
  have hp (f : Path) : ENNReal.ofReal (Φ (originalTriple (n+1) times f)) =
      (Ψ (fun i ↦ f (times i.castSucc)) : ℝ≥0∞) := by
    have he : H (originalTriple (n+1) times f) = fun i ↦ f (times i.castSucc) := by
      funext i
      change f (times i.castSucc)-minimumValue _ f+minimumValue _ f = _
      ring
    simp only [Φ,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,he,F,
      BoundedContinuousFunction.coe_mk,ENNReal.ofReal_coe_nnreal]
  have hv (v : FreeVector (n+1)) : ENNReal.ofReal (Φ (0,0,Fin.snoc v 0)) = (Ψ v : ℝ≥0∞) := by
    have he : H (0,0,Fin.snoc v 0) = v := by
      funext i
      simp only [H,Fin.snoc_castSucc,add_zero]
    simp only [Φ,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,he,F,
      BoundedContinuousFunction.coe_mk,ENNReal.ofReal_coe_nnreal]
  simpa only [hp,hv] using actual_smallMinimum_original_test_tendsto n times hstrict hfirst Φ

end PerronWright.BrownianSmallMinimumTupleLaw
