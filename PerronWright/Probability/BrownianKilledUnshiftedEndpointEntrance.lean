import PerronWright.Probability.BrownianKilledGlobalEntranceNonnegativeTests

/-! # Actual unshifted survived endpoint has the entrance limit

The endpoint used in minimum-window disintegration is the literal future
increment, not that increment plus the window width. A continuous change
of the test removes the deterministic width shift from the genuine killed
endpoint law. The normalized limit is therefore proved for the actual
survived Brownian endpoint under its actual path law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledUnshiftedEndpointEntrance

open BrownianPathLaw ContinuousPathFirstPassage BrownianPositiveKilledEndpoint
open BrownianKilledBoundaryEntrance BrownianKilledGlobalEntranceNonnegativeTests

theorem actual_normalized_survived_endpoint_test_tendsto (T : ℝ≥0) (hT : 0 < T)
    (G : (ℝ × ℝ) →ᵇ ℝ) (hG : ∀ p, 0 ≤ G p) :
    Tendsto (fun δ : ℝ ↦
      (∫⁻ f in survival (-δ) T, ENNReal.ofReal (G (δ,f T)) ∂pathLaw)/ENNReal.ofReal δ)
      (𝓝[>] 0) (𝓝 (∫⁻ y, entrance T y*ENNReal.ofReal (G (0,y)))) := by
  let L : C(ℝ × ℝ,ℝ × ℝ) :=
    ⟨fun p ↦ (p.1,p.2-p.1),continuous_fst.prodMk (continuous_snd.sub continuous_fst)⟩
  have h := normalized_law_nonnegative_test_tendsto T hT (G.compContinuous L)
    (fun p ↦ hG _)
  simp only [BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,
    L,sub_zero] at h
  apply h.congr
  intro δ
  have hm : Measurable (fun y : ℝ ↦ ENNReal.ofReal (G (δ,y-δ))) :=
    (G.continuous.measurable.comp
      (measurable_const.prodMk (measurable_id.sub_const δ))).ennreal_ofReal
  rw [law,lintegral_map hm ((continuous_eval T).measurable.add_const δ)]
  simp only [add_sub_cancel_right]

end PerronWright.BrownianKilledUnshiftedEndpointEntrance
