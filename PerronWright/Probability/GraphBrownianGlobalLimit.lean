import PerronWright.Probability.GraphBrownianWindowLimit
import PerronWright.Probability.GraphGlobalSizeRescaling

/-! # Actual Brownian identification of the full graph process

The proved Brownian window limits identify every finite compact-support
test law. Genuine vague-Borel determination then identifies the actual
full graph limit, and literal starred dilation gives Aldous's law.
No Brownian moment or process-identification hypothesis is introduced.
-/

open MeasureTheory Filter Topology
open scoped Classical CompactlySupported
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GraphBrownianGlobalLimit

open GraphWindowFactorialLimits GraphGlobalSpatialLimit GraphGlobalSizeRescaling
open ComponentGlobalPointProcess LocallyFinitePointMeasureVague
open CompactGlobalTestLawLimit BrownianInverseSizeLaw GlobalPointSizeRescaling

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]

theorem globalTestLaw_tendsto_actual_Brownian {D : Type*} [Fintype D]
    {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (f : D → C_c(PositiveSizeSurplus, ℝ)) :
    Tendsto (fun n ↦ GraphGlobalSpatialLimit.globalTestLaw ρ n f) atTop
      (𝓝 ((inverseScaledLaw (alpha*beta^(-2/3 : ℝ)*lambda)
        (Real.rpow_pos_of_pos hbeta (1/3 : ℝ))).map
          (continuous_testVector f).measurable.aemeasurable)) := by
  obtain ⟨a,b,R,ha,hab,hf⟩ := exists_common_test_window f
  have hwindow := GraphBrownianWindowLimit.windowLaw_tendsto_actual_Brownian
    ρ hbeta hlocal ha hab R
  have htest := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hwindow
    (continuous_windowTestVector a b R ha f)
  rw [BrownianInverseWindowLaw.globalTestLaw_eq_window_map
    (alpha*beta^(-2/3 : ℝ)*lambda) a b R
    (Real.rpow_pos_of_pos hbeta (1/3 : ℝ)) ha hab f hf]
  simpa only [GraphGlobalSpatialLimit.globalTestLaw_eq_window_map ρ a b R ha _ f hf]
    using htest

theorem processLimitLaw_eq_actual_Brownian {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) :
    processLimitLaw ρ hbeta hlocal =
      inverseScaledLaw (alpha*beta^(-2/3 : ℝ)*lambda)
        (Real.rpow_pos_of_pos hbeta (1/3 : ℝ)) := by
  apply CompactGlobalPointLawLimit.probability_ext_of_finiteTestMaps
  intro F
  let f : F → C_c(PositiveSizeSurplus, ℝ) := Subtype.val
  have hgraph := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (tendsto_processLimitLaw ρ hbeta hlocal) (continuous_testVector f)
  exact tendsto_nhds_unique hgraph
    (globalTestLaw_tendsto_actual_Brownian ρ hbeta hlocal f)

theorem processLaw_tendsto_actual_Brownian {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) :
    Tendsto (processLaw ρ) atTop
      (𝓝 (inverseScaledLaw (alpha*beta^(-2/3 : ℝ)*lambda)
        (Real.rpow_pos_of_pos hbeta (1/3 : ℝ)))) := by
  rw [← processLimitLaw_eq_actual_Brownian ρ hbeta hlocal]
  exact tendsto_processLimitLaw ρ hbeta hlocal

theorem starredProcessLaw_tendsto_actual_Brownian {alpha beta lambda : ℝ}
    (hbeta : 0 < beta) (hlocal : HasUniformLocalLimit ρ alpha beta lambda) :
    Tendsto (scaledProcessLaw ρ (Real.rpow_pos_of_pos hbeta (1/3 : ℝ))) atTop
      (𝓝 (BrownianExcursionPointProcessLaw.law (alpha*beta^(-2/3 : ℝ)*lambda))) := by
  change Tendsto (fun n ↦ scaledProcessLaw ρ (Real.rpow_pos_of_pos hbeta (1/3 : ℝ)) n)
    atTop (𝓝 (BrownianExcursionPointProcessLaw.law (alpha*beta^(-2/3 : ℝ)*lambda)))
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (processLaw_tendsto_actual_Brownian ρ hbeta hlocal)
    (continuous_scalePoint (Real.rpow_pos_of_pos hbeta (1/3 : ℝ)))
  simpa only [scaledProcessLaw_eq_map, inverseScaledLaw_map] using h

end PerronWright.GraphBrownianGlobalLimit
