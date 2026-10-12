import PerronWright.Probability.GraphGlobalSpatialLimit
import PerronWright.Probability.GlobalPointSizeRescaling

/-! # Literal size dilation of actual graph global spatial limits

The source is the genuine finite graph law, not an assumed point process.
Positive dilation is proper, acts on every actual component atom, and
continuously transports the proved full-sequence vague limit. No Brownian
identification is asserted by this transport.
-/

open MeasureTheory Filter Topology
open scoped Classical Topology
noncomputable section

namespace PerronWright.GraphGlobalSizeRescaling

open ComponentGlobalPointProcess LocallyFinitePointMeasureVague
open GlobalPointSizeRescaling GraphGlobalSpatialLimit GraphWindowFactorialLimits

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]

def scaledProcessLaw {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  ⟨(ρ n).map (scaledProcess hc),
    Measure.isProbabilityMeasure_map (measurable_scaledProcess hc (n+1)).aemeasurable⟩

theorem scaledProcessLaw_eq_map {c : ℝ} (hc : 0 < c) (n : ℕ) :
    scaledProcessLaw ρ hc n = (processLaw ρ n).map
      (continuous_scalePoint hc).measurable.aemeasurable := by
  apply Subtype.ext
  change (ρ n).map (scaledProcess hc) =
    ((ρ n).map unmarkedProcess).map (scalePoint hc)
  rw [Measure.map_map (continuous_scalePoint hc).measurable (measurable_unmarkedProcess (n+1))]
  congr 1
  exact funext (scaledProcess_eq_map hc)

def scaledProcessLimitLaw {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) {c : ℝ} (hc : 0 < c) :
    ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  (processLimitLaw ρ hbeta hlocal).map (continuous_scalePoint hc).measurable.aemeasurable

theorem tendsto_scaledProcessLimitLaw {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) {c : ℝ} (hc : 0 < c) :
    Tendsto (scaledProcessLaw ρ hc) atTop
      (𝓝 (scaledProcessLimitLaw ρ hbeta hlocal hc)) := by
  change Tendsto (fun n ↦ scaledProcessLaw ρ hc n) atTop
    (𝓝 (scaledProcessLimitLaw ρ hbeta hlocal hc))
  simpa only [scaledProcessLaw_eq_map, scaledProcessLimitLaw] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (processLaw ρ) (processLimitLaw ρ hbeta hlocal)
      (tendsto_processLimitLaw ρ hbeta hlocal) (continuous_scalePoint hc)

theorem exists_unique_scaledProcessLaw_limit {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) {c : ℝ} (hc : 0 < c) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      Tendsto (scaledProcessLaw ρ hc) atTop (𝓝 ν) :=
  ⟨scaledProcessLimitLaw ρ hbeta hlocal hc,
    tendsto_scaledProcessLimitLaw ρ hbeta hlocal hc,
    fun _ hν ↦ tendsto_nhds_unique hν (tendsto_scaledProcessLimitLaw ρ hbeta hlocal hc)⟩

end PerronWright.GraphGlobalSizeRescaling
