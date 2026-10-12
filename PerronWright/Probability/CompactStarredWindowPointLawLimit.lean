import PerronWright.Probability.WindowSizeRescaling
import PerronWright.Probability.CompactWindowPointLawLimit

/-!
# Actual starred-window point-law convergence

Positive size rescaling transports the proved genuine unmarked window
limit to the paper's literal starred component point law. No target law
or Brownian identity is introduced as an assumption.
-/

open MeasureTheory Filter Topology
open scoped Classical Topology

noncomputable section

namespace PerronWright.CompactStarredWindowPointLawLimit

open FinitePointMeasureCompact FinitePointMeasureMarking
open ComponentWindowPointMeasures ComponentPointProcesses WindowSizeRescaling

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- Every fixed positive size rescaling of the actual component process
has a unique entire-sequence weak limit on the actual compact window. -/
theorem exists_unique_windowLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (windowLaw M lambda a b R c) atTop (𝓝 ν) := by
  let : MetricSpace (SurplusWindow a b R) := TopologicalSpace.metrizableSpaceMetric _
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  have hab' : a / c ≤ b / c := (div_le_div_iff_of_pos_right hc).mpr hab
  obtain ⟨ν, hν, _⟩ := CompactWindowPointLawLimit.exists_unique_unmarkedWindowLaw_limit
    M hM hQP lambda (a / c) (b / c) (div_pos ha hc) hab' R
  have hcont := continuous_mapPoint (windowScaleMap a b R hc)
    (continuous_windowScaleMap a b R hc)
  let ρ := ν.map hcont.measurable.aemeasurable
  have hρ : Tendsto (windowLaw M lambda a b R c) atTop (𝓝 ρ) := by
    change Tendsto (fun n ↦ windowLaw M lambda a b R c n) atTop (𝓝 ρ)
    simpa only [windowLaw_eq_map_unmarkedWindowLaw M lambda a b R hc, ρ] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (unmarkedWindowLaw M lambda (a / c) (b / c) R) ν hν hcont
  exact ⟨ρ, hρ, fun θ hθ ↦ tendsto_nhds_unique hθ hρ⟩

/-- The literal `beta^(1/3)` normalization appearing in Chapter 3. -/
theorem exists_unique_starredWindowLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (starredWindowLaw M hM lambda a b R) atTop (𝓝 ν) := by
  change ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
    Tendsto (windowLaw M lambda a b R (sizeScale M hM)) atTop (𝓝 ν)
  exact exists_unique_windowLaw_limit M hM hQP lambda a b ha hab R (sizeScale_pos M hM)

end PerronWright.CompactStarredWindowPointLawLimit
