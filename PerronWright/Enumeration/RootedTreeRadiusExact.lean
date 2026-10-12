import PerronWright.Enumeration.RootedTreeSeriesPhysical
import PerronWright.Analysis.CriticalNoAnalyticBranch

/-!
# Exact critical radius of the genuine rooted-tree series

The enumerative domination gives radius at least one.  If the radius were
larger, the full-ball residual identity would make the Taylor sum an ordinary
activity-analytic tree branch through the critical point, contradicting the
proved Perron obstruction.
-/

open Filter
open scoped Classical Topology ENNReal NNReal
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The canonical Taylor series obtained from literal labelled rooted trees
has convergence radius exactly the Perron critical value one. -/
theorem CompactBJRModel.complexTypeRootedTreeFMS_radius_eq_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    M.complexTypeRootedTreeFMS.radius = 1 := by
  apply le_antisymm ?_ M.one_le_complexTypeRootedTreeFMS_radius
  by_contra hle
  have hlt : (1 : ℝ≥0∞) < M.complexTypeRootedTreeFMS.radius :=
    lt_of_not_ge hle
  have hconv : (1 : ℂ) ∈
      Metric.eball 0 M.complexTypeRootedTreeFMS.radius := by
    rw [Metric.mem_eball]
    simpa using hlt
  let V : C(S, ℝ) := M.rootedTreeSeriesReal 1
  have hseries : M.rootedTreeSeries (1 : ℂ) =
      TreeRealComplexBridge.complexify V :=
    M.rootedTreeSeries_eq_complexify_real 1 hconv
  have hres : TreeCritical.residual M
      (((1 : ℂ), 0), TreeRealComplexBridge.complexify V) = 0 := by
    rw [← hseries]
    exact M.rootedTreeSeries_residual_zero hconv
  have hfix : M.normalizedZeroTreeMap 1 V = V :=
    (TreeRealComplexBridge.normalizedZeroTreeMap_fixed_iff_residual_zero
      M 1 V).mpr hres
  have hV : V = 1 := M.normalizedZeroTreeMap_one_unique hM V hfix
  have hseriesOne : M.rootedTreeSeries (1 : ℂ) = 1 := by
    rw [hseries, hV, TreeRealComplexBridge.complexify_one]
  have hseriesAnalytic : AnalyticAt ℂ M.rootedTreeSeries 1 :=
    M.rootedTreeSeries_analyticOnNhd 1 hconv
  have hresNear : ∀ᶠ z : ℂ in 𝓝 1,
      TreeCritical.residual M ((z, 0), M.rootedTreeSeries z) = 0 := by
    filter_upwards [Metric.isOpen_eball.mem_nhds hconv] with z hz
    exact M.rootedTreeSeries_residual_zero hz
  exact M.not_exists_analytic_tree_curve_through_critical hM
    ⟨M.rootedTreeSeries, hseriesAnalytic, hseriesOne, hresNear⟩

end PerronWright
