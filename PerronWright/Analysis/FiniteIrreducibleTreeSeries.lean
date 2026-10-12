import PerronWright.Analysis.FiniteIrreducibleLeastBranch
import PerronWright.Analysis.FiniteIrreducibleNoAnalyticBranch
import PerronWright.Enumeration.RootedTreeSeriesPhysical

/-!
# Exact radius and physical identification of the literal finite tree series

The series is the existing formal multilinear series of actual labelled
rooted trees on the proved discrete BJR data. Pure enumerative lower bounds
and residual identities are reused; no `IsRegularCritical` or B2 adapter
is supplied. The finite Perron obstruction proves its exact radius, and
finite tree domination identifies its sum with the genuine least branch.
-/

open Filter
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

theorem complexTypeRootedTreeFMS_radius_eq_one (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) : M.bjrModel.complexTypeRootedTreeFMS.radius = 1 := by
  apply le_antisymm ?_ M.bjrModel.one_le_complexTypeRootedTreeFMS_radius
  by_contra hle
  have hlt : (1 : ℝ≥0∞) < M.bjrModel.complexTypeRootedTreeFMS.radius := lt_of_not_ge hle
  have hconv : (1 : ℂ) ∈ Metric.eball 0 M.bjrModel.complexTypeRootedTreeFMS.radius := by
    rw [Metric.mem_eball]
    simpa using hlt
  let V : C(S, ℝ) := M.bjrModel.rootedTreeSeriesReal 1
  have hseries : M.bjrModel.rootedTreeSeries (1 : ℂ) =
      TreeRealComplexBridge.complexify V :=
    M.bjrModel.rootedTreeSeries_eq_complexify_real 1 hconv
  have hres : M.treeResidual (((1 : ℂ), 0), TreeRealComplexBridge.complexify V) = 0 := by
    rw [← hseries]
    exact M.bjrModel.rootedTreeSeries_residual_zero hconv
  have hfix : M.bjrModel.normalizedZeroTreeMap 1 V = V :=
    (TreeRealComplexBridge.normalizedZeroTreeMap_fixed_iff_residual_zero
      M.bjrModel 1 V).mpr hres
  have hV : V = 1 := M.normalizedZeroTreeMap_one_unique hcrit V hfix
  have hseriesOne : M.bjrModel.rootedTreeSeries (1 : ℂ) = 1 := by
    rw [hseries, hV, TreeRealComplexBridge.complexify_one]
  have ha : AnalyticAt ℂ M.bjrModel.rootedTreeSeries 1 :=
    M.bjrModel.rootedTreeSeries_analyticOnNhd 1 hconv
  have hnear : ∀ᶠ z : ℂ in 𝓝 1, M.treeResidual ((z, 0), M.bjrModel.rootedTreeSeries z) = 0 := by
    filter_upwards [Metric.isOpen_eball.mem_nhds hconv] with z hz
    exact M.bjrModel.rootedTreeSeries_residual_zero hz
  exact M.not_exists_analytic_tree_curve_through_critical hcrit
    ⟨M.bjrModel.rootedTreeSeries, ha, hseriesOne, hnear⟩

/-- The actual labelled rooted-tree sum equals the limit of the zero-start
iteration. This proof uses tree domination and leastness, not an assumed
uniqueness interface. -/
theorem rootedTreeSeries_eq_least_fixedPoint (M : FiniteIrreducibleModel S)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) :
    ∃ V : C(S, ℝ), Tendsto (M.bjrModel.normalizedZeroTreeIter w) atTop (𝓝 V) ∧
      (∀ a, 0 ≤ V a ∧ V a ≤ 1) ∧ M.bjrModel.normalizedZeroTreeMap w V = V ∧
      M.bjrModel.rootedTreeSeries (w : ℂ) = TreeRealComplexBridge.complexify V := by
  have hwball : (w : ℂ) ∈ Metric.eball 0 (1 : ℝ≥0∞) := by
    rw [← ENNReal.coe_one, Metric.eball_coe]
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hw, NNReal.coe_one] using hw1
  have hconv : (w : ℂ) ∈ Metric.eball 0 M.bjrModel.complexTypeRootedTreeFMS.radius :=
    Metric.eball_subset_eball M.bjrModel.one_le_complexTypeRootedTreeFMS_radius hwball
  let W : C(S, ℝ) := M.bjrModel.rootedTreeSeriesReal w
  have hWbounds : ∀ a, 0 ≤ W a ∧ W a ≤ 1 :=
    M.bjrModel.rootedTreeSeriesReal_bounded w hw hw1.le hconv
  have hseries : M.bjrModel.rootedTreeSeries (w : ℂ) = TreeRealComplexBridge.complexify W :=
    M.bjrModel.rootedTreeSeries_eq_complexify_real w hconv
  have hWfix : M.bjrModel.normalizedZeroTreeMap w W = W := by
    apply (TreeRealComplexBridge.normalizedZeroTreeMap_fixed_iff_residual_zero M.bjrModel w W).mpr
    rw [← hseries]
    exact M.bjrModel.rootedTreeSeries_residual_zero hconv
  obtain ⟨V, hVlim, hVbounds, hVfix, hleast⟩ :=
    M.normalizedZeroTreeIter_least_fixed w hw hw1.le
  have hVW : V = W := by
    ext a
    apply le_antisymm (hleast W (fun b ↦ (hWbounds b).1) hWfix a)
    have hsum : Tendsto (fun n ↦ M.bjrModel.rootedTreePartialSum n w a) atTop (𝓝 (W a)) :=
      ((continuous_eval_const a).tendsto W).comp
        (M.bjrModel.rootedTreePartialSum_tendsto_seriesReal w hconv)
    have hiter : Tendsto (fun n ↦ M.bjrModel.normalizedZeroTreeIter w n a) atTop (𝓝 (V a)) :=
      ((continuous_eval_const a).tendsto V).comp hVlim
    exact le_of_tendsto_of_tendsto' hsum hiter (fun n ↦
      M.bjrModel.rootedTreePartialSum_le_normalizedZeroTreeIter n hw a)
  refine ⟨V, hVlim, hVbounds, hVfix, ?_⟩
  rw [hseries, hVW]

end PerronWright.FiniteIrreducibleModel
