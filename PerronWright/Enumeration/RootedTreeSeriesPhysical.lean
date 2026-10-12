import PerronWright.Enumeration.RootedTreeRadiusLower
import PerronWright.Analysis.TreePhysicalBranch
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The actual rooted-tree series on its convergence ball

The canonical Taylor sum satisfies the genuine compact-BJR tree equation on
its full convergence ball.  On the real subcritical interval it is the
complexification of the unique bounded physical fixed point.
-/

open Filter
open scoped Classical Topology ENNReal NNReal
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Sum of the canonical complex rooted-tree Taylor series. -/
def CompactBJRModel.rootedTreeSeries
    (M : CompactBJRModel S) (z : ℂ) : C(S, ℂ) :=
  M.complexTypeRootedTreeFMS.sum z

/-- The canonical real profile underlying the rooted-tree sum at a real
argument. -/
def CompactBJRModel.rootedTreeSeriesReal
    (M : CompactBJRModel S) (w : ℝ) : C(S, ℝ) :=
  ContinuousMap.rclikeToReal (M.rootedTreeSeries (w : ℂ))

/-- The complex Taylor sum is analytic throughout its full convergence
ball. -/
theorem CompactBJRModel.rootedTreeSeries_analyticOnNhd
    (M : CompactBJRModel S) :
    AnalyticOnNhd ℂ M.rootedTreeSeries
      (Metric.eball 0 M.complexTypeRootedTreeFMS.radius) := by
  change AnalyticOnNhd ℂ M.complexTypeRootedTreeFMS.sum
    (Metric.eball 0 M.complexTypeRootedTreeFMS.radius)
  exact M.complexTypeRootedTreeFMS.analyticOnNhd

/-- The actual rooted-tree Taylor residual is analytic throughout the full
convergence ball. -/
theorem CompactBJRModel.rootedTreeSeriesResidual_analyticOnNhd
    (M : CompactBJRModel S) :
    AnalyticOnNhd ℂ
      (fun z : ℂ =>
        TreeCritical.residual M ((z, 0), M.rootedTreeSeries z))
      (Metric.eball 0 M.complexTypeRootedTreeFMS.radius) := by
  intro z hz
  have hT : AnalyticAt ℂ M.rootedTreeSeries z :=
    M.rootedTreeSeries_analyticOnNhd z hz
  simpa only [TreeCritical.residual, Function.comp_apply, id_eq] using
    (TreeAnalytic.residual_analytic M.kernel M.mu
      (TreeCritical.degree M)
      (((z, (0 : C(S, ℂ))), M.rootedTreeSeries z))).comp₂
        (analyticAt_id.prod analyticAt_const) hT

private def rootedTreeZeroFieldLine :
    ℂ →L[ℂ] ℂ × C(S, ℂ) :=
  ContinuousLinearMap.inl ℂ ℂ C(S, ℂ)

private theorem CompactBJRModel.rootedTreeSeriesResidual_eventually_zero
    (M : CompactBJRModel S) :
    Filter.EventuallyEq (nhds (0 : ℂ))
      (fun z : ℂ =>
        TreeCritical.residual M ((z, 0), M.rootedTreeSeries z))
      (0 : ℂ → C(S, ℂ)) := by
  obtain ⟨psi, -, -, hres, hp⟩ :=
    M.exists_zeroTreeBranch_with_canonicalTaylorSeries
  have hRadius : (1 : ℝ≥0∞) ≤ M.complexTypeRootedTreeFMS.radius :=
    M.one_le_complexTypeRootedTreeFMS_radius
  have hRadiusPos : 0 < M.complexTypeRootedTreeFMS.radius :=
    (by norm_num : (0 : ℝ≥0∞) < 1).trans_le hRadius
  have hseries : HasFPowerSeriesAt M.rootedTreeSeries
      M.complexTypeRootedTreeFMS 0 := by
    change HasFPowerSeriesAt M.complexTypeRootedTreeFMS.sum
      M.complexTypeRootedTreeFMS 0
    exact (M.complexTypeRootedTreeFMS.hasFPowerSeriesOnBall
      hRadiusPos).hasFPowerSeriesAt
  have heq : Filter.EventuallyEq (nhds (0 : ℂ))
      (fun z : ℂ => psi (z, 0)) M.rootedTreeSeries := by
    filter_upwards [hp.eventually_hasSum_sub,
      hseries.eventually_hasSum_sub] with z hpsi htree
    exact hpsi.unique htree
  have hline : Filter.Eventually
      (fun z : ℂ => TreeCritical.residual M ((z, 0), psi (z, 0)) = 0)
      (nhds (0 : ℂ)) := by
    have ht : Filter.Tendsto (rootedTreeZeroFieldLine (S := S))
        (nhds (0 : ℂ))
        (nhds ((0 : ℂ), (0 : C(S, ℂ)))) := by
      have hz : rootedTreeZeroFieldLine (S := S) (0 : ℂ) =
          ((0 : ℂ), (0 : C(S, ℂ))) := by
        rw [map_zero]
        apply Prod.ext <;> rfl
      rw [← hz]
      exact (rootedTreeZeroFieldLine (S := S)).continuous.continuousAt
    simpa only [rootedTreeZeroFieldLine,
      ContinuousLinearMap.inl_apply, map_zero] using ht.eventually hres
  filter_upwards [hline, heq] with z hz heqz
  simpa only [Pi.zero_apply, heqz] using hz

/-- The actual rooted-tree Taylor sum satisfies the genuine compact-BJR tree
equation at every point of its full convergence ball. -/
theorem CompactBJRModel.rootedTreeSeries_residual_zero
    (M : CompactBJRModel S) {z : ℂ}
    (hz : z ∈ Metric.eball 0 M.complexTypeRootedTreeFMS.radius) :
    TreeCritical.residual M ((z, 0), M.rootedTreeSeries z) = 0 := by
  have hRadius : (1 : ℝ≥0∞) ≤ M.complexTypeRootedTreeFMS.radius :=
    M.one_le_complexTypeRootedTreeFMS_radius
  have hRadiusPos : 0 < M.complexTypeRootedTreeFMS.radius :=
    (by norm_num : (0 : ℝ≥0∞) < 1).trans_le hRadius
  have hglobal :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      M.rootedTreeSeriesResidual_analyticOnNhd
      Metric.isPreconnected_eball
      (Metric.mem_eball_self hRadiusPos)
      M.rootedTreeSeriesResidual_eventually_zero
  exact hglobal hz

/-- A real argument turns each homogeneous complex rooted-tree term into the
complexification of the corresponding real EGF term. -/
theorem CompactBJRModel.complexTypeRootedTreeFMS_apply_real
    (M : CompactBJRModel S) (n : ℕ) (w : ℝ) :
    M.complexTypeRootedTreeFMS n (fun _ : Fin n => (w : ℂ)) =
      TreeRealComplexBridge.complexify
        (w ^ n • PowerSeries.coeff n M.typeRootedTreeEGF) := by
  ext x
  simp only [CompactBJRModel.complexTypeRootedTreeFMS,
    oneDimensionalFormalMultilinearSeries,
    ContinuousMultilinearMap.mkPiRing_apply,
    M.complexTypeRootedTreeEGF_coeff,
    continuousMapComplexifyRingHom_apply,
    TreeRealComplexBridge.complexify_apply,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ContinuousMap.smul_apply, smul_eq_mul]
  norm_cast

/-- Finite complex Taylor sums on the real axis are exactly the
complexifications of the actual finite labelled-tree sums. -/
theorem CompactBJRModel.complexTypeRootedTreeFMS_partialSum_real
    (M : CompactBJRModel S) (N : ℕ) (w : ℝ) :
    ∑ n ∈ Finset.range N,
        M.complexTypeRootedTreeFMS n (fun _ : Fin n => (w : ℂ)) =
      TreeRealComplexBridge.complexify (M.rootedTreePartialSum N w) := by
  rw [CompactBJRModel.rootedTreePartialSum,
    ← continuousMapComplexifyRingHom_apply, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact M.complexTypeRootedTreeFMS_apply_real n w

/-- Inside the convergence ball, the formal multilinear terms sum to the
canonical rooted-tree series. -/
theorem CompactBJRModel.complexTypeRootedTreeFMS_hasSum
    (M : CompactBJRModel S) {z : ℂ}
    (hz : z ∈ Metric.eball 0 M.complexTypeRootedTreeFMS.radius) :
    HasSum (fun n : ℕ =>
        M.complexTypeRootedTreeFMS n (fun _ : Fin n => z))
      (M.rootedTreeSeries z) := by
  simpa only [CompactBJRModel.rootedTreeSeries] using
    M.complexTypeRootedTreeFMS.hasSum hz

/-- At every real argument in the convergence ball, the complex Taylor sum
is self-adjoint, hence genuinely real-valued. -/
theorem CompactBJRModel.rootedTreeSeries_isSelfAdjoint
    (M : CompactBJRModel S) (w : ℝ)
    (hw : (w : ℂ) ∈
      Metric.eball 0 M.complexTypeRootedTreeFMS.radius) :
    IsSelfAdjoint (M.rootedTreeSeries (w : ℂ)) := by
  have hs := M.complexTypeRootedTreeFMS_hasSum hw
  have hsStar := hs.star
  have hterm :
      (fun n : ℕ => star
        (M.complexTypeRootedTreeFMS n (fun _ : Fin n => (w : ℂ)))) =
      (fun n : ℕ =>
        M.complexTypeRootedTreeFMS n (fun _ : Fin n => (w : ℂ))) := by
    funext n
    rw [M.complexTypeRootedTreeFMS_apply_real]
    exact (ContinuousMap.isSelfAdjoint_realToRCLike ℂ
      (f := w ^ n • PowerSeries.coeff n M.typeRootedTreeEGF)).star_eq
  rw [hterm] at hsStar
  exact hsStar.unique hs

/-- The complex Taylor sum at a real argument is the complexification of its
canonical real profile. -/
theorem CompactBJRModel.rootedTreeSeries_eq_complexify_real
    (M : CompactBJRModel S) (w : ℝ)
    (hw : (w : ℂ) ∈
      Metric.eball 0 M.complexTypeRootedTreeFMS.radius) :
    M.rootedTreeSeries (w : ℂ) =
      TreeRealComplexBridge.complexify (M.rootedTreeSeriesReal w) := by
  have hself := M.rootedTreeSeries_isSelfAdjoint w hw
  change M.rootedTreeSeries (w : ℂ) =
    ContinuousMap.realToRCLike ℂ
      (ContinuousMap.rclikeToReal (M.rootedTreeSeries (w : ℂ)))
  exact (ContinuousMap.IsSelfAdjoint.realToRCLike_rclikeToReal hself).symm

/-- The finite actual labelled-tree sums converge, on the real part of the
convergence ball, to the canonical real profile of the complex Taylor sum. -/
theorem CompactBJRModel.rootedTreePartialSum_tendsto_seriesReal
    (M : CompactBJRModel S) (w : ℝ)
    (hw : (w : ℂ) ∈
      Metric.eball 0 M.complexTypeRootedTreeFMS.radius) :
    Filter.Tendsto (fun N => M.rootedTreePartialSum N w)
      Filter.atTop (nhds (M.rootedTreeSeriesReal w)) := by
  change Filter.Tendsto (fun N => M.rootedTreePartialSum N w)
    Filter.atTop
    (nhds (ContinuousMap.rclikeToReal (M.rootedTreeSeries (w : ℂ))))
  have hsum := (M.complexTypeRootedTreeFMS_hasSum hw).tendsto_sum_nat
  have hcont : Continuous
      (ContinuousMap.rclikeToReal : C(S, ℂ) → C(S, ℝ)) :=
    ContinuousMap.continuous_rclikeToReal S ℂ
  have hre := (hcont.tendsto (M.rootedTreeSeries (w : ℂ))).comp hsum
  convert hre using 1
  funext N
  simp only [Function.comp_apply]
  rw [M.complexTypeRootedTreeFMS_partialSum_real]
  exact (ContinuousMap.rclikeToReal_realToRCLike ℂ
    (M.rootedTreePartialSum N w)).symm

/-- Whenever a real point `0 ≤ w ≤ 1` lies in the convergence ball, the
canonical real rooted-tree sum lies pointwise in `[0,1]`. -/
theorem CompactBJRModel.rootedTreeSeriesReal_bounded
    (M : CompactBJRModel S) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hconv : (w : ℂ) ∈
      Metric.eball 0 M.complexTypeRootedTreeFMS.radius) (x : S) :
    0 ≤ M.rootedTreeSeriesReal w x ∧
      M.rootedTreeSeriesReal w x ≤ 1 := by
  have hlim := M.rootedTreePartialSum_tendsto_seriesReal w hconv
  have hpoint : Filter.Tendsto
      (fun N => M.rootedTreePartialSum N w x) Filter.atTop
      (nhds (M.rootedTreeSeriesReal w x)) :=
    ((continuous_eval_const x).tendsto _).comp hlim
  refine ⟨ge_of_tendsto' hpoint (fun N =>
      M.rootedTreePartialSum_nonneg N hw x), ?_⟩
  exact le_of_tendsto' hpoint (fun N =>
    (M.rootedTreePartialSum_le_normalizedZeroTreeIter N hw x).trans
      (M.normalizedZeroTreeIter_bounded w hw hw1 N x).2)

private theorem CompactBJRModel.real_subcritical_mem_tree_radius
    (M : CompactBJRModel S) {w : ℝ} (hw : 0 ≤ w) (hw1 : w < 1) :
    (w : ℂ) ∈ Metric.eball 0 M.complexTypeRootedTreeFMS.radius := by
  have hwBall : (w : ℂ) ∈ Metric.eball 0 (1 : ℝ≥0∞) := by
    rw [← ENNReal.coe_one, Metric.eball_coe]
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hw, NNReal.coe_one] using hw1
  exact Metric.eball_subset_eball
    M.one_le_complexTypeRootedTreeFMS_radius hwBall

/-- On every real subcritical parameter, the actual labelled rooted-tree
series is the complexification of the unique bounded physical fixed point. -/
theorem CompactBJRModel.rootedTreeSeries_eq_physical_fixedPoint
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) :
    ∃ V : C(S, ℝ),
      Filter.Tendsto (M.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
      (∀ x, 0 ≤ V x ∧ V x ≤ 1) ∧
      M.normalizedZeroTreeMap w V = V ∧
      M.rootedTreeSeries (w : ℂ) =
        TreeRealComplexBridge.complexify V := by
  have hconv := M.real_subcritical_mem_tree_radius hw hw1
  let W : C(S, ℝ) := M.rootedTreeSeriesReal w
  have hWbounds : ∀ x, 0 ≤ W x ∧ W x ≤ 1 :=
    M.rootedTreeSeriesReal_bounded w hw hw1.le hconv
  have hseries : M.rootedTreeSeries (w : ℂ) =
      TreeRealComplexBridge.complexify W :=
    M.rootedTreeSeries_eq_complexify_real w hconv
  have hres : TreeCritical.residual M
      (((w : ℂ), 0), TreeRealComplexBridge.complexify W) = 0 := by
    rw [← hseries]
    exact M.rootedTreeSeries_residual_zero hconv
  have hWfix : M.normalizedZeroTreeMap w W = W :=
    (TreeRealComplexBridge.normalizedZeroTreeMap_fixed_iff_residual_zero
      M w W).mpr hres
  obtain ⟨V, hVlim, hVbounds, hVfix, hunique⟩ :=
    M.normalizedZeroTreeMap_unique_bounded_fixed hM w hw hw1
  have hWV : W = V := hunique W hWbounds hWfix
  refine ⟨V, hVlim, hVbounds, hVfix, ?_⟩
  rw [hseries, hWV]

end PerronWright
