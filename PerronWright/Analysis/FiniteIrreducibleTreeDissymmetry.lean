import PerronWright.Analysis.FiniteIrreducibleZeroFieldTreeLocalSingularity
import PerronWright.Enumeration.ZeroFieldTreeGlobalContinuation
import PerronWright.Analysis.FiniteIrreducibleNormalizedDeltaProfile

/-!
# Actual finite irreducible tree dissymmetry

The scalar dissymmetry functional and its symmetry calculation are pure
kernel/measure facts. The fold primitive and its matching to the actual tree
series use the constructed finite critical fold, without B2 or primitivity.
-/

open Filter Topology MeasureTheory Set
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.FiniteIrreducibleTreeDissymmetry

export PerronWright.ZeroFieldTreeGlobalContinuation
  (treeDissymmetryFunctional treeDissymmetryFunctional_analyticAt
   treeDissymmetryFunctional_analyticOnNhd treeDissymmetryFunctional_hasDerivAt
   treeDissymmetryFunctional_hasDerivAt_of_fixedPoint zeroFieldTreeSeries_zero)

namespace Match
export PerronWright.ZeroFieldTreeEGFMatching
  (zeroFieldTreeSeries zeroFieldTreeSeries_analyticOnNhd_unit
   rooted_equals_X_mul_tree_deriv_on_unit scalarRootedTreeSeries)
end Match

namespace MPR
export PerronWright.FiniteIrreducibleMarkedPathResolvent
  (scalarIntegralCLM scalarIntegralCLM_apply)
end MPR

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- Equality of the actual finite integration map with the pure discrete BJR
data integration map. This is a definitional bridge, not a regularity adapter. -/
theorem scalarIntegralCLM_eq_bjr (M : FiniteIrreducibleModel S) :
    MPR.scalarIntegralCLM M = MarkedPathResolvent.scalarIntegralCLM M.bjrModel := rfl

/-- The dissymmetry functional evaluated on the canonical zero-field fold
profile.  Unlike the global activity chart, this function is analytic across
the fold point `X = 0`. -/
def zeroFieldFoldDissymmetry (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (X : ℂ) : ℂ :=
  treeDissymmetryFunctional M.bjrModel
    (FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM (0, X))

/-- On a genuine disk around the fold point, the fold dissymmetry functional
is an analytic primitive of the previously constructed tree fold
derivative. -/
theorem exists_zeroFieldFoldDissymmetry_derivative
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ (zeroFieldFoldDissymmetry M hM)
        (Metric.ball (0 : ℂ) r) ∧
      ∀ X ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt (zeroFieldFoldDissymmetry M hM)
          (FiniteIrreducibleZeroFieldTreeLocalSingularity.treeFoldDerivative M hM X) X := by
  let T : ℂ → C(S, ℂ) := fun X ↦
    FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM (0, X)
  have hT0 : AnalyticAt ℂ T 0 := by
    exact (FiniteIrreducibleNormalizedFoldActivity.foldProfile_analytic M hM).comp_of_eq
      (analyticAt_const.prod analyticAt_id) rfl
  have hline : Tendsto (fun X : ℂ ↦ ((0 : C(S, ℂ)), X))
      (nhds 0) (nhds ((0 : C(S, ℂ)), (0 : ℂ))) :=
    continuousAt_const.prodMk continuousAt_id
  have hres : ∀ᶠ X : ℂ in nhds 0,
      TreeCritical.residual M.bjrModel (((1 - X ^ 2 : ℂ), 0), T X) = 0 := by
    simpa only [T, FiniteIrreducibleRadiusResponse.radius_base, one_mul,
      FiniteIrreducibleModel.treeResidual] using
      hline.eventually
        (FiniteIrreducibleNormalizedFoldActivity.foldProfile_residual M hM)
  have hgood : ∀ᶠ X : ℂ in nhds 0,
      AnalyticAt ℂ T X ∧
        TreeCritical.residual M.bjrModel (((1 - X ^ 2 : ℂ), 0), T X) = 0 :=
    hT0.eventually_analyticAt.and hres
  obtain ⟨r0, hr0, hball0⟩ := Metric.mem_nhds_iff.mp hgood
  let r : ℝ := min r0 1
  have hr : 0 < r := lt_min hr0 zero_lt_one
  have hr0' : r ≤ r0 := min_le_left r0 1
  have hr1 : r ≤ 1 := min_le_right r0 1
  have hTan : AnalyticOnNhd ℂ T (Metric.ball (0 : ℂ) r) := by
    intro X hX
    exact (hball0 (Metric.ball_subset_ball hr0' hX)).1
  have hHan : AnalyticOnNhd ℂ (zeroFieldFoldDissymmetry M hM)
      (Metric.ball (0 : ℂ) r) := by
    change AnalyticOnNhd ℂ
      (fun X : ℂ ↦ treeDissymmetryFunctional M.bjrModel
        (FiniteIrreducibleNormalizedFoldActivity.foldProfile M hM (0, X)))
      (Metric.ball (0 : ℂ) r)
    exact treeDissymmetryFunctional_analyticOnNhd M.bjrModel hTan
  refine ⟨r, hr, hHan, ?_⟩
  intro X hX
  have hX0 : X ∈ Metric.ball (0 : ℂ) r0 :=
    Metric.ball_subset_ball hr0' hX
  have hTX : HasDerivAt T (deriv T X) X :=
    (hball0 hX0).1.differentiableAt.hasDerivAt
  have hzne : (1 - X ^ 2 : ℂ) ≠ 0 := by
    intro hzero
    have hpow : X ^ 2 = 1 := (sub_eq_zero.mp hzero).symm
    have hnorm : ‖X‖ ^ 2 = 1 := by
      rw [← norm_pow, hpow, norm_one]
    have hnormlt : ‖X‖ < 1 := by
      have : ‖X‖ < r := by
        simpa only [Metric.mem_ball, dist_zero_right] using hX
      exact this.trans_le hr1
    nlinarith [norm_nonneg X]
  have hz : HasDerivAt (fun Y : ℂ ↦ 1 - Y ^ 2) (-2 * X) X := by
    have hraw :=
      (hasDerivAt_const X (1 : ℂ)).sub ((hasDerivAt_id X).pow 2)
    have heq : (fun Y : ℂ ↦ 1 - Y ^ 2) =ᶠ[nhds X]
        ((fun _Y : ℂ ↦ 1) - id ^ 2) :=
      Filter.Eventually.of_forall (fun Y ↦ by simp [pow_two])
    apply (hraw.congr_of_eventuallyEq heq).congr_deriv
    simp [id]
  have hfix : ∀ᶠ Y : ℂ in nhds X,
      T Y = (1 - Y ^ 2) • NormedSpace.exp
        (-TreeCritical.degree M.bjrModel +
          M.bjrModel.kernel.complexActionCLM M.bjrModel.mu (T Y)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hX] with Y hY
    have hresY := (hball0
      (Metric.ball_subset_ball hr0' hY)).2
    change T Y - (1 - Y ^ 2) • NormedSpace.exp
      ((0 : C(S, ℂ)) - TreeCritical.degree M.bjrModel +
        M.bjrModel.kernel.complexActionCLM M.bjrModel.mu (T Y)) = 0 at hresY
    simpa only [zero_sub] using sub_eq_zero.mp hresY
  have hprimitive :=
    treeDissymmetryFunctional_hasDerivAt_of_fixedPoint
      (M := M.bjrModel) (z := fun Y : ℂ ↦ 1 - Y ^ 2) (T := T)
      hz hTX hfix hzne
  apply hprimitive.congr_deriv
  simp only [FiniteIrreducibleZeroFieldTreeLocalSingularity.treeFoldDerivative,
    FiniteIrreducibleZeroFieldTreeLocalSingularity.foldVertexRootedScalar, T,
    scalarIntegralCLM_eq_bjr]

/-- The global dissymmetry chart is the literal unrooted-tree EGF throughout
the open unit disk. -/
theorem global_dissymmetry_eq_zeroFieldTreeSeries_on_unit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {eta : ℝ} {theta : ℂ → C(S, ℂ)} {G : ℂ → ℂ}
    (heta : 0 < eta)
    (_htheta : AnalyticOnNhd ℂ theta (Transfer.cartesianDelta eta 0))
    (hG : AnalyticOnNhd ℂ G (Transfer.cartesianDelta eta 0))
    (hthetaInside : Set.EqOn theta M.bjrModel.rootedTreeSeries
      (Metric.ball (0 : ℂ) 1))
    (hGdef : ∀ w : ℂ, G w = treeDissymmetryFunctional M.bjrModel (theta w))
    (hGderiv : ∀ w ∈ Transfer.cartesianDelta eta 0, w ≠ 0 →
      deriv G w = MPR.scalarIntegralCLM M (theta w) / w) :
    Set.EqOn G (Match.zeroFieldTreeSeries M.bjrModel)
      (Metric.ball (0 : ℂ) 1) := by
  let U : Set ℂ := Metric.ball (0 : ℂ) 1
  have hUsub : U ⊆ Transfer.cartesianDelta eta 0 :=
    Transfer.unit_ball_subset_cartesianDelta heta
  have hGunit : AnalyticOnNhd ℂ G U := hG.mono hUsub
  have hTree : AnalyticOnNhd ℂ (Match.zeroFieldTreeSeries M.bjrModel) U :=
    Match.zeroFieldTreeSeries_analyticOnNhd_unit M.bjrModel
  have hderivEq_of_ne {w : ℂ} (hw : w ∈ U) (hwne : w ≠ 0) :
      deriv G w = deriv (Match.zeroFieldTreeSeries M.bjrModel) w := by
    have hroot := Match.rooted_equals_X_mul_tree_deriv_on_unit M.bjrModel hw
    have hscalar : MPR.scalarIntegralCLM M (theta w) =
        Match.scalarRootedTreeSeries M.bjrModel w := by
      rw [hthetaInside hw]
      rfl
    have htreeDeriv : deriv (Match.zeroFieldTreeSeries M.bjrModel) w =
        MPR.scalarIntegralCLM M (theta w) / w := by
      apply (eq_div_iff hwne).2
      rw [hscalar]
      simpa only [mul_comm] using hroot
    rw [hGderiv w (hUsub hw) hwne, htreeDeriv]
  let w₀ : ℂ := (1 / 2 : ℂ)
  have hw₀U : w₀ ∈ U := by
    simp only [U, w₀, Metric.mem_ball, dist_zero_right]
    norm_num
  have hw₀ne : w₀ ≠ 0 := by norm_num [w₀]
  have hevent : ∀ᶠ w : ℂ in nhds w₀,
      deriv G w = deriv (Match.zeroFieldTreeSeries M.bjrModel) w := by
    have hUnhds : U ∈ nhds w₀ := Metric.isOpen_ball.mem_nhds hw₀U
    have hnenhds : ({0}ᶜ : Set ℂ) ∈ nhds w₀ :=
      isOpen_compl_singleton.mem_nhds (by simpa using hw₀ne)
    filter_upwards [hUnhds, hnenhds] with w hwU hwne
    exact hderivEq_of_ne hwU (by simpa using hwne)
  have hderivEq : Set.EqOn (deriv G)
      (deriv (Match.zeroFieldTreeSeries M.bjrModel)) U :=
    hGunit.deriv.eqOn_of_preconnected_of_eventuallyEq hTree.deriv
      (convex_ball (0 : ℂ) 1).isPreconnected hw₀U hevent
  have hzeroU : (0 : ℂ) ∈ U := Metric.mem_ball_self zero_lt_one
  have hrootZero : M.bjrModel.rootedTreeSeries 0 = 0 := by
    have hres := M.rootedTreeSeries_residual_zero_openDisk hM
      (z := (0 : ℂ)) (by norm_num)
    change M.bjrModel.rootedTreeSeries 0 -
      (0 : ℂ) • NormedSpace.exp
        ((0 : C(S, ℂ)) - TreeCritical.degree M.bjrModel +
          M.bjrModel.kernel.complexActionCLM M.bjrModel.mu (M.bjrModel.rootedTreeSeries 0)) = 0 at hres
    simpa only [zero_smul, sub_zero] using hres
  have hthetaZero : theta 0 = 0 := by
    rw [hthetaInside hzeroU, hrootZero]
  have hGzero : G 0 = Match.zeroFieldTreeSeries M.bjrModel 0 := by
    rw [hGdef, hthetaZero, zeroFieldTreeSeries_zero]
    simp [treeDissymmetryFunctional]
  exact Metric.isOpen_ball.eqOn_of_deriv_eq
    (convex_ball (0 : ℂ) 1).isPreconnected
    hGunit.differentiableOn hTree.differentiableOn hderivEq
    hzeroU hGzero


end PerronWright.FiniteIrreducibleTreeDissymmetry
