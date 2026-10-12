import PerronWright.Analysis.NormalizedFoldActivity
import PerronWright.Analysis.MarkedPathResolvent
import Mathlib.Analysis.Complex.HasPrimitives

/-!
# The local zero-field tree singularity

The rooted-tree fold profile already gives the singular derivative of the
unrooted tree series.  This file performs the remaining scalar integration
locally in the square-root coordinate.  No primitive or asymptotic expansion
is assumed: the primitive is supplied by the holomorphic primitive theorem on
a disk, and its first non-polynomial term is obtained from Taylor's theorem.
-/

open Filter Topology MeasureTheory
open scoped Topology

noncomputable section

namespace PerronWright.ZeroFieldTreeLocalSingularity

namespace MPR

export PerronWright.MarkedPathResolvent
  (scalarIntegralCLM scalarIntegralCLM_apply)

end MPR

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The scalar vertex-rooted tree profile in the zero-field fold coordinate. -/
def foldVertexRootedScalar (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (X : ℂ) : ℂ :=
  MPR.scalarIntegralCLM M
    (TreeNormalizedFoldActivity.foldProfile M hM (0, X))

/-- The scalar fold profile is analytic at the critical point. -/
theorem foldVertexRootedScalar_analyticAt
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (foldVertexRootedScalar M hM) 0 := by
  have hline : AnalyticAt ℂ
      (fun X : ℂ ↦ ((0 : C(S, ℂ)), X)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hinner :=
    (TreeNormalizedFoldActivity.foldProfile_analytic M hM).comp_of_eq
      hline rfl
  change AnalyticAt ℂ
    (fun X : ℂ => MPR.scalarIntegralCLM M
      (TreeNormalizedFoldActivity.foldProfile M hM (0, X))) 0
  exact ((MPR.scalarIntegralCLM M).analyticAt _).comp hinner

/-- At the critical point the scalar vertex-rooted profile equals one. -/
@[simp] theorem foldVertexRootedScalar_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    foldVertexRootedScalar M hM 0 = 1 := by
  rw [foldVertexRootedScalar,
    TreeNormalizedFoldActivity.foldProfile_base,
    MPR.scalarIntegralCLM_apply]
  simp only [ContinuousMap.one_apply, integral_const, probReal_univ,
    one_smul]

/-- Its first fold-coordinate derivative is the negative fold amplitude. -/
theorem foldVertexRootedScalar_deriv_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    deriv (foldVertexRootedScalar M hM) 0 =
      -(FoldCoefficients.gamma M hM : ℂ) := by
  let T : ℂ → C(S, ℂ) := fun X ↦
    TreeNormalizedFoldActivity.foldProfile M hM (0, X)
  have hTa : AnalyticAt ℂ T 0 := by
    have hline : AnalyticAt ℂ
        (fun X : ℂ ↦ ((0 : C(S, ℂ)), X)) 0 :=
      analyticAt_const.prod analyticAt_id
    exact (TreeNormalizedFoldActivity.foldProfile_analytic M hM).comp_of_eq
      hline rfl
  have hTd : deriv T 0 =
      (-(FoldCoefficients.gamma M hM : ℂ)) •
        M.complexPerronFunction hM := by
    exact TreeNormalizedFoldActivity.foldProfile_vertical_deriv M hM
  have hTderiv : HasDerivAt T
      ((-(FoldCoefficients.gamma M hM : ℂ)) •
        M.complexPerronFunction hM) 0 := by
    simpa only [hTd] using hTa.differentiableAt.hasDerivAt
  have hcomp := (MPR.scalarIntegralCLM M).hasFDerivAt.comp_hasDerivAt
    (x := 0) hTderiv
  have hint : MPR.scalarIntegralCLM M
      ((-(FoldCoefficients.gamma M hM : ℂ)) •
        M.complexPerronFunction hM) =
      -(FoldCoefficients.gamma M hM : ℂ) := by
    rw [map_smul, MPR.scalarIntegralCLM_apply]
    simp only [smul_eq_mul]
    have hu := M.perronFunction_integral hM
    have huc : (∫ x, M.complexPerronFunction hM x ∂M.mu) = 1 := by
      change (∫ x, (M.perronFunction hM x : ℂ) ∂M.mu) = 1
      calc
        (∫ x, (M.perronFunction hM x : ℂ) ∂M.mu) =
            Complex.ofReal (∫ x, M.perronFunction hM x ∂M.mu) := by
          exact integral_complex_ofReal
        _ = 1 := by rw [hu]; rfl
    rw [huc, mul_one]
  change deriv (fun X : ℂ ↦ MPR.scalarIntegralCLM M (T X)) 0 = _
  exact hcomp.deriv.trans hint

/-- The fold-coordinate derivative forced by
`w U'(w)=V(w)` and `w=1-X²`. -/
def treeFoldDerivative (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (X : ℂ) : ℂ :=
  (-2 * X) * foldVertexRootedScalar M hM X / (1 - X ^ 2)

@[simp] theorem treeFoldDerivative_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    treeFoldDerivative M hM 0 = 0 := by
  simp [treeFoldDerivative]

/-- The derivative of the local unrooted-tree continuation has the exact
quadratic jet `-2X + 2γX²`; its analytic remainder is divisible by `X³`.
This is the differential form of the cubic tree singularity. -/
theorem exists_treeFoldDerivative_cubic_remainder
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ Q : ℂ → ℂ, AnalyticAt ℂ Q 0 ∧
      ∀ᶠ X : ℂ in 𝓝 0,
        treeFoldDerivative M hM X =
          -2 * X + 2 * (FoldCoefficients.gamma M hM : ℂ) * X ^ 2 +
            X ^ 3 * Q X := by
  let V := foldVertexRootedScalar M hM
  have hVa : AnalyticAt ℂ V 0 := foldVertexRootedScalar_analyticAt M hM
  have hV0 : V 0 = 1 := foldVertexRootedScalar_zero M hM
  have hVd : deriv V 0 = -(FoldCoefficients.gamma M hM : ℂ) :=
    foldVertexRootedScalar_deriv_zero M hM
  obtain ⟨A, hAa, hAeq⟩ := hVa.exists_eq_sum_add_pow_mul 2
  have hVjet : ∀ X : ℂ,
      V X = 1 - (FoldCoefficients.gamma M hM : ℂ) * X + X ^ 2 * A X := by
    intro X
    rw [hAeq]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      iteratedDeriv_succ, iteratedDeriv_zero,
      hV0, hVd, smul_eq_mul]
    norm_num
    ring
  let Q : ℂ → ℂ := fun X =>
    (-2 * A X - 2 + 2 * (FoldCoefficients.gamma M hM : ℂ) * X) /
      (1 - X ^ 2)
  have hQa : AnalyticAt ℂ Q 0 := by
    have hnum : AnalyticAt ℂ
        (fun X : ℂ => (-2 : ℂ) * A X - 2 +
          2 * (FoldCoefficients.gamma M hM : ℂ) * X) 0 := by
      fun_prop
    have hdena : AnalyticAt ℂ (fun X : ℂ => 1 - X ^ 2) 0 := by
      fun_prop
    exact hnum.div hdena (by norm_num)
  refine ⟨Q, hQa, ?_⟩
  have hdena : AnalyticAt ℂ (fun X : ℂ => 1 - X ^ 2) 0 := by
    fun_prop
  have hden : ∀ᶠ X : ℂ in 𝓝 0, 1 - X ^ 2 ≠ 0 :=
    hdena.continuousAt.eventually_ne (by norm_num)
  filter_upwards [hden] with X hX
  rw [treeFoldDerivative,
    show foldVertexRootedScalar M hM X = V X from rfl, hVjet]
  dsimp only [Q]
  field_simp
  ring

/-- The differential singularity has a normalized analytic primitive on a
genuine disk.  This is the local analytic realization of the unrooted tree
series, up to the single additive constant fixed later by matching to the
convergent Taylor series. -/
theorem exists_normalized_zeroFieldTree_fold_primitive
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (U : ℂ → ℂ) (r : ℝ),
      0 < r ∧ U 0 = 0 ∧
      AnalyticOnNhd ℂ U (Metric.ball (0 : ℂ) r) ∧
      ∀ X ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt U (treeFoldDerivative M hM X) X := by
  have hha : AnalyticAt ℂ (treeFoldDerivative M hM) 0 :=
    ((analyticAt_const.mul analyticAt_id).mul
      (foldVertexRootedScalar_analyticAt M hM)).div
        (analyticAt_const.sub (analyticAt_id.pow 2)) (by norm_num)
  obtain ⟨r, hr, hball⟩ := hha.exists_ball_analyticOnNhd
  have hdiff : DifferentiableOn ℂ (treeFoldDerivative M hM)
      (Metric.ball (0 : ℂ) r) :=
    (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).mp hball
  obtain ⟨U, hU0, hUderiv⟩ :=
    (hdiff.isExactOn_ball.with_val_at (0 : ℂ) (0 : ℂ))
  have hUdiff : DifferentiableOn ℂ U (Metric.ball (0 : ℂ) r) := by
    intro X hX
    exact (hUderiv X hX).differentiableAt.differentiableWithinAt
  have hUa : AnalyticOnNhd ℂ U (Metric.ball (0 : ℂ) r) :=
    (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).mpr
      hUdiff
  exact ⟨U, r, hr, hU0, hUa, hUderiv⟩

end PerronWright.ZeroFieldTreeLocalSingularity
