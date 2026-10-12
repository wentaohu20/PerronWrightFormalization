import PerronWright.Enumeration.SimpleCycleLogContinuation

/-!
# The zero-field unicyclic singularity constant

This module packages the already constructed logarithmic continuation
as the singular expansion of the genuine zero-field unicyclic EGF.  The
additive constant is the value called `H₁` in the paper: the remaining
analytic term is normalized to vanish at the fold point.  Equivalently,
`H₁` is the unique positive-ray renormalized limit.
-/

open Filter Topology PerronWright Set
open scoped Topology RightActions

noncomputable section

namespace PerronWright.ZeroFieldUnicyclicSingularity

/- Keep the calculus and complex-algebra additive structures aligned. -/
@[reducible] local instance complexAddCommGroup : AddCommGroup ℂ :=
  Complex.instNormedAddCommGroup.toAddCommGroup

namespace MPR

export PerronWright.MarkedPathResolvent (profile)

end MPR

namespace JS

export PerronWright.JointSimpleCycleEGF (profileSimpleCycleSeries)

end JS

namespace SC

export PerronWright.SimpleCycleResolventBridge
  (simpleCycleDerivativeContinuation)

end SC

namespace LogCont

export PerronWright.SimpleCycleLogContinuation
  (exists_simpleCycle_logarithmic_continuation)

end LogCont

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The genuine zero-field unicyclic EGF, obtained by substituting the
actual rooted-tree Taylor sum into the direct profile simple-cycle series. -/
def zeroFieldUnicyclicEGF (M : CompactBJRModel S) (z : ℂ) : ℂ :=
  JS.profileSimpleCycleSeries M (M.rootedTreeSeries z)

/-- The zero-field unicyclic EGF has the paper's logarithmic singularity.
The constant `H₁` is separated from an analytic remainder vanishing at
the fold point.  The complex function `G` is only asserted to be the
continuation of the direct series; equality with the direct series is kept
on the positive physical ray. -/
theorem exists_zeroFieldUnicyclic_singularity_data
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (H₁ : ℂ) (R G : ℂ → ℂ) (r : ℝ),
      0 < r ∧
      AnalyticAt ℂ R 0 ∧
      R 0 = 0 ∧
      (fun X : ℂ => R X) =O[𝓝 (0 : ℂ)] (fun X : ℂ => X) ∧
      (∀ X : ℂ, G X = -(1 / 2 : ℂ) * Complex.log X + R X + H₁) ∧
      IsOpen (Complex.slitPlane ∩ Metric.ball (0 : ℂ) r) ∧
      AnalyticOnNhd ℂ G
        (Complex.slitPlane ∩ Metric.ball (0 : ℂ) r) ∧
      (∀ X : ℂ, X ∈ Complex.slitPlane ∩ Metric.ball (0 : ℂ) r →
        HasDerivAt G
          (SC.simpleCycleDerivativeContinuation M hM
            ((0 : C(S, ℂ)), X)) X) ∧
      ∀ X : ℝ, 0 < X → X < r →
        zeroFieldUnicyclicEGF M ((1 - X ^ 2 : ℝ) : ℂ) = G (X : ℂ) := by
  obtain ⟨B, H, C, rLog, G, hBa, hHa, hHaxis, hrLog,
      hGformula, -, hGanalytic, hGderiv, hphysical⟩ :=
    LogCont.exists_simpleCycle_logarithmic_continuation M hM
  obtain ⟨δ, hδ, hfold⟩ :=
    TreeNormalizedFoldActivity.foldProfile_eq_rootedTreeSeries_real_near_one
      M hM
  let r : ℝ := min rLog (min δ 1)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min hrLog (lt_min hδ zero_lt_one)
  let R : ℂ → ℂ := fun X => H ((0 : C(S, ℂ)), X)
  have hlineAt : AnalyticAt ℂ
      (fun X : ℂ => ((0 : C(S, ℂ)), X)) 0 :=
    analyticAt_const.prod analyticAt_id
  have hRanalytic : AnalyticAt ℂ R 0 := by
    change AnalyticAt ℂ
      (H ∘ fun X : ℂ => ((0 : C(S, ℂ)), X)) 0
    exact hHa.comp_of_eq hlineAt rfl
  have hR0 : R 0 = 0 := by
    simpa only [R] using hHaxis (0 : C(S, ℂ))
  have hRO : (fun X : ℂ => R X) =O[𝓝 (0 : ℂ)] (fun X : ℂ => X) := by
    have h := hRanalytic.differentiableAt.isBigO_sub
    simpa only [hR0, sub_zero] using h
  have hGformula' : ∀ X : ℂ,
      G X = -(1 / 2 : ℂ) * Complex.log X + R X + C := by
    intro X
    simpa only [R] using hGformula X
  have hUsub : Complex.slitPlane ∩ Metric.ball (0 : ℂ) r ⊆
      Complex.slitPlane ∩ Metric.ball (0 : ℂ) rLog := by
    intro X hX
    refine ⟨hX.1, ?_⟩
    have hdist : dist X 0 < r := by
      simpa only [Metric.mem_ball] using hX.2
    rw [Metric.mem_ball]
    exact hdist.trans_le (min_le_left rLog (min δ 1))
  have hGanalytic' : AnalyticOnNhd ℂ G
      (Complex.slitPlane ∩ Metric.ball (0 : ℂ) r) := by
    intro X hX
    exact hGanalytic X (hUsub hX)
  have hGderiv' : ∀ X : ℂ,
      X ∈ Complex.slitPlane ∩ Metric.ball (0 : ℂ) r →
      HasDerivAt G
        (SC.simpleCycleDerivativeContinuation M hM
          ((0 : C(S, ℂ)), X)) X := by
    intro X hX
    exact hGderiv X (hUsub hX)
  have hphysical' : ∀ X : ℝ, 0 < X → X < r →
      zeroFieldUnicyclicEGF M ((1 - X ^ 2 : ℝ) : ℂ) = G (X : ℂ) := by
    intro X hX hXr
    have hXLog : X < rLog :=
      hXr.trans_le (min_le_left rLog (min δ 1))
    have hXδ : X < δ :=
      hXr.trans_le ((min_le_right rLog (min δ 1)).trans
        (min_le_left δ 1))
    have hXone : X < 1 :=
      hXr.trans_le ((min_le_right rLog (min δ 1)).trans
        (min_le_right δ 1))
    let w : ℝ := 1 - X ^ 2
    have hXsq_lt_one : X ^ 2 < 1 := by nlinarith
    have hw0 : 0 ≤ w := by dsimp only [w]; linarith
    have hw1 : w < 1 := by
      dsimp only [w]
      nlinarith [sq_pos_of_pos hX]
    have hXsq_lt_δ : X ^ 2 < δ := by
      have hXsq_lt_X : X ^ 2 < X := by nlinarith
      exact hXsq_lt_X.trans hXδ
    have hclose : |w - 1| < δ := by
      have hwsub : w - 1 = -(X ^ 2) := by dsimp only [w]; ring
      rw [hwsub, abs_neg, abs_of_nonneg (sq_nonneg X)]
      exact hXsq_lt_δ
    have hsqrt : Real.sqrt (1 - w) = X := by
      have hone : 1 - w = X ^ 2 := by dsimp only [w]; ring
      rw [hone, Real.sqrt_sq_eq_abs, abs_of_pos hX]
    have hprofileEq : MPR.profile M hM
          ((0 : C(S, ℂ)), (X : ℂ)) =
        M.rootedTreeSeries ((w : ℝ) : ℂ) := by
      have hseed := hfold w hw0 hw1 hclose
      simpa only [MPR.profile, hsqrt] using hseed
    have hdirect := hphysical X hX hXLog
    change JS.profileSimpleCycleSeries M
        (M.rootedTreeSeries ((w : ℝ) : ℂ)) = G (X : ℂ)
    rw [← hprofileEq]
    exact hdirect
  refine ⟨C, R, G, r, hr, hRanalytic, hR0, hRO, hGformula', ?_,
    hGanalytic', hGderiv', hphysical'⟩
  exact Complex.isOpen_slitPlane.inter Metric.isOpen_ball

end PerronWright.ZeroFieldUnicyclicSingularity
