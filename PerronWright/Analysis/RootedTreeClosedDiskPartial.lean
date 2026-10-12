import PerronWright.Analysis.RootedTreeUnitCircleGerm

/-!
# The rooted-tree implicit derivative on the noncritical closed unit disk

The unit-circle argument already proves the strict norm margin away from the
critical point.  In the open disk, coefficient positivity gives the sharper
pointwise estimate `|T(z,x)| ≤ |z|`.  Combining the two cases makes the
unknown derivative of the genuine tree residual invertible at every point of
the closed unit disk except `z = 1`.
-/

open Filter
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem CompactBJRModel.rootedTreeSeries_apply_norm_le_norm_of_norm_lt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ < 1) (x : S) :
    ‖M.rootedTreeSeries z x‖ ≤ ‖z‖ := by
  have hzle : ‖z‖ ≤ 1 := hz.le
  have hc := ContinuousMap.hasSum_apply
    (M.complexTypeRootedTreeFMS_hasSum_closedDisk hM hzle) x
  have hr := ContinuousMap.hasSum_apply
    (M.typeRootedTreeEGF_hasSum_one hM) x
  have hrz : HasSum
      (fun n : ℕ => ‖z‖ * PowerSeries.coeff n M.typeRootedTreeEGF x)
      ‖z‖ := by
    simpa only [ContinuousMap.one_apply, mul_one] using hr.mul_left ‖z‖
  apply hc.norm_le_of_bounded hrz
  intro n
  rw [M.complexTypeRootedTreeFMS_apply]
  simp only [ContinuousMap.smul_apply,
    continuousMapComplexifyRingHom_apply,
    TreeRealComplexBridge.complexify_apply, smul_eq_mul,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (M.typeRootedTreeEGF_coeff_nonneg n x)]
  cases n with
  | zero =>
      simp only [pow_zero]
      rw [M.typeRootedTreeEGF_coeff_zero]
      simp only [ContinuousMap.zero_apply, mul_zero]
      exact le_rfl
  | succ n =>
      rw [pow_succ]
      have hpow : ‖z‖ ^ n ≤ 1 := by
        exact pow_le_one₀ (norm_nonneg z) hzle
      have hnonneg : 0 ≤ PowerSeries.coeff (n + 1) M.typeRootedTreeEGF x :=
        M.typeRootedTreeEGF_coeff_nonneg (n + 1) x
      have hfactor : ‖z‖ ^ n * ‖z‖ ≤ ‖z‖ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hpow (norm_nonneg z)
      exact mul_le_mul_of_nonneg_right hfactor hnonneg

/-- The genuine rooted-tree profile has norm strictly below one at every
point of the closed unit disk other than the critical point `1`. -/
theorem CompactBJRModel.rootedTreeSeries_norm_lt_one_of_closedDisk_ne_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    ‖M.rootedTreeSeries z‖ < 1 := by
  rcases lt_or_eq_of_le hz with hzlt | hzeq
  · exact ((M.rootedTreeSeries z).norm_lt_iff zero_lt_one).mpr fun x =>
      (M.rootedTreeSeries_apply_norm_le_norm_of_norm_lt_one hM hzlt x).trans_lt hzlt
  · exact M.rootedTreeSeries_norm_lt_one_of_unit hM hzeq hz1

/-- At every noncritical point of the closed unit disk, the derivative in the
unknown profile of the actual tree residual is invertible. -/
theorem CompactBJRModel.rootedTreeSeries_closedDisk_partial_isUnit
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    IsUnit (fderiv ℂ (TreeCritical.residual M)
      ((z, 0), M.rootedTreeSeries z) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)) := by
  let U := M.rootedTreeSeries z
  let K := M.kernel.complexActionCLM M.mu
  have hres : TreeCritical.residual M ((z, 0), U) = 0 :=
    M.rootedTreeSeries_residual_zero_closedDisk hM hz
  have htree : U = z • NormedSpace.exp
      (-(TreeCritical.degree M) + K U) := by
    have hres' : U - z • NormedSpace.exp
        (-(TreeCritical.degree M) + K U) = 0 := by
      simpa only [TreeCritical.residual, TreeAnalytic.residual,
        zero_sub] using hres
    exact sub_eq_zero.mp hres'
  have hlin : z •
      (NormedSpace.exp (-(TreeCritical.degree M) + K U) • K) =
      TreeOuterNeumann.weightedComplexAction M U := by
    ext f x
    simp only [smul_apply, ContinuousMap.smul_apply, smul_eq_mul,
      TreeOuterNeumann.weightedComplexAction_apply,
      ContinuousMap.mul_apply]
    have hpt := congrArg (fun F : C(S, ℂ) => F x) htree
    simp only [ContinuousMap.smul_apply, smul_eq_mul] at hpt
    rw [hpt]
    ring
  have hpartial : fderiv ℂ (TreeCritical.residual M) ((z, 0), U) ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ) =
      1 - TreeOuterNeumann.weightedComplexAction M U := by
    change fderiv ℂ
      (TreeAnalytic.residual M.kernel M.mu (TreeCritical.degree M))
      ((z, 0), U) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ) = _
    rw [TreeAnalytic.residual_partial]
    simpa only [zero_sub, ContinuousLinearMap.one_def] using congrArg
      (fun A : C(S, ℂ) →L[ℂ] C(S, ℂ) =>
        ContinuousLinearMap.id ℂ C(S, ℂ) - A) hlin
  rw [show M.rootedTreeSeries z = U from rfl, hpartial]
  let q : ℝ := ‖U‖
  have hq : 0 ≤ q := norm_nonneg U
  have hq1 : q < 1 := by
    exact M.rootedTreeSeries_norm_lt_one_of_closedDisk_ne_one hM hz hz1
  have hU (x : S) : ‖U x‖ ≤ q := U.norm_coe_le_norm x
  exact TreeOuterNeumann.weightedComplexAction_one_sub_isUnit
    M hM U q hq hq1 hU

end PerronWright
