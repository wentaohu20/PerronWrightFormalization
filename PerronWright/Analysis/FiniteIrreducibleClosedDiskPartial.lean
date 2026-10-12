import PerronWright.Analysis.FiniteIrreducibleClosedDisk
import PerronWright.Analysis.FiniteIrreducibleOuterNeumann
import PerronWright.Analysis.RootedTreeUnitCircleGerm

/-! Genuine closed-disk residual and invertible partial tree derivative,
including the noncritical unit circle of a possibly bipartite kernel. -/
open Filter
open scoped Classical Topology ENNReal NNReal
noncomputable section
namespace PerronWright
variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- Inside the ordinary unit disk, the exact-radius theorem identifies the
convergence ball needed by the existing residual identity. -/
theorem FiniteIrreducibleModel.rootedTreeSeries_residual_zero_openDisk
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {z : ℂ} (hz : ‖z‖ < 1) :
    TreeCritical.residual M.bjrModel ((z, 0), M.bjrModel.rootedTreeSeries z) = 0 := by
  apply M.bjrModel.rootedTreeSeries_residual_zero
  rw [M.complexTypeRootedTreeFMS_radius_eq_one hM,
    ← ENNReal.coe_one, Metric.eball_coe]
  simpa only [Metric.mem_ball, dist_zero_right, NNReal.coe_one] using hz

/-- Radial points `n/(n+1) z` approach a closed-disk point from the open
disk. -/
private theorem radial_unitDisk_tendsto {z : ℂ} :
    Filter.Tendsto
      (fun n : ℕ => (((n : ℝ) / (n + 1) : ℝ) : ℂ) * z)
      Filter.atTop (nhds z) := by
  have hr : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) / (n + 1)) Filter.atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have hc : Filter.Tendsto
      (fun n : ℕ => (((n : ℝ) / (n + 1) : ℝ) : ℂ))
      Filter.atTop (nhds (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  simpa only [one_mul] using hc.mul_const z

private theorem radial_unitDisk_norm_lt_one {z : ℂ} (hz : ‖z‖ ≤ 1)
    (n : ℕ) :
    ‖(((n : ℝ) / (n + 1) : ℝ) : ℂ) * z‖ < 1 := by
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hr0 : (0 : ℝ) ≤ (n : ℝ) / (n + 1) := by positivity
  have hr1 : (n : ℝ) / (n + 1) < 1 := by
    rw [div_lt_one hden]
    norm_num
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0]
  calc
    (n : ℝ) / (n + 1) * ‖z‖ ≤
        (n : ℝ) / (n + 1) * 1 :=
      mul_le_mul_of_nonneg_left hz hr0
    _ = (n : ℝ) / (n + 1) := mul_one _
    _ < 1 := hr1

/-- The actual closed-disk sum satisfies the genuine compact-BJR tree
equation even on the boundary.  This is obtained by radial continuity, not
by asserting boundary analyticity of the Taylor series. -/
theorem FiniteIrreducibleModel.rootedTreeSeries_residual_zero_closedDisk
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    TreeCritical.residual M.bjrModel ((z, 0), M.bjrModel.rootedTreeSeries z) = 0 := by
  let zseq : ℕ → ℂ := fun n =>
    (((n : ℝ) / (n + 1) : ℝ) : ℂ) * z
  have hzseq : Filter.Tendsto zseq Filter.atTop (nhds z) :=
    radial_unitDisk_tendsto
  have hzseq_mem : ∀ n, zseq n ∈ {w : ℂ | ‖w‖ ≤ 1} := by
    intro n
    exact (radial_unitDisk_norm_lt_one hz n).le
  have hzWithin : Filter.Tendsto zseq Filter.atTop
      (nhdsWithin z {w : ℂ | ‖w‖ ≤ 1}) :=
    (tendsto_nhdsWithin_iff.mpr
      ⟨hzseq, Filter.Eventually.of_forall hzseq_mem⟩)
  have hTseq : Filter.Tendsto
      (fun n => M.bjrModel.rootedTreeSeries (zseq n)) Filter.atTop
      (nhds (M.bjrModel.rootedTreeSeries z)) :=
    (M.rootedTreeSeries_continuousOn_closedDisk hM z hz).tendsto.comp hzWithin
  have hpair : Filter.Tendsto
      (fun n => ((zseq n, (0 : C(S, ℂ))), M.bjrModel.rootedTreeSeries (zseq n)))
      Filter.atTop
      (nhds ((z, (0 : C(S, ℂ))), M.bjrModel.rootedTreeSeries z)) :=
    (hzseq.prodMk_nhds tendsto_const_nhds).prodMk_nhds hTseq
  have hresT : Filter.Tendsto
      (fun n => TreeCritical.residual M.bjrModel
        ((zseq n, 0), M.bjrModel.rootedTreeSeries (zseq n)))
      Filter.atTop
      (nhds (TreeCritical.residual M.bjrModel ((z, 0), M.bjrModel.rootedTreeSeries z))) :=
    (TreeAnalytic.residual_analytic M.bjrModel.kernel M.bjrModel.mu
      (TreeCritical.degree M.bjrModel)
      ((z, (0 : C(S, ℂ))), M.bjrModel.rootedTreeSeries z)).continuousAt.tendsto.comp hpair
  have hzero : ∀ n, TreeCritical.residual M.bjrModel
      ((zseq n, 0), M.bjrModel.rootedTreeSeries (zseq n)) = 0 := by
    intro n
    exact M.rootedTreeSeries_residual_zero_openDisk hM
      (radial_unitDisk_norm_lt_one hz n)
  have hresZero : Filter.Tendsto
      (fun n => TreeCritical.residual M.bjrModel
        ((zseq n, 0), M.bjrModel.rootedTreeSeries (zseq n)))
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => (0 : C(S, ℂ))) Filter.atTop (nhds 0)) using 1
    funext n
    exact hzero n
  exact tendsto_nhds_unique hresT hresZero

/-- At a noncritical unit-circle point, the unknown derivative of the actual
tree equation is invertible. -/
theorem FiniteIrreducibleModel.rootedTreeSeries_unit_partial_isUnit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    IsUnit (fderiv ℂ (TreeCritical.residual M.bjrModel)
      ((z, 0), M.bjrModel.rootedTreeSeries z) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)) := by
  let U := M.bjrModel.rootedTreeSeries z
  let K := M.bjrModel.kernel.complexActionCLM M.bjrModel.mu
  have hres : TreeCritical.residual M.bjrModel ((z, 0), U) = 0 :=
    M.rootedTreeSeries_residual_zero_closedDisk hM hz.le
  have htree : U = z • NormedSpace.exp
      (-(TreeCritical.degree M.bjrModel) + K U) := by
    have hres' : U - z • NormedSpace.exp
        (-(TreeCritical.degree M.bjrModel) + K U) = 0 := by
      simpa only [TreeCritical.residual, TreeAnalytic.residual,
        zero_sub] using hres
    exact sub_eq_zero.mp hres'
  have hlin : z •
      (NormedSpace.exp (-(TreeCritical.degree M.bjrModel) + K U) • K) =
      FiniteIrreducibleOuterNeumann.weightedComplexAction M U := by
    ext f x
    simp only [smul_apply, ContinuousMap.smul_apply, smul_eq_mul,
      FiniteIrreducibleOuterNeumann.weightedComplexAction_apply,
      ContinuousMap.mul_apply]
    have hpt := congrArg (fun F : C(S, ℂ) => F x) htree
    simp only [ContinuousMap.smul_apply, smul_eq_mul] at hpt
    rw [hpt]
    have hk : M.complexOperator f = K f := rfl
    rw [hk, mul_assoc]
  have hpartial : fderiv ℂ (TreeCritical.residual M.bjrModel) ((z, 0), U) ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ) =
      1 - FiniteIrreducibleOuterNeumann.weightedComplexAction M U := by
    change fderiv ℂ
      (TreeAnalytic.residual M.bjrModel.kernel M.bjrModel.mu (TreeCritical.degree M.bjrModel))
      ((z, 0), U) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ) = _
    rw [TreeAnalytic.residual_partial]
    simpa only [zero_sub, ContinuousLinearMap.one_def] using congrArg
      (fun A : C(S, ℂ) →L[ℂ] C(S, ℂ) =>
        ContinuousLinearMap.id ℂ C(S, ℂ) - A) hlin
  rw [show M.bjrModel.rootedTreeSeries z = U from rfl, hpartial]
  let q : ℝ := ‖U‖
  have hq : 0 ≤ q := norm_nonneg U
  have hq1 : q < 1 := by
    exact M.rootedTreeSeries_norm_lt_one_of_unit hM hz hz1
  have hU (x : S) : ‖U x‖ ≤ q := U.norm_coe_le_norm x
  exact FiniteIrreducibleOuterNeumann.weightedComplexAction_one_sub_isUnit
    M hM U q hq hq1 hU

private theorem FiniteIrreducibleModel.rootedTreeSeries_apply_norm_le_norm_of_norm_lt_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {z : ℂ} (hz : ‖z‖ < 1) (x : S) :
    ‖M.bjrModel.rootedTreeSeries z x‖ ≤ ‖z‖ := by
  have hzle : ‖z‖ ≤ 1 := hz.le
  have hc := ContinuousMap.hasSum_apply
    (M.complexTypeRootedTreeFMS_hasSum_closedDisk hM hzle) x
  have hr := ContinuousMap.hasSum_apply
    (M.typeRootedTreeEGF_hasSum_one hM) x
  have hrz : HasSum
      (fun n : ℕ => ‖z‖ * PowerSeries.coeff n M.bjrModel.typeRootedTreeEGF x)
      ‖z‖ := by
    simpa only [ContinuousMap.one_apply, mul_one] using hr.mul_left ‖z‖
  apply hc.norm_le_of_bounded hrz
  intro n
  rw [M.bjrModel.complexTypeRootedTreeFMS_apply]
  simp only [ContinuousMap.smul_apply,
    continuousMapComplexifyRingHom_apply,
    TreeRealComplexBridge.complexify_apply, smul_eq_mul,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (M.bjrModel.typeRootedTreeEGF_coeff_nonneg n x)]
  cases n with
  | zero =>
      simp only [pow_zero]
      rw [M.bjrModel.typeRootedTreeEGF_coeff_zero]
      simp only [ContinuousMap.zero_apply, mul_zero]
      exact le_rfl
  | succ n =>
      rw [pow_succ]
      have hpow : ‖z‖ ^ n ≤ 1 := by
        exact pow_le_one₀ (norm_nonneg z) hzle
      have hnonneg : 0 ≤ PowerSeries.coeff (n + 1) M.bjrModel.typeRootedTreeEGF x :=
        M.bjrModel.typeRootedTreeEGF_coeff_nonneg (n + 1) x
      have hfactor : ‖z‖ ^ n * ‖z‖ ≤ ‖z‖ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hpow (norm_nonneg z)
      exact mul_le_mul_of_nonneg_right hfactor hnonneg

/-- The genuine rooted-tree profile has norm strictly below one at every
point of the closed unit disk other than the critical point `1`. -/
theorem FiniteIrreducibleModel.rootedTreeSeries_norm_lt_one_of_closedDisk_ne_one
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    ‖M.bjrModel.rootedTreeSeries z‖ < 1 := by
  rcases lt_or_eq_of_le hz with hzlt | hzeq
  · exact ((M.bjrModel.rootedTreeSeries z).norm_lt_iff zero_lt_one).mpr fun x =>
      (M.rootedTreeSeries_apply_norm_le_norm_of_norm_lt_one hM hzlt x).trans_lt hzlt
  · exact M.rootedTreeSeries_norm_lt_one_of_unit hM hzeq hz1

/-- At every noncritical point of the closed unit disk, the derivative in the
unknown profile of the actual tree residual is invertible. -/
theorem FiniteIrreducibleModel.rootedTreeSeries_closedDisk_partial_isUnit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    IsUnit (fderiv ℂ (TreeCritical.residual M.bjrModel)
      ((z, 0), M.bjrModel.rootedTreeSeries z) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)) := by
  let U := M.bjrModel.rootedTreeSeries z
  let K := M.bjrModel.kernel.complexActionCLM M.bjrModel.mu
  have hres : TreeCritical.residual M.bjrModel ((z, 0), U) = 0 :=
    M.rootedTreeSeries_residual_zero_closedDisk hM hz
  have htree : U = z • NormedSpace.exp
      (-(TreeCritical.degree M.bjrModel) + K U) := by
    have hres' : U - z • NormedSpace.exp
        (-(TreeCritical.degree M.bjrModel) + K U) = 0 := by
      simpa only [TreeCritical.residual, TreeAnalytic.residual,
        zero_sub] using hres
    exact sub_eq_zero.mp hres'
  have hlin : z •
      (NormedSpace.exp (-(TreeCritical.degree M.bjrModel) + K U) • K) =
      FiniteIrreducibleOuterNeumann.weightedComplexAction M U := by
    ext f x
    simp only [smul_apply, ContinuousMap.smul_apply, smul_eq_mul,
      FiniteIrreducibleOuterNeumann.weightedComplexAction_apply,
      ContinuousMap.mul_apply]
    have hpt := congrArg (fun F : C(S, ℂ) => F x) htree
    simp only [ContinuousMap.smul_apply, smul_eq_mul] at hpt
    rw [hpt]
    have hk : M.complexOperator f = K f := rfl
    rw [hk, mul_assoc]
  have hpartial : fderiv ℂ (TreeCritical.residual M.bjrModel) ((z, 0), U) ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ) =
      1 - FiniteIrreducibleOuterNeumann.weightedComplexAction M U := by
    change fderiv ℂ
      (TreeAnalytic.residual M.bjrModel.kernel M.bjrModel.mu (TreeCritical.degree M.bjrModel))
      ((z, 0), U) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ) = _
    rw [TreeAnalytic.residual_partial]
    simpa only [zero_sub, ContinuousLinearMap.one_def] using congrArg
      (fun A : C(S, ℂ) →L[ℂ] C(S, ℂ) =>
        ContinuousLinearMap.id ℂ C(S, ℂ) - A) hlin
  rw [show M.bjrModel.rootedTreeSeries z = U from rfl, hpartial]
  let q : ℝ := ‖U‖
  have hq : 0 ≤ q := norm_nonneg U
  have hq1 : q < 1 := by
    exact M.rootedTreeSeries_norm_lt_one_of_closedDisk_ne_one hM hz hz1
  have hU (x : S) : ‖U x‖ ≤ q := U.norm_coe_le_norm x
  exact FiniteIrreducibleOuterNeumann.weightedComplexAction_one_sub_isUnit
    M hM U q hq hq1 hU

end PerronWright
