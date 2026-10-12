import PerronWright.Enumeration.RootedTreeClosedDisk
import PerronWright.Analysis.TreeOuterNeumann

/-!
# Analytic rooted-tree germs at the noncritical unit circle

The genuine closed-disk rooted-tree sum still satisfies the tree equation
on the boundary.  Away from the critical point `1`, its strict norm bound
makes the unknown derivative invertible by the proved Perron-gauge Neumann
argument.  The analytic implicit function theorem then gives a genuine
joint `(z,g)` germ, locally unique and glued to the actual Taylor sum on the
interior side of the unit disk.
-/

open Filter
open scoped Classical Topology ENNReal NNReal
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Inside the ordinary unit disk, the exact-radius theorem identifies the
convergence ball needed by the existing residual identity. -/
theorem CompactBJRModel.rootedTreeSeries_residual_zero_openDisk
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ < 1) :
    TreeCritical.residual M ((z, 0), M.rootedTreeSeries z) = 0 := by
  apply M.rootedTreeSeries_residual_zero
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
theorem CompactBJRModel.rootedTreeSeries_residual_zero_closedDisk
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    TreeCritical.residual M ((z, 0), M.rootedTreeSeries z) = 0 := by
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
      (fun n => M.rootedTreeSeries (zseq n)) Filter.atTop
      (nhds (M.rootedTreeSeries z)) :=
    (M.rootedTreeSeries_continuousOn_closedDisk hM z hz).tendsto.comp hzWithin
  have hpair : Filter.Tendsto
      (fun n => ((zseq n, (0 : C(S, ℂ))), M.rootedTreeSeries (zseq n)))
      Filter.atTop
      (nhds ((z, (0 : C(S, ℂ))), M.rootedTreeSeries z)) :=
    (hzseq.prodMk_nhds tendsto_const_nhds).prodMk_nhds hTseq
  have hresT : Filter.Tendsto
      (fun n => TreeCritical.residual M
        ((zseq n, 0), M.rootedTreeSeries (zseq n)))
      Filter.atTop
      (nhds (TreeCritical.residual M ((z, 0), M.rootedTreeSeries z))) :=
    (TreeAnalytic.residual_analytic M.kernel M.mu
      (TreeCritical.degree M)
      ((z, (0 : C(S, ℂ))), M.rootedTreeSeries z)).continuousAt.tendsto.comp hpair
  have hzero : ∀ n, TreeCritical.residual M
      ((zseq n, 0), M.rootedTreeSeries (zseq n)) = 0 := by
    intro n
    exact M.rootedTreeSeries_residual_zero_openDisk hM
      (radial_unitDisk_norm_lt_one hz n)
  have hresZero : Filter.Tendsto
      (fun n => TreeCritical.residual M
        ((zseq n, 0), M.rootedTreeSeries (zseq n)))
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => (0 : C(S, ℂ))) Filter.atTop (nhds 0)) using 1
    funext n
    exact hzero n
  exact tendsto_nhds_unique hresT hresZero

/-- At a noncritical unit-circle point, the unknown derivative of the actual
tree equation is invertible. -/
theorem CompactBJRModel.rootedTreeSeries_unit_partial_isUnit
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    IsUnit (fderiv ℂ (TreeCritical.residual M)
      ((z, 0), M.rootedTreeSeries z) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)) := by
  let U := M.rootedTreeSeries z
  let K := M.kernel.complexActionCLM M.mu
  have hres : TreeCritical.residual M ((z, 0), U) = 0 :=
    M.rootedTreeSeries_residual_zero_closedDisk hM hz.le
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
    exact M.rootedTreeSeries_norm_lt_one_of_unit hM hz hz1
  have hU (x : S) : ‖U x‖ ≤ q := U.norm_coe_le_norm x
  exact TreeOuterNeumann.weightedComplexAction_one_sub_isUnit
    M hM U q hq hq1 hU

/-- The actual tree profile at a noncritical unit-circle point has a jointly
analytic and locally unique `(z,g)` continuation. -/
theorem CompactBJRModel.rootedTreeSeries_unit_analytic_neighborhood
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ ψ : ℂ × C(S, ℂ) → C(S, ℂ),
      AnalyticAt ℂ ψ (z, 0) ∧
      ψ (z, 0) = M.rootedTreeSeries z ∧
      (∀ᶠ q in 𝓝 (z, 0), TreeCritical.residual M (q, ψ q) = 0) ∧
      ∀ᶠ p in 𝓝 ((z, 0), M.rootedTreeSeries z),
        TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2 := by
  let a : (ℂ × C(S, ℂ)) × C(S, ℂ) :=
    ((z, 0), M.rootedTreeSeries z)
  have hu : IsUnit (fderiv ℂ (TreeCritical.residual M) a ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)) :=
    M.rootedTreeSeries_unit_partial_isUnit hM hz hz1
  have hi : (fderiv ℂ (TreeCritical.residual M) a ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofUnit hu.unit, by
      change (hu.unit : C(S, ℂ) →L[ℂ] C(S, ℂ)) = _
      exact hu.unit_spec⟩
  have hres : TreeCritical.residual M a = 0 :=
    M.rootedTreeSeries_residual_zero_closedDisk hM hz.le
  have hres' : TreeAnalytic.residual M.kernel M.mu
      (TreeCritical.degree M) a = 0 := hres
  obtain ⟨ψ, ha, heq, hloc, huniq⟩ :=
    TreeAnalytic.residual_implicit_exists M.kernel M.mu
      (TreeCritical.degree M) a hi
  rw [hres'] at hloc huniq
  exact ⟨ψ, ha, heq, hloc, huniq⟩

/-- On the interior side of the unit disk, the new boundary germ is exactly
the actual labelled-tree Taylor sum. -/
theorem CompactBJRModel.exists_rootedTreeSeries_unit_germ_glued
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ ψ : ℂ × C(S, ℂ) → C(S, ℂ),
      AnalyticAt ℂ ψ (z, 0) ∧
      ψ (z, 0) = M.rootedTreeSeries z ∧
      (∀ᶠ q in 𝓝 (z, 0), TreeCritical.residual M (q, ψ q) = 0) ∧
      (∀ᶠ p in 𝓝 ((z, 0), M.rootedTreeSeries z),
        TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2) ∧
      ψ ∘ (fun w : ℂ => (w, (0 : C(S, ℂ)))) =ᶠ[
        𝓝[{w : ℂ | ‖w‖ < 1}] z] M.rootedTreeSeries := by
  obtain ⟨ψ, hψa, hψz, hψres, huniq⟩ :=
    M.rootedTreeSeries_unit_analytic_neighborhood hM hz hz1
  refine ⟨ψ, hψa, hψz, hψres, huniq, ?_⟩
  let I : Set ℂ := {w : ℂ | ‖w‖ < 1}
  let D : Set ℂ := {w : ℂ | ‖w‖ ≤ 1}
  have hID : I ⊆ D := by
    intro w hw
    change ‖w‖ ≤ 1
    exact hw.le
  have hzD : z ∈ D := by
    change ‖z‖ ≤ 1
    exact hz.le
  have hwlim : Filter.Tendsto (fun w : ℂ => w)
      (nhdsWithin z I) (nhds z) := tendsto_id.mono_left inf_le_left
  have hTlim : Filter.Tendsto M.rootedTreeSeries
      (nhdsWithin z I) (nhds (M.rootedTreeSeries z)) :=
    ((M.rootedTreeSeries_continuousOn_closedDisk hM z hzD).mono hID)
  have hpair : Filter.Tendsto
      (fun w : ℂ => ((w, (0 : C(S, ℂ))), M.rootedTreeSeries w))
      (nhdsWithin z I)
      (nhds (((z, (0 : C(S, ℂ))), M.rootedTreeSeries z))) :=
    (hwlim.prodMk_nhds tendsto_const_nhds).prodMk_nhds hTlim
  filter_upwards [hpair.eventually huniq, self_mem_nhdsWithin] with w hwuniq hwI
  change ψ (w, 0) = M.rootedTreeSeries w
  apply hwuniq.mp
  exact M.rootedTreeSeries_residual_zero_openDisk hM hwI

end PerronWright
