import PerronWright.Enumeration.ZeroFieldUnicyclicSingularity
import PerronWright.Transfer.LogarithmicCoefficient
import PerronWright.Analysis.NormalizedFoldActivity

/-!
# The zero-field unicyclic singularity in activity coordinates

The logarithmic continuation is first constructed in the fold coordinate
`X`.  This file transports it through the canonical principal coordinate
`X(w) = sqrt (1-w)` on the Cartesian Delta-domain.  The leading term then
becomes `-(1/4) log (1-w)`, which is the form consumed by coefficient
transfer.
-/

open Filter Topology PerronWright Set
open ComplexOrder
open scoped Topology

noncomputable section

namespace PerronWright.ZeroFieldUnicyclicActivitySingularity

namespace ZF

export PerronWright.ZeroFieldUnicyclicSingularity
  (zeroFieldUnicyclicEGF exists_zeroFieldUnicyclic_singularity_data)

end ZF

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The principal square root selected on the Cartesian Delta-domain remains
in the principal slit plane. -/
theorem cartesianDeltaSqrt_mem_slitPlane
    {η m : ℝ} (hm : 0 ≤ m) {w : ℂ}
    (hw : w ∈ Transfer.cartesianDelta η m) :
    Transfer.cartesianDeltaSqrt w ∈ Complex.slitPlane := by
  have hne := Transfer.cartesianDeltaSqrt_ne_zero hm hw
  have hre : 0 ≤ (Transfer.cartesianDeltaSqrt w).re := by
    rw [Transfer.cartesianDeltaSqrt, Complex.sqrt,
      Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (Transfer.cartesianDeltaSqrt w).im = 0
  · left
    have hre0 : (Transfer.cartesianDeltaSqrt w).re ≠ 0 := by
      intro hzero
      apply hne
      exact Complex.ext hzero him
    exact lt_of_le_of_ne hre hre0.symm
  · exact Or.inr him

/-- The norm of the selected fold coordinate is the square root of the
distance to the critical activity. -/
theorem norm_cartesianDeltaSqrt (w : ℂ) :
    ‖Transfer.cartesianDeltaSqrt w‖ = Real.sqrt ‖1 - w‖ := by
  have hsquare := Transfer.cartesianDeltaSqrt_sq w
  have hnormSquare : ‖Transfer.cartesianDeltaSqrt w‖ ^ 2 = ‖1 - w‖ := by
    rw [← norm_pow, hsquare]
  have hrealSquare : (Real.sqrt ‖1 - w‖) ^ 2 = ‖1 - w‖ :=
    Real.sq_sqrt (norm_nonneg _)
  nlinarith [norm_nonneg (Transfer.cartesianDeltaSqrt w),
    Real.sqrt_nonneg ‖1 - w‖]

/-- Equivalent half-power form of the preceding norm identity. -/
theorem norm_cartesianDeltaSqrt_eq_rpow (w : ℂ) :
    ‖Transfer.cartesianDeltaSqrt w‖ = ‖1 - w‖ ^ (1 / 2 : ℝ) := by
  rw [norm_cartesianDeltaSqrt, Real.sqrt_eq_rpow]

/-- The zero-field unicyclic continuation in normalized activity coordinates.
The analytic error remains `O(X(w))`; its norm is therefore of square-root
order by `norm_cartesianDeltaSqrt_eq_rpow`. -/
theorem exists_zeroFieldUnicyclic_activity_singularity_data
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (H₁ : ℂ) (E F : ℂ → ℂ) (r : ℝ),
      0 < r ∧
      IsOpen (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r) ∧
      AnalyticOnNhd ℂ E
        (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r) ∧
      AnalyticOnNhd ℂ F
        (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r) ∧
      (∀ w ∈ TreeNormalizedFoldActivity.localCartesianDelta 1 0 r,
        F w = -(1 / 4 : ℂ) * Complex.log (1 - w) + E w + H₁) ∧
      (fun w : ℂ => E w) =O[𝓝 (1 : ℂ)]
        (fun w : ℂ => Transfer.cartesianDeltaSqrt w) ∧
      ∀ X : ℝ, 0 < X → X < r →
        ZF.zeroFieldUnicyclicEGF M (((1 - X ^ 2 : ℝ) : ℂ)) =
          F (((1 - X ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨H₁, R, G, rG, hrG, hRanalytic, -, hRO, hGformula,
      -, hGanalytic, -, hphysical⟩ :=
    ZF.exists_zeroFieldUnicyclic_singularity_data M hM
  obtain ⟨rR, hrR, hRball⟩ :=
    Metric.eventually_nhds_iff.mp hRanalytic.eventually_analyticAt
  let r : ℝ := min rG rR
  have hr : 0 < r := lt_min hrG hrR
  let E : ℂ → ℂ := fun w => R (Transfer.cartesianDeltaSqrt w)
  let F : ℂ → ℂ := fun w => G (Transfer.cartesianDeltaSqrt w)
  have hEanalytic : AnalyticOnNhd ℂ E
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r) := by
    intro w hw
    have hXanalytic : AnalyticAt ℂ Transfer.cartesianDeltaSqrt w :=
      Transfer.analyticOnNhd_cartesianDeltaSqrt (m := (0 : ℝ))
        (by norm_num) w hw.1
    have hXball : Transfer.cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) rR :=
      Metric.ball_subset_ball (min_le_right rG rR) hw.2
    exact (hRball hXball).comp_of_eq hXanalytic rfl
  have hFanalytic : AnalyticOnNhd ℂ F
      (TreeNormalizedFoldActivity.localCartesianDelta 1 0 r) := by
    intro w hw
    have hXanalytic : AnalyticAt ℂ Transfer.cartesianDeltaSqrt w :=
      Transfer.analyticOnNhd_cartesianDeltaSqrt (m := (0 : ℝ))
        (by norm_num) w hw.1
    have hXball : Transfer.cartesianDeltaSqrt w ∈ Metric.ball (0 : ℂ) rG :=
      Metric.ball_subset_ball (min_le_left rG rR) hw.2
    have hXslit : Transfer.cartesianDeltaSqrt w ∈ Complex.slitPlane :=
      cartesianDeltaSqrt_mem_slitPlane (m := (0 : ℝ)) (by norm_num) hw.1
    exact (hGanalytic _ ⟨hXslit, hXball⟩).comp_of_eq hXanalytic rfl
  have hformula : ∀ w ∈
      TreeNormalizedFoldActivity.localCartesianDelta 1 0 r,
      F w = -(1 / 4 : ℂ) * Complex.log (1 - w) + E w + H₁ := by
    intro w hw
    have hne : 1 - w ≠ 0 := Complex.slitPlane_ne_zero
      (Transfer.one_sub_mem_slitPlane_of_mem_cartesianDelta
        (m := (0 : ℝ)) (by norm_num) hw.1)
    dsimp only [F, E]
    rw [hGformula, Transfer.cartesianDeltaSqrt,
      Transfer.log_sqrt_eq_half_log hne]
    ring
  have hXcontinuous : Tendsto Transfer.cartesianDeltaSqrt
      (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hinner : Tendsto (fun w : ℂ => 1 - w)
        (𝓝 (1 : ℂ)) (𝓝 (0 : ℂ)) := by
      have hcont : ContinuousAt (fun w : ℂ => 1 - w) 1 :=
        continuousAt_const.sub continuousAt_id
      simpa using hcont.tendsto
    have hsqrt : Tendsto Complex.sqrt (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa using
        (Complex.continuousAt_sqrt (z := (0 : ℂ))
          (Or.inl (by norm_num))).tendsto
    exact hsqrt.comp hinner
  have hEO : (fun w : ℂ => E w) =O[𝓝 (1 : ℂ)]
      (fun w : ℂ => Transfer.cartesianDeltaSqrt w) := by
    simpa only [E, Function.comp_def] using hRO.comp_tendsto hXcontinuous
  have hphysical' : ∀ X : ℝ, 0 < X → X < r →
      ZF.zeroFieldUnicyclicEGF M (((1 - X ^ 2 : ℝ) : ℂ)) =
        F (((1 - X ^ 2 : ℝ) : ℂ)) := by
    intro X hX hXr
    have hXrG : X < rG := hXr.trans_le (min_le_left rG rR)
    have hnonneg : 0 ≤ ((X ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast sq_nonneg X
    have hsqrt0 := Complex.sqrt_of_nonneg hnonneg
    have hsqrtReal : Real.sqrt (X ^ 2) = X := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hX]
    have hsqrt : Transfer.cartesianDeltaSqrt
        (((1 - X ^ 2 : ℝ) : ℂ)) = (X : ℂ) := by
      rw [Transfer.cartesianDeltaSqrt]
      have hone : (1 : ℂ) - ((1 - X ^ 2 : ℝ) : ℂ) =
          ((X ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hone]
      simpa only [Complex.ofReal_re, hsqrtReal] using hsqrt0
    dsimp only [F]
    rw [hsqrt]
    exact hphysical X hX hXrG
  refine ⟨H₁, E, F, r, hr,
    TreeNormalizedFoldActivity.isOpen_localCartesianDelta (by norm_num),
    hEanalytic, hFanalytic, hformula, hEO, hphysical'⟩

end PerronWright.ZeroFieldUnicyclicActivitySingularity
