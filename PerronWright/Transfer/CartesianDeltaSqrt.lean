import PerronWright.Transfer.DeltaDiscGeometry
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The canonical square-root coordinate on the Cartesian Delta-domain

The Cartesian dent removes a closed right-pointing cone based at `1`.
Consequently `1 - w` never lies on the nonpositive real axis, so mathlib's
principal complex square root gives a canonical analytic coordinate on the
whole Cartesian Delta-domain without an additional branch assumption.

This module concerns the normalized activity coordinate `w` only.  It does
not yet compose the coordinate with the field-dependent critical activity,
construct the corresponding joint tree profile, or prove an overlap with the
unit-away continuation.
-/

noncomputable section

namespace PerronWright.Transfer

/-- Membership in a Cartesian Delta-domain forces the translated coordinate
`1 - w` into mathlib's principal slit plane. -/
theorem one_sub_mem_slitPlane_of_mem_cartesianDelta
    {η m : ℝ} (hm : 0 ≤ m) {w : ℂ} (hw : w ∈ cartesianDelta η m) :
    1 - w ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (1 - w).im = 0
  · left
    have hwim : (w - 1).im = 0 := by
      simp only [Complex.sub_im, Complex.one_im, zero_sub] at him
      simp only [Complex.sub_im, Complex.one_im, sub_zero]
      exact neg_eq_zero.mp him
    by_contra hre
    have hnonpos : (1 - w).re ≤ 0 := not_lt.mp hre
    have hwre : 0 ≤ (w - 1).re := by
      simp only [Complex.sub_re, Complex.one_re] at hnonpos ⊢
      linarith
    apply hw.2
    refine ⟨hwre, ?_⟩
    rw [hwim, abs_zero]
    exact mul_nonneg hm hwre
  · exact Or.inr him

/-- The selected square-root coordinate on the dented plane. -/
def cartesianDeltaSqrt (w : ℂ) : ℂ :=
  Complex.sqrt (1 - w)

/-- The selected coordinate has the required square everywhere; this is the
existing principal complex power identity, not a postulated branch law. -/
@[simp] theorem cartesianDeltaSqrt_sq (w : ℂ) :
    cartesianDeltaSqrt w ^ 2 = 1 - w := by
  unfold cartesianDeltaSqrt Complex.sqrt
  exact Complex.cpow_nat_inv_pow (1 - w) (by norm_num : (2 : ℕ) ≠ 0)

/-- The selected coordinate is nonzero throughout a Cartesian Delta-domain. -/
theorem cartesianDeltaSqrt_ne_zero
    {η m : ℝ} (hm : 0 ≤ m) {w : ℂ} (hw : w ∈ cartesianDelta η m) :
    cartesianDeltaSqrt w ≠ 0 := by
  intro hzero
  have hsquare := cartesianDeltaSqrt_sq w
  rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsquare
  exact Complex.slitPlane_ne_zero
    (one_sub_mem_slitPlane_of_mem_cartesianDelta hm hw) hsquare.symm

/-- The principal square-root coordinate is complex differentiable throughout
the Cartesian Delta-domain. -/
theorem differentiableOn_cartesianDeltaSqrt
    {η m : ℝ} (hm : 0 ≤ m) :
    DifferentiableOn ℂ cartesianDeltaSqrt (cartesianDelta η m) := by
  intro w hw
  have hinner : DifferentiableAt ℂ (fun z : ℂ => 1 - z) w :=
    DifferentiableAt.sub (differentiableAt_const _) differentiableAt_id
  exact ((Complex.differentiableAt_sqrt
    (one_sub_mem_slitPlane_of_mem_cartesianDelta hm hw)).comp
      w hinner).differentiableWithinAt

/-- Equivalently, the selected coordinate is analytic on a neighborhood of
every point of the Cartesian Delta-domain. -/
theorem analyticOnNhd_cartesianDeltaSqrt
    {η m : ℝ} (hm : 0 ≤ m) :
    AnalyticOnNhd ℂ cartesianDeltaSqrt (cartesianDelta η m) :=
  (differentiableOn_cartesianDeltaSqrt hm).analyticOnNhd
    (isOpen_cartesianDelta η m)

end PerronWright.Transfer

