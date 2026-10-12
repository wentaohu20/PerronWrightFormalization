import PerronWright.Transfer.CartesianOuterArcGeometry
import PerronWright.Transfer.BanachContourBounds

/-!
# A fixed parametrization of the Cartesian outer arc

The intrinsic major circle arc from `CartesianOuterArcGeometry` is
parametrized by one real angular interval.  Its endpoints are exactly the
two truncated keyhole rays, its range remains in the Cartesian Δ-domain,
and its Banach-valued coefficient integral is exponentially small.
-/

open Complex ComplexConjugate MeasureTheory Set
noncomputable section

namespace PerronWright.Transfer

/-- Principal argument of the upper truncated-ray endpoint. -/
def cartesianOuterAngle (M : ℝ) : ℝ :=
  Complex.arg ((1 : ℂ) + (M : ℂ) * cartesianUpperDir)

theorem cartesianOuterAngle_nonneg {M : ℝ} (hM : 0 < M) :
    0 ≤ cartesianOuterAngle M := by
  rw [cartesianOuterAngle, Complex.arg_nonneg_iff]
  simp [cartesianUpperDir]
  positivity

theorem cartesianOuterAngle_le_pi (M : ℝ) :
    cartesianOuterAngle M ≤ Real.pi :=
  Complex.arg_le_pi _

theorem cartesianOuterAngle_interval_nonempty (M : ℝ) :
    cartesianOuterAngle M ≤ 2 * Real.pi - cartesianOuterAngle M := by
  linarith [cartesianOuterAngle_le_pi M]

theorem cartesianOuterCircleMap_at_angle (M : ℝ) :
    circleMap 0 (cartesianOuterRadius M) (cartesianOuterAngle M) =
      (1 : ℂ) + (M : ℂ) * cartesianUpperDir := by
  simpa only [circleMap_zero, cartesianOuterRadius, cartesianOuterAngle] using
    Complex.norm_mul_exp_arg_mul_I
      ((1 : ℂ) + (M : ℂ) * cartesianUpperDir)

theorem cartesianOuterCircleMap_at_two_pi_sub_angle (M : ℝ) :
    circleMap 0 (cartesianOuterRadius M)
        (2 * Real.pi - cartesianOuterAngle M) =
      (1 : ℂ) + (M : ℂ) * cartesianLowerDir := by
  let R := cartesianOuterRadius M
  let theta := cartesianOuterAngle M
  let u : ℂ := (1 : ℂ) + (M : ℂ) * cartesianUpperDir
  have hu : circleMap 0 R theta = u :=
    cartesianOuterCircleMap_at_angle M
  have hconj : conj u =
      (1 : ℂ) + (M : ℂ) * cartesianLowerDir := by
    dsimp [u]
    apply Complex.ext
    · simp [cartesianUpperDir, cartesianLowerDir]
    · simp [cartesianUpperDir, cartesianLowerDir]
  calc
    circleMap 0 R (2 * Real.pi - theta) =
        circleMap 0 R (-theta + 2 * Real.pi) := by congr 2; ring
    _ = circleMap 0 R (-theta) := periodic_circleMap 0 R (-theta)
    _ = conj (circleMap 0 R theta) :=
      (conj_circleMap_zero R theta).symm
    _ = conj u := congrArg conj hu
    _ = (1 : ℂ) + (M : ℂ) * cartesianLowerDir := hconj

/-- Every point of the standard angular parametrization between the two
endpoint angles lies on the intrinsic major arc. -/
theorem cartesianOuterCircleMap_mem_majorArc
    {M theta : ℝ} (hM : 0 < M)
    (htheta : theta ∈ Icc (cartesianOuterAngle M)
      (2 * Real.pi - cartesianOuterAngle M)) :
    circleMap 0 (cartesianOuterRadius M) theta ∈
      cartesianOuterMajorArc M := by
  let R := cartesianOuterRadius M
  let theta0 := cartesianOuterAngle M
  have hR0 : 0 ≤ R := norm_nonneg _
  have hRpos : 0 < R := lt_trans zero_lt_one (cartesianOuterRadius_gt_one hM)
  have htheta0 : 0 ≤ theta0 := cartesianOuterAngle_nonneg hM
  have hcos : Real.cos theta ≤ Real.cos theta0 := by
    by_cases hthetaPi : theta ≤ Real.pi
    · exact Real.cos_le_cos_of_nonneg_of_le_pi htheta0 hthetaPi htheta.1
    · have hpiTheta : Real.pi ≤ theta := le_of_not_ge hthetaPi
      have hleft : theta0 ≤ 2 * Real.pi - theta := by
        linarith [htheta.2]
      have hright : 2 * Real.pi - theta ≤ Real.pi := by
        linarith
      have h := Real.cos_le_cos_of_nonneg_of_le_pi htheta0 hright hleft
      simpa only [Real.cos_two_pi_sub] using h
  constructor
  · rw [norm_circleMap_zero,
      abs_of_pos (lt_trans zero_lt_one (cartesianOuterRadius_gt_one hM))]
  · calc
      (circleMap 0 R theta).re = R * Real.cos theta :=
        circleMap_zero_re R theta
      _ ≤ R * Real.cos theta0 := mul_le_mul_of_nonneg_left hcos hR0
      _ = (circleMap 0 R theta0).re :=
        (circleMap_zero_re R theta0).symm
      _ = ((1 : ℂ) + (M : ℂ) * cartesianUpperDir).re := by
        rw [cartesianOuterCircleMap_at_angle]
      _ = 1 + 3 * M / 5 := by
        simp [cartesianUpperDir]
        ring

theorem cartesianOuterCircleMap_range_subset_majorArc {M : ℝ}
    (hM : 0 < M) :
    circleMap 0 (cartesianOuterRadius M) ''
        Icc (cartesianOuterAngle M)
          (2 * Real.pi - cartesianOuterAngle M) ⊆
      cartesianOuterMajorArc M := by
  rintro z ⟨theta, htheta, rfl⟩
  exact cartesianOuterCircleMap_mem_majorArc hM htheta

/-- The chosen parametrization is globally continuously differentiable;
in particular it is piecewise `C¹` on the major-arc interval. -/
theorem cartesianOuterCircleMap_contDiff (M : ℝ) :
    ContDiff ℝ 1 (circleMap 0 (cartesianOuterRadius M)) :=
  contDiff_circleMap 0 (cartesianOuterRadius M)

theorem cartesianOuterCircleMap_constant_norm {M theta : ℝ}
    (hM : 0 < M) :
    ‖circleMap 0 (cartesianOuterRadius M) theta‖ =
      cartesianOuterRadius M := by
  simp only [norm_circleMap_zero,
    abs_of_pos (lt_trans zero_lt_one (cartesianOuterRadius_gt_one hM))]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The major outer arc with the orientation needed to close the local
keyhole: from the lower endpoint back to the upper endpoint. -/
def banachCartesianFixedOuterArcIntegral
    (F : ℂ → E) (M : ℝ) (n : ℕ) : E :=
  -(∫ theta in cartesianOuterAngle M..
      (2 * Real.pi - cartesianOuterAngle M),
    (deriv (circleMap 0 (cartesianOuterRadius M)) theta *
      ((circleMap 0 (cartesianOuterRadius M) theta)⁻¹ ^ (n + 1))) •
        F (circleMap 0 (cartesianOuterRadius M) theta))

theorem banachCartesianFixedOuterArcIntegral_bound
    {F : ℂ → E} {M B : ℝ} {n : ℕ}
    (hM : 0 < M) (hB : 0 ≤ B)
    (hF : ∀ z ∈ cartesianOuterMajorArc M, ‖F z‖ ≤ B) :
    ‖banachCartesianFixedOuterArcIntegral F M n‖ ≤
      ((2 * Real.pi - cartesianOuterAngle M) - cartesianOuterAngle M) *
        (cartesianOuterRadius M * B *
          Real.exp (-((n : ℝ) * (Real.log (cartesianOuterRadius M) / 2)))) := by
  rw [banachCartesianFixedOuterArcIntegral, norm_neg]
  apply banach_outer_arc_bound (cartesianOuterRadius_gt_one hM) hB
    (cartesianOuterAngle_interval_nonempty M)
  intro theta htheta
  exact hF _ (cartesianOuterCircleMap_mem_majorArc hM htheta)

theorem banachCartesianFixedOuterArcIntegral_isLittleO
    {F : ℂ → E} {M B : ℝ}
    (hM : 0 < M) (hB : 0 ≤ B)
    (hF : ∀ z ∈ cartesianOuterMajorArc M, ‖F z‖ ≤ B)
    (a : ℝ) :
    (fun n : ℕ => banachCartesianFixedOuterArcIntegral F M n)
      =o[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ a) := by
  have h := banach_outer_arc_integral_isLittleO
    (cartesianOuterRadius_gt_one hM) hB
    (cartesianOuterAngle_interval_nonempty M)
    (fun theta htheta =>
      hF _ (cartesianOuterCircleMap_mem_majorArc hM htheta)) a
  simpa only [banachCartesianFixedOuterArcIntegral] using h.neg_left

end PerronWright.Transfer
