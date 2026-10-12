import PerronWright.Transfer.CoefficientCauchy
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Exact coefficients of the logarithmic singularity

The unicyclic layer produces `-(1/2) log X` in the fold coordinate
`X = sqrt (1 - z)`.  This file identifies that germ with
`-(1/4) log (1 - z)` and records its exact Taylor coefficients.  No
Delta-domain remainder estimate is used here.
-/

open Filter Topology
open scoped Topology

noncomputable section

namespace PerronWright.Transfer

/-- The scalar coefficients of `-log (1-z)`, with the constant coefficient
set to zero by the field convention `0⁻¹ = 0`. -/
def logarithmicCoefficient (n : ℕ) : ℂ := (n : ℂ)⁻¹

/-- The formal multilinear series of `-log (1-z)` at the origin. -/
def logarithmicPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ logarithmicCoefficient

/-- The formal multilinear series of the pure unicyclic fold singularity. -/
def unicyclicLogPowerSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (fun n => (1 / 4 : ℂ) * logarithmicCoefficient n)

@[simp]
theorem logarithmicPowerSeries_coeff (n : ℕ) :
    logarithmicPowerSeries.coeff n = logarithmicCoefficient n :=
  FormalMultilinearSeries.coeff_ofScalars

@[simp]
theorem unicyclicLogPowerSeries_coeff (n : ℕ) :
    unicyclicLogPowerSeries.coeff n =
      (1 / 4 : ℂ) * logarithmicCoefficient n :=
  FormalMultilinearSeries.coeff_ofScalars

/-- The standard logarithmic series, packaged in the analytic API used by
the coefficient-extraction layer. -/
theorem neg_log_one_sub_hasFPowerSeriesAt :
    HasFPowerSeriesAt (fun z : ℂ => -Complex.log (1 - z))
      logarithmicPowerSeries 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
  have hnorm : ‖z‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  simpa only [zero_add, logarithmicPowerSeries_coeff,
    logarithmicCoefficient, smul_eq_mul, div_eq_mul_inv] using
    (Complex.hasSum_taylorSeries_neg_log hnorm)

/-- Exact Taylor coefficient of `-log (1-z)`. -/
theorem taylorCoefficient_neg_log_one_sub (n : ℕ) :
    taylorCoefficient (fun z : ℂ => -Complex.log (1 - z)) n =
      logarithmicCoefficient n :=
  taylorCoefficient_eq_seriesCoefficient
    neg_log_one_sub_hasFPowerSeriesAt n

/-- For every nonzero input, the principal logarithm of the principal
square root is half the principal logarithm. -/
theorem log_sqrt_eq_half_log {z : ℂ} (hz : z ≠ 0) :
    Complex.log (Complex.sqrt z) = Complex.log z / 2 := by
  rw [sqrt_eq_exp hz]
  apply Complex.log_exp
  · have h := Complex.neg_pi_lt_log_im z
    have hpi := Real.pi_pos
    simp only [Complex.div_ofNat_im]
    linarith
  · have h := Complex.log_im_le_pi z
    have hpi := Real.pi_pos
    simp only [Complex.div_ofNat_im]
    linarith

/-- On a neighborhood of the origin, the generic square-root logarithm
identity applies to `1-z`. -/
theorem log_sqrt_one_sub_eventually :
    (fun z : ℂ => Complex.log (Complex.sqrt (1 - z))) =ᶠ[𝓝 0]
      (fun z : ℂ => Complex.log (1 - z) / 2) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
  have hnorm : ‖z‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  apply log_sqrt_eq_half_log
  intro h
  have hz1 : z = 1 := (sub_eq_zero.mp h).symm
  subst z
  norm_num at hnorm

/-- The fold-coordinate logarithmic singularity is exactly one quarter of
the standard logarithmic singularity as a germ at the origin. -/
theorem neg_half_log_sqrt_one_sub_eventually :
    (fun z : ℂ => -(1 / 2 : ℂ) *
        Complex.log (Complex.sqrt (1 - z))) =ᶠ[𝓝 0]
      (fun z : ℂ => (1 / 4 : ℂ) * (-Complex.log (1 - z))) := by
  filter_upwards [log_sqrt_one_sub_eventually] with z hz
  rw [hz]
  ring

/-- The pure unicyclic fold singularity has the explicitly scaled
logarithmic power series. -/
theorem neg_half_log_sqrt_one_sub_hasFPowerSeriesAt :
    HasFPowerSeriesAt
        (fun z : ℂ => -(1 / 2 : ℂ) *
          Complex.log (Complex.sqrt (1 - z)))
      unicyclicLogPowerSeries 0 := by
  rw [hasFPowerSeriesAt_iff]
  have hbase := hasFPowerSeriesAt_iff.mp
    neg_log_one_sub_hasFPowerSeriesAt
  filter_upwards [hbase, neg_half_log_sqrt_one_sub_eventually]
    with z hz hidentity
  simp only [zero_add]
  rw [hidentity]
  have hscaled := hz.const_smul (1 / 4 : ℂ)
  simpa only [zero_add, unicyclicLogPowerSeries_coeff,
    logarithmicPowerSeries_coeff, smul_eq_mul, mul_assoc,
    mul_left_comm] using hscaled

/-- Exact Taylor coefficient of the pure unicyclic fold singularity. -/
theorem taylorCoefficient_neg_half_log_sqrt_one_sub (n : ℕ) :
    taylorCoefficient
        (fun z : ℂ => -(1 / 2 : ℂ) *
          Complex.log (Complex.sqrt (1 - z))) n =
      (1 / 4 : ℂ) * logarithmicCoefficient n := by
  exact taylorCoefficient_eq_seriesCoefficient
    neg_half_log_sqrt_one_sub_hasFPowerSeriesAt n

end PerronWright.Transfer
