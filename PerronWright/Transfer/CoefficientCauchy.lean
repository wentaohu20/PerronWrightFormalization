import PerronWright.Transfer.DeltaSideParam
import PerronWright.Transfer.Polynomial

/-! Cauchy's coefficient formula for the exact contour integrand used in the
Delta-transfer development. -/

open Complex MeasureTheory
noncomputable section

namespace PerronWright.Transfer

def taylorCoefficient (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n F 0 / (n.factorial : ℂ)

theorem taylorCoefficient_sub {F G : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) (n : ℕ) :
    taylorCoefficient (fun z => F z - G z) n =
      taylorCoefficient F n - taylorCoefficient G n := by
  simp only [taylorCoefficient, iteratedDeriv_fun_sub hF.contDiffAt hG.contDiffAt,
    sub_div]

/-- A proven local power series has precisely the Taylor coefficients used
in Cauchy's formula. -/
theorem taylorCoefficient_eq_seriesCoefficient
    {F : ℂ → ℂ} {c : ℕ → ℂ}
    (hF : HasFPowerSeriesAt F
      (FormalMultilinearSeries.ofScalars ℂ c) 0) (n : ℕ) :
    taylorCoefficient F n = c n := by
  have hcanonical := hF.analyticAt.hasFPowerSeriesAt
  have hseries := hF.eq_formalMultilinearSeries hcanonical
  have hcoeff := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hseries
  simpa only [FormalMultilinearSeries.coeff_ofScalars, taylorCoefficient] using hcoeff.symm

/-- Exact Taylor coefficient of a polynomial times a pure algebraic
singularity, including the negative half-powers used in the paper. -/
theorem taylorCoefficient_prefactor (P : Polynomial ℝ) (s : ℝ) (n : ℕ) :
    taylorCoefficient
      (fun z : ℂ => P.eval₂ (algebraMap ℝ ℂ) z * (1 - z) ^ (-(s : ℂ))) n =
      (prefactorCoefficient P s n : ℂ) :=
  taylorCoefficient_eq_seriesCoefficient
    (prefactorPowerSeries_hasFPowerSeriesAt P s) n

theorem taylorCoefficient_pure (s : ℝ) (n : ℕ) :
    taylorCoefficient (fun z : ℂ => (1 - z) ^ (-(s : ℂ))) n =
      (coefficient s n : ℂ) := by
  have h : HasFPowerSeriesAt
      (fun z : ℂ => (1 - z) ^ (-(s : ℂ))) (powerSeries s) 0 :=
    (powerSeries_neg_cpow s).hasFPowerSeriesAt
  exact taylorCoefficient_eq_seriesCoefficient h n

theorem circleIntegral_eq_taylorCoefficient
    {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (Metric.closedBall 0 R)) (n : ℕ) :
    (∮ z in C((0 : ℂ), R), F z * z⁻¹ ^ (n + 1)) =
      (2 * Real.pi * I) * taylorCoefficient F n := by
  have h := hF.circleIntegral_one_div_sub_center_pow_smul hR n
  simpa only [sub_zero, one_div, inv_pow, one_mul, smul_eq_mul, taylorCoefficient,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

theorem circleIntegral_pure_exact (s : ℝ) {R : ℝ}
    (hR : 0 < R) (hR1 : R < 1) (n : ℕ) :
    (∮ z in C((0 : ℂ), R),
      (1 - z) ^ (-(s : ℂ)) * z⁻¹ ^ (n + 1)) =
      (2 * Real.pi * I) * (coefficient s n : ℂ) := by
  have hdiff : DifferentiableOn ℂ
      (fun z : ℂ => (1 - z) ^ (-(s : ℂ)))
      (Metric.closedBall 0 R) := by
    intro z hz
    have hz1 : z ∈ Metric.eball (0 : ℂ) 1 := by
      rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
      exact Metric.closedBall_subset_ball hR1 hz
    exact ((powerSeries_neg_cpow s).analyticAt_of_mem hz1).differentiableAt.differentiableWithinAt
  rw [circleIntegral_eq_taylorCoefficient hR hdiff n, taylorCoefficient_pure]

theorem circleIntegral_prefactor_exact (P : Polynomial ℝ) (s : ℝ)
    {R : ℝ} (hR : 0 < R) (hR1 : R < 1) (n : ℕ) :
    (∮ z in C((0 : ℂ), R),
      (P.eval₂ (algebraMap ℝ ℂ) z * (1 - z) ^ (-(s : ℂ))) * z⁻¹ ^ (n + 1)) =
      (2 * Real.pi * I) * (prefactorCoefficient P s n : ℂ) := by
  have hdiff : DifferentiableOn ℂ
      (fun z : ℂ => P.eval₂ (algebraMap ℝ ℂ) z * (1 - z) ^ (-(s : ℂ)))
      (Metric.closedBall 0 R) := by
    intro z hz
    have hz1 : z ∈ Metric.eball (0 : ℂ) 1 := by
      rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
      exact Metric.closedBall_subset_ball hR1 hz
    have hp : DifferentiableAt ℂ (fun z : ℂ => P.eval₂ (algebraMap ℝ ℂ) z) z := by
      simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
      have hsum : DifferentiableAt ℂ
          (∑ i ∈ P.support,
            fun w : ℂ => (algebraMap ℝ ℂ) (P.coeff i) * w ^ i) z := by
        apply DifferentiableAt.sum
        intro i hi
        fun_prop
      convert hsum using 1
      funext w
      simp
    exact (hp.mul ((powerSeries_neg_cpow s).analyticAt_of_mem hz1).differentiableAt).differentiableWithinAt
  rw [circleIntegral_eq_taylorCoefficient hR hdiff n, taylorCoefficient_prefactor]

end PerronWright.Transfer
