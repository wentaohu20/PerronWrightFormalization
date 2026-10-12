import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Moments.IntegrableExpMul

/-! # Exponential integrability from a literal quadratic tail

Layercake and a Gaussian integral prove this reduction. The tail
identity will be discharged for the actual bridge minimum using the
proved finite-horizon survival formula, not added as a model assumption.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal
noncomputable section

namespace PerronWright.GaussianQuadraticTailIntegrability

theorem integrable_exp_linear_sub_quadratic (c : ℝ) (hc : 0 < c) (u : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (u*x-c*x^2)) volume := by
  have hi := (integrable_exp_neg_mul_sq (by positivity : 0 < c/2)).const_mul
    (Real.exp (u^2/(2*c)))
  apply hi.mono' (by fun_prop)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : u^2/(2*c)-(c/2)*x^2-(u*x-c*x^2) = (u-c*x)^2/(2*c) := by
    field_simp
    ring
  have hn := div_nonneg (sq_nonneg (u-c*x)) (by positivity : 0 ≤ 2*c)
  rw [← he] at hn
  linarith

theorem integral_exp_derivative (u b : ℝ) :
    (∫ t in (0 : ℝ)..b, u*Real.exp (u*t)) = Real.exp (u*b)-1 := by
  have hderiv (t : ℝ) : HasDerivAt (fun x : ℝ ↦ Real.exp (u*x))
      (u*Real.exp (u*t)) t := by
    simpa only [id_eq,mul_comm,mul_one] using ((hasDerivAt_id t).const_mul u).exp
  simpa only [mul_zero,Real.exp_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
      ((by fun_prop : Continuous (fun t : ℝ ↦ u*Real.exp (u*t))).intervalIntegrable 0 b)

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integrable_exp_mul_of_quadratic_tail (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hXnonneg : ∀ ω, 0 ≤ X ω)
    (c : ℝ) (hc : 0 < c)
    (htail : ∀ t : ℝ, 0 < t → μ {ω | t ≤ X ω} = ENNReal.ofReal (Real.exp (-c*t^2)))
    (u : ℝ) : Integrable (fun ω ↦ Real.exp (u*X ω)) μ := by
  by_cases hu : u ≤ 0
  · apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hu (hXnonneg ω))
  · have hu : 0 < u := lt_of_not_ge hu
    have hcake := lintegral_comp_eq_lintegral_meas_le_mul μ
      (Eventually.of_forall hXnonneg) hX.aemeasurable
      (fun t _ ↦ ((by fun_prop : Continuous (fun s : ℝ ↦ u*Real.exp (u*s))).intervalIntegrable 0 t))
      (Eventually.of_forall (fun t ↦ mul_nonneg hu.le (Real.exp_pos _).le))
    have he : (∫⁻ ω, ENNReal.ofReal (Real.exp (u*X ω)-1) ∂μ) =
        ∫⁻ t in Ioi 0, ENNReal.ofReal (u*Real.exp (u*t-c*t^2)) := by
      simpa only [integral_exp_derivative] using hcake |>.trans (by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change μ {ω | t ≤ X ω} * ENNReal.ofReal (u*Real.exp (u*t)) = _
        rw [htail t ht,← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        calc
          Real.exp (-c*t^2)*(u*Real.exp (u*t)) =
              u*(Real.exp (u*t)*Real.exp (-c*t^2)) := by ring
          _ = u*Real.exp (u*t+(-c*t^2)) := by rw [← Real.exp_add]
          _ = u*Real.exp (u*t-c*t^2) := by rw [sub_eq_add_neg,neg_mul])
    have hr := ((integrable_exp_linear_sub_quadratic c hc u).const_mul u).integrableOn
      (s := Ioi (0 : ℝ))
    have hfin : (∫⁻ ω, ENNReal.ofReal (Real.exp (u*X ω)-1) ∂μ) ≠ ⊤ :=
      he ▸ hr.lintegral_lt_top.ne
    have hnn : ∀ ω, 0 ≤ Real.exp (u*X ω)-1 := by
      intro ω
      exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hu.le (hXnonneg ω)))
    have hi := (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Eventually.of_forall hnn)).mp hfin
    have hsum := hi.add (integrable_const (1 : ℝ))
    change Integrable (fun ω ↦ (Real.exp (u*X ω)-1)+1) μ at hsum
    simpa only [sub_add_cancel] using hsum

end PerronWright.GaussianQuadraticTailIntegrability
