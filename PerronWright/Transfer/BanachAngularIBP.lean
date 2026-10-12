import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Vector-valued angular integration by parts.  This is an alternative
route toward a uniform Δ-transfer theorem: it converts analyticity
and local derivative bounds into decay of actual circle coefficients,
without assuming a keyhole contour deformation.
-/

open Complex MeasureTheory intervalIntegral Set AddCircle
open scoped Interval
noncomputable section

namespace PerronWright.Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [CompleteSpace E] [IsScalarTower ℝ ℂ E]

/-- Integration by parts for a complex Banach-valued function against
the actual angular Fourier mode on an interval. -/
theorem banach_fourier_interval_ibp
    {a b : ℝ} (hab : a < b) {f f' : ℝ → E} (n : ℤ)
    (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    (∫ x in a..b,
      (-2 * Real.pi * I * n / (b - a) *
        fourier (-n) (x : AddCircle (b - a))) • f x +
      fourier (-n) (x : AddCircle (b - a)) • f' x) =
      fourier (-n) (b : AddCircle (b - a)) • f b -
        fourier (-n) (a : AddCircle (b - a)) • f a := by
  have hT : Fact (0 < b - a) := ⟨sub_pos.mpr hab⟩
  have hmode : Continuous
      (fun x : ℝ => fourier (-n) (x : AddCircle (b - a))) :=
    (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)
  apply intervalIntegral.integral_deriv_smul_eq_sub_of_hasDeriv_right
    (u' := fun x => -2 * Real.pi * I * n / (b - a) *
      fourier (-n) (x : AddCircle (b - a)))
    (v' := f') hmode.continuousOn hf
  · intro x hx
    simpa only [Complex.ofReal_sub] using
      (hasDerivAt_fourier_neg (b - a) n x).hasDerivWithinAt (s := Ioi x)
  · intro x hx
    exact (hff' x (by simpa [min_eq_left hab.le, max_eq_right hab.le] using hx)).hasDerivWithinAt
  · have hc : Continuous (fun x : ℝ =>
        -2 * Real.pi * I * n / (b - a) *
          fourier (-n) (x : AddCircle (b - a))) := by
      fun_prop
    exact hc.intervalIntegrable a b
  · exact hf'

/-- For a periodic Banach-valued function, one angular integration by
parts transfers a nonzero Fourier mode to its derivative exactly. -/
theorem banach_fourier_periodic_integral_relation
    {a b : ℝ} (hab : a < b) {f f' : ℝ → E} (n : ℤ)
    (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b)
    (hper : f a = f b) :
    (-2 * Real.pi * I * n / (b - a)) •
      (∫ x in a..b,
        fourier (-n) (x : AddCircle (b - a)) • f x) =
      -(∫ x in a..b,
        fourier (-n) (x : AddCircle (b - a)) • f' x) := by
  have hT : Fact (0 < b - a) := ⟨sub_pos.mpr hab⟩
  have hmode : Continuous
      (fun x : ℝ => fourier (-n) (x : AddCircle (b - a))) :=
    (map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _)
  have hmode' : Continuous (fun x : ℝ =>
      -2 * Real.pi * I * n / (b - a) *
        fourier (-n) (x : AddCircle (b - a))) := by
    fun_prop
  have hi₁ : IntervalIntegrable
      (fun x : ℝ =>
        (-2 * Real.pi * I * n / (b - a) *
          fourier (-n) (x : AddCircle (b - a))) • f x)
      volume a b :=
    (hmode'.continuousOn.smul hf).intervalIntegrable
  have hi₂ : IntervalIntegrable
      (fun x : ℝ =>
        fourier (-n) (x : AddCircle (b - a)) • f' x)
      volume a b :=
    hf'.continuousOn_smul hmode.continuousOn
  have h := banach_fourier_interval_ibp hab n hf hff' hf'
  rw [intervalIntegral.integral_add hi₁ hi₂] at h
  simp only [mul_smul, intervalIntegral.integral_smul] at h
  have hmode_end : (b : AddCircle (b - a)) =
      (a : AddCircle (b - a)) := by
    simpa using coe_add_period (b - a) a
  rw [hmode_end, ← hper] at h
  simp only [sub_self] at h
  calc
    (-2 * Real.pi * I * n / (b - a)) •
        (∫ x in a..b,
          fourier (-n) (x : AddCircle (b - a)) • f x) =
      ((-2 * Real.pi * I * n / (b - a)) •
        (∫ x in a..b,
          fourier (-n) (x : AddCircle (b - a)) • f x)) +
        (∫ x in a..b,
          fourier (-n) (x : AddCircle (b - a)) • f' x) -
        (∫ x in a..b,
          fourier (-n) (x : AddCircle (b - a)) • f' x) := by abel
    _ = -(∫ x in a..b,
          fourier (-n) (x : AddCircle (b - a)) • f' x) := by
      rw [h]
      simp

/-- The exact vector-valued integration-by-parts relation in norm.  The
scalar factor on the left grows linearly with the nonzero Fourier index. -/
theorem banach_fourier_periodic_integral_norm
    {a b : ℝ} (hab : a < b) {f f' : ℝ → E} (n : ℤ)
    (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b)
    (hper : f a = f b) :
    ‖(-2 * Real.pi * I * n / (b - a) : ℂ)‖ *
      ‖∫ x in a..b,
        fourier (-n) (x : AddCircle (b - a)) • f x‖ =
      ‖∫ x in a..b,
        fourier (-n) (x : AddCircle (b - a)) • f' x‖ := by
  have h := banach_fourier_periodic_integral_relation
    hab n hf hff' hf' hper
  simpa only [norm_smul, norm_neg] using congrArg norm h

/-- A one-derivative bound for the actual Banach-valued angular
coefficient integral.  Iterating this estimate is the analytic core of
the Fourier-route remainder transfer. -/
theorem banach_fourier_periodic_integral_derivative_bound
    {a b : ℝ} (hab : a < b) {f f' : ℝ → E} (n : ℤ)
    (hf : ContinuousOn f [[a, b]])
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b)
    (hper : f a = f b) :
    ‖(-2 * Real.pi * I * n / (b - a) : ℂ)‖ *
      ‖∫ x in a..b,
        fourier (-n) (x : AddCircle (b - a)) • f x‖ ≤
      ∫ x in a..b, ‖f' x‖ := by
  rw [banach_fourier_periodic_integral_norm
    hab n hf hff' hf' hper]
  have hb := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) hab.le (f := fun x : ℝ =>
      fourier (-n) (x : AddCircle (b - a)) • f' x)
  simpa only [norm_smul, fourier_apply, Circle.norm_coe,
    one_mul] using hb

/-- Repeated integration by parts for a smooth periodic Banach-valued
function. Every derivative is an actual derivative of the preceding one;
no abstract Fourier-decay assumption is introduced. -/
theorem banach_fourier_periodic_iterated_norm
    {a b : ℝ} (hab : a < b) (f : ℕ → ℝ → E) (n : ℤ)
    (hcont : ∀ j, ContinuousOn (f j) [[a, b]])
    (hder : ∀ j, ∀ x ∈ Ioo a b, HasDerivAt (f j) (f (j + 1) x) x)
    (hint : ∀ j, IntervalIntegrable (f j) volume a b)
    (hper : ∀ j, f j a = f j b) (j : ℕ) :
    ‖(-2 * Real.pi * I * n / (b - a) : ℂ)‖ ^ j *
      ‖∫ x in a..b,
        fourier (-n) (x : AddCircle (b - a)) • f 0 x‖ =
      ‖∫ x in a..b,
        fourier (-n) (x : AddCircle (b - a)) • f j x‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep := banach_fourier_periodic_integral_norm
        hab (f := f j) (f' := f (j + 1)) n
        (hcont j) (hder j) (hint (j + 1)) (hper j)
      calc
        ‖(-2 * Real.pi * I * n / (b - a) : ℂ)‖ ^ (j + 1) *
            ‖∫ x in a..b,
              fourier (-n) (x : AddCircle (b - a)) • f 0 x‖ =
          ‖(-2 * Real.pi * I * n / (b - a) : ℂ)‖ *
            (‖(-2 * Real.pi * I * n / (b - a) : ℂ)‖ ^ j *
              ‖∫ x in a..b,
                fourier (-n) (x : AddCircle (b - a)) • f 0 x‖) := by
                  rw [pow_succ]
                  ring
        _ = ‖(-2 * Real.pi * I * n / (b - a) : ℂ)‖ *
            ‖∫ x in a..b,
              fourier (-n) (x : AddCircle (b - a)) • f j x‖ := by rw [ih]
        _ = ‖∫ x in a..b,
              fourier (-n) (x : AddCircle (b - a)) • f (j + 1) x‖ := hstep

/-- The norm estimate after any prescribed finite number of angular
integrations by parts. -/
theorem banach_fourier_periodic_iterated_bound
    {a b : ℝ} (hab : a < b) (f : ℕ → ℝ → E) (n : ℤ)
    (hcont : ∀ j, ContinuousOn (f j) [[a, b]])
    (hder : ∀ j, ∀ x ∈ Ioo a b, HasDerivAt (f j) (f (j + 1) x) x)
    (hint : ∀ j, IntervalIntegrable (f j) volume a b)
    (hper : ∀ j, f j a = f j b) (j : ℕ) :
    ‖(-2 * Real.pi * I * n / (b - a) : ℂ)‖ ^ j *
      ‖∫ x in a..b,
        fourier (-n) (x : AddCircle (b - a)) • f 0 x‖ ≤
      ∫ x in a..b, ‖f j x‖ := by
  rw [banach_fourier_periodic_iterated_norm
    hab f n hcont hder hint hper j]
  have hb := intervalIntegral.norm_integral_le_integral_norm
    (μ := volume) hab.le (f := fun x : ℝ =>
      fourier (-n) (x : AddCircle (b - a)) • f j x)
  simpa only [norm_smul, fourier_apply, Circle.norm_coe,
    one_mul] using hb

end PerronWright.Transfer
