import PerronWright.Probability.BrownianContinuousModification
import PerronWright.Probability.BrownianGaussianLinearTests

/-!
# Real-time characteristic tests of the constructed continuous process

The finite rational characteristic identity passes to actual continuous
sample limits by bounded dominated convergence. The limiting Brownian
minimum-kernel quadratic form is computed from literal dyadic floors,
not supplied as a covariance or convergence hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianContinuousLinearTests

open BrownianGaussianSkeleton BrownianDyadicGrid BrownianContinuousModification
open BrownianGaussianLinearTests

def timeApprox (n : ℕ) (t : ℝ≥0) : RationalTime :=
  dyadicTime n (DyadicFloorGeometry.index n t)

theorem timeApprox_distance_bound (n : ℕ) (t : ℝ≥0) :
    |((timeApprox n t).val : ℝ) - (t : ℝ)| ≤ 1 / (2 : ℝ) ^ n := by
  have hd : 0 < (2 : ℝ) ^ n := by positivity
  have h0 := DyadicFloorGeometry.index_le_scaled n t
  have h1 := DyadicFloorGeometry.scaled_lt_index_add_one n t
  rw [timeApprox,dyadicTime_real,abs_sub_comm]
  have hnn : 0 ≤ (t : ℝ) - (DyadicFloorGeometry.index n t : ℝ) / (2 : ℝ) ^ n :=
    sub_nonneg.mpr ((div_le_iff₀ hd).mpr h0)
  rw [abs_of_nonneg hnn]
  apply le_of_lt
  rw [sub_lt_iff_lt_add,← add_div,lt_div_iff₀ hd]
  simpa only [add_comm] using h1

theorem timeApprox_tendsto_real (t : ℝ≥0) :
    Tendsto (fun n ↦ ((timeApprox n t).val : ℝ)) atTop (𝓝 (t : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb (n : ℕ) : ‖((timeApprox n t).val : ℝ) - (t : ℝ)‖ ≤ 1 / (2 : ℝ) ^ n := by
    simpa only [Real.norm_eq_abs] using timeApprox_distance_bound n t
  have hh : Tendsto (fun n : ℕ ↦ 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1))
  exact squeeze_zero (fun _ ↦ norm_nonneg _) hb hh

variable {ι : Type*} [Fintype ι]

def realLinearTest (t : ι → ℝ≥0) (c : ι → ℝ) (x : ℕ → ℝ) : ℝ :=
  ∑ i, c i * process (t i) x

def realQuadraticVariance (t : ι → ℝ≥0) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * min (t i).val (t j).val

theorem quadraticVariance_timeApprox_tendsto (t : ι → ℝ≥0) (c : ι → ℝ) :
    Tendsto (fun n ↦ quadraticVariance (fun i ↦ timeApprox n (t i)) c)
      atTop (𝓝 (realQuadraticVariance t c)) := by
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact ((timeApprox_tendsto_real (t i)).min (timeApprox_tendsto_real (t j))).const_mul (c i * c j)

theorem ae_linearTest_timeApprox_tendsto (t : ι → ℝ≥0) (c : ι → ℝ) :
    ∀ᵐ x ∂rationalLaw, Tendsto (fun n ↦ linearTest (fun i ↦ timeApprox n (t i)) c x)
      atTop (𝓝 (realLinearTest t c x)) := by
  have hh : ∀ᵐ x ∂rationalLaw, ∀ i : ι,
      Tendsto (fun n ↦ rationalProcess (timeApprox n (t i)) x) atTop (𝓝 (process (t i) x)) :=
    ae_all_iff.mpr (fun i ↦ ae_samples_tendsto_process (t i))
  filter_upwards [hh] with x hx
  exact tendsto_finsetSum _ (fun i _ ↦ (hx i).const_mul (c i))

/-- Genuine characteristic integrals of the actual constructed continuous
process at arbitrary finitely many nonnegative real times. -/
theorem integral_exp_realLinearTest (t : ι → ℝ≥0) (c : ι → ℝ) :
    (∫ x, Complex.exp ((realLinearTest t c x : ℂ) * Complex.I) ∂rationalLaw) =
      Complex.exp (-((realQuadraticVariance t c : ℝ) : ℂ) / 2) := by
  have hchar : Continuous (fun u : ℝ ↦ Complex.exp ((u : ℂ) * Complex.I)) := by fun_prop
  have hlim : Tendsto
      (fun n ↦ ∫ x, Complex.exp ((linearTest (fun i ↦ timeApprox n (t i)) c x : ℂ) * Complex.I) ∂rationalLaw)
      atTop (𝓝 (∫ x, Complex.exp ((realLinearTest t c x : ℂ) * Complex.I) ∂rationalLaw)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
    · intro n
      exact (hchar.measurable.comp_aemeasurable
        (hasGaussianLaw_linearTest (fun i ↦ timeApprox n (t i)) c).aemeasurable).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall (fun x ↦ by simp [Complex.norm_exp])
    · filter_upwards [ae_linearTest_timeApprox_tendsto t c] with x hx
      exact (hchar.tendsto (realLinearTest t c x)).comp hx
  have hformula : Tendsto
      (fun n ↦ ∫ x, Complex.exp ((linearTest (fun i ↦ timeApprox n (t i)) c x : ℂ) * Complex.I) ∂rationalLaw)
      atTop (𝓝 (Complex.exp (-((realQuadraticVariance t c : ℝ) : ℂ) / 2))) := by
    simp only [integral_exp_linearTest]
    have hc : Continuous (fun u : ℝ ↦ Complex.exp (-(u : ℂ) / 2)) := by fun_prop
    exact (hc.tendsto (realQuadraticVariance t c)).comp (quadraticVariance_timeApprox_tendsto t c)
  exact tendsto_nhds_unique hlim hformula

end PerronWright.BrownianContinuousLinearTests
