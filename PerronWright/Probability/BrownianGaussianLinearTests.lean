import PerronWright.Probability.BrownianGaussianSkeleton
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Distributions.Gaussian.CharFun

/-!
# Exact characteristic tests of the actual rational Gaussian process

All finite real linear combinations of literal sampled coordinates have
the proved mean-zero and Brownian quadratic variance. Consequently their
characteristic integrals are an explicit finite minimum-kernel sum. This
is the source computation for the real-time continuous realization.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianGaussianLinearTests

open BrownianGaussianSkeleton

variable {ι : Type*} [Fintype ι]

def linearTest (q : ι → RationalTime) (c : ι → ℝ) (x : ℕ → ℝ) : ℝ :=
  ∑ i, c i * rationalProcess (q i) x

def quadraticVariance (q : ι → RationalTime) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * min ((q i).val : ℝ) ((q j).val : ℝ)

theorem hasGaussianLaw_linearTest (q : ι → RationalTime) (c : ι → ℝ) :
    HasGaussianLaw (linearTest q c) rationalLaw := by
  change HasGaussianLaw (fun x ↦ ∑ i, c i * rationalProcess (q i) x) rationalLaw
  simpa only [Function.comp_def,smul_eq_mul] using
    ((rational_isGaussianProcess.comp_right q).smul c).hasGaussianLaw_fun_sum (I := Finset.univ)

omit [Fintype ι] in theorem integrable_coordinate_mul (q : ι → RationalTime) (c : ι → ℝ) (i : ι) :
    Integrable (fun x ↦ c i * rationalProcess (q i) x) rationalLaw :=
  (rational_hasLaw_eval (q i)).hasGaussianLaw.integrable.const_mul (c i)

omit [Fintype ι] in theorem memLp_two_coordinate_mul (q : ι → RationalTime) (c : ι → ℝ) (i : ι) :
    MemLp (fun x ↦ c i * rationalProcess (q i) x) 2 rationalLaw :=
  (rational_hasLaw_eval (q i)).hasGaussianLaw.memLp_two.const_mul (c i)

theorem integral_linearTest (q : ι → RationalTime) (c : ι → ℝ) :
    (∫ x, linearTest q c x ∂rationalLaw) = 0 := by
  change (∫ x, ∑ i, c i * rationalProcess (q i) x ∂rationalLaw) = 0
  rw [integral_finsetSum _ (fun i _ ↦ integrable_coordinate_mul q c i)]
  simp only [integral_const_mul,rational_integral_eval,mul_zero,Finset.sum_const_zero]

theorem variance_linearTest (q : ι → RationalTime) (c : ι → ℝ) :
    Var[linearTest q c;rationalLaw] = quadraticVariance q c := by
  change Var[fun x ↦ ∑ i, c i * rationalProcess (q i) x;rationalLaw] = quadraticVariance q c
  rw [variance_fun_sum (memLp_two_coordinate_mul q c)]
  simp only [covariance_const_mul_left,covariance_const_mul_right,rational_covariance_eval,quadraticVariance]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticVariance_nonneg (q : ι → RationalTime) (c : ι → ℝ) :
    0 ≤ quadraticVariance q c := by
  rw [← variance_linearTest]
  exact variance_nonneg _ _

/-- Exact finite linear characteristic integral under the actually
constructed infinite rational probability law. -/
theorem integral_exp_linearTest (q : ι → RationalTime) (c : ι → ℝ) :
    (∫ x, Complex.exp ((linearTest q c x : ℂ) * Complex.I) ∂rationalLaw) =
      Complex.exp (-((quadraticVariance q c : ℝ) : ℂ) / 2) := by
  have hh := (hasGaussianLaw_linearTest q c).charFunDual_map_eq_fun
    (ContinuousLinearMap.id ℝ ℝ)
  have hm : AEMeasurable (linearTest q c) rationalLaw :=
    (hasGaussianLaw_linearTest q c).aemeasurable
  rw [charFunDual_apply,integral_map hm (by fun_prop)] at hh
  simpa only [ContinuousLinearMap.id_apply,integral_linearTest,variance_linearTest,
    Complex.ofReal_zero,zero_mul,zero_sub,neg_div] using hh

end PerronWright.BrownianGaussianLinearTests
