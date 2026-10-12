import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Genuine measurable Poisson count kernels

The rate-dependent Poisson measures and their finite independent products
are constructed as actual Markov kernels. Their exact count probabilities
and independent marginal laws are proved. This is not yet a spatial
Poisson point process or an excursion-area identification theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

noncomputable section

namespace PerronWright.PoissonCountKernel

theorem measurable_poissonMeasure : Measurable poissonMeasure := by
  apply Measure.measurable_measure.mpr
  intro s hs
  simp only [poissonMeasure, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
  apply Measurable.tsum
  intro n
  have h : Measurable (fun r : ℝ≥0 ↦
      ENNReal.ofReal (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ))) := by
    fun_prop
  exact h.mul_const _

/-- The actual Poisson law as a measurable, normalized rate kernel. -/
def countKernel : Kernel ℝ≥0 ℕ := ⟨poissonMeasure, measurable_poissonMeasure⟩

instance : IsMarkovKernel countKernel :=
  ⟨fun r ↦ inferInstanceAs (IsProbabilityMeasure (poissonMeasure r))⟩

theorem countKernel_singleton (r : ℝ≥0) (n : ℕ) :
    countKernel r {n} = ENNReal.ofReal
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / (n.factorial : ℝ)) :=
  poissonMeasure_singleton r n

variable {ι : Type*} [Fintype ι]

/-- The genuine joint count measure at finitely many nonnegative rates. -/
def finiteCountLaw (r : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi (fun i ↦ poissonMeasure (r i))

instance (r : ι → ℝ≥0) : IsProbabilityMeasure (finiteCountLaw r) := by
  unfold finiteCountLaw
  infer_instance

theorem finiteCountLaw_singleton (r : ι → ℝ≥0) (n : ι → ℕ) :
    finiteCountLaw r {n} = ∏ i, ENNReal.ofReal
      (Real.exp (-(r i : ℝ)) * (r i : ℝ) ^ n i / ((n i).factorial : ℝ)) := by
  simp only [finiteCountLaw, Measure.pi_singleton, poissonMeasure_singleton]

theorem measurable_finiteCountLaw : Measurable (finiteCountLaw (ι := ι)) := by
  apply Measure.measurable_measure.mpr
  intro s hs
  have he (r : ι → ℝ≥0) : finiteCountLaw r s =
      ∑' n : ι → ℕ, finiteCountLaw r {n} * Measure.dirac n s := by
    calc
      _ = (Measure.sum (fun n ↦ finiteCountLaw r {n} • Measure.dirac n)) s :=
        congrArg (fun μ : Measure (ι → ℕ) ↦ μ s)
          (Measure.sum_smul_dirac (finiteCountLaw r)).symm
      _ = _ := by rw [Measure.sum_apply _ hs]; simp only [Measure.smul_apply, smul_eq_mul]
  simp only [he, finiteCountLaw_singleton]
  apply Measurable.tsum
  intro n
  apply Measurable.mul_const
  apply Finset.measurable_prod
  intro i _
  fun_prop

/-- A literal finite independent Poisson-count Markov kernel. -/
def finiteCountKernel : Kernel (ι → ℝ≥0) (ι → ℕ) :=
  ⟨finiteCountLaw, measurable_finiteCountLaw⟩

instance : IsMarkovKernel (finiteCountKernel (ι := ι)) :=
  ⟨fun r ↦ inferInstanceAs (IsProbabilityMeasure (finiteCountLaw r))⟩

theorem finiteCountLaw_hasLaw_eval (r : ι → ℝ≥0) (i : ι) :
    HasLaw (fun n : ι → ℕ ↦ n i) (poissonMeasure (r i)) (finiteCountLaw r) :=
  (measurePreserving_eval (fun j ↦ poissonMeasure (r j)) i).hasLaw

theorem finiteCountLaw_independent (r : ι → ℝ≥0) :
    iIndepFun (fun i (n : ι → ℕ) ↦ n i) (finiteCountLaw r) := by
  simpa only [finiteCountLaw, Function.id_def] using
    (iIndepFun_pi (μ := fun i ↦ poissonMeasure (r i))
      (X := fun _ (n : ℕ) ↦ n) (fun _ ↦ measurable_id.aemeasurable))

end PerronWright.PoissonCountKernel
