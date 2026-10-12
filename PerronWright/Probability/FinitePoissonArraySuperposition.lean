import PerronWright.Probability.FinitePoissonSuperposition
import PerronWright.Probability.CountableProductTranspose
import PerronWright.Probability.PoissonCountKernel

/-!
# Exact vector-valued superposition of independent Poisson arrays

The actual row-product law is transposed into a column-product law, then
the genuine scalar Poisson convolution theorem is applied to each column.
The resulting vector law is exactly the independent summed-rate product.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.FinitePoissonArraySuperposition

variable {D : Type*} [Fintype D]

def matrixLaw (r : ℕ → D → ℝ≥0) : Measure (ℕ → D → ℕ) :=
  Measure.infinitePi (fun j ↦ PoissonCountKernel.finiteCountLaw (r j))

instance (r : ℕ → D → ℝ≥0) : IsProbabilityMeasure (matrixLaw r) := by
  unfold matrixLaw
  infer_instance

theorem matrixLaw_map_transpose (r : ℕ → D → ℝ≥0) :
    (matrixLaw r).map (fun x : ℕ → D → ℕ ↦ fun i j ↦ x j i) =
      Measure.infinitePi (fun i : D ↦ Measure.infinitePi (fun j ↦ poissonMeasure (r j i))) := by
  simpa only [matrixLaw,PoissonCountKernel.finiteCountLaw,Measure.infinitePi_eq_pi] using
    CountableProductTranspose.infinitePi_map_transpose (fun j i ↦ poissonMeasure (r j i))

theorem matrixLaw_columns_independent (r : ℕ → D → ℝ≥0) :
    iIndepFun (fun i (x : ℕ → D → ℕ) ↦ fun j ↦ x j i) (matrixLaw r) := by
  simpa only [matrixLaw,PoissonCountKernel.finiteCountLaw,Measure.infinitePi_eq_pi] using
    CountableProductTranspose.columns_independent (fun j i ↦ poissonMeasure (r j i))

theorem matrixLaw_hasLaw_column (r : ℕ → D → ℝ≥0) (i : D) :
    HasLaw (fun x : ℕ → D → ℕ ↦ fun j ↦ x j i)
      (Measure.infinitePi (fun j ↦ poissonMeasure (r j i))) (matrixLaw r) := by
  have hm : Measurable (fun x : ℕ → D → ℕ ↦ fun i j ↦ x j i) := by fun_prop
  have ht : HasLaw (fun x : ℕ → D → ℕ ↦ fun i j ↦ x j i)
      (Measure.infinitePi (fun i : D ↦ Measure.infinitePi (fun j ↦ poissonMeasure (r j i))))
      (matrixLaw r) := ⟨hm.aemeasurable,matrixLaw_map_transpose r⟩
  exact (measurePreserving_eval_infinitePi
    (fun i : D ↦ Measure.infinitePi (fun j ↦ poissonMeasure (r j i))) i).hasLaw.fun_comp ht

def sumArray (N : ℕ) (x : ℕ → D → ℕ) (i : D) : ℕ := ∑ j ∈ Finset.range N, x j i

omit [Fintype D] in
theorem measurable_sumArray (N : ℕ) : Measurable (sumArray (D := D) N) := by
  apply measurable_pi_lambda
  intro i
  exact Finset.measurable_fun_sum (Finset.range N)
    (fun j _ ↦ (measurable_pi_apply i).comp (measurable_pi_apply j))

theorem sumArray_hasLaw_eval (r : ℕ → D → ℝ≥0) (N : ℕ) (i : D) :
    HasLaw (fun x : ℕ → D → ℕ ↦ sumArray N x i)
      (poissonMeasure (∑ j ∈ Finset.range N, r j i)) (matrixLaw r) :=
  (FinitePoissonSuperposition.infinitePi_hasLaw_finset_sum (fun j ↦ r j i) (Finset.range N)).fun_comp
    (matrixLaw_hasLaw_column r i)

theorem sumArray_independent (r : ℕ → D → ℝ≥0) (N : ℕ) :
    iIndepFun (fun i (x : ℕ → D → ℕ) ↦ sumArray N x i) (matrixLaw r) := by
  exact (matrixLaw_columns_independent r).comp
    (fun _ (x : ℕ → ℕ) ↦ ∑ j ∈ Finset.range N, x j)
    (fun _ ↦ Finset.measurable_fun_sum (Finset.range N) (fun j _ ↦ measurable_pi_apply j))

/-- Literal pushforward equality for the independent summed-rate vector. -/
theorem matrixLaw_map_sumArray (r : ℕ → D → ℝ≥0) (N : ℕ) :
    (matrixLaw r).map (sumArray N) =
      PoissonCountKernel.finiteCountLaw (fun i ↦ ∑ j ∈ Finset.range N, r j i) := by
  have hm : ∀ i : D, AEMeasurable (fun x : ℕ → D → ℕ ↦ sumArray N x i) (matrixLaw r) :=
    fun i ↦ ((measurable_pi_apply i).comp (measurable_sumArray N)).aemeasurable
  change (matrixLaw r).map (fun x i ↦ sumArray N x i) = _
  rw [(sumArray_independent r N).map_fun_eq_pi_map hm]
  congr 1
  funext i
  exact (sumArray_hasLaw_eval r N i).map_eq

end PerronWright.FinitePoissonArraySuperposition
