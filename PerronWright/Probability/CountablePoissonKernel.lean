import PerronWright.Probability.PoissonFactorialMoments
import PerronWright.Probability.PoissonMixedCountLaw
import Mathlib.Probability.Independence.InfinitePi

/-!
# Genuine countable independent Poisson marking kernels

The law is the actual infinite product of the literal Poisson measures.
Measurability in all rates is proved from its finite measurable cylinders.
The resulting Markov kernel constructs a joint source/count probability
law and gives its exact finite count probabilities. This supplies countable
Poisson marks once actual measurable excursion areas are available; it does
not assume their enumeration or the Aldous density identity.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal ENNReal

noncomputable section

namespace PerronWright.CountablePoissonKernel

/-- The genuine law of all countably many independent Poisson marks. -/
def countLaw (r : ℕ → ℝ≥0) : Measure (ℕ → ℕ) :=
  Measure.infinitePi (fun i ↦ poissonMeasure (r i))

instance (r : ℕ → ℝ≥0) : IsProbabilityMeasure (countLaw r) := by
  unfold countLaw
  infer_instance

theorem countLaw_map_restrict (r : ℕ → ℝ≥0) (I : Finset ℕ) :
    (countLaw r).map I.restrict = PoissonCountKernel.finiteCountLaw (fun i : I ↦ r i) :=
  Measure.infinitePi_map_restrict _

theorem countLaw_cylinder (r : ℕ → ℝ≥0) (I : Finset ℕ)
    (s : Set (I → ℕ)) (hs : MeasurableSet s) :
    countLaw r (cylinder I s) = PoissonCountKernel.finiteCountLaw (fun i : I ↦ r i) s :=
  Measure.infinitePi_cylinder _ hs

/-- Rate measurability is a proved cylinder argument, not a kernel input. -/
theorem measurable_countLaw : Measurable countLaw := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  intro s hs
  obtain ⟨I, t, ht, rfl⟩ := (mem_measurableCylinders s).mp hs
  simp only [countLaw_cylinder _ I t ht]
  exact (Measure.measurable_coe ht).comp
    (PoissonCountKernel.measurable_finiteCountLaw.comp
      (measurable_pi_lambda _ (fun i : I ↦ measurable_pi_apply i.val)))

def countKernel : Kernel (ℕ → ℝ≥0) (ℕ → ℕ) := ⟨countLaw,measurable_countLaw⟩

instance : IsMarkovKernel countKernel :=
  ⟨fun r ↦ inferInstanceAs (IsProbabilityMeasure (countLaw r))⟩

theorem countLaw_hasLaw_eval (r : ℕ → ℝ≥0) (i : ℕ) :
    HasLaw (fun n : ℕ → ℕ ↦ n i) (poissonMeasure (r i)) (countLaw r) :=
  (measurePreserving_eval_infinitePi (fun j ↦ poissonMeasure (r j)) i).hasLaw

theorem countLaw_independent (r : ℕ → ℝ≥0) :
    iIndepFun (fun i (n : ℕ → ℕ) ↦ n i) (countLaw r) := by
  exact iIndepFun_infinitePi (X := fun _ (n : ℕ) ↦ n) (fun _ ↦ measurable_id)

theorem countLaw_cylinder_singleton (r : ℕ → ℝ≥0) (I : Finset ℕ) (n : I → ℕ) :
    countLaw r (cylinder I {n}) = ∏ i : I, ENNReal.ofReal
      (Real.exp (-(r i : ℝ)) * (r i : ℝ) ^ n i / ((n i).factorial : ℝ)) := by
  rw [countLaw_cylinder _ _ _ (measurableSet_singleton n),
    PoissonCountKernel.finiteCountLaw_singleton]

variable {Ω : Type*} [MeasurableSpace Ω]

def rateKernel (A : Ω → ℕ → ℝ≥0) (hA : Measurable A) : Kernel Ω (ℕ → ℕ) :=
  ⟨fun x ↦ countLaw (A x),measurable_countLaw.comp hA⟩

instance (A : Ω → ℕ → ℝ≥0) (hA : Measurable A) : IsMarkovKernel (rateKernel A hA) :=
  ⟨fun x ↦ inferInstanceAs (IsProbabilityMeasure (countLaw (A x)))⟩

/-- A constructed joint probability law for the source and all marks. -/
def jointLaw (μ : Measure Ω) (A : Ω → ℕ → ℝ≥0) (hA : Measurable A) :
    Measure (Ω × (ℕ → ℕ)) := μ ⊗ₘ rateKernel A hA

instance (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ℕ → ℝ≥0) (hA : Measurable A) : IsProbabilityMeasure (jointLaw μ A hA) := by
  unfold jointLaw
  infer_instance

theorem jointLaw_source (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ℕ → ℝ≥0) (hA : Measurable A) :
    (jointLaw μ A hA).map Prod.fst = μ := Measure.fst_compProd μ (rateKernel A hA)

/-- Exact conditional finite-count events under the genuine countable law. -/
theorem jointLaw_source_finite_count_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ℕ → ℝ≥0) (hA : Measurable A)
    (s : Set Ω) (hs : MeasurableSet s) (I : Finset ℕ) (n : I → ℕ) :
    jointLaw μ A hA (s ×ˢ cylinder (α := fun _ : ℕ ↦ ℕ) I {n}) = ∫⁻ x in s, ∏ i : I, ENNReal.ofReal
      (Real.exp (-(A x i : ℝ)) * (A x i : ℝ) ^ n i / ((n i).factorial : ℝ)) ∂μ := by
  have hc : MeasurableSet (cylinder (α := fun _ : ℕ ↦ ℕ) I {n}) :=
    (measurableSet_singleton n).preimage
      (show Measurable (fun m : ℕ → ℕ ↦ fun i : I ↦ m i) from
        measurable_pi_lambda _ (fun i : I ↦ measurable_pi_apply i.val))
  rw [jointLaw,Measure.compProd_apply_prod hs hc]
  simp only [rateKernel,Kernel.coe_mk,countLaw_cylinder_singleton]

end PerronWright.CountablePoissonKernel
