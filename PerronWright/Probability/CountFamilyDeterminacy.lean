import PerronWright.Probability.FactorialWindowCountDeterminacy
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Finite mixed factorial moments determine the whole count family

Joint count inversion is combined with the proved uniqueness theorem for
projective limits.  Thus the complete law of the count family, not only its
individual coordinates, is recovered.  Encoding restricted point measures
by counts on a generating algebra and their weak topology is separate work.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.CountFamilyDeterminacy

open FactorialCountDeterminacy FactorialGeneratingSeries

variable {T : Type*}

/-- The actual joint law of the counts at a finite set of coordinates. -/
def finiteLaw (μ : Measure (T → ℕ)) (I : Finset T) : Measure (I → ℕ) :=
  μ.map I.restrict

instance finiteLaw_isFinite (μ : Measure (T → ℕ)) [IsFiniteMeasure μ] (I : Finset T) :
    IsFiniteMeasure (finiteLaw μ I) := by
  unfold finiteLaw
  infer_instance

/-- Equality of all finite mixed factorial moments determines the law of
the whole count family under genuine exponential integrability. -/
theorem measure_eq_of_finite_factorialMoments
    (μ ν : Measure (T → ℕ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμexp : ∀ I : Finset T,
      Integrable (fun n ↦ (3 : ℝ) ^ totalCount n) (finiteLaw μ I))
    (hνexp : ∀ I : Finset T,
      Integrable (fun n ↦ (3 : ℝ) ^ totalCount n) (finiteLaw ν I))
    (hmom : ∀ (I : Finset T) (q : I → ℕ),
      factorialMoment (finiteLaw μ I) q = factorialMoment (finiteLaw ν I) q) : μ = ν := by
  have hfinite (I : Finset T) : finiteLaw μ I = finiteLaw ν I :=
    measure_eq_of_factorialMoments_of_total_exp (finiteLaw μ I) (finiteLaw ν I)
      (hμexp I) (hνexp I) (hmom I)
  have hμ : IsProjectiveLimit μ (fun I : Finset T ↦ finiteLaw μ I) := fun _ ↦ rfl
  have hν : IsProjectiveLimit ν (fun I : Finset T ↦ finiteLaw μ I) := by
    intro I
    exact (hfinite I).symm
  exact hμ.unique hν

end PerronWright.CountFamilyDeterminacy
