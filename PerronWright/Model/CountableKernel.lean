import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.Normed.Group.Real

/-!
# Literal data for a bounded countable kernel

The type space is `ℕ` with its usual measurable structure.  No compactness,
continuous extension, integral operator, or Perron eigenvector is a field.
The probability measure has a positive atom at every type.
-/

open MeasureTheory

noncomputable section

namespace PerronWright

structure CountableKernel where
  mu : Measure ℕ
  probability : IsProbabilityMeasure mu
  atom_pos : ∀ a : ℕ, 0 < mu {a}
  kernel : ℕ → ℕ → ℝ
  symmetric : ∀ a b, kernel a b = kernel b a
  nonneg : ∀ a b, 0 ≤ kernel a b
  upper : ℝ
  upper_nonneg : 0 ≤ upper
  le_upper : ∀ a b, kernel a b ≤ upper

namespace CountableKernel

instance (M : CountableKernel) : IsProbabilityMeasure M.mu := M.probability

theorem norm_kernel_le (M : CountableKernel) (a b : ℕ) : ‖M.kernel a b‖ ≤ M.upper := by
  rw [Real.norm_of_nonneg (M.nonneg a b)]
  exact M.le_upper a b

theorem atomMass_pos (M : CountableKernel) (a : ℕ) : 0 < M.mu.real {a} := by
  exact ENNReal.toReal_pos (M.atom_pos a).ne' (measure_ne_top M.mu {a})

theorem atomMass_hasSum (M : CountableKernel) : HasSum (fun a : ℕ ↦ M.mu.real {a}) 1 := by
  have hsum : (∑' a : ℕ, M.mu {a}) = 1 := by
    have h := congrArg (fun nu : Measure ℕ ↦ nu Set.univ) M.mu.sum_smul_dirac
    simpa only [Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
      measure_univ, smul_eq_mul, mul_one] using h
  have hs := ENNReal.hasSum_toReal (f := fun a : ℕ ↦ M.mu {a})
    (by rw [hsum]; simp)
  have hreal : (∑' a : ℕ, (M.mu {a}).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun a ↦ measure_ne_top M.mu {a}), hsum]
    simp
  simpa [measureReal_def, hreal] using hs

end CountableKernel
end PerronWright
