import PerronWright.Model.CompactBJR

/-!
# The paper's projective quadratic regularity assumption

The assumption `(QP)` is the existence of a symmetric feature expansion
whose supremum-norm majorants are summable.  The convergence of the actual
kernel series, and its pointwise expansion, are proved below; neither is
stored as an independent hypothesis.
-/

open scoped BigOperators

noncomputable section

namespace PerronWright.ProjectiveKernel

variable {S : Type*} [MetricSpace S]

/-- The symmetric feature kernel `f(x) f(y)`. -/
def square (f : C(S, ℝ)) : C(S × S, ℝ) :=
  ⟨fun p ↦ f p.1 * f p.2,
    (f.continuous.comp continuous_fst).mul (f.continuous.comp continuous_snd)⟩

@[simp] theorem square_apply (f : C(S, ℝ)) (x y : S) :
    square f (x, y) = f x * f y := rfl

theorem square_symmetric (f : C(S, ℝ)) (x y : S) :
    square f (x, y) = square f (y, x) := mul_comm _ _

variable [CompactSpace S]

theorem norm_square_le (f : C(S, ℝ)) : ‖square f‖ ≤ ‖f‖ ^ 2 := by
  apply (ContinuousMap.norm_le _ (sq_nonneg ‖f‖)).mpr
  intro p
  change ‖f p.1 * f p.2‖ ≤ ‖f‖ ^ 2
  rw [norm_mul, pow_two]
  exact mul_le_mul (f.norm_coe_le_norm p.1) (f.norm_coe_le_norm p.2)
    (norm_nonneg _) (norm_nonneg _)

theorem norm_term_le (a : ℝ) (f : C(S, ℝ)) :
    ‖a • square f‖ ≤ |a| * ‖f‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_square_le f) (abs_nonneg a)

/-- The defining absolutely summable symmetric feature expansion. -/
def HasRepresentation (h : C(S × S, ℝ)) : Prop :=
  ∃ (a : ℕ → ℝ) (f : ℕ → C(S, ℝ)),
    Summable (fun j ↦ |a j| * ‖f j‖ ^ 2) ∧
      h = ∑' j, (a j) • square (f j)

/-- Supremum-norm summability of the actual continuous-kernel series. -/
theorem summable_terms {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (h : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) :
    Summable (fun j ↦ (a j) • square (f j)) :=
  h.of_norm_bounded (fun j ↦ norm_term_le (a j) (f j))

/-- The kernel equality holds at every pair of types. -/
theorem hasSum_at {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (h : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) (x y : S) :
    HasSum (fun j ↦ a j * f j x * f j y)
      ((∑' j, (a j) • square (f j)) (x, y)) := by
  have he := (ContinuousMap.evalCLM ℝ (x, y)).hasSum (summable_terms h).hasSum
  simpa only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply,
    square_apply, smul_eq_mul, mul_assoc] using he

/-- Partial sums converge in the supremum norm, hence uniformly. -/
theorem tendsto_partialSums {a : ℕ → ℝ} {f : ℕ → C(S, ℝ)}
    (h : Summable (fun j ↦ |a j| * ‖f j‖ ^ 2)) :
    Filter.Tendsto (fun N ↦ ∑ j ∈ Finset.range N, (a j) • square (f j))
      Filter.atTop (nhds (∑' j, (a j) • square (f j))) :=
  (summable_terms h).hasSum.tendsto_sum_nat

end PerronWright.ProjectiveKernel

namespace PerronWright.CompactBJRModel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Exactly assumption `(QP)` from the probabilistic theorem. -/
def QP (M : CompactBJRModel S) : Prop :=
  ProjectiveKernel.HasRepresentation M.kernel.toContinuousMap

end PerronWright.CompactBJRModel
