import PerronWright.Kernel.FiniteIrreduciblePositiveCritical
import PerronWright.Analysis.FiniteIrreducibleComplex
import PerronWright.Analysis.TreeRealComplexBridge

/-!
# The actual finite model obtained by a positive profile tilt

The law is `μ τ / c` and the symmetric kernel is `c κ`, where `c = ∑ μ τ`.
Thus its actual mean operator is exactly `K ∘ M_τ`. Irreducibility and
literal spectral criticality are proved, not inserted into an adapter.
-/

open scoped BigOperators
noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem irreducible_pos_smul (M : FiniteIrreducibleModel S) {c : ℝ} (hc : 0 < c) :
    (c • M.kernel).IsIrreducible := by
  have hn (a b : S) : 0 ≤ (c • M.kernel) a b :=
    mul_nonneg hc.le (M.kernel_nonneg a b)
  apply (Matrix.isIrreducible_iff_exists_pow_pos hn).mpr
  intro a b
  obtain ⟨k, hk, hkab⟩ :=
    (Matrix.isIrreducible_iff_exists_pow_pos M.irreducible.nonneg).mp M.irreducible a b
  refine ⟨k, hk, ?_⟩
  rw [smul_pow]
  exact mul_pos (pow_pos hc k) hkab

def tilted (M : FiniteIrreducibleModel S) (τ : S → ℝ) (hτ : ∀ a, 0 < τ a) :
    FiniteIrreducibleModel S where
  weight a := M.weight a * τ a / M.average τ
  weight_pos a := div_pos (mul_pos (M.weight_pos a) (hτ a)) (M.average_pos τ hτ)
  weight_sum := by
    rw [← Finset.sum_div]
    exact div_self (M.average_pos τ hτ).ne'
  kernel := M.average τ • M.kernel
  symmetric a b := by
    change M.average τ * M.kernel a b = M.average τ * M.kernel b a
    rw [M.symmetric a b]
  irreducible := M.irreducible_pos_smul (M.average_pos τ hτ)

@[simp] theorem tilted_weight (M : FiniteIrreducibleModel S)
    (τ : S → ℝ) (hτ : ∀ a, 0 < τ a) (a : S) :
    (M.tilted τ hτ).weight a = M.weight a * τ a / M.average τ := rfl

@[simp] theorem tilted_kernel (M : FiniteIrreducibleModel S)
    (τ : S → ℝ) (hτ : ∀ a, 0 < τ a) (a b : S) :
    (M.tilted τ hτ).kernel a b = M.average τ * M.kernel a b := rfl

theorem tilted_meanMatrix_apply (M : FiniteIrreducibleModel S)
    (τ : S → ℝ) (hτ : ∀ a, 0 < τ a) (a b : S) :
    (M.tilted τ hτ).meanMatrix a b = M.kernel a b * M.weight b * τ b := by
  rw [meanMatrix_apply, tilted_weight, tilted_kernel]
  field_simp [(M.average_pos τ hτ).ne']

theorem tilted_action (M : FiniteIrreducibleModel S)
    (τ : S → ℝ) (hτ : ∀ a, 0 < τ a) (f : S → ℝ) :
    (M.tilted τ hτ).action f = M.action (τ * f) := by
  rw [action_eq_meanMatrix_mulVec]
  funext a
  simp only [Matrix.mulVec, dotProduct, tilted_meanMatrix_apply, action, Pi.mul_apply]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tilted_isCritical_of_positive_fixed (M : FiniteIrreducibleModel S)
    (τ : S → ℝ) (hτ : ∀ a, 0 < τ a) (u : S → ℝ) (hu : ∀ a, 0 < u a)
    (hfix : M.action (τ * u) = u) : (M.tilted τ hτ).IsCritical := by
  apply (M.tilted τ hτ).isCritical_of_positive_fixed_function u hu
  rw [M.tilted_action, hfix]

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem tilted_complexOperator (M : FiniteIrreducibleModel S)
    (τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) (f : C(S, ℂ)) :
    (M.tilted τ hτ).complexOperator f =
      M.complexOperator (TreeRealComplexBridge.complexify τ * f) := by
  ext a
  rw [complexOperator_apply, complexOperator_apply]
  apply Finset.sum_congr rfl
  intro b _
  rw [← meanMatrix_apply, tilted_meanMatrix_apply]
  simp only [ContinuousMap.mul_apply, TreeRealComplexBridge.complexify_apply]
  push_cast
  ring

end PerronWright.FiniteIrreducibleModel
