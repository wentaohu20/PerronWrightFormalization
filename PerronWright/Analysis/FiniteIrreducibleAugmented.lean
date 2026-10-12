import PerronWright.Analysis.FiniteIrreducibleComplex
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# The actual finite augmented kernel inverse

The projection is built from the literal type-law Perron functional.
`I - K + P` is genuinely a unit, and its inverse solves the complement
equation with a proved norm bound.  No strict contraction is required;
the negative unit eigenvalue of a bipartite model remains admissible.
-/

open Module

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def perronProjection (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    C(S, ℂ) →L[ℂ] C(S, ℂ) :=
  (M.normalizedPerronFunctional hcrit).smulRight (M.complexPerronFunction hcrit)

omit [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem perronProjection_apply (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (f : C(S, ℂ)) :
    M.perronProjection hcrit f =
      M.normalizedPerronFunctional hcrit f • M.complexPerronFunction hcrit := rfl

omit [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem normalizedPerronFunctional_projection (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (f : C(S, ℂ)) :
    M.normalizedPerronFunctional hcrit (M.perronProjection hcrit f) =
      M.normalizedPerronFunctional hcrit f := by
  rw [M.perronProjection_apply, map_smul, M.normalizedPerronFunctional_perronFunction,
    smul_eq_mul, mul_one]

omit [MeasurableSpace S] [BorelSpace S] in
theorem perronProjection_idempotent (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    (M.perronProjection hcrit).comp (M.perronProjection hcrit) = M.perronProjection hcrit := by
  apply ContinuousLinearMap.ext
  intro f
  change M.perronProjection hcrit (M.perronProjection hcrit f) = M.perronProjection hcrit f
  rw [M.perronProjection_apply, M.normalizedPerronFunctional_projection,
    M.perronProjection_apply]

theorem kernel_sub_perronProjection_isCompact (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    IsCompactOperator (M.complexOperator - M.perronProjection hcrit) := by
  have hk : IsCompactOperator M.complexOperator :=
    M.continuousKernel.isCompactOperator_complexActionCLM M.measure
  have hp : IsCompactOperator (M.perronProjection hcrit) := by
    have h := isCompactOperator_of_locallyCompactSpace_dom (M.normalizedPerronFunctional hcrit)
    exact h.clm_comp ((ContinuousLinearMap.id ℂ ℂ).smulRight (M.complexPerronFunction hcrit))
  exact hk.sub hp

theorem kernel_sub_perronProjection_no_eigenvalue_one (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ¬ Module.End.HasEigenvalue
      (M.complexOperator - M.perronProjection hcrit).toLinearMap 1 := by
  intro hev
  obtain ⟨f, hf, hfne⟩ := hev.exists_hasEigenvector
  have heq : M.complexOperator f - M.perronProjection hcrit f = f := by
    have heq := Module.End.mem_eigenspace_iff.mp hf
    change M.complexOperator f - M.perronProjection hcrit f = (1 : ℂ) • f at heq
    simpa only [one_smul] using heq
  have hell := congrArg (M.normalizedPerronFunctional hcrit) heq
  rw [map_sub, M.normalizedPerronFunctional_action,
    M.normalizedPerronFunctional_projection, sub_self] at hell
  have hp : M.perronProjection hcrit f = 0 := by
    rw [M.perronProjection_apply, ← hell, zero_smul]
  rw [hp, sub_zero] at heq
  have hfix := M.complex_fixed_eq_perronFunctional_smul hcrit f heq
  rw [← hell, zero_smul] at hfix
  exact hfne hfix

theorem augmented_kernel_isUnit (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    IsUnit (1 - M.complexOperator + M.perronProjection hcrit) := by
  have hr := (M.kernel_sub_perronProjection_isCompact hcrit).hasEigenvalue_or_mem_resolventSet
    (by norm_num : (1 : ℂ) ≠ 0)
  have hres := hr.resolve_left (M.kernel_sub_perronProjection_no_eigenvalue_one hcrit)
  rw [spectrum.mem_resolventSet_iff] at hres
  simpa only [map_one, sub_sub_eq_add_sub, sub_add_eq_add_sub] using hres

def augmentedKernelEquiv (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    C(S, ℂ) ≃L[ℂ] C(S, ℂ) :=
  ContinuousLinearEquiv.ofUnit (M.augmented_kernel_isUnit hcrit).unit

theorem augmentedKernelEquiv_apply (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (f : C(S, ℂ)) :
    M.augmentedKernelEquiv hcrit f =
      f - M.complexOperator f + M.perronProjection hcrit f := by
  change ((M.augmented_kernel_isUnit hcrit).unit : C(S, ℂ) →L[ℂ] C(S, ℂ)) f = _
  rw [IsUnit.unit_spec]
  rfl

def augmentedKernelInverse (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    C(S, ℂ) →L[ℂ] C(S, ℂ) :=
  (M.augmentedKernelEquiv hcrit).symm.toContinuousLinearMap

theorem augmentedKernelInverse_right_inverse (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (f : C(S, ℂ)) :
    M.augmentedKernelInverse hcrit f -
        M.complexOperator (M.augmentedKernelInverse hcrit f) +
        M.perronProjection hcrit (M.augmentedKernelInverse hcrit f) = f := by
  exact (M.augmentedKernelEquiv_apply hcrit _).symm.trans
    ((M.augmentedKernelEquiv hcrit).apply_symm_apply f)

theorem normalizedPerronFunctional_inverse (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (f : C(S, ℂ)) :
    M.normalizedPerronFunctional hcrit (M.augmentedKernelInverse hcrit f) =
      M.normalizedPerronFunctional hcrit f := by
  have heq := congrArg (M.normalizedPerronFunctional hcrit)
    (M.augmentedKernelInverse_right_inverse hcrit f)
  simpa only [map_add, map_sub, M.normalizedPerronFunctional_action,
    M.normalizedPerronFunctional_projection, sub_self, zero_add] using heq

theorem augmentedKernelInverse_on_complement (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (f : C(S, ℂ))
    (hf : M.normalizedPerronFunctional hcrit f = 0) :
    M.normalizedPerronFunctional hcrit (M.augmentedKernelInverse hcrit f) = 0 ∧
      M.augmentedKernelInverse hcrit f -
        M.complexOperator (M.augmentedKernelInverse hcrit f) = f := by
  have hzero : M.normalizedPerronFunctional hcrit (M.augmentedKernelInverse hcrit f) = 0 :=
    (M.normalizedPerronFunctional_inverse hcrit f).trans hf
  refine ⟨hzero, ?_⟩
  have heq := M.augmentedKernelInverse_right_inverse hcrit f
  rwa [M.perronProjection_apply, hzero, zero_smul, add_zero] at heq

theorem complement_solution_unique (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (f g : C(S, ℂ)) (hg : M.normalizedPerronFunctional hcrit g = 0)
    (heq : g - M.complexOperator g = f) :
    g = M.augmentedKernelInverse hcrit f := by
  apply (M.augmentedKernelEquiv hcrit).injective
  rw [M.augmentedKernelEquiv_apply, M.perronProjection_apply, hg, zero_smul, add_zero, heq]
  exact ((M.augmentedKernelEquiv hcrit).apply_symm_apply f).symm

theorem complement_inverse_bounded (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : C(S, ℂ), M.normalizedPerronFunctional hcrit f = 0 →
      ∃! g : C(S, ℂ), M.normalizedPerronFunctional hcrit g = 0 ∧
        g - M.complexOperator g = f ∧ ‖g‖ ≤ C * ‖f‖ := by
  refine ⟨‖M.augmentedKernelInverse hcrit‖ + 1, by positivity, ?_⟩
  intro f hf
  refine ⟨M.augmentedKernelInverse hcrit f, ?_, ?_⟩
  · obtain ⟨hzero, heq⟩ := M.augmentedKernelInverse_on_complement hcrit f hf
    refine ⟨hzero, heq, ?_⟩
    calc
      ‖M.augmentedKernelInverse hcrit f‖ ≤ ‖M.augmentedKernelInverse hcrit‖ * ‖f‖ :=
        (M.augmentedKernelInverse hcrit).le_opNorm f
      _ ≤ (‖M.augmentedKernelInverse hcrit‖ + 1) * ‖f‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg f)
  · intro g hg
    exact M.complement_solution_unique hcrit f g hg.1 hg.2.1

end PerronWright.FiniteIrreducibleModel
