import PerronWright.Analysis.PerronFunctional

open MeasureTheory Module
noncomputable section

namespace PerronWright.CompactBJRModel
variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem complex_fixed_eq_scalar_multiple (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℂ)) (hf : M.kernel.complexAction M.mu f = f) :
    ∃ c : ℂ, f = c • M.complexPerronFunction hM := by
  have hre : M.kernel.action M.mu (realMap f) = realMap f := by
    rw [← realMap_complexAction, hf]
  have him : M.kernel.action M.mu (imagMap f) = imagMap f := by
    rw [← imagMap_complexAction, hf]
  obtain ⟨a, ha⟩ := fixed_eq_scalar_multiple M hM.b2 (M.perronFunction hM)
    (M.perronFunction_pos hM) (M.perronFunction_fixed hM) (realMap f) hre
  obtain ⟨b, hb⟩ := fixed_eq_scalar_multiple M hM.b2 (M.perronFunction hM)
    (M.perronFunction_pos hM) (M.perronFunction_fixed hM) (imagMap f) him
  refine ⟨⟨a, b⟩, ?_⟩
  ext x
  apply Complex.ext
  · have hax := congrArg (fun g : C(S, ℝ) => g x) ha
    simpa only [realMap, ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul,
      complexPerronFunction_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using hax
  · have hbx := congrArg (fun g : C(S, ℝ) => g x) hb
    simpa only [imagMap, ContinuousMap.coe_mk, ContinuousMap.smul_apply, smul_eq_mul,
      complexPerronFunction_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add] using hbx

theorem complex_fixed_eq_perronFunctional_smul (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (f : C(S, ℂ))
    (hf : M.kernel.complexAction M.mu f = f) :
    f = M.normalizedPerronFunctional hM f • M.complexPerronFunction hM := by
  obtain ⟨c, hc⟩ := M.complex_fixed_eq_scalar_multiple hM f hf
  rw [hc, map_smul, M.normalizedPerronFunctional_perronFunction, smul_eq_mul, mul_one]

def perronProjection (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    C(S, ℂ) →L[ℂ] C(S, ℂ) :=
  (M.normalizedPerronFunctional hM).smulRight (M.complexPerronFunction hM)

@[simp] theorem perronProjection_apply (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℂ)) :
    M.perronProjection hM f = M.normalizedPerronFunctional hM f • M.complexPerronFunction hM := rfl

theorem perronProjection_isCompact (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    IsCompactOperator (M.perronProjection hM) := by
  have h := isCompactOperator_of_locallyCompactSpace_dom (M.normalizedPerronFunctional hM)
  exact h.clm_comp ((ContinuousLinearMap.id ℂ ℂ).smulRight (M.complexPerronFunction hM))

theorem normalizedPerronFunctional_action (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℂ)) :
    M.normalizedPerronFunctional hM (M.kernel.complexAction M.mu f) =
      M.normalizedPerronFunctional hM f :=
  congrArg (fun A : C(S, ℂ) →L[ℂ] ℂ => A f) (M.normalizedPerronFunctional_comp_action hM)

@[simp] theorem normalizedPerronFunctional_projection (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (f : C(S, ℂ)) :
    M.normalizedPerronFunctional hM (M.perronProjection hM f) =
      M.normalizedPerronFunctional hM f := by
  rw [M.perronProjection_apply, map_smul, M.normalizedPerronFunctional_perronFunction,
    smul_eq_mul, mul_one]

theorem perronProjection_idempotent (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (M.perronProjection hM).comp (M.perronProjection hM) = M.perronProjection hM := by
  apply ContinuousLinearMap.ext
  intro f
  change M.perronProjection hM (M.perronProjection hM f) = M.perronProjection hM f
  rw [M.perronProjection_apply, M.normalizedPerronFunctional_projection,
    M.perronProjection_apply]

theorem kernel_sub_perronProjection_isCompact (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    IsCompactOperator (M.kernel.complexActionCLM M.mu - M.perronProjection hM) :=
  (M.kernel.isCompactOperator_complexActionCLM M.mu).sub (M.perronProjection_isCompact hM)

theorem kernel_sub_perronProjection_no_eigenvalue_one (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ¬ Module.End.HasEigenvalue
      (M.kernel.complexActionCLM M.mu - M.perronProjection hM).toLinearMap 1 := by
  intro hev
  obtain ⟨f, hf, hfne⟩ := hev.exists_hasEigenvector
  have heq : M.kernel.complexAction M.mu f - M.perronProjection hM f = f := by
    have heq := Module.End.mem_eigenspace_iff.mp hf
    change M.kernel.complexAction M.mu f - M.perronProjection hM f = (1 : ℂ) • f at heq
    simpa only [one_smul] using heq
  have hell := congrArg (M.normalizedPerronFunctional hM) heq
  rw [map_sub, M.normalizedPerronFunctional_action,
    M.normalizedPerronFunctional_projection, sub_self] at hell
  have hp : M.perronProjection hM f = 0 := by
    rw [M.perronProjection_apply, ← hell, zero_smul]
  rw [hp, sub_zero] at heq
  have hfix := M.complex_fixed_eq_perronFunctional_smul hM f heq
  rw [← hell, zero_smul] at hfix
  exact hfne hfix

theorem augmented_kernel_isUnit (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    IsUnit (1 - M.kernel.complexActionCLM M.mu + M.perronProjection hM) := by
  have hr := (M.kernel_sub_perronProjection_isCompact hM).hasEigenvalue_or_mem_resolventSet
    (by norm_num : (1 : ℂ) ≠ 0)
  have hres := hr.resolve_left (M.kernel_sub_perronProjection_no_eigenvalue_one hM)
  rw [spectrum.mem_resolventSet_iff] at hres
  simpa only [map_one, sub_sub_eq_add_sub, sub_add_eq_add_sub] using hres

def augmentedKernelEquiv (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    C(S, ℂ) ≃L[ℂ] C(S, ℂ) :=
  ContinuousLinearEquiv.ofUnit (M.augmented_kernel_isUnit hM).unit

theorem augmentedKernelEquiv_apply (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℂ)) :
    M.augmentedKernelEquiv hM f =
      f - M.kernel.complexAction M.mu f + M.perronProjection hM f := by
  change ((M.augmented_kernel_isUnit hM).unit : C(S, ℂ) →L[ℂ] C(S, ℂ)) f = _
  rw [IsUnit.unit_spec]
  rfl

def augmentedKernelInverse (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    C(S, ℂ) →L[ℂ] C(S, ℂ) :=
  (M.augmentedKernelEquiv hM).symm.toContinuousLinearMap

theorem augmentedKernelInverse_right_inverse (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (f : C(S, ℂ)) :
    M.augmentedKernelInverse hM f -
        M.kernel.complexAction M.mu (M.augmentedKernelInverse hM f) +
        M.perronProjection hM (M.augmentedKernelInverse hM f) = f := by
  exact (M.augmentedKernelEquiv_apply hM _).symm.trans
    ((M.augmentedKernelEquiv hM).apply_symm_apply f)

theorem normalizedPerronFunctional_inverse (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (f : C(S, ℂ)) :
    M.normalizedPerronFunctional hM (M.augmentedKernelInverse hM f) =
      M.normalizedPerronFunctional hM f := by
  have heq := congrArg (M.normalizedPerronFunctional hM)
    (M.augmentedKernelInverse_right_inverse hM f)
  simpa only [map_add, map_sub, M.normalizedPerronFunctional_action,
    M.normalizedPerronFunctional_projection, sub_self, zero_add] using heq

theorem augmentedKernelInverse_on_complement (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (f : C(S, ℂ))
    (hf : M.normalizedPerronFunctional hM f = 0) :
    M.normalizedPerronFunctional hM (M.augmentedKernelInverse hM f) = 0 ∧
      M.augmentedKernelInverse hM f -
        M.kernel.complexAction M.mu (M.augmentedKernelInverse hM f) = f := by
  have hzero : M.normalizedPerronFunctional hM (M.augmentedKernelInverse hM f) = 0 :=
    (M.normalizedPerronFunctional_inverse hM f).trans hf
  refine ⟨hzero, ?_⟩
  have heq := M.augmentedKernelInverse_right_inverse hM f
  rwa [M.perronProjection_apply, hzero, zero_smul, add_zero] at heq

theorem complement_solution_unique (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f g : C(S, ℂ)) (hg : M.normalizedPerronFunctional hM g = 0)
    (heq : g - M.kernel.complexAction M.mu g = f) :
    g = M.augmentedKernelInverse hM f := by
  apply (M.augmentedKernelEquiv hM).injective
  rw [M.augmentedKernelEquiv_apply, M.perronProjection_apply, hg, zero_smul, add_zero, heq]
  exact ((M.augmentedKernelEquiv hM).apply_symm_apply f).symm

theorem complement_inverse_bounded (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : C(S, ℂ), M.normalizedPerronFunctional hM f = 0 →
      ∃! g : C(S, ℂ), M.normalizedPerronFunctional hM g = 0 ∧
        g - M.kernel.complexAction M.mu g = f ∧ ‖g‖ ≤ C * ‖f‖ := by
  refine ⟨‖M.augmentedKernelInverse hM‖ + 1, by positivity, ?_⟩
  intro f hf
  refine ⟨M.augmentedKernelInverse hM f, ?_, ?_⟩
  · obtain ⟨hzero, heq⟩ := M.augmentedKernelInverse_on_complement hM f hf
    refine ⟨hzero, heq, ?_⟩
    calc
      ‖M.augmentedKernelInverse hM f‖ ≤ ‖M.augmentedKernelInverse hM‖ * ‖f‖ :=
        (M.augmentedKernelInverse hM).le_opNorm f
      _ ≤ (‖M.augmentedKernelInverse hM‖ + 1) * ‖f‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg f)
  · intro g hg
    exact M.complement_solution_unique hM f g hg.1 hg.2.1






end PerronWright.CompactBJRModel

