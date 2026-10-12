import PerronWright.Model.PerronQuantities
import PerronWright.Analysis.PerronSpectrum

open MeasureTheory
noncomputable section
namespace PerronWright
namespace CompactBJRModel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

def weightedIntegral (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℝ)) : ℝ :=
  ∫ x, M.perronFunction hM x * f x ∂M.mu

theorem weightedIntegral_action (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℝ)) :
    M.weightedIntegral hM (M.kernel.action M.mu f) = M.weightedIntegral hM f := by
  obtain ⟨B⟩ := hM.b1
  let u := M.perronFunction hM
  let uf := ContinuousMap.toLp 2 M.mu ℝ u
  let ff := ContinuousMap.toLp 2 M.mu ℝ f
  have hu : B.operator uf = uf := by
    simpa [u, uf] using B.associated.intertwines M B.operator u |>.trans
      (congrArg (ContinuousMap.toLp 2 M.mu ℝ) (M.perronFunction_fixed hM))
  have hf := B.associated.intertwines M B.operator f
  have hs := B.isSymmetric uf ff
  change inner ℝ (B.operator uf) ff = inner ℝ uf (B.operator ff) at hs
  rw [hu] at hs
  rw [hf] at hs
  unfold weightedIntegral
  have hinner₁ := ContinuousMap.inner_toLp (μ := M.mu) u (M.kernel.action M.mu f)
  have hinner₂ := ContinuousMap.inner_toLp (μ := M.mu) u f
  simp only [conj_trivial] at hinner₁ hinner₂
  simpa only [mul_comm] using hinner₁.symm.trans (hs.symm.trans hinner₂)

def weightedIntegralComplex (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℂ)) : ℂ :=
  ∫ x, (M.perronFunction hM x : ℂ) * f x ∂M.mu

theorem weightedIntegralComplex_integrable (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℂ)) :
    Integrable (fun x => (M.perronFunction hM x : ℂ) * f x) M.mu :=
  ((Complex.continuous_ofReal.comp (M.perronFunction hM).continuous).mul f.continuous)
    |>.integrable_of_hasCompactSupport isClosed_closure.isCompact

theorem weightedIntegralComplex_re (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℂ)) :
    (M.weightedIntegralComplex hM f).re = M.weightedIntegral hM (realMap f) := by
  unfold weightedIntegralComplex weightedIntegral
  have heq := Complex.reCLM.integral_comp_comm (M.weightedIntegralComplex_integrable hM f)
  simp only [Complex.reCLM_apply] at heq
  rw [← heq]
  apply integral_congr_ae
  filter_upwards [] with x
  change ((M.perronFunction hM x : ℂ) * f x).re = M.perronFunction hM x * (f x).re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem weightedIntegralComplex_im (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℂ)) :
    (M.weightedIntegralComplex hM f).im = M.weightedIntegral hM (imagMap f) := by
  unfold weightedIntegralComplex weightedIntegral
  have heq := Complex.imCLM.integral_comp_comm (M.weightedIntegralComplex_integrable hM f)
  simp only [Complex.imCLM_apply] at heq
  rw [← heq]
  apply integral_congr_ae
  filter_upwards [] with x
  change ((M.perronFunction hM x : ℂ) * f x).im = M.perronFunction hM x * (f x).im
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

theorem weightedIntegralComplex_action (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℂ)) :
    M.weightedIntegralComplex hM (M.kernel.complexAction M.mu f) =
      M.weightedIntegralComplex hM f := by
  apply Complex.ext
  · rw [M.weightedIntegralComplex_re, M.weightedIntegralComplex_re,
      realMap_complexAction, M.weightedIntegral_action]
  · rw [M.weightedIntegralComplex_im, M.weightedIntegralComplex_im,
      imagMap_complexAction, M.weightedIntegral_action]

theorem weightedIntegralComplex_add (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f g : C(S, ℂ)) :
    M.weightedIntegralComplex hM (f + g) =
      M.weightedIntegralComplex hM f + M.weightedIntegralComplex hM g := by
  unfold weightedIntegralComplex
  simp only [ContinuousMap.add_apply, mul_add]
  exact integral_add (M.weightedIntegralComplex_integrable hM f)
    (M.weightedIntegralComplex_integrable hM g)

theorem weightedIntegralComplex_smul (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (c : ℂ) (f : C(S, ℂ)) :
    M.weightedIntegralComplex hM (c • f) = c • M.weightedIntegralComplex hM f := by
  unfold weightedIntegralComplex
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  calc
    (∫ x, (M.perronFunction hM x : ℂ) * (c * f x) ∂M.mu) =
        ∫ x, c * ((M.perronFunction hM x : ℂ) * f x) ∂M.mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := integral_const_mul _ _

theorem weightedIntegralComplex_norm_le (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℂ)) : ‖M.weightedIntegralComplex hM f‖ ≤ ‖f‖ := by
  have hu : Integrable (M.perronFunction hM) M.mu :=
    (M.perronFunction hM).continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact
  calc
    ‖M.weightedIntegralComplex hM f‖ ≤
        ∫ x, ‖(M.perronFunction hM x : ℂ) * f x‖ ∂M.mu := norm_integral_le_integral_norm _
    _ ≤ ∫ x, M.perronFunction hM x * ‖f‖ ∂M.mu := by
      apply integral_mono (M.weightedIntegralComplex_integrable hM f).norm (hu.mul_const _)
      intro x
      change ‖(M.perronFunction hM x : ℂ) * f x‖ ≤ M.perronFunction hM x * ‖f‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (M.perronFunction_pos hM x)]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (M.perronFunction_pos hM x).le
    _ = ‖f‖ := by rw [integral_mul_const, M.perronFunction_integral, one_mul]

def weightedIntegralComplexCLM (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    C(S, ℂ) →L[ℂ] ℂ :=
  ({ toFun := M.weightedIntegralComplex hM
     map_add' := M.weightedIntegralComplex_add hM
     map_smul' := M.weightedIntegralComplex_smul hM } : C(S, ℂ) →ₗ[ℂ] ℂ).mkContinuous 1
    (fun f => by
      change ‖M.weightedIntegralComplex hM f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using M.weightedIntegralComplex_norm_le hM f)

@[simp] theorem weightedIntegralComplexCLM_apply (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (f : C(S, ℂ)) :
    M.weightedIntegralComplexCLM hM f = M.weightedIntegralComplex hM f := rfl

theorem weightedIntegralComplexCLM_comp_action (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    (M.weightedIntegralComplexCLM hM).comp (M.kernel.complexActionCLM M.mu) =
      M.weightedIntegralComplexCLM hM := by
  ext f
  exact M.weightedIntegralComplex_action hM f

def complexPerronFunction (M : CompactBJRModel S) (hM : M.IsRegularCritical) : C(S, ℂ) :=
  ⟨fun x => (M.perronFunction hM x : ℂ),
    Complex.continuous_ofReal.comp (M.perronFunction hM).continuous⟩

@[simp] theorem complexPerronFunction_apply (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (x : S) :
    M.complexPerronFunction hM x = (M.perronFunction hM x : ℂ) := rfl

@[simp] theorem realMap_complexPerronFunction (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    realMap (M.complexPerronFunction hM) = M.perronFunction hM := by
  ext x
  rfl

@[simp] theorem imagMap_complexPerronFunction (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) : imagMap (M.complexPerronFunction hM) = 0 := by
  ext x
  rfl

theorem complexPerronFunction_fixed (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    M.kernel.complexAction M.mu (M.complexPerronFunction hM) =
      M.complexPerronFunction hM := by
  have hre := realMap_complexAction M (M.complexPerronFunction hM)
  rw [M.realMap_complexPerronFunction, M.perronFunction_fixed] at hre
  have him := imagMap_complexAction M (M.complexPerronFunction hM)
  rw [M.imagMap_complexPerronFunction] at him
  have him0 : M.kernel.action M.mu (0 : C(S, ℝ)) = 0 :=
    (M.kernel.actionCLM M.mu).map_zero
  rw [him0] at him
  ext x
  apply Complex.ext
  · exact congrArg (fun g : C(S, ℝ) => g x) hre
  · exact congrArg (fun g : C(S, ℝ) => g x) him

theorem weightedIntegral_perronFunction (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    M.weightedIntegral hM (M.perronFunction hM) = M.alpha hM := by
  unfold weightedIntegral alpha
  simp only [pow_two]

theorem weightedIntegralComplex_perronFunction (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    M.weightedIntegralComplex hM (M.complexPerronFunction hM) = (M.alpha hM : ℂ) := by
  apply Complex.ext
  · rw [M.weightedIntegralComplex_re, M.realMap_complexPerronFunction,
      M.weightedIntegral_perronFunction, Complex.ofReal_re]
  · rw [M.weightedIntegralComplex_im, M.imagMap_complexPerronFunction]
    simp only [weightedIntegral, ContinuousMap.zero_apply, mul_zero, integral_zero,
      Complex.ofReal_im]

/-- The left Perron functional normalized by `ell(u) = 1`. -/
def normalizedPerronFunctional (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    C(S, ℂ) →L[ℂ] ℂ :=
  (M.alpha hM : ℂ)⁻¹ • M.weightedIntegralComplexCLM hM

theorem normalizedPerronFunctional_perronFunction (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    M.normalizedPerronFunctional hM (M.complexPerronFunction hM) = 1 := by
  simp only [normalizedPerronFunctional, smul_apply, smul_eq_mul,
    weightedIntegralComplexCLM_apply, weightedIntegralComplex_perronFunction]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (M.alpha_pos hM).ne')

theorem normalizedPerronFunctional_comp_action (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    (M.normalizedPerronFunctional hM).comp (M.kernel.complexActionCLM M.mu) =
      M.normalizedPerronFunctional hM := by
  ext f
  change (M.alpha hM : ℂ)⁻¹ * M.weightedIntegralComplex hM (M.kernel.complexAction M.mu f) =
    (M.alpha hM : ℂ)⁻¹ * M.weightedIntegralComplex hM f
  rw [M.weightedIntegralComplex_action]








end CompactBJRModel
end PerronWright

