import PerronWright.Analysis.Positive
import PerronWright.Kernel.Complex
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

open MeasureTheory Module
noncomputable section
namespace PerronWright
variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem l2_fixed_eq_scalar_multiple (M : CompactBJRModel S) (B : M.B1Witness)
    (hB2 : M.B2) (u : C(S, ℝ)) (hu : ∀ x, 0 < u x)
    (hTu : M.kernel.action M.mu u = u)
    (v : M.L2) (hv : B.operator v = v) :
    ∃ c : ℝ, v = c • ContinuousMap.toLp 2 M.mu ℝ u := by
  have hf : M.kernel.action M.mu (M.smooth v) = M.smooth v := by
    rw [← M.smooth_toLp, B.associated.smoothing M B.operator, hv]
  obtain ⟨c, hc⟩ := fixed_eq_scalar_multiple M hB2 u hu hTu (M.smooth v) hf
  refine ⟨c, ?_⟩
  rw [← hv, ← B.associated.smoothing M B.operator v, hc, map_smul]

theorem l2_eigenspace_one_eq_span (M : CompactBJRModel S) (B : M.B1Witness)
    (hB2 : M.B2) (u : C(S, ℝ)) (hu : ∀ x, 0 < u x)
    (hTu : M.kernel.action M.mu u = u) :
    Module.End.eigenspace B.operator.toLinearMap 1 =
      Submodule.span ℝ {ContinuousMap.toLp 2 M.mu ℝ u} := by
  apply le_antisymm
  · intro v hv
    obtain ⟨c, hc⟩ := l2_fixed_eq_scalar_multiple M B hB2 u hu hTu v
      (by simpa using Module.End.mem_eigenspace_iff.mp hv)
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · apply Submodule.span_le.mpr
    intro v hv
    obtain rfl := Set.mem_singleton_iff.mp hv
    apply Module.End.mem_eigenspace_iff.mpr
    simpa [hTu] using B.associated.intertwines M B.operator u

theorem l2_genEigenspace_one_eq_span (M : CompactBJRModel S) (B : M.B1Witness)
    (hB2 : M.B2) (u : C(S, ℝ)) (hu : ∀ x, 0 < u x)
    (hTu : M.kernel.action M.mu u = u) {n : ℕ∞} (hn : 0 < n) :
    Module.End.genEigenspace B.operator.toLinearMap 1 n =
      Submodule.span ℝ {ContinuousMap.toLp 2 M.mu ℝ u} := by
  rw [B.isSymmetric.isFinitelySemisimple.genEigenspace_eq_eigenspace 1 hn]
  exact l2_eigenspace_one_eq_span M B hB2 u hu hTu

theorem l2_genEigenspace_one_finrank (M : CompactBJRModel S) (B : M.B1Witness)
    (hB2 : M.B2) (u : C(S, ℝ)) (hu : ∀ x, 0 < u x)
    (hTu : M.kernel.action M.mu u = u) {n : ℕ∞} (hn : 0 < n) :
    Module.finrank ℝ (Module.End.genEigenspace B.operator.toLinearMap 1 n) = 1 := by
  rw [l2_genEigenspace_one_eq_span M B hB2 u hu hTu hn]
  apply finrank_span_singleton
  intro hz
  have hzero : u = 0 := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) M.mu
    (by simpa using hz)
  obtain ⟨x, -⟩ := nonempty_of_measure_ne_zero (μ := M.mu)
    (s := Set.univ) (by simp)
  have := hu x
  simp [hzero] at this

omit [MeasurableSpace S] [BorelSpace S] in
theorem stronglyPositivePower_square [Nonempty S]
    (T : C(S, ℝ) →L[ℝ] C(S, ℝ))
    (hT : ∃ n : ℕ, ∀ f : C(S, ℝ), (∀ y, 0 ≤ f y) → f ≠ 0 →
      ∀ x, 0 < (T ^ n.succ) f x) :
    ∃ n : ℕ, ∀ f : C(S, ℝ), (∀ y, 0 ≤ f y) → f ≠ 0 →
      ∀ x, 0 < ((T ^ 2) ^ n.succ) f x := by
  obtain ⟨n, hn⟩ := hT
  refine ⟨n, ?_⟩
  intro f hf hfne x
  have hpos := hn f hf hfne
  have hne : (T ^ n.succ) f ≠ 0 := by
    intro hz
    have := hpos (Classical.choice ‹Nonempty S›)
    simp [hz] at this
  have hpos2 := hn ((T ^ n.succ) f) (fun x => (hpos x).le) hne x
  rw [← mul_apply_eq_comp, ← pow_add] at hpos2
  rw [← pow_mul, two_mul]
  exact hpos2

theorem continuous_neg_one_eigenvector_eq_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (f : C(S, ℝ))
    (hf : M.kernel.action M.mu f = -f) : f = 0 := by
  obtain ⟨x, -⟩ := nonempty_of_measure_ne_zero (μ := M.mu)
    (s := Set.univ) (by simp)
  let _ : Nonempty S := ⟨x⟩
  obtain ⟨u, hu, hTu⟩ := exists_positive_fixed M hM
  let T := M.kernel.actionCLM M.mu
  have hT2u : (T ^ 2) u = u := by
    simp [T, pow_two, mul_apply_eq_comp, hTu]
  have hT2f : (T ^ 2) f = f := by
    simp only [pow_two, mul_apply_eq_comp]
    change M.kernel.action M.mu (M.kernel.action M.mu f) = f
    rw [hf]
    change T (-f) = f
    rw [map_neg]
    change -(M.kernel.action M.mu f) = f
    rw [hf, neg_neg]
  obtain ⟨c, hc⟩ := fixed_eq_smul_of_positive (T ^ 2)
    (stronglyPositivePower_square T (hM.b2.stronglyPositivePower M))
    u hu hT2u f hT2f
  have hfix : M.kernel.action M.mu f = f := by
    rw [hc, M.kernel.action_smul, hTu]
  have heq : f = -f := hfix.symm.trans hf
  ext y
  have hy := congrArg (fun g : C(S, ℝ) => g y) heq
  change f y = 0
  simp only [ContinuousMap.neg_apply] at hy
  linarith

theorem l2_not_hasEigenvalue_neg_one (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (B : M.B1Witness) :
    ¬ Module.End.HasEigenvalue B.operator.toLinearMap (-1) := by
  intro h
  obtain ⟨v, hv, hvne⟩ := h.exists_hasEigenvector
  obtain ⟨f, hfne, -, hf⟩ := B.associated.exists_continuous_eigenvector
    M B.operator (by norm_num : (-1 : ℝ) ≠ 0)
    (Module.End.mem_eigenspace_iff.mp hv) hvne
  exact hfne (continuous_neg_one_eigenvector_eq_zero M hM f (by simpa using hf))

theorem l2_real_peripheral_eigenvalue_eq_one (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (B : M.B1Witness) (lam : ℝ)
    (hlam : |lam| = 1)
    (hev : Module.End.HasEigenvalue B.operator.toLinearMap lam) : lam = 1 := by
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hlam with hp | hn
  · exact hp
  · exact False.elim (l2_not_hasEigenvalue_neg_one M hM B (hn ▸ hev))

theorem l2_real_peripheral_spectrum_eq_one (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (B : M.B1Witness) (lam : ℝ)
    (hlam : |lam| = 1) (hs : lam ∈ spectrum ℝ B.operator) : lam = 1 := by
  have hne : lam ≠ 0 := by
    intro heq
    simp [heq] at hlam
  exact l2_real_peripheral_eigenvalue_eq_one M hM B lam hlam
    ((B.isCompact.hasEigenvalue_iff_mem_spectrum hne).mpr hs)

def realMap (f : C(S, ℂ)) : C(S, ℝ) :=
  ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
def imagMap (f : C(S, ℂ)) : C(S, ℝ) :=
  ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩

theorem realMap_complexAction (M : CompactBJRModel S) (f : C(S, ℂ)) :
    realMap (M.kernel.complexAction M.mu f) = M.kernel.action M.mu (realMap f) := by
  ext x
  change (M.kernel.complexAction M.mu f x).re = M.kernel.action M.mu (realMap f) x
  rw [ContinuousKernel.complexAction_apply, ContinuousKernel.action_apply]
  have hi : Integrable (fun y => (M.kernel x y : ℂ) * f y) M.mu :=
    ((Complex.continuous_ofReal.comp (M.kernel.continuous_left x)).mul f.continuous)
      |>.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have heq := Complex.reCLM.integral_comp_comm hi
  simp only [Complex.reCLM_apply] at heq
  rw [← heq]
  apply integral_congr_ae
  filter_upwards [] with y
  change ((M.kernel x y : ℂ) * f y).re = M.kernel x y * (f y).re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem imagMap_complexAction (M : CompactBJRModel S) (f : C(S, ℂ)) :
    imagMap (M.kernel.complexAction M.mu f) = M.kernel.action M.mu (imagMap f) := by
  ext x
  change (M.kernel.complexAction M.mu f x).im = M.kernel.action M.mu (imagMap f) x
  rw [ContinuousKernel.complexAction_apply, ContinuousKernel.action_apply]
  have hi : Integrable (fun y => (M.kernel x y : ℂ) * f y) M.mu :=
    ((Complex.continuous_ofReal.comp (M.kernel.continuous_left x)).mul f.continuous)
      |>.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have heq := Complex.imCLM.integral_comp_comm hi
  simp only [Complex.imCLM_apply] at heq
  rw [← heq]
  apply integral_congr_ae
  filter_upwards [] with y
  change ((M.kernel x y : ℂ) * f y).im = M.kernel x y * (f y).im
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

theorem realMap_eigen_equation (M : CompactBJRModel S) (f : C(S, ℂ)) (lam : ℂ)
    (hf : M.kernel.complexAction M.mu f = lam • f) :
    M.kernel.action M.mu (realMap f) = lam.re • realMap f - lam.im • imagMap f := by
  rw [← realMap_complexAction, hf]
  ext x
  simp [realMap, imagMap, Complex.mul_re]

theorem imagMap_eigen_equation (M : CompactBJRModel S) (f : C(S, ℂ)) (lam : ℂ)
    (hf : M.kernel.complexAction M.mu f = lam • f) :
    M.kernel.action M.mu (imagMap f) = lam.im • realMap f + lam.re • imagMap f := by
  rw [← imagMap_complexAction, hf]
  ext x
  simp [realMap, imagMap, Complex.mul_im, add_comm]

theorem complex_eigenvalue_im_eq_zero (M : CompactBJRModel S) (B : M.B1Witness)
    (f : C(S, ℂ)) (hfne : f ≠ 0) (lam : ℂ)
    (hf : M.kernel.complexAction M.mu f = lam • f) : lam.im = 0 := by
  let a := ContinuousMap.toLp 2 M.mu ℝ (realMap f)
  let b := ContinuousMap.toLp 2 M.mu ℝ (imagMap f)
  have ha : B.operator a = lam.re • a - lam.im • b := by
    dsimp [a, b]
    rw [B.associated.intertwines, realMap_eigen_equation M f lam hf, map_sub,
      map_smul, map_smul]
  have hb : B.operator b = lam.im • a + lam.re • b := by
    dsimp [a, b]
    rw [B.associated.intertwines, imagMap_eigen_equation M f lam hf, map_add,
      map_smul, map_smul]
  have hs := B.isSymmetric a b
  change inner ℝ (B.operator a) b = inner ℝ a (B.operator b) at hs
  rw [ha, hb, inner_sub_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hs
  have hmul : lam.im * (‖a‖ ^ 2 + ‖b‖ ^ 2) = 0 := by linarith
  rcases mul_eq_zero.mp hmul with h | h
  · exact h
  · have ha0 : a = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖b‖, norm_nonneg a])
    have hb0 : b = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg ‖a‖, norm_nonneg b])
    have har : realMap f = 0 := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) M.mu
      (by simpa [a] using ha0)
    have hbi : imagMap f = 0 := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) M.mu
      (by simpa [b] using hb0)
    exfalso
    apply hfne
    ext x
    apply Complex.ext
    · exact congrArg (fun g : C(S, ℝ) => g x) har
    · exact congrArg (fun g : C(S, ℝ) => g x) hbi

theorem complex_peripheral_eigenvalue_eq_one (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (B : M.B1Witness)
    (f : C(S, ℂ)) (hfne : f ≠ 0) (lam : ℂ) (hlam : ‖lam‖ = 1)
    (hf : M.kernel.complexAction M.mu f = lam • f) : lam = 1 := by
  have him := complex_eigenvalue_im_eq_zero M B f hfne lam hf
  have hreal : (lam.re : ℂ) = lam := by
    apply Complex.ext <;> simp [him]
  have hre : |lam.re| = 1 := by
    rw [← hreal, Complex.norm_real, Real.norm_eq_abs] at hlam
    exact hlam
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hre with hp | hn
  · apply Complex.ext <;> simp [hp, him]
  · have ha := realMap_eigen_equation M f lam hf
    have hb := imagMap_eigen_equation M f lam hf
    rw [hn, him, zero_smul, sub_zero, neg_one_smul] at ha
    rw [hn, him, zero_smul, zero_add, neg_one_smul] at hb
    have ha0 := continuous_neg_one_eigenvector_eq_zero M hM (realMap f) ha
    have hb0 := continuous_neg_one_eigenvector_eq_zero M hM (imagMap f) hb
    exfalso
    apply hfne
    ext x
    apply Complex.ext
    · exact congrArg (fun g : C(S, ℝ) => g x) ha0
    · exact congrArg (fun g : C(S, ℝ) => g x) hb0

theorem complex_peripheral_spectrum_eq_one (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (B : M.B1Witness)
    (lam : ℂ) (hlam : ‖lam‖ = 1)
    (hs : lam ∈ spectrum ℂ (M.kernel.complexActionCLM M.mu)) : lam = 1 := by
  have hne : lam ≠ 0 := by
    intro heq
    simp [heq] at hlam
  have hcompact := M.kernel.isCompactOperator_complexActionCLM M.mu
  have hev := (hcompact.hasEigenvalue_iff_mem_spectrum hne).mpr hs
  obtain ⟨f, hf, hfne⟩ := hev.exists_hasEigenvector
  exact complex_peripheral_eigenvalue_eq_one M hM B f hfne lam hlam
    (Module.End.mem_eigenspace_iff.mp hf)

end PerronWright

