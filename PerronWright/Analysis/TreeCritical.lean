import PerronWright.Analysis.TreeImplicit
import PerronWright.Model.CompactBJR

open MeasureTheory PerronWright

noncomputable section

namespace PerronWright.TreeCritical

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The complex degree function is the actual kernel applied to one. -/
def degree (M : CompactBJRModel S) : C(S, ℂ) := M.kernel.complexActionCLM M.mu 1

theorem degree_apply (M : CompactBJRModel S) (x : S) :
    degree M x = (M.kernel.degree M.mu x : ℂ) := by
  unfold degree
  rw [ContinuousKernel.complexActionCLM_apply, ContinuousKernel.complexAction_apply]
  simp only [ContinuousMap.one_apply, mul_one]
  exact integral_complex_ofReal

/-- The model's tree residual, with the degree fixed by the same model. -/
def residual (M : CompactBJRModel S) :=
  TreeAnalytic.residual M.kernel M.mu (degree M)

theorem critical_base (M : CompactBJRModel S) :
    residual M ((1, 0), 1) = 0 := by
  simp only [residual, TreeAnalytic.residual, degree,
    zero_sub, neg_add_cancel, NormedSpace.exp_zero, one_smul, sub_self]

theorem critical_partial (M : CompactBJRModel S) :
    fderiv ℂ (residual M) ((1, 0), 1) ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ) =
      ContinuousLinearMap.id ℂ C(S, ℂ) - M.kernel.complexActionCLM M.mu := by
  unfold residual
  rw [TreeAnalytic.residual_partial]
  simp only [degree, zero_sub, neg_add_cancel, NormedSpace.exp_zero, one_smul]

theorem critical_fderiv_unknown (M : CompactBJRModel S) :
    fderiv ℂ (fun U : C(S, ℂ) ↦ residual M ((1, 0), U)) 1 =
      ContinuousLinearMap.id ℂ C(S, ℂ) - M.kernel.complexActionCLM M.mu := by
  unfold residual
  rw [TreeAnalytic.residual_fderiv_unknown]
  simp only [degree, zero_sub, neg_add_cancel, NormedSpace.exp_zero, one_smul]

theorem critical_z_deriv (M : CompactBJRModel S) :
    deriv (fun z : ℂ ↦ residual M ((z, 0), 1)) 1 = -(1 : C(S, ℂ)) := by
  have hfun : (fun z : ℂ ↦ residual M ((z, 0), 1)) =
      (fun z : ℂ ↦ (1 : C(S, ℂ)) - z • (1 : C(S, ℂ))) := by
    funext z
    simp only [residual, TreeAnalytic.residual, degree,
      zero_sub, neg_add_cancel, NormedSpace.exp_zero]
  rw [hfun]
  convert ((hasDerivAt_const (1 : ℂ) (1 : C(S, ℂ))).sub
    ((hasDerivAt_id (1 : ℂ)).smul_const (1 : C(S, ℂ)))).deriv using 1 <;>
    first | rfl | simp only [one_smul, zero_sub]

/-- The second derivative in two arbitrary continuous field directions. -/
theorem critical_second_unknown (M : CompactBJRModel S) (h v : C(S, ℂ)) :
    (fderiv ℂ (fun U : C(S, ℂ) ↦
      (fderiv ℂ (fun V : C(S, ℂ) ↦ residual M ((1, 0), V)) U) h) 1) v =
      -(M.kernel.complexActionCLM M.mu v * M.kernel.complexActionCLM M.mu h) := by
  let K := M.kernel.complexActionCLM M.mu
  have hfun : (fun U : C(S, ℂ) ↦
      (fderiv ℂ (fun V : C(S, ℂ) ↦ residual M ((1, 0), V)) U) h) =
      (fun U : C(S, ℂ) ↦ h - NormedSpace.exp (-degree M + K U) * K h) := by
    funext U
    unfold residual
    rw [TreeAnalytic.residual_fderiv_unknown]
    ext x
    simp only [K, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      smul_eq_mul, one_mul, zero_sub]
  have hinner := K.hasFDerivAt.const_add (-degree M) (x := (1 : C(S, ℂ)))
  have hexp := (hasFDerivAt_exp (𝕂 := ℂ) (x := -degree M + K 1)).comp 1 hinner
  have hderiv := (hexp.mul_const (K h)).neg.const_add h
  rw [hfun]
  have hd : fderiv ℂ (fun U : C(S, ℂ) ↦ h - NormedSpace.exp (-degree M + K U) * K h) 1 =
      -(K h • ((NormedSpace.exp (-degree M + K 1) • 1) ∘L K)) := by
    convert hderiv.fderiv using 1
    congr 1
  rw [hd]
  ext x
  simp only [K, degree, neg_add_cancel, NormedSpace.exp_zero,
    one_smul, ContinuousLinearMap.comp_apply,
    one_apply_eq_self, neg_apply, smul_apply,
    ContinuousMap.neg_apply, ContinuousMap.mul_apply,
    smul_eq_mul]
  ring

end PerronWright.TreeCritical

