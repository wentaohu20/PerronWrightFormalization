import PerronWright.Kernel.Complex
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped Topology ContDiff

noncomputable section

namespace PerronWright.TreeAnalytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Banach analytic IFT directly from the existing `C^ω` theorem. -/
theorem analytic_implicit_exists {f : E × F → F} {a : E × F}
    (hf : AnalyticAt ℂ f a)
    (hi : (fderiv ℂ f a ∘L ContinuousLinearMap.inr ℂ E F).IsInvertible) :
    ∃ ψ : E → F, AnalyticAt ℂ ψ a.1 ∧ ψ a.1 = a.2 ∧
      (∀ᶠ x in 𝓝 a.1, f (x, ψ x) = f a) ∧
      (∀ᶠ p in 𝓝 a, f p = f a ↔ ψ p.1 = p.2) := by
  have hc : ContDiffAt ℂ ω f a := hf.contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  refine ⟨hc.implicitFunction hn hi, ?_, ?_, ?_, ?_⟩
  · exact (hc.contDiffAt_implicitFunction hn hi).analyticAt
  · exact hc.implicitFunction_apply_self hn hi
  · exact hc.eventually_apply_implicitFunction hn hi
  · exact hc.eventually_apply_eq_iff_implicitFunction hn hi

open MeasureTheory PerronWright

variable {S : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

variable (k : ContinuousKernel S) (mu : Measure S) [IsProbabilityMeasure mu]

def residual (d : C(S, ℂ)) : (ℂ × C(S, ℂ)) × C(S, ℂ) → C(S, ℂ) :=
  fun q ↦ q.2 - q.1.1 • NormedSpace.exp (q.1.2 - d + k.complexActionCLM mu q.2)

theorem residual_analytic (d : C(S, ℂ)) (q : (ℂ × C(S, ℂ)) × C(S, ℂ)) :
    AnalyticAt ℂ (residual k mu d) q := by
  unfold residual
  have hU : AnalyticAt ℂ (fun q : (ℂ × C(S, ℂ)) × C(S, ℂ) ↦ q.2) q :=
    analyticAt_snd
  have hg : AnalyticAt ℂ (fun q : (ℂ × C(S, ℂ)) × C(S, ℂ) ↦ q.1.2) q :=
    analyticAt_snd.comp analyticAt_fst
  have hz : AnalyticAt ℂ (fun q : (ℂ × C(S, ℂ)) × C(S, ℂ) ↦ q.1.1) q :=
    analyticAt_fst.comp analyticAt_fst
  have hinner : AnalyticAt ℂ
      (fun q : (ℂ × C(S, ℂ)) × C(S, ℂ) ↦
        q.1.2 - d + k.complexActionCLM mu q.2) q :=
    (hg.sub analyticAt_const).add ((k.complexActionCLM mu).analyticAt _ |>.comp hU)
  have hexp : AnalyticAt ℂ
      (fun q : (ℂ × C(S, ℂ)) × C(S, ℂ) ↦
        NormedSpace.exp (q.1.2 - d + k.complexActionCLM mu q.2)) q := by
    exact (NormedSpace.exp_analytic _).comp hinner
  exact hU.sub (hz.smul hexp)

theorem residual_implicit_exists (d : C(S, ℂ)) (a : (ℂ × C(S, ℂ)) × C(S, ℂ))
    (hi : (fderiv ℂ (residual k mu d) a ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)).IsInvertible) :
    ∃ ψ : ℂ × C(S, ℂ) → C(S, ℂ), AnalyticAt ℂ ψ a.1 ∧ ψ a.1 = a.2 ∧
      (∀ᶠ x in 𝓝 a.1, residual k mu d (x, ψ x) = residual k mu d a) ∧
      (∀ᶠ p in 𝓝 a, residual k mu d p = residual k mu d a ↔ ψ p.1 = p.2) :=
  analytic_implicit_exists (residual_analytic k mu d a) hi

theorem residual_fderiv_unknown (d g U : C(S, ℂ)) (z : ℂ) :
    fderiv ℂ (fun V : C(S, ℂ) ↦ residual k mu d ((z, g), V)) U =
      ContinuousLinearMap.id ℂ C(S, ℂ) -
        z • (NormedSpace.exp (g - d + k.complexActionCLM mu U) • k.complexActionCLM mu) := by
  have hinner : HasFDerivAt (fun V : C(S, ℂ) ↦ g - d + k.complexActionCLM mu V)
      (k.complexActionCLM mu) U := (k.complexActionCLM mu).hasFDerivAt.const_add _
  have hexp := (hasFDerivAt_exp (𝕂 := ℂ)
    (x := g - d + k.complexActionCLM mu U)).comp U hinner
  have h := (hasFDerivAt_id U).sub (hexp.const_smul z)
  convert h.fderiv using 1
  · rfl
  · rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]

theorem residual_partial (d g U : C(S, ℂ)) (z : ℂ) :
    fderiv ℂ (residual k mu d) ((z, g), U) ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ) =
      ContinuousLinearMap.id ℂ C(S, ℂ) -
        z • (NormedSpace.exp (g - d + k.complexActionCLM mu U) • k.complexActionCLM mu) := by
  have hj := (hasFDerivAt_const (𝕜 := ℂ) (z, g) U).prodMk (hasFDerivAt_id U)
  have h := ((residual_analytic k mu d ((z, g), U)).hasStrictFDerivAt.hasFDerivAt.comp U hj).fderiv
  have hinr : ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ) =
      ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℂ C(S, ℂ)) := by
    ext V <;> rfl
  rw [hinr]
  rw [← h]
  exact residual_fderiv_unknown k mu d g U z

theorem zero_tree_branch (d : C(S, ℂ)) :
    ∃ ψ : ℂ × C(S, ℂ) → C(S, ℂ), AnalyticAt ℂ ψ (0, 0) ∧ ψ (0, 0) = 0 ∧
      (∀ᶠ x in 𝓝 (0, (0 : C(S, ℂ))), residual k mu d (x, ψ x) = 0) ∧
      (∀ᶠ p in 𝓝 ((0, (0 : C(S, ℂ))), (0 : C(S, ℂ))),
        residual k mu d p = 0 ↔ ψ p.1 = p.2) := by
  have hi : (fderiv ℂ (residual k mu d) ((0, 0), 0) ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)).IsInvertible := by
    rw [residual_partial]
    refine ⟨ContinuousLinearEquiv.refl ℂ C(S, ℂ), ?_⟩
    ext V x
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.refl_apply,
      sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      smul_eq_mul, zero_mul, sub_zero]
  have hzero : residual k mu d ((0, 0), 0) = 0 := by
    simp only [residual, zero_smul, sub_zero]
  simpa only [hzero] using residual_implicit_exists k mu d ((0, 0), 0) hi

end PerronWright.TreeAnalytic

