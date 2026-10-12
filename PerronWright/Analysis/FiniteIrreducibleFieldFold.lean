import PerronWright.Analysis.FiniteIrreducibleComplexFold
import PerronWright.Analysis.FiniteIrreducibleRadiusResponse

/-! Centering the genuine finite fold curve at the actual analytic critical field. -/

open MeasureTheory PerronWright
open scoped Topology ContDiff

noncomputable section

namespace PerronWright.FiniteIrreducibleFieldFold

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

theorem foldResidual_fderiv_apply (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (v : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ))) :
    fderiv ℂ (M.foldResidual hcrit) ((0, 0), (1, 1)) v =
      (v.2.2 - M.complexOperator v.2.2 -
        v.2.1 • (1 : C(S, ℂ)) - v.1.1,
        M.normalizedPerronFunctional hcrit v.2.2 - v.1.2) := by
  let K := M.complexOperator
  let d := TreeCritical.degree M.bjrModel
  let ell := M.normalizedPerronFunctional hcrit
  let a : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) := ((0, 0), (1, 1))
  have hz : HasFDerivAt (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦ p.2.1)
      ((ContinuousLinearMap.fst ℂ ℂ C(S, ℂ)).comp
        (ContinuousLinearMap.snd ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ)))) a :=
    (hasFDerivAt_fst (𝕜 := ℂ) (p := a.2)).comp a
      (hasFDerivAt_snd (𝕜 := ℂ) (p := a))
  have hg : HasFDerivAt (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦ p.1.1)
      ((ContinuousLinearMap.fst ℂ C(S, ℂ) ℂ).comp
        (ContinuousLinearMap.fst ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ)))) a :=
    (hasFDerivAt_fst (𝕜 := ℂ) (p := a.1)).comp a
      (hasFDerivAt_fst (𝕜 := ℂ) (p := a))
  have ht : HasFDerivAt (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦ p.1.2)
      ((ContinuousLinearMap.snd ℂ C(S, ℂ) ℂ).comp
        (ContinuousLinearMap.fst ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ)))) a :=
    (hasFDerivAt_snd (𝕜 := ℂ) (p := a.1)).comp a
      (hasFDerivAt_fst (𝕜 := ℂ) (p := a))
  have hU : HasFDerivAt (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦ p.2.2)
      ((ContinuousLinearMap.snd ℂ ℂ C(S, ℂ)).comp
        (ContinuousLinearMap.snd ℂ (C(S, ℂ) × ℂ) (ℂ × C(S, ℂ)))) a :=
    (hasFDerivAt_snd (𝕜 := ℂ) (p := a.2)).comp a
      (hasFDerivAt_snd (𝕜 := ℂ) (p := a))
  have hinner := (hg.sub_const d).add (K.hasFDerivAt.comp a hU)
  have hexp := (hasFDerivAt_exp (𝕂 := ℂ) (x := (0 : C(S, ℂ)) - d + K 1)).comp a hinner
  have hfirst := hU.sub (hz.smul hexp)
  have hsecond := ((ell.hasFDerivAt.comp a hU).sub_const (ell 1)).sub ht
  have heq : M.foldResidual hcrit =
      (fun p : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) ↦
        (p.2.2 - p.2.1 • NormedSpace.exp (p.1.1 - d + K p.2.2),
          ell p.2.2 - ell 1 - p.1.2)) := rfl
  have hres := (hfirst.prodMk hsecond).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun p ↦ congrFun heq p))
  rw [hres.fderiv]
  simp only [a, d, K, ell, TreeCritical.degree, FiniteIrreducibleModel.complexOperator,
    FiniteIrreducibleModel.bjrModel, Function.comp_apply, Pi.add_apply,
    zero_sub, neg_add_cancel,
    NormedSpace.exp_zero, one_smul, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, add_apply]
  apply Prod.ext
  · change v.2.2 - (v.1.1 + M.complexOperator v.2.2 +
        v.2.1 • (1 : C(S, ℂ))) =
      v.2.2 - M.complexOperator v.2.2 - v.2.1 • (1 : C(S, ℂ)) - v.1.1
    abel
  · abel

def foldCurve (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    C(S, ℂ) × ℂ → ℂ × C(S, ℂ) :=
  Classical.choose (M.foldCurve_germ hcrit)

theorem foldCurve_analytic (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    AnalyticAt ℂ (foldCurve M hcrit) (0, 0) :=
  (Classical.choose_spec (M.foldCurve_germ hcrit)).1

theorem foldCurve_base (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    foldCurve M hcrit (0, 0) = (1, 1) :=
  (Classical.choose_spec (M.foldCurve_germ hcrit)).2.1

theorem foldCurve_equations (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∀ᶠ q in 𝓝 ((0, 0) : C(S, ℂ) × ℂ),
      M.treeResidual (((foldCurve M hcrit q).1, q.1), (foldCurve M hcrit q).2) = 0 ∧
      M.normalizedPerronFunctional hcrit ((foldCurve M hcrit q).2 - 1) = q.2 :=
  (Classical.choose_spec (M.foldCurve_germ hcrit)).2.2.1

theorem foldCurve_tangent (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    (fderiv ℂ (foldCurve M hcrit) (0, 0)) (0, 1) =
      (0, M.complexPerronFunction hcrit) := by
  let ψ := foldCurve M hcrit
  let q₀ : C(S, ℂ) × ℂ := (0, 0)
  let a : (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) := (q₀, (1, 1))
  have hψ := foldCurve_analytic M hcrit
  have hψ0 := foldCurve_base M hcrit
  have heq : (fun q ↦ M.foldResidual hcrit (q, ψ q)) =ᶠ[𝓝 q₀]
      (fun _ ↦ ((0, 0) : C(S, ℂ) × ℂ)) := by
    filter_upwards [foldCurve_equations M hcrit] with q hq
    apply Prod.ext
    · exact hq.1
    · change M.normalizedPerronFunctional hcrit (ψ q).2 -
        M.normalizedPerronFunctional hcrit 1 - q.2 = 0
      rw [← map_sub, hq.2]
      ring
  have hD : fderiv ℂ (fun q ↦ M.foldResidual hcrit (q, ψ q)) q₀ = 0 := by
    have h := heq.fderiv_eq (𝕜 := ℂ)
    simpa using h
  have hj := (hasFDerivAt_id q₀).prodMk hψ.hasStrictFDerivAt.hasFDerivAt
  have ha : (q₀, ψ q₀) = a := by
    exact congrArg (fun t : ℂ × C(S, ℂ) ↦ (q₀, t)) hψ0
  have houter : HasFDerivAt (M.foldResidual hcrit)
      (fderiv ℂ (M.foldResidual hcrit) a) (q₀, ψ q₀) := by
    rw [ha]
    exact (M.foldResidual_analytic hcrit).hasStrictFDerivAt.hasFDerivAt
  have hcomp : HasFDerivAt (fun q ↦ M.foldResidual hcrit (q, ψ q))
      ((fderiv ℂ (M.foldResidual hcrit) a) ∘L
        ((ContinuousLinearMap.id ℂ (C(S, ℂ) × ℂ)).prod
          (fderiv ℂ ψ q₀))) q₀ := by
    simpa only [Function.comp_def, id_eq] using (houter.comp q₀ hj)
  have hzero := congrArg (fun L : (C(S, ℂ) × ℂ) →L[ℂ] (C(S, ℂ) × ℂ) ↦ L (0, 1))
    (hcomp.fderiv.symm.trans hD)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply] at hzero
  let v := (fderiv ℂ ψ q₀) (0, 1)
  have hv : M.foldBaseDerivative hcrit v = ((0 : C(S, ℂ)), 1) := by
    have hf := foldResidual_fderiv_apply M hcrit ((0, 1), v)
    rw [hf] at hzero
    rw [M.foldBaseDerivative_apply]
    apply Prod.ext
    · change v.2 - M.complexOperator v.2 - v.1 • (1 : C(S, ℂ)) = 0
      have hs := congrArg Prod.fst hzero
      simpa using hs
    · change M.normalizedPerronFunctional hcrit v.2 = 1
      have hs := congrArg Prod.snd hzero
      simpa only [Prod.fst, Prod.snd] using sub_eq_zero.mp hs
  have htarget : M.foldBaseDerivative hcrit (0, M.complexPerronFunction hcrit) =
      ((0 : C(S, ℂ)), 1) := by
    rw [M.foldBaseDerivative_apply, M.normalizedPerronFunctional_perronFunction]
    simp only [M.complexPerronFunction_fixed hcrit, sub_self, zero_smul]
  exact (M.foldBaseDerivative_injective hcrit (hv.trans htarget.symm))

/-- The coordinate of the actual critical profile on the analytic fold curve. -/
def criticalCoordinate (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (g : C(S, ℂ)) : ℂ :=
  M.normalizedPerronFunctional hcrit (FiniteIrreducibleRadiusResponse.profile M hcrit g - 1)

theorem criticalCoordinate_analytic (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    AnalyticAt ℂ (criticalCoordinate M hcrit) 0 := by
  unfold criticalCoordinate
  exact (M.normalizedPerronFunctional hcrit).analyticAt _ |>.comp
    ((FiniteIrreducibleRadiusResponse.profile_analytic M hcrit).sub analyticAt_const)

theorem criticalCoordinate_base (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    criticalCoordinate M hcrit 0 = 0 := by
  simp only [criticalCoordinate, FiniteIrreducibleRadiusResponse.profile_base, sub_self, map_zero]

theorem criticalPair_on_foldCurve (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∀ᶠ g in 𝓝 (0 : C(S, ℂ)),
      foldCurve M hcrit (g, criticalCoordinate M hcrit g) = FiniteIrreducibleCriticalPair.criticalPair M hcrit g := by
  have hcp := Classical.choose_spec (FiniteIrreducibleCriticalPair.criticalPair_germ M hcrit)
  rw [← FiniteIrreducibleCriticalPair.criticalPair] at hcp
  have hfold := (Classical.choose_spec (M.foldCurve_germ hcrit)).2.2.2
  rw [← foldCurve] at hfold
  let j : C(S, ℂ) → (C(S, ℂ) × ℂ) × (ℂ × C(S, ℂ)) :=
    fun g ↦ ((g, criticalCoordinate M hcrit g), FiniteIrreducibleCriticalPair.criticalPair M hcrit g)
  have hj : Filter.Tendsto j (𝓝 0) (𝓝 ((0, 0), (1, 1))) := by
    have hleft : Filter.Tendsto (fun g : C(S, ℂ) ↦ (g, criticalCoordinate M hcrit g))
        (𝓝 0) (𝓝 (0, 0)) := by
      simpa only [id_eq, criticalCoordinate_base] using
        (continuousAt_id.tendsto.prodMk_nhds
          (criticalCoordinate_analytic M hcrit).continuousAt.tendsto)
    have hright : Filter.Tendsto (FiniteIrreducibleCriticalPair.criticalPair M hcrit)
        (𝓝 0) (𝓝 (1, 1)) := by
      simpa only [hcp.2.1] using hcp.1.continuousAt.tendsto
    exact hleft.prodMk_nhds hright
  filter_upwards [hcp.2.2.1, hj.eventually hfold] with g heq hu
  apply hu.mp
  apply Prod.ext
  · exact sub_eq_zero.mpr heq.1
  · change M.normalizedPerronFunctional hcrit (FiniteIrreducibleRadiusResponse.profile M hcrit g) -
      M.normalizedPerronFunctional hcrit 1 - criticalCoordinate M hcrit g = 0
    rw [criticalCoordinate, ← map_sub]
    ring

def centeredFoldCurve (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (q : C(S, ℂ) × ℂ) : ℂ × C(S, ℂ) :=
  foldCurve M hcrit (q.1, criticalCoordinate M hcrit q.1 + q.2)

theorem centeredFoldCurve_analytic (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    AnalyticAt ℂ (centeredFoldCurve M hcrit) (0, 0) := by
  have hfst : AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦ q.1)
      ((0, 0) : C(S, ℂ) × ℂ) := analyticAt_fst
  have hsnd : AnalyticAt ℂ (fun q : C(S, ℂ) × ℂ ↦ q.2)
      ((0, 0) : C(S, ℂ) × ℂ) := analyticAt_snd
  have hcoord : AnalyticAt ℂ
      (fun q : C(S, ℂ) × ℂ ↦ criticalCoordinate M hcrit q.1) (0, 0) :=
    (criticalCoordinate_analytic M hcrit).comp_of_eq hfst rfl
  have harg : AnalyticAt ℂ
      (fun q : C(S, ℂ) × ℂ ↦ (q.1, criticalCoordinate M hcrit q.1 + q.2)) (0, 0) :=
    hfst.prod (hcoord.add hsnd)
  unfold centeredFoldCurve
  exact (foldCurve_analytic M hcrit).comp_of_eq harg (by
    simp only [criticalCoordinate_base, zero_add])

theorem centeredFoldCurve_critical (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∀ᶠ g in 𝓝 (0 : C(S, ℂ)),
      centeredFoldCurve M hcrit (g, 0) = FiniteIrreducibleCriticalPair.criticalPair M hcrit g := by
  filter_upwards [criticalPair_on_foldCurve M hcrit] with g hg
  simpa only [centeredFoldCurve, add_zero] using hg

end PerronWright.FiniteIrreducibleFieldFold

