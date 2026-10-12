import PerronWright.Analysis.FiniteIrreducibleFieldNormalization
import PerronWright.Analysis.FiniteIrreducibleCriticalPerron
import PerronWright.Analysis.FiniteIrreducibleRadiusResponse

/-! The constructed real critical pair defines an actual critical tilted
finite model. All positivity, fixed-vector and spectral assertions below
are obtained from the proved analytic critical pair. -/

open Filter Topology
open scoped BigOperators
noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def realPartMap (f : C(S, ℂ)) : C(S, ℝ) :=
  ⟨fun a ↦ (f a).re, continuous_of_discreteTopology⟩

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [BorelSpace S] in
theorem complexify_realPartMap (f : C(S, ℂ)) (hf : ∀ a, (f a).im = 0) :
    TreeRealComplexBridge.complexify (realPartMap f) = f := by
  ext a
  apply Complex.ext
  · rfl
  · simpa only [TreeRealComplexBridge.complexify_apply, Complex.ofReal_im] using (hf a).symm

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [BorelSpace S] in
theorem complexify_realPartMap_of_star (f : C(S, ℂ)) (hf : star f = f) :
    TreeRealComplexBridge.complexify (realPartMap f) = f := by
  apply complexify_realPartMap
  intro a
  apply Complex.conj_eq_iff_im.mp
  exact congrArg (fun f : C(S, ℂ) ↦ f a) hf

theorem complexify_fieldTreeMap (M : FiniteIrreducibleModel S)
    (z : ℝ) (g V : C(S, ℝ)) :
    TreeRealComplexBridge.complexify (M.fieldTreeMap z g V) =
      (z : ℂ) • NormedSpace.exp (TreeRealComplexBridge.complexify g -
        TreeCritical.degree M.bjrModel + M.complexOperator (TreeRealComplexBridge.complexify V)) := by
  ext a
  have hexp (f : C(S, ℂ)) : NormedSpace.exp f a = Complex.exp (f a) := by
    simpa only [ContinuousMap.evalAlgHom_apply, ← Complex.exp_eq_exp_ℂ] using
      NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ a)
        (ContinuousMap.evalCLM ℂ a).continuous f
  have harg : (TreeRealComplexBridge.complexify g -
      TreeCritical.degree M.bjrModel + M.complexOperator (TreeRealComplexBridge.complexify V)) a =
      ((g a - M.action 1 a + M.action V a : ℝ) : ℂ) := by
    change (g a : ℂ) - M.complexOperator 1 a +
      M.complexOperator (TreeRealComplexBridge.complexify V) a = _
    simp only [complexOperator_apply, ContinuousMap.one_apply,
      TreeRealComplexBridge.complexify_apply, action, Pi.one_apply, mul_one,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [TreeRealComplexBridge.complexify_apply, fieldTreeMap_apply,
    ContinuousMap.smul_apply, smul_eq_mul, hexp, harg, Complex.ofReal_mul, Complex.ofReal_exp]

def realCriticalProfile (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (g : C(S, ℂ)) : C(S, ℝ) :=
  realPartMap (FiniteIrreducibleRadiusResponse.profile M hcrit g)

/-- On a genuine real-field neighbourhood, the actual profile is a positive
fixed point and the normalized tilted model has literal matrix radius one. -/
theorem real_critical_tilt_eventually (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0, star g = g →
      ∃ hτ : ∀ a, 0 < realCriticalProfile M hcrit g a,
        0 < (FiniteIrreducibleRadiusResponse.radius M hcrit g).re ∧
        (FiniteIrreducibleRadiusResponse.radius M hcrit g).im = 0 ∧
        TreeRealComplexBridge.complexify (realCriticalProfile M hcrit g) =
          FiniteIrreducibleRadiusResponse.profile M hcrit g ∧
        M.fieldTreeMap (FiniteIrreducibleRadiusResponse.radius M hcrit g).re
          (realPartMap g) (realCriticalProfile M hcrit g) = realCriticalProfile M hcrit g ∧
        (M.tilted (realCriticalProfile M hcrit g) hτ).IsCritical := by
  have hs := Classical.choose_spec (FiniteIrreducibleCriticalPair.criticalPair_germ M hcrit)
  rw [← FiniteIrreducibleCriticalPair.criticalPair] at hs
  have ht : Tendsto (fun g ↦ (FiniteIrreducibleCriticalPair.criticalPair M hcrit g).2)
      (𝓝 0) (𝓝 1) := by
    simpa only [hs.2.1] using hs.1.continuousAt.snd.tendsto
  filter_upwards [FiniteIrreducibleCriticalPair.criticalPair_real_positive M hcrit,
    FiniteIrreducibleCriticalPair.criticalPair_positive_simple_one M hcrit,
    ht.eventually (FiniteIrreducibleCriticalPair.eigenpair_equations M hcrit),
    hs.2.2.1] with g hpos hu he hg
  intro hreal
  have hp := hpos hreal
  have hτ : ∀ a, 0 < realCriticalProfile M hcrit g a := fun a ↦ (hp.2.2 a).2
  have hτc : TreeRealComplexBridge.complexify (realCriticalProfile M hcrit g) =
      FiniteIrreducibleRadiusResponse.profile M hcrit g :=
    complexify_realPartMap _ (fun a ↦ (hp.2.2 a).1)
  have hρc : ((FiniteIrreducibleRadiusResponse.radius M hcrit g).re : ℂ) =
      FiniteIrreducibleRadiusResponse.radius M hcrit g := by
    apply Complex.ext
    · rfl
    · change 0 = (FiniteIrreducibleCriticalPair.criticalPair M hcrit g).1.im
      exact hp.1.symm
  have hfix : M.fieldTreeMap (FiniteIrreducibleRadiusResponse.radius M hcrit g).re
      (realPartMap g) (realCriticalProfile M hcrit g) = realCriticalProfile M hcrit g := by
    have hc : TreeRealComplexBridge.complexify
        (M.fieldTreeMap (FiniteIrreducibleRadiusResponse.radius M hcrit g).re
          (realPartMap g) (realCriticalProfile M hcrit g)) =
        TreeRealComplexBridge.complexify (realCriticalProfile M hcrit g) := by
      rw [complexify_fieldTreeMap, hτc, complexify_realPartMap_of_star g hreal, hρc]
      exact hg.1.symm
    ext a
    exact congrArg (fun f : C(S, ℂ) ↦ (f a).re) hc
  let u : S → ℝ := fun a ↦
    (FiniteIrreducibleCriticalPair.eigenvector M hcrit
      (FiniteIrreducibleCriticalPair.criticalPair M hcrit g).2 a).re
  have hup : ∀ a, 0 < u a := fun a ↦ ((hu hreal).1 a).2
  have hufix : M.action ((realCriticalProfile M hcrit g : S → ℝ) * u) = u := by
    have heq := he.1
    rw [hg.2, one_smul] at heq
    funext a
    change M.action (fun b ↦
      ((FiniteIrreducibleCriticalPair.criticalPair M hcrit g).2 b).re *
        (FiniteIrreducibleCriticalPair.eigenvector M hcrit
          (FiniteIrreducibleCriticalPair.criticalPair M hcrit g).2 b).re) a =
      (FiniteIrreducibleCriticalPair.eigenvector M hcrit
        (FiniteIrreducibleCriticalPair.criticalPair M hcrit g).2 a).re
    have hx := congrArg (fun f : C(S, ℂ) ↦ (f a).re) heq
    rw [M.complexOperator_re] at hx
    simpa only [ContinuousMap.mul_apply, Complex.mul_re,
      (show ((FiniteIrreducibleCriticalPair.criticalPair M hcrit g).2 _).im = 0 from
        (hp.2.2 _).1), zero_mul, sub_zero] using hx
  exact ⟨hτ, hp.2.1, hp.1, hτc, hfix,
    M.tilted_isCritical_of_positive_fixed _ hτ u hup hufix⟩

end PerronWright.FiniteIrreducibleModel
