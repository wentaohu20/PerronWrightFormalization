import PerronWright.Probability.FreshTypePerronCentering
import PerronWright.Probability.EmpiricalMarkWeakConcentration
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Continuous functions of the genuine pooled empirical mark

The raw fresh-exposure moments are continuous functionals of an actual
`ProbabilityMeasure`, through its literal independent finite products.
Their concentration is derived from genuine weak-mark concentration.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedProfileFunctionalContinuous

open EmpiricalMarkConcentration EmpiricalMarkWeakConcentration
  EmpiricalTypeMarks ProfileFiniteCollection ProjectiveFiniteCollection
  FreshTypeAveraging FreshTypeCumulantExpansion FreshTypePerronCentering

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def linearFunctional (f : C(S,ℝ)) (ν : ProbabilityMeasure S) : ℝ := ∫ x, f x ∂(ν:Measure S)

theorem linearFunctional_continuous (f : C(S,ℝ)) : Continuous (linearFunctional f) :=
  ProbabilityMeasure.continuous_integral_continuousMap f

def pairFunctional (H : C(S × S,ℝ)) (ν : ProbabilityMeasure S) : ℝ :=
  ∫ z, H z ∂(ν:Measure S).prod (ν:Measure S)

theorem pairFunctional_continuous (H : C(S × S,ℝ)) : Continuous (pairFunctional H) := by
  exact (ProbabilityMeasure.continuous_integral_continuousMap H).comp
    (ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id))

def exposureProfile (M : CompactBJRModel S) (ν : ProbabilityMeasure S) (y : S) : ℝ :=
  ∫ x, M.kernel x y ∂(ν:Measure S)

def exposureMomentKernel (M : CompactBJRModel S) (j : ℕ) : C((Fin j → S),ℝ) where
  toFun x := ∫ y, ∏ i : Fin j, M.kernel (x i) y ∂M.mu
  continuous_toFun := by
    have hf : Continuous (fun p : (Fin j → S) × S ↦ ∏ i : Fin j, M.kernel (p.1 i) p.2) := by
      apply continuous_finsetProd
      intro i _
      exact M.kernel.toContinuousMap.continuous.comp
        (((continuous_apply i).comp continuous_fst).prodMk continuous_snd)
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous (μ := M.mu) hf isCompact_univ

def exposureMomentFunctional (M : CompactBJRModel S) (j : ℕ) (ν : ProbabilityMeasure S) : ℝ :=
  ∫ x : Fin j → S, exposureMomentKernel M j x ∂Measure.pi (fun _ ↦ (ν:Measure S))

theorem exposureMomentFunctional_continuous (M : CompactBJRModel S) (j : ℕ) :
    Continuous (exposureMomentFunctional M j) := by
  exact (ProbabilityMeasure.continuous_integral_continuousMap (exposureMomentKernel M j)).comp
    (ProbabilityMeasure.continuous_pi.comp (continuous_pi (fun _ ↦ continuous_id)))

/-- Literal Fubini/product calculation of the moment functional. -/
theorem exposureMomentFunctional_eq_power_integral (M : CompactBJRModel S) (j : ℕ)
    (ν : ProbabilityMeasure S) :
    exposureMomentFunctional M j ν = ∫ y, exposureProfile M ν y ^ j ∂M.mu := by
  have hi : Integrable (fun p : (Fin j → S) × S ↦ ∏ i : Fin j, M.kernel (p.1 i) p.2)
      ((Measure.pi (fun _ : Fin j ↦ (ν:Measure S))).prod M.mu) := by
    apply Continuous.integrable_of_hasCompactSupport _ isClosed_closure.isCompact
    apply continuous_finsetProd
    intro i _
    exact M.kernel.toContinuousMap.continuous.comp
      (((continuous_apply i).comp continuous_fst).prodMk continuous_snd)
  unfold exposureMomentFunctional exposureMomentKernel
  change (∫ x : Fin j → S, ∫ y, ∏ i : Fin j, M.kernel (x i) y ∂M.mu
    ∂Measure.pi (fun _ ↦ (ν:Measure S))) = _
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [integral_fintype_prod_eq_prod (fun _ : Fin j ↦ fun x : S ↦ M.kernel x y)]
  simp only [exposureProfile,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

def degreeFunctional (M : CompactBJRModel S) := linearFunctional M.degreeFunction
def kernelPairFunctional (M : CompactBJRModel S) := pairFunctional M.kernel.toContinuousMap
def varianceFunctional (M : CompactBJRModel S) (ν : ProbabilityMeasure S) : ℝ :=
  exposureMomentFunctional M 2 ν - degreeFunctional M ν ^ 2
def thirdCumulantFunctional (M : CompactBJRModel S) (ν : ProbabilityMeasure S) : ℝ :=
  exposureMomentFunctional M 3 ν - 3 * degreeFunctional M ν * exposureMomentFunctional M 2 ν +
    2 * degreeFunctional M ν ^ 3

theorem degreeFunctional_continuous (M : CompactBJRModel S) : Continuous (degreeFunctional M) :=
  linearFunctional_continuous _
theorem kernelPairFunctional_continuous (M : CompactBJRModel S) : Continuous (kernelPairFunctional M) :=
  pairFunctional_continuous _
theorem varianceFunctional_continuous (M : CompactBJRModel S) : Continuous (varianceFunctional M) :=
  (exposureMomentFunctional_continuous M 2).sub ((degreeFunctional_continuous M).pow 2)
theorem thirdCumulantFunctional_continuous (M : CompactBJRModel S) : Continuous (thirdCumulantFunctional M) := by
  exact ((exposureMomentFunctional_continuous M 3).sub
    ((continuous_const.mul (degreeFunctional_continuous M)).mul (exposureMomentFunctional_continuous M 2))).add
      (continuous_const.mul ((degreeFunctional_continuous M).pow 3))

/-- Every actual continuous profile functional concentrates at its Perron
value, directly from the already proved weak-neighbourhood concentration. -/
theorem pooled_continuousFunctional_probability_tendsto_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (R q : ℕ) (hq : 0 < q) (L : ℝ) (hL : 0 ≤ L)
    (k r : ℕ → Fin q → ℕ) (hk : ∀ n i, 0 < k n i)
    (g : ℕ → Fin q → C(S,ℝ))
    (hC : ∀ n i, 0 < M.fieldConnectedWeight (g n i) (k n i) (r n i))
    (hKTop : Tendsto (fun n ↦ ∑ i, (k n i : ℝ)) atTop atTop)
    (hr : ∀ᶠ n in atTop, ∀ i, r n i ≤ R)
    (hg : ∀ᶠ n in atTop, ∀ i, Real.sqrt (k n i : ℝ) * ‖g n i‖ ≤ L)
    (F : ProbabilityMeasure S → ℝ) (hF : Continuous F) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (productLaw M (k n) (r n) (g n) (hC n)).real
      {p | ε ≤ |F (pooledMark hq (k n) (hk n) p) - F (perronMark M hM)|}) atTop (𝓝 0) := by
  let U := {ν : ProbabilityMeasure S | |F ν - F (perronMark M hM)| < ε}
  have hU : U ∈ 𝓝 (perronMark M hM) := by
    apply (isOpen_lt (hF.sub continuous_const |>.abs) continuous_const).mem_nhds
    change |F (perronMark M hM) - F (perronMark M hM)| < ε
    simpa only [sub_self,abs_zero] using hε
  have h := pooledMark_probability_outside_weak_nhds_tendsto_zero
    M hM R q hq L hL k r hk g hC hKTop hr hg U hU
  simpa only [U,Set.mem_ofPred_eq,not_lt] using h

theorem exposureProfile_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) (y : S) :
    exposureProfile M (perronMark M hM) y = M.perronFunction hM y := by
  have h := perronLaw_row_integral_eq_action M hM M.kernel.toContinuousMap y
  rw [KernelMap.action_toContinuousMap,M.perronFunction_fixed hM] at h
  unfold exposureProfile
  change (∫ x, M.kernel x y ∂M.perronLaw hM) = _
  exact (integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ M.kernel.symmetric x y))).trans h

theorem exposureMomentFunctional_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) (j : ℕ) :
    exposureMomentFunctional M j (perronMark M hM) = ∫ y, M.perronFunction hM y ^ j ∂M.mu := by
  rw [exposureMomentFunctional_eq_power_integral]
  simp_rw [exposureProfile_perronMark]

theorem exposureMomentFunctional_two_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    exposureMomentFunctional M 2 (perronMark M hM) = M.alpha hM :=
  exposureMomentFunctional_perronMark M hM 2

theorem exposureMomentFunctional_three_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    exposureMomentFunctional M 3 (perronMark M hM) = M.beta hM :=
  exposureMomentFunctional_perronMark M hM 3

theorem degreeFunctional_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    degreeFunctional M (perronMark M hM) = 1 := perronLaw_degreeFunction_integral M hM

theorem kernelPairFunctional_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    kernelPairFunctional M (perronMark M hM) = M.alpha hM := by
  have hi : Integrable (fun z ↦ M.kernel.toContinuousMap z) ((M.perronLaw hM).prod (M.perronLaw hM)) :=
    M.kernel.toContinuousMap.continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact
  unfold kernelPairFunctional pairFunctional
  change (∫ z, M.kernel.toContinuousMap z ∂(M.perronLaw hM).prod (M.perronLaw hM)) = _
  rw [integral_prod _ hi]
  have hrow (x : S) : (∫ y, M.kernel x y ∂M.perronLaw hM) = M.perronFunction hM x := by
    have h := perronLaw_row_integral_eq_action M hM M.kernel.toContinuousMap x
    rw [KernelMap.action_toContinuousMap,M.perronFunction_fixed hM] at h
    exact h
  change (∫ x, (∫ y, M.kernel x y ∂M.perronLaw hM) ∂M.perronLaw hM) = _
  simp_rw [hrow]
  rw [M.perronLaw_integral hM (M.perronFunction hM)]
  unfold CompactBJRModel.alpha
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ (pow_two _).symm)

theorem varianceFunctional_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    varianceFunctional M (perronMark M hM) = M.alpha hM - 1 := by
  simp only [varianceFunctional,exposureMomentFunctional_two_perronMark,degreeFunctional_perronMark,one_pow]

theorem thirdCumulantFunctional_perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    thirdCumulantFunctional M (perronMark M hM) = M.beta hM - 3 * M.alpha hM + 2 := by
  simp only [thirdCumulantFunctional,exposureMomentFunctional_two_perronMark,
    exposureMomentFunctional_three_perronMark,degreeFunctional_perronMark,one_pow,mul_one]

end PerronWright.AnnealedProfileFunctionalContinuous
