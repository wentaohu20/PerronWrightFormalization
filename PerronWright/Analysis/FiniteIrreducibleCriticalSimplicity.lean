import PerronWright.Analysis.FiniteIrreducibleCriticalPair
import Mathlib.Analysis.Normed.Ring.Units

/-! Simplicity of the actual perturbed finite eigenvalue and critical pair.
The augmented operator remains a unit by continuity from the proved inverse;
no spectral conclusion is assumed for a perturbed profile. -/

open scoped Topology

noncomputable section

namespace PerronWright.FiniteIrreducibleCriticalPair

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def perturbedOperator (M : FiniteIrreducibleModel S) (τ : C(S, ℂ)) :
    C(S, ℂ) →L[ℂ] C(S, ℂ) :=
  M.complexOperator.comp (ContinuousLinearMap.mul ℂ C(S, ℂ) τ)

@[simp] theorem perturbedOperator_apply (M : FiniteIrreducibleModel S)
    (τ f : C(S, ℂ)) : perturbedOperator M τ f = M.complexOperator (τ * f) := rfl

def eigenAugmented (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) (τ : C(S, ℂ)) :
    C(S, ℂ) →L[ℂ] C(S, ℂ) :=
  eigenvalue M hcrit τ • ContinuousLinearMap.id ℂ C(S, ℂ) - perturbedOperator M τ +
    (M.normalizedPerronFunctional hcrit).smulRight (eigenvector M hcrit τ)

theorem eigenAugmented_apply (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (τ f : C(S, ℂ)) :
    eigenAugmented M hcrit τ f = eigenvalue M hcrit τ • f - perturbedOperator M τ f +
      M.normalizedPerronFunctional hcrit f • eigenvector M hcrit τ := rfl

theorem eigenAugmented_base (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    eigenAugmented M hcrit 1 = 1 - M.complexOperator + M.perronProjection hcrit := by
  ext f a
  simp only [eigenAugmented_apply, eigenvalue_base, eigenvector_base, one_smul,
    perturbedOperator_apply, one_mul, add_apply, sub_apply, one_apply_eq_self,
    FiniteIrreducibleModel.perronProjection_apply]

theorem eigenAugmented_continuousAt (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ContinuousAt (eigenAugmented M hcrit) 1 := by
  have hk : ContinuousAt (perturbedOperator M) 1 :=
    ((ContinuousLinearMap.compL ℂ C(S, ℂ) C(S, ℂ) C(S, ℂ) M.complexOperator).continuous.continuousAt).comp
      (ContinuousLinearMap.mul ℂ C(S, ℂ)).continuous.continuousAt
  have hp : ContinuousAt (fun τ ↦
      (M.normalizedPerronFunctional hcrit).smulRight (eigenvector M hcrit τ)) 1 :=
    ((ContinuousLinearMap.smulRightL ℂ C(S, ℂ) C(S, ℂ)
      (M.normalizedPerronFunctional hcrit)).continuous.continuousAt).comp
        (eigenvector_analytic M hcrit).continuousAt
  exact (((eigenvalue_analytic M hcrit).continuousAt.smul continuousAt_const).sub hk).add hp

theorem eigenAugmented_eventually_isUnit (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∀ᶠ τ in 𝓝 (1 : C(S, ℂ)), IsUnit (eigenAugmented M hcrit τ) := by
  have hb : IsUnit (eigenAugmented M hcrit 1) := by
    rw [eigenAugmented_base]
    exact M.augmented_kernel_isUnit hcrit
  have hnbhd : {A : C(S, ℂ) →L[ℂ] C(S, ℂ) | IsUnit A} ∈
      𝓝 (eigenAugmented M hcrit 1) :=
    (Units.isOpen (R := C(S, ℂ) →L[ℂ] C(S, ℂ))).mem_nhds hb
  exact (eigenAugmented_continuousAt M hcrit).tendsto.eventually hnbhd

theorem perturbed_eigenvalue_simple (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∀ᶠ τ in 𝓝 (1 : C(S, ℂ)),
      eigenvector M hcrit τ ≠ 0 ∧
      ∀ f : C(S, ℂ), perturbedOperator M τ f = eigenvalue M hcrit τ • f ↔
        f = M.normalizedPerronFunctional hcrit f • eigenvector M hcrit τ := by
  filter_upwards [eigenAugmented_eventually_isUnit M hcrit, eigenpair_equations M hcrit]
    with τ hA heq
  have hvec : eigenvector M hcrit τ ≠ 0 := by
    intro hz
    have h := heq.2
    rw [hz, map_zero] at h
    exact zero_ne_one h
  refine ⟨hvec, ?_⟩
  intro f
  constructor
  · intro hf
    have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hA).1
    apply hinj
    have hu : eigenAugmented M hcrit τ (eigenvector M hcrit τ) = eigenvector M hcrit τ := by
      rw [eigenAugmented_apply, perturbedOperator_apply, heq.1, sub_self, zero_add,
        heq.2, one_smul]
    rw [eigenAugmented_apply, hf, sub_self, zero_add, map_smul, hu]
  · intro hf
    rw [hf, map_smul, perturbedOperator_apply, heq.1, smul_smul, smul_smul]
    congr 1
    ring

theorem criticalPair_simple_one (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∀ᶠ g in 𝓝 (0 : C(S, ℂ)),
      eigenvector M hcrit (criticalPair M hcrit g).2 ≠ 0 ∧
      ∀ f : C(S, ℂ), perturbedOperator M (criticalPair M hcrit g).2 f = f ↔
        f = M.normalizedPerronFunctional hcrit f •
          eigenvector M hcrit (criticalPair M hcrit g).2 := by
  have hs := Classical.choose_spec (criticalPair_germ M hcrit)
  rw [← criticalPair] at hs
  have ht : Filter.Tendsto (fun g ↦ (criticalPair M hcrit g).2) (𝓝 0) (𝓝 1) := by
    simpa only [hs.2.1] using hs.1.continuousAt.snd.tendsto
  filter_upwards [ht.eventually (perturbed_eigenvalue_simple M hcrit), hs.2.2.1]
    with g hsimple hg
  simpa only [hg.2, one_smul] using hsimple

/-- The normalized eigenvector stays strictly positive on the real slice.
This uses the actual finite set of atoms, not a primitive-power hypothesis. -/
theorem eigenvector_real_positive (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∀ᶠ τ in 𝓝 (1 : C(S, ℂ)), star τ = τ →
      ∀ a, (eigenvector M hcrit τ a).im = 0 ∧
        0 < (eigenvector M hcrit τ a).re := by
  have hpos : ∀ᶠ τ in 𝓝 (1 : C(S, ℂ)),
      ∀ a, 0 < (eigenvector M hcrit τ a).re := by
    apply Filter.eventually_all.mpr
    intro a
    have hc : ContinuousAt (fun τ ↦ (eigenvector M hcrit τ a).re) 1 :=
      Complex.continuous_re.continuousAt.comp
        (((ContinuousMap.evalCLM ℂ a).continuous.continuousAt).comp
          (eigenvector_analytic M hcrit).continuousAt)
    have hp : 0 < (eigenvector M hcrit 1 a).re := by
      simpa only [eigenvector_base, FiniteIrreducibleModel.complexPerronFunction_apply,
        Complex.ofReal_re] using M.perronFunction_pos hcrit a
    exact hc.tendsto.eventually (Ioi_mem_nhds hp)
  filter_upwards [eigenpair_star M hcrit, hpos] with τ hstar hp
  intro hτ a
  rw [hτ] at hstar
  exact ⟨Complex.conj_eq_iff_im.mp
    (congrArg (fun q : ℂ × C(S, ℂ) ↦ q.2 a) hstar.symm), hp a⟩

theorem criticalPair_positive_simple_one (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ∀ᶠ g in 𝓝 (0 : C(S, ℂ)), star g = g →
      (∀ a, (eigenvector M hcrit (criticalPair M hcrit g).2 a).im = 0 ∧
        0 < (eigenvector M hcrit (criticalPair M hcrit g).2 a).re) ∧
      (∀ f : C(S, ℂ), perturbedOperator M (criticalPair M hcrit g).2 f = f ↔
        f = M.normalizedPerronFunctional hcrit f •
          eigenvector M hcrit (criticalPair M hcrit g).2) := by
  have hs := Classical.choose_spec (criticalPair_germ M hcrit)
  rw [← criticalPair] at hs
  have ht : Filter.Tendsto (fun g ↦ (criticalPair M hcrit g).2) (𝓝 0) (𝓝 1) := by
    simpa only [hs.2.1] using hs.1.continuousAt.snd.tendsto
  filter_upwards [ht.eventually (eigenvector_real_positive M hcrit),
    criticalPair_star M hcrit, criticalPair_simple_one M hcrit] with g hp hstar hsimple
  intro hg
  rw [hg] at hstar
  exact ⟨hp (congrArg Prod.snd hstar.symm), hsimple.2⟩

/-- No higher generalized eigenvectors occur at the analytic eigenvalue.
Thus the proved simplicity is algebraic as well as geometric. -/
theorem perturbed_eigenvalue_power_kernel (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ∀ᶠ τ in 𝓝 (1 : C(S, ℂ)), ∀ n : ℕ, ∀ f : C(S, ℂ),
      ((perturbedOperator M τ - eigenvalue M hcrit τ • 1) ^ n) f = 0 →
        f = M.normalizedPerronFunctional hcrit f • eigenvector M hcrit τ := by
  filter_upwards [eigenAugmented_eventually_isUnit M hcrit, eigenpair_equations M hcrit]
    with τ hA heq
  let B := perturbedOperator M τ - eigenvalue M hcrit τ • 1
  let ell := M.normalizedPerronFunctional hcrit
  let v := eigenvector M hcrit τ
  have hv : eigenAugmented M hcrit τ v = v := by
    rw [eigenAugmented_apply, perturbedOperator_apply, heq.1, sub_self,
      zero_add, heq.2, one_smul]
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hA).1
  have hpre (f : C(S, ℂ)) (c : ℂ) (hf : B f = c • v) : f = ell f • v := by
    have hAf : eigenAugmented M hcrit τ f = (ell f - c) • v := by
      calc
        _ = -B f + ell f • v := by
          rw [eigenAugmented_apply]
          change eigenvalue M hcrit τ • f - perturbedOperator M τ f + ell f • v =
            -(perturbedOperator M τ f - eigenvalue M hcrit τ • f) + ell f • v
          abel
        _ = (ell f - c) • v := by
          rw [hf, sub_smul]
          abel
    have hf' : f = (ell f - c) • v := by
      apply hinj
      rw [hAf, map_smul, hv]
    have hc := congrArg ell hf'
    have hev : ell v = 1 := heq.2
    rw [map_smul, hev, smul_eq_mul, mul_one] at hc
    have hz : c = 0 := by linear_combination hc
    simpa only [hz, sub_zero] using hf'
  intro n
  induction n with
  | zero =>
    intro f hf
    have hz : f = 0 := by simpa only [pow_zero, one_apply_eq_self] using hf
    simp only [hz, map_zero, zero_smul]
  | succ n ih =>
    intro f hf
    have hb : (B ^ n) (B f) = 0 := by
      simpa only [pow_succ, mul_apply_eq_comp] using hf
    exact hpre f (ell (B f)) (ih (B f) hb)

theorem criticalPair_power_kernel_one (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    ∀ᶠ g in 𝓝 (0 : C(S, ℂ)), ∀ n : ℕ, ∀ f : C(S, ℂ),
      ((perturbedOperator M (criticalPair M hcrit g).2 - 1) ^ n) f = 0 →
        f = M.normalizedPerronFunctional hcrit f •
          eigenvector M hcrit (criticalPair M hcrit g).2 := by
  have hs := Classical.choose_spec (criticalPair_germ M hcrit)
  rw [← criticalPair] at hs
  have ht : Filter.Tendsto (fun g ↦ (criticalPair M hcrit g).2) (𝓝 0) (𝓝 1) := by
    simpa only [hs.2.1] using hs.1.continuousAt.snd.tendsto
  filter_upwards [ht.eventually (perturbed_eigenvalue_power_kernel M hcrit), hs.2.2.1]
    with g hk hg
  simpa only [hg.2, one_smul] using hk

end PerronWright.FiniteIrreducibleCriticalPair
