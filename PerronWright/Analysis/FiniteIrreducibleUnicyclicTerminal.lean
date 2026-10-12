import PerronWright.Analysis.FiniteIrreducibleUnicyclicPerronWrightFormula
import PerronWright.Analysis.FiniteIrreduciblePhysicalScalarRadius

/-!
# The literal finite irreducible unicyclic Perron--Wright terminal

The weights below are the actual labelled simple connected graph weights at
surplus one. Their radius is the constructed critical radius of the literal
field-rooted tree series. No primitivity or two-step positivity is required.
The Wright constant is derived from the exact simple-cycle logarithmic
coefficient and is displayed as `sqrt (pi / 8)`.
-/

open Filter Topology Asymptotics
open scoped Topology Real

noncomputable section

namespace PerronWright.FiniteIrreducibleUnicyclicTerminal

namespace PW
export PerronWright.FiniteIrreducibleUnicyclicPerronWrightFormula
  (physicalUnicyclicRadiusMainTerm physicalUnicyclicGaussianMainTerm
   physicalUnicyclicRadiusMainTerm_eq_exp_rpow
   physicalUnicyclicGaussianMainTerm_eq_exp_rpow
   exists_unicyclicPerronWright_radius_relative_bound_uniform_eta
   exists_unicyclicPerronWright_gaussian_relative_bound)
end PW

namespace Radius
export PerronWright.FiniteIrreducibleCriticalWindowRadiusConversion
  (realScalarRadius criticalQuadraticRate)
end Radius

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- The surplus-one Wright constant in its classical closed form. -/
theorem unicyclicWrightConstant_eq_sqrt_pi_div_eight :
    UnicyclicPerronWrightFormula.unicyclicWrightConstant =
      Real.sqrt (Real.pi / 8) := by
  unfold UnicyclicPerronWrightFormula.unicyclicWrightConstant
  have h₁ := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have h₂ := Real.sq_sqrt (show 0 ≤ Real.pi / 8 by positivity)
  have h₃ := Real.sqrt_nonneg (2 * Real.pi)
  have h₄ := Real.sqrt_nonneg (Real.pi / 8)
  nlinarith

/-- The paper's radius main term at surplus one, with the genuine scalar
rooted-tree convergence radius. -/
def unicyclicRadiusMain (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (k : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (Real.pi / 8) * (Radius.realScalarRadius M hM t)⁻¹ ^ k *
    Real.exp (-(k : ℝ)) * (k : ℝ) ^ ((k : ℝ) - 1 / 2)

/-- The paper's Gaussian main term at surplus one. -/
def unicyclicGaussianMain (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (k : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (Real.pi / 8) * Real.exp (-(k : ℝ)) *
    Real.exp (-(M.alpha hM ^ 2 / (2 * M.beta hM)) *
      (k : ℝ) * (t - 1) ^ 2) *
    (k : ℝ) ^ ((k : ℝ) - 1 / 2)

theorem unicyclicRadiusMain_eq (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {k : ℕ} (hk : 0 < k) (t : ℝ) :
    unicyclicRadiusMain M hM k t = PW.physicalUnicyclicRadiusMainTerm M hM k t := by
  rw [PW.physicalUnicyclicRadiusMainTerm_eq_exp_rpow M hM hk t,
    unicyclicWrightConstant_eq_sqrt_pi_div_eight]
  rfl

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem unicyclicGaussianMain_eq (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {k : ℕ} (hk : 0 < k) (t : ℝ) :
    unicyclicGaussianMain M hM k t =
      PW.physicalUnicyclicGaussianMainTerm M hM k t := by
  unfold unicyclicGaussianMain PW.physicalUnicyclicGaussianMainTerm
  rw [UnicyclicPerronWrightFormula.unicyclicPerronWrightMainTerm_eq_exp_rpow hk,
    unicyclicWrightConstant_eq_sqrt_pi_div_eight]
  unfold Radius.criticalQuadraticRate
  ring

/-- The genuine simple connected unicyclic weight satisfies the literal
radius formula on every shrinking scalar window. The error constant is
chosen before the window sequence. Monotonicity of the sequence is not needed. -/
theorem exists_connectedWeight_unicyclic_radius_relative_bound_uniform_eta
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (𝓝 0) →
      ∀ᶠ k : ℕ in atTop, ∀ t : ℝ, |t - 1| ≤ eta k →
        |M.bjrModel.connectedWeight t k 1 /
            unicyclicRadiusMain M hM k t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, hbound⟩ :=
    PW.exists_unicyclicPerronWright_radius_relative_bound_uniform_eta M hM
  refine ⟨K, hK, ?_⟩
  intro eta heta hlim
  filter_upwards [hbound eta heta hlim, eventually_ge_atTop (1 : ℕ)]
    with k hk hkone
  intro t ht
  rw [unicyclicRadiusMain_eq M hM (Nat.zero_lt_one.trans_le hkone)]
  exact hk t ht

/-- Uniform critical-window Gaussian asymptotics of the actual surplus-one
connected weight, in the original paper normalization. -/
theorem exists_connectedWeight_unicyclic_gaussian_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop, ∀ t : ℝ,
      Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        |M.bjrModel.connectedWeight t k 1 /
            unicyclicGaussianMain M hM k t - 1| ≤
          K / Real.sqrt (k : ℝ) := by
  obtain ⟨K, hK, hbound⟩ :=
    PW.exists_unicyclicPerronWright_gaussian_relative_bound M hM L hL
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)]
    with k hk hkone
  intro t ht
  rw [unicyclicGaussianMain_eq M hM (Nat.zero_lt_one.trans_le hkone)]
  exact hk t ht

/-- Along any bounded critical-window sequence, the ratio of the genuine
simple connected unicyclic weight to its explicit Gaussian main term tends
to one. -/
theorem tendsto_connectedWeight_div_unicyclicGaussianMain
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (L : ℝ) (hL : 0 ≤ L) (t : ℕ → ℝ)
    (ht : ∀ᶠ k : ℕ in atTop, Real.sqrt (k : ℝ) * |t k - 1| ≤ L) :
    Tendsto (fun k : ℕ ↦ M.bjrModel.connectedWeight (t k) k 1 /
      unicyclicGaussianMain M hM k (t k)) atTop (𝓝 1) := by
  obtain ⟨K, _hK, hbound⟩ :=
    exists_connectedWeight_unicyclic_gaussian_relative_bound M hM L hL
  have herror : (fun k : ℕ ↦ M.bjrModel.connectedWeight (t k) k 1 /
      unicyclicGaussianMain M hM k (t k) - 1) =O[atTop]
      (fun k : ℕ ↦ (Real.sqrt (k : ℝ))⁻¹) := by
    apply Asymptotics.IsBigO.of_bound K
    filter_upwards [hbound, ht] with k hk htk
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
      div_eq_mul_inv] using hk (t k) htk
  have hscale : Tendsto (fun k : ℕ ↦ (Real.sqrt (k : ℝ))⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  simpa only [zero_add, sub_add_cancel] using
    (herror.trans_tendsto hscale).add_const 1

end PerronWright.FiniteIrreducibleUnicyclicTerminal
