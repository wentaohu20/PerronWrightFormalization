import PerronWright.Analysis.FiniteIrreducibleTreePerronWrightFormula
import PerronWright.Analysis.FiniteIrreduciblePhysicalScalarRadius

/-!
# The literal finite irreducible tree Perron--Wright terminal

The weights below are the actual labelled simple connected graph weights at
surplus zero. Their radius is the constructed critical radius of the literal
field-rooted tree series. No primitivity or two-step positivity is required.
The tree cubic amplitude gives exactly the paper's beta^(-1/2) factor.
-/

open Filter Topology Asymptotics
open scoped Topology Real

noncomputable section

namespace PerronWright.FiniteIrreducibleTreeTerminal

namespace PW
export PerronWright.FiniteIrreducibleTreePerronWrightFormula
  (physicalTreeRadiusMainTerm physicalTreeGaussianMainTerm
   physicalTreeRadiusMainTerm_eq_exp_rpow
   exists_treePerronWright_radius_relative_bound_uniform_eta
   exists_treePerronWright_gaussian_relative_bound)
end PW

namespace Radius
export PerronWright.FiniteIrreducibleCriticalWindowRadiusConversion
  (realScalarRadius criticalQuadraticRate)
end Radius

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- The paper's radius main term at surplus zero, with the genuine scalar
rooted-tree convergence radius. -/
def treeRadiusMain (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (k : ℕ) (t : ℝ) : ℝ :=
  (M.beta hM) ^ (-(1 / 2 : ℝ)) * (Radius.realScalarRadius M hM t)⁻¹ ^ k *
    Real.exp (-(k : ℝ)) * (k : ℝ) ^ ((k : ℝ) - 2)

/-- The paper's Gaussian main term at surplus zero. -/
def treeGaussianMain (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (k : ℕ) (t : ℝ) : ℝ :=
  (M.beta hM) ^ (-(1 / 2 : ℝ)) * Real.exp (-(k : ℝ)) *
    Real.exp (-(M.alpha hM ^ 2 / (2 * M.beta hM)) *
      (k : ℝ) * (t - 1) ^ 2) *
    (k : ℝ) ^ ((k : ℝ) - 2)

theorem treeRadiusMain_eq (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {k : ℕ} (hk : 0 < k) (t : ℝ) :
    treeRadiusMain M hM k t = PW.physicalTreeRadiusMainTerm M hM k t := by
  rw [PW.physicalTreeRadiusMainTerm_eq_exp_rpow M hM hk t]
  rfl

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem treeGaussianMain_eq (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {k : ℕ} (hk : 0 < k) (t : ℝ) :
    treeGaussianMain M hM k t =
      PW.physicalTreeGaussianMainTerm M hM k t := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hbase : ((k : ℝ) / Real.exp 1) ^ k =
      Real.exp (-(k : ℝ)) * (k : ℝ) ^ k := by
    rw [div_pow, Real.exp_one_pow, Real.exp_neg]
    ring
  have hrpow : (k : ℝ) ^ (-(2 : ℝ)) * (k : ℝ) ^ (k : ℝ) =
      (k : ℝ) ^ ((k : ℝ) - 2) := by
    rw [← Real.rpow_add hkreal]
    congr 1
    ring
  unfold treeGaussianMain PW.physicalTreeGaussianMainTerm
    FiniteIrreducibleFieldTreeConnectedWeightAsymptotic.fieldTreePerronWrightMainTerm
    Radius.criticalQuadraticRate
  rw [hbase, ← Real.rpow_natCast (k : ℝ) k]
  rw [show (M.beta hM) ^ (-(1 / 2 : ℝ)) *
      (k : ℝ) ^ (-(2 : ℝ)) *
      (Real.exp (-(k : ℝ)) * (k : ℝ) ^ (k : ℝ)) *
      Real.exp (-(M.alpha hM ^ 2 / (2 * M.beta hM)) * (k : ℝ) * (t - 1) ^ 2) =
    (M.beta hM) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(k : ℝ)) *
      Real.exp (-(M.alpha hM ^ 2 / (2 * M.beta hM)) * (k : ℝ) * (t - 1) ^ 2) *
      ((k : ℝ) ^ (-(2 : ℝ)) * (k : ℝ) ^ (k : ℝ)) by ring]
  rw [hrpow]

/-- The genuine simple connected tree weight satisfies the literal
radius formula on every shrinking scalar window. The error constant is
chosen before the window sequence. Monotonicity of the sequence is not needed. -/
theorem exists_connectedWeight_tree_radius_relative_bound_uniform_eta
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (𝓝 0) →
      ∀ᶠ k : ℕ in atTop, ∀ t : ℝ, |t - 1| ≤ eta k →
        |M.bjrModel.connectedWeight t k 0 /
            treeRadiusMain M hM k t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, hbound⟩ :=
    PW.exists_treePerronWright_radius_relative_bound_uniform_eta M hM
  refine ⟨K, hK, ?_⟩
  intro eta heta hlim
  filter_upwards [hbound eta heta hlim, eventually_ge_atTop (1 : ℕ)]
    with k hk hkone
  intro t ht
  rw [treeRadiusMain_eq M hM (Nat.zero_lt_one.trans_le hkone)]
  exact hk t ht

/-- Uniform critical-window Gaussian asymptotics of the actual surplus-zero
connected weight, in the original paper normalization. -/
theorem exists_connectedWeight_tree_gaussian_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop, ∀ t : ℝ,
      Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        |M.bjrModel.connectedWeight t k 0 /
            treeGaussianMain M hM k t - 1| ≤
          K / Real.sqrt (k : ℝ) := by
  obtain ⟨K, hK, hbound⟩ :=
    PW.exists_treePerronWright_gaussian_relative_bound M hM L hL
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)]
    with k hk hkone
  intro t ht
  rw [treeGaussianMain_eq M hM (Nat.zero_lt_one.trans_le hkone)]
  exact hk t ht

/-- Along any bounded critical-window sequence, the ratio of the genuine
simple connected tree weight to its explicit Gaussian main term tends
to one. -/
theorem tendsto_connectedWeight_div_treeGaussianMain
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (L : ℝ) (hL : 0 ≤ L) (t : ℕ → ℝ)
    (ht : ∀ᶠ k : ℕ in atTop, Real.sqrt (k : ℝ) * |t k - 1| ≤ L) :
    Tendsto (fun k : ℕ ↦ M.bjrModel.connectedWeight (t k) k 0 /
      treeGaussianMain M hM k (t k)) atTop (𝓝 1) := by
  obtain ⟨K, _hK, hbound⟩ :=
    exists_connectedWeight_tree_gaussian_relative_bound M hM L hL
  have herror : (fun k : ℕ ↦ M.bjrModel.connectedWeight (t k) k 0 /
      treeGaussianMain M hM k (t k) - 1) =O[atTop]
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

end PerronWright.FiniteIrreducibleTreeTerminal
