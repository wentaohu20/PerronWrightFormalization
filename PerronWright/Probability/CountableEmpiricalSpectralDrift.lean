import PerronWright.Probability.CountableEmpiricalGraphLaw

/-! # The paper spectral-drift assumption for the actual empirical graph

The construction is indexed by n+1 positive vertices. Its actual
empirical spectral root is used throughout. The final countable
theorem's stated critical-scale drift gives the exact lambda+theta
parameter shift; no varying-parameter graph convergence is assumed.
-/

open Filter Topology
open scoped Real
noncomputable section

namespace PerronWright.CountableKernel

def empiricalEffectiveParameter (M : CountableKernel) (level : ℕ → ℕ)
    (lambda : ℝ) (n : ℕ) : ℝ :=
  CriticalParameterDrift.effectiveParameter lambda
    (fun m ↦ M.empiricalSpectralRadius level (m - 1)) (n + 1)

private theorem empirical_drift_reindexed (M : CountableKernel) (level : ℕ → ℕ)
    (theta : ℝ)
    (h : Tendsto (fun n ↦ ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) *
      (M.empiricalSpectralRadius level n - 1)) atTop (𝓝 theta)) :
    Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (1 / 3 : ℝ) *
      (M.empiricalSpectralRadius level (m - 1) - 1)) atTop (𝓝 theta) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.add_sub_cancel] using h

theorem empiricalSpectralRadius_tendsto_one_of_drift (M : CountableKernel)
    (level : ℕ → ℕ) (theta : ℝ)
    (h : Tendsto (fun n ↦ ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) *
      (M.empiricalSpectralRadius level n - 1)) atTop (𝓝 theta)) :
    Tendsto (M.empiricalSpectralRadius level) atTop (𝓝 1) := by
  have hs := CriticalParameterDrift.sigma_tendsto_one (M.empirical_drift_reindexed level theta h)
  have hs' := hs.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n : ℕ ↦ M.empiricalSpectralRadius level ((n + 1) - 1)) atTop (𝓝 1) at hs'
  simpa only [Nat.add_sub_cancel] using hs'

theorem empiricalEffectiveParameter_tendsto (M : CountableKernel) (level : ℕ → ℕ)
    (lambda theta : ℝ)
    (h : Tendsto (fun n ↦ ((n + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) *
      (M.empiricalSpectralRadius level n - 1)) atTop (𝓝 theta)) :
    Tendsto (M.empiricalEffectiveParameter level lambda) atTop (𝓝 (lambda + theta)) := by
  exact (CriticalParameterDrift.effectiveParameter_tendsto
    (M.empirical_drift_reindexed level theta h) lambda).comp (tendsto_add_atTop_nat 1)

theorem empiricalUnnormalizedGraphLaw_eq_effective_normalized (M : CountableKernel)
    (level : ℕ → ℕ) (lambda : ℝ) {lower : ℝ}
    (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) (n : ℕ) :
    M.empiricalUnnormalizedGraphLaw level lambda n =
      M.empiricalNormalizedGraphLaw level (M.empiricalEffectiveParameter level lambda n)
        hlower hlo n :=
  M.empiricalUnnormalizedGraphLaw_eq_normalized level lambda hlower hlo n

end PerronWright.CountableKernel
