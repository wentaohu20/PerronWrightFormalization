import PerronWright.Probability.CountableFixedSupportVaryingLocal

/-! # Exact source identity at the actually selected support

At graph index `n`, both the actual vertices and the empirical spectral
root depend on the selected support at vertex count `n+1`. The full
independent-edge measure is therefore precisely the fixed-support
measure at that support value. This includes all small graph sizes.
-/

open MeasureTheory
open scoped BigOperators Classical Real
noncomputable section

namespace PerronWright.CountableKernel

theorem empiricalSpectralRadius_eq_fixedSupport_level (M : CountableKernel)
    (level : ℕ → ℕ) (n : ℕ) :
    M.empiricalSpectralRadius level n =
      M.empiricalSpectralRadius (fun _ ↦ level (n + 1)) n := by
  unfold empiricalSpectralRadius
  congr 1

theorem empiricalNormalizedGraphLaw_eq_fixedSupport_level (M : CountableKernel)
    (level : ℕ → ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t) (n : ℕ) :
    M.empiricalNormalizedGraphLaw level lambda hlower hlo n =
      M.empiricalNormalizedGraphLaw (fun _ ↦ level (n + 1)) lambda hlower hlo n := by
  unfold empiricalNormalizedGraphLaw
  congr 1

def growingLocalExpectation (M : CountableKernel) (level : ℕ → ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {q : ℕ} (n : ℕ) (y : Fin q → ℝ) (r : Fin q → ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (2 * (q : ℝ) / 3) *
    ∫ G, (ComponentCounts.count G (fun i ↦ CriticalScaling.size (y i) (n + 1)) r : ℝ)
      ∂M.empiricalNormalizedGraphLaw level lambda hlower hlo n

theorem growingLocalExpectation_eq_fixedSupport (M : CountableKernel)
    (level : ℕ → ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {q : ℕ} (n : ℕ) (y : Fin q → ℝ) (r : Fin q → ℕ) :
    M.growingLocalExpectation level lambda hlower hlo n y r =
      M.fixedSupportLocalExpectation (level (n + 1)) lambda hlower hlo n y r := by
  unfold growingLocalExpectation fixedSupportLocalExpectation
  rw [M.empiricalNormalizedGraphLaw_eq_fixedSupport_level]

end PerronWright.CountableKernel
