import PerronWright.Probability.CountableVariationMarks

/-!
# Actual finite-support Perron marks converge in atomic total variation

The source and target marks are literal probability measures. Their
convergence in the constructed variation metric follows from the proved
atomic Perron approximation, rather than a topology-conversion hypothesis.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace PerronWright.CountablePerronMarkConvergence

open CountableVariationMarks

def perronMark (M : CountableKernel) (hM : M.IsRegularCritical) : VariationMark :=
  ofProbability ⟨M.perronLaw hM, inferInstance⟩

def finitePerronMark (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) (s : Finset ℕ) (hzero : ∀ a, a ∉ s → w a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) : VariationMark :=
  ofProbability ⟨M.finitePerronLaw w hw hs s hzero hlower hlo, inferInstance⟩

/-- Actual finite Perron probability marks tend to the original Perron
probability mark in the literal countable atomic-variation metric. -/
theorem finitePerronMark_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    (w : ℕ → ℕ → ℝ) (hw : ∀ n a, 0 ≤ w n a) (hs : ∀ n, HasSum (w n) 1)
    (s : ℕ → Finset ℕ) (hzero : ∀ n a, a ∉ s n → w n a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (herr : Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) atTop (𝓝 0)) :
    Tendsto (fun n ↦ finitePerronMark M (w n) (hw n) (hs n) (s n)
      (hzero n) hlower hlo) atTop (𝓝 (perronMark M hM)) := by
  apply (tendsto_iff_atomic_variation _ _).mpr
  exact M.finitePerronLaw_atomic_variation_tendsto hM w hw hs s hzero hlower hlo herr

end PerronWright.CountablePerronMarkConvergence
