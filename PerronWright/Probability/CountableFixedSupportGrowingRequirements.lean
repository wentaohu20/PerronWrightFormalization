import PerronWright.Probability.CountableFixedSupportUniformParameter
import PerronWright.Probability.GrowingTypeRefinedRealization

/-! # Proved countable local requirements for the actual support diagonal

The integer index encodes finitely many tuple orders together with a
bounded surplus, bounded scalar parameter, positive real size window
and error tolerance. Each fixed-support requirement is proved eventual
from the actual uniform graph-source estimate.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section

namespace PerronWright.CountableKernel

def fixedSupportLocalRequirement (M : CountableKernel)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (m j N : ℕ) : Prop :=
  ∀ q : Fin (j + 2), 0 < q.val →
    ∀ lambda : ℝ, |lambda| ≤ (j + 1 : ℝ) →
    ∀ y : Fin q.val → ℝ, ∀ r : Fin q.val → ℕ,
    (∀ i, 1 / (j + 1 : ℝ) ≤ y i) → (∀ i, y i ≤ (j + 1 : ℝ)) →
    (∀ i, r i ≤ j + 1) →
    |M.fixedSupportLocalExpectation m lambda hlower hlo (N - 1) y r -
      M.fixedSupportReferenceDensity m lambda hlower hlo y r| < 1 / (j + 1 : ℝ)

theorem fixedSupportLocalRequirement_eventually (M : CountableKernel)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (m j : ℕ) :
    ∀ᶠ N : ℕ in atTop, M.fixedSupportLocalRequirement hlower hlo m j N := by
  have hp : Tendsto (fun N : ℕ ↦ N - 1) atTop atTop := tendsto_atTop.mpr (fun b ↦ by
    filter_upwards [eventually_ge_atTop (b + 1)] with N hN
    omega)
  unfold fixedSupportLocalRequirement
  apply eventually_all.mpr
  intro q
  by_cases hq : 0 < q.val
  · have h := M.fixedSupport_eventually_uniform_parameter_local_error
      m q.val (j + 1) hq (1 / (j + 1 : ℝ)) (j + 1 : ℝ) (j + 1 : ℝ)
      (by positivity) (by positivity) hlower hlo (show 0 < 1 / (j + 1 : ℝ) by positivity)
    exact (hp.eventually h).mono (fun _ h _ ↦ h)
  · exact Eventually.of_forall (fun _ h ↦ False.elim (hq h))

end PerronWright.CountableKernel
