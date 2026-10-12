import PerronWright.Probability.CountableFixedSupportVaryingLocal
import PerronWright.Probability.CountableFixedSupportSequentialParameter

/-! # Genuine fixed-support local error uniformly on bounded parameters

Every convergent input-parameter sequence has already been controlled
using the actual empirical-normalized graph measures. Compactness of
the parameter interval now gives one threshold for all its parameters,
all real size coordinates in the window, and all bounded surplus tuples.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section

namespace PerronWright.CountableKernel

theorem fixedSupport_eventually_uniform_parameter_local_error
    (M : CountableKernel) (m q R : ℕ) (hq : 0 < q)
    (a b L : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
      ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |M.fixedSupportLocalExpectation m lambda hlower hlo n y r -
        M.fixedSupportReferenceDensity m lambda hlower hlo y r| < ε := by
  have h := CountableFixedSupportSequentialParameter.eventually_forall_compact_parameters
    (K := Set.Icc (-L) L) isCompact_Icc
    (fun n lambda ↦ ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
      (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
      |M.fixedSupportLocalExpectation m lambda hlower hlo n y r -
        M.fixedSupportReferenceDensity m lambda hlower hlo y r| < ε)
    (fun ell lambda _ hl ↦ M.fixedSupport_varying_local_error
      m q R hq ell lambda a b hl ha hb hlower hlo hε)
  filter_upwards [h] with n hn lambda hl
  exact hn lambda (abs_le.mp hl)

end PerronWright.CountableKernel
