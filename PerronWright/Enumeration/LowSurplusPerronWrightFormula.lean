import PerronWright.Enumeration.TreePerronWrightFormula
import PerronWright.Enumeration.UnicyclicPerronWrightFormula

/-!
# A common shrinking-window formula for surplus zero and one

This file packages the already proved tree and unicyclic radius formulas
with one constant and one eventual threshold.  It is the low-surplus branch
of the eventual bounded-surplus theorem; no estimate is assumed here.
-/

open Filter Topology
open scoped Real

noncomputable section

namespace PerronWright.LowSurplusPerronWrightFormula

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The radius-dependent main term for the two low-surplus cases.  The
definition is only used below under the hypothesis `r ≤ 1`. -/
def lowSurplusRadiusMainTerm (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (k r : ℕ) (t : ℝ) : ℝ :=
  if r = 0 then
    TreePerronWrightFormula.physicalTreeRadiusMainTerm M hM k t
  else
    UnicyclicPerronWrightFormula.physicalUnicyclicRadiusMainTerm M hM k t

@[simp] theorem lowSurplusRadiusMainTerm_zero
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (k : ℕ) (t : ℝ) :
    lowSurplusRadiusMainTerm M hM k 0 t =
      TreePerronWrightFormula.physicalTreeRadiusMainTerm M hM k t := by
  simp [lowSurplusRadiusMainTerm]

@[simp] theorem lowSurplusRadiusMainTerm_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (k : ℕ) (t : ℝ) :
    lowSurplusRadiusMainTerm M hM k 1 t =
      UnicyclicPerronWrightFormula.physicalUnicyclicRadiusMainTerm M hM k t := by
  simp [lowSurplusRadiusMainTerm]

/-- The tree and unicyclic Perron--Wright formulas hold simultaneously,
with one relative-error constant, on every prescribed nonnegative shrinking
window. -/
theorem exists_lowSurplusPerronWright_radius_relative_bound_uniform_eta
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (nhds 0) →
      ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ 1 → ∀ t : ℝ,
        |t - 1| ≤ eta k →
        |M.connectedWeight t k r /
            lowSurplusRadiusMainTerm M hM k r t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K0, hK0, htree⟩ :=
    TreePerronWrightFormula.exists_treePerronWright_radius_relative_bound_uniform_eta
      M hM
  obtain ⟨K1, hK1, hunicyclic⟩ :=
    UnicyclicPerronWrightFormula.exists_unicyclicPerronWright_radius_relative_bound_uniform_eta
      M hM
  refine ⟨max K0 K1, lt_of_lt_of_le hK0 (le_max_left _ _), ?_⟩
  intro eta hetaNonneg heta
  have htreeWindow := htree eta hetaNonneg heta
  have hunicyclicWindow := hunicyclic eta hetaNonneg heta
  filter_upwards [htreeWindow, hunicyclicWindow] with k htreeK hunicyclicK
  intro r hr t ht
  have hscale :
      0 ≤ eta k + (k : ℝ) ^ (-(1 / 2 : ℝ)) :=
    add_nonneg (hetaNonneg k) (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hrCases : r = 0 ∨ r = 1 := by omega
  rcases hrCases with rfl | rfl
  · calc
      |M.connectedWeight t k 0 /
          lowSurplusRadiusMainTerm M hM k 0 t - 1| ≤
          K0 * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
        simpa using htreeK t ht
      _ ≤ max K0 K1 * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left K0 K1) hscale
  · calc
      |M.connectedWeight t k 1 /
          lowSurplusRadiusMainTerm M hM k 1 t - 1| ≤
          K1 * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
        simpa using hunicyclicK t ht
      _ ≤ max K0 K1 * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_right K0 K1) hscale

/-- Compatibility form with a prescribed shrinking window. -/
theorem exists_lowSurplusPerronWright_radius_relative_bound_of_tendsto
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (eta : ℕ → ℝ) (hetaNonneg : ∀ k, 0 ≤ eta k)
    (heta : Tendsto eta atTop (nhds 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ 1 → ∀ t : ℝ,
        |t - 1| ≤ eta k →
        |M.connectedWeight t k r /
            lowSurplusRadiusMainTerm M hM k r t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, huniform⟩ :=
    exists_lowSurplusPerronWright_radius_relative_bound_uniform_eta M hM
  exact ⟨K, hK, huniform eta hetaNonneg heta⟩

end PerronWright.LowSurplusPerronWrightFormula
