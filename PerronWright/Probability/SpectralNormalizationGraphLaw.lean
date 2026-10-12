import PerronWright.Probability.FixedTypeGraph
import PerronWright.Probability.CriticalParameterDrift

/-!
# Equality of normalized and unnormalized finite graph laws

The exact effective-parameter calculation is lifted to the actual graph
probability law.  This is the algebraic reduction used in the final
countable theorem; convergence for the varying parameter is a further
proof obligation and is not assumed here.
-/

open MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace PerronWright.SpectralNormalizationGraphLaw

open AnnealedGraph CriticalParameterDrift

def hazards {n : ℕ} (lambda : ℝ) (kappa : Edge n → ℝ) : Edge n → ℝ :=
  fun e ↦ CriticalScaling.time lambda n * kappa e / (n : ℝ)

def normalizedHazards {n : ℕ} (lambda : ℝ) (sigma : ℕ → ℝ)
    (kappa : Edge n → ℝ) : Edge n → ℝ :=
  fun e ↦ CriticalScaling.time (effectiveParameter lambda sigma n) n * kappa e /
    ((n : ℝ) * sigma n)

theorem hazards_nonneg {n : ℕ} (lambda : ℝ) (kappa : Edge n → ℝ)
    (hk : ∀ e, 0 ≤ kappa e) (e : Edge n) : 0 ≤ hazards lambda kappa e :=
  div_nonneg (mul_nonneg (CriticalScaling.time_nonneg lambda n) (hk e)) (Nat.cast_nonneg n)

theorem normalizedHazards_nonneg {n : ℕ} (lambda : ℝ) (sigma : ℕ → ℝ)
    (kappa : Edge n → ℝ) (hk : ∀ e, 0 ≤ kappa e) (hs : 0 ≤ sigma n) (e : Edge n) :
    0 ≤ normalizedHazards lambda sigma kappa e :=
  div_nonneg (mul_nonneg (CriticalScaling.time_nonneg _ n) (hk e))
    (mul_nonneg (Nat.cast_nonneg n) hs)

theorem hazards_eq_normalized {n : ℕ} (hn : 0 < n) (lambda : ℝ)
    (sigma : ℕ → ℝ) (hs : 0 < sigma n) (kappa : Edge n → ℝ) :
    hazards lambda kappa = normalizedHazards lambda sigma kappa := by
  funext e
  exact edge_hazard_eq hn lambda sigma hs (kappa e)

private theorem law_congr {n : ℕ} {z w : Edge n → ℝ}
    (hz : ∀ e, 0 ≤ z e) (hw : ∀ e, 0 ≤ w e) (h : z = w) :
    FixedTypeGraph.law z hz = FixedTypeGraph.law w hw := by
  cases h
  rfl

/-- Equality of actual graph laws, not just a formal time-parameter identity. -/
theorem unnormalized_law_eq_normalized {n : ℕ} (hn : 0 < n)
    (lambda : ℝ) (sigma : ℕ → ℝ) (hs : 0 < sigma n)
    (kappa : Edge n → ℝ) (hk : ∀ e, 0 ≤ kappa e) :
    FixedTypeGraph.law (hazards lambda kappa) (hazards_nonneg lambda kappa hk) =
      FixedTypeGraph.law (normalizedHazards lambda sigma kappa)
        (normalizedHazards_nonneg lambda sigma kappa hk hs.le) :=
  law_congr _ _ (hazards_eq_normalized hn lambda sigma hs kappa)

end PerronWright.SpectralNormalizationGraphLaw
