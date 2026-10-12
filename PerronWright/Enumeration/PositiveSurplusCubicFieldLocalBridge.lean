import PerronWright.Enumeration.PositiveSurplusCubicFullTaylor
import PerronWright.Enumeration.FieldRootedTreeAnalyticGerm

/-!
# The actual-field local bridge for the positive-surplus cubic part

The power series defined here contains only the cubic part of the
fixed-surplus connected coefficient.  Along any genuine analytic
field-rooted tree branch at activity zero, the literal admissible cubic
profile functional has exactly this power series as its Taylor series.

No assertion is made that the cubic part equals the total connected graph
weight.  The final identity records the exact complementary noncubic term.
-/

open scoped Classical Topology

noncomputable section

namespace PerronWright.GraphCore

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The literal complex-field cubic-part EGF at fixed positive surplus.
Its coefficient is the cubic summand of the exact cubic/noncubic split; it
is not the total connected coefficient. -/
def complexFieldCubicPartEGF
    (M : CompactBJRModel S) (g : C(S, ℂ)) (ell : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk
    (cubicFixedSurplusProfileCompositionCoeff M
      (FieldRootedTree.series M g) ell)

@[simp] theorem complexFieldCubicPartEGF_coeff
    (M : CompactBJRModel S) (g : C(S, ℂ)) (ell k : ℕ) :
    PowerSeries.coeff k (complexFieldCubicPartEGF M g ell) =
      cubicFixedSurplusProfileCompositionCoeff M
        (FieldRootedTree.series M g) ell k := by
  simp [complexFieldCubicPartEGF]

/-- Along a genuine analytic field-rooted tree branch at activity zero, the
literal admissible cubic profile functional has the complex-field
cubic-part EGF as its complete Taylor series. -/
theorem positiveSurplusCubicProfileSeries_hasFPowerSeriesAt_complexFieldCubicPart
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (hell : 0 < ell)
    (g : C(S, ℂ)) (psi : ℂ × C(S, ℂ) → C(S, ℂ))
    (hpsi : AnalyticAt ℂ psi (0, g))
    (hpsi0 : psi (0, g) = 0)
    (hres : ∀ᶠ z in 𝓝 (0 : ℂ),
      TreeCritical.residual M ((z, g), psi (z, g)) = 0) :
    HasFPowerSeriesAt
      (fun w ↦ positiveSurplusCubicProfileSeries M ell (psi (w, g)))
      (oneDimensionalFormalMultilinearSeries
        (complexFieldCubicPartEGF M g ell)) 0 := by
  obtain ⟨p, hp, -, hpSeries⟩ :=
    FieldRootedTree.branch_taylorSeries_eq_series
      M g psi hpsi hpsi0 hres
  have hp0 : p.coeff 0 = 0 := by
    rw [← oneDimensionalPowerSeries_coeff p 0, hpSeries]
    exact FieldRootedTree.series_coeff_zero M g
  have hcubic :=
    positiveSurplusCubicProfileSeries_hasFPowerSeriesAt_cubicComposition
      M hM hell hp hp0
  have hpower :
      PowerSeries.mk
          (cubicFixedSurplusProfileCompositionCoeff M
            (oneDimensionalPowerSeries p) ell) =
        complexFieldCubicPartEGF M g ell := by
    rw [hpSeries]
    rfl
  rw [hpower] at hcubic
  exact hcubic

/-- Exact relation between the total normalized connected coefficient and
the cubic-part EGF coefficient.  The remaining summand is explicitly the
noncubic fixed-surplus profile-composition coefficient. -/
theorem complexFieldConnectedWeight_div_factorial_eq_cubicPartEGF_coeff_add_noncubic
    (M : CompactBJRModel S) (g : C(S, ℂ)) (ell k : ℕ) :
    M.complexFieldConnectedWeight g k (ell + 1) / (k.factorial : ℂ) =
      PowerSeries.coeff k (complexFieldCubicPartEGF M g ell) +
        noncubicFixedSurplusProfileCompositionCoeff M
          (FieldRootedTree.series M g) ell k := by
  rw [complexFieldConnectedWeight_div_factorial_eq_cubic_add_noncubic,
    complexFieldCubicPartEGF_coeff]

end PerronWright.GraphCore
