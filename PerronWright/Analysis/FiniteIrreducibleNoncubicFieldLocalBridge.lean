import PerronWright.Enumeration.NoncubicActualAdmissibleCoefficientBridge
import PerronWright.Analysis.FiniteIrreducibleCubicFieldLocalBridge
import PerronWright.Analysis.FiniteIrreducibleNoncubicProfileTaylor

/-!
# The actual-field local bridge for the positive-surplus noncubic part

The power series in this file is the noncubic summand in the exact
cubic/noncubic partition of the normalized connected coefficient.  Its
definition is therefore made directly from the actual labelled-graph
coefficient, rather than from a kernel-side analytic expression.
-/

open scoped Classical Topology

noncomputable section

namespace PerronWright.FiniteIrreducibleKernelAmplitude
open GraphCore

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The literal complex-field noncubic-part EGF at fixed positive
surplus. -/
def complexFieldNoncubicPartEGF
    (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) (ell : ℕ) :
    PowerSeries ℂ :=
  PowerSeries.mk
    (noncubicFixedSurplusProfileCompositionCoeff M.bjrModel
      (FieldRootedTree.series M.bjrModel g) ell)

@[simp] theorem complexFieldNoncubicPartEGF_coeff
    (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) (ell k : ℕ) :
    PowerSeries.coeff k (complexFieldNoncubicPartEGF M g ell) =
      noncubicFixedSurplusProfileCompositionCoeff M.bjrModel
        (FieldRootedTree.series M.bjrModel g) ell k := by
  simp [complexFieldNoncubicPartEGF]

/-- Along a genuine analytic field-rooted tree branch at activity zero,
the noncubic away-profile functional has the actual complex-field
noncubic-part EGF as its complete Taylor series. -/
theorem
    positiveSurplusNoncubicAdmissibleProfileFunctional_hasFPowerSeriesAt_complexFieldNoncubicPart
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell)
    (g : C(S, ℂ)) (psi : ℂ × C(S, ℂ) → C(S, ℂ))
    (hpsi : AnalyticAt ℂ psi (0, g))
    (hpsi0 : psi (0, g) = 0)
    (hres : ∀ᶠ z in 𝓝 (0 : ℂ),
      TreeCritical.residual M.bjrModel ((z, g), psi (z, g)) = 0) :
    HasFPowerSeriesAt
      (fun w ↦ positiveSurplusNoncubicAdmissibleProfileFunctional
        M ell (psi (w, g)))
      (oneDimensionalFormalMultilinearSeries
        (complexFieldNoncubicPartEGF M g ell)) 0 := by
  obtain ⟨p, hp, -, hpSeries⟩ :=
    FieldRootedTree.branch_taylorSeries_eq_series M.bjrModel g psi hpsi hpsi0 hres
  have hp0 : p.coeff 0 = 0 := by
    rw [← oneDimensionalPowerSeries_coeff p 0, hpSeries]
    exact FieldRootedTree.series_coeff_zero M.bjrModel g
  have hnoncubic :=
    positiveSurplusNoncubicAdmissibleProfileFunctional_hasFPowerSeriesAt
      M hM hell hp hp0
  have hpower :
      positiveSurplusNoncubicProfileCompositionSeries M.bjrModel
          (oneDimensionalPowerSeries p) ell =
        complexFieldNoncubicPartEGF M g ell := by
    rw [positiveSurplusNoncubicProfileCompositionSeries_eq_actual M.bjrModel (oneDimensionalPowerSeries p) hell]
    rw [hpSeries]
    rfl
  rw [hpower] at hnoncubic
  exact hnoncubic

/-- The normalized actual connected EGF at fixed positive surplus. -/
def complexFieldFixedSurplusConnectedEGF
    (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) (ell : ℕ) :
    PowerSeries ℂ :=
  PowerSeries.mk (fun k ↦
    M.bjrModel.complexFieldConnectedWeight g k (ell + 1) / (k.factorial : ℂ))

@[simp] theorem complexFieldFixedSurplusConnectedEGF_coeff
    (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) (ell k : ℕ) :
    PowerSeries.coeff k (complexFieldFixedSurplusConnectedEGF M g ell) =
      M.bjrModel.complexFieldConnectedWeight g k (ell + 1) /
        (k.factorial : ℂ) := by
  simp [complexFieldFixedSurplusConnectedEGF]

/-- The exact cubic/noncubic partition holds coefficientwise, hence as an
identity of the two actual normalized EGFs. -/
theorem complexFieldFixedSurplusConnectedEGF_eq_cubic_add_noncubic
    (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) (ell : ℕ) :
    complexFieldFixedSurplusConnectedEGF M g ell =
      complexFieldCubicPartEGF M g ell +
        complexFieldNoncubicPartEGF M g ell := by
  ext k
  rw [complexFieldFixedSurplusConnectedEGF_coeff, map_add,
    complexFieldCubicPartEGF_coeff, complexFieldNoncubicPartEGF_coeff]
  exact complexFieldConnectedWeight_div_factorial_eq_cubic_add_noncubic M.bjrModel g ell k

/-- The cubic-normalized noncubic local numerator has one explicit fold
coordinate and an analytic remainder.  Both the remainder and the
factorization are the already constructed finite bounded-kernel sums. -/
theorem exists_analytic_noncubicIntegratedRemainder
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (ell : ℕ) :
    ∃ R : C(S, ℂ) × ℂ → ℂ,
      AnalyticAt ℂ R (0, 0) ∧
        ∀ q, positiveSurplusNoncubicIntegratedAmplitude M hM ell q =
          q.2 * R q := by
  exact ⟨positiveSurplusNoncubicIntegratedRemainder M hM ell,
    positiveSurplusNoncubicIntegratedRemainder_analytic M hM ell,
    positiveSurplusNoncubicIntegratedAmplitude_eq_X_mul M hM ell⟩

end PerronWright.FiniteIrreducibleKernelAmplitude
