import PerronWright.Enumeration.BoundedSurplusPerronWrightFormula

/-!
# Compact-type Perron--Wright conclusions

This file is the theorem-facing wrapper for the regular compact BJR model.
It exposes the analytic critical radius, its physical real branch, the
quadratic logarithmic expansion, and the bounded-surplus enumeration
formulae in one namespace.

For the arbitrary shrinking-window estimate, the error constant is chosen
before the window sequence; only the eventual threshold may depend on that
sequence.  Thus the wrapper records the sequence-uniform quantifier order
of the paper.  The fixed-`L` Gaussian conclusion is given separately in its
literal square-root-window form.
-/

open Filter Topology Asymptotics
open scoped Topology Real

noncomputable section

namespace PerronWright.CompactPerronWrightTheorem

namespace ScalarRadius

/-- The complex analytic extension of the physical critical radius. -/
abbrev criticalRadius {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) : ℂ → ℂ :=
  ScalarRadiusSecond.scalarRadius M hM

/-- The positive real branch of the critical radius. -/
abbrev physicalRadius {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) : ℝ → ℝ :=
  CriticalWindowRadiusConversion.realScalarRadius M hM

/-- The locally normalized analytic logarithm of the critical radius. -/
abbrev logCriticalRadius {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) : ℂ → ℂ :=
  ScalarLogRadiusTaylor.logScalarRadius M hM

end ScalarRadius

namespace MainTerm

export PerronWright.PerronWrightFormulaMainTerm
  (wrightConstant wrightConstant_pos perronWrightRadiusMainTerm)

export PerronWright.BoundedSurplusPerronWrightFormula
  (perronWrightGaussianMainTerm)

end MainTerm

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The critical radius has a complex analytic extension at the critical
point. -/
theorem criticalRadius_analyticAt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (ScalarRadius.criticalRadius M hM) 1 :=
  ScalarRadiusSecond.scalarRadius_analytic M hM

/-- Consequently, the physical radius is real analytic at one. -/
theorem physicalRadius_analyticAt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℝ (ScalarRadius.physicalRadius M hM) 1 := by
  change AnalyticAt ℝ
    (fun t : ℝ ↦ (ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).re) 1
  exact (criticalRadius_analyticAt_one M hM).re_ofReal

@[simp] theorem criticalRadius_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ScalarRadius.criticalRadius M hM 1 = 1 :=
  ScalarRadiusSecond.scalarRadius_one M hM

@[simp] theorem physicalRadius_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ScalarRadius.physicalRadius M hM 1 = 1 := by
  simp [ScalarRadius.physicalRadius,
    CriticalWindowRadiusConversion.realScalarRadius]

/-- The physical radius is strictly positive throughout a real
neighborhood of the critical point. -/
theorem physicalRadius_pos_eventually
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∀ᶠ t : ℝ in 𝓝 1, 0 < ScalarRadius.physicalRadius M hM t :=
  CriticalWindowRadiusConversion.realScalarRadius_pos_eventually M hM

/-- The normalized logarithm of the complex radius is analytic and
vanishes at one. -/
theorem logCriticalRadius_analyticAt_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (ScalarRadius.logCriticalRadius M hM) 1 :=
  ScalarLogRadiusTaylor.logScalarRadius_analytic M hM

@[simp] theorem logCriticalRadius_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ScalarRadius.logCriticalRadius M hM 1 = 0 :=
  ScalarLogRadiusTaylor.logScalarRadius_one M hM

/-- The logarithm of the physical radius has the paper's quadratic term
and a cubic local remainder. -/
theorem logPhysicalRadius_quadratic_remainder
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fun t : ℝ ↦
      Real.log (ScalarRadius.physicalRadius M hM t) -
        (M.alpha hM ^ 2 / (2 * M.beta hM)) * (t - 1) ^ 2)
      =O[𝓝 (1 : ℝ)] (fun t : ℝ ↦ |t - 1| ^ 3) := by
  simpa only [ScalarRadius.physicalRadius,
    CriticalWindowRadiusConversion.criticalQuadraticRate] using
      CriticalWindowRadiusConversion.real_logScalarRadius_cubic_remainder
        M hM

/-- Explicit local form of the logarithmic expansion, including the
positivity required to use the real logarithm. -/
theorem exists_logPhysicalRadius_quadratic_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ t : ℝ, |t - 1| < δ →
        0 < ScalarRadius.physicalRadius M hM t ∧
        |Real.log (ScalarRadius.physicalRadius M hM t) -
            (M.alpha hM ^ 2 / (2 * M.beta hM)) * (t - 1) ^ 2| ≤
          C * |t - 1| ^ 3 := by
  simpa only [ScalarRadius.physicalRadius,
    CriticalWindowRadiusConversion.criticalQuadraticRate] using
      CriticalWindowRadiusConversion.exists_real_logScalarRadius_cubic_bound
        M hM

/-- Near one, the analytic critical activity is the genuine convergence
radius of the rooted-tree generating series. -/
theorem exists_criticalRadius_eq_rootedTreeFMS_radius
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - 1| < δ →
      (FieldRootedTree.fms M
          (ScalarFieldResponse.scalarFieldComplex M (t : ℂ))).radius =
        ‖(ScalarRadius.physicalRadius M hM t : ℂ)‖ₑ := by
  simpa only [ScalarRadius.physicalRadius,
    TreePerronWrightFormula.physicalTreeRadius] using
      TreePerronWrightFormula.exists_physicalTreeRadius_eq_rootedTreeFMS_radius
        M hM

/-- The bounded-surplus radius estimate with the sequence-uniform quantifier
order of the paper: `K` is independent of the particular nonnegative
sequence `eta → 0`, while the eventual threshold may depend on `eta`. -/
theorem exists_boundedSurplus_radius_relative_bound_uniform_eta
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (nhds 0) →
      ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R → ∀ t : ℝ,
        |t - 1| ≤ eta k →
        |M.connectedWeight t k r /
            MainTerm.perronWrightRadiusMainTerm M hM k r t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) :=
  PerronWright.BoundedSurplusPerronWrightFormula.exists_boundedSurplusPerronWright_radius_relative_bound_uniform_eta
      M hM R

/-- Compatibility form obtained by specializing the sequence-uniform
radius estimate to one prescribed shrinking window. -/
theorem exists_boundedSurplus_radius_relative_bound_sequencewise
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (R : ℕ) (eta : ℕ → ℝ) (hetaNonneg : ∀ k, 0 ≤ eta k)
    (heta : Tendsto eta atTop (nhds 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R → ∀ t : ℝ,
        |t - 1| ≤ eta k →
        |M.connectedWeight t k r /
            MainTerm.perronWrightRadiusMainTerm M hM k r t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) :=
  PerronWright.BoundedSurplusPerronWrightFormula.exists_boundedSurplusPerronWright_radius_relative_bound_of_tendsto
      M hM R eta hetaNonneg heta

/-- The uniform bounded-surplus Gaussian formula on every fixed critical
window `|t-1| ≤ L k⁻¹ᐟ²`. -/
theorem exists_boundedSurplus_gaussian_relative_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (R : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ r : ℕ, r ≤ R → ∀ t : ℝ,
        |t - 1| ≤ L * (k : ℝ) ^ (-(1 / 2 : ℝ)) →
        |M.connectedWeight t k r /
            MainTerm.perronWrightGaussianMainTerm M hM k r t - 1| ≤
          K * (k : ℝ) ^ (-(1 / 2 : ℝ)) :=
  PerronWright.BoundedSurplusPerronWrightFormula.exists_boundedSurplusPerronWright_gaussian_relative_bound_rpow_window
      M hM R L hL

/-- The proposition collecting the analytic-radius and bounded-surplus
Perron--Wright conclusions with their exact quantifier order. -/
structure CompactPerronWrightConclusions
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R : ℕ) : Prop where
  complexRadiusAnalytic :
    AnalyticAt ℂ (ScalarRadius.criticalRadius M hM) 1
  physicalRadiusAnalytic :
    AnalyticAt ℝ (ScalarRadius.physicalRadius M hM) 1
  radiusNormalized : ScalarRadius.physicalRadius M hM 1 = 1
  radiusPositive :
    ∀ᶠ t : ℝ in 𝓝 1, 0 < ScalarRadius.physicalRadius M hM t
  radiusIdentification :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - 1| < δ →
      (FieldRootedTree.fms M
          (ScalarFieldResponse.scalarFieldComplex M (t : ℂ))).radius =
        ‖(ScalarRadius.physicalRadius M hM t : ℂ)‖ₑ
  logRadiusExpansion :
    (fun t : ℝ ↦
      Real.log (ScalarRadius.physicalRadius M hM t) -
        (M.alpha hM ^ 2 / (2 * M.beta hM)) * (t - 1) ^ 2)
      =O[𝓝 (1 : ℝ)] (fun t : ℝ ↦ |t - 1| ^ 3)
  uniformRadiusFormula :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (nhds 0) →
      ∀ᶠ k : ℕ in atTop,
        ∀ r : ℕ, r ≤ R → ∀ t : ℝ,
          |t - 1| ≤ eta k →
          |M.connectedWeight t k r /
              MainTerm.perronWrightRadiusMainTerm M hM k r t - 1| ≤
            K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ)))
  gaussianFormula :
    ∀ L : ℝ, 0 ≤ L →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
        ∀ r : ℕ, r ≤ R → ∀ t : ℝ,
          |t - 1| ≤ L * (k : ℝ) ^ (-(1 / 2 : ℝ)) →
          |M.connectedWeight t k r /
              MainTerm.perronWrightGaussianMainTerm M hM k r t - 1| ≤
            K * (k : ℝ) ^ (-(1 / 2 : ℝ))

/-- Assembly of the compact-type analytic and bounded-surplus enumeration
conclusions without adding any assumption beyond regular criticality. -/
theorem compactPerronWright_theorem
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (R : ℕ) :
    CompactPerronWrightConclusions M hM R where
  complexRadiusAnalytic := criticalRadius_analyticAt_one M hM
  physicalRadiusAnalytic := physicalRadius_analyticAt_one M hM
  radiusNormalized := physicalRadius_one M hM
  radiusPositive := physicalRadius_pos_eventually M hM
  radiusIdentification :=
    exists_criticalRadius_eq_rootedTreeFMS_radius M hM
  logRadiusExpansion := logPhysicalRadius_quadratic_remainder M hM
  uniformRadiusFormula :=
    exists_boundedSurplus_radius_relative_bound_uniform_eta M hM R
  gaussianFormula := fun L hL ↦
    exists_boundedSurplus_gaussian_relative_bound M hM R L hL

end PerronWright.CompactPerronWrightTheorem
