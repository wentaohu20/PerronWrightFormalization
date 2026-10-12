import PerronWright.Analysis.TreeOuterNeumann

open scoped Topology

noncomputable section

namespace PerronWright.TreeSubcriticalAnalytic

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Every real subcritical physical tree point has an actual complex analytic
continuation jointly in the radius and field, with local uniqueness. -/
theorem physicalTree_subcritical_analytic_neighborhood
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1)
    (V : C(S, ℝ)) (hV : ∀ x, 0 ≤ V x ∧ V x ≤ 1)
    (hfix : M.normalizedZeroTreeMap w V = V) :
    ∃ ψ : ℂ × C(S, ℂ) → C(S, ℂ),
      AnalyticAt ℂ ψ ((w : ℂ), 0) ∧
      ψ ((w : ℂ), 0) = TreeRealComplexBridge.complexify V ∧
      (∀ᶠ x in 𝓝 ((w : ℂ), 0), TreeCritical.residual M (x, ψ x) = 0) ∧
      (∀ᶠ p in 𝓝 (((w : ℂ), 0), TreeRealComplexBridge.complexify V),
        TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2) := by
  let U := TreeRealComplexBridge.complexify V
  let a : (ℂ × C(S, ℂ)) × C(S, ℂ) := (((w : ℂ), 0), U)
  have hu : IsUnit (fderiv ℂ (TreeCritical.residual M) a ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)) :=
    TreeOuterNeumann.physicalTree_subcritical_partial_isUnit M hM w hw hw1 V hV hfix
  have hi : (fderiv ℂ (TreeCritical.residual M) a ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofUnit hu.unit, by
      change (hu.unit : C(S, ℂ) →L[ℂ] C(S, ℂ)) = _
      exact hu.unit_spec⟩
  have hres : TreeCritical.residual M a = 0 :=
    (TreeRealComplexBridge.normalizedZeroTreeMap_fixed_iff_residual_zero M w V).mp hfix
  have hres' : TreeAnalytic.residual M.kernel M.mu (TreeCritical.degree M) a = 0 :=
    hres
  obtain ⟨ψ, ha, heq, hloc, huniq⟩ :=
    TreeAnalytic.residual_implicit_exists M.kernel M.mu (TreeCritical.degree M) a hi
  rw [hres'] at hloc huniq
  refine ⟨ψ, ha, heq, ?_, ?_⟩
  · exact hloc
  · exact huniq

/-- The physical branch and its joint analytic germ exist without taking any
tree solution, positivity bound, or invertibility as an extra hypothesis. -/
theorem exists_physical_subcritical_joint_analytic_germ
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) :
    ∃ (V : C(S, ℝ)) (ψ : ℂ × C(S, ℂ) → C(S, ℂ)),
      Filter.Tendsto (M.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
      (∀ x, 0 ≤ V x ∧ V x ≤ 1) ∧
      M.normalizedZeroTreeMap w V = V ∧
      AnalyticAt ℂ ψ ((w : ℂ), 0) ∧
      ψ ((w : ℂ), 0) = TreeRealComplexBridge.complexify V ∧
      (∀ᶠ x in 𝓝 ((w : ℂ), 0), TreeCritical.residual M (x, ψ x) = 0) ∧
      (∀ᶠ p in 𝓝 (((w : ℂ), 0), TreeRealComplexBridge.complexify V),
        TreeCritical.residual M p = 0 ↔ ψ p.1 = p.2) := by
  obtain ⟨V, hlim, hV, hfix, _⟩ :=
    M.normalizedZeroTreeIter_least_fixed hM w hw hw1
  obtain ⟨ψ, ha, heq, hzero, huniq⟩ :=
    physicalTree_subcritical_analytic_neighborhood M hM w hw hw1 V hV hfix
  exact ⟨V, ψ, hlim, hV, hfix, ha, heq, hzero, huniq⟩


end PerronWright.TreeSubcriticalAnalytic
