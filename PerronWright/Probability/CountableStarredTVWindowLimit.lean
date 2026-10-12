import PerronWright.Probability.CountableStarredTVWindowLaw

/-! # One actual countable source for starred global and TV window limits

Positive dilation is applied to the proved joint unmarked and marked
window limits of the same graph source. The model terminal retains its
single positive integer realization and all prior conclusions; the raw
source uses the literal paper spectral drift. TV marks are never made
compact, and no global TV-product vague space is introduced.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableStarredTVWindowLimit

open CountableKernel CountableComponentWindowLaw CountableTVWindowConvergence CountableTVWindowProfile
open CountableStarredTVWindowLaw CountableStarredGlobalSizeRescaling
open GraphWindowSource GraphWindowScaledTVLaw GraphWindowMarkTransfer
open ComponentWindowPointMeasures FinitePointMeasureCompact FactorialDensity
open ComponentGlobalPointProcess LocallyFinitePointMeasureVague GraphGlobalSpatialLimit

theorem normalized_starred_window_limits_of_actual_joint_limit
    (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (lambda a b : ℝ) (hab : a ≤ b) (R : ℕ)
    (hsource : ∃! μ : ProbabilityMeasure
        (PointMeasure (SurplusWindow (a/sizeScale M hM) (b/sizeScale M hM) R)),
      Tendsto (windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
        (a/sizeScale M hM) (b/sizeScale M hM) R) atTop (𝓝 μ) ∧
      Tendsto (M.empiricalMarkedWindowLaw level lambda (a/sizeScale M hM) (b/sizeScale M hM) R hlower hlo)
        atTop (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM)
          (a/sizeScale M hM) (b/sizeScale M hM) R μ))) :
    (∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (normalizedStarredWindowLaw M hM level hlower hlo lambda a b R) atTop (𝓝 ν) ∧
      Tendsto (normalizedStarredMarkedWindowLaw M hM level hlower hlo lambda a b R) atTop
        (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R ν))) ∧
    (∃! τ : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)),
      Tendsto (normalizedStarredMarkedWindowLaw M hM level hlower hlo lambda a b R) atTop (𝓝 τ)) := by
  obtain ⟨μ, ⟨hμ, hmarked⟩, _⟩ := hsource
  have he : markedWindowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
      (fun n ↦ CountableTypeRealization.vertexTypes M (level (n+1)) (n+1))
        (a/sizeScale M hM) (b/sizeScale M hM) R =
      M.empiricalMarkedWindowLaw level lambda (a/sizeScale M hM) (b/sizeScale M hM) R hlower hlo :=
    funext (fun n ↦ M.graphMarkedWindowLaw_eq_empirical level hlower hlo lambda
      (a/sizeScale M hM) (b/sizeScale M hM) R n)
  rw [← he] at hmarked
  exact ⟨scaled_joint_window_limit_of_joint_limit _ _ a b hab R (sizeScale_pos M hM)
      (CountablePerronMarkConvergence.perronMark M hM) μ hμ hmarked,
    scaled_marked_window_limit_of_joint_limit _ _ a b hab R (sizeScale_pos M hM)
      (CountablePerronMarkConvergence.perronMark M hM) μ hμ hmarked⟩

theorem unnormalized_starred_window_limits_of_actual_joint_limit
    (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
    (lambda a b : ℝ) (hab : a ≤ b) (R : ℕ)
    (hsource : ∃! μ : ProbabilityMeasure
        (PointMeasure (SurplusWindow (a/sizeScale M hM) (b/sizeScale M hM) R)),
      Tendsto (windowLaw (M.empiricalUnnormalizedGraphLaw level lambda)
        (a/sizeScale M hM) (b/sizeScale M hM) R) atTop (𝓝 μ) ∧
      Tendsto (M.empiricalUnnormalizedMarkedWindowLaw level lambda
        (a/sizeScale M hM) (b/sizeScale M hM) R) atTop
          (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM)
            (a/sizeScale M hM) (b/sizeScale M hM) R μ))) :
    (∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (unnormalizedStarredWindowLaw M hM level lambda a b R) atTop (𝓝 ν) ∧
      Tendsto (unnormalizedStarredMarkedWindowLaw M hM level lambda a b R) atTop
        (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R ν))) ∧
    (∃! τ : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)),
      Tendsto (unnormalizedStarredMarkedWindowLaw M hM level lambda a b R) atTop (𝓝 τ)) := by
  obtain ⟨μ, ⟨hμ, hmarked⟩, _⟩ := hsource
  have he : markedWindowLaw (M.empiricalUnnormalizedGraphLaw level lambda)
      (fun n ↦ CountableTypeRealization.vertexTypes M (level (n+1)) (n+1))
        (a/sizeScale M hM) (b/sizeScale M hM) R =
      M.empiricalUnnormalizedMarkedWindowLaw level lambda (a/sizeScale M hM) (b/sizeScale M hM) R :=
    funext (fun n ↦ M.graphMarkedWindowLaw_eq_empiricalUnnormalized level lambda
      (a/sizeScale M hM) (b/sizeScale M hM) R n)
  rw [← he] at hmarked
  exact ⟨scaled_joint_window_limit_of_joint_limit _ _ a b hab R (sizeScale_pos M hM)
      (CountablePerronMarkConvergence.perronMark M hM) μ hμ hmarked,
    scaled_marked_window_limit_of_joint_limit _ _ a b hab R (sizeScale_pos M hM)
      (CountablePerronMarkConvergence.perronMark M hM) μ hμ hmarked⟩

theorem exists_actual_growing_starred_global_and_TV_window_limits
    (M : CountableKernel) (hM : M.IsRegularCritical)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t) :
    ∃ level : ℕ → ℕ, Monotone level ∧ Tendsto level atTop atTop ∧
      (∀ N, level N ≤ N) ∧
      (∀ N, ∑ a, GrowingTypeCounts.truncatedCounts
        (CountableTypeRealization.weights M) (level N) N a = N) ∧
      (∀ N > 0, ∀ a, 0 < GrowingTypeCounts.truncatedCounts
        (CountableTypeRealization.weights M) (level N) N a) ∧
      (∀ N > 0, IsProbabilityMeasure (CountableTypeRealization.empiricalMeasure M (level N) N)) ∧
      Tendsto (fun N ↦ ∑' s : ℕ,
        |(CountableTypeRealization.empiricalMeasure M (level N) N).real {s} - M.mu.real {s}|)
        atTop (𝓝 0) ∧
      (∀ B : ℝ, ∀ᶠ N : ℕ in atTop, ∀ a : Fin (level N+1),
        B ≤ (N : ℝ)^(1/3 : ℝ) *
          (CountableTypeRealization.empiricalMeasure M (level N) N).real {a.val}) ∧
      (∀ q R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop, ∀ lambda : ℝ, |lambda| ≤ L →
          ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
          (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
          |M.growingLocalExpectation level lambda hlower hlo n y r -
            density (M.alpha hM) (M.beta hM) lambda y r| < ε) ∧
      (∀ lambda : ℝ, ∃! ξ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
        Tendsto (processLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo))
          atTop (𝓝 ξ)) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda : ℝ, ∃! ξ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
          Tendsto (processLaw (M.empiricalUnnormalizedGraphLaw level lambda))
            atTop (𝓝 ξ)) ∧
      (∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
        (∃! μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
          Tendsto (windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R)
            atTop (𝓝 μ) ∧
          Tendsto (M.empiricalMarkedWindowLaw level lambda a b R hlower hlo) atTop
            (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R μ))) ∧
        (∃! ν : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)),
          Tendsto (M.empiricalMarkedWindowLaw level lambda a b R hlower hlo) atTop (𝓝 ν))) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
          (∃! μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
            Tendsto (windowLaw (M.empiricalUnnormalizedGraphLaw level lambda) a b R) atTop (𝓝 μ) ∧
            Tendsto (M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R) atTop
              (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R μ))) ∧
          (∃! ν : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)),
            Tendsto (M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R) atTop (𝓝 ν))) ∧
      (∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
        Tendsto (fun n ↦ M.growingWindowDistanceExpectation level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM)) atTop (𝓝 0) ∧
        ∀ δ > 0, Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n
          (CountablePerronMarkConvergence.perronMark M hM) δ) atTop (𝓝 0)) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
          Tendsto (fun n ↦ ∫ G, windowDistance
            (CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) G a b R
            (CountablePerronMarkConvergence.perronMark M hM)
            ∂M.empiricalUnnormalizedGraphLaw level lambda n) atTop (𝓝 0) ∧
          ∀ δ > 0, Tendsto (fun n ↦ (M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R n :
            Measure (PointMeasure (MarkedWindow a b R))).real
              {η | 0 < count η (badMarkCell a b R (CountablePerronMarkConvergence.perronMark M hM) δ)})
            atTop (𝓝 0))
      ∧ (∀ lambda : ℝ, ∃! ξ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
        Tendsto (normalizedStarredProcessLaw M hM level hlower hlo lambda) atTop (𝓝 ξ))
      ∧ (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda : ℝ, ∃! ξ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
          Tendsto (unnormalizedStarredProcessLaw M hM level lambda) atTop (𝓝 ξ))
      ∧ (∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
        (∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
          Tendsto (normalizedStarredWindowLaw M hM level hlower hlo lambda a b R) atTop (𝓝 ν) ∧
          Tendsto (normalizedStarredMarkedWindowLaw M hM level hlower hlo lambda a b R) atTop
            (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R ν))) ∧
        (∃! τ : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)),
          Tendsto (normalizedStarredMarkedWindowLaw M hM level hlower hlo lambda a b R) atTop (𝓝 τ)))
      ∧ (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda a b : ℝ, 0 < a → a ≤ b → ∀ R : ℕ,
          (∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
            Tendsto (unnormalizedStarredWindowLaw M hM level lambda a b R) atTop (𝓝 ν) ∧
            Tendsto (unnormalizedStarredMarkedWindowLaw M hM level lambda a b R) atTop
              (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R ν))) ∧
          (∃! τ : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)),
            Tendsto (unnormalizedStarredMarkedWindowLaw M hM level lambda a b R) atTop (𝓝 τ))) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal,
    hglobal, hrawGlobal, hmarked, hrawMarked, hTV, hrawTV⟩ :=
      M.exists_actual_growing_global_and_marked_window_limits hM hlower hlo
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal,
    hglobal, hrawGlobal, hmarked, hrawMarked, hTV, hrawTV, ?_, ?_, ?_, ?_⟩
  · intro lambda
    exact normalized_limit_of_actual_estimates M hM level hlower hlo hlocal lambda
  · intro theta hθ lambda
    exact unnormalized_limit_of_actual_estimates M hM level hlower hlo hlocal theta hθ lambda
  · intro lambda a b ha hab R
    exact normalized_starred_window_limits_of_actual_joint_limit M hM level hlower hlo lambda a b hab R
      (hmarked lambda (a/sizeScale M hM) (b/sizeScale M hM)
        (div_pos ha (sizeScale_pos M hM))
        ((div_le_div_iff_of_pos_right (sizeScale_pos M hM)).mpr hab) R).1
  · intro theta hθ lambda a b ha hab R
    exact unnormalized_starred_window_limits_of_actual_joint_limit M hM level lambda a b hab R
      (hrawMarked theta hθ lambda (a/sizeScale M hM) (b/sizeScale M hM)
        (div_pos ha (sizeScale_pos M hM))
        ((div_le_div_iff_of_pos_right (sizeScale_pos M hM)).mpr hab) R).1


end PerronWright.CountableStarredTVWindowLimit
