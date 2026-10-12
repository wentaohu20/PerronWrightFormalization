import PerronWright.Probability.CountableStarredTVWindowLimit
import PerronWright.Probability.CountableActualBrownianWindowTransport
import PerronWright.Probability.GraphBrownianWindowLimit
import PerronWright.Probability.GraphBrownianGlobalLimit

/-! # Actual Brownian-identified countable graph limits

A single genuinely constructed growing integer realization is retained.
The source dilation uses the original countable beta^(1/3); its global
unmarked law and localized empirical-TV marked window laws converge to
the actual Brownian full-excursion laws. The raw graph source has drift
alpha * beta^(-2/3) * (lambda + theta), with the original spectral drift
theta inside that factor. All local estimates and marked source limits
are discharged by the actual realization theorem, not assumed as a
Brownian identity or factorial-moment premise. No global TV-product
point-process topology is asserted.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableActualBrownianLimits

open CountableKernel CountableComponentWindowLaw CountableTVWindowConvergence CountableTVWindowProfile
open CountableStarredTVWindowLaw CountableStarredGlobalSizeRescaling
open ComponentWindowPointMeasures FinitePointMeasureCompact FinitePointMeasureMarking ComponentGlobalPointProcess
open LocallyFinitePointMeasureVague GraphWindowSource GraphWindowFactorialLimits FactorialDensity
open WindowSizeRescaling

variable (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
variable {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
variable (hlocal : ∀ q R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
  ∀ᶠ n : ℕ in atTop, ∀ ell : ℝ, |ell| ≤ L →
    ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
    (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
    |M.growingLocalExpectation level ell hlower hlo n y r -
      density (M.alpha hM) (M.beta hM) ell y r| < ε)

include hlocal

private theorem normalized_starred_window_tendsto
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    Tendsto (normalizedStarredWindowLaw M hM level hlower hlo lambda a b R) atTop
      (𝓝 (BrownianArbitraryWindowLaw.law
        (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * lambda) a b R ha hab)) := by
  change Tendsto (fun n ↦ normalizedStarredWindowLaw M hM level hlower hlo lambda a b R n)
    atTop (𝓝 (BrownianArbitraryWindowLaw.law
      (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * lambda) a b R ha hab))
  have hc := sizeScale_pos M hM
  have hu := GraphBrownianWindowLimit.windowLaw_tendsto_actual_Brownian
    (M.empiricalNormalizedGraphLaw level lambda hlower hlo) (M.beta_pos hM)
    (M.growing_uniform_local_limit hM level hlower hlo hlocal lambda)
    (div_pos ha hc) ((div_le_div_iff_of_pos_right hc).mpr hab) R
  have hs := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hu
    (continuous_mapPoint (windowScaleMap a b R hc) (continuous_windowScaleMap a b R hc))
  rw [CountableActualBrownianWindowTransport.inverse_window_map_eq_actual
    (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * lambda) a b R hc ha hab] at hs
  simpa only [normalizedStarredWindowLaw_eq_map M hM level hlower hlo lambda a b R] using hs

private theorem unnormalized_starred_window_tendsto (theta : ℝ)
    (hθ : Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
      (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta))
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    Tendsto (unnormalizedStarredWindowLaw M hM level lambda a b R) atTop
      (𝓝 (BrownianArbitraryWindowLaw.law
        (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * (lambda+theta)) a b R ha hab)) := by
  change Tendsto (fun n ↦ unnormalizedStarredWindowLaw M hM level lambda a b R n)
    atTop (𝓝 (BrownianArbitraryWindowLaw.law
      (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * (lambda+theta)) a b R ha hab))
  have hc := sizeScale_pos M hM
  have hu := GraphBrownianWindowLimit.windowLaw_tendsto_actual_Brownian
    (M.empiricalUnnormalizedGraphLaw level lambda) (M.beta_pos hM)
    (M.growing_unnormalized_uniform_local_limit hM level hlower hlo hlocal theta hθ lambda)
    (div_pos ha hc) ((div_le_div_iff_of_pos_right hc).mpr hab) R
  have hs := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hu
    (continuous_mapPoint (windowScaleMap a b R hc) (continuous_windowScaleMap a b R hc))
  rw [CountableActualBrownianWindowTransport.inverse_window_map_eq_actual
    (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * (lambda+theta)) a b R hc ha hab] at hs
  simpa only [unnormalizedStarredWindowLaw_eq_map M hM level lambda a b R] using hs

omit level hlocal in
/-- One positive integer realization, actual Brownian global laws, actual
Brownian closed-window laws with the original Perron TV mark, and the
already established quantitative TV controls, for both normalizations. -/
theorem exists_actual_growing_Brownian_global_and_TV_window_limits :
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
        ∀ᶠ n : ℕ in atTop, ∀ ell : ℝ, |ell| ≤ L →
          ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
          (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
          |M.growingLocalExpectation level ell hlower hlo n y r -
            density (M.alpha hM) (M.beta hM) ell y r| < ε) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda : ℝ, ∀ q R : ℕ, ∀ a b : ℝ, 0 < a → ∀ ε > 0,
          ∀ᶠ n : ℕ in atTop,
            0 < 1 + lambda * ((n+1 : ℕ) : ℝ)^(-(1/3 : ℝ)) ∧
            ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
            (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
            |M.growingUnnormalizedLocalExpectation level lambda n y r -
              density (M.alpha hM) (M.beta hM) (lambda+theta) y r| < ε) ∧
      (∀ lambda : ℝ,
        Tendsto (normalizedStarredProcessLaw M hM level hlower hlo lambda) atTop
          (𝓝 (BrownianExcursionPointProcessLaw.law
            (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * lambda)))) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda : ℝ,
          Tendsto (unnormalizedStarredProcessLaw M hM level lambda) atTop
            (𝓝 (BrownianExcursionPointProcessLaw.law
              (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * (lambda+theta))))) ∧
      (∀ lambda a b : ℝ, ∀ ha : 0 < a, ∀ hab : a ≤ b, ∀ R : ℕ,
        Tendsto (normalizedStarredWindowLaw M hM level hlower hlo lambda a b R) atTop
          (𝓝 (BrownianArbitraryWindowLaw.law
            (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * lambda) a b R ha hab)) ∧
        Tendsto (normalizedStarredMarkedWindowLaw M hM level hlower hlo lambda a b R) atTop
          (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R
            (BrownianArbitraryWindowLaw.law
              (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * lambda) a b R ha hab)))) ∧
      (∀ theta : ℝ,
        Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
          (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta) →
        ∀ lambda a b : ℝ, ∀ ha : 0 < a, ∀ hab : a ≤ b, ∀ R : ℕ,
          Tendsto (unnormalizedStarredWindowLaw M hM level lambda a b R) atTop
            (𝓝 (BrownianArbitraryWindowLaw.law
              (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * (lambda+theta)) a b R ha hab)) ∧
          Tendsto (unnormalizedStarredMarkedWindowLaw M hM level lambda a b R) atTop
            (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R
              (BrownianArbitraryWindowLaw.law
                (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * (lambda+theta)) a b R ha hab)))) ∧
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
            atTop (𝓝 0)) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal,
    _, _, _, _, hTV, hrawTV, _, _, hstarMarked, hstarRawMarked⟩ :=
      CountableStarredTVWindowLimit.exists_actual_growing_starred_global_and_TV_window_limits
        M hM hlower hlo
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, ?_,
    ?_, ?_, ?_, ?_, hTV, hrawTV⟩
  · intro theta hθ lambda q R a b ha ε hε
    exact M.growing_unnormalized_local_of_uniform_normalized hM level hlower hlo hlocal
      theta hθ lambda q R a b ha hε
  · intro lambda
    simpa only [normalizedStarredProcessLaw,sizeScale] using
      GraphBrownianGlobalLimit.starredProcessLaw_tendsto_actual_Brownian
        (M.empiricalNormalizedGraphLaw level lambda hlower hlo) (M.beta_pos hM)
        (M.growing_uniform_local_limit hM level hlower hlo hlocal lambda)
  · intro theta hθ lambda
    simpa only [unnormalizedStarredProcessLaw,sizeScale] using
      GraphBrownianGlobalLimit.starredProcessLaw_tendsto_actual_Brownian
        (M.empiricalUnnormalizedGraphLaw level lambda) (M.beta_pos hM)
        (M.growing_unnormalized_uniform_local_limit hM level hlower hlo hlocal theta hθ lambda)
  · intro lambda a b ha hab R
    let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
    let : MetricSpace (PointMeasure (SurplusWindow a b R)) :=
      TopologicalSpace.metrizableSpaceMetric _
    have hu := normalized_starred_window_tendsto M hM level hlower hlo hlocal lambda a b ha hab R
    obtain ⟨μ,hμ,_⟩ := (hstarMarked lambda a b ha hab R).1
    have he : μ = BrownianArbitraryWindowLaw.law
        (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * lambda) a b R ha hab :=
      tendsto_nhds_unique hμ.1 hu
    exact ⟨hu,by simpa only [he] using hμ.2⟩
  · intro theta hθ lambda a b ha hab R
    let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
    let : MetricSpace (PointMeasure (SurplusWindow a b R)) :=
      TopologicalSpace.metrizableSpaceMetric _
    have hu := unnormalized_starred_window_tendsto M hM level hlower hlo hlocal theta hθ
      lambda a b ha hab R
    obtain ⟨μ,hμ,_⟩ := (hstarRawMarked theta hθ lambda a b ha hab R).1
    have he : μ = BrownianArbitraryWindowLaw.law
        (M.alpha hM * (M.beta hM)^(-2/3 : ℝ) * (lambda+theta)) a b R ha hab :=
      tendsto_nhds_unique hμ.1 hu
    exact ⟨hu,by simpa only [he] using hμ.2⟩

end PerronWright.CountableActualBrownianLimits
