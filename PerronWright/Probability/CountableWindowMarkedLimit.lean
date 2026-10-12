import PerronWright.Probability.CountableVaryingTVWindowProfile
import PerronWright.Probability.GraphWindowMarkedSpatialLimit

/-! # One actual growing countable realization with TV-marked weak limits

All numerical and profile inputs are discharged by the same proved
positive integer realization. Both normalizations use its literal graph
law and empirical component probability marks. Their full weak window
limits are canonical Perron markings of actual spatial window limits.
Only the paper's actual spectral-drift premise is used for the shifted
unnormalized parameter. No Brownian identification is asserted.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

open GraphWindowSource GraphWindowFactorialLimits GraphWindowMarkedSpatialLimit
open GraphWindowMarkTransfer CountableTVWindowConvergence
open CountableVariationMarks CountableComponentWindowLaw CountableTVWindowProfile
open ComponentWindowPointMeasures FinitePointMeasureCompact FactorialDensity

variable (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
variable {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
variable (hlocal : ∀ q R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
  ∀ᶠ n : ℕ in atTop, ∀ ell : ℝ, |ell| ≤ L →
    ∀ y : Fin q → ℝ, ∀ r : Fin q → ℕ,
    (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
    |M.growingLocalExpectation level ell hlower hlo n y r -
      density (M.alpha hM) (M.beta hM) ell y r| < ε)
variable (hTV : ∀ R : ℕ, ∀ a b L : ℝ, 0 < a → ∀ ε > 0,
  ∀ᶠ n : ℕ in atTop, ∀ ell : ℝ, |ell| ≤ L →
    ∀ y : Fin 1 → ℝ, ∀ r : Fin 1 → ℕ,
    (∀ i, a ≤ y i) → (∀ i, y i ≤ b) → (∀ i, r i ≤ R) →
    M.growingDistanceLocalExpectation level ell hlower hlo n y r
      (CountablePerronMarkConvergence.perronMark M hM) < ε)

include hlocal hTV

theorem normalized_joint_window_limit_of_actual_estimates
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃! μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R)
        atTop (𝓝 μ) ∧
      Tendsto (M.empiricalMarkedWindowLaw level lambda a b R hlower hlo) atTop
        (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R μ)) := by
  have hbad (δ : ℝ) (hδ : 0 < δ) := M.varying_windowBadEvent_probability_tendsto_zero
    level hlower hlo (CountablePerronMarkConvergence.perronMark M hM) hTV
    (fun _ ↦ lambda) lambda tendsto_const_nhds a b ha hab R δ hδ
  have hh :=
    exists_unique_joint_window_limit (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
      (fun n ↦ CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) (M.beta_pos hM)
      (M.growing_uniform_local_limit hM level hlower hlo hlocal lambda) ha hab R
      (CountablePerronMarkConvergence.perronMark M hM) hbad
  have he : markedWindowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
      (fun n ↦ CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) a b R =
      M.empiricalMarkedWindowLaw level lambda a b R hlower hlo :=
    funext (fun n ↦ M.graphMarkedWindowLaw_eq_empirical level hlower hlo lambda a b R n)
  rwa [he] at hh

theorem unnormalized_joint_window_limit_of_actual_estimates
    (theta : ℝ)
    (hθ : Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
      (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta))
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃! μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (windowLaw (M.empiricalUnnormalizedGraphLaw level lambda) a b R) atTop (𝓝 μ) ∧
      Tendsto (M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R) atTop
        (𝓝 (canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R μ)) := by
  have hbad := M.unnormalized_windowBadEvent_probability_tendsto_zero level hlower hlo
    (CountablePerronMarkConvergence.perronMark M hM) hTV theta hθ lambda a b ha hab R
  have hh :=
    exists_unique_joint_window_limit (M.empiricalUnnormalizedGraphLaw level lambda)
      (fun n ↦ CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) (M.beta_pos hM)
      (M.growing_unnormalized_uniform_local_limit hM level hlower hlo hlocal theta hθ lambda)
      ha hab R (CountablePerronMarkConvergence.perronMark M hM) hbad
  have he : markedWindowLaw (M.empiricalUnnormalizedGraphLaw level lambda)
      (fun n ↦ CountableTypeRealization.vertexTypes M (level (n+1)) (n+1)) a b R =
      M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R :=
    funext (fun n ↦ M.graphMarkedWindowLaw_eq_empiricalUnnormalized level lambda a b R n)
  rwa [he] at hh

theorem normalized_marked_window_limit_of_actual_estimates
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃! ν : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)),
      Tendsto (M.empiricalMarkedWindowLaw level lambda a b R hlower hlo) atTop (𝓝 ν) := by
  let : TopologicalSpace.MetrizableSpace (PointMeasure (MarkedWindow a b R)) :=
    markedPointMeasure_metrizableSpace a b hab R (CountablePerronMarkConvergence.perronMark M hM)
  obtain ⟨μ, hμ, _⟩ := M.normalized_joint_window_limit_of_actual_estimates hM level hlower hlo
    hlocal hTV lambda a b ha hab R
  exact ⟨canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R μ,
    hμ.2, fun ν hν ↦ tendsto_nhds_unique hν hμ.2⟩

theorem unnormalized_marked_window_limit_of_actual_estimates
    (theta : ℝ)
    (hθ : Tendsto (fun n ↦ ((n+1 : ℕ) : ℝ)^(1/3 : ℝ) *
      (M.empiricalSpectralRadius level n-1)) atTop (𝓝 theta))
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    ∃! ν : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)),
      Tendsto (M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R) atTop (𝓝 ν) := by
  let : TopologicalSpace.MetrizableSpace (PointMeasure (MarkedWindow a b R)) :=
    markedPointMeasure_metrizableSpace a b hab R (CountablePerronMarkConvergence.perronMark M hM)
  obtain ⟨μ, hμ, _⟩ := M.unnormalized_joint_window_limit_of_actual_estimates hM level hlower hlo
    hlocal hTV theta hθ lambda a b ha hab R
  exact ⟨canonicalMarkedWindowLaw (CountablePerronMarkConvergence.perronMark M hM) a b R μ,
    hμ.2, fun ν hν ↦ tendsto_nhds_unique hν hμ.2⟩

omit level hlocal hTV in
theorem exists_actual_growing_marked_window_limits :
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
            atTop (𝓝 0)) := by
  obtain ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, hTV, _, _, hfixed⟩ :=
    M.exists_actual_growing_local_main_and_window_TV_profile hM hlower hlo
  refine ⟨level, hm, ht, hle, hc, hpos, hprob, herr, hmin, hlocal, ?_, ?_, hfixed, ?_⟩
  · intro lambda a b ha hab R
    exact ⟨M.normalized_joint_window_limit_of_actual_estimates hM level hlower hlo hlocal hTV
        lambda a b ha hab R,
      M.normalized_marked_window_limit_of_actual_estimates hM level hlower hlo hlocal hTV
        lambda a b ha hab R⟩
  · intro theta hθ lambda a b ha hab R
    exact ⟨M.unnormalized_joint_window_limit_of_actual_estimates hM level hlower hlo hlocal hTV
        theta hθ lambda a b ha hab R,
      M.unnormalized_marked_window_limit_of_actual_estimates hM level hlower hlo hlocal hTV
        theta hθ lambda a b ha hab R⟩
  · intro theta hθ lambda a b ha hab R
    exact ⟨M.unnormalized_windowDistance_tendsto_zero level hlower hlo
        (CountablePerronMarkConvergence.perronMark M hM) hTV theta hθ lambda a b ha hab R,
      M.unnormalized_markedWindowBadProbability_tendsto_zero level hlower hlo
        (CountablePerronMarkConvergence.perronMark M hM) hTV theta hθ lambda a b ha hab R⟩

end PerronWright.CountableKernel
