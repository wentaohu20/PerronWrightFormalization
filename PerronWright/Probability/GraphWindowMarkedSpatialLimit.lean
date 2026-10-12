import PerronWright.Probability.GraphWindowMarkTransfer
import PerronWright.Probability.GraphWindowSpatialLimit

/-! # Genuine full-sequence marked spatial window limits

The unmarked spatial law is constructed from actual graph factorial
estimates. Actual localized TV probabilities identify its marked
pushforward limit. The empirical marked law is the literal graph source;
the TV mark space is not required to be compact.
-/

open MeasureTheory Filter Topology
open scoped Classical Real Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000

namespace PerronWright.GraphWindowMarkedSpatialLimit

open GraphWindowSource GraphWindowFactorialLimits GraphWindowSpatialLimit
open GraphWindowMarkTransfer CountableTVWindowConvergence
open CountableVariationMarks CountableComponentWindowLaw CountableTVWindowProfile
open ComponentWindowPointMeasures FinitePointMeasureCompact

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]
variable (x : (n : ℕ) → Fin (n+1) → ℕ)

/-- The existing normalization encoding is an embedding without compact
marks; its target is a product of genuine weak-metrizable spaces. -/
theorem markedPointMeasure_metrizableSpace (a b : ℝ) (hab : a ≤ b) (R : ℕ) (p : VariationMark) :
    TopologicalSpace.MetrizableSpace (PointMeasure (MarkedWindow a b R)) := by
  let : Nonempty (MarkedWindow a b R) := ⟨((⟨a, le_rfl, hab⟩, ⟨0, by omega⟩), p)⟩
  exact (FinitePointMeasurePolish.isEmbedding_encode (E := MarkedWindow a b R)).metrizableSpace

theorem exists_unique_joint_window_limit {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (p : VariationMark)
    (hTV : ∀ δ > 0, Tendsto (fun n ↦ (ρ n).real (badTVEvent (x n) a b R p δ)) atTop (𝓝 0)) :
    ∃! μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (windowLaw ρ a b R) atTop (𝓝 μ) ∧
      Tendsto (markedWindowLaw ρ x a b R) atTop (𝓝 (canonicalMarkedWindowLaw p a b R μ)) := by
  obtain ⟨μ, hμ, huniq⟩ := exists_unique_windowLaw_limit ρ hbeta hlocal ha hab R
  exact ⟨μ, ⟨hμ, markedWindowLaw_tendsto_of_local_limit ρ x hbeta hlocal ha hab R p hTV μ hμ⟩,
    fun ν hν ↦ huniq ν hν.1⟩

theorem exists_unique_marked_window_limit {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (p : VariationMark)
    (hTV : ∀ δ > 0, Tendsto (fun n ↦ (ρ n).real (badTVEvent (x n) a b R p δ)) atTop (𝓝 0)) :
    ∃! ν : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)),
      Tendsto (markedWindowLaw ρ x a b R) atTop (𝓝 ν) := by
  let : TopologicalSpace.MetrizableSpace (PointMeasure (MarkedWindow a b R)) :=
    markedPointMeasure_metrizableSpace a b hab R p
  obtain ⟨μ, hμ, _⟩ := exists_unique_joint_window_limit ρ x hbeta hlocal ha hab R p hTV
  refine ⟨canonicalMarkedWindowLaw p a b R μ, hμ.2, ?_⟩
  intro ν hν
  exact tendsto_nhds_unique hν hμ.2

end PerronWright.GraphWindowMarkedSpatialLimit
