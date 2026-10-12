import PerronWright.Probability.CountableTVWindowSizeRescaling
import PerronWright.Probability.GraphWindowMarkedSpatialLimit

/-! # Actual graph probabilities under TV-marked window dilation

Both laws below are literal graph pushforwards. Their map identities
keep the selected actual components and their empirical marks. Full
weak limits follow by continuous mapping of genuine unscaled source
limits, with canonical marking commuting exactly with size dilation.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GraphWindowScaledTVLaw

open CountableVariationMarks CountableComponentWindowLaw CountableTVWindowConvergence
open CountableTVWindowSizeRescaling WindowSizeRescaling
open GraphWindowSource GraphWindowMarkTransfer GraphWindowMarkedSpatialLimit
open ComponentWindowPointMeasures FinitePointMeasureCompact FinitePointMeasureMarking

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]
variable (x : (n : ℕ) → Fin (n+1) → ℕ)

def scaledUnmarkedWindowLaw (a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ) :
    ProbabilityMeasure (PointMeasure (SurplusWindow a b R)) :=
  ⟨(ρ n).map (windowPointMeasure a b R c),
    Measure.isProbabilityMeasure_map (measurable_windowPointMeasure a b R c (n+1)).aemeasurable⟩

def scaledMarkedWindowLaw (a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ) :
    ProbabilityMeasure (PointMeasure (MarkedWindow a b R)) :=
  ⟨(ρ n).map (fun G ↦ scaledMarkedWindowPointMeasure (x n) G a b R c),
    Measure.isProbabilityMeasure_map (measurable_scaledMarkedWindowPointMeasure _ a b R c).aemeasurable⟩

theorem scaledUnmarkedWindowLaw_integral (a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ)
    {F : PointMeasure (SurplusWindow a b R) → ℝ} (hF : Measurable F) :
    (∫ η, F η ∂(scaledUnmarkedWindowLaw ρ a b R c n : Measure _)) =
      ∫ G, F (windowPointMeasure a b R c G) ∂ρ n :=
  integral_map (measurable_windowPointMeasure a b R c (n+1)).aemeasurable hF.aestronglyMeasurable

theorem scaledMarkedWindowLaw_integral (a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ)
    {F : PointMeasure (MarkedWindow a b R) → ℝ} (hF : Measurable F) :
    (∫ η, F η ∂(scaledMarkedWindowLaw ρ x a b R c n : Measure _)) =
      ∫ G, F (scaledMarkedWindowPointMeasure (x n) G a b R c) ∂ρ n :=
  integral_map (measurable_scaledMarkedWindowPointMeasure _ a b R c).aemeasurable hF.aestronglyMeasurable

theorem scaledUnmarkedWindowLaw_eq_map (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    scaledUnmarkedWindowLaw ρ a b R c n =
      (windowLaw ρ (a/c) (b/c) R n).map
        (continuous_mapPoint (windowScaleMap a b R hc)
          (continuous_windowScaleMap a b R hc)).measurable.aemeasurable := by
  apply Subtype.ext
  change (ρ n).map (windowPointMeasure a b R c) =
    ((ρ n).map (windowPointMeasure (a/c) (b/c) R 1)).map
      (mapPoint (windowScaleMap a b R hc) (continuous_windowScaleMap a b R hc).measurable)
  rw [Measure.map_map (continuous_mapPoint _ (continuous_windowScaleMap a b R hc)).measurable
    (measurable_windowPointMeasure (a/c) (b/c) R 1 (n+1))]
  congr 1
  exact funext (windowPointMeasure_eq_map a b R hc)

theorem scaledMarkedWindowLaw_eq_map (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    scaledMarkedWindowLaw ρ x a b R c n =
      (markedWindowLaw ρ x (a/c) (b/c) R n).map
        (continuous_mapPoint (markedWindowScaleMap a b R hc)
          (continuous_markedWindowScaleMap a b R hc)).measurable.aemeasurable := by
  apply Subtype.ext
  change (ρ n).map (fun G ↦ scaledMarkedWindowPointMeasure (x n) G a b R c) =
    ((ρ n).map (fun G ↦ markedWindowPointMeasure (x n) G (a/c) (b/c) R)).map
      (mapPoint (markedWindowScaleMap a b R hc) (continuous_markedWindowScaleMap a b R hc).measurable)
  rw [Measure.map_map (continuous_mapPoint _ (continuous_markedWindowScaleMap a b R hc)).measurable
    (measurable_markedWindowPointMeasure (x n) (a/c) (b/c) R)]
  congr 1
  exact funext (scaledMarkedWindowPointMeasure_eq_map a b R hc (x n))

theorem scaledMarkedWindowLaw_forget (a b : ℝ) (R : ℕ) (c : ℝ) (n : ℕ) :
    (scaledMarkedWindowLaw ρ x a b R c n).map
      (continuous_mapPoint Prod.fst continuous_fst).measurable.aemeasurable =
      scaledUnmarkedWindowLaw ρ a b R c n := by
  apply Subtype.ext
  change ((ρ n).map (fun G ↦ scaledMarkedWindowPointMeasure (x n) G a b R c)).map
    (mapPoint Prod.fst measurable_fst) = (ρ n).map (windowPointMeasure a b R c)
  rw [Measure.map_map (continuous_mapPoint Prod.fst continuous_fst).measurable
    (measurable_scaledMarkedWindowPointMeasure _ a b R c)]
  congr 1
  exact funext (fun G ↦ scaledMarkedWindowPointMeasure_forget (x n) G a b R c)

theorem scaled_joint_window_limit_of_joint_limit
    (a b : ℝ) (hab : a ≤ b) (R : ℕ) {c : ℝ} (hc : 0 < c) (p : VariationMark)
    (μ : ProbabilityMeasure (PointMeasure (SurplusWindow (a/c) (b/c) R)))
    (hμ : Tendsto (windowLaw ρ (a/c) (b/c) R) atTop (𝓝 μ))
    (hmarked : Tendsto (markedWindowLaw ρ x (a/c) (b/c) R) atTop
      (𝓝 (canonicalMarkedWindowLaw p (a/c) (b/c) R μ))) :
    ∃! ν : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (fun n ↦ scaledUnmarkedWindowLaw ρ a b R c n) atTop (𝓝 ν) ∧
      Tendsto (fun n ↦ scaledMarkedWindowLaw ρ x a b R c n) atTop
        (𝓝 (canonicalMarkedWindowLaw p a b R ν)) := by
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  let : MetricSpace (PointMeasure (SurplusWindow a b R)) := TopologicalSpace.metrizableSpaceMetric _
  let ν := μ.map (continuous_mapPoint (windowScaleMap a b R hc)
    (continuous_windowScaleMap a b R hc)).measurable.aemeasurable
  have hν : Tendsto (fun n ↦ scaledUnmarkedWindowLaw ρ a b R c n) atTop (𝓝 ν) := by
    simpa only [scaledUnmarkedWindowLaw_eq_map ρ a b R hc, ν] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (windowLaw ρ (a/c) (b/c) R) μ hμ
        (continuous_mapPoint _ (continuous_windowScaleMap a b R hc))
  have hνMarked : Tendsto (fun n ↦ scaledMarkedWindowLaw ρ x a b R c n) atTop
      (𝓝 (canonicalMarkedWindowLaw p a b R ν)) := by
    simpa only [scaledMarkedWindowLaw_eq_map ρ x a b R hc,
      map_canonicalMarkedWindowLaw a b R hc p, ν] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (markedWindowLaw ρ x (a/c) (b/c) R)
        (canonicalMarkedWindowLaw p (a/c) (b/c) R μ) hmarked
        (continuous_mapPoint _ (continuous_markedWindowScaleMap a b R hc))
  exact ⟨ν, ⟨hν, hνMarked⟩, fun θ hθ ↦ tendsto_nhds_unique hθ.1 hν⟩

theorem scaled_marked_window_limit_of_joint_limit
    (a b : ℝ) (hab : a ≤ b) (R : ℕ) {c : ℝ} (hc : 0 < c) (p : VariationMark)
    (μ : ProbabilityMeasure (PointMeasure (SurplusWindow (a/c) (b/c) R)))
    (hμ : Tendsto (windowLaw ρ (a/c) (b/c) R) atTop (𝓝 μ))
    (hmarked : Tendsto (markedWindowLaw ρ x (a/c) (b/c) R) atTop
      (𝓝 (canonicalMarkedWindowLaw p (a/c) (b/c) R μ))) :
    ∃! ν : ProbabilityMeasure (PointMeasure (MarkedWindow a b R)),
      Tendsto (fun n ↦ scaledMarkedWindowLaw ρ x a b R c n) atTop (𝓝 ν) := by
  let : TopologicalSpace.MetrizableSpace (PointMeasure (MarkedWindow a b R)) :=
    markedPointMeasure_metrizableSpace a b hab R p
  obtain ⟨ν, hν, _⟩ := scaled_joint_window_limit_of_joint_limit ρ x a b hab R hc p μ hμ hmarked
  exact ⟨canonicalMarkedWindowLaw p a b R ν, hν.2, fun θ hθ ↦ tendsto_nhds_unique hθ hν.2⟩

end PerronWright.GraphWindowScaledTVLaw
