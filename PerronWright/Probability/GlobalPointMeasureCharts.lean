import PerronWright.Probability.PositiveSizeSurplusExhaustion
import PerronWright.Probability.FinitePointMeasurePolish
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Closed interior-compatible actual compact point-measure charts

Compatibility is stated using actual compact-support integrals whose
support lies in the interior of the smaller chart. It is one closed
event, even though the test class is uncountable. The literal graph
charts satisfy it exactly. Genuine weak limits therefore give this
whole event probability one; no uncountable intersection of individual
almost-everywhere assertions is used.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported ENNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.GlobalPointMeasureCharts

open ComponentGlobalPointProcess ComponentWindowPointMeasures
open PositiveSizeSurplusExhaustion FinitePointMeasureCompact

instance canonicalWindow_metric (m : ℕ) : MetricSpace (SurplusWindow (lower m) (upper m) m) :=
  TopologicalSpace.metrizableSpaceMetric _

instance canonicalWindow_nonempty (m : ℕ) : Nonempty (SurplusWindow (lower m) (upper m) m) :=
  ⟨(⟨lower m, le_rfl, lower_le_upper m⟩, ⟨0, by omega⟩)⟩

abbrev Chart (m : ℕ) := PointMeasure (SurplusWindow (lower m) (upper m) m)

abbrev ChartProduct := (m : ℕ) → Chart m

def testIntegral (m : ℕ) (f : C_c(PositiveSizeSurplus, ℝ)) (η : Chart m) : ℝ :=
  ∫ z, f (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) z)
    ∂((η : FiniteMeasure (SurplusWindow (lower m) (upper m) m)) :
      Measure (SurplusWindow (lower m) (upper m) m))

theorem continuous_testIntegral (m : ℕ) (f : C_c(PositiveSizeSurplus, ℝ)) :
    Continuous (testIntegral m f) := by
  let g : C(SurplusWindow (lower m) (upper m) m, ℝ) :=
    ⟨fun z ↦ f (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) z),
      f.continuous.comp (continuous_positiveWindowEmbedding _ _ _ _)⟩
  exact (FiniteMeasure.continuous_integral_continuousMap g).comp continuous_val

/-- Actual integrals agree inside every inner chart. Full closed-window
restriction compatibility is deliberately not asserted to be closed. -/
def compatible : Set ChartProduct := {ζ | ∀ m n, m ≤ n → ∀ f : C_c(PositiveSizeSurplus, ℝ),
  tsupport f ⊆ interior (window m) → testIntegral m f (ζ m) = testIntegral n f (ζ n)}

theorem isClosed_compatible : IsClosed compatible := by
  have he : compatible = (⋂ m, ⋂ n, ⋂ (_h : m ≤ n), ⋂ f : C_c(PositiveSizeSurplus, ℝ),
    ⋂ (_hf : tsupport f ⊆ interior (window m)),
      {ζ : ChartProduct | testIntegral m f (ζ m) = testIntegral n f (ζ n)}) := by
    ext ζ
    simp [compatible]
  rw [he]
  exact isClosed_iInter (fun m ↦ isClosed_iInter (fun n ↦ isClosed_iInter (fun _ ↦
    isClosed_iInter (fun f ↦ isClosed_iInter (fun _ ↦ isClosed_eq
      ((continuous_testIntegral m f).comp (continuous_apply m))
      ((continuous_testIntegral n f).comp (continuous_apply n)))))))

def CompatibleCharts := {ζ : ChartProduct // ζ ∈ compatible}

instance : TopologicalSpace CompatibleCharts :=
  inferInstanceAs (TopologicalSpace {ζ : ChartProduct // ζ ∈ compatible})

instance : MeasurableSpace CompatibleCharts := borel CompatibleCharts

instance : BorelSpace CompatibleCharts := ⟨rfl⟩

/-- Polishness follows from actual proved compact point-measure
Polishness, the countable product, and the proved closed event. -/
instance compatibleCharts_polish : PolishSpace CompatibleCharts :=
  isClosed_compatible.polishSpace

instance : StandardBorelSpace CompatibleCharts := inferInstance

def sourceCharts {n : ℕ} (G : SimpleGraph (Fin n)) : ChartProduct :=
  fun m ↦ windowPointMeasure (lower m) (upper m) m 1 G

theorem sourceCharts_mem_compatible {n : ℕ} (G : SimpleGraph (Fin n)) :
    sourceCharts G ∈ compatible := by
  intro m k hmk f hf
  have hfm : tsupport f ⊆ window m := hf.trans interior_subset
  have hfk : tsupport f ⊆ window k := hfm.trans (exhaustion.subset hmk)
  exact (unmarkedProcess_integral_eq_window (lower m) (upper m) m (lower_pos m) G f hfm).symm.trans
    (unmarkedProcess_integral_eq_window (lower k) (upper k) k (lower_pos k) G f hfk)

def sourceCompatibleCharts {n : ℕ} (G : SimpleGraph (Fin n)) : CompatibleCharts :=
  ⟨sourceCharts G, sourceCharts_mem_compatible G⟩

theorem measurable_sourceCharts (n : ℕ) :
    Measurable (sourceCharts : SimpleGraph (Fin n) → ChartProduct) := measurable_of_finite _

theorem measurable_sourceCompatibleCharts (n : ℕ) :
    Measurable (sourceCompatibleCharts : SimpleGraph (Fin n) → CompatibleCharts) :=
  measurable_of_finite _

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

def chartLaw (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) : ProbabilityMeasure ChartProduct :=
  ⟨(AnnealedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map sourceCharts,
      Measure.isProbabilityMeasure_map (measurable_sourceCharts n).aemeasurable⟩

def compatibleChartLaw (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    ProbabilityMeasure CompatibleCharts :=
  ⟨(AnnealedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map sourceCompatibleCharts,
      Measure.isProbabilityMeasure_map (measurable_sourceCompatibleCharts n).aemeasurable⟩

theorem chartLaw_eval (M : CompactBJRModel S) (lambda : ℝ) (n m : ℕ) :
    (chartLaw M lambda n).map (continuous_apply m).measurable.aemeasurable =
      unmarkedWindowLaw M lambda (lower m) (upper m) m n := by
  apply Subtype.ext
  change ((AnnealedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map sourceCharts).map (fun ζ : ChartProduct ↦ ζ m) = _
  rw [Measure.map_map (continuous_apply m).measurable (measurable_sourceCharts n)]
  rfl

theorem chartLaw_compatible_eq_one (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    (chartLaw M lambda n : Measure ChartProduct) compatible = 1 := by
  change ((AnnealedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map sourceCharts) compatible = 1
  rw [Measure.map_apply (measurable_sourceCharts n) isClosed_compatible.measurableSet]
  have he : sourceCharts ⁻¹' compatible = (Set.univ : Set (SimpleGraph (Fin n))) :=
    Set.eq_univ_of_forall (fun G ↦ sourceCharts_mem_compatible G)
  rw [he, measure_univ]

/-- Correct closed-event Portmanteau proves simultaneous compatibility
for the entire uncountable test class under any genuine weak limit. -/
theorem ae_compatible_of_tendsto (M : CompactBJRModel S) (lambda : ℝ)
    (N : ℕ → ℕ) (ν : ProbabilityMeasure ChartProduct)
    (hν : Tendsto (fun k ↦ chartLaw M lambda (N k)) atTop (𝓝 ν)) :
    ∀ᵐ ζ : ChartProduct ∂(ν : Measure ChartProduct), ζ ∈ compatible := by
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hν isClosed_compatible
  simp only [chartLaw_compatible_eq_one, limsup_const] at h
  apply ae_iff.mpr
  change (ν : Measure ChartProduct) compatibleᶜ = 0
  exact (prob_compl_eq_zero_iff isClosed_compatible.measurableSet).mpr
    (le_antisymm (prob_le_one) h)

end PerronWright.GlobalPointMeasureCharts
