import PerronWright.Probability.MarkedPositiveSizeSurplusExhaustion
import PerronWright.Probability.FinitePointMeasurePolishEmpty
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! # Actual empirical-marked compact charts and closed interior compatibility

Every chart is a finite integer point measure on the literal compact
size/surplus/weak-probability-mark window. Compatibility is one closed
event of compact-support integral identities, not closed-window
restriction equality.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported ENNReal
open scoped PerronWright.ComponentWindowMarkedLaw

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.MarkedGlobalPointMeasureCharts

open ComponentGlobalPointProcess ComponentGlobalMarkedProcess ComponentWindowPointMeasures
open ComponentWindowMarkedLaw MarkedPositiveSizeSurplusExhaustion FinitePointMeasureCompact
open PositiveSizeSurplusExhaustion (lower upper lower_pos lower_le_upper)

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

abbrev Chart (S : Type*) [MeasurableSpace S] [MetricSpace S]
    [CompactSpace S] [BorelSpace S] (m : ℕ) :=
  PointMeasure (MarkedWindow S (lower m) (upper m) m)

instance chart_polish (m : ℕ) : PolishSpace (Chart S m) :=
  FinitePointMeasurePolishEmpty.pointMeasure_polishSpace

abbrev ChartProduct (S : Type*) [MeasurableSpace S] [MetricSpace S]
    [CompactSpace S] [BorelSpace S] := (m : ℕ) → Chart S m

def testIntegral (m : ℕ) (f : C_c(MarkedPositiveSizeSurplus S, ℝ)) (η : Chart S m) : ℝ :=
  ∫ z, f (markedPositiveWindowEmbedding (lower m) (upper m) m (lower_pos m) z)
    ∂((η : FiniteMeasure (MarkedWindow S (lower m) (upper m) m)) : Measure _)

theorem continuous_testIntegral (m : ℕ) (f : C_c(MarkedPositiveSizeSurplus S, ℝ)) :
    Continuous (testIntegral m f) := by
  let g : C(MarkedWindow S (lower m) (upper m) m, ℝ) :=
    ⟨fun z ↦ f (markedPositiveWindowEmbedding (lower m) (upper m) m (lower_pos m) z),
      f.continuous.comp (continuous_markedPositiveWindowEmbedding _ _ _ _)⟩
  exact (FiniteMeasure.continuous_integral_continuousMap g).comp continuous_val

def compatible : Set (ChartProduct S) := {ζ | ∀ m n, m ≤ n →
  ∀ f : C_c(MarkedPositiveSizeSurplus S, ℝ), tsupport f ⊆ interior (window m) →
    testIntegral m f (ζ m) = testIntegral n f (ζ n)}

theorem isClosed_compatible : IsClosed (compatible (S := S)) := by
  have he : compatible (S := S) =
      (⋂ m, ⋂ n, ⋂ (_h : m ≤ n), ⋂ f : C_c(MarkedPositiveSizeSurplus S, ℝ),
        ⋂ (_hf : tsupport f ⊆ interior (window m)),
          {ζ : ChartProduct S | testIntegral m f (ζ m) = testIntegral n f (ζ n)}) := by
    ext ζ
    simp [compatible]
  rw [he]
  exact isClosed_iInter (fun m ↦ isClosed_iInter (fun n ↦ isClosed_iInter (fun _ ↦
    isClosed_iInter (fun f ↦ isClosed_iInter (fun _ ↦ isClosed_eq
      ((continuous_testIntegral m f).comp (continuous_apply m))
      ((continuous_testIntegral n f).comp (continuous_apply n)))))))

def CompatibleCharts (S : Type*) [MeasurableSpace S] [MetricSpace S]
    [CompactSpace S] [BorelSpace S] := {ζ : ChartProduct S // ζ ∈ compatible}

instance : TopologicalSpace (CompatibleCharts S) :=
  inferInstanceAs (TopologicalSpace {ζ : ChartProduct S // ζ ∈ compatible})
instance : MeasurableSpace (CompatibleCharts S) := borel (CompatibleCharts S)
instance : BorelSpace (CompatibleCharts S) := ⟨rfl⟩
instance compatibleCharts_polish : PolishSpace (CompatibleCharts S) :=
  isClosed_compatible.polishSpace
instance : StandardBorelSpace (CompatibleCharts S) := inferInstance

def sourceCharts {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) : ChartProduct S :=
  fun m ↦ markedWindowPointMeasure x G (lower m) (upper m) m

theorem sourceCharts_mem_compatible {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) :
    sourceCharts x G ∈ compatible := by
  intro m k hmk f hf
  have hfm : tsupport f ⊆ window m := hf.trans interior_subset
  have hfk : tsupport f ⊆ window k := hfm.trans (exhaustion.subset hmk)
  exact (markedProcess_integral_eq_window (lower m) (upper m) m (lower_pos m) x G f hfm).symm.trans
    (markedProcess_integral_eq_window (lower k) (upper k) k (lower_pos k) x G f hfk)

def sourceCompatibleCharts {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) :
    CompatibleCharts S := ⟨sourceCharts x G, sourceCharts_mem_compatible x G⟩

theorem continuous_sourceCharts_slice {n : ℕ} (G : SimpleGraph (Fin n)) :
    Continuous (fun x : Fin n → S ↦ sourceCharts x G) :=
  continuous_pi (fun m ↦ continuous_markedWindowPointMeasure_slice G (lower m) (upper m) m)

theorem continuous_sourceCompatibleCharts_slice {n : ℕ} (G : SimpleGraph (Fin n)) :
    Continuous (fun x : Fin n → S ↦ sourceCompatibleCharts x G) :=
  (continuous_sourceCharts_slice G).subtype_mk _

theorem measurable_sourceCharts (n : ℕ) :
    Measurable (fun p : AnnealedTypedGraph.State S n ↦
      sourceCharts p.1 (AnnealedTypedGraph.graph p)) :=
  measurable_from_prod_countable_left (fun ea ↦
    (continuous_sourceCharts_slice (AnnealedGraph.toGraph ea)).measurable)

theorem measurable_sourceCompatibleCharts (n : ℕ) :
    Measurable (fun p : AnnealedTypedGraph.State S n ↦
      sourceCompatibleCharts p.1 (AnnealedTypedGraph.graph p)) :=
  measurable_from_prod_countable_left (fun ea ↦
    (continuous_sourceCompatibleCharts_slice (AnnealedGraph.toGraph ea)).measurable)

def chartLaw (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    ProbabilityMeasure (ChartProduct S) :=
  (typedProbability M lambda n).map (measurable_sourceCharts n).aemeasurable

def compatibleChartLaw (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    ProbabilityMeasure (CompatibleCharts S) :=
  (typedProbability M lambda n).map (measurable_sourceCompatibleCharts n).aemeasurable

theorem chartLaw_eval (M : CompactBJRModel S) (lambda : ℝ) (n m : ℕ) :
    (chartLaw M lambda n).map (continuous_apply m).measurable.aemeasurable =
      markedWindowLaw M lambda (lower m) (upper m) m n := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [chartLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_apply m).measurable (measurable_sourceCharts n)]
  rfl

theorem chartLaw_compatible_eq_one (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    (chartLaw M lambda n : Measure (ChartProduct S)) compatible = 1 := by
  simp only [chartLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (measurable_sourceCharts n) isClosed_compatible.measurableSet]
  have he : (fun p : AnnealedTypedGraph.State S n ↦
      sourceCharts p.1 (AnnealedTypedGraph.graph p)) ⁻¹' compatible = Set.univ :=
    Set.eq_univ_of_forall (fun p ↦ sourceCharts_mem_compatible p.1 (AnnealedTypedGraph.graph p))
  rw [he, measure_univ]

theorem ae_compatible_of_tendsto (M : CompactBJRModel S) (lambda : ℝ)
    (N : ℕ → ℕ) (ν : ProbabilityMeasure (ChartProduct S))
    (hν : Tendsto (fun k ↦ chartLaw M lambda (N k)) atTop (𝓝 ν)) :
    ∀ᵐ ζ : ChartProduct S ∂(ν : Measure (ChartProduct S)), ζ ∈ compatible := by
  have h := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hν isClosed_compatible
  simp only [chartLaw_compatible_eq_one, limsup_const] at h
  apply ae_iff.mpr
  change (ν : Measure (ChartProduct S)) compatibleᶜ = 0
  exact (prob_compl_eq_zero_iff isClosed_compatible.measurableSet).mpr
    (le_antisymm prob_le_one h)

end PerronWright.MarkedGlobalPointMeasureCharts
