import PerronWright.Probability.MarkedGlobalPointChartAtomicAssembly
import Mathlib.Topology.Compactness.Lindelof

/-!
# Every actual global point measure has actual compatible charts

Every compact restriction is already a literal finite integer Dirac
sum by the point-measure definition. All its labelled atoms belong to
the compact set; their literal preimages in the compact window give
actual finite point charts. Interior test integrals prove compatibility,
and Riesz uniqueness proves that assembly returns the original measure.
In particular the global vague space is a continuous image of the
already proved Polish chart space and is genuinely hereditarily Lindelöf.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.MarkedGlobalPointChartSurjective

open MarkedGlobalPointMeasureCharts MarkedGlobalPointChartAssembly MarkedGlobalPointChartAtomicAssembly
open ComponentGlobalMarkedProcess MarkedPositiveSizeSurplusExhaustion
open PositiveSizeSurplusExhaustion (lower upper lower_pos)
open ComponentWindowMarkedLaw
open scoped PerronWright.ComponentWindowMarkedLaw

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]
open LocallyFinitePointMeasureVague FinitePointMeasureCompact FiniteAtomicPointMeasure

def embeddedMeasure (m : ℕ) (η : Chart S m) : Measure (MarkedPositiveSizeSurplus S) :=
  ((η : FiniteMeasure (MarkedWindow S (lower m) (upper m) m)) :
    Measure (MarkedWindow S (lower m) (upper m) m)).map
      (markedPositiveWindowEmbedding (lower m) (upper m) m (lower_pos m))

theorem embeddedMeasure_integral (m : ℕ) (η : Chart S m)
    (f : C_c(MarkedPositiveSizeSurplus S, ℝ)) :
    (∫ z, f z ∂embeddedMeasure m η) = testIntegral m f η := by
  unfold embeddedMeasure testIntegral
  exact integral_map ((continuous_markedPositiveWindowEmbedding _ _ _ _).measurable).aemeasurable
    (show AEStronglyMeasurable (fun z ↦ f z) _ from
      f.continuous.measurable.aestronglyMeasurable)

theorem exists_chart_restriction (η : LocalPointMeasure (MarkedPositiveSizeSurplus S)) (m : ℕ) :
    ∃ ξ : Chart S m, embeddedMeasure m ξ =
      (η : Measure (MarkedPositiveSizeSurplus S)).restrict (window m) := by
  obtain ⟨n, x, hx⟩ := compact_restriction η (isCompact_window m)
  have hW := (isCompact_window (S := S) m).measurableSet
  have hout : (∑ i, Measure.dirac (x i)) (window m)ᶜ = 0 := by
    rw [← hx, Measure.restrict_apply hW.compl]
    simp
  rw [Measure.finsetSum_apply] at hout
  have hxW (i : Fin n) : x i ∈ window m := by
    have hle : Measure.dirac (x i) (window m)ᶜ ≤
        ∑ j : Fin n, Measure.dirac (x j) (window m)ᶜ :=
      Finset.single_le_sum (f := fun j : Fin n ↦ Measure.dirac (x j) (window m)ᶜ)
        (fun _ _ ↦ bot_le) (Finset.mem_univ i)
    rw [hout] at hle
    have hz := le_antisymm hle zero_le
    by_contra hi
    simp [Measure.dirac_apply', hW.compl, hi] at hz
  have hp : ∀ i : Fin n, ∃ z : MarkedWindow S (lower m) (upper m) m,
      markedPositiveWindowEmbedding (lower m) (upper m) m (lower_pos m) z = x i := by
    intro i
    have hi := hxW i
    rw [window, ← range_markedPositiveWindowEmbedding _ _ _ (lower_pos m)] at hi
    exact hi
  choose y hy using hp
  refine ⟨ofAtomsPoint y, ?_⟩
  rw [embeddedMeasure, ofAtomsPoint_val, ofAtoms_toMeasure,
    Measure.map_finset_sum' ((continuous_markedPositiveWindowEmbedding _ _ _ _).measurable).aemeasurable]
  simp only [Measure.map_dirac' ((continuous_markedPositiveWindowEmbedding _ _ _ _).measurable), hy]
  exact hx.symm

def charts (η : LocalPointMeasure (MarkedPositiveSizeSurplus S)) : ChartProduct S :=
  fun m ↦ (exists_chart_restriction η m).choose

theorem embeddedMeasure_charts (η : LocalPointMeasure (MarkedPositiveSizeSurplus S)) (m : ℕ) :
    embeddedMeasure m (charts η m) =
      (η : Measure (MarkedPositiveSizeSurplus S)).restrict (window m) :=
  (exists_chart_restriction η m).choose_spec

omit [CompactSpace S] in
theorem integral_restrict_test_eq (μ : Measure (MarkedPositiveSizeSurplus S))
    {K : Set (MarkedPositiveSizeSurplus S)} (hK : MeasurableSet K)
    (f : C_c(MarkedPositiveSizeSurplus S, ℝ)) (hf : tsupport f ⊆ K) :
    (∫ z, f z ∂μ.restrict K) = ∫ z, f z ∂μ := by
  rw [← integral_indicator hK]
  congr 1
  funext z
  by_cases hz : z ∈ K
  · simp [hz]
  · have hzero : f z = 0 := image_eq_zero_of_notMem_tsupport (fun hs ↦ hz (hf hs))
    simp [hz, hzero]

theorem charts_mem_compatible (η : LocalPointMeasure (MarkedPositiveSizeSurplus S)) :
    charts η ∈ compatible := by
  intro m n hmn f hf
  rw [← embeddedMeasure_integral, ← embeddedMeasure_integral,
    embeddedMeasure_charts, embeddedMeasure_charts,
    integral_restrict_test_eq _ (isCompact_window m).measurableSet f
      (hf.trans interior_subset),
    integral_restrict_test_eq _ (isCompact_window n).measurableSet f
      ((hf.trans interior_subset).trans (exhaustion.subset hmn))]

def compatibleCharts (η : LocalPointMeasure (MarkedPositiveSizeSurplus S)) : CompatibleCharts S :=
  ⟨charts η, charts_mem_compatible η⟩

/-- Actual pointwise right inverse: no abstract assembly-surjectivity
assumption is introduced. -/
theorem assemble_compatibleCharts (η : LocalPointMeasure (MarkedPositiveSizeSurplus S)) :
    assemble (compatibleCharts η) = η := by
  apply Subtype.ext
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ z, f z ∂assembledMeasure (compatibleCharts η)) = ∫ z, f z ∂(η : Measure _)
  rw [assembledMeasure_integral]
  change testIntegral (supportIndex f) f (charts η (supportIndex f)) = _
  rw [← embeddedMeasure_integral, embeddedMeasure_charts]
  exact integral_restrict_test_eq _ (isCompact_window _).measurableSet f
    ((support_subset_interior_index f).trans interior_subset)

theorem assemble_surjective : Function.Surjective (assemble (S := S)) :=
  fun η ↦ ⟨compatibleCharts η, assemble_compatibleCharts η⟩

instance globalPoint_hereditarilyLindelof :
    HereditarilyLindelofSpace (LocalPointMeasure (MarkedPositiveSizeSurplus S)) where
  isHereditarilyLindelof_univ U _ := by
    rw [← Set.image_preimage_eq (f := assemble) U assemble_surjective]
    exact (HereditarilyLindelofSpace.isLindelof _).image continuous_assemble

end PerronWright.MarkedGlobalPointChartSurjective


