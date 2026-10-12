import PerronWright.Probability.GlobalPointChartAtomicAssembly
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

namespace PerronWright.GlobalPointChartSurjective

open GlobalPointMeasureCharts GlobalPointChartAssembly GlobalPointChartAtomicAssembly
open ComponentGlobalPointProcess PositiveSizeSurplusExhaustion
open LocallyFinitePointMeasureVague FinitePointMeasureCompact FiniteAtomicPointMeasure

def embeddedMeasure (m : ℕ) (η : Chart m) : Measure PositiveSizeSurplus :=
  ((η : FiniteMeasure (SurplusWindow (lower m) (upper m) m)) :
    Measure (SurplusWindow (lower m) (upper m) m)).map
      (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m))

theorem embeddedMeasure_integral (m : ℕ) (η : Chart m)
    (f : C_c(PositiveSizeSurplus, ℝ)) :
    (∫ z, f z ∂embeddedMeasure m η) = testIntegral m f η := by
  unfold embeddedMeasure testIntegral
  exact integral_map (measurable_positiveWindowEmbedding _ _ _ _).aemeasurable
    (show AEStronglyMeasurable (fun z ↦ f z) _ from
      f.continuous.measurable.aestronglyMeasurable)

theorem exists_chart_restriction (η : LocalPointMeasure PositiveSizeSurplus) (m : ℕ) :
    ∃ ξ : Chart m, embeddedMeasure m ξ =
      (η : Measure PositiveSizeSurplus).restrict (window m) := by
  obtain ⟨n, x, hx⟩ := compact_restriction η (isCompact_window m)
  have hW := (isCompact_window m).measurableSet
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
  have hp : ∀ i : Fin n, ∃ z : SurplusWindow (lower m) (upper m) m,
      positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) z = x i := by
    intro i
    have hi := hxW i
    rw [window, ← range_positiveWindowEmbedding _ _ _ (lower_pos m)] at hi
    exact hi
  choose y hy using hp
  refine ⟨ofAtomsPoint y, ?_⟩
  rw [embeddedMeasure, ofAtomsPoint_val, ofAtoms_toMeasure,
    Measure.map_finset_sum' (measurable_positiveWindowEmbedding _ _ _ _).aemeasurable]
  simp only [Measure.map_dirac' (measurable_positiveWindowEmbedding _ _ _ _), hy]
  exact hx.symm

def charts (η : LocalPointMeasure PositiveSizeSurplus) : ChartProduct :=
  fun m ↦ (exists_chart_restriction η m).choose

theorem embeddedMeasure_charts (η : LocalPointMeasure PositiveSizeSurplus) (m : ℕ) :
    embeddedMeasure m (charts η m) =
      (η : Measure PositiveSizeSurplus).restrict (window m) :=
  (exists_chart_restriction η m).choose_spec

theorem integral_restrict_test_eq (μ : Measure PositiveSizeSurplus)
    {K : Set PositiveSizeSurplus} (hK : MeasurableSet K)
    (f : C_c(PositiveSizeSurplus, ℝ)) (hf : tsupport f ⊆ K) :
    (∫ z, f z ∂μ.restrict K) = ∫ z, f z ∂μ := by
  rw [← integral_indicator hK]
  congr 1
  funext z
  by_cases hz : z ∈ K
  · simp [hz]
  · have hzero : f z = 0 := image_eq_zero_of_notMem_tsupport (fun hs ↦ hz (hf hs))
    simp [hz, hzero]

theorem charts_mem_compatible (η : LocalPointMeasure PositiveSizeSurplus) :
    charts η ∈ compatible := by
  intro m n hmn f hf
  rw [← embeddedMeasure_integral, ← embeddedMeasure_integral,
    embeddedMeasure_charts, embeddedMeasure_charts,
    integral_restrict_test_eq _ (isCompact_window m).measurableSet f
      (hf.trans interior_subset),
    integral_restrict_test_eq _ (isCompact_window n).measurableSet f
      ((hf.trans interior_subset).trans (exhaustion.subset hmn))]

def compatibleCharts (η : LocalPointMeasure PositiveSizeSurplus) : CompatibleCharts :=
  ⟨charts η, charts_mem_compatible η⟩

/-- Actual pointwise right inverse: no abstract assembly-surjectivity
assumption is introduced. -/
theorem assemble_compatibleCharts (η : LocalPointMeasure PositiveSizeSurplus) :
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

theorem assemble_surjective : Function.Surjective assemble :=
  fun η ↦ ⟨compatibleCharts η, assemble_compatibleCharts η⟩

instance globalPoint_hereditarilyLindelof :
    HereditarilyLindelofSpace (LocalPointMeasure PositiveSizeSurplus) where
  isHereditarilyLindelof_univ U _ := by
    rw [← Set.image_preimage_eq (f := assemble) U assemble_surjective]
    exact (HereditarilyLindelofSpace.isLindelof _).image continuous_assemble

end PerronWright.GlobalPointChartSurjective
