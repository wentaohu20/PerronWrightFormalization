import PerronWright.Probability.GlobalPointChartAssembly
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integer atomicity and vague continuity of actual chart assembly

Compactly supported cutoffs equal to one on a given compact set compare
the assembled Riesz measure to one literal finite integer chart measure.
The comparison is an actual equality of weighted measures, proved by
compact-support integral determination. Every compact restriction is
therefore a genuine finite integer Dirac sum. The resulting assembly map
lands in the actual locally finite point-measure space and is vague
continuous.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GlobalPointChartAtomicAssembly

open GlobalPointMeasureCharts GlobalPointChartAssembly ComponentGlobalPointProcess
open PositiveSizeSurplusExhaustion LocallyFinitePointMeasureVague
open FinitePointMeasureCompact

def chartMeasure (ξ : CompatibleCharts) (m : ℕ) : Measure PositiveSizeSurplus :=
  (((ξ.val m : FiniteMeasure (SurplusWindow (lower m) (upper m) m)) :
    Measure (SurplusWindow (lower m) (upper m) m)).map
      (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m)))

instance chartMeasure_finite (ξ : CompatibleCharts) (m : ℕ) :
    IsFiniteMeasure (chartMeasure ξ m) := by unfold chartMeasure; infer_instance

theorem chartMeasure_integral (ξ : CompatibleCharts) (m : ℕ)
    (f : C_c(PositiveSizeSurplus, ℝ)) :
    (∫ z, f z ∂chartMeasure ξ m) = testIntegral m f (ξ.val m) := by
  unfold chartMeasure testIntegral
  exact integral_map (measurable_positiveWindowEmbedding _ _ _ _).aemeasurable
    (show AEStronglyMeasurable (fun z ↦ f z) _ from
      f.continuous.measurable.aestronglyMeasurable)

theorem chartMeasure_isLocalPoint (ξ : CompatibleCharts) (m : ℕ) :
    IsLocallyFinitePointMeasure (chartMeasure ξ m) := by
  obtain ⟨n, x, hx⟩ := (ξ.val m).property
  rw [chartMeasure, hx, FiniteAtomicPointMeasure.ofAtoms_toMeasure,
    Measure.map_finset_sum' (measurable_positiveWindowEmbedding _ _ _ _).aemeasurable]
  simp only [Measure.map_dirac' (measurable_positiveWindowEmbedding _ _ _ _)]
  exact isLocallyFinitePointMeasure_sum_dirac _

theorem weighted_measures_eq (ξ : CompatibleCharts) (m : ℕ)
    (χ : C_c(PositiveSizeSurplus, ℝ)) (hχ : ∀ z, 0 ≤ χ z)
    (hs : tsupport χ ⊆ interior (window m)) :
    (assembledMeasure ξ).withDensity (fun z ↦ ENNReal.ofReal (χ z)) =
      (chartMeasure ξ m).withDensity (fun z ↦ ENNReal.ofReal (χ z)) := by
  let : IsLocallyFiniteMeasure ((assembledMeasure ξ).withDensity
      (fun z ↦ ENNReal.ofReal (χ z))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal χ.continuous
  let : IsLocallyFiniteMeasure ((chartMeasure ξ m).withDensity
      (fun z ↦ ENNReal.ofReal (χ z))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal χ.continuous
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hmeas : Measurable (fun z ↦ ENNReal.ofReal (χ z)) :=
    ENNReal.continuous_ofReal.measurable.comp χ.continuous.measurable
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
      (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul hmeas
      (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hχ _), smul_eq_mul]
  have hprod : tsupport (χ * f) ⊆ interior (window m) := tsupport_mul_subset_left.trans hs
  calc
    (∫ z, χ z * f z ∂assembledMeasure ξ) = value ξ (χ * f) := assembledMeasure_integral ξ (χ * f)
    _ = testIntegral m (χ * f) (ξ.val m) := value_eq_coordinate ξ (χ * f) m hprod
    _ = ∫ z, χ z * f z ∂chartMeasure ξ m := (chartMeasure_integral ξ m (χ * f)).symm

theorem restrict_withDensity_eq_self_of_eq_one (μ : Measure PositiveSizeSurplus)
    {K : Set PositiveSizeSurplus} (hK : MeasurableSet K)
    (χ : C_c(PositiveSizeSurplus, ℝ)) (hχ : Set.EqOn χ 1 K) :
    ((μ.withDensity (fun z ↦ ENNReal.ofReal (χ z))).restrict K) = μ.restrict K := by
  rw [restrict_withDensity hK]
  have h : (fun z ↦ ENNReal.ofReal (χ z)) =ᵐ[μ.restrict K] (1 : PositiveSizeSurplus → ℝ≥0∞) :=
    (ae_restrict_mem hK).mono (fun z hz ↦ by simp [hχ hz])
  rw [withDensity_congr_ae h, withDensity_one]

/-- Every compact restriction of the actual assembled measure is the
restriction of one actual finite integer chart measure. -/
theorem assembledMeasure_restrict_eq_chart (ξ : CompatibleCharts)
    {K : Set PositiveSizeSurplus} (hK : IsCompact K) :
    ∃ m, (assembledMeasure ξ).restrict K = (chartMeasure ξ m).restrict K := by
  obtain ⟨k, hk⟩ := exists_compact_subset_window hK
  let m := k + 1
  have hKm : K ⊆ interior (window m) := hk.trans (window_subset_interior_succ k)
  obtain ⟨g, hg, hgcompact, hgs, hgnonneg⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_interior hKm
  let χ : C_c(PositiveSizeSurplus, ℝ) := ⟨g, hgcompact⟩
  have he := congrArg (fun μ : Measure PositiveSizeSurplus ↦ μ.restrict K)
    (weighted_measures_eq ξ m χ (fun z ↦ (hgnonneg z).1) hgs)
  rw [restrict_withDensity_eq_self_of_eq_one _ hK.measurableSet χ hg,
    restrict_withDensity_eq_self_of_eq_one _ hK.measurableSet χ hg] at he
  exact ⟨m, he⟩

theorem assembledMeasure_isLocalPoint (ξ : CompatibleCharts) :
    IsLocallyFinitePointMeasure (assembledMeasure ξ) := by
  refine ⟨inferInstance, ?_⟩
  intro K hK
  obtain ⟨m, hm⟩ := assembledMeasure_restrict_eq_chart ξ hK
  rw [hm]
  exact (chartMeasure_isLocalPoint ξ m).2 K hK

/-- Actual integer-point assembly, with no unproved representation
condition attached to the interface. -/
def assemble (ξ : CompatibleCharts) : LocalPointMeasure PositiveSizeSurplus :=
  ⟨assembledMeasure ξ, assembledMeasure_isLocalPoint ξ⟩

theorem continuous_assemble : Continuous assemble := by
  apply isInducing_testEncoding.continuous_iff.mpr
  apply continuous_pi
  intro f
  exact continuous_assembledMeasure_integral f

theorem assemble_sourceCompatibleCharts {n : ℕ} (G : SimpleGraph (Fin n)) :
    assemble (sourceCompatibleCharts G) = unmarkedProcess G :=
  Subtype.ext (assembledMeasure_sourceCompatibleCharts G)

end PerronWright.GlobalPointChartAtomicAssembly
