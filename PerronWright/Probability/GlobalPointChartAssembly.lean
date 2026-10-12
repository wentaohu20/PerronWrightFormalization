import PerronWright.Probability.GlobalPointMeasureCharts
import Mathlib.Topology.UrysohnsLemma

/-!
# A genuine locally finite measure assembled from interior-compatible charts

The compatible chart integrals define an actual positive real-linear
functional on `C_c`. Riesz--Markov constructs its actual Borel measure.
Its compact finiteness, all test integrals, and exact recovery of the
finite graph source are proved. Integer atomicity for arbitrary chart
inputs and the final global point-law assembly are separate remaining
steps, not assumed interfaces in this file.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GlobalPointChartAssembly

open GlobalPointMeasureCharts PositiveSizeSurplusExhaustion ComponentGlobalPointProcess

def supportIndex (f : C_c(PositiveSizeSurplus, ℝ)) : ℕ :=
  (exists_support_subset_window f).choose + 1

theorem support_subset_interior_index (f : C_c(PositiveSizeSurplus, ℝ)) :
    tsupport f ⊆ interior (window (supportIndex f)) :=
  (exists_support_subset_window f).choose_spec.trans
    (window_subset_interior_succ (exists_support_subset_window f).choose)

theorem support_subset_interior_of_index_le (f : C_c(PositiveSizeSurplus, ℝ))
    {m : ℕ} (h : supportIndex f ≤ m) : tsupport f ⊆ interior (window m) :=
  (support_subset_interior_index f).trans (interior_mono (exhaustion.subset h))

def value (ξ : CompatibleCharts) (f : C_c(PositiveSizeSurplus, ℝ)) : ℝ :=
  testIntegral (supportIndex f) f (ξ.val (supportIndex f))

/-- The construction does not depend on the selected covering chart. -/
theorem value_eq_coordinate (ξ : CompatibleCharts) (f : C_c(PositiveSizeSurplus, ℝ))
    (m : ℕ) (hf : tsupport f ⊆ interior (window m)) :
    value ξ f = testIntegral m f (ξ.val m) := by
  have hm := ξ.property m (max m (supportIndex f)) (le_max_left _ _) f hf
  have hi := ξ.property (supportIndex f) (max m (supportIndex f)) (le_max_right _ _) f
    (support_subset_interior_index f)
  exact hi.trans hm.symm

theorem test_integrable (m : ℕ) (f : C_c(PositiveSizeSurplus, ℝ)) (η : Chart m) :
    Integrable (fun z ↦ f (positiveWindowEmbedding (lower m) (upper m) m (lower_pos m) z))
      ((η : FiniteMeasure (FinitePointMeasureCompact.SurplusWindow (lower m) (upper m) m)) :
        Measure (FinitePointMeasureCompact.SurplusWindow (lower m) (upper m) m)) := by
  exact (f.continuous.comp (continuous_positiveWindowEmbedding _ _ _ _)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem value_add (ξ : CompatibleCharts) (f g : C_c(PositiveSizeSurplus, ℝ)) :
    value ξ (f + g) = value ξ f + value ξ g := by
  let m := max (supportIndex f) (max (supportIndex g) (supportIndex (f + g)))
  have hf : supportIndex f ≤ m := le_max_left _ _
  have hg : supportIndex g ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hfg : supportIndex (f + g) ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  rw [value_eq_coordinate ξ (f + g) m (support_subset_interior_of_index_le _ hfg),
    value_eq_coordinate ξ f m (support_subset_interior_of_index_le _ hf),
    value_eq_coordinate ξ g m (support_subset_interior_of_index_le _ hg)]
  exact integral_add (test_integrable m f _) (test_integrable m g _)

theorem value_smul (ξ : CompatibleCharts) (c : ℝ) (f : C_c(PositiveSizeSurplus, ℝ)) :
    value ξ (c • f) = c • value ξ f := by
  let m := max (supportIndex f) (supportIndex (c • f))
  rw [value_eq_coordinate ξ (c • f) m
      (support_subset_interior_of_index_le _ (le_max_right _ _)),
    value_eq_coordinate ξ f m (support_subset_interior_of_index_le _ (le_max_left _ _))]
  exact integral_smul c _

theorem value_monotone (ξ : CompatibleCharts) : Monotone (value ξ) := by
  intro f g hfg
  let m := max (supportIndex f) (supportIndex g)
  rw [value_eq_coordinate ξ f m (support_subset_interior_of_index_le _ (le_max_left _ _)),
    value_eq_coordinate ξ g m (support_subset_interior_of_index_le _ (le_max_right _ _))]
  exact integral_mono (test_integrable m f _) (test_integrable m g _) (fun z ↦ hfg _)

/-- The actual positive linear functional, proved from the literal
compatibility equalities rather than assumed as an interface. -/
def functional (ξ : CompatibleCharts) : C_c(PositiveSizeSurplus, ℝ) →ₚ[ℝ] ℝ where
  toFun := value ξ
  map_add' := value_add ξ
  map_smul' := value_smul ξ
  monotone' := value_monotone ξ

@[simp] theorem functional_apply (ξ : CompatibleCharts) (f : C_c(PositiveSizeSurplus, ℝ)) :
    functional ξ f = value ξ f := rfl

/-- Actual Riesz--Markov assembly on the paper's positive ground space. -/
def assembledMeasure (ξ : CompatibleCharts) : Measure PositiveSizeSurplus :=
  RealRMK.rieszMeasure (functional ξ)

instance assembledMeasure_regular (ξ : CompatibleCharts) : (assembledMeasure ξ).Regular :=
  RealRMK.regular_rieszMeasure _

theorem assembledMeasure_integral (ξ : CompatibleCharts) (f : C_c(PositiveSizeSurplus, ℝ)) :
    (∫ z, f z ∂assembledMeasure ξ) = value ξ f := RealRMK.integral_rieszMeasure _ f

instance assembledMeasure_finiteOnCompacts (ξ : CompatibleCharts) :
    IsFiniteMeasureOnCompacts (assembledMeasure ξ) := by
  constructor
  intro K hK
  obtain ⟨g, hg, hgcompact, _, hgnonneg⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (Set.subset_univ K)
  let f : C_c(PositiveSizeSurplus, ℝ) := ⟨g, hgcompact⟩
  have hb := RealRMK.rieszMeasure_le_of_eq_one (functional ξ) (f := f)
    (fun z ↦ (hgnonneg z).1) hK (fun z hz ↦ hg hz)
  exact hb.trans_lt ENNReal.ofReal_lt_top

instance assembledMeasure_locallyFinite (ξ : CompatibleCharts) :
    IsLocallyFiniteMeasure (assembledMeasure ξ) := inferInstance

theorem continuous_assembledMeasure_integral (f : C_c(PositiveSizeSurplus, ℝ)) :
    Continuous (fun ξ : CompatibleCharts ↦ ∫ z, f z ∂assembledMeasure ξ) := by
  simp only [assembledMeasure_integral, value]
  exact (continuous_testIntegral (supportIndex f) f).comp
    ((continuous_apply (supportIndex f)).comp continuous_subtype_val)

/-- Assembly recovers the literal finite sampled graph process as an
actual measure, including the empty graph. -/
theorem assembledMeasure_sourceCompatibleCharts {n : ℕ} (G : SimpleGraph (Fin n)) :
    assembledMeasure (sourceCompatibleCharts G) =
      (unmarkedProcess G : Measure PositiveSizeSurplus) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [assembledMeasure_integral]
  exact (unmarkedProcess_integral_eq_window (lower (supportIndex f)) (upper (supportIndex f))
    (supportIndex f) (lower_pos (supportIndex f)) G f
      ((support_subset_interior_index f).trans interior_subset)).symm

end PerronWright.GlobalPointChartAssembly
