import PerronWright.Probability.FinitePointMeasureFintype
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Actual locally finite integer point measures and their vague topology

The underlying objects are actual Borel measures. Every compact restriction
is a finite integer Dirac sum, and the topology is induced by the actual
integrals of compactly supported continuous real functions. No process-law
existence or convergence criterion is assumed.
-/

open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators Classical CompactlySupported

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.LocallyFinitePointMeasureVague

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]

/-- Literal locally finite point measures, including arbitrary integer
multiplicities and the zero measure. -/
def IsLocallyFinitePointMeasure (μ : Measure E) : Prop :=
  IsLocallyFiniteMeasure μ ∧ ∀ K : Set E, IsCompact K →
    ∃ n : ℕ, ∃ x : Fin n → E, μ.restrict K = ∑ i, Measure.dirac (x i)

def LocalPointMeasure (E : Type*) [MeasurableSpace E] [TopologicalSpace E] :=
  {μ : Measure E // IsLocallyFinitePointMeasure μ}

instance : Coe (LocalPointMeasure E) (Measure E) := ⟨Subtype.val⟩

instance (η : LocalPointMeasure E) : IsLocallyFiniteMeasure (η : Measure E) :=
  η.property.1

theorem compact_restriction (η : LocalPointMeasure E) {K : Set E} (hK : IsCompact K) :
    ∃ n : ℕ, ∃ x : Fin n → E,
      (η : Measure E).restrict K = ∑ i, Measure.dirac (x i) := η.property.2 K hK

/-- All actual compact-support integrals, used to define vague topology. -/
def testEncoding (η : LocalPointMeasure E) : C_c(E, ℝ) → ℝ :=
  fun f ↦ ∫ x, f x ∂(η : Measure E)

instance : TopologicalSpace (LocalPointMeasure E) :=
  TopologicalSpace.induced testEncoding inferInstance

instance : MeasurableSpace (LocalPointMeasure E) := borel (LocalPointMeasure E)

instance : BorelSpace (LocalPointMeasure E) := ⟨rfl⟩

theorem isInducing_testEncoding :
    IsInducing (testEncoding : LocalPointMeasure E → (C_c(E, ℝ) → ℝ)) := ⟨rfl⟩

theorem continuous_testEncoding :
    Continuous (testEncoding : LocalPointMeasure E → (C_c(E, ℝ) → ℝ)) :=
  continuous_induced_dom

theorem continuous_integral (f : C_c(E, ℝ)) :
    Continuous (fun η : LocalPointMeasure E ↦ ∫ x, f x ∂(η : Measure E)) :=
  (continuous_apply f).comp continuous_testEncoding

theorem measurable_integral (f : C_c(E, ℝ)) :
    Measurable (fun η : LocalPointMeasure E ↦ ∫ x, f x ∂(η : Measure E)) :=
  (continuous_integral f).measurable

variable [OpensMeasurableSpace E]

theorem integrable_test (η : LocalPointMeasure E) (f : C_c(E, ℝ)) :
    Integrable f (η : Measure E) := f.integrable

omit [OpensMeasurableSpace E] in
/-- The literal vague convergence criterion follows from the defined
topology, not from an unproved measure-space interface. -/
theorem tendsto_iff_integrals {I : Type*} {l : Filter I}
    {η : I → LocalPointMeasure E} {ξ : LocalPointMeasure E} :
    Tendsto η l (𝓝 ξ) ↔ ∀ f : C_c(E, ℝ),
      Tendsto (fun i ↦ ∫ x, f x ∂(η i : Measure E)) l
        (𝓝 (∫ x, f x ∂(ξ : Measure E))) := by
  rw [isInducing_testEncoding.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

variable [T2Space E] [LocallyCompactSpace E] [SigmaCompactSpace E] [BorelSpace E]
  [PseudoMetrizableSpace E]

omit [OpensMeasurableSpace E] in
theorem testEncoding_injective :
    Function.Injective (testEncoding : LocalPointMeasure E → (C_c(E, ℝ) → ℝ)) := by
  intro η ξ h
  apply Subtype.ext
  exact Measure.ext_of_integral_eq_on_compactlySupported (fun f ↦ congrFun h f)

omit [OpensMeasurableSpace E] in
theorem isEmbedding_testEncoding :
    IsEmbedding (testEncoding : LocalPointMeasure E → (C_c(E, ℝ) → ℝ)) :=
  ⟨isInducing_testEncoding, testEncoding_injective⟩

instance : T2Space (LocalPointMeasure E) := isEmbedding_testEncoding.t2Space

/-- Every finite labelled atom measure has genuine local point structure.
The compact restriction is obtained by filtering the literal labels. -/
theorem isLocallyFinitePointMeasure_sum_dirac {I : Type*} [Fintype I] (x : I → E) :
    IsLocallyFinitePointMeasure (∑ i, Measure.dirac (x i)) := by
  refine ⟨by infer_instance, ?_⟩
  intro K _
  let A := {i : I // x i ∈ K}
  let ζ := FinitePointMeasureFintype.ofFintype (fun i : A ↦ x i.val)
  obtain ⟨n, y, hy⟩ := ζ.property
  refine ⟨n, y, ?_⟩
  have hfilter : (∑ i, Measure.dirac (x i)).restrict K =
      ∑ i : A, Measure.dirac (x i.val) := by
    change Measure.restrictₗ K (∑ i, Measure.dirac (x i)) = _
    rw [map_sum]
    change (∑ i, (Measure.dirac (x i)).restrict K) = _
    simp only [restrict_dirac]
    exact Finset.sum_congr_set {i : I | x i ∈ K}
      (fun i ↦ if x i ∈ K then Measure.dirac (x i) else 0)
      (fun i : A ↦ Measure.dirac (x i.val))
      (fun i hi ↦ if_pos hi) (fun i hi ↦ if_neg hi)
  rw [hfilter]
  exact congrArg (fun μ : FiniteMeasure E ↦ (μ : Measure E)) hy

def ofFintype {I : Type*} [Fintype I] (x : I → E) : LocalPointMeasure E :=
  ⟨∑ i, Measure.dirac (x i), isLocallyFinitePointMeasure_sum_dirac x⟩

@[simp] theorem ofFintype_toMeasure {I : Type*} [Fintype I] (x : I → E) :
    (ofFintype x : Measure E) = ∑ i, Measure.dirac (x i) := rfl

theorem ofFintype_integral {I : Type*} [Fintype I] (x : I → E) (f : E → ℝ) :
    (∫ z, f z ∂(ofFintype x : Measure E)) = ∑ i, f (x i) := by
  rw [ofFintype_toMeasure, integral_finsetSum_measure]
  · simp only [integral_dirac]
  · intro i _
    exact integrable_dirac (by simp)

theorem continuous_ofFintype {I : Type*} [Fintype I] :
    Continuous (ofFintype : (I → E) → LocalPointMeasure E) := by
  apply isInducing_testEncoding.continuous_iff.mpr
  apply continuous_pi
  intro f
  simp only [Function.comp_def, testEncoding, ofFintype_integral]
  exact continuous_finsetSum _ (fun i _ ↦ f.continuous.comp (continuous_apply i))

omit [MeasurableSpace E] [OpensMeasurableSpace E] [T2Space E]
  [LocallyCompactSpace E] [SigmaCompactSpace E] [BorelSpace E] [PseudoMetrizableSpace E] in
/-- Every compact-support test is contained in one member of any actual
compact exhaustion. -/
theorem exists_test_support_subset (K : CompactExhaustion E) (f : C_c(E, ℝ)) :
    ∃ n, tsupport f ⊆ K n := K.exists_superset_of_isCompact f.hasCompactSupport

end PerronWright.LocallyFinitePointMeasureVague
