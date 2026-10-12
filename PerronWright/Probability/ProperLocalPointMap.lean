import PerronWright.Probability.LocallyFinitePointMeasureVague
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Metrizable.Basic

/-!
# Actual proper pushforwards of local integer point measures

Compact preimages prove both local finiteness and integer atomicity of
the literal pushforward measure. Compact-support pullback then proves
vague continuity. These proved operations support size rescaling and
deterministic Perron marking; properness is to be proved for each actual
map, not supplied as a model-level convergence interface.
-/

open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators Classical CompactlySupported

noncomputable section

namespace PerronWright.ProperLocalPointMap

open LocallyFinitePointMeasureVague

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
  [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
  [T2Space E] [T2Space F] [LocallyCompactSpace E] [LocallyCompactSpace F]

omit [T2Space E] [LocallyCompactSpace E] in
theorem isLocalPoint_map (f : E → F) (hf : IsProperMap f) (η : LocalPointMeasure E) :
    IsLocallyFinitePointMeasure ((η : Measure E).map f) := by
  let : IsFiniteMeasureOnCompacts ((η : Measure E).map f) := ⟨by
    intro K hK
    rw [Measure.map_apply hf.continuous.measurable hK.measurableSet]
    exact (hf.isCompact_preimage hK).measure_lt_top⟩
  refine ⟨inferInstance, ?_⟩
  intro K hK
  obtain ⟨n, x, hx⟩ := compact_restriction η (hf.isCompact_preimage hK)
  refine ⟨n, fun i ↦ f (x i), ?_⟩
  rw [Measure.restrict_map hf.continuous.measurable hK.measurableSet, hx,
    Measure.map_finset_sum' hf.continuous.measurable.aemeasurable]
  simp only [Measure.map_dirac' hf.continuous.measurable]

def mapPoint (f : E → F) (hf : IsProperMap f) (η : LocalPointMeasure E) :
    LocalPointMeasure F := ⟨(η : Measure E).map f, isLocalPoint_map f hf η⟩

omit [T2Space E] [LocallyCompactSpace E] in
@[simp] theorem mapPoint_toMeasure (f : E → F) (hf : IsProperMap f)
    (η : LocalPointMeasure E) :
    (mapPoint f hf η : Measure F) = (η : Measure E).map f := rfl

def pullbackTest (f : E → F) (hf : IsProperMap f) (φ : C_c(F, ℝ)) : C_c(E, ℝ) where
  toFun x := φ (f x)
  continuous_toFun := φ.continuous.comp hf.continuous
  hasCompactSupport' := by
    apply exists_compact_iff_hasCompactSupport.mp
    refine ⟨f ⁻¹' tsupport φ, hf.isCompact_preimage φ.hasCompactSupport, ?_⟩
    intro x hx
    exact image_eq_zero_of_notMem_tsupport hx

omit [LocallyCompactSpace E] in
theorem mapPoint_integral (f : E → F) (hf : IsProperMap f)
    (η : LocalPointMeasure E) (φ : C_c(F, ℝ)) :
    (∫ y, φ y ∂(mapPoint f hf η : Measure F)) =
      ∫ x, pullbackTest f hf φ x ∂(η : Measure E) := by
  exact integral_map hf.continuous.measurable.aemeasurable
    φ.continuous.measurable.aestronglyMeasurable

omit [LocallyCompactSpace E] in
theorem continuous_mapPoint (f : E → F) (hf : IsProperMap f) :
    Continuous (mapPoint f hf) := by
  apply isInducing_testEncoding.continuous_iff.mpr
  apply continuous_pi
  intro φ
  simpa only [Function.comp_def, testEncoding, mapPoint_integral] using
    (continuous_integral (pullbackTest f hf φ))

variable [SigmaCompactSpace E] [PseudoMetrizableSpace E]
  [SigmaCompactSpace F] [PseudoMetrizableSpace F]

theorem mapPoint_ofFintype (f : E → F) (hf : IsProperMap f)
    {I : Type*} [Fintype I] (x : I → E) :
    mapPoint f hf (ofFintype x) = ofFintype (fun i ↦ f (x i)) := by
  apply Subtype.ext
  rw [mapPoint_toMeasure, ofFintype_toMeasure, ofFintype_toMeasure,
    Measure.map_finset_sum' hf.continuous.measurable.aemeasurable]
  simp only [Measure.map_dirac' hf.continuous.measurable]

end PerronWright.ProperLocalPointMap
