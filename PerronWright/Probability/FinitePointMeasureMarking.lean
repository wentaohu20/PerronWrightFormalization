import PerronWright.Probability.FinitePointMeasureFintype
import PerronWright.Probability.FinitePointMeasurePolish

/-! # Proved continuous push-forward and constant marking of actual point measures -/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology

noncomputable section
set_option maxHeartbeats 800000

namespace PerronWright.FinitePointMeasureMarking

open FiniteAtomicPointMeasure FinitePointMeasureCompact FinitePointMeasureFintype

section Map

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

theorem map_ofAtoms {n : ℕ} (x : Fin n → E) (f : E → F) (hf : Measurable f) :
    (ofAtoms x).map f = ofAtoms (f ∘ x) := by
  apply Subtype.ext
  change (∑ i, Measure.dirac (x i)).map f = ∑ i, Measure.dirac (f (x i))
  rw [Measure.map_finset_sum' hf.aemeasurable]
  simp only [Measure.map_dirac' hf]

def mapPoint (f : E → F) (hf : Measurable f) (η : PointMeasure E) : PointMeasure F :=
  ⟨(η : FiniteMeasure E).map f, by
    obtain ⟨n,x,hx⟩ := η.property
    exact ⟨n,f ∘ x,by rw [hx,map_ofAtoms x f hf]⟩⟩

@[simp] theorem mapPoint_val (f : E → F) (hf : Measurable f) (η : PointMeasure E) :
    (mapPoint f hf η : FiniteMeasure F) = (η : FiniteMeasure E).map f := rfl

@[simp] theorem mapPoint_ofAtomsPoint {n : ℕ} (x : Fin n → E) (f : E → F) (hf : Measurable f) :
    mapPoint f hf (ofAtomsPoint x) = ofAtomsPoint (f ∘ x) :=
  Subtype.ext (map_ofAtoms x f hf)

theorem mapPoint_ofFintype {I : Type*} [Fintype I] (x : I → E) (f : E → F) (hf : Measurable f) :
    mapPoint f hf (ofFintype x) = ofFintype (f ∘ x) := by
  apply Subtype.ext
  apply Subtype.ext
  change (∑ i, Measure.dirac (x i)).map f = ∑ i, Measure.dirac (f (x i))
  rw [Measure.map_finset_sum' hf.aemeasurable]
  simp only [Measure.map_dirac' hf]

@[simp] theorem size_mapPoint (f : E → F) (hf : Measurable f) (η : PointMeasure E) :
    size (mapPoint f hf η) = size η := by
  obtain ⟨n,x,hx⟩ := η.property
  have he : η = ofAtomsPoint x := Subtype.ext hx
  simp only [he,mapPoint_ofAtomsPoint,size_ofAtomsPoint]

@[simp] theorem mass_mapPoint (f : E → F) (hf : Measurable f) (η : PointMeasure E) :
    mass (mapPoint f hf η) = mass η := by
  rw [mass_eq_size,mass_eq_size,size_mapPoint]

variable [TopologicalSpace E] [OpensMeasurableSpace E] [TopologicalSpace F] [BorelSpace F]

theorem continuous_mapPoint (f : E → F) (hf : Continuous f) :
    Continuous (mapPoint f hf.measurable : PointMeasure E → PointMeasure F) :=
  ((FiniteMeasure.continuous_map hf).comp continuous_val).subtype_mk _

end Map

theorem continuous_ofFintype {E I : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [Fintype I] :
    Continuous (ofFintype : (I → E) → PointMeasure E) := by
  have he : (ofFintype : (I → E) → PointMeasure E) =
      fun x ↦ ofAtomsPoint (x ∘ (Fintype.equivFin I).symm) :=
    funext ofFintype_eq_ofAtomsPoint
  rw [he]
  exact (continuous_ofAtomsPoint _).comp
    (continuous_pi (fun i ↦ continuous_apply ((Fintype.equivFin I).symm i)))

section Mark

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
  [MetricSpace E] [MetricSpace A] [CompactSpace E] [CompactSpace A] [BorelSpace E] [BorelSpace A]

def constantMark (ν : A) : PointMeasure E → PointMeasure (E × A) :=
  mapPoint (fun z ↦ (z,ν)) (measurable_id.prodMk measurable_const)

omit [CompactSpace E] in
theorem continuous_constantMark (ν : A) :
    Continuous (constantMark ν : PointMeasure E → PointMeasure (E × A)) :=
  continuous_mapPoint _ (continuous_id.prodMk continuous_const)

def canonicalMarkedLaw (ν : A) (μ : ProbabilityMeasure (PointMeasure E)) :
    ProbabilityMeasure (PointMeasure (E × A)) :=
  μ.map (continuous_constantMark ν).measurable.aemeasurable

omit [CompactSpace E] in
theorem continuous_canonicalMarkedLaw (ν : A) :
    Continuous (canonicalMarkedLaw ν : ProbabilityMeasure (PointMeasure E) →
      ProbabilityMeasure (PointMeasure (E × A))) :=
  ProbabilityMeasure.continuous_map (continuous_constantMark ν)

end Mark

end PerronWright.FinitePointMeasureMarking
