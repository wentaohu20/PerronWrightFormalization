import PerronWright.Probability.FinitePointMeasureCompact

/-!
# Point measures from actual finite index types

The constructor below retains the literal finite Dirac sum. Its membership
in the point-measure space follows by enumerating the finite index type,
not by postulating a representation or a measurable point-process space.
-/

open MeasureTheory
open scoped BigOperators Classical ENNReal NNReal

noncomputable section

namespace PerronWright.FinitePointMeasureFintype

open FiniteAtomicPointMeasure FinitePointMeasureCompact

variable {E I : Type*} [MeasurableSpace E] [Fintype I]

/-- The point measure associated with a genuinely finite family of atoms. -/
def ofFintype (x : I → E) : PointMeasure E :=
  ⟨⟨∑ i, Measure.dirac (x i), by infer_instance⟩,
    Fintype.card I, x ∘ (Fintype.equivFin I).symm, by
      apply Subtype.ext
      exact ((Fintype.equivFin I).symm.sum_comp (fun i ↦ Measure.dirac (x i))).symm⟩

@[simp] theorem ofFintype_toMeasure (x : I → E) :
    ((ofFintype x : FiniteMeasure E) : Measure E) = ∑ i, Measure.dirac (x i) := rfl

theorem ofFintype_eq_ofAtomsPoint (x : I → E) :
    ofFintype x = ofAtomsPoint (x ∘ (Fintype.equivFin I).symm) := by
  apply Subtype.ext
  apply Subtype.ext
  exact ((Fintype.equivFin I).symm.sum_comp (fun i ↦ Measure.dirac (x i))).symm

@[simp] theorem mass_ofFintype (x : I → E) : mass (ofFintype x) = Fintype.card I := by
  rw [ofFintype_eq_ofAtomsPoint, mass_ofAtomsPoint]

@[simp] theorem size_ofFintype (x : I → E) : size (ofFintype x) = Fintype.card I := by
  rw [ofFintype_eq_ofAtomsPoint, size_ofAtomsPoint]

theorem ofFintype_integrable [MeasurableSingletonClass E]
    (x : I → E) (f : E → ℝ) :
    Integrable f ((ofFintype x : FiniteMeasure E) : Measure E) := by
  rw [ofFintype_toMeasure]
  exact integrable_finsetSum_measure.mpr (fun i _ ↦ integrable_dirac (by simp))

theorem ofFintype_integral [MeasurableSingletonClass E]
    (x : I → E) (f : E → ℝ) :
    (∫ z, f z ∂((ofFintype x : FiniteMeasure E) : Measure E)) = ∑ i, f (x i) := by
  rw [ofFintype_toMeasure, integral_finsetSum_measure]
  · simp only [integral_dirac]
  · intro i _
    exact integrable_dirac (by simp)

/-- Intrinsic point counts equal the literal cardinality of the family
of labelled atoms in the given measurable cell. -/
theorem count_ofFintype (x : I → E) {A : Set E} (hA : MeasurableSet A) :
    count (ofFintype x) A = Fintype.card {i : I // x i ∈ A} := by
  classical
  have he : ((ofFintype x : FiniteMeasure E) : Measure E) A =
      (Fintype.card {i : I // x i ∈ A} : ℝ≥0∞) := by
    simp [ofFintype_toMeasure, Measure.finsetSum_apply, hA,
      Measure.dirac_apply', Set.indicator_apply, Fintype.card_subtype]
  unfold count
  change ⌊(((ofFintype x : FiniteMeasure E) : Measure E) A).toReal⌋₊ = _
  rw [he]
  simp

end PerronWright.FinitePointMeasureFintype
