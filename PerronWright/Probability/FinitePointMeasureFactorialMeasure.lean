import PerronWright.Probability.FinitePointMeasureRectangleFactorials
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# The actual intrinsic factorial measure of a finite point measure

Distinctness is in labels, so atoms at coincident positions retain
their multiplicity. Equality on all Borel rectangles proves that the
finite Dirac measure does not depend on its atomic presentation.
-/

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FinitePointMeasureFactorialMeasure

open FinitePointMeasureCompact FinitePointMeasureFintype
open FinitePointMeasureRectangleFactorials

variable {E : Type*} [MeasurableSpace E]

def labelledMeasure {I J : Type*} [Fintype I] [Fintype J] (x : I → E) : Measure (J → E) :=
  ∑ e : J ↪ I, Measure.dirac (fun j ↦ x (e j))

instance labelledMeasure_isFiniteMeasure {I J : Type*} [Fintype I] [Fintype J] (x : I → E) :
    IsFiniteMeasure (labelledMeasure (J := J) x) := by
  unfold labelledMeasure
  infer_instance

theorem labelledMeasure_rectangle {I J : Type*} [Fintype I] [Fintype J]
    (x : I → E) (A : J → Set E) (hA : ∀ j, MeasurableSet (A j)) :
    labelledMeasure x (Set.pi univ A) = (rectangleFactorial (ofFintype x) A : ℝ≥0∞) := by
  rw [rectangleFactorial_ofFintype x A hA]
  have hB : MeasurableSet (Set.pi univ A) := MeasurableSet.pi Set.countable_univ (fun j _ ↦ hA j)
  simp [labelledMeasure,Measure.finsetSum_apply,hB,Measure.dirac_apply',
    Set.indicator_apply,Fintype.card_subtype]

theorem labelledMeasure_univ {I J : Type*} [Fintype I] [Fintype J] (x : I → E) :
    labelledMeasure (J := J) x univ =
      ((Fintype.card I).descFactorial (Fintype.card J) : ℝ≥0∞) := by
  simp [labelledMeasure,Measure.finsetSum_apply,Fintype.card_embedding_eq]

/-- Complete measure equality, not just equality of total tuple counts. -/
theorem labelledMeasure_eq_of_pointMeasure_eq {I I' J : Type*}
    [Fintype I] [Fintype I'] [Fintype J] (x : I → E) (y : I' → E)
    (h : ofFintype x = ofFintype y) :
    labelledMeasure (J := J) x = labelledMeasure (J := J) y := by
  apply ext_of_generate_finite
    (Set.pi univ '' Set.pi univ (fun _ : J ↦ {A : Set E | MeasurableSet A}))
    (generateFrom_pi (α := fun _ : J ↦ E)).symm isPiSystem_pi
  · rintro B ⟨A,hA,rfl⟩
    have hm : ∀ j, MeasurableSet (A j) := fun j ↦ hA j (mem_univ j)
    rw [labelledMeasure_rectangle x A hm,labelledMeasure_rectangle y A hm,h]
  · have hm : ∀ _ : J, MeasurableSet (univ : Set E) := fun _ ↦ MeasurableSet.univ
    simpa only [Set.pi_univ] using
      (show labelledMeasure x (Set.pi univ (fun _ : J ↦ univ)) =
        labelledMeasure y (Set.pi univ (fun _ : J ↦ univ)) by
        rw [labelledMeasure_rectangle x _ hm,labelledMeasure_rectangle y _ hm,h])

def chosenSize (η : PointMeasure E) : ℕ := η.property.choose

def chosenAtoms (η : PointMeasure E) : Fin (chosenSize η) → E :=
  η.property.choose_spec.choose

theorem chosenAtoms_spec (η : PointMeasure E) : ofFintype (chosenAtoms η) = η :=
  Subtype.ext η.property.choose_spec.choose_spec.symm

/-- The genuine finite integer measure of ordered distinct atom tuples. -/
def factorialMeasure (J : Type*) [Fintype J] (η : PointMeasure E) : Measure (J → E) :=
  labelledMeasure (J := J) (chosenAtoms η)

instance factorialMeasure_isFiniteMeasure (J : Type*) [Fintype J] (η : PointMeasure E) :
    IsFiniteMeasure (factorialMeasure J η) := by
  unfold factorialMeasure
  infer_instance

theorem factorialMeasure_ofFintype {I J : Type*} [Fintype I] [Fintype J] (x : I → E) :
    factorialMeasure J (ofFintype x) = labelledMeasure (J := J) x :=
  labelledMeasure_eq_of_pointMeasure_eq _ _ (chosenAtoms_spec (ofFintype x))

theorem factorialMeasure_rectangle {J : Type*} [Fintype J]
    (η : PointMeasure E) (A : J → Set E) (hA : ∀ j, MeasurableSet (A j)) :
    factorialMeasure J η (Set.pi univ A) = (rectangleFactorial η A : ℝ≥0∞) := by
  rw [factorialMeasure,labelledMeasure_rectangle _ A hA,chosenAtoms_spec]

theorem factorialMeasure_univ (J : Type*) [Fintype J] (η : PointMeasure E) :
    factorialMeasure J η univ = ((size η).descFactorial (Fintype.card J) : ℝ≥0∞) := by
  have hs := congrArg size (chosenAtoms_spec η)
  simp only [size_ofFintype,Fintype.card_fin] at hs
  rw [factorialMeasure,labelledMeasure_univ,Fintype.card_fin,hs]

theorem labelledMeasure_lintegral {I J : Type*} [Fintype I] [Fintype J]
    (x : I → E) (Ψ : (J → E) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ z, Ψ z ∂labelledMeasure (J := J) x) =
      ∑ e : J ↪ I, Ψ (fun j ↦ x (e j)) := by
  simp [labelledMeasure,lintegral_finsetSum_measure,lintegral_dirac' _ hΨ]

theorem factorialMeasure_ofFintype_lintegral {I J : Type*} [Fintype I] [Fintype J]
    (x : I → E) (Ψ : (J → E) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    (∫⁻ z, Ψ z ∂factorialMeasure J (ofFintype x)) =
      ∑ e : J ↪ I, Ψ (fun j ↦ x (e j)) := by
  rw [factorialMeasure_ofFintype]
  exact labelledMeasure_lintegral x Ψ hΨ

end PerronWright.FinitePointMeasureFactorialMeasure
