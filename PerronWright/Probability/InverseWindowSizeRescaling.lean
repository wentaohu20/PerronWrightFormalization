import PerronWright.Probability.WindowSizeRescaling
import PerronWright.Probability.ComponentWindowMixedFactorials

/-! # Literal inverse size dilation of compact-window count laws

Closed endpoints, surplus values and atom multiplicities are retained.
Cell counts are exact preimage counts, not an asserted distributional
identification or a continuity claim for closed-window restriction.
-/

open MeasureTheory Set
open scoped Classical ENNReal
noncomputable section

namespace PerronWright.InverseWindowSizeRescaling

open ComponentWindowPointMeasures FinitePointMeasureCompact FinitePointMeasureMarking
open FinitePointMeasureMeasurable ComponentWindowMixedFactorials

def inverseWindowScaleMap (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) :
    SurplusWindow (c*a) (c*b) R → SurplusWindow a b R := fun z ↦
  (⟨z.1.val/c, (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using z.1.property.1),
    (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using z.1.property.2)⟩, z.2)

theorem continuous_inverseWindowScaleMap (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c) :
    Continuous (inverseWindowScaleMap a b R hc) :=
  (((continuous_subtype_val.comp continuous_fst).div_const c).subtype_mk _).prodMk continuous_snd

theorem count_map_inverseWindowScaleMap {D : Type*}
    (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (η : PointMeasure (SurplusWindow (c*a) (c*b) R)) (i : D) :
    count (mapPoint (inverseWindowScaleMap a b R hc)
      (continuous_inverseWindowScaleMap a b R hc).measurable η)
      (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i) =
    count η (windowEmbedding (c*a) (c*b) R ⁻¹'
      sizeSurplusCells (fun j ↦ (fun z : ℝ ↦ z/c) ⁻¹' J j) S i) := by
  have he :
      ((((mapPoint (inverseWindowScaleMap a b R hc)
        (continuous_inverseWindowScaleMap a b R hc).measurable η) :
          FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))
        (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)) =
      (((η : FiniteMeasure (SurplusWindow (c*a) (c*b) R)) :
        Measure (SurplusWindow (c*a) (c*b) R))
        (windowEmbedding (c*a) (c*b) R ⁻¹'
          sizeSurplusCells (fun j ↦ (fun z : ℝ ↦ z/c) ⁻¹' J j) S i)) := by
    change ((((η : FiniteMeasure (SurplusWindow (c*a) (c*b) R)) :
      Measure (SurplusWindow (c*a) (c*b) R)).map
        (inverseWindowScaleMap a b R hc))
        (windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)) = _
    rw [Measure.map_apply (continuous_inverseWindowScaleMap a b R hc).measurable
      ((measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i))]
    rfl
  exact congrArg (fun x : ℝ≥0∞ ↦ ⌊x.toReal⌋₊) he

theorem countLaw_map_inverseWindowScaleMap {D : Type*} [Fintype D]
    (a b : ℝ) (R : ℕ) {c : ℝ} (hc : 0 < c)
    (J : D → Set ℝ) (S : D → Finset ℕ) (hJ : ∀ i, MeasurableSet (J i))
    (ν : ProbabilityMeasure (PointMeasure (SurplusWindow (c*a) (c*b) R))) :
    countLaw (ν.map (continuous_mapPoint (inverseWindowScaleMap a b R hc)
      (continuous_inverseWindowScaleMap a b R hc)).measurable.aemeasurable)
      (fun i ↦ windowEmbedding a b R ⁻¹' sizeSurplusCells J S i)
      (fun i ↦ (measurable_windowEmbedding a b R) (measurableSet_sizeSurplusCells J S hJ i)) =
    countLaw ν
      (fun i ↦ windowEmbedding (c*a) (c*b) R ⁻¹'
        sizeSurplusCells (fun j ↦ (fun z : ℝ ↦ z/c) ⁻¹' J j) S i)
      (fun i ↦ (measurable_windowEmbedding (c*a) (c*b) R)
        (measurableSet_sizeSurplusCells _ S
          (fun j ↦ (measurable_id.div_const c) (hJ j)) i)) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [countLaw_toMeasure,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map
    (measurable_count_vector _ (fun i ↦ (measurable_windowEmbedding a b R)
      (measurableSet_sizeSurplusCells J S hJ i)))
    (continuous_mapPoint _ (continuous_inverseWindowScaleMap a b R hc)).measurable]
  congr 1
  funext η i
  exact count_map_inverseWindowScaleMap a b R hc J S hJ η i

end PerronWright.InverseWindowSizeRescaling
