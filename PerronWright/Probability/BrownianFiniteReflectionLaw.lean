import PerronWright.Probability.BrownianPathIndependentIncrements

/-! # Actual Brownian reflection selected from a measurable partition

Fixed-time reflections preserve the actual Brownian path law. If a
countable measurable partition is invariant under its corresponding
reflection, restriction and countable additivity prove preservation by
the selected reflection. This proved reduction will be applied to actual
finite first-passage grid events, rather than assumed as a stopping-time
reflection principle.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFiniteReflectionLaw

open BrownianPathLaw BrownianPathIndependentIncrements

theorem continuous_joint_reflectionPath :
    Continuous (fun p : ℝ≥0 × Path ↦ reflectionPath p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((continuous_fst.snd.eval (continuous_snd.min continuous_fst.fst)).const_mul 2).sub
    (continuous_fst.snd.eval continuous_snd)

theorem reflectionPath_involution (T : ℝ≥0) (f : Path) :
    reflectionPath T (reflectionPath T f) = f := by
  apply ContinuousMap.ext
  intro t
  change 2*(2*f (min (min t T) T)-f (min t T))-(2*f (min t T)-f t) = f t
  simp only [min_assoc,min_self]
  ring

theorem pastPath_reflectionPath (T : ℝ≥0) (f : Path) :
    pastPath T (reflectionPath T f) = pastPath T f := by
  apply ContinuousMap.ext
  intro t
  change 2*f (min (min t T) T)-f (min t T) = f (min t T)
  simp only [min_assoc,min_self]
  ring

theorem reflectionPath_restrict_law (T : ℝ≥0) {A : Set Path}
    (hA : MeasurableSet A) (hstable : ∀ f, reflectionPath T f ∈ A ↔ f ∈ A) :
    (pathLaw.restrict A).map (reflectionPath T) = pathLaw.restrict A := by
  have hp : reflectionPath T ⁻¹' A = A := Set.ext hstable
  have h := Measure.restrict_map (μ := pathLaw) (measurable_reflectionPath T) hA
  rw [reflectionPath_law,hp] at h
  exact h.symm

variable {I : Type*} [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]

def chosenReflection (t : I → ℝ≥0) (κ : Path → I) (f : Path) : Path :=
  reflectionPath (t (κ f)) f

theorem measurable_chosenReflection (t : I → ℝ≥0) {κ : Path → I} (hκ : Measurable κ) :
    Measurable (chosenReflection t κ) :=
  continuous_joint_reflectionPath.measurable.comp
    (((measurable_of_countable t).comp hκ).prodMk measurable_id)

theorem law_eq_sum_fibers {κ : Path → I} (hκ : Measurable κ) :
    pathLaw = Measure.sum (fun i : I ↦ pathLaw.restrict {f | κ f = i}) := by
  have hA (i : I) : MeasurableSet {f : Path | κ f = i} := hκ (measurableSet_singleton i)
  have hd : Pairwise (fun i j : I ↦ Disjoint {f : Path | κ f = i} {f : Path | κ f = j}) := by
    intro i j hij
    exact disjoint_left.mpr (fun f hi hj ↦ hij (hi.symm.trans hj))
  have hu : (⋃ i : I, {f : Path | κ f = i}) = univ := by ext f; simp
  have h := Measure.restrict_iUnion (μ := pathLaw) hd hA
  rw [hu,Measure.restrict_univ] at h
  exact h

omit [Countable I] in
theorem chosenReflection_restrict_law (t : I → ℝ≥0) {κ : Path → I} (hκ : Measurable κ)
    (hstable : ∀ i f, κ (reflectionPath (t i) f) = i ↔ κ f = i) (i : I) :
    (pathLaw.restrict {f | κ f = i}).map (chosenReflection t κ) =
      pathLaw.restrict {f | κ f = i} := by
  have hA : MeasurableSet {f : Path | κ f = i} := hκ (measurableSet_singleton i)
  have he : chosenReflection t κ =ᵐ[pathLaw.restrict {f | κ f = i}] reflectionPath (t i) := by
    filter_upwards [ae_restrict_mem hA] with f hf
    change reflectionPath (t (κ f)) f = reflectionPath (t i) f
    rw [show κ f = i from hf]
  rw [Measure.map_congr he]
  exact reflectionPath_restrict_law (t i) hA (hstable i)

/-- A proved actual path-law identity for any measurable countable
reflection partition satisfying its explicit deterministic invariance. -/
theorem chosenReflection_law (t : I → ℝ≥0) {κ : Path → I} (hκ : Measurable κ)
    (hstable : ∀ i f, κ (reflectionPath (t i) f) = i ↔ κ f = i) :
    pathLaw.map (chosenReflection t κ) = pathLaw := by
  calc
    _ = (Measure.sum (fun i : I ↦ pathLaw.restrict {f | κ f = i})).map
        (chosenReflection t κ) := by rw [← law_eq_sum_fibers hκ]
    _ = Measure.sum (fun i : I ↦ (pathLaw.restrict {f | κ f = i}).map
        (chosenReflection t κ)) := Measure.map_sum (measurable_chosenReflection t hκ).aemeasurable
    _ = Measure.sum (fun i : I ↦ pathLaw.restrict {f | κ f = i}) := by
      congr 1
      funext i
      exact chosenReflection_restrict_law t hκ hstable i
    _ = pathLaw := (law_eq_sum_fibers hκ).symm

end PerronWright.BrownianFiniteReflectionLaw
