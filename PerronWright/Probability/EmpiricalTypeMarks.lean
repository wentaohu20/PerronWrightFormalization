import PerronWright.Probability.ComponentCounts
import PerronWright.Probability.AnnealedTypedGraph
import PerronWright.Model.PerronQuantities
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Literal empirical type marks of graph components

Every nonempty vertex block carries its empirical probability measure.
The component mark is this actual measure, not a list of test values or an
assumed limiting profile.  Integration of continuous test functions is
exactly the corresponding vertex average.
-/

open MeasureTheory
open scoped BigOperators Classical ENNReal

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.EmpiricalTypeMarks

open ComponentBlocks ComponentCounts

variable {S : Type*} [MeasurableSpace S]

/-- The empirical type measure on a vertex block. -/
def empiricalMeasure {n : ℕ} (x : Fin n → S) (B : Finset (Fin n)) : Measure S :=
  (B.card : ℝ≥0∞)⁻¹ • ∑ v ∈ B, Measure.dirac (x v)

theorem empiricalMeasure_isProbability {n : ℕ} (x : Fin n → S)
    (B : Finset (Fin n)) (hB : B.Nonempty) :
    IsProbabilityMeasure (empiricalMeasure x B) := by
  constructor
  have hc : (B.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hB.card_pos.ne'
  simp only [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const,
    nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel hc (by simp)

/-- The empirical mark, bundled as a probability measure. -/
def empiricalProbability {n : ℕ} (x : Fin n → S) (B : Finset (Fin n))
    (hB : B.Nonempty) : ProbabilityMeasure S :=
  ⟨empiricalMeasure x B, empiricalMeasure_isProbability x B hB⟩

/-- Empirical measures are measurable as actual measure-valued variables. -/
theorem empiricalMeasure_measurable {n : ℕ} (B : Finset (Fin n)) :
    Measurable (fun x : Fin n → S ↦ empiricalMeasure x B) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply]
  exact measurable_const.mul (Finset.measurable_fun_sum B (fun v _ ↦
    (Measure.measurable_coe hA).comp
      (Measure.measurable_dirac.comp (measurable_pi_apply v))))

theorem empiricalProbability_measurable {n : ℕ}
    (B : Finset (Fin n)) (hB : B.Nonempty) :
    Measurable (fun x : Fin n → S ↦ empiricalProbability x B hB) := by
  unfold empiricalProbability
  exact (empiricalMeasure_measurable B).subtype_mk

theorem componentBlock_nonempty {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) : (componentBlockEquiv G C).val.Nonempty := by
  obtain ⟨⟨v, hv⟩⟩ := (componentBlockEquiv G C).property.1.nonempty
  exact ⟨v, hv⟩

theorem componentSize_pos {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) : 0 < componentSize C :=
  (componentBlock_nonempty C).card_pos

/-- The actual empirical type mark attached to a connected component. -/
def componentMark {n : ℕ} {G : SimpleGraph (Fin n)}
    (x : Fin n → S) (C : G.ConnectedComponent) : ProbabilityMeasure S :=
  empiricalProbability x (componentBlockEquiv G C).val (componentBlock_nonempty C)

theorem componentMark_measurable {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) :
    Measurable (fun x : Fin n → S ↦ componentMark x C) :=
  empiricalProbability_measurable _ _

variable [MetricSpace S] [BorelSpace S]

/-- Continuous tests of the empirical measure are exact vertex averages. -/
theorem empiricalMeasure_integral {n : ℕ} (x : Fin n → S)
    (B : Finset (Fin n)) (f : C(S, ℝ)) :
    (∫ y, f y ∂empiricalMeasure x B) =
      (B.card : ℝ)⁻¹ * ∑ v ∈ B, f (x v) := by
  rw [empiricalMeasure, integral_smul_measure]
  rw [integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  · intro v _
    exact integrable_dirac (a := x v) (f := fun y : S ↦ f y) (by simp)

/-- Tests of a component mark use that component's genuine vertex support. -/
theorem componentMark_integral {n : ℕ} {G : SimpleGraph (Fin n)}
    (x : Fin n → S) (C : G.ConnectedComponent) (f : C(S, ℝ)) :
    (∫ y, f y ∂(componentMark x C : Measure S)) =
      (componentSize C : ℝ)⁻¹ * ∑ v ∈ (componentBlockEquiv G C).val, f (x v) :=
  empiricalMeasure_integral x _ f

/-- Every continuous test of a fixed component mark is continuous in the
sampled type vector. -/
theorem componentMark_test_continuous {n : ℕ} {G : SimpleGraph (Fin n)}
    (C : G.ConnectedComponent) (f : C(S, ℝ)) :
    Continuous (fun x : Fin n → S ↦
      ∫ y, f y ∂(componentMark x C : Measure S)) := by
  simp_rw [componentMark_integral]
  exact continuous_const.mul
    (continuous_finsetSum _ (fun v _ ↦ f.continuous.comp (continuous_apply v)))

variable [CompactSpace S]

/-- The deterministic candidate limit of empirical marks is the proved
Perron probability law, bundled in the same space as the finite marks. -/
def perronMark (M : CompactBJRModel S) (hM : M.IsRegularCritical) : ProbabilityMeasure S :=
  ⟨M.perronLaw hM, inferInstance⟩

theorem perronMark_integral (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℝ)) :
    (∫ y, f y ∂(perronMark M hM : Measure S)) =
      ∫ y, M.perronFunction hM y * f y ∂M.mu := M.perronLaw_integral hM f

end PerronWright.EmpiricalTypeMarks
