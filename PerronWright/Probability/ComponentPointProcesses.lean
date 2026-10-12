import PerronWright.Probability.EmpiricalTypeMarks
import PerronWright.Probability.CriticalScaling

/-!
# Actual finite graph component point measures

Both unmarked and empirically marked point measures are constructed on
the joint type-and-edge probability space.  They are measurable random
measures for the evaluation sigma algebra.  No assertion of local-vague
or weak convergence is made in this finite-size construction.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ComponentPointProcesses

open ComponentCounts EmpiricalTypeMarks AnnealedGraph

/-- Scaled size and surplus of a literal graph component. -/
def atom {n : ℕ} {G : SimpleGraph (Fin n)} (C : G.ConnectedComponent) : ℝ × ℕ :=
  ((componentSize C : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ), componentSurplus C)

/-- The finite unmarked component point measure. -/
def unmarked {n : ℕ} (G : SimpleGraph (Fin n)) : Measure (ℝ × ℕ) :=
  ∑ C : G.ConnectedComponent, Measure.dirac (atom C)

instance unmarked_isFinite {n : ℕ} (G : SimpleGraph (Fin n)) :
    IsFiniteMeasure (unmarked G) := by
  unfold unmarked
  infer_instance

theorem unmarked_integral {n : ℕ} (G : SimpleGraph (Fin n)) (f : (ℝ × ℕ) → ℝ) :
    (∫ z, f z ∂unmarked G) = ∑ C : G.ConnectedComponent, f (atom C) := by
  rw [unmarked, integral_finsetSum_measure]
  · simp only [integral_dirac]
  · intro C _
    exact integrable_dirac (a := atom C) (f := f) (by simp)

variable {S : Type*} [MeasurableSpace S]

/-- Scaled size, surplus, and the literal empirical type probability measure. -/
def markedAtom {n : ℕ} {G : SimpleGraph (Fin n)}
    (x : Fin n → S) (C : G.ConnectedComponent) : (ℝ × ℕ) × ProbabilityMeasure S :=
  (atom C, componentMark x C)

/-- The finite empirically marked component point measure. -/
def marked {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → S) :
    Measure ((ℝ × ℕ) × ProbabilityMeasure S) :=
  ∑ C : G.ConnectedComponent, Measure.dirac (markedAtom x C)

instance marked_isFinite {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → S) :
    IsFiniteMeasure (marked G x) := by
  unfold marked
  infer_instance

theorem marked_measurable {n : ℕ} (G : SimpleGraph (Fin n)) :
    Measurable (marked G : (Fin n → S) → Measure ((ℝ × ℕ) × ProbabilityMeasure S)) := by
  unfold marked
  apply Finset.measurable_fun_sum
  intro C _
  apply Measure.measurable_dirac.comp
  exact measurable_const.prodMk (componentMark_measurable C)

/-- Unmarked process on the same space that retains the sampled types. -/
def unmarkedSample {n : ℕ} (p : AnnealedTypedGraph.State S n) : Measure (ℝ × ℕ) :=
  unmarked (toGraph p.2)

/-- Marked process on the joint sampled type-and-edge space. -/
def markedSample {n : ℕ} (p : AnnealedTypedGraph.State S n) :
    Measure ((ℝ × ℕ) × ProbabilityMeasure S) := marked (toGraph p.2) p.1

theorem unmarkedSample_measurable (n : ℕ) :
    Measurable (unmarkedSample : AnnealedTypedGraph.State S n → Measure (ℝ × ℕ)) :=
  (measurable_of_finite (fun a : Assignment n ↦ unmarked (toGraph a))).comp measurable_snd

theorem markedSample_measurable (n : ℕ) :
    Measurable (markedSample : AnnealedTypedGraph.State S n →
      Measure ((ℝ × ℕ) × ProbabilityMeasure S)) :=
  measurable_from_prod_countable_left (fun a ↦ marked_measurable (toGraph a))

variable [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- The actual probability law of the unmarked point measure at critical time. -/
def unmarkedLaw (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) : Measure (Measure (ℝ × ℕ)) :=
  (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map unmarkedSample

/-- The actual probability law of the marked point measure at critical time. -/
def markedLaw (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    Measure (Measure ((ℝ × ℕ) × ProbabilityMeasure S)) :=
  (AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map markedSample

instance unmarkedLaw_isProbability (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    IsProbabilityMeasure (unmarkedLaw M lambda n) :=
  Measure.isProbabilityMeasure_map (unmarkedSample_measurable n).aemeasurable

instance markedLaw_isProbability (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    IsProbabilityMeasure (markedLaw M lambda n) :=
  Measure.isProbabilityMeasure_map (markedSample_measurable n).aemeasurable

end PerronWright.ComponentPointProcesses
