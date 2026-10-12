import PerronWright.Probability.ComponentGlobalPointProcess
import PerronWright.Probability.ComponentWindowFactorialCounts
import PerronWright.Probability.FiniteIrreducibleTypedGraphLaw

/-! # Actual deterministic finite component point-process laws

The source measure fixes the literal vertex-type assignment. The atoms,
window filters and vague topology are the already proved genuine graph
component constructions, not an annealed replacement. No criticality or
limiting-law assumption is required for these exact identities.
-/

open MeasureTheory Filter Topology
open scoped Real Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleComponentProcess

open ComponentGlobalPointProcess LocallyFinitePointMeasureVague
open ComponentWindowPointMeasures ComponentWindowFactorialCounts
open FinitePointMeasureCompact

variable {S : Type*} [Fintype S] [DecidableEq S]

def graphLaw (M : FiniteIrreducibleModel S) (lambda : ℝ) (n : ℕ)
    (x : Fin n → S) : Measure (SimpleGraph (Fin n)) :=
  FiniteIrreducibleTypedGraphLaw.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) x

instance graphLaw_isProbability (M : FiniteIrreducibleModel S) (lambda : ℝ)
    (n : ℕ) (x : Fin n → S) : IsProbabilityMeasure (graphLaw M lambda n x) := by
  unfold graphLaw
  infer_instance

def unmarkedProcessLaw (M : FiniteIrreducibleModel S) (lambda : ℝ) (n : ℕ)
    (x : Fin n → S) : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  ⟨(graphLaw M lambda n x).map unmarkedProcess,
    Measure.isProbabilityMeasure_map (measurable_unmarkedProcess n).aemeasurable⟩

def unmarkedWindowLaw (M : FiniteIrreducibleModel S) (lambda a b : ℝ)
    (R n : ℕ) (x : Fin n → S) : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)) :=
  ⟨(graphLaw M lambda n x).map (windowPointMeasure a b R 1),
    Measure.isProbabilityMeasure_map (measurable_windowPointMeasure a b R 1 n).aemeasurable⟩

@[simp] theorem unmarkedProcessLaw_toMeasure (M : FiniteIrreducibleModel S)
    (lambda : ℝ) (n : ℕ) (x : Fin n → S) :
    (unmarkedProcessLaw M lambda n x : Measure (LocalPointMeasure PositiveSizeSurplus)) =
      (graphLaw M lambda n x).map unmarkedProcess := rfl

@[simp] theorem unmarkedWindowLaw_toMeasure (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S) :
    (unmarkedWindowLaw M lambda a b R n x : Measure (PointMeasure (SurplusWindow a b R))) =
      (graphLaw M lambda n x).map (windowPointMeasure a b R 1) := rfl

theorem windowLaw_integrable (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S)
    {f : PointMeasure (SurplusWindow a b R) → ℝ} (hf : Measurable f) :
    Integrable f (unmarkedWindowLaw M lambda a b R n x :
      Measure (PointMeasure (SurplusWindow a b R))) := by
  rw [unmarkedWindowLaw_toMeasure]
  exact (integrable_map_measure hf.aestronglyMeasurable
    (measurable_windowPointMeasure a b R 1 n).aemeasurable).mpr Integrable.of_finite

theorem windowLaw_integral (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S)
    {f : PointMeasure (SurplusWindow a b R) → ℝ} (hf : Measurable f) :
    (∫ η, f η ∂(unmarkedWindowLaw M lambda a b R n x :
      Measure (PointMeasure (SurplusWindow a b R)))) =
      ∫ G, f (windowPointMeasure a b R 1 G) ∂graphLaw M lambda n x := by
  rw [unmarkedWindowLaw_toMeasure]
  exact integral_map (measurable_windowPointMeasure a b R 1 n).aemeasurable hf.aestronglyMeasurable

theorem windowLaw_descFactorial_integrable (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (R n q : ℕ) (x : Fin n → S) :
    Integrable (fun η ↦ ((size η).descFactorial q : ℝ))
      (unmarkedWindowLaw M lambda a b R n x : Measure (PointMeasure (SurplusWindow a b R))) :=
  windowLaw_integrable M lambda a b R n x
    ((measurable_of_countable (fun m : ℕ ↦ (m.descFactorial q : ℝ))).comp measurable_size)

/-- Exact factorial moment identity under the true deterministic graph law. -/
theorem windowLaw_descFactorial_expectation_eq_sum (M : FiniteIrreducibleModel S)
    (lambda a b : ℝ) (hb : 0 ≤ b) (R n q : ℕ) (hn : 0 < n) (x : Fin n → S) :
    (∫ η, ((size η).descFactorial q : ℝ) ∂(unmarkedWindowLaw M lambda a b R n x :
      Measure (PointMeasure (SurplusWindow a b R)))) =
      ∑ r ∈ surplusIndices q R,
        ∑ k ∈ integerWindow ((n : ℝ)^(2/3 : ℝ)) (fun _ ↦ a) (fun _ ↦ b),
          (∫ G, (ComponentCounts.count G k r : ℝ) ∂graphLaw M lambda n x) := by
  have hm : Measurable (fun η : PointMeasure (SurplusWindow a b R) ↦
      ((size η).descFactorial q : ℝ)) :=
    (measurable_of_countable (fun m : ℕ ↦ (m.descFactorial q : ℝ))).comp measurable_size
  rw [windowLaw_integral M lambda a b R n x hm]
  simp_rw [window_size_descFactorial_eq_sum _ hn a b hb R, Nat.cast_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _
    exact integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)
  · intro _ _
    exact Integrable.of_finite

end PerronWright.FiniteIrreducibleComponentProcess
