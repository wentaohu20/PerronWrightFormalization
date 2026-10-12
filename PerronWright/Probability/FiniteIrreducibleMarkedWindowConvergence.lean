import PerronWright.Probability.FiniteIrreducibleMarkedWindowTransfer

/-! # Actual fixed-assignment marked window-law composition

Unconditional bounded-test transfer is proved below. The last theorem
is explicitly a source-composition lemma along an actual unmarked weak
subsequence, not a model-only existence claim for the spatial limit.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000

namespace PerronWright.FiniteIrreducibleMarkedWindowConvergence

open FiniteIrreducibleMarkedComponentProcess FiniteIrreducibleMarkedWindowTransfer
  ComponentWindowMarkedLaw ComponentWindowPointMeasures WeakProbabilityMarks
  FinitePointMeasureCompact FinitePointMeasureMarking
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def canonicalPerronMarkedLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (a b : ℝ) (R : ℕ) (μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R))) :
    ProbabilityMeasure (PointMeasure (MarkedWindow S a b R)) :=
  canonicalMarkedLaw (perronWeakMark M hM) μ

omit [DiscreteTopology S] in
theorem continuous_canonicalPerronMarkedLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (a b : ℝ) (R : ℕ) : Continuous (canonicalPerronMarkedLaw M hM a b R) :=
  continuous_canonicalMarkedLaw (perronWeakMark M hM)

omit [DiscreteTopology S] in
theorem canonicalPerronMarkedLaw_integral (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S)
    (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) :
    (∫ η, F η ∂(canonicalPerronMarkedLaw M hM a b R
      (FiniteIrreducibleComponentProcess.unmarkedWindowLaw M lambda a b R n x) : Measure _)) =
      ∫ G, F (constantMark (perronWeakMark M hM) (windowPointMeasure a b R 1 G))
        ∂FiniteIrreducibleComponentProcess.graphLaw M lambda n x := by
  unfold canonicalPerronMarkedLaw canonicalMarkedLaw
  rw [ProbabilityMeasure.toMeasure_map,integral_map
    (continuous_constantMark _).measurable.aemeasurable F.continuous.measurable.aestronglyMeasurable]
  exact FiniteIrreducibleComponentProcess.windowLaw_integral M lambda a b R n x
    (f := fun η ↦ F (constantMark (perronWeakMark M hM) η))
    ((F.continuous.comp (continuous_constantMark _)).measurable)

omit [DiscreteTopology S] in
theorem means_difference_integral (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S)
    (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) :
    (∫ η, F η ∂(FiniteIrreducibleMarkedComponentProcess.markedWindowLaw M lambda a b R n x : Measure _)) -
      (∫ η, F η ∂(canonicalPerronMarkedLaw M hM a b R
        (FiniteIrreducibleComponentProcess.unmarkedWindowLaw M lambda a b R n x) : Measure _)) =
      ∫ G, testDifference M hM a b R n x F G
        ∂FiniteIrreducibleComponentProcess.graphLaw M lambda n x := by
  rw [FiniteIrreducibleMarkedComponentProcess.markedWindowLaw_integral M lambda a b R n x
    F.continuous.measurable,canonicalPerronMarkedLaw_integral M hM lambda a b R n x F]
  rw [← integral_sub Integrable.of_finite Integrable.of_finite]
  rfl

theorem means_difference_tendsto_zero (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) :
    Tendsto (fun n ↦
      (∫ η, F η ∂(FiniteIrreducibleMarkedComponentProcess.markedWindowLaw M lambda a b R n (x n) : Measure _)) -
      (∫ η, F η ∂(canonicalPerronMarkedLaw M hM a b R
        (FiniteIrreducibleComponentProcess.unmarkedWindowLaw M lambda a b R n (x n)) : Measure _)))
      atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _
    (testDifference_l1_tendsto_zero M hM lambda a b ha hab R x D hD hround F)
  exact Eventually.of_forall (fun n ↦ by
    rw [means_difference_integral M hM lambda a b R n (x n) F]
    exact abs_integral_le_integral_abs)

theorem markedWindowLaw_tendsto_of_unmarked (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hsource : Tendsto (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedWindowLaw
      M lambda a b R (N n) (x (N n))) atTop (𝓝 μ)) :
    Tendsto (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedWindowLaw
      M lambda a b R (N n) (x (N n))) atTop (𝓝 (canonicalPerronMarkedLaw M hM a b R μ)) := by
  have hc := (continuous_canonicalPerronMarkedLaw M hM a b R).tendsto μ |>.comp hsource
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  have hCF := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hc F
  have hdiff := (means_difference_tendsto_zero M hM lambda a b ha hab R x D hD hround F).comp hN
  simpa only [Function.comp_apply,zero_add,sub_add_cancel] using hdiff.add hCF

end PerronWright.FiniteIrreducibleMarkedWindowConvergence
