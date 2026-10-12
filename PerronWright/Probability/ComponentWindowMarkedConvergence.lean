import PerronWright.Probability.ComponentWindowMarkedTransfer

/-! # Actual marked window-law composition along unmarked weak subsequences

This is an intermediate source-composition theorem. The only source
convergence parameter concerns the actual unmarked graph window law;
all empirical-mark measurability, tightness and bounded-test transfer
have already been proved from the actual model.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Topology
open scoped PerronWright.ComponentWindowMarkedLaw

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.ComponentWindowMarkedConvergence

open WeakProbabilityMarks FinitePointMeasureCompact FinitePointMeasureMarking
  ComponentWindowPointMeasures ComponentWindowMarkedLaw ComponentWindowMarkedTransfer ProfileSquareMoment

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- Explicit push-forward of a genuine unmarked point-process law by
attaching the actual Perron probability measure to every atom. -/
def canonicalPerronMarkedLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (a b : ℝ) (R : ℕ) (μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R))) :
    ProbabilityMeasure (PointMeasure (MarkedWindow S a b R)) :=
  canonicalMarkedLaw (perronWeakMark M hM) μ

theorem continuous_canonicalPerronMarkedLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (a b : ℝ) (R : ℕ) : Continuous (canonicalPerronMarkedLaw M hM a b R) :=
  continuous_canonicalMarkedLaw (perronWeakMark M hM)

theorem canonicalPerronMarkedLaw_integral (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda a b : ℝ) (R n : ℕ) (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) :
    (∫ η, F η ∂(canonicalPerronMarkedLaw M hM a b R (unmarkedWindowLaw M lambda a b R n) : Measure _)) =
      ∫ p, F (constantMark (perronWeakMark M hM)
        (windowPointMeasure a b R 1 (AnnealedTypedGraph.graph p)))
          ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
            (CriticalScaling.time_nonneg lambda n) n := by
  calc
    _ = ∫ η, F (constantMark (perronWeakMark M hM) η)
        ∂(unmarkedWindowLaw M lambda a b R n : Measure _) := by
      unfold canonicalPerronMarkedLaw canonicalMarkedLaw
      rw [ProbabilityMeasure.toMeasure_map]
      exact integral_map (continuous_constantMark _).measurable.aemeasurable F.continuous.measurable.aestronglyMeasurable
    _ = ∫ G, F (constantMark (perronWeakMark M hM) (windowPointMeasure a b R 1 G))
        ∂AnnealedGraph.law M (CriticalScaling.time lambda n)
          (CriticalScaling.time_nonneg lambda n) n :=
      windowLaw_integral M lambda a b R 1 n
        ((F.continuous.comp (continuous_constantMark (perronWeakMark M hM))).measurable)
    _ = _ := (AnnealedTypedGraph.graph_expectation M _ (CriticalScaling.time_nonneg lambda n) n
      (fun G ↦ F (constantMark (perronWeakMark M hM) (windowPointMeasure a b R 1 G)))).symm

theorem means_difference_integral (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda a b : ℝ) (R n : ℕ) (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) :
    (∫ η, F η ∂(markedWindowLaw M lambda a b R n : Measure _)) -
      (∫ η, F η ∂(canonicalPerronMarkedLaw M hM a b R (unmarkedWindowLaw M lambda a b R n) : Measure _)) =
        ∫ p, testDifference M hM a b R n F p
          ∂AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
            (CriticalScaling.time_nonneg lambda n) n := by
  let μ := AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n
  have hA : Integrable (fun p : AnnealedTypedGraph.State S n ↦
      F (markedWindowPointMeasure p.1 (AnnealedTypedGraph.graph p) a b R)) μ :=
    integrable_of_measurable_abs_le μ
      (F.continuous.measurable.comp (measurable_markedWindowPointMeasure a b R n))
      (fun _ ↦ norm_coe_le_norm F _)
  have hC : Integrable (fun p : AnnealedTypedGraph.State S n ↦
      F (constantMark (perronWeakMark M hM) (windowPointMeasure a b R 1 (AnnealedTypedGraph.graph p)))) μ :=
    integrable_of_measurable_abs_le μ
      ((F.continuous.comp (continuous_constantMark _)).measurable.comp
        ((measurable_windowPointMeasure a b R 1 n).comp (AnnealedTypedGraph.measurable_graph n)))
      (fun _ ↦ norm_coe_le_norm F _)
  rw [markedWindowLaw_integral M lambda a b R n F.continuous.measurable,
    canonicalPerronMarkedLaw_integral M hM lambda a b R n F,← integral_sub hA hC]
  rfl

/-- The actual marked-law and canonical-marked-unmarked-law means are
asymptotically equal for every bounded continuous point-process test. -/
theorem means_difference_tendsto_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ) :
    Tendsto (fun n ↦ (∫ η, F η ∂(markedWindowLaw M lambda a b R n : Measure _)) -
      (∫ η, F η ∂(canonicalPerronMarkedLaw M hM a b R (unmarkedWindowLaw M lambda a b R n) : Measure _)))
        atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _
    (testDifference_l1_tendsto_zero M hM hQP lambda a b ha hab R F)
  exact Eventually.of_forall (fun n ↦ by
    rw [means_difference_integral M hM lambda a b R n F]
    exact abs_integral_le_integral_abs)

/-- Intermediate composition theorem for an arbitrary actual unmarked
weak subsequence. The corresponding actual marked graph law converges
to the explicit constant-Perron push-forward of that source limit. -/
theorem markedWindowLaw_tendsto_of_unmarked (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hsource : Tendsto (fun n ↦ unmarkedWindowLaw M lambda a b R (N n)) atTop (𝓝 μ)) :
    Tendsto (fun n ↦ markedWindowLaw M lambda a b R (N n)) atTop
      (𝓝 (canonicalPerronMarkedLaw M hM a b R μ)) := by
  have hc := (continuous_canonicalPerronMarkedLaw M hM a b R).tendsto μ |>.comp hsource
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  have hCF := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hc F
  have hdiff := (means_difference_tendsto_zero M hM hQP lambda a b ha hab R F).comp hN
  simpa only [Function.comp_apply,zero_add,sub_add_cancel] using hdiff.add hCF

end PerronWright.ComponentWindowMarkedConvergence
