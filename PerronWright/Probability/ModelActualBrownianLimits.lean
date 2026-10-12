import PerronWright.Probability.ModelGraphUniformLocalBridge
import PerronWright.Probability.GraphBrownianGlobalLimit
import PerronWright.Probability.FiniteIrreducibleMarkedWindowConvergence
import PerronWright.Probability.FiniteIrreducibleMarkedGlobalConvergence
import PerronWright.Probability.FiniteIrreducibleGlobalMarkedSizeRescaling
import PerronWright.Probability.ComponentWindowMarkedConvergence
import PerronWright.Probability.GlobalMarkedPointSizeRescaling

/-! # Model-only convergence to the actual Brownian excursion process

The genuine uniform local model estimates discharge the generic graph
condition. The successor-indexed graph limits therefore give the entire
model sequence, not only a subsequence. Actual empirical probability
marks converge to the proved Perron marking of the actual Brownian law.
Literal beta^(1/3) size dilation gives the starred laws of the paper.
-/

open MeasureTheory Filter Topology
open scoped Real Classical Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.ModelActualBrownianLimits

open ModelGraphUniformLocalBridge BrownianInverseSizeLaw
open GlobalPointSizeRescaling GlobalMarkedPointSizeRescaling
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

section Finite

variable {S : Type*} [Fintype S] [DecidableEq S]

private instance finiteSource_probability (M : FiniteIrreducibleModel S)
    (lambda : ℝ) (x : (n : ℕ) → Fin n → S) :
    ∀ n, IsProbabilityMeasure (finiteGraphSource M lambda x n) := fun n ↦
  inferInstanceAs (IsProbabilityMeasure
    (FiniteIrreducibleComponentProcess.graphLaw M lambda (n+1) (x (n+1))))

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Any bounded-count-error assignment has the actual Brownian window
limit. The finite kernel is only irreducible, not strictly positive. -/
theorem finite_windowLaw_tendsto_actual_Brownian (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    Tendsto (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedWindowLaw
      M lambda a b R n (x n)) atTop
      (𝓝 (BrownianInverseWindowLaw.law (M.alpha hM*M.beta hM^(-2/3 : ℝ)*lambda)
        a b R (Real.rpow_pos_of_pos (M.beta_pos hM) (1/3 : ℝ)) ha hab)) := by
  have h := GraphBrownianWindowLimit.windowLaw_tendsto_actual_Brownian
    (finiteGraphSource M lambda x) (M.beta_pos hM)
    (finite_hasUniformLocalLimit M hM lambda x D hD hround) ha hab R
  change Tendsto (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedWindowLaw
    M lambda a b R (n+1) (x (n+1))) atTop _ at h
  exact (tendsto_add_atTop_iff_nat 1).mp h

/-- The actual finite irreducible global law converges on the full
vague-Borel point-measure space. -/
theorem finite_processLaw_tendsto_actual_Brownian (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    Tendsto (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedProcessLaw
      M lambda n (x n)) atTop
      (𝓝 (inverseScaledLaw (M.alpha hM*M.beta hM^(-2/3 : ℝ)*lambda)
        (Real.rpow_pos_of_pos (M.beta_pos hM) (1/3 : ℝ)))) := by
  have h := GraphBrownianGlobalLimit.processLaw_tendsto_actual_Brownian
    (finiteGraphSource M lambda x) (M.beta_pos hM)
    (finite_hasUniformLocalLimit M hM lambda x D hD hround)
  change Tendsto (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedProcessLaw
    M lambda (n+1) (x (n+1))) atTop _ at h
  exact (tendsto_add_atTop_iff_nat 1).mp h

/-- The literal empirical type marks have the actual constant-Perron
Brownian window limit. -/
theorem finite_markedWindowLaw_tendsto_actual_Brownian (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    Tendsto (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedWindowLaw
      M lambda a b R n (x n)) atTop
      (𝓝 (FiniteIrreducibleMarkedWindowConvergence.canonicalPerronMarkedLaw M hM a b R
        (BrownianInverseWindowLaw.law (M.alpha hM*M.beta hM^(-2/3 : ℝ)*lambda)
          a b R (Real.rpow_pos_of_pos (M.beta_pos hM) (1/3 : ℝ)) ha hab))) := by
  simpa only [id_eq] using
    FiniteIrreducibleMarkedWindowConvergence.markedWindowLaw_tendsto_of_unmarked
      M hM lambda a b ha hab R x D hD hround id tendsto_id _
      (finite_windowLaw_tendsto_actual_Brownian M hM lambda a b ha hab R x D hD hround)

/-- Whole empirical-marked global laws, not only individual component
marks, converge to actual Perron-marked Brownian point measures. -/
theorem finite_markedProcessLaw_tendsto_actual_Brownian (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    Tendsto (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedProcessLaw
      M lambda n (x n)) atTop
      (𝓝 (FiniteIrreducibleMarkedGlobalTests.canonicalGlobalMarkedLaw M hM
        (inverseScaledLaw (M.alpha hM*M.beta hM^(-2/3 : ℝ)*lambda)
          (Real.rpow_pos_of_pos (M.beta_pos hM) (1/3 : ℝ))))) := by
  simpa only [id_eq] using
    FiniteIrreducibleMarkedGlobalConvergence.markedProcessLaw_tendsto_of_unmarked
      M hM lambda x D hD hround id tendsto_id _
      (finite_processLaw_tendsto_actual_Brownian M hM lambda x D hD hround)

/-- Literal starred finite component laws converge to the actual Aldous
excursion law at the paper's transformed parameter. -/
theorem finite_starredProcessLaw_tendsto_actual_Brownian (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    Tendsto (fun n ↦ FiniteIrreducibleGlobalSizeRescaling.starredProcessLaw
      M hM lambda n (x n)) atTop
      (𝓝 (BrownianExcursionPointProcessLaw.law (M.alpha hM*M.beta hM^(-2/3 : ℝ)*lambda))) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (finite_processLaw_tendsto_actual_Brownian M hM lambda x D hD hround)
    (continuous_scalePoint (FiniteIrreduciblePointProcessNormalization.sizeScale_pos M hM))
  simpa only [FiniteIrreducibleGlobalSizeRescaling.starredProcessLaw,
    FiniteIrreducibleGlobalSizeRescaling.scaledProcessLaw_eq_map,
    inverseScaledLaw_map] using h

/-- The starred size map leaves genuine empirical type marks unchanged. -/
theorem finite_starredMarkedProcessLaw_tendsto_actual_Brownian (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(fiberCount (x n) s : ℝ) - (n : ℝ)*M.weight s| ≤ D) :
    Tendsto (fun n ↦ FiniteIrreducibleGlobalMarkedSizeRescaling.starredMarkedProcessLaw
      M hM lambda n (x n)) atTop
      (𝓝 (FiniteIrreducibleMarkedGlobalTests.canonicalGlobalMarkedLaw M hM
        (BrownianExcursionPointProcessLaw.law (M.alpha hM*M.beta hM^(-2/3 : ℝ)*lambda)))) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (finite_markedProcessLaw_tendsto_actual_Brownian M hM lambda x D hD hround)
    (continuous_scaleMarkedPoint
      (FiniteIrreduciblePointProcessNormalization.sizeScale_pos M hM))
  simpa only [FiniteIrreducibleGlobalMarkedSizeRescaling.starredMarkedProcessLaw,
    FiniteIrreducibleGlobalMarkedSizeRescaling.scaledMarkedProcessLaw_eq_map,
    FiniteIrreducibleGlobalMarkedSizeRescaling.canonicalGlobalMarkedLaw_scale,
    inverseScaledLaw_map] using h

end Finite

section Compact

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

private instance compactSource_probability (M : CompactBJRModel S) (lambda : ℝ) :
    ∀ n, IsProbabilityMeasure (compactGraphSource M lambda n) := fun n ↦
  inferInstanceAs (IsProbabilityMeasure (AnnealedGraph.law M
    (CriticalScaling.time lambda (n+1)) (CriticalScaling.time_nonneg lambda (n+1)) (n+1)))

/-- Actual regular compact graph windows converge to actual Brownian
windows under the paper's model assumptions. -/
theorem compact_windowLaw_tendsto_actual_Brownian (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    Tendsto (fun n ↦ ComponentWindowPointMeasures.unmarkedWindowLaw M lambda a b R n) atTop
      (𝓝 (BrownianInverseWindowLaw.law (M.alpha hM*M.beta hM^(-2/3 : ℝ)*lambda)
        a b R (Real.rpow_pos_of_pos (M.beta_pos hM) (1/3 : ℝ)) ha hab)) := by
  have h := GraphBrownianWindowLimit.windowLaw_tendsto_actual_Brownian
    (compactGraphSource M lambda) (M.beta_pos hM)
    (compact_hasUniformLocalLimit M hM hQP lambda) ha hab R
  change Tendsto (fun n ↦ ComponentWindowPointMeasures.unmarkedWindowLaw
    M lambda a b R (n+1)) atTop _ at h
  exact (tendsto_add_atTop_iff_nat 1).mp h

/-- The whole compact-model vague law is the inverse-dilated actual
Brownian excursion point-process law. -/
theorem compact_processLaw_tendsto_actual_Brownian (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    Tendsto (fun n ↦ ComponentGlobalPointProcess.unmarkedProcessLaw M lambda n) atTop
      (𝓝 (inverseScaledLaw (M.alpha hM*M.beta hM^(-2/3 : ℝ)*lambda)
        (Real.rpow_pos_of_pos (M.beta_pos hM) (1/3 : ℝ)))) := by
  have h := GraphBrownianGlobalLimit.processLaw_tendsto_actual_Brownian
    (compactGraphSource M lambda) (M.beta_pos hM)
    (compact_hasUniformLocalLimit M hM hQP lambda)
  change Tendsto (fun n ↦ ComponentGlobalPointProcess.unmarkedProcessLaw
    M lambda (n+1)) atTop _ at h
  exact (tendsto_add_atTop_iff_nat 1).mp h

/-- Actual compact empirical probability marks converge on each closed
window to the actual Perron marking of the Brownian window law. -/
theorem compact_markedWindowLaw_tendsto_actual_Brownian (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (R : ℕ) :
    Tendsto (fun n ↦ ComponentWindowMarkedLaw.markedWindowLaw M lambda a b R n) atTop
      (𝓝 (ComponentWindowMarkedConvergence.canonicalPerronMarkedLaw M hM a b R
        (BrownianInverseWindowLaw.law (M.alpha hM*M.beta hM^(-2/3 : ℝ)*lambda)
          a b R (Real.rpow_pos_of_pos (M.beta_pos hM) (1/3 : ℝ)) ha hab))) := by
  simpa only [id_eq] using
    ComponentWindowMarkedConvergence.markedWindowLaw_tendsto_of_unmarked
      M hM hQP lambda a b ha hab R id tendsto_id _
      (compact_windowLaw_tendsto_actual_Brownian M hM hQP lambda a b ha hab R)

/-- The entire actual compact marked global law has the literal
constant-Perron marking of the actual Brownian global law as its limit. -/
theorem compact_markedProcessLaw_tendsto_actual_Brownian (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    Tendsto (fun n ↦ ComponentGlobalMarkedProcess.markedProcessLaw M lambda n) atTop
      (𝓝 (GlobalPointMeasureMarking.canonicalGlobalMarkedLaw M hM
        (inverseScaledLaw (M.alpha hM*M.beta hM^(-2/3 : ℝ)*lambda)
          (Real.rpow_pos_of_pos (M.beta_pos hM) (1/3 : ℝ))))) := by
  have he := tendsto_nhds_unique
    (CompactGlobalPointLawLimit.tendsto_unmarkedProcessLimitLaw M hM hQP lambda)
    (compact_processLaw_tendsto_actual_Brownian M hM hQP lambda)
  simpa only [GlobalPointMeasureMarking.canonicalGlobalMarkedLimitLaw,he] using
    CompactGlobalMarkedPointLawLimit.tendsto_markedProcessLaw_canonical M hM hQP lambda

/-- The literal starred regular compact process has the actual Aldous
law at the paper's transformed critical parameter. -/
theorem compact_starredProcessLaw_tendsto_actual_Brownian (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    Tendsto (GlobalPointSizeRescaling.starredProcessLaw M hM lambda) atTop
      (𝓝 (BrownianExcursionPointProcessLaw.law (M.alpha hM*M.beta hM^(-2/3 : ℝ)*lambda))) := by
  change Tendsto (fun n ↦ GlobalPointSizeRescaling.scaledProcessLaw M lambda
    (ComponentPointProcesses.sizeScale_pos M hM) n) atTop _
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (compact_processLaw_tendsto_actual_Brownian M hM hQP lambda)
    (continuous_scalePoint (ComponentPointProcesses.sizeScale_pos M hM))
  simpa only [GlobalPointSizeRescaling.starredProcessLaw,
    GlobalPointSizeRescaling.scaledProcessLaw_eq_map,inverseScaledLaw_map] using h

/-- Literal starred empirical-marked compact laws converge to the
actual Perron-marked Aldous law, without a Brownian interface premise. -/
theorem compact_starredMarkedProcessLaw_tendsto_actual_Brownian (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    Tendsto (GlobalMarkedPointSizeRescaling.starredMarkedProcessLaw M hM lambda) atTop
      (𝓝 (GlobalPointMeasureMarking.canonicalGlobalMarkedLaw M hM
        (BrownianExcursionPointProcessLaw.law (M.alpha hM*M.beta hM^(-2/3 : ℝ)*lambda)))) := by
  change Tendsto (fun n ↦ GlobalMarkedPointSizeRescaling.scaledMarkedProcessLaw M lambda
    (ComponentPointProcesses.sizeScale_pos M hM) n) atTop _
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (compact_markedProcessLaw_tendsto_actual_Brownian M hM hQP lambda)
    (continuous_scaleMarkedPoint (ComponentPointProcesses.sizeScale_pos M hM))
  simpa only [GlobalMarkedPointSizeRescaling.starredMarkedProcessLaw,
    GlobalMarkedPointSizeRescaling.scaledMarkedProcessLaw_eq_map,
    GlobalMarkedPointSizeRescaling.canonicalGlobalMarkedLaw_scale,
    inverseScaledLaw_map] using h

end Compact

end PerronWright.ModelActualBrownianLimits
