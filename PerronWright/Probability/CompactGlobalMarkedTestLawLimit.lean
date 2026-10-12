import PerronWright.Probability.GlobalPointMeasureMarking

/-!
# Actual global empirical-marked finite test laws

Every finite family of marked compact-support tests fits in one actual
size-surplus window. Exact source/window identities and the proved
empirical-mark transfer identify its joint law with the canonical
Perron-marked genuine global unmarked limit. No marked source-law
convergence is assumed. This file proves joint test-law convergence,
not yet weak convergence of the entire marked point-measure law.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical CompactlySupported
open scoped PerronWright.ComponentWindowMarkedLaw

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CompactGlobalMarkedTestLawLimit

open ComponentGlobalPointProcess ComponentGlobalMarkedProcess GlobalPointMeasureMarking
open LocallyFinitePointMeasureVague WeakProbabilityMarks ComponentWindowMarkedTransfer
open ComponentWindowPointMeasures ComponentWindowMarkedLaw ComponentWindowMarkedConvergence
open FinitePointMeasureCompact

variable {S D : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]
  [Fintype D]

def globalTestVector (f : D → C_c(MarkedPositiveSizeSurplus S, ℝ))
    (η : LocalPointMeasure (MarkedPositiveSizeSurplus S)) : D → ℝ :=
  fun i ↦ ∫ z, f i z ∂(η : Measure (MarkedPositiveSizeSurplus S))

omit [Fintype D] [CompactSpace S] in
theorem continuous_globalTestVector (f : D → C_c(MarkedPositiveSizeSurplus S, ℝ)) :
    Continuous (globalTestVector f) := continuous_pi (fun i ↦ continuous_integral (f i))

def windowTestVector (a b : ℝ) (R : ℕ) (ha : 0 < a)
    (f : D → C_c(MarkedPositiveSizeSurplus S, ℝ))
    (η : PointMeasure (MarkedWindow S a b R)) : D → ℝ :=
  fun i ↦ ∫ z, f i (markedPositiveWindowEmbedding a b R ha z)
    ∂((η : FiniteMeasure (MarkedWindow S a b R)) : Measure (MarkedWindow S a b R))

omit [Fintype D] in
theorem continuous_windowTestVector (a b : ℝ) (R : ℕ) (ha : 0 < a)
    (f : D → C_c(MarkedPositiveSizeSurplus S, ℝ)) :
    Continuous (windowTestVector a b R ha f) := by
  apply continuous_pi
  intro i
  let g : C(MarkedWindow S a b R, ℝ) :=
    ⟨fun z ↦ f i (markedPositiveWindowEmbedding a b R ha z),
      (f i).continuous.comp (continuous_markedPositiveWindowEmbedding a b R ha)⟩
  exact (FiniteMeasure.continuous_integral_continuousMap g).comp continuous_val

def markedTestLaw (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ)
    (f : D → C_c(MarkedPositiveSizeSurplus S, ℝ)) : ProbabilityMeasure (D → ℝ) :=
  (markedProcessLaw M lambda n).map (continuous_globalTestVector f).measurable.aemeasurable

def canonicalTestLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (μ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus))
    (f : D → C_c(MarkedPositiveSizeSurplus S, ℝ)) : ProbabilityMeasure (D → ℝ) :=
  (canonicalGlobalMarkedLaw M hM μ).map (continuous_globalTestVector f).measurable.aemeasurable

theorem markedTestLaw_eq_window_map (M : CompactBJRModel S) (lambda a b : ℝ)
    (R : ℕ) (ha : 0 < a) (n : ℕ) (f : D → C_c(MarkedPositiveSizeSurplus S, ℝ))
    (hf : ∀ i, tsupport (f i) ⊆ markedWindowSet a b R) :
    markedTestLaw M lambda n f =
      (markedWindowLaw M lambda a b R n).map
        (continuous_windowTestVector a b R ha f).measurable.aemeasurable := by
  apply Subtype.ext
  change ((AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map
      (fun p ↦ markedProcess p.1 (AnnealedTypedGraph.graph p))).map (globalTestVector f) =
    ((AnnealedTypedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n).map
        (fun p ↦ markedWindowPointMeasure p.1 (AnnealedTypedGraph.graph p) a b R)).map
          (windowTestVector a b R ha f)
  rw [Measure.map_map (continuous_globalTestVector f).measurable (measurable_markedProcess n),
    Measure.map_map (continuous_windowTestVector a b R ha f).measurable
      (measurable_markedWindowPointMeasure a b R n)]
  congr 1
  funext p i
  exact markedProcess_integral_eq_window a b R ha p.1 (AnnealedTypedGraph.graph p) (f i) (hf i)

theorem canonicalTestLaw_eq_window_map (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda a b : ℝ) (R : ℕ) (ha : 0 < a) (n : ℕ)
    (f : D → C_c(MarkedPositiveSizeSurplus S, ℝ))
    (hf : ∀ i, tsupport (f i) ⊆ markedWindowSet a b R) :
    canonicalTestLaw M hM (unmarkedProcessLaw M lambda n) f =
      (canonicalPerronMarkedLaw M hM a b R (unmarkedWindowLaw M lambda a b R n)).map
        (continuous_windowTestVector a b R ha f).measurable.aemeasurable := by
  apply Subtype.ext
  change (((AnnealedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map unmarkedProcess).map
      (GlobalPointMeasureMarking.constantMark (perronWeakMark M hM))).map (globalTestVector f) =
    (((AnnealedGraph.law M (CriticalScaling.time lambda n)
      (CriticalScaling.time_nonneg lambda n) n).map (windowPointMeasure a b R 1)).map
        (FinitePointMeasureMarking.constantMark (perronWeakMark M hM))).map (windowTestVector a b R ha f)
  rw [Measure.map_map (continuous_globalTestVector f).measurable
      (GlobalPointMeasureMarking.continuous_constantMark _).measurable,
    Measure.map_map ((continuous_globalTestVector f).comp
      (GlobalPointMeasureMarking.continuous_constantMark _)).measurable (measurable_unmarkedProcess n),
    Measure.map_map (continuous_windowTestVector a b R ha f).measurable
      (FinitePointMeasureMarking.continuous_constantMark _).measurable,
    Measure.map_map ((continuous_windowTestVector a b R ha f).comp
      (FinitePointMeasureMarking.continuous_constantMark _)).measurable
        (measurable_windowPointMeasure a b R 1 n)]
  congr 1
  funext G i
  exact constantMark_process_integral_eq_window _ a b R ha G (f i) (hf i)

theorem means_difference_tendsto_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ)
    (f : D → C_c(MarkedPositiveSizeSurplus S, ℝ)) (G : (D → ℝ) →ᵇ ℝ) :
    Tendsto (fun n ↦ (∫ z, G z ∂(markedTestLaw M lambda n f : Measure (D → ℝ))) -
      (∫ z, G z ∂(canonicalTestLaw M hM (unmarkedProcessLaw M lambda n) f : Measure (D → ℝ))))
        atTop (𝓝 0) := by
  obtain ⟨a, b, R, ha, hab, hf⟩ := exists_marked_test_window f
  let F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ :=
    G.compContinuous ⟨windowTestVector a b R ha f, continuous_windowTestVector a b R ha f⟩
  have hdiff := ComponentWindowMarkedConvergence.means_difference_tendsto_zero
    M hM hQP lambda a b ha hab R F
  convert hdiff using 1
  funext n
  rw [markedTestLaw_eq_window_map M lambda a b R ha n f hf,
    canonicalTestLaw_eq_window_map M hM lambda a b R ha n f hf]
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [integral_map (continuous_windowTestVector a b R ha f).measurable.aemeasurable
      G.continuous.measurable.aestronglyMeasurable,
    integral_map (continuous_windowTestVector a b R ha f).measurable.aemeasurable
      G.continuous.measurable.aestronglyMeasurable]
  rfl

/-- The joint law of any genuine finite family of marked vague-test
integrals converges to the actual canonical-Perron marked global limit.
This uses the proved real empirical concentration, not a marked-law
convergence or target-marking interface. -/
theorem markedTestLaw_tendsto_canonical (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ)
    (f : D → C_c(MarkedPositiveSizeSurplus S, ℝ)) :
    Tendsto (fun n ↦ markedTestLaw M lambda n f) atTop
      (𝓝 ((canonicalGlobalMarkedLimitLaw M hM hQP lambda).map
        (continuous_globalTestVector f).measurable.aemeasurable)) := by
  have hc := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n ↦ canonicalGlobalMarkedLaw M hM (unmarkedProcessLaw M lambda n))
    (canonicalGlobalMarkedLimitLaw M hM hQP lambda)
    (tendsto_canonicalGlobalMarkedLaw M hM hQP lambda) (continuous_globalTestVector f)
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro G
  have hCG := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hc G
  have hdiff := means_difference_tendsto_zero M hM hQP lambda f G
  simpa only [canonicalTestLaw, zero_add, sub_add_cancel] using hdiff.add hCG

end PerronWright.CompactGlobalMarkedTestLawLimit
