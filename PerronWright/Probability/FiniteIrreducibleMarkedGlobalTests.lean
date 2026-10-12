import PerronWright.Probability.FiniteIrreducibleMarkedWindowConvergence
import PerronWright.Probability.CompactGlobalMarkedTestLawLimit

/-! # Actual deterministic global joint marked test-law transfer

All finite compact-support test families fit in a genuine window. The
actual empirical-marked graph and its constant-Perron marking have
asymptotically identical coupled bounded-continuous joint test means.
The source-composition theorem is explicitly conditional on convergence
of the actual unmarked source; no target existence is postulated here.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical CompactlySupported
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleMarkedGlobalTests

open FiniteIrreducibleMarkedComponentProcess FiniteIrreducibleMarkedWindowConvergence
  ComponentGlobalPointProcess ComponentGlobalMarkedProcess ComponentWindowMarkedLaw
  ComponentWindowPointMeasures
  GlobalPointMeasureMarking LocallyFinitePointMeasureVague FinitePointMeasureCompact
  CompactGlobalMarkedTestLawLimit
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S D₀ : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] [Fintype D₀]

def canonicalGlobalMarkedLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (μ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus)) :
    ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  μ.map (GlobalPointMeasureMarking.continuous_constantMark (perronWeakMark M hM)).measurable.aemeasurable

omit [Fintype D₀] [DiscreteTopology S] in
theorem continuous_canonicalGlobalMarkedLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    Continuous (canonicalGlobalMarkedLaw M hM) :=
  ProbabilityMeasure.continuous_map (GlobalPointMeasureMarking.continuous_constantMark (perronWeakMark M hM))

def markedTestLaw (M : FiniteIrreducibleModel S) (lambda : ℝ) (n : ℕ) (x : Fin n → S)
    (f : D₀ → C_c(MarkedPositiveSizeSurplus S, ℝ)) : ProbabilityMeasure (D₀ → ℝ) :=
  (FiniteIrreducibleMarkedComponentProcess.markedProcessLaw M lambda n x).map
    (continuous_globalTestVector f).measurable.aemeasurable

def canonicalTestLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (μ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus))
    (f : D₀ → C_c(MarkedPositiveSizeSurplus S, ℝ)) : ProbabilityMeasure (D₀ → ℝ) :=
  (canonicalGlobalMarkedLaw M hM μ).map (continuous_globalTestVector f).measurable.aemeasurable

omit [DiscreteTopology S] in
theorem markedTestLaw_eq_window_map (M : FiniteIrreducibleModel S) (lambda a b : ℝ)
    (R : ℕ) (ha : 0 < a) (n : ℕ) (x : Fin n → S)
    (f : D₀ → C_c(MarkedPositiveSizeSurplus S, ℝ))
    (hf : ∀ i, tsupport (f i) ⊆ markedWindowSet a b R) :
    markedTestLaw M lambda n x f =
      (FiniteIrreducibleMarkedComponentProcess.markedWindowLaw M lambda a b R n x).map
        (continuous_windowTestVector a b R ha f).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((FiniteIrreducibleComponentProcess.graphLaw M lambda n x).map
    (fun G ↦ markedProcess x G)).map (globalTestVector f) =
    ((FiniteIrreducibleComponentProcess.graphLaw M lambda n x).map
      (fun G ↦ markedWindowPointMeasure x G a b R)).map (windowTestVector a b R ha f)
  rw [Measure.map_map (continuous_globalTestVector f).measurable
      (FiniteIrreducibleMarkedComponentProcess.measurable_markedProcess x),
    Measure.map_map (continuous_windowTestVector a b R ha f).measurable
      (FiniteIrreducibleMarkedComponentProcess.measurable_markedWindowPointMeasure x a b R)]
  congr 1
  funext G i
  exact markedProcess_integral_eq_window a b R ha x G (f i) (hf i)

omit [DiscreteTopology S] in
theorem canonicalTestLaw_eq_window_map (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda a b : ℝ) (R : ℕ) (ha : 0 < a) (n : ℕ) (x : Fin n → S)
    (f : D₀ → C_c(MarkedPositiveSizeSurplus S, ℝ))
    (hf : ∀ i, tsupport (f i) ⊆ markedWindowSet a b R) :
    canonicalTestLaw M hM (FiniteIrreducibleComponentProcess.unmarkedProcessLaw M lambda n x) f =
      (canonicalPerronMarkedLaw M hM a b R
        (FiniteIrreducibleComponentProcess.unmarkedWindowLaw M lambda a b R n x)).map
          (continuous_windowTestVector a b R ha f).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change (((FiniteIrreducibleComponentProcess.graphLaw M lambda n x).map unmarkedProcess).map
    (GlobalPointMeasureMarking.constantMark (perronWeakMark M hM))).map (globalTestVector f) =
    (((FiniteIrreducibleComponentProcess.graphLaw M lambda n x).map (windowPointMeasure a b R 1)).map
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

/-- Genuine finite families of global vague-test integrals, including
coupled bounded-continuous tests, collapse to the actual Perron marking. -/
theorem means_difference_tendsto_zero (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (f : D₀ → C_c(MarkedPositiveSizeSurplus S, ℝ)) (G : (D₀ → ℝ) →ᵇ ℝ) :
    Tendsto (fun n ↦ (∫ z, G z ∂(markedTestLaw M lambda n (x n) f : Measure (D₀ → ℝ))) -
      (∫ z, G z ∂(canonicalTestLaw M hM
        (FiniteIrreducibleComponentProcess.unmarkedProcessLaw M lambda n (x n)) f : Measure (D₀ → ℝ))))
      atTop (𝓝 0) := by
  obtain ⟨a,b,R,ha,hab,hf⟩ := exists_marked_test_window f
  let F : PointMeasure (MarkedWindow S a b R) →ᵇ ℝ :=
    G.compContinuous ⟨windowTestVector a b R ha f,continuous_windowTestVector a b R ha f⟩
  have hdiff := FiniteIrreducibleMarkedWindowConvergence.means_difference_tendsto_zero
    M hM lambda a b ha hab R x D hD hround F
  convert hdiff using 1
  funext n
  rw [markedTestLaw_eq_window_map M lambda a b R ha n (x n) f hf,
    canonicalTestLaw_eq_window_map M hM lambda a b R ha n (x n) f hf]
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [integral_map (continuous_windowTestVector a b R ha f).measurable.aemeasurable
      G.continuous.measurable.aestronglyMeasurable,
    integral_map (continuous_windowTestVector a b R ha f).measurable.aemeasurable
      G.continuous.measurable.aestronglyMeasurable]
  rfl

theorem markedTestLaw_tendsto_of_unmarked (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus))
    (hsource : Tendsto (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedProcessLaw
      M lambda (N n) (x (N n))) atTop (𝓝 μ))
    (f : D₀ → C_c(MarkedPositiveSizeSurplus S, ℝ)) :
    Tendsto (fun n ↦ markedTestLaw M lambda (N n) (x (N n)) f) atTop
      (𝓝 ((canonicalGlobalMarkedLaw M hM μ).map
        (continuous_globalTestVector f).measurable.aemeasurable)) := by
  have hcan := (continuous_canonicalGlobalMarkedLaw M hM).tendsto μ |>.comp hsource
  have hc := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n ↦ canonicalGlobalMarkedLaw M hM
      (FiniteIrreducibleComponentProcess.unmarkedProcessLaw M lambda (N n) (x (N n))))
    (canonicalGlobalMarkedLaw M hM μ) hcan (continuous_globalTestVector f)
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro G
  have hCG := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hc G
  have hdiff := (means_difference_tendsto_zero M hM lambda x D hD hround f G).comp hN
  simpa only [canonicalTestLaw,Function.comp_apply,zero_add,sub_add_cancel] using hdiff.add hCG

end PerronWright.FiniteIrreducibleMarkedGlobalTests
