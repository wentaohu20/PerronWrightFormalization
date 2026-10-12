import PerronWright.Probability.GlobalMarkedPointSizeRescaling
import PerronWright.Probability.FiniteIrreducibleGlobalSizeRescaling
import PerronWright.Probability.FiniteIrreducibleMarkedPointLawLimit

/-! # Literal deterministic empirical-marked starred global weak limits

Positive dilation changes size alone; actual component empirical marks
and surplus are unchanged. Canonical finite Perron marking commutes with
the proved proper point pushforward as an exact law identity. The source
marked full weak limit was proved, not assumed. No Brownian identity is
asserted.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleGlobalMarkedSizeRescaling

open ComponentGlobalPointProcess ComponentGlobalMarkedProcess LocallyFinitePointMeasureVague
open WeakProbabilityMarks GlobalPointMeasureMarking ComponentWindowPointMeasures EmpiricalTypeMarks
open GlobalPointSizeRescaling (positiveSizeScale scalePoint continuous_scalePoint)
open GlobalMarkedPointSizeRescaling (markedSizeScale scaleMarkedPoint continuous_scaleMarkedPoint
  scaledMarkedProcess scaledMarkedProcess_eq_map markedSizeScale_atom_size markedSizeScale_atom_mark
  scaleMarkedPoint_constantMark)
open FiniteIrreduciblePointProcessNormalization
open FiniteIrreducibleGlobalSizeRescaling (scaledProcessLimitLaw starredProcessLimitLaw)
open FiniteIrreducibleMarkedGlobalTests (canonicalGlobalMarkedLaw)
open FiniteIrreducibleMarkedComponentProcess (perronWeakMark)
open FiniteIrreducibleMarkedPointLawLimit
  (canonicalGlobalMarkedLimitLaw tendsto_markedProcessLaw_canonical)
open FiniteIrreducibleComponentProcess (graphLaw)
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def scaledMarkedProcessLaw (M : FiniteIrreducibleModel S) (lambda : ℝ) {c : ℝ}
    (hc : 0 < c) (n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  ⟨(graphLaw M lambda n x).map (fun G ↦ scaledMarkedProcess hc x G),
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable⟩

omit [DiscreteTopology S] in
theorem scaledMarkedProcessLaw_eq_map (M : FiniteIrreducibleModel S) (lambda : ℝ)
    {c : ℝ} (hc : 0 < c) (n : ℕ) (x : Fin n → S) :
    scaledMarkedProcessLaw M lambda hc n x =
      (FiniteIrreducibleMarkedComponentProcess.markedProcessLaw M lambda n x).map
        (continuous_scaleMarkedPoint hc).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change (graphLaw M lambda n x).map (fun G ↦ scaledMarkedProcess hc x G) =
    ((graphLaw M lambda n x).map (fun G ↦ markedProcess x G)).map (scaleMarkedPoint hc)
  rw [Measure.map_map (continuous_scaleMarkedPoint hc).measurable
    (FiniteIrreducibleMarkedComponentProcess.measurable_markedProcess x)]
  congr 1
  exact funext (scaledMarkedProcess_eq_map hc x)

omit [DiscreteTopology S] in
theorem scaledMarkedProcessLaw_integral (M : FiniteIrreducibleModel S) (lambda : ℝ)
    {c : ℝ} (hc : 0 < c) (n : ℕ) (x : Fin n → S)
    {F : LocalPointMeasure (MarkedPositiveSizeSurplus S) → ℝ} (hF : Measurable F) :
    (∫ η, F η ∂(scaledMarkedProcessLaw M lambda hc n x : Measure _)) =
      ∫ G, F (scaledMarkedProcess hc x G) ∂graphLaw M lambda n x := by
  unfold scaledMarkedProcessLaw
  exact integral_map (measurable_of_countable _).aemeasurable hF.aestronglyMeasurable

def starredMarkedProcess (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) :
    LocalPointMeasure (MarkedPositiveSizeSurplus S) :=
  scaledMarkedProcess (sizeScale_pos M hM) x G

omit [DiscreteTopology S] in
theorem starredMarkedProcess_eq_map (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) :
    starredMarkedProcess M hM x G = scaleMarkedPoint (sizeScale_pos M hM) (markedProcess x G) :=
  scaledMarkedProcess_eq_map (sizeScale_pos M hM) x G

omit [DiscreteTopology S] in
theorem starredMarked_atom_mark (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (x : Fin n → S) {G : SimpleGraph (Fin n)} (C : G.ConnectedComponent) :
    (markedSizeScale (sizeScale_pos M hM) (positiveMarkedAtom x C)).2.val = componentMark x C := rfl

omit [DiscreteTopology S] in
theorem starredMarked_atoms_eq_paper (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) :
    (∑ C : G.ConnectedComponent,
      Measure.dirac (ambientEmbedding (markedSizeScale (sizeScale_pos M hM)
        (positiveMarkedAtom x C)).1,
        (markedSizeScale (sizeScale_pos M hM) (positiveMarkedAtom x C)).2.val)) =
      markedStar M hM G x := by
  rw [markedStar_eq_sum]
  apply Finset.sum_congr rfl
  intro C _
  rw [markedSizeScale_atom_size,markedSizeScale_atom_mark]
  simp only [componentAtom,mul_div_assoc]

omit [DiscreteTopology S] in
/-- Exact law-level commutation; the finite Perron probability mark is
not rescaled or replaced by an averaged mark. -/
theorem canonicalGlobalMarkedLaw_scale (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {c : ℝ} (hc : 0 < c) (μ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus)) :
    (canonicalGlobalMarkedLaw M hM μ).map (continuous_scaleMarkedPoint hc).measurable.aemeasurable =
      canonicalGlobalMarkedLaw M hM (μ.map (continuous_scalePoint hc).measurable.aemeasurable) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [FiniteIrreducibleMarkedGlobalTests.canonicalGlobalMarkedLaw,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_scaleMarkedPoint hc).measurable
      (continuous_constantMark (perronWeakMark M hM)).measurable,
    Measure.map_map (continuous_constantMark (perronWeakMark M hM)).measurable
      (continuous_scalePoint hc).measurable]
  congr 1
  exact funext (scaleMarkedPoint_constantMark hc (perronWeakMark M hM))

def scaledCanonicalMarkedLimitLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) {c : ℝ} (hc : 0 < c)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  canonicalGlobalMarkedLaw M hM (scaledProcessLimitLaw M hM lambda hc v E hE hround)

theorem tendsto_scaledMarkedProcessLaw_canonical (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) {c : ℝ} (hc : 0 < c)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    Tendsto (fun n ↦ scaledMarkedProcessLaw M lambda hc n (v n)) atTop
      (𝓝 (scaledCanonicalMarkedLimitLaw M hM lambda hc v E hE hround)) := by
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedProcessLaw M lambda n (v n))
    (canonicalGlobalMarkedLimitLaw M hM lambda v E hE hround)
    (tendsto_markedProcessLaw_canonical M hM lambda v E hE hround) (continuous_scaleMarkedPoint hc)
  simpa only [scaledMarkedProcessLaw_eq_map M lambda hc,
    FiniteIrreducibleMarkedPointLawLimit.canonicalGlobalMarkedLimitLaw,
    canonicalGlobalMarkedLaw_scale M hM hc,scaledCanonicalMarkedLimitLaw,scaledProcessLimitLaw] using h

theorem exists_unique_scaledMarkedProcessLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) {c : ℝ} (hc : 0 < c)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)),
      Tendsto (fun n ↦ scaledMarkedProcessLaw M lambda hc n (v n)) atTop (𝓝 ν) :=
  ⟨scaledCanonicalMarkedLimitLaw M hM lambda hc v E hE hround,
    tendsto_scaledMarkedProcessLaw_canonical M hM lambda hc v E hE hround,
    fun _θ hθ ↦ tendsto_nhds_unique hθ
      (tendsto_scaledMarkedProcessLaw_canonical M hM lambda hc v E hE hround)⟩

def starredMarkedProcessLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  scaledMarkedProcessLaw M lambda (sizeScale_pos M hM) n x

def starredCanonicalMarkedLimitLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  scaledCanonicalMarkedLimitLaw M hM lambda (sizeScale_pos M hM) v E hE hround

theorem starredCanonicalMarkedLimitLaw_eq (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    starredCanonicalMarkedLimitLaw M hM lambda v E hE hround =
      canonicalGlobalMarkedLaw M hM (starredProcessLimitLaw M hM lambda v E hE hround) := rfl

theorem tendsto_starredMarkedProcessLaw_canonical (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    Tendsto (fun n ↦ starredMarkedProcessLaw M hM lambda n (v n)) atTop
      (𝓝 (starredCanonicalMarkedLimitLaw M hM lambda v E hE hround)) :=
  tendsto_scaledMarkedProcessLaw_canonical M hM lambda (sizeScale_pos M hM) v E hE hround

theorem exists_unique_starredMarkedProcessLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)),
      Tendsto (fun n ↦ starredMarkedProcessLaw M hM lambda n (v n)) atTop (𝓝 ν) :=
  exists_unique_scaledMarkedProcessLaw_limit M hM lambda (sizeScale_pos M hM) v E hE hround

/-- Simultaneous genuine starred unmarked and empirical-marked global
full-sequence limits, with the actual finite Perron probability mark. -/
theorem exists_unique_starred_unmarked_and_markedProcessLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ∃! μ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      Tendsto (fun n ↦ FiniteIrreducibleGlobalSizeRescaling.starredProcessLaw M hM lambda n (v n))
        atTop (𝓝 μ) ∧
      Tendsto (fun n ↦ starredMarkedProcessLaw M hM lambda n (v n)) atTop
        (𝓝 (canonicalGlobalMarkedLaw M hM μ)) := by
  have hu := FiniteIrreducibleGlobalSizeRescaling.tendsto_starredProcessLimitLaw
    M hM lambda v E hE hround
  have hm := tendsto_starredMarkedProcessLaw_canonical M hM lambda v E hE hround
  rw [starredCanonicalMarkedLimitLaw_eq] at hm
  exact ⟨starredProcessLimitLaw M hM lambda v E hE hround,⟨hu,hm⟩,
    fun _θ hθ ↦ tendsto_nhds_unique hθ.1 hu⟩

theorem starred_marked_graph_test_expectation_tendsto (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E)
    (F : LocalPointMeasure (MarkedPositiveSizeSurplus S) →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ G, F (starredMarkedProcess M hM (v n) G)
      ∂graphLaw M lambda n (v n)) atTop
      (𝓝 (∫ η, F η ∂(starredCanonicalMarkedLimitLaw M hM lambda v E hE hround : Measure _))) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_starredMarkedProcessLaw_canonical M hM lambda v E hE hround) F
  simpa only [starredMarkedProcessLaw,
    scaledMarkedProcessLaw_integral M lambda (sizeScale_pos M hM) _ _ F.continuous.measurable,
    starredMarkedProcess] using h

end PerronWright.FiniteIrreducibleGlobalMarkedSizeRescaling
