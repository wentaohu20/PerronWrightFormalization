import PerronWright.Probability.GlobalPointSizeRescaling
import PerronWright.Probability.FiniteIrreduciblePointProcessNormalization
import PerronWright.Probability.FiniteIrreducibleGlobalPointLawLimit

/-! # Actual deterministic positive dilation and starred global laws

The already proved positive-size homeomorphism is proper. Its genuine
continuous point pushforward exactly transports each literal fixed-type
graph configuration and its law. Full source weak convergence was
proved; it is not an input interface to any model-only terminal here.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FiniteIrreducibleGlobalSizeRescaling

open ComponentGlobalPointProcess LocallyFinitePointMeasureVague ComponentWindowPointMeasures
open GlobalPointSizeRescaling (positiveSizeScale positiveSizeScale_atom scalePoint
  continuous_scalePoint scaledProcess scaledProcess_eq_map measurable_scaledProcess)
open FiniteIrreduciblePointProcessNormalization
open FiniteIrreducibleComponentProcess
open FiniteIrreducibleGlobalPointLawLimit (unmarkedProcessLimitLaw tendsto_unmarkedProcessLimitLaw)
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S]

def scaledProcessLaw (M : FiniteIrreducibleModel S) (lambda : ℝ)
    {c : ℝ} (hc : 0 < c) (n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  ⟨(graphLaw M lambda n x).map (scaledProcess hc),
    Measure.isProbabilityMeasure_map (measurable_scaledProcess hc n).aemeasurable⟩

theorem scaledProcessLaw_eq_map (M : FiniteIrreducibleModel S) (lambda : ℝ)
    {c : ℝ} (hc : 0 < c) (n : ℕ) (x : Fin n → S) :
    scaledProcessLaw M lambda hc n x = (FiniteIrreducibleComponentProcess.unmarkedProcessLaw
      M lambda n x).map (continuous_scalePoint hc).measurable.aemeasurable := by
  apply Subtype.ext
  change (graphLaw M lambda n x).map (scaledProcess hc) =
    ((graphLaw M lambda n x).map unmarkedProcess).map (scalePoint hc)
  rw [Measure.map_map (continuous_scalePoint hc).measurable (measurable_unmarkedProcess n)]
  congr 1
  exact funext (scaledProcess_eq_map hc)

theorem scaledProcessLaw_integral (M : FiniteIrreducibleModel S) (lambda : ℝ)
    {c : ℝ} (hc : 0 < c) (n : ℕ) (x : Fin n → S)
    {F : LocalPointMeasure PositiveSizeSurplus → ℝ} (hF : Measurable F) :
    (∫ η, F η ∂(scaledProcessLaw M lambda hc n x : Measure _)) =
      ∫ G, F (scaledProcess hc G) ∂graphLaw M lambda n x := by
  unfold scaledProcessLaw
  exact integral_map (measurable_scaledProcess hc n).aemeasurable hF.aestronglyMeasurable

def starredProcess (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (G : SimpleGraph (Fin n)) : LocalPointMeasure PositiveSizeSurplus :=
  scaledProcess (sizeScale_pos M hM) G

theorem starredProcess_eq_map (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    starredProcess M hM G = scalePoint (sizeScale_pos M hM) (unmarkedProcess G) :=
  scaledProcess_eq_map (sizeScale_pos M hM) G

/-- The actual positive-space atoms agree exactly with the paper's
literal ambient starred Dirac sum, including all multiplicities. -/
theorem starred_atoms_eq_paper (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    (∑ C : G.ConnectedComponent,
      Measure.dirac (ambientEmbedding (positiveSizeScale (sizeScale_pos M hM) (positiveAtom C)))) =
        unmarkedStar M hM G := by
  rw [unmarkedStar_eq_sum]
  apply Finset.sum_congr rfl
  intro C _
  rw [positiveSizeScale_atom]
  simp only [componentAtom,mul_div_assoc]

def starredProcessLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  scaledProcessLaw M lambda (sizeScale_pos M hM) n x

theorem starredProcessLaw_eq_map (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (n : ℕ) (x : Fin n → S) :
    starredProcessLaw M hM lambda n x =
      (FiniteIrreducibleComponentProcess.unmarkedProcessLaw M lambda n x).map
        (continuous_scalePoint (sizeScale_pos M hM)).measurable.aemeasurable :=
  scaledProcessLaw_eq_map M lambda (sizeScale_pos M hM) n x

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def scaledProcessLimitLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) {c : ℝ} (hc : 0 < c)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  (unmarkedProcessLimitLaw M hM lambda v E hE hround).map
    (continuous_scalePoint hc).measurable.aemeasurable

theorem tendsto_scaledProcessLimitLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) {c : ℝ} (hc : 0 < c)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    Tendsto (fun n ↦ scaledProcessLaw M lambda hc n (v n)) atTop
      (𝓝 (scaledProcessLimitLaw M hM lambda hc v E hE hround)) := by
  simpa only [scaledProcessLaw_eq_map,scaledProcessLimitLaw] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedProcessLaw M lambda n (v n))
      (unmarkedProcessLimitLaw M hM lambda v E hE hround)
      (tendsto_unmarkedProcessLimitLaw M hM lambda v E hE hround) (continuous_scalePoint hc)

theorem exists_unique_scaledProcessLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) {c : ℝ} (hc : 0 < c)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      Tendsto (fun n ↦ scaledProcessLaw M lambda hc n (v n)) atTop (𝓝 ν) :=
  ⟨scaledProcessLimitLaw M hM lambda hc v E hE hround,
    tendsto_scaledProcessLimitLaw M hM lambda hc v E hE hround,
    fun _θ hθ ↦ tendsto_nhds_unique hθ (tendsto_scaledProcessLimitLaw M hM lambda hc v E hE hround)⟩

def starredProcessLimitLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  scaledProcessLimitLaw M hM lambda (sizeScale_pos M hM) v E hE hround

theorem tendsto_starredProcessLimitLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ) (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    Tendsto (fun n ↦ starredProcessLaw M hM lambda n (v n)) atTop
      (𝓝 (starredProcessLimitLaw M hM lambda v E hE hround)) :=
  tendsto_scaledProcessLimitLaw M hM lambda (sizeScale_pos M hM) v E hE hround

theorem exists_unique_starredProcessLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      Tendsto (fun n ↦ starredProcessLaw M hM lambda n (v n)) atTop (𝓝 ν) :=
  exists_unique_scaledProcessLaw_limit M hM lambda (sizeScale_pos M hM) v E hE hround

theorem starred_graph_test_expectation_tendsto (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E)
    (F : LocalPointMeasure PositiveSizeSurplus →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ G, F (starredProcess M hM G) ∂graphLaw M lambda n (v n)) atTop
      (𝓝 (∫ η, F η ∂(starredProcessLimitLaw M hM lambda v E hE hround : Measure _))) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_starredProcessLimitLaw M hM lambda v E hE hround) F
  simpa only [starredProcessLaw,
    scaledProcessLaw_integral M lambda (sizeScale_pos M hM) _ _ F.continuous.measurable,
    starredProcess] using h

end PerronWright.FiniteIrreducibleGlobalSizeRescaling
