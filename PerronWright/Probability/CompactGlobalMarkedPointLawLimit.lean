import PerronWright.Probability.InitialTopologyLawDetermination
import PerronWright.Probability.MarkedGlobalPointChartSurjective
import PerronWright.Probability.CompactGlobalMarkedPointLawSubsequence
import PerronWright.Probability.CompactGlobalMarkedTestLawLimit

/-! # Whole global empirical-marked law convergence to canonical Perron marking

The source is the actual sampled-type/component finite integer point
measure on `(0,∞) × ℕ × WeakMark S`. Compact marks, genuine compatible
chart tightness and actual RMK integer assembly give subsequences.
Actual finite compact-support joint laws identify every subsequence
with the deterministic Perron marking of the genuine unmarked global
limit. True vague-Borel generation then gives whole-law convergence.
No target-law existence, marked convergence or law-determination
interface is assumed. Brownian identification is a separate question.
-/

open MeasureTheory Filter Topology
open scoped Classical CompactlySupported

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CompactGlobalMarkedPointLawLimit

open ComponentGlobalMarkedProcess LocallyFinitePointMeasureVague
open InitialTopologyLawDetermination MarkedGlobalPointChartSurjective
open CompactGlobalMarkedPointLawSubsequence CompactGlobalMarkedTestLawLimit
open GlobalPointMeasureMarking

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

theorem probability_ext_of_finiteTestMaps
    (μ ν : ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)))
    (h : ∀ F : Finset C_c(MarkedPositiveSizeSurplus S, ℝ),
      μ.map (continuous_finiteProjection continuous_testEncoding F).measurable.aemeasurable =
        ν.map (continuous_finiteProjection continuous_testEncoding F).measurable.aemeasurable) :
    μ = ν := by
  let : IsProbabilityMeasure (μ : Measure (LocalPointMeasure (MarkedPositiveSizeSurplus S))) :=
    μ.property
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_finiteProjection_map_of_hereditarilyLindelof testEncoding isInducing_testEncoding
    (μ : Measure (LocalPointMeasure (MarkedPositiveSizeSurplus S)))
    (ν : Measure (LocalPointMeasure (MarkedPositiveSizeSurplus S)))
  intro F
  simpa only [ProbabilityMeasure.toMeasure_map] using congrArg
    (fun θ : ProbabilityMeasure (F → ℝ) ↦ (θ : Measure (F → ℝ))) (h F)

def finiteTestLawEncoding
    (μ : ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S))) :
    (F : Finset C_c(MarkedPositiveSizeSurplus S, ℝ)) → ProbabilityMeasure (F → ℝ) :=
  fun F ↦ μ.map (continuous_finiteProjection continuous_testEncoding F).measurable.aemeasurable

omit [CompactSpace S] in
theorem continuous_finiteTestLawEncoding : Continuous (finiteTestLawEncoding (S := S)) :=
  continuous_pi (fun F ↦ ProbabilityMeasure.continuous_map
    (continuous_finiteProjection continuous_testEncoding F))

theorem finiteTestLawEncoding_injective : Function.Injective (finiteTestLawEncoding (S := S)) :=
  fun μ ν h ↦ probability_ext_of_finiteTestMaps μ ν (fun F ↦ congrFun h F)

instance globalMarkedPointLaw_t2 :
    T2Space (ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S))) :=
  T2Space.of_injective_continuous finiteTestLawEncoding_injective continuous_finiteTestLawEncoding

/-- Every actual weak subsequential law equals the explicit canonical
Perron-marked global unmarked law. -/
theorem markedProcessLaw_subseq_limit_eq_canonical (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ)
    {I : ℕ → ℕ} (hI : Tendsto I atTop atTop)
    {μ : ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S))}
    (hμ : Tendsto (fun k ↦ markedProcessLaw M lambda (I k)) atTop (𝓝 μ)) :
    μ = canonicalGlobalMarkedLimitLaw M hM hQP lambda := by
  apply probability_ext_of_finiteTestMaps
  intro F
  let f : F → C_c(MarkedPositiveSizeSurplus S, ℝ) := Subtype.val
  have hμf := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun k ↦ markedProcessLaw M lambda (I k)) μ hμ (continuous_globalTestVector f)
  change Tendsto (fun k ↦ markedTestLaw M lambda (I k) f) atTop
    (𝓝 (μ.map (continuous_globalTestVector f).measurable.aemeasurable)) at hμf
  exact tendsto_nhds_unique hμf
    ((markedTestLaw_tendsto_canonical M hM hQP lambda f).comp hI)

/-- Actual full-sequence weak convergence for the `C_c`-integral vague
topology, to the true deterministic Perron marking pushforward. -/
theorem tendsto_markedProcessLaw_canonical (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    Tendsto (fun n ↦ markedProcessLaw M lambda n) atTop
      (𝓝 (canonicalGlobalMarkedLimitLaw M hM hQP lambda)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro I hI
  obtain ⟨ρ, J, hJ, hρ⟩ :=
    exists_reindexed_markedProcessLaw_subseq_limit M hM hQP lambda I
  have he : ρ = canonicalGlobalMarkedLimitLaw M hM hQP lambda :=
    markedProcessLaw_subseq_limit_eq_canonical M hM hQP lambda
      (hI.comp hJ.tendsto_atTop) hρ
  exact ⟨J, he ▸ hρ⟩

theorem exists_unique_markedProcessLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)),
      Tendsto (fun n ↦ markedProcessLaw M lambda n) atTop (𝓝 ν) := by
  refine ⟨canonicalGlobalMarkedLimitLaw M hM hQP lambda,
    tendsto_markedProcessLaw_canonical M hM hQP lambda, ?_⟩
  intro ρ hρ
  exact markedProcessLaw_subseq_limit_eq_canonical M hM hQP lambda tendsto_id hρ

end PerronWright.CompactGlobalMarkedPointLawLimit
