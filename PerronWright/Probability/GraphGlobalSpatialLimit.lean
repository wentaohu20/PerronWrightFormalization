import PerronWright.Probability.GraphWindowSpatialLimit
import PerronWright.Probability.GlobalPointChartTightness
import PerronWright.Probability.GlobalPointChartAtomicAssembly
import PerronWright.Probability.CompactGlobalPointLawLimit

/-! # Actual full vague spatial limits from proved graph window formulas

The source laws are literal finite graph probabilities. Their exact
compatible point charts, actual window mass bounds, Polish chart
compactness, and continuous assembly construct global subsequences.
Finite compact-support test laws, already obtained from the actual
spatial window limits, identify every global subsequence and yield the
unique full vague weak limit. No global-law existence is postulated.
-/

open MeasureTheory Filter Topology
open scoped Real Topology BigOperators Classical CompactlySupported
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GraphGlobalSpatialLimit

open GraphWindowSource GraphWindowFactorialLimits GraphWindowSpatialLimit
open GlobalPointMeasureCharts GlobalPointChartTightness GlobalPointChartAtomicAssembly
  PositiveSizeSurplusExhaustion LocallyFinitePointMeasureVague
open ComponentGlobalPointProcess (PositiveSizeSurplus unmarkedProcess measurable_unmarkedProcess)
open InitialTopologyLawDetermination GlobalPointChartSurjective
open CompactGlobalPointLawLimit (probability_ext_of_finiteTestMaps)
open CompactGlobalTestLawLimit (testVector continuous_testVector exists_common_test_window
  windowTestVector continuous_windowTestVector)
open ComponentWindowPointMeasures FinitePointMeasureCompact

variable (ρ : (n : ℕ) → Measure (SimpleGraph (Fin (n+1))))
variable [∀ n, IsProbabilityMeasure (ρ n)]

def processLaw (n : ℕ) : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  ⟨(ρ n).map unmarkedProcess,
    Measure.isProbabilityMeasure_map (measurable_unmarkedProcess (n+1)).aemeasurable⟩

def chartLaw (n : ℕ) : ProbabilityMeasure ChartProduct :=
  ⟨(ρ n).map sourceCharts,
    Measure.isProbabilityMeasure_map (measurable_sourceCharts (n+1)).aemeasurable⟩

def compatibleChartLaw (n : ℕ) : ProbabilityMeasure CompatibleCharts :=
  ⟨(ρ n).map sourceCompatibleCharts,
    Measure.isProbabilityMeasure_map (measurable_sourceCompatibleCharts (n+1)).aemeasurable⟩

theorem chartLaw_eval (n m : ℕ) :
    (chartLaw ρ n).map (continuous_apply m).measurable.aemeasurable =
      windowLaw ρ (lower m) (upper m) m n := by
  apply Subtype.ext
  change ((ρ n).map sourceCharts).map (fun ζ : ChartProduct ↦ ζ m) = _
  rw [Measure.map_map (continuous_apply m).measurable (measurable_sourceCharts (n+1))]
  rfl

theorem compatibleChartLaw_map_val (n : ℕ) :
    (compatibleChartLaw ρ n).map measurable_forgetCharts.aemeasurable = chartLaw ρ n := by
  apply Subtype.ext
  change ((ρ n).map sourceCompatibleCharts).map forgetCharts = _
  rw [Measure.map_map measurable_forgetCharts (measurable_sourceCompatibleCharts (n+1))]
  rfl

theorem compatibleChartLaw_map_assemble (n : ℕ) :
    (compatibleChartLaw ρ n).map continuous_assemble.measurable.aemeasurable = processLaw ρ n := by
  apply Subtype.ext
  change ((ρ n).map sourceCompatibleCharts).map assemble = (ρ n).map unmarkedProcess
  rw [Measure.map_map continuous_assemble.measurable (measurable_sourceCompatibleCharts (n+1))]
  congr 1
  funext G
  exact assemble_sourceCompatibleCharts G

theorem isTight_chartLaws {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) :
    IsTightMeasureSet (Set.range (fun n ↦ (chartLaw ρ n : Measure ChartProduct))) := by
  apply isTight_countable_product_of_marginals
  intro m
  simpa only [chartLaw_eval] using isTight_windowLaws ρ hbeta hlocal
    (lower_pos m) (lower_le_upper m) m

theorem isTight_compatibleChartLaws {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) :
    IsTightMeasureSet (Set.range (fun n ↦
      (compatibleChartLaw ρ n : Measure CompatibleCharts))) := by
  apply isTight_of_isClosedEmbedding_map (compatibleChartLaw ρ)
    forgetCharts isClosed_compatible.isClosedEmbedding_subtypeVal
  simpa only [compatibleChartLaw_map_val] using isTight_chartLaws ρ hbeta hlocal

theorem isCompact_closure_compatibleChartLaws {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) :
    IsCompact (closure (Set.range (compatibleChartLaw ρ))) := by
  apply isCompact_closure_of_isTightMeasureSet
  have he : {((ν : ProbabilityMeasure CompatibleCharts) : Measure CompatibleCharts) |
      ν ∈ Set.range (compatibleChartLaw ρ)} =
      Set.range (fun n ↦ (compatibleChartLaw ρ n : Measure CompatibleCharts)) := by
    ext μ
    simp
  rw [he]
  exact isTight_compatibleChartLaws ρ hbeta hlocal

theorem exists_reindexed_processLaw_subseq_limit {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) (I : ℕ → ℕ) :
    ∃ ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      ∃ N : ℕ → ℕ, StrictMono N ∧
        Tendsto (fun k ↦ processLaw ρ (I (N k))) atTop (𝓝 ν) := by
  let : MetricSpace CompatibleCharts := TopologicalSpace.metrizableSpaceMetric _
  let : MetricSpace (ProbabilityMeasure CompatibleCharts) := TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨ξ, _, N, hN, hξ⟩ := (isCompact_closure_compatibleChartLaws ρ hbeta hlocal).tendsto_subseq
    (fun k ↦ subset_closure (Set.mem_range_self (I k)))
  refine ⟨ξ.map continuous_assemble.measurable.aemeasurable, N, hN, ?_⟩
  simpa only [compatibleChartLaw_map_assemble] using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun k ↦ compatibleChartLaw ρ (I (N k))) ξ hξ continuous_assemble

theorem exists_processLaw_subseq_limit {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) :
    ∃ ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      ∃ N : ℕ → ℕ, StrictMono N ∧ Tendsto (fun k ↦ processLaw ρ (N k)) atTop (𝓝 ν) :=
  exists_reindexed_processLaw_subseq_limit ρ hbeta hlocal id

def globalTestLaw {D : Type*} [Fintype D] (n : ℕ)
    (f : D → C_c(PositiveSizeSurplus, ℝ)) : ProbabilityMeasure (D → ℝ) :=
  (processLaw ρ n).map (continuous_testVector f).measurable.aemeasurable

theorem globalTestLaw_eq_window_map {D : Type*} [Fintype D] (a b : ℝ)
    (R : ℕ) (ha : 0 < a) (n : ℕ) (f : D → C_c(PositiveSizeSurplus, ℝ))
    (hf : ∀ i, tsupport (f i) ⊆ ComponentGlobalPointProcess.ambientEmbedding ⁻¹' windowSet a b R) :
    globalTestLaw ρ n f = (windowLaw ρ a b R n).map
      (continuous_windowTestVector a b R ha f).measurable.aemeasurable := by
  apply Subtype.ext
  change ((ρ n).map unmarkedProcess).map (testVector f) =
      ((ρ n).map (windowPointMeasure a b R 1)).map (windowTestVector a b R ha f)
  rw [Measure.map_map (continuous_testVector f).measurable (measurable_unmarkedProcess (n+1)),
    Measure.map_map (continuous_windowTestVector a b R ha f).measurable
      (measurable_windowPointMeasure a b R 1 (n+1))]
  congr 1
  funext G i
  exact ComponentGlobalPointProcess.unmarkedProcess_integral_eq_window a b R ha G (f i) (hf i)

theorem exists_unique_globalTestLaw_limit {D : Type*} [Fintype D]
    {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    (f : D → C_c(PositiveSizeSurplus, ℝ)) :
    ∃! θ : ProbabilityMeasure (D → ℝ), Tendsto (fun n ↦ globalTestLaw ρ n f) atTop (𝓝 θ) := by
  obtain ⟨a, b, R, ha, hab, hf⟩ := exists_common_test_window f
  obtain ⟨ν, hν, _⟩ := exists_unique_windowLaw_limit ρ hbeta hlocal ha hab R
  let θ := ν.map (continuous_windowTestVector a b R ha f).measurable.aemeasurable
  have hθ : Tendsto (fun n ↦ globalTestLaw ρ n f) atTop (𝓝 θ) := by
    simpa only [globalTestLaw_eq_window_map ρ a b R ha _ f hf] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (windowLaw ρ a b R) ν hν (continuous_windowTestVector a b R ha f)
  exact ⟨θ, hθ, fun μ hμ ↦ tendsto_nhds_unique hμ hθ⟩

theorem processLaw_subseq_limits_eq {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda)
    {I J : ℕ → ℕ} (hI : Tendsto I atTop atTop) (hJ : Tendsto J atTop atTop)
    {μ ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus)}
    (hμ : Tendsto (fun k ↦ processLaw ρ (I k)) atTop (𝓝 μ))
    (hν : Tendsto (fun k ↦ processLaw ρ (J k)) atTop (𝓝 ν)) : μ = ν := by
  apply probability_ext_of_finiteTestMaps
  intro F
  let f : F → C_c(PositiveSizeSurplus, ℝ) := Subtype.val
  obtain ⟨θ, hθ, _⟩ := exists_unique_globalTestLaw_limit ρ hbeta hlocal f
  have hμf := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun k ↦ processLaw ρ (I k)) μ hμ (continuous_testVector f)
  have hνf := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun k ↦ processLaw ρ (J k)) ν hν (continuous_testVector f)
  change Tendsto (fun k ↦ globalTestLaw ρ (I k) f) atTop
    (𝓝 (μ.map (continuous_testVector f).measurable.aemeasurable)) at hμf
  change Tendsto (fun k ↦ globalTestLaw ρ (J k) f) atTop
    (𝓝 (ν.map (continuous_testVector f).measurable.aemeasurable)) at hνf
  exact (tendsto_nhds_unique hμf (hθ.comp hI)).trans
    (tendsto_nhds_unique hνf (hθ.comp hJ)).symm

theorem exists_unique_processLaw_limit {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      Tendsto (processLaw ρ) atTop (𝓝 ν) := by
  obtain ⟨ν, N, hN, hν⟩ := exists_processLaw_subseq_limit ρ hbeta hlocal
  have hfull : Tendsto (processLaw ρ) atTop (𝓝 ν) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro I hI
    obtain ⟨μ, J, hJ, hμ⟩ := exists_reindexed_processLaw_subseq_limit ρ hbeta hlocal I
    have he : μ = ν := processLaw_subseq_limits_eq ρ hbeta hlocal
      (hI.comp hJ.tendsto_atTop) hN.tendsto_atTop hμ hν
    exact ⟨J, he ▸ hμ⟩
  refine ⟨ν, hfull, ?_⟩
  intro μ hμ
  exact processLaw_subseq_limits_eq ρ hbeta hlocal tendsto_id tendsto_id hμ hfull

def processLimitLaw {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) :
    ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  (exists_unique_processLaw_limit ρ hbeta hlocal).choose

theorem tendsto_processLimitLaw {alpha beta lambda : ℝ} (hbeta : 0 < beta)
    (hlocal : HasUniformLocalLimit ρ alpha beta lambda) :
    Tendsto (processLaw ρ) atTop (𝓝 (processLimitLaw ρ hbeta hlocal)) :=
  (exists_unique_processLaw_limit ρ hbeta hlocal).choose_spec.1

end PerronWright.GraphGlobalSpatialLimit
