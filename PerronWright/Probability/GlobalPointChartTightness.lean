import PerronWright.Probability.GlobalPointMeasureCharts
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual tightness and subsequential laws of compatible point charts

Tightness of all genuine coordinate laws gives tightness on the countable
product by compact products and an explicitly summable error allocation.
The actual source laws live on the proved closed compatible-chart space.
Closed-embedding pullback transfers tightness there, and Prokhorov gives
an actual subsequential probability law. No target-existence or product
tightness interface is assumed.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GlobalPointChartTightness

/-- A proved countable-product tightness theorem for actual probability
laws, with no independence assumption. -/
theorem isTight_countable_product_of_marginals
    {E : ℕ → Type*} [∀ m, TopologicalSpace (E m)] [∀ m, MeasurableSpace (E m)]
    [∀ m, BorelSpace (E m)] [∀ m, T2Space (E m)] [∀ m, SecondCountableTopology (E m)]
    (μ : ℕ → ProbabilityMeasure ((m : ℕ) → E m))
    (hμ : ∀ m, IsTightMeasureSet (Set.range (fun n ↦
      ((μ n).map (measurable_pi_apply m).aemeasurable : Measure (E m))))) :
    IsTightMeasureSet (Set.range (fun n ↦ (μ n : Measure ((m : ℕ) → E m)))) := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  let δ : ℕ → ℝ≥0∞ := fun m ↦ min ε 1 * 2 ^ (-1 - (m : ℤ))
  have hδ : ∀ m, 0 < δ m := by
    intro m
    have he : 0 < min ε 1 := lt_min hε zero_lt_one
    dsimp [δ]
    exact ENNReal.mul_pos_iff.mpr ⟨he, ENNReal.zpow_pos (by norm_num) (by norm_num) _⟩
  have hK m : ∃ K : Set (E m), IsCompact K ∧ ∀ n,
      ((μ n).map (measurable_pi_apply m).aemeasurable : Measure (E m)) Kᶜ ≤ δ m := by
    obtain ⟨K, hK, hb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp (hμ m)
      (δ m) (hδ m)
    exact ⟨K, hK, fun n ↦ hb _ (Set.mem_range_self n)⟩
  choose K hK hb using hK
  let P : Set ((m : ℕ) → E m) := Set.pi Set.univ K
  have hP : IsCompact P := isCompact_univ_pi hK
  have hc : Pᶜ = ⋃ m, (fun ζ : (m : ℕ) → E m ↦ ζ m) ⁻¹' (K m)ᶜ := by
    ext ζ
    simp [P, Set.mem_pi]
  refine ⟨P, hP, ?_⟩
  rintro ν ⟨n, rfl⟩
  calc
    (μ n : Measure ((m : ℕ) → E m)) Pᶜ =
      (μ n : Measure ((m : ℕ) → E m))
        (⋃ m, (fun ζ : (m : ℕ) → E m ↦ ζ m) ⁻¹' (K m)ᶜ) := by rw [hc]
    _ ≤ ∑' m, (μ n : Measure ((m : ℕ) → E m))
        ((fun ζ ↦ ζ m) ⁻¹' (K m)ᶜ) := measure_iUnion_le _
    _ ≤ ∑' m, δ m := ENNReal.tsum_le_tsum (fun m ↦ by
      simpa only [ProbabilityMeasure.toMeasure_map,
        Measure.map_apply (measurable_pi_apply m) (hK m).measurableSet.compl] using hb m n)
    _ = min ε 1 := by
      simp only [δ, ENNReal.tsum_mul_left, ENNReal.tsum_two_zpow_neg_add_one, mul_one]
    _ ≤ ε := min_le_left _ _

/-- Actual tight laws pull back through a genuine closed embedding. -/
theorem isTight_of_isClosedEmbedding_map
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [T2Space Y]
    (μ : ℕ → ProbabilityMeasure X) (f : X → Y) (hf : IsClosedEmbedding f)
    (hμ : IsTightMeasureSet (Set.range (fun n ↦
      ((μ n).map hf.continuous.measurable.aemeasurable : Measure Y)))) :
    IsTightMeasureSet (Set.range (fun n ↦ (μ n : Measure X))) := by
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  obtain ⟨K, hK, hb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hμ ε hε
  refine ⟨f ⁻¹' K, hf.isCompact_preimage hK, ?_⟩
  rintro ν ⟨n, rfl⟩
  simpa only [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply hf.continuous.measurable hK.measurableSet.compl,
    Set.preimage_compl] using hb _ (Set.mem_range_self n)

open GlobalPointMeasureCharts PositiveSizeSurplusExhaustion ComponentWindowTightness

def forgetCharts : CompatibleCharts → ChartProduct := Subtype.val

theorem continuous_forgetCharts : Continuous forgetCharts := continuous_subtype_val

theorem measurable_forgetCharts : Measurable forgetCharts := continuous_forgetCharts.measurable

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

theorem isTight_chartLaws (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (hQP : M.QP) (lambda : ℝ) :
    IsTightMeasureSet (Set.range (fun n ↦ (chartLaw M lambda n : Measure ChartProduct))) := by
  apply isTight_countable_product_of_marginals
  intro m
  simpa only [chartLaw_eval] using isTight_unmarkedWindowLaws M hM hQP lambda
    (lower m) (upper m) (lower_pos m) (lower_le_upper m) m

theorem compatibleChartLaw_map_val (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ) :
    (compatibleChartLaw M lambda n).map measurable_forgetCharts.aemeasurable =
        chartLaw M lambda n := by
  apply Subtype.ext
  change ((AnnealedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map sourceCompatibleCharts).map
      forgetCharts = _
  rw [Measure.map_map measurable_forgetCharts (measurable_sourceCompatibleCharts n)]
  rfl

theorem isTight_compatibleChartLaws (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (hQP : M.QP) (lambda : ℝ) :
    IsTightMeasureSet (Set.range (fun n ↦
      (compatibleChartLaw M lambda n : Measure CompatibleCharts))) := by
  apply isTight_of_isClosedEmbedding_map (compatibleChartLaw M lambda)
    forgetCharts isClosed_compatible.isClosedEmbedding_subtypeVal
  simpa only [compatibleChartLaw_map_val] using isTight_chartLaws M hM hQP lambda

theorem isCompact_closure_compatibleChartLaws (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    IsCompact (closure (Set.range (compatibleChartLaw M lambda))) := by
  apply isCompact_closure_of_isTightMeasureSet
  have he : {((ν : ProbabilityMeasure CompatibleCharts) : Measure CompatibleCharts) |
      ν ∈ Set.range (compatibleChartLaw M lambda)} =
      Set.range (fun n ↦ (compatibleChartLaw M lambda n : Measure CompatibleCharts)) := by
    ext μ
    simp
  rw [he]
  exact isTight_compatibleChartLaws M hM hQP lambda

/-- Genuine compatible-chart probability subsequential limits exist
for the actual graph sequence, from proved tightness and Polishness. -/
theorem exists_compatibleChartLaw_subseq_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    ∃ ν : ProbabilityMeasure CompatibleCharts, ∃ N : ℕ → ℕ, StrictMono N ∧
      Tendsto (fun k ↦ compatibleChartLaw M lambda (N k)) atTop (𝓝 ν) := by
  let : MetricSpace CompatibleCharts := TopologicalSpace.metrizableSpaceMetric _
  let : MetricSpace (ProbabilityMeasure CompatibleCharts) := TopologicalSpace.metrizableSpaceMetric _
  obtain ⟨ν, _, N, hN, hν⟩ := (isCompact_closure_compatibleChartLaws M hM hQP lambda).tendsto_subseq
    (fun n ↦ subset_closure (Set.mem_range_self n))
  exact ⟨ν, N, hN, hν⟩

end PerronWright.GlobalPointChartTightness
