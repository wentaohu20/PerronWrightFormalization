import PerronWright.Probability.CompactGlobalPointLawLimit
import PerronWright.Probability.FiniteIrreducibleGlobalTightness
import PerronWright.Probability.FiniteIrreducibleGlobalTestLawLimit

/-! # Full-sequence unique vague weak limit of the fixed-type component law

Finite joint test-vector limits determine every actual subsequential
law, using the already proved vague-Borel generation and chart assembly.
The actual fixed-type source subsequence compactness then yields full
weak convergence. Neither a target process nor Brownian identity is assumed.
-/

open MeasureTheory Filter Topology
open scoped Classical CompactlySupported
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleGlobalPointLawLimit

open ComponentGlobalPointProcess LocallyFinitePointMeasureVague
open InitialTopologyLawDetermination GlobalPointChartSurjective
open CompactGlobalPointLawLimit (probability_ext_of_finiteTestMaps)
open CompactGlobalTestLawLimit (testVector continuous_testVector)
open FiniteIrreducibleGlobalTightness FiniteIrreducibleGlobalTestLawLimit
  FiniteIrreducibleComponentProcess

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Any two actual weak subsequential law limits coincide, not merely
their first moments or individual test integrals. -/
theorem unmarkedProcessLaw_subseq_limits_eq (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E)
    {I J : ℕ → ℕ} (hI : Tendsto I atTop atTop) (hJ : Tendsto J atTop atTop)
    {μ ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus)}
    (hμ : Tendsto (fun k ↦ unmarkedProcessLaw M lambda (I k) (v (I k))) atTop (𝓝 μ))
    (hν : Tendsto (fun k ↦ unmarkedProcessLaw M lambda (J k) (v (J k))) atTop (𝓝 ν)) :
    μ = ν := by
  apply probability_ext_of_finiteTestMaps
  intro F
  let f : F → C_c(PositiveSizeSurplus, ℝ) := Subtype.val
  obtain ⟨θ, hθ, _⟩ := exists_unique_globalTestLaw_limit M hM lambda f v E hE hround
  have hμf := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun k ↦ unmarkedProcessLaw M lambda (I k) (v (I k))) μ hμ (continuous_testVector f)
  have hνf := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun k ↦ unmarkedProcessLaw M lambda (J k) (v (J k))) ν hν (continuous_testVector f)
  change Tendsto (fun k ↦ globalTestLaw M lambda (I k) (v (I k)) f) atTop
    (𝓝 (μ.map (continuous_testVector f).measurable.aemeasurable)) at hμf
  change Tendsto (fun k ↦ globalTestLaw M lambda (J k) (v (J k)) f) atTop
    (𝓝 (ν.map (continuous_testVector f).measurable.aemeasurable)) at hνf
  exact (tendsto_nhds_unique hμf (hθ.comp hI)).trans
    (tendsto_nhds_unique hνf (hθ.comp hJ)).symm

/-- Actual full-sequence weak convergence of the literal unmarked
component point process on `(0, ∞) × ℕ`, for the proved `C_c`-integral
vague topology. The probability law is both genuinely constructed and
unique among all actual probability measures on the vague-Borel space.
Only literal finite irreducible criticality and the actual bounded O(1) count error are used. -/
theorem exists_unique_unmarkedProcessLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      Tendsto (fun n ↦ unmarkedProcessLaw M lambda n (v n)) atTop (𝓝 ν) := by
  obtain ⟨ν, N, hN, hν⟩ := exists_unmarkedProcessLaw_subseq_limit M hM lambda v E hE hround
  have hfull : Tendsto (fun n ↦ unmarkedProcessLaw M lambda n (v n)) atTop (𝓝 ν) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro I hI
    obtain ⟨ρ, J, hJ, hρ⟩ :=
      exists_reindexed_unmarkedProcessLaw_subseq_limit M hM lambda v E hE hround I
    have he : ρ = ν := unmarkedProcessLaw_subseq_limits_eq M hM lambda v E hE hround
      (hI.comp hJ.tendsto_atTop) hN.tendsto_atTop hρ hν
    exact ⟨J, he ▸ hρ⟩
  refine ⟨ν, hfull, ?_⟩
  intro ρ hρ
  exact unmarkedProcessLaw_subseq_limits_eq M hM lambda v E hE hround
    tendsto_id tendsto_id hρ hfull

/-- The unique law constructed from the genuine finite graph sequence.
This is not a separately supplied candidate process law. -/
def unmarkedProcessLimitLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E) : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  (exists_unique_unmarkedProcessLaw_limit M hM lambda v E hE hround).choose

theorem tendsto_unmarkedProcessLimitLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (lambda : ℝ)
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E) :
    Tendsto (fun n ↦ unmarkedProcessLaw M lambda n (v n)) atTop
      (𝓝 (unmarkedProcessLimitLaw M hM lambda v E hE hround)) :=
  (exists_unique_unmarkedProcessLaw_limit M hM lambda v E hE hround).choose_spec.1

end PerronWright.FiniteIrreducibleGlobalPointLawLimit

