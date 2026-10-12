import PerronWright.Probability.FinitePointMeasureMeasurable
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The actual compact-window point-measure space is Polish

Integer masses make the zero point measure an isolated mass stratum.
Consequently normalization is continuous on the genuine point space,
including zero. Integer mass and normalization give a proved closed
embedding into `Nat × ProbabilityMeasure E`, yielding Polishness and
standard Borelness rather than imposing either as an interface.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FinitePointMeasurePolish

open FiniteAtomicPointMeasure FinitePointMeasureCompact FinitePointMeasureMeasurable

variable {E : Type*} [MeasurableSpace E] [MetricSpace E] [CompactSpace E]
  [BorelSpace E] [Nonempty E]

omit [CompactSpace E] [Nonempty E] in
/-- Integer mass is genuinely continuous for the actual weak topology. -/
theorem continuous_size : Continuous (size : PointMeasure E → ℕ) := by
  have hc : Continuous (fun η : PointMeasure E ↦ (mass η : ℝ)) :=
    NNReal.continuous_coe.comp continuous_mass
  have he : (Nat.cast : ℕ → ℝ) ∘ (size : PointMeasure E → ℕ) =
      fun η : PointMeasure E ↦ (mass η : ℝ) := by
    funext η
    change (size η : ℝ) = (mass η : ℝ)
    exact_mod_cast (mass_eq_size η).symm
  rw [← he] at hc
  exact Nat.isClosedEmbedding_coe_real.isEmbedding.continuous_iff.mpr hc

omit [CompactSpace E] in
/-- Actual normalization is continuous on integer atomic measures even
at zero, since the zero-size stratum is open. -/
theorem continuous_normalize : Continuous (fun η : PointMeasure E ↦
    (η : FiniteMeasure E).normalize) := by
  apply continuous_iff_continuousAt.mpr
  intro η
  by_cases hzero : (η : FiniteMeasure E) = 0
  · have hsize : size η = 0 := by
      have hm : mass η = 0 := by simp [mass, hzero]
      rw [mass_eq_size] at hm
      exact_mod_cast hm
    have hs : ∀ᶠ η' in 𝓝 η, size η' = 0 := by
      have ht := (continuous_size.tendsto η).eventually
        ((isOpen_discrete ({0} : Set ℕ)).mem_nhds hsize)
      exact ht.mono (fun η' hη' ↦ hη')
    apply (tendsto_const_nhds : Tendsto (fun _ : PointMeasure E ↦
      (η : FiniteMeasure E).normalize) (𝓝 η) (𝓝 (η : FiniteMeasure E).normalize)).congr'
    filter_upwards [hs] with η' hη'
    have hm : mass η' = 0 := by rw [mass_eq_size, hη']; simp
    have hz : (η' : FiniteMeasure E) = 0 :=
      (FiniteMeasure.mass_zero_iff (η' : FiniteMeasure E)).mp hm
    simp [hzero, hz]
  · exact FiniteMeasure.tendsto_normalize_of_tendsto (continuous_val.tendsto η) hzero

/-- A literal integer-mass and normalized-measure encoding. -/
def encode (η : PointMeasure E) : ℕ × ProbabilityMeasure E :=
  (size η, (η : FiniteMeasure E).normalize)

omit [CompactSpace E] in
theorem continuous_encode : Continuous (encode : PointMeasure E → ℕ × ProbabilityMeasure E) :=
  continuous_size.prodMk continuous_normalize

/-- Continuous decoding into actual finite measures. -/
def decode (p : ℕ × ProbabilityMeasure E) : FiniteMeasure E :=
  (p.1 : ℝ≥0) • p.2.toFiniteMeasure

omit [CompactSpace E] [Nonempty E] in
theorem continuous_decode : Continuous (decode : (ℕ × ProbabilityMeasure E) → FiniteMeasure E) := by
  have hn : Continuous (fun p : ℕ × ProbabilityMeasure E ↦ (p.1 : ℝ≥0)) :=
    continuous_of_discreteTopology.comp continuous_fst
  exact hn.smul (ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_snd)

omit [MetricSpace E] [CompactSpace E] [BorelSpace E] in
theorem decode_encode (η : PointMeasure E) : decode (encode η) = (η : FiniteMeasure E) := by
  unfold decode encode
  rw [← mass_eq_size η]
  exact (FiniteMeasure.self_eq_mass_smul_normalize (η : FiniteMeasure E)).symm

omit [CompactSpace E] in
theorem isEmbedding_encode : Topology.IsEmbedding
    (encode : PointMeasure E → ℕ × ProbabilityMeasure E) := by
  apply Topology.IsEmbedding.of_comp continuous_encode continuous_decode
  have he : (decode : (ℕ × ProbabilityMeasure E) → FiniteMeasure E) ∘ encode =
      fun η : PointMeasure E ↦ (η : FiniteMeasure E) := by
    funext η
    exact decode_encode η
  rw [he]
  exact Topology.IsEmbedding.subtypeVal

omit [Nonempty E] in
/-- Each integer-mass stratum is compact in the actual weak topology. -/
theorem isCompact_size_eq (n : ℕ) : IsCompact {η : PointMeasure E | size η = n} := by
  have he : {η : PointMeasure E | size η = n} =
      {η | mass η ≤ (n : ℝ≥0)} ∩ {η | size η = n} := by
    ext η
    constructor
    · intro hη
      change size η = n at hη
      refine ⟨?_, hη⟩
      change mass η ≤ (n : ℝ≥0)
      rw [mass_eq_size, hη]
    · exact And.right
  rw [he]
  exact (isCompact_mass_le n).inter_right (isClosed_eq continuous_size continuous_const)

theorem isClosed_range_encode : IsClosed
    (Set.range (encode : PointMeasure E → ℕ × ProbabilityMeasure E)) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  let C : Set (ℕ × ProbabilityMeasure E) := encode '' {η : PointMeasure E | size η = y.1}
  have hC : IsClosed C := ((isCompact_size_eq y.1).image continuous_encode).isClosed
  have hyC : y ∈ Cᶜ := by
    intro h
    obtain ⟨η, _, hη⟩ := h
    exact hy ⟨η, hη⟩
  have hU : IsOpen {z : ℕ × ProbabilityMeasure E | z.1 = y.1} :=
    (isOpen_discrete ({y.1} : Set ℕ)).preimage continuous_fst
  have hn : {z : ℕ × ProbabilityMeasure E | z.1 = y.1} ∩ Cᶜ ∈ 𝓝 y :=
    inter_mem (hU.mem_nhds rfl) (hC.isOpen_compl.mem_nhds hyC)
  apply Filter.mem_of_superset hn
  intro z hz hzr
  obtain ⟨η, rfl⟩ := hzr
  exact hz.2 ⟨η, hz.1, rfl⟩

theorem isClosedEmbedding_encode : Topology.IsClosedEmbedding
    (encode : PointMeasure E → ℕ × ProbabilityMeasure E) :=
  ⟨isEmbedding_encode, isClosed_range_encode⟩

omit [Nonempty E] in
/-- Compactness and genuine weak metrizability supply a complete Polish
topology on probability measures of the actual compact metric window. -/
theorem probabilityMeasure_polishSpace : PolishSpace (ProbabilityMeasure E) := by
  let : MetricSpace (ProbabilityMeasure E) :=
    TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure E)
  infer_instance

/-- Polishness is derived from the proved closed embedding, not a
condition on a presumed point-process state space. -/
theorem pointMeasure_polishSpace : PolishSpace (PointMeasure E) := by
  let : PolishSpace (ProbabilityMeasure E) := probabilityMeasure_polishSpace
  exact isClosedEmbedding_encode.polishSpace

instance : PolishSpace (PointMeasure E) := pointMeasure_polishSpace

instance : StandardBorelSpace (PointMeasure E) := inferInstance

end PerronWright.FinitePointMeasurePolish
