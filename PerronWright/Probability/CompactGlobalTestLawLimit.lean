import PerronWright.Probability.ComponentGlobalPointProcess
import PerronWright.Probability.CompactWindowPointLawLimit

/-!
# Genuine joint compact-support test laws of the global component process

Every finite family of compactly supported continuous tests fits in one
actual compact size-surplus window. The literal global test vector is
exactly that window's continuous integral vector. The already proved
whole-window point-law convergence therefore gives an actual unique
joint test-law limit, without any target process-law assumption.

This is a finite-dimensional statement about actual vague tests; it
does not by itself assert tightness or weak convergence of the entire
global locally finite point-process law.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.CompactGlobalTestLawLimit

open ComponentGlobalPointProcess LocallyFinitePointMeasureVague
open ComponentWindowPointMeasures FinitePointMeasureCompact

variable {D : Type*} [Fintype D]

def testVector (f : D → C_c(PositiveSizeSurplus, ℝ))
    (η : LocalPointMeasure PositiveSizeSurplus) : D → ℝ :=
  fun i ↦ ∫ z, f i z ∂(η : Measure PositiveSizeSurplus)

omit [Fintype D] in
theorem continuous_testVector (f : D → C_c(PositiveSizeSurplus, ℝ)) :
    Continuous (testVector f) := continuous_pi (fun i ↦ continuous_integral (f i))

theorem exists_common_test_window (f : D → C_c(PositiveSizeSurplus, ℝ)) :
    ∃ a b : ℝ, ∃ R : ℕ, 0 < a ∧ a ≤ b ∧
      ∀ i, tsupport (f i) ⊆ ambientEmbedding ⁻¹' windowSet a b R := by
  obtain ⟨a, b, R, ha, hab, hK⟩ :=
    exists_compact_window (isCompact_iUnion (fun i ↦ (f i).hasCompactSupport))
  exact ⟨a, b, R, ha, hab, fun i ↦ (Set.subset_iUnion _ i).trans hK⟩

def windowTestVector (a b : ℝ) (R : ℕ) (ha : 0 < a)
    (f : D → C_c(PositiveSizeSurplus, ℝ))
    (η : PointMeasure (SurplusWindow a b R)) : D → ℝ :=
  fun i ↦ ∫ z, f i (positiveWindowEmbedding a b R ha z)
    ∂((η : FiniteMeasure (SurplusWindow a b R)) : Measure (SurplusWindow a b R))

omit [Fintype D] in
theorem continuous_windowTestVector (a b : ℝ) (R : ℕ) (ha : 0 < a)
    (f : D → C_c(PositiveSizeSurplus, ℝ)) :
    Continuous (windowTestVector a b R ha f) := by
  apply continuous_pi
  intro i
  let g : C(SurplusWindow a b R, ℝ) :=
    ⟨fun z ↦ f i (positiveWindowEmbedding a b R ha z),
      (f i).continuous.comp (continuous_positiveWindowEmbedding a b R ha)⟩
  exact (FiniteMeasure.continuous_integral_continuousMap g).comp continuous_val

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

def globalTestLaw (M : CompactBJRModel S) (lambda : ℝ) (n : ℕ)
    (f : D → C_c(PositiveSizeSurplus, ℝ)) : ProbabilityMeasure (D → ℝ) :=
  (unmarkedProcessLaw M lambda n).map (continuous_testVector f).measurable.aemeasurable

/-- An exact finite-size identity of genuine probability pushforwards,
including the empty graph. -/
theorem globalTestLaw_eq_window_map (M : CompactBJRModel S) (lambda a b : ℝ)
    (R : ℕ) (ha : 0 < a) (n : ℕ) (f : D → C_c(PositiveSizeSurplus, ℝ))
    (hf : ∀ i, tsupport (f i) ⊆ ambientEmbedding ⁻¹' windowSet a b R) :
    globalTestLaw M lambda n f =
      (unmarkedWindowLaw M lambda a b R n).map
        (continuous_windowTestVector a b R ha f).measurable.aemeasurable := by
  apply Subtype.ext
  change ((AnnealedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map unmarkedProcess).map (testVector f) =
      ((AnnealedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n).map (windowPointMeasure a b R 1)).map
          (windowTestVector a b R ha f)
  rw [Measure.map_map (continuous_testVector f).measurable (measurable_unmarkedProcess n),
    Measure.map_map (continuous_windowTestVector a b R ha f).measurable
      (measurable_windowPointMeasure a b R 1 n)]
  congr 1
  funext G i
  exact unmarkedProcess_integral_eq_window a b R ha G (f i) (hf i)

/-- Every genuine finite family of vague-test integrals of the actual
global graph process has a unique actual joint weak law limit. No
global target point-process law or projective-existence interface is
assumed. -/
theorem exists_unique_globalTestLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ)
    (f : D → C_c(PositiveSizeSurplus, ℝ)) :
    ∃! θ : ProbabilityMeasure (D → ℝ),
      Tendsto (fun n ↦ globalTestLaw M lambda n f) atTop (𝓝 θ) := by
  obtain ⟨a, b, R, ha, hab, hf⟩ := exists_common_test_window f
  obtain ⟨ν, hν, _⟩ :=
    CompactWindowPointLawLimit.exists_unique_unmarkedWindowLaw_limit
      M hM hQP lambda a b ha hab R
  let θ := ν.map (continuous_windowTestVector a b R ha f).measurable.aemeasurable
  have hθ : Tendsto (fun n ↦ globalTestLaw M lambda n f) atTop (𝓝 θ) := by
    simpa only [globalTestLaw_eq_window_map M lambda a b R ha _ f hf] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (unmarkedWindowLaw M lambda a b R) ν hν (continuous_windowTestVector a b R ha f)
  exact ⟨θ, hθ, fun ρ hρ ↦ tendsto_nhds_unique hρ hθ⟩

end PerronWright.CompactGlobalTestLawLimit
