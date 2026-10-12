import PerronWright.Probability.CompactGlobalTestLawLimit
import PerronWright.Probability.FiniteIrreducibleWindowPointLawLimit

/-! # Genuine joint compact-support test laws for the fixed-type process

Every finite family of vague tests fits in one common window. Their
actual joint law is exactly that window's continuous integral-vector
pushforward, and the proved full window-location limit applies.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported
noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FiniteIrreducibleGlobalTestLawLimit

open ComponentGlobalPointProcess LocallyFinitePointMeasureVague
open ComponentWindowPointMeasures FinitePointMeasureCompact
open CompactGlobalTestLawLimit (testVector continuous_testVector exists_common_test_window
  windowTestVector continuous_windowTestVector)
open FiniteIrreducibleComponentProcess

variable {D : Type*} [Fintype D]
variable {S : Type*} [Fintype S] [DecidableEq S]

def globalTestLaw (M : FiniteIrreducibleModel S) (lambda : ℝ) (n : ℕ) (x0 : Fin n → S)
    (f : D → C_c(PositiveSizeSurplus, ℝ)) : ProbabilityMeasure (D → ℝ) :=
  (unmarkedProcessLaw M lambda n x0).map (continuous_testVector f).measurable.aemeasurable

/-- An exact finite-size identity of genuine probability pushforwards,
including the empty graph. -/
theorem globalTestLaw_eq_window_map (M : FiniteIrreducibleModel S) (lambda a b : ℝ)
    (R : ℕ) (ha : 0 < a) (n : ℕ) (x0 : Fin n → S) (f : D → C_c(PositiveSizeSurplus, ℝ))
    (hf : ∀ i, tsupport (f i) ⊆ ambientEmbedding ⁻¹' windowSet a b R) :
    globalTestLaw M lambda n x0 f =
      (unmarkedWindowLaw M lambda a b R n x0).map
        (continuous_windowTestVector a b R ha f).measurable.aemeasurable := by
  apply Subtype.ext
  change ((graphLaw M lambda n x0).map unmarkedProcess).map (testVector f) =
      ((graphLaw M lambda n x0).map (windowPointMeasure a b R 1)).map
          (windowTestVector a b R ha f)
  rw [Measure.map_map (continuous_testVector f).measurable (measurable_unmarkedProcess n),
    Measure.map_map (continuous_windowTestVector a b R ha f).measurable
      (measurable_windowPointMeasure a b R 1 n)]
  congr 1
  funext G i
  exact unmarkedProcess_integral_eq_window a b R ha G (f i) (hf i)

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Every genuine finite family of vague-test integrals of the actual
global graph process has a unique actual joint weak law limit. No
global target point-process law or projective-existence interface is
assumed. -/
theorem exists_unique_globalTestLaw_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ)
    (f : D → C_c(PositiveSizeSurplus, ℝ))
    (v : (n : ℕ) → Fin n → S) (E : ℝ) (hE : 0 ≤ E)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(FiniteIrreducibleTypePlacementMultiplicity.fiberCount (v n) s : ℝ) -
        (n : ℝ)*M.weight s| ≤ E) :
    ∃! θ : ProbabilityMeasure (D → ℝ),
      Tendsto (fun n ↦ globalTestLaw M lambda n (v n) f) atTop (𝓝 θ) := by
  obtain ⟨a, b, R, ha, hab, hf⟩ := exists_common_test_window f
  obtain ⟨ν, hν, _⟩ :=
    FiniteIrreducibleWindowPointLawLimit.exists_unique_unmarkedWindowLaw_limit
      M hM lambda a b ha hab R v E hE hround
  let θ := ν.map (continuous_windowTestVector a b R ha f).measurable.aemeasurable
  have hθ : Tendsto (fun n ↦ globalTestLaw M lambda n (v n) f) atTop (𝓝 θ) := by
    simpa only [globalTestLaw_eq_window_map M lambda a b R ha _ (v _) f hf] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (fun n ↦ unmarkedWindowLaw M lambda a b R n (v n)) ν hν (continuous_windowTestVector a b R ha f)
  exact ⟨θ, hθ, fun ρ hρ ↦ tendsto_nhds_unique hρ hθ⟩

end PerronWright.FiniteIrreducibleGlobalTestLawLimit

