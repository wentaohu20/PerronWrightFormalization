import PerronWright.Probability.FiniteIrreducibleMarkedGlobalTests
import PerronWright.Probability.FiniteIrreducibleMarkedGlobalTightness
import PerronWright.Probability.FiniteIrreducibleGlobalTightness
import PerronWright.Probability.CompactGlobalMarkedPointLawLimit

/-! # Actual deterministic global empirical-mark collapse

Real marked tightness and the proved joint compact-support test-law
transfer lift every genuine unmarked weak subsequence to its actual
constant-Perron marked weak law. This yields a model-only simultaneous
unmarked/marked vague weak subsequence. Full-sequence spatial uniqueness
is deliberately not assumed or asserted in the model-only terminal.
-/

open MeasureTheory Filter Topology
open scoped Classical CompactlySupported
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteIrreducibleMarkedGlobalConvergence

open FiniteIrreducibleMarkedGlobalTests FiniteIrreducibleMarkedGlobalTightness
  FiniteIrreducibleMarkedComponentProcess ComponentGlobalMarkedProcess
  ComponentGlobalPointProcess LocallyFinitePointMeasureVague
  CompactGlobalMarkedTestLawLimit CompactGlobalMarkedPointLawLimit
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Source-composition theorem, not a model-only spatial-limit premise.
All marked concentration, tightness and law determination are proved. -/
theorem markedProcessLaw_tendsto_of_unmarked (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus))
    (hsource : Tendsto (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedProcessLaw
      M lambda (N n) (x (N n))) atTop (𝓝 μ)) :
    Tendsto (fun n ↦ FiniteIrreducibleMarkedComponentProcess.markedProcessLaw
      M lambda (N n) (x (N n))) atTop (𝓝 (canonicalGlobalMarkedLaw M hM μ)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro I hI
  obtain ⟨ρ,J,hJ,hρ⟩ := exists_reindexed_markedProcessLaw_subseq_limit
    M hM lambda x D hD hround (N ∘ I)
  have he : ρ = canonicalGlobalMarkedLaw M hM μ := by
    apply probability_ext_of_finiteTestMaps
    intro F
    let f : F → C_c(MarkedPositiveSizeSurplus S, ℝ) := Subtype.val
    have hρf := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun k ↦ FiniteIrreducibleMarkedComponentProcess.markedProcessLaw
        M lambda ((N ∘ I) (J k)) (x ((N ∘ I) (J k)))) ρ hρ (continuous_globalTestVector f)
    change Tendsto (fun k ↦ FiniteIrreducibleMarkedGlobalTests.markedTestLaw
      M lambda (N (I (J k))) (x (N (I (J k)))) f) atTop
      (𝓝 (ρ.map (continuous_globalTestVector f).measurable.aemeasurable)) at hρf
    exact tendsto_nhds_unique hρf
      ((FiniteIrreducibleMarkedGlobalTests.markedTestLaw_tendsto_of_unmarked
        M hM lambda x D hD hround N hN μ hsource f).comp (hI.comp hJ.tendsto_atTop))
  exact ⟨J,he ▸ hρ⟩

/-- Genuine model-only simultaneous vague weak subsequence. Every atom
of the marked limit carries the actual Perron probability law via the
proved proper marking pushforward; no target-law existence is input. -/
theorem exists_joint_unmarked_markedProcessLaw_subseq_limit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ) (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s, |(fiberCount (x n) s : ℝ)-(n : ℝ)*M.weight s| ≤ D) :
    ∃ μ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus), ∃ N : ℕ → ℕ,
      StrictMono N ∧
      Tendsto (fun k ↦ FiniteIrreducibleComponentProcess.unmarkedProcessLaw
        M lambda (N k) (x (N k))) atTop (𝓝 μ) ∧
      Tendsto (fun k ↦ FiniteIrreducibleMarkedComponentProcess.markedProcessLaw
        M lambda (N k) (x (N k))) atTop (𝓝 (canonicalGlobalMarkedLaw M hM μ)) := by
  obtain ⟨μ,N,hN,hμ⟩ := FiniteIrreducibleGlobalTightness.exists_unmarkedProcessLaw_subseq_limit
    M hM lambda x D hD hround
  exact ⟨μ,N,hN,hμ,markedProcessLaw_tendsto_of_unmarked
    M hM lambda x D hD hround N hN.tendsto_atTop μ hμ⟩

end PerronWright.FiniteIrreducibleMarkedGlobalConvergence
