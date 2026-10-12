import PerronWright.Probability.FiniteIrreducibleGlobalPointLawLimit

/-! # Independence of the actual limit from O(1)-rounded assignments

An actual alternating assignment sequence still satisfies the literal
O(1) fiber-count condition. Its already proved full weak convergence,
together with the genuine even and odd subsequences, proves that two
arbitrary fixed-type realizations have the same spatial limit law.
No density-determination or convergence conclusion is an input to the
model-only terminal comparing the constructed limit laws.
-/

open MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FiniteIrreducibleProcessAssignmentIndependence

open FiniteIrreducibleComponentProcess
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*}

def interleavedAssignment (v w : (n : ℕ) → Fin n → S) (n : ℕ) : Fin n → S :=
  if n % 2 = 0 then v n else w n

theorem interleavedAssignment_even (v w : (n : ℕ) → Fin n → S) (k : ℕ) :
    interleavedAssignment v w (2*k) = v (2*k) := by
  simp [interleavedAssignment]

theorem interleavedAssignment_odd (v w : (n : ℕ) → Fin n → S) (k : ℕ) :
    interleavedAssignment v w (2*k+1) = w (2*k+1) := by
  simp [interleavedAssignment, Nat.add_mod]

variable [Fintype S] [DecidableEq S]

theorem interleavedAssignment_rounding (M : FiniteIrreducibleModel S)
    (v w : (n : ℕ) → Fin n → S) (E F : ℝ)
    (hv : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E)
    (hw : ∀ᶠ n in atTop, ∀ s, |(fiberCount (w n) s : ℝ)-(n : ℝ)*M.weight s| ≤ F) :
    ∀ᶠ n in atTop, ∀ s,
      |(fiberCount (interleavedAssignment v w n) s : ℝ)-(n : ℝ)*M.weight s| ≤ max E F := by
  filter_upwards [hv,hw] with n hnV hnW s
  by_cases hn : n % 2 = 0
  · simpa only [interleavedAssignment,if_pos hn] using (hnV s).trans (le_max_left E F)
  · simpa only [interleavedAssignment,if_neg hn] using (hnW s).trans (le_max_right E F)

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

/-- Different actual assignment sequences cannot have different global
spatial weak limits under the same literal model and critical time. -/
theorem process_limits_eq_of_assignments (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ)
    (v w : (n : ℕ) → Fin n → S) (E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hv : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E)
    (hw : ∀ᶠ n in atTop, ∀ s, |(fiberCount (w n) s : ℝ)-(n : ℝ)*M.weight s| ≤ F)
    {ν ρ : ProbabilityMeasure
      (LocallyFinitePointMeasureVague.LocalPointMeasure ComponentGlobalPointProcess.PositiveSizeSurplus)}
    (hν : Tendsto (fun n ↦ unmarkedProcessLaw M lambda n (v n)) atTop (𝓝 ν))
    (hρ : Tendsto (fun n ↦ unmarkedProcessLaw M lambda n (w n)) atTop (𝓝 ρ)) :
    ν = ρ := by
  obtain ⟨ζ,hζ,_⟩ := FiniteIrreducibleGlobalPointLawLimit.exists_unique_unmarkedProcessLaw_limit
    M hM lambda (interleavedAssignment v w) (max E F)
      (by simpa using max_le_max hE hF) (interleavedAssignment_rounding M v w E F hv hw)
  have he : Tendsto (fun k : ℕ ↦ 2*k) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ by change k ≤ 2*k; omega) tendsto_id
  have ho : Tendsto (fun k : ℕ ↦ 2*k+1) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ by change k ≤ 2*k+1; omega) tendsto_id
  have hζe : Tendsto (fun k ↦ unmarkedProcessLaw M lambda (2*k) (v (2*k))) atTop (𝓝 ζ) := by
    simpa only [Function.comp_def,interleavedAssignment_even] using hζ.comp he
  have hζo : Tendsto (fun k ↦ unmarkedProcessLaw M lambda (2*k+1) (w (2*k+1))) atTop (𝓝 ζ) := by
    simpa only [Function.comp_def,interleavedAssignment_odd] using hζ.comp ho
  exact (tendsto_nhds_unique (hν.comp he) hζe).trans
    (tendsto_nhds_unique (hρ.comp ho) hζo).symm

/-- Model-only equality of the genuine constructed full spatial limit
laws for arbitrary O(1)-rounded fixed assignments. -/
theorem unmarkedProcessLimitLaw_eq_of_assignments (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (lambda : ℝ)
    (v w : (n : ℕ) → Fin n → S) (E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hv : ∀ᶠ n in atTop, ∀ s, |(fiberCount (v n) s : ℝ)-(n : ℝ)*M.weight s| ≤ E)
    (hw : ∀ᶠ n in atTop, ∀ s, |(fiberCount (w n) s : ℝ)-(n : ℝ)*M.weight s| ≤ F) :
    FiniteIrreducibleGlobalPointLawLimit.unmarkedProcessLimitLaw M hM lambda v E hE hv =
      FiniteIrreducibleGlobalPointLawLimit.unmarkedProcessLimitLaw M hM lambda w F hF hw :=
  process_limits_eq_of_assignments M hM lambda v w E F hE hF hv hw
    (FiniteIrreducibleGlobalPointLawLimit.tendsto_unmarkedProcessLimitLaw M hM lambda v E hE hv)
    (FiniteIrreducibleGlobalPointLawLimit.tendsto_unmarkedProcessLimitLaw M hM lambda w F hF hw)

end PerronWright.FiniteIrreducibleProcessAssignmentIndependence
