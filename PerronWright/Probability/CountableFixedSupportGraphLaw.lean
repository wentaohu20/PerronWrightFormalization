import PerronWright.Probability.CountableFixedSupportSpectralDrift
import PerronWright.Probability.CountableEmpiricalGraphLaw

/-! # Exact actual fixed-truncation graph law at a varying finite parameter

The empirical spectral normalization is kept literal. It is absorbed into
the time of the fixed reference critical model by a proved parameter map.
The actual critical-scale rounding drift proves convergence of this map.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableKernel

def fixedSupportRootRatio (M : CountableKernel) (m n : ℕ) : ℝ :=
  M.fixedSupportSpectralRadius m / M.fixedSupportEmpiricalRoot m n

theorem fixedSupportRootRatio_pos (M : CountableKernel) (m n : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    0 < M.fixedSupportRootRatio m n :=
  div_pos (M.fixedSupportSpectralRadius_pos m hlower hlo)
    (M.fixedSupportEmpiricalRoot_pos m n hlower hlo)

theorem fixedSupportRootRatio_scaled_drift (M : CountableKernel) (m : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ) * (M.fixedSupportRootRatio m n - 1))
      atTop (𝓝 0) := by
  have h := (M.fixedSupportEmpiricalRoot_scaled_drift m).neg.div
    (M.fixedSupportEmpiricalRoot_tendsto m hlower hlo)
    (M.fixedSupportSpectralRadius_pos m hlower hlo).ne'
  simp only [neg_zero, zero_div] at h
  apply h.congr'
  exact Eventually.of_forall (fun n ↦ by
    unfold fixedSupportRootRatio
    change -(↑n ^ (1 / 3 : ℝ) * (M.fixedSupportEmpiricalRoot m n - M.fixedSupportSpectralRadius m)) /
      M.fixedSupportEmpiricalRoot m n =
      ↑n ^ (1 / 3 : ℝ) * (M.fixedSupportSpectralRadius m / M.fixedSupportEmpiricalRoot m n - 1)
    field_simp [(M.fixedSupportEmpiricalRoot_pos m n hlower hlo).ne']
    ring)

def fixedSupportEffectiveParameter (M : CountableKernel) (m : ℕ) (lambda : ℝ) : ℕ → ℝ :=
  CriticalParameterDrift.effectiveParameter lambda (M.fixedSupportRootRatio m)

theorem fixedSupportEffectiveParameter_tendsto (M : CountableKernel) (m : ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    Tendsto (M.fixedSupportEffectiveParameter m lambda) atTop (𝓝 lambda) := by
  simpa only [fixedSupportEffectiveParameter, add_zero] using
    CriticalParameterDrift.effectiveParameter_tendsto
      (M.fixedSupportRootRatio_scaled_drift m hlower hlo) lambda

theorem fixedSupportModel_actual_hazard (M : CountableKernel) (m n : ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (e : AnnealedGraph.Edge (n + 1)) :
    FiniteIrreducibleTypedGraphLaw.hazard (M.fixedSupportModel m hlower hlo)
      (CriticalScaling.time (M.fixedSupportEffectiveParameter m lambda (n + 1)) (n + 1))
      (M.fixedSupportVertexTypes m (n + 1)) e =
        M.empiricalNormalizedHazards (fun _ ↦ m) lambda n e := by
  unfold fixedSupportModel
  rw [M.finiteCriticalModel_hazard]
  have hr := M.fixedSupportRootRatio_pos m (n + 1) hlower hlo
  have he := CriticalParameterDrift.effective_time_eq (Nat.succ_pos n) lambda
    (M.fixedSupportRootRatio m) hr.le
  unfold fixedSupportEffectiveParameter
  rw [he]
  change (CriticalScaling.time lambda (n + 1) *
    (M.fixedSupportSpectralRadius m / M.fixedSupportEmpiricalRoot m (n + 1))) *
    M.retainedPairKernel (CountableTypeRealization.vertexTypes M m (n + 1)) e.val /
      (((n + 1 : ℕ) : ℝ) * M.fixedSupportSpectralRadius m) = _
  simp only [fixedSupportEmpiricalRoot, Nat.add_sub_cancel]
  unfold empiricalNormalizedHazards
  field_simp [(M.fixedSupportSpectralRadius_pos m hlower hlo).ne']

/-- Equality of the entire genuine independent-edge laws at every n,
not merely equality of their one-edge marginals. -/
theorem fixedSupportModel_graphLaw_eq_actual (M : CountableKernel) (m n : ℕ) (lambda : ℝ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    FiniteIrreducibleComponentProcess.graphLaw (M.fixedSupportModel m hlower hlo)
      (M.fixedSupportEffectiveParameter m lambda (n + 1)) (n + 1)
      (M.fixedSupportVertexTypes m (n + 1)) =
      M.empiricalNormalizedGraphLaw (fun _ ↦ m) lambda hlower hlo n := by
  unfold FiniteIrreducibleComponentProcess.graphLaw FiniteIrreducibleTypedGraphLaw.law
    empiricalNormalizedGraphLaw
  congr 1
  funext e
  exact M.fixedSupportModel_actual_hazard m n lambda hlower hlo e

end PerronWright.CountableKernel
