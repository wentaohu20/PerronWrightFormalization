import PerronWright.Kernel.CountableApproximationPerron
import Mathlib.Topology.Sequences

/-!
# Convergence of genuine normalized Perron vectors

Compactness of the original operator and its proved simple positive fixed
space force every nonnegative unit approximate eigenvector to converge to
the canonical unit Perron vector.  The final theorem specializes this
argument to the constructed finite probability operators and their actual
spectral radii.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace PerronWright.CountableKernel

theorem inner_atomVector (M : CountableKernel) (v : M.L2) (a : ℕ) :
    inner ℝ (M.atomVector a) v = M.mu.real {a} * v a := by
  classical
  rw [L2.inner_def, M.integral_eq_tsum_atom]
  simp_rw [M.atomVector_apply]
  simp [mul_comm]

def pointEvaluationCLM (M : CountableKernel) (a : ℕ) : M.L2 →L[ℝ] ℝ :=
  (M.mu.real {a})⁻¹ • innerSL ℝ (M.atomVector a)

theorem pointEvaluationCLM_apply (M : CountableKernel) (a : ℕ) (v : M.L2) :
    M.pointEvaluationCLM a v = v a := by
  rw [pointEvaluationCLM, smul_apply, innerSL_apply_apply, M.inner_atomVector]
  simp only [smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (M.atomMass_pos a).ne', one_mul]

def unitPerronVector (M : CountableKernel) (hM : M.IsRegularCritical) : M.L2 :=
  ‖M.perronVector hM‖⁻¹ • M.perronVector hM

theorem perronVector_norm_pos (M : CountableKernel) (hM : M.IsRegularCritical) :
    0 < ‖M.perronVector hM‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have hp := M.perronVector_pos hM 0
  simp [hz] at hp

theorem unitPerronVector_norm (M : CountableKernel) (hM : M.IsRegularCritical) :
    ‖M.unitPerronVector hM‖ = 1 := by
  rw [unitPerronVector, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (M.perronVector_norm_pos hM).le),
    inv_mul_cancel₀ (M.perronVector_norm_pos hM).ne']

theorem unitPerronVector_pos (M : CountableKernel) (hM : M.IsRegularCritical) (a : ℕ) :
    0 < M.unitPerronVector hM a := by
  rw [unitPerronVector, M.coe_smul_at]
  exact mul_pos (inv_pos.mpr (M.perronVector_norm_pos hM)) (M.perronVector_pos hM a)

theorem unitPerronVector_fixed (M : CountableKernel) (hM : M.IsRegularCritical) :
    M.actionCLM (M.unitPerronVector hM) = M.unitPerronVector hM := by
  rw [unitPerronVector, map_smul, M.perronVector_fixed hM]

theorem eq_unitPerronVector_of_nonnegative_unit_fixed (M : CountableKernel)
    (hM : M.IsRegularCritical) (v : M.L2) (hn : ‖v‖ = 1)
    (hv : ∀ a, 0 ≤ v a) (hfix : M.actionCLM v = v) : v = M.unitPerronVector hM := by
  obtain ⟨lower, hlower, hlo⟩ := hM.2
  obtain ⟨c, hc⟩ := M.fixed_eq_scalar_multiple hM.1 hlower hlo
    (M.unitPerronVector hM) (M.unitPerronVector_pos hM) (M.unitPerronVector_fixed hM) v hfix
  have hp : 0 ≤ c := by
    have h0 := hv 0
    rw [hc, M.coe_smul_at] at h0
    exact (mul_nonneg_iff_of_pos_right (M.unitPerronVector_pos hM 0)).mp h0
  have he : c = 1 := by
    rw [hc, norm_smul, Real.norm_of_nonneg hp, M.unitPerronVector_norm, mul_one] at hn
    exact hn
  simpa [he] using hc

theorem approximate_eigenvector_residual_tendsto (M : CountableKernel)
    (T : ℕ → M.L2 →L[ℝ] M.L2) (r : ℕ → ℝ) (v : ℕ → M.L2)
    (hT : Tendsto T atTop (nhds M.actionCLM)) (hr : Tendsto r atTop (nhds 1))
    (hn : ∀ n, ‖v n‖ = 1) (hev : ∀ n, T n (v n) = r n • v n) :
    Tendsto (fun n ↦ M.actionCLM (v n) - v n) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht := tendsto_iff_norm_sub_tendsto_zero.mp hT
  have hrs : Tendsto (fun n ↦ ‖r n - 1‖) atTop (nhds 0) := by
    have hd : Tendsto (fun n ↦ r n - 1) atTop (nhds 0) := by simpa using hr.sub_const 1
    simpa only [Function.comp_def, norm_zero] using ((continuous_norm.tendsto (0 : ℝ)).comp hd)
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) (by simpa using ht.add hrs)
  have he : M.actionCLM (v n) - v n = (M.actionCLM - T n) (v n) + (r n - 1) • v n := by
    rw [sub_apply, hev n, sub_smul, one_smul]
    abel
  rw [he]
  calc
    ‖(M.actionCLM - T n) (v n) + (r n - 1) • v n‖ ≤
        ‖(M.actionCLM - T n) (v n)‖ + ‖(r n - 1) • v n‖ := norm_add_le _ _
    _ ≤ ‖M.actionCLM - T n‖ * ‖v n‖ + ‖r n - 1‖ * ‖v n‖ := by
      rw [norm_smul]
      exact add_le_add ((M.actionCLM - T n).le_opNorm _) le_rfl
    _ = ‖T n - M.actionCLM‖ + ‖r n - 1‖ := by rw [hn n, mul_one, mul_one, norm_sub_rev]

theorem unit_approximate_perron_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    (v : ℕ → M.L2) (hn : ∀ n, ‖v n‖ = 1) (hv : ∀ n a, 0 ≤ v n a)
    (hres : Tendsto (fun n ↦ M.actionCLM (v n) - v n) atTop (nhds 0)) :
    Tendsto v atTop (nhds (M.unitPerronVector hM)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨K, hK, hKi⟩ := M.isCompactOperator_actionCLM.image_closedBall_subset_compact 1
  obtain ⟨u, _, ms, hms, hmu⟩ := hK.tendsto_subseq (fun n ↦
    hKi ⟨v (ns n), by simp [Metric.mem_closedBall, dist_eq_norm, hn], rfl⟩)
  have hsub := hres.comp (hns.comp hms.tendsto_atTop)
  have hu : Tendsto (fun n ↦ v (ns (ms n))) atTop (nhds u) := by
    have he := hmu.sub hsub
    convert he using 1
    · funext n
      change v (ns (ms n)) = M.actionCLM (v (ns (ms n))) -
        (M.actionCLM (v (ns (ms n))) - v (ns (ms n)))
      abel
    · simp
  have hnorm : ‖u‖ = 1 := by
    have he := (continuous_norm.tendsto u).comp hu
    have hconst : Tendsto (fun n ↦ ‖v (ns (ms n))‖) atTop (nhds (1 : ℝ)) := by
      simpa only [hn] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))
    exact tendsto_nhds_unique he hconst
  have hnonneg : ∀ a, 0 ≤ u a := by
    intro a
    have he := ((M.pointEvaluationCLM a).continuous.tendsto u).comp hu
    simp only [Function.comp_def, M.pointEvaluationCLM_apply] at he
    exact ge_of_tendsto he (Filter.Eventually.of_forall (fun n ↦ hv (ns (ms n)) a))
  have hfix : M.actionCLM u = u := by
    have he := ((M.actionCLM.continuous.tendsto u).comp hu).sub hu
    have hz : M.actionCLM u - u = 0 := tendsto_nhds_unique he hsub
    exact sub_eq_zero.mp hz
  have heq := M.eq_unitPerronVector_of_nonnegative_unit_fixed hM u hnorm hnonneg hfix
  exact ⟨ms, heq ▸ hu⟩

/-- Perron convergence is a conclusion of literal probability-weight
convergence, compactness and proved simplicity, not an interface premise. -/
theorem weighted_perron_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    (w : ℕ → ℕ → ℝ) (hw : ∀ n a, 0 ≤ w n a) (hs : ∀ n, HasSum (w n) 1)
    (herr : Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) atTop (nhds 0))
    (v : ℕ → M.L2) (hn : ∀ n, ‖v n‖ = 1) (hv : ∀ n a, 0 ≤ v n a)
    (hev : ∀ n, M.weightedActionCLM (M.weightFeature (w n) (hw n) (hs n)) (v n) =
      M.weightedSpectralRadius (w n) (hw n) (hs n) • v n) :
    Tendsto v atTop (nhds (M.unitPerronVector hM)) :=
  M.unit_approximate_perron_tendsto hM v hn hv
    (M.approximate_eigenvector_residual_tendsto _ _ v
      (M.weighted_probability_operator_tendsto w hw hs herr)
      (M.weightedSpectralRadius_tendsto_one hM.1 w hw hs herr) hn hev)

end PerronWright.CountableKernel
