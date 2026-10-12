import PerronWright.Kernel.CountableApproximationVectors
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Literal finite-law Perron functions and normalization

The finite-law Perron function is constructed from the proved nonnegative
unit eigenvector.  It is extended to all types by the literal kernel row
formula; no positive eigenfunction, convergence, or moment conclusion is
stored in the model.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section

namespace PerronWright.CountableKernel

theorem weightedActionCLM_ge_lower_pairing (M : CountableKernel) (h v : M.L2)
    (hh : ∀ a, 0 ≤ h a) (hv : ∀ a, 0 ≤ v a) {lower : ℝ}
    (hlo : ∀ a b, lower ≤ M.kernel a b) (a : ℕ) :
    h a * (lower * inner ℝ h v) ≤ M.weightedActionCLM h v a := by
  rw [weightedActionCLM, M.featureActionCLM_apply_integral, L2.inner_def]
  apply mul_le_mul_of_nonneg_left _ (hh a)
  rw [← integral_const_mul]
  apply integral_mono ((L2.integrable_inner h v).const_mul lower)
    (M.integrable_feature_row_mul_input h v a)
  intro b
  change lower * inner ℝ (h b) (v b) ≤ M.kernel a b * h b * v b
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_right (hlo a b) (mul_nonneg (hh b) (hv b))

theorem weightedActionCLM_le_upper_pairing (M : CountableKernel) (h v : M.L2)
    (hh : ∀ a, 0 ≤ h a) (hv : ∀ a, 0 ≤ v a) (a : ℕ) :
    M.weightedActionCLM h v a ≤ h a * (M.upper * inner ℝ h v) := by
  rw [weightedActionCLM, M.featureActionCLM_apply_integral, L2.inner_def]
  apply mul_le_mul_of_nonneg_left _ (hh a)
  rw [← integral_const_mul]
  apply integral_mono (M.integrable_feature_row_mul_input h v a)
    ((L2.integrable_inner h v).const_mul M.upper)
  intro b
  change M.kernel a b * h b * v b ≤ M.upper * inner ℝ (h b) (v b)
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_right (M.le_upper a b) (mul_nonneg (hh b) (hv b))

theorem weighted_eigenvector_pairing_pos (M : CountableKernel) (h v : M.L2)
    (hh : ∀ a, 0 ≤ h a) (hv : ∀ a, 0 ≤ v a) (hvne : v ≠ 0)
    {r : ℝ} (hr : 0 < r) (hev : M.weightedActionCLM h v = r • v) :
    0 < inner ℝ h v := by
  have hc : 0 ≤ inner ℝ h v := by
    rw [L2.inner_def]
    exact integral_nonneg (fun a ↦ by simpa [mul_comm] using mul_nonneg (hh a) (hv a))
  apply lt_of_le_of_ne hc
  intro hz
  have hvzero : v = 0 := by
    apply Lp.ext
    filter_upwards [] with a
    have hle := M.weightedActionCLM_le_upper_pairing h v hh hv a
    have hnonneg := M.weightedActionCLM_nonneg h v hh hv a
    rw [← hz, mul_zero, mul_zero] at hle
    have he : M.weightedActionCLM h v a = 0 := le_antisymm hle hnonneg
    rw [hev, M.coe_smul_at] at he
    simpa using (mul_eq_zero.mp he).resolve_left hr.ne'
  exact hvne hvzero

def finitePerronVector (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) (s : Finset ℕ) (hzero : ∀ a, a ∉ s → w a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) : M.L2 :=
  Classical.choose (M.exists_nonnegative_weighted_perron w hw hs s hzero hlower hlo).2

theorem finitePerronVector_spec (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) (s : Finset ℕ) (hzero : ∀ a, a ∉ s → w a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    ‖M.finitePerronVector w hw hs s hzero hlower hlo‖ = 1 ∧
      (∀ a, 0 ≤ M.finitePerronVector w hw hs s hzero hlower hlo a) ∧
      M.weightedActionCLM (M.weightFeature w hw hs)
        (M.finitePerronVector w hw hs s hzero hlower hlo) =
      M.weightedSpectralRadius w hw hs • M.finitePerronVector w hw hs s hzero hlower hlo :=
  Classical.choose_spec (M.exists_nonnegative_weighted_perron w hw hs s hzero hlower hlo).2

def finitePerronFunction (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) (s : Finset ℕ) (hzero : ∀ a, a ∉ s → w a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) (a : ℕ) : ℝ :=
  inner ℝ (M.featureRow (M.weightFeature w hw hs) a)
    (M.finitePerronVector w hw hs s hzero hlower hlo) /
  (M.weightedSpectralRadius w hw hs * inner ℝ (M.weightFeature w hw hs)
    (M.finitePerronVector w hw hs s hzero hlower hlo))

theorem norm_featureRow_sub_le (M : CountableKernel) (h g : M.L2) (a : ℕ) :
    ‖M.featureRow h a - M.featureRow g a‖ ≤ M.upper * ‖h - g‖ := by
  rw [← M.featureRow_sub]
  exact M.norm_featureRow_le _ _

theorem featureRow_tendsto (M : CountableKernel) (h : ℕ → M.L2) (g : M.L2)
    (ht : Tendsto h atTop (nhds g)) (a : ℕ) :
    Tendsto (fun n ↦ M.featureRow (h n) a) atTop (nhds (M.featureRow g a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ M.norm_featureRow_sub_le _ _ _)
    (by simpa using (tendsto_iff_norm_sub_tendsto_zero.mp ht).const_mul M.upper)

theorem featureRow_baseFeature (M : CountableKernel) (a : ℕ) :
    M.featureRow M.baseFeature a = M.row a := by
  apply Lp.ext
  filter_upwards [M.row_coe_ae a] with b hb
  rw [M.featureRow_apply, M.baseFeature_apply, mul_one, hb]

theorem inner_baseFeature (M : CountableKernel) (v : M.L2) :
    inner ℝ M.baseFeature v = ∫ a, v a ∂M.mu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with a
  rw [M.baseFeature_apply]
  simp

theorem inner_baseFeature_unitPerron (M : CountableKernel) (hM : M.IsRegularCritical) :
    inner ℝ M.baseFeature (M.unitPerronVector hM) = ‖M.perronVector hM‖⁻¹ := by
  rw [M.inner_baseFeature, unitPerronVector, M.integral_smul_input, M.perronVector_integral, mul_one]

/-- The chosen finite-law vectors converge to the proved canonical unit
Perron vector.  Every operator/vector here is constructed from `w`. -/
theorem finitePerronVector_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    (w : ℕ → ℕ → ℝ) (hw : ∀ n a, 0 ≤ w n a) (hs : ∀ n, HasSum (w n) 1)
    (s : ℕ → Finset ℕ) (hzero : ∀ n a, a ∉ s n → w n a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (herr : Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) atTop (nhds 0)) :
    Tendsto (fun n ↦ M.finitePerronVector (w n) (hw n) (hs n) (s n) (hzero n) hlower hlo)
      atTop (nhds (M.unitPerronVector hM)) :=
  M.weighted_perron_tendsto hM w hw hs herr _
    (fun n ↦ (M.finitePerronVector_spec (w n) (hw n) (hs n) (s n) (hzero n) hlower hlo).1)
    (fun n ↦ (M.finitePerronVector_spec (w n) (hw n) (hs n) (s n) (hzero n) hlower hlo).2.1)
    (fun n ↦ (M.finitePerronVector_spec (w n) (hw n) (hs n) (s n) (hzero n) hlower hlo).2.2)

theorem finitePerron_pairing_pos (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) (s : Finset ℕ) (hzero : ∀ a, a ∉ s → w a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    0 < inner ℝ (M.weightFeature w hw hs) (M.finitePerronVector w hw hs s hzero hlower hlo) := by
  have hv := M.finitePerronVector_spec w hw hs s hzero hlower hlo
  have hh : ∀ a, 0 ≤ M.weightFeature w hw hs a := by
    intro a
    rw [M.weightFeature_apply, weightFeatureFunction]
    exact Real.sqrt_nonneg _
  apply M.weighted_eigenvector_pairing_pos _ _ hh hv.2.1 _
    (M.exists_nonnegative_weighted_perron w hw hs s hzero hlower hlo).1 hv.2.2
  intro hz
  simpa [hz] using hv.1

theorem featureRow_inner_bounds (M : CountableKernel) (h v : M.L2)
    (hh : ∀ a, 0 ≤ h a) (hv : ∀ a, 0 ≤ v a) {lower : ℝ}
    (hlo : ∀ a b, lower ≤ M.kernel a b) (a : ℕ) :
    lower * inner ℝ h v ≤ inner ℝ (M.featureRow h a) v ∧
      inner ℝ (M.featureRow h a) v ≤ M.upper * inner ℝ h v := by
  rw [L2.inner_def, L2.inner_def]
  have hr : (∫ b, inner ℝ (M.featureRow h a b) (v b) ∂M.mu) =
      ∫ b, M.kernel a b * h b * v b ∂M.mu := by
    apply integral_congr_ae
    filter_upwards [] with b
    rw [M.featureRow_apply]
    simp [mul_comm]
  rw [hr]
  constructor
  · rw [← integral_const_mul]
    apply integral_mono ((L2.integrable_inner h v).const_mul lower)
      (M.integrable_feature_row_mul_input h v a)
    intro b
    change lower * inner ℝ (h b) (v b) ≤ M.kernel a b * h b * v b
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_right (hlo a b) (mul_nonneg (hh b) (hv b))
  · rw [← integral_const_mul]
    apply integral_mono (M.integrable_feature_row_mul_input h v a)
      ((L2.integrable_inner h v).const_mul M.upper)
    intro b
    change M.kernel a b * h b * v b ≤ M.upper * inner ℝ (h b) (v b)
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_right (M.le_upper a b) (mul_nonneg (hh b) (hv b))

theorem finitePerronFunction_bounds (M : CountableKernel) (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : HasSum w 1) (s : Finset ℕ) (hzero : ∀ a, a ∉ s → w a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) (a : ℕ) :
    0 < M.finitePerronFunction w hw hs s hzero hlower hlo a ∧
      M.finitePerronFunction w hw hs s hzero hlower hlo a ≤ M.upper / lower := by
  let h := M.weightFeature w hw hs
  let v := M.finitePerronVector w hw hs s hzero hlower hlo
  let r := M.weightedSpectralRadius w hw hs
  let c := inner ℝ h v
  have hc : 0 < c := M.finitePerron_pairing_pos w hw hs s hzero hlower hlo
  have hr : 0 < r := (M.exists_nonnegative_weighted_perron w hw hs s hzero hlower hlo).1
  have hlr : lower ≤ r := by
    dsimp [r]
    rw [M.weightedSpectralRadius_eq_norm]
    exact M.weighted_norm_ge_lower h (M.norm_weightFeature w hw hs) hlo
  have hh : ∀ a, 0 ≤ h a := by
    intro a
    dsimp [h]
    rw [M.weightFeature_apply, weightFeatureFunction]
    exact Real.sqrt_nonneg _
  have hb := M.featureRow_inner_bounds h v hh
    (M.finitePerronVector_spec w hw hs s hzero hlower hlo).2.1 hlo a
  change 0 < inner ℝ (M.featureRow h a) v / (r * c) ∧
    inner ℝ (M.featureRow h a) v / (r * c) ≤ M.upper / lower
  constructor
  · exact div_pos ((mul_pos hlower hc).trans_le hb.1) (mul_pos hr hc)
  · calc
      inner ℝ (M.featureRow h a) v / (r * c) ≤ M.upper * c / (r * c) :=
        div_le_div_of_nonneg_right hb.2 (mul_nonneg hr.le hc.le)
      _ = M.upper / r := by field_simp
      _ ≤ M.upper / lower := div_le_div_of_nonneg_left M.upper_nonneg hlower hlr

theorem finitePerronFunction_tendsto (M : CountableKernel) (hM : M.IsRegularCritical)
    (w : ℕ → ℕ → ℝ) (hw : ∀ n a, 0 ≤ w n a) (hs : ∀ n, HasSum (w n) 1)
    (s : ℕ → Finset ℕ) (hzero : ∀ n a, a ∉ s n → w n a = 0)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b)
    (herr : Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) atTop (nhds 0)) (a : ℕ) :
    Tendsto (fun n ↦ M.finitePerronFunction (w n) (hw n) (hs n) (s n) (hzero n) hlower hlo a)
      atTop (nhds (M.perronVector hM a)) := by
  have hh := M.weightFeature_tendsto w hw hs herr
  have hv := M.finitePerronVector_tendsto hM w hw hs s hzero hlower hlo herr
  have hc := hh.inner (𝕜 := ℝ) hv
  have hrow := (M.featureRow_tendsto _ _ hh a).inner (𝕜 := ℝ) hv
  have hr := M.weightedSpectralRadius_tendsto_one hM.1 w hw hs herr
  have hd : (1 : ℝ) * inner ℝ M.baseFeature (M.unitPerronVector hM) ≠ 0 := by
    rw [one_mul, M.inner_baseFeature_unitPerron]
    exact inv_ne_zero (M.perronVector_norm_pos hM).ne'
  have ht := hrow.div (hr.mul hc) hd
  have he : inner ℝ (M.featureRow M.baseFeature a) (M.unitPerronVector hM) /
      (1 * inner ℝ M.baseFeature (M.unitPerronVector hM)) = M.perronVector hM a := by
    rw [M.featureRow_baseFeature, one_mul, M.inner_baseFeature_unitPerron]
    have hfix := congrArg (fun v : M.L2 ↦ v a) (M.unitPerronVector_fixed hM)
    have hact : M.actionCLM (M.unitPerronVector hM) a =
        inner ℝ (M.row a) (M.unitPerronVector hM) := M.forall_of_ae (M.action_coe_ae _) a
    rw [hact] at hfix
    rw [hfix, unitPerronVector, M.coe_smul_at]
    field_simp [(M.perronVector_norm_pos hM).ne']
  exact he ▸ ht

theorem finitePerronFunction_weight_identity (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) {lower : ℝ}
    (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) (a : ℕ) :
    w a * M.finitePerronFunction w hw hs s hzero hlower hlo a =
      M.mu.real {a} * (M.weightFeature w hw hs a *
        M.finitePerronVector w hw hs s hzero hlower hlo a) /
      inner ℝ (M.weightFeature w hw hs) (M.finitePerronVector w hw hs s hzero hlower hlo) := by
  let h := M.weightFeature w hw hs
  let v := M.finitePerronVector w hw hs s hzero hlower hlo
  let r := M.weightedSpectralRadius w hw hs
  let c := inner ℝ h v
  have hr : r ≠ 0 := (M.exists_nonnegative_weighted_perron w hw hs s hzero hlower hlo).1.ne'
  have hc : c ≠ 0 := (M.finitePerron_pairing_pos w hw hs s hzero hlower hlo).ne'
  have he : h a * inner ℝ (M.featureRow h a) v = r * v a := by
    have he := congrArg (fun v : M.L2 ↦ v a)
      (M.finitePerronVector_spec w hw hs s hzero hlower hlo).2.2
    rw [weightedActionCLM, M.featureActionCLM_apply, M.coe_smul_at] at he
    exact he
  have hsq : M.mu.real {a} * h a ^ 2 = w a := by
    dsimp [h]
    rw [M.weightFeature_apply]
    exact M.weightFeatureFunction_square w hw a
  change w a * (inner ℝ (M.featureRow h a) v / (r * c)) = M.mu.real {a} * (h a * v a) / c
  field_simp
  linear_combination (norm := ring) -(inner ℝ (M.featureRow h a) v) * hsq +
    (M.mu.real {a} * h a) * he

theorem finitePerronFunction_hasSum_one (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) {lower : ℝ}
    (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) :
    HasSum (fun a ↦ w a * M.finitePerronFunction w hw hs s hzero hlower hlo a) 1 := by
  let h := M.weightFeature w hw hs
  let v := M.finitePerronVector w hw hs s hzero hlower hlo
  let c := inner ℝ h v
  have hb := M.finitePerronFunction_bounds w hw hs s hzero hlower hlo
  have hsum : Summable (fun a ↦ w a * M.finitePerronFunction w hw hs s hzero hlower hlo a) := by
    apply (hs.summable.mul_left (M.upper / lower)).of_nonneg_of_le
    · intro a
      exact mul_nonneg (hw a) (hb a).1.le
    · intro a
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hb a).2 (hw a)
  apply hsum.hasSum_iff.mpr
  simp_rw [M.finitePerronFunction_weight_identity]
  rw [tsum_div_const, ← M.integral_eq_tsum_atom]
  have he : (∫ a, h a * v a ∂M.mu) = c := by
    dsimp only [c]
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [] with a
    simp [mul_comm]
  change (∫ a, h a * v a ∂M.mu) / c = 1
  rw [he, div_self (M.finitePerron_pairing_pos w hw hs s hzero hlower hlo).ne']

/-- The normalized positive function really satisfies the literal finite
kernel-law eigen-equation on every type, including its row-formula
extension outside the finite support. -/
theorem finitePerronFunction_eigen (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) {lower : ℝ}
    (hlower : 0 < lower) (hlo : ∀ a b, lower ≤ M.kernel a b) (a : ℕ) :
    M.finiteLawAction s w (M.finitePerronFunction w hw hs s hzero hlower hlo) a =
      M.weightedSpectralRadius w hw hs * M.finitePerronFunction w hw hs s hzero hlower hlo a := by
  classical
  let h := M.weightFeature w hw hs
  let v := M.finitePerronVector w hw hs s hzero hlower hlo
  let r := M.weightedSpectralRadius w hw hs
  let c := inner ℝ h v
  have hr : r ≠ 0 := (M.exists_nonnegative_weighted_perron w hw hs s hzero hlower hlo).1.ne'
  have hc : c ≠ 0 := (M.finitePerron_pairing_pos w hw hs s hzero hlower hlo).ne'
  have hrow : inner ℝ (M.featureRow h a) v =
      ∑ b ∈ s, M.kernel a b * (M.mu.real {b} * (h b * v b)) := by
    rw [L2.inner_def, M.integral_eq_tsum_atom]
    simp_rw [M.featureRow_apply]
    have ht : (∑' b, M.mu.real {b} * inner ℝ (M.kernel a b * h b) (v b)) =
        ∑' b, M.kernel a b * (M.mu.real {b} * (h b * v b)) := by
      apply tsum_congr
      intro b
      simp [mul_comm, mul_assoc]
    rw [ht]
    apply tsum_eq_sum
    intro b hb
    have hz : h b = 0 := M.weightFeature_eq_zero w hw hs (hzero b hb)
    rw [hz]
    simp
  unfold finiteLawAction
  simp_rw [mul_assoc, M.finitePerronFunction_weight_identity]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← hrow]
  change inner ℝ (M.featureRow h a) v / c = r * (inner ℝ (M.featureRow h a) v / (r * c))
  field_simp

/-- Every genuine eigenvalue of the literal finite law is bounded in
modulus by the constructed spectral radius.  Together with the positive
normalized eigenfunction above, this identifies its actual Perron root
without assuming a matrix-spectrum convergence theorem. -/
theorem finiteLaw_eigenvalue_abs_le (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (f : ℕ → ℝ) {lam : ℝ}
    (hfne : ∃ a ∈ s, 0 < w a ∧ f a ≠ 0)
    (he : ∀ a ∈ s, M.finiteLawAction s w f a = lam * f a) :
    |lam| ≤ M.weightedSpectralRadius w hw hs := by
  classical
  let h := M.weightFeature w hw hs
  let v := M.finiteLawLift s h f
  have hvne : v ≠ 0 := by
    obtain ⟨a, ha, hwa, hfa⟩ := hfne
    have hha : 0 < h a := by
      dsimp [h]
      rw [M.weightFeature_apply, weightFeatureFunction]
      exact Real.sqrt_pos.mpr (div_pos hwa (M.atomMass_pos a))
    intro hz
    have hez := congrArg (fun v : M.L2 ↦ v a) hz
    have hez' : M.finiteLawLift s h f a = 0 := by simpa [v] using hez
    rw [M.finiteLawLift_apply, if_pos ha] at hez'
    exact hfa ((mul_eq_zero.mp hez').resolve_left hha.ne')
  have hev : M.weightedActionCLM h v = lam • v := by
    dsimp only [v, h]
    rw [M.finiteLawLift_intertwines w hw hs s hzero f]
    apply Lp.ext
    filter_upwards [] with a
    rw [M.coe_smul_at, M.finiteLawLift_apply, M.finiteLawLift_apply]
    by_cases ha : a ∈ s
    · simp only [if_pos ha, he a ha]
      ring
    · simp only [if_neg ha, mul_zero]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hb := (M.weightedActionCLM h).le_opNorm v
  rw [hev, norm_smul, Real.norm_eq_abs] at hb
  rw [M.weightedSpectralRadius_eq_norm]
  exact (mul_le_mul_iff_of_pos_right hn).mp hb

end PerronWright.CountableKernel
