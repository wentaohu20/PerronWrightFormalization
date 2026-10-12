import PerronWright.Kernel.CountableApproximationWeights

/-!
# Spectral convergence of the actual shared-space probability operators

The square-root density conjugates are self-adjoint actual integral
operators.  Their real spectral radii converge to one whenever the atomic
probability weights converge to the original critical law in absolute `ℓ¹`.
Identification with a finite support's matrix spectrum is a separate step.
-/

open MeasureTheory

noncomputable section

namespace PerronWright.CountableKernel

theorem featureActionCLM_apply_integral (M : CountableKernel) (h g v : M.L2) (a : ℕ) :
    M.featureActionCLM h g v a = h a * ∫ b, M.kernel a b * g b * v b ∂M.mu := by
  rw [M.featureActionCLM_apply, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with b
  rw [M.featureRow_apply]
  simp [mul_comm]

theorem integrable_weighted_bilinear_kernel (M : CountableKernel) (h v w : M.L2) :
    Integrable (fun p : ℕ × ℕ ↦ M.kernel p.1 p.2 * (h p.2 * v p.2) * (h p.1 * w p.1))
      (M.mu.prod M.mu) := by
  have hi := ((Lp.memLp h).integrable_mul (Lp.memLp w)).mul_prod
    ((Lp.memLp h).integrable_mul (Lp.memLp v))
  have hκ : AEStronglyMeasurable (fun p : ℕ × ℕ ↦ M.kernel p.1 p.2) (M.mu.prod M.mu) :=
    (measurable_of_countable _).aestronglyMeasurable
  have hb := hi.bdd_mul hκ
    (Filter.Eventually.of_forall (fun p : ℕ × ℕ ↦ M.norm_kernel_le p.1 p.2))
  exact hb.congr (Filter.Eventually.of_forall (fun p ↦ by dsimp; ring))

theorem inner_weightedAction_eq_double_integral (M : CountableKernel) (h v w : M.L2) :
    inner ℝ (M.weightedActionCLM h v) w =
      ∫ a, ∫ b, M.kernel a b * (h b * v b) * (h a * w a) ∂M.mu ∂M.mu := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with a
  change inner ℝ (M.featureActionCLM h h v a) (w a) = _
  rw [M.featureActionCLM_apply_integral]
  simp_rw [integral_mul_const]
  have hi : (∫ b, M.kernel a b * (h b * v b) ∂M.mu) =
      ∫ b, M.kernel a b * h b * v b ∂M.mu := by
    apply integral_congr_ae
    filter_upwards [] with b
    ring
  rw [hi]
  simp [mul_comm, mul_assoc, mul_left_comm]

theorem isSymmetric_weightedActionCLM (M : CountableKernel) (h : M.L2) :
    (M.weightedActionCLM h).IsSymmetric := by
  intro v w
  change inner ℝ (M.weightedActionCLM h v) w = inner ℝ v (M.weightedActionCLM h w)
  rw [M.inner_weightedAction_eq_double_integral h v w, real_inner_comm,
    M.inner_weightedAction_eq_double_integral h w v]
  rw [integral_integral_swap (M.integrable_weighted_bilinear_kernel h v w)]
  apply integral_congr_ae
  filter_upwards [] with b
  apply integral_congr_ae
  filter_upwards [] with a
  rw [M.symmetric a b]
  ring

def weightedSpectralRadius (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) : ℝ :=
  (spectralRadius ℝ (M.weightedActionCLM (M.weightFeature w hw hs))).toReal

theorem weightedSpectralRadius_eq_norm (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) :
    M.weightedSpectralRadius w hw hs = ‖M.weightedActionCLM (M.weightFeature w hw hs)‖ := by
  unfold weightedSpectralRadius
  rw [ContinuousLinearMap.spectralRadius_eq_nnnorm (𝕜 := ℝ)
    (T := M.weightedActionCLM (M.weightFeature w hw hs))
    (M.isSymmetric_weightedActionCLM _).isSelfAdjoint]
  simp

/-- No spectral convergence hypothesis is used: it follows from the actual
weighted integral operator and full atomic absolute variation convergence. -/
theorem weightedSpectralRadius_tendsto_one (M : CountableKernel) (hcrit : M.IsCritical)
    (w : ℕ → ℕ → ℝ) (hw : ∀ n a, 0 ≤ w n a) (hs : ∀ n, HasSum (w n) 1)
    (herr : Filter.Tendsto (fun n ↦ ∑' a, |w n a - M.mu.real {a}|) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ M.weightedSpectralRadius (w n) (hw n) (hs n))
      Filter.atTop (nhds 1) := by
  have h := (continuous_norm.tendsto M.actionCLM).comp (M.weighted_probability_operator_tendsto w hw hs herr)
  simpa only [Function.comp_def, M.weightedSpectralRadius_eq_norm, M.norm_eq_one_of_critical hcrit] using h

end PerronWright.CountableKernel
