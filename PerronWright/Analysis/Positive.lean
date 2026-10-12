import PerronWright.Kernel.Smoothing
import PerronWright.Analysis.CompactSymmetric
import Mathlib.Topology.Order.Compact

/-!
# Positive-operator arguments for the compact BJR kernel

These elementary estimates upgrade an endpoint eigenvector to a positive
fixed point and show geometric simplicity using the strictly positive
power supplied by `(B2)`.
-/

open MeasureTheory
open Module

noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

def absMap (f : C(S, ℝ)) : C(S, ℝ) := ⟨fun x => |f x|, f.continuous.abs⟩

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem absMap_apply (f : C(S, ℝ)) (x : S) : absMap f x = |f x| := rfl

theorem abs_action_le (k : ContinuousKernel S) (mu : Measure S)
    [IsFiniteMeasure mu] (f : C(S, ℝ)) (x : S) :
    |k.action mu f x| ≤ k.action mu (absMap f) x := by
  simp only [ContinuousKernel.action_apply, absMap_apply]
  calc
    |∫ y, k x y * f y ∂mu| ≤ ∫ y, |k x y * f y| ∂mu :=
      abs_integral_le_integral_abs
    _ = ∫ y, k x y * |f y| ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [abs_mul, abs_of_nonneg (k.nonneg x y)]

omit [MeasurableSpace S] [BorelSpace S] in
theorem pow_apply_of_fixed (T : C(S, ℝ) →L[ℝ] C(S, ℝ))
    (f : C(S, ℝ)) (hf : T f = f) (n : ℕ) : (T ^ n) f = f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, hf]

omit [MeasurableSpace S] [BorelSpace S] in
/-- Strong positivity of a power and a strictly positive fixed point imply
geometric simplicity, by a maximum-ratio argument. -/
theorem fixed_eq_smul_of_positive (T : C(S, ℝ) →L[ℝ] C(S, ℝ))
    (hT : ∃ n : ℕ, ∀ f : C(S, ℝ), (∀ y, 0 ≤ f y) → f ≠ 0 →
      ∀ x, 0 < (T ^ n.succ) f x)
    (u : C(S, ℝ)) (hu : ∀ x, 0 < u x) (hTu : T u = u)
    (f : C(S, ℝ)) (hTf : T f = f) : ∃ c : ℝ, f = c • u := by
  by_cases hS : Nonempty S
  · let _ : Nonempty S := hS
    have hcont : Continuous (fun x => f x / u x) :=
      f.continuous.div u.continuous (fun x => (hu x).ne')
    obtain ⟨x₀, -, hmax⟩ := isCompact_univ.exists_isMaxOn
      Set.univ_nonempty hcont.continuousOn
    let c := f x₀ / u x₀
    let h : C(S, ℝ) := c • u - f
    have hh : ∀ x, 0 ≤ h x := by
      intro x
      change 0 ≤ c * u x - f x
      have hratio : f x / u x ≤ c := hmax (Set.mem_univ x)
      exact sub_nonneg.mpr ((div_le_iff₀ (hu x)).mp hratio)
    have hhzero : h x₀ = 0 := by
      change f x₀ / u x₀ * u x₀ - f x₀ = 0
      rw [div_mul_cancel₀ _ (hu x₀).ne', sub_self]
    have hTh : T h = h := by
      dsimp [h]
      rw [map_sub, map_smul, hTu, hTf]
    have heq : h = 0 := by
      by_contra hne
      obtain ⟨n, hn⟩ := hT
      have hpos := hn h hh hne x₀
      rw [pow_apply_of_fixed T h hTh, hhzero] at hpos
      exact lt_irrefl _ hpos
    refine ⟨c, ?_⟩
    have := sub_eq_zero.mp heq
    exact this.symm
  · have _ : IsEmpty S := not_nonempty_iff.mp hS
    exact ⟨0, Subsingleton.elim _ _⟩

theorem toLp_norm_sq (mu : Measure S) [IsFiniteMeasure mu]
    (f : C(S, ℝ)) :
    ‖ContinuousMap.toLp 2 mu ℝ f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq, ContinuousMap.inner_toLp]
  simp only [conj_trivial, pow_two]

/-- Nonnegative continuous functions have strictly monotone `L²` norm
under full support. -/
theorem eq_of_nonneg_le_of_toLp_norm_le (mu : Measure S)
    [IsFiniteMeasure mu] [mu.IsOpenPosMeasure]
    (f g : C(S, ℝ)) (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x)
    (hnorm : ‖ContinuousMap.toLp 2 mu ℝ g‖ ≤ ‖ContinuousMap.toLp 2 mu ℝ f‖) :
    f = g := by
  have hfi : Integrable (fun x => (f x) ^ 2) mu :=
    (f.continuous.pow 2).integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hgi : Integrable (fun x => (g x) ^ 2) mu :=
    (g.continuous.pow 2).integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hsq : ∀ x, (f x) ^ 2 ≤ (g x) ^ 2 := by
    intro x
    exact sq_le_sq₀ (hf x) ((hf x).trans (hfg x)) |>.mpr (hfg x)
  have hnormsq := (sq_le_sq₀ (norm_nonneg (ContinuousMap.toLp 2 mu ℝ g))
    (norm_nonneg (ContinuousMap.toLp 2 mu ℝ f))).mpr hnorm
  rw [toLp_norm_sq, toLp_norm_sq] at hnormsq
  have heq : (∫ x, (f x) ^ 2 ∂mu) = ∫ x, (g x) ^ 2 ∂mu :=
    le_antisymm (integral_mono hfi hgi hsq) hnormsq
  have hae := (integral_eq_iff_of_ae_le hfi hgi
    (Filter.Eventually.of_forall hsq)).mp heq
  have hpoint := MeasureTheory.Measure.eq_of_ae_eq hae
    (f.continuous.pow 2) (g.continuous.pow 2)
  ext x
  exact (sq_eq_sq₀ (hf x) ((hf x).trans (hfg x))).mp (congrFun hpoint x)

theorem fixed_of_nonneg_subfixed (M : CompactBJRModel S) (B : M.B1Witness)
    (u : C(S, ℝ)) (hu : ∀ x, 0 ≤ u x)
    (hsub : ∀ x, u x ≤ M.kernel.action M.mu u x) :
    M.kernel.action M.mu u = u := by
  apply Eq.symm
  apply eq_of_nonneg_le_of_toLp_norm_le M.mu u _ hu hsub
  rw [← B.associated.intertwines M B.operator u]
  have h := B.operator.le_opNorm (ContinuousMap.toLp 2 M.mu ℝ u)
  simpa only [B.norm_eq_one, one_mul] using h

theorem fixed_abs_of_abs_action_eq (M : CompactBJRModel S) (B : M.B1Witness)
    (f : C(S, ℝ)) (hf : ∀ x, |M.kernel.action M.mu f x| = |f x|) :
    M.kernel.action M.mu (absMap f) = absMap f := by
  apply fixed_of_nonneg_subfixed M B (absMap f)
  · exact fun x => abs_nonneg (f x)
  · intro x
    rw [absMap_apply, ← hf x]
    exact abs_action_le M.kernel M.mu f x

theorem positive_abs_of_abs_action_eq (M : CompactBJRModel S) (B : M.B1Witness)
    (hB2 : M.B2) (f : C(S, ℝ)) (hfne : f ≠ 0)
    (hf : ∀ x, |M.kernel.action M.mu f x| = |f x|) :
    ∀ x, 0 < absMap f x := by
  have hfix := fixed_abs_of_abs_action_eq M B f hf
  have hne : absMap f ≠ 0 := by
    intro heq
    apply hfne
    ext x
    have h := congrArg (fun g : C(S, ℝ) => g x) heq
    simpa using h
  obtain ⟨n, hn⟩ := hB2.stronglyPositivePower M
  intro x
  have hpos := hn (absMap f) (fun x => abs_nonneg (f x)) hne x
  rw [pow_apply_of_fixed _ _ hfix] at hpos
  exact hpos

theorem positive_fixed_of_eigenvalue_abs_one (M : CompactBJRModel S)
    (B : M.B1Witness) (hB2 : M.B2) (lam : ℝ) (hlam : |lam| = 1)
    (hev : Module.End.HasEigenvalue B.operator.toLinearMap lam) :
    ∃ u : C(S, ℝ), (∀ x, 0 < u x) ∧ M.kernel.action M.mu u = u := by
  obtain ⟨v, hv, hvne⟩ := hev.exists_hasEigenvector
  have hev_eq : B.operator v = lam • v := Module.End.mem_eigenspace_iff.mp hv
  have hlamne : lam ≠ 0 := by
    intro h
    simp [h] at hlam
  let f := M.smooth v
  have hTf : M.kernel.action M.mu f = lam • f := by
    calc
      M.kernel.action M.mu f = M.smooth (ContinuousMap.toLp 2 M.mu ℝ f) :=
        (M.smooth_toLp f).symm
      _ = M.smooth (B.operator v) := by rw [B.associated.smoothing M B.operator v]
      _ = lam • f := by rw [hev_eq, M.smooth_smul]
  have hfne : f ≠ 0 := by
    intro h
    have heq := B.associated.smoothing M B.operator v
    change ContinuousMap.toLp 2 M.mu ℝ f = B.operator v at heq
    rw [h, map_zero, hev_eq] at heq
    exact hvne ((smul_eq_zero.mp heq.symm).resolve_left hlamne)
  have habs : ∀ x, |M.kernel.action M.mu f x| = |f x| := by
    intro x
    rw [hTf, ContinuousMap.smul_apply, smul_eq_mul, abs_mul, hlam, one_mul]
  exact ⟨absMap f, positive_abs_of_abs_action_eq M B hB2 f hfne habs,
    fixed_abs_of_abs_action_eq M B f habs⟩

/-- The positive Perron fixed point follows from the original `(B1)` and
`(B2)`; neither an eigenvector nor an eigenvalue is postulated. -/
theorem exists_positive_fixed (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ u : C(S, ℝ), (∀ x, 0 < u x) ∧ M.kernel.action M.mu u = u := by
  obtain ⟨B⟩ := hM.b1
  rcases eigenvalue_one_or_neg_one B.operator B.isCompact B.isSymmetric B.norm_eq_one
      with hpos | hneg
  · exact positive_fixed_of_eigenvalue_abs_one M B hM.b2 1 (by norm_num) hpos
  · exact positive_fixed_of_eigenvalue_abs_one M B hM.b2 (-1) (by norm_num) hneg

/-- Normalize the positive Perron vector to have integral one. -/
theorem exists_normalized_positive_fixed (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃ u : C(S, ℝ), (∀ x, 0 < u x) ∧ M.kernel.action M.mu u = u ∧
      (∫ x, u x ∂M.mu) = 1 := by
  obtain ⟨u, hu, hTu⟩ := exists_positive_fixed M hM
  have hnonempty : (Set.univ : Set S).Nonempty :=
    nonempty_of_measure_ne_zero (μ := M.mu) (by simp)
  obtain ⟨x₀, -⟩ := hnonempty
  have hint : Integrable u M.mu :=
    u.continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hpos : 0 < ∫ x, u x ∂M.mu :=
    integral_pos_of_integrable_nonneg_nonzero u.continuous hint
      (fun x => (hu x).le) (hu x₀).ne'
  let c : ℝ := (∫ x, u x ∂M.mu)⁻¹
  refine ⟨c • u, ?_, ?_, ?_⟩
  · intro x
    exact mul_pos (inv_pos.mpr hpos) (hu x)
  · rw [M.kernel.action_smul, hTu]
  · simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
    exact inv_mul_cancel₀ hpos.ne'

/-- All continuous fixed points lie on the Perron line. -/
theorem fixed_eq_scalar_multiple (M : CompactBJRModel S) (hB2 : M.B2)
    (u : C(S, ℝ)) (hu : ∀ x, 0 < u x) (hTu : M.kernel.action M.mu u = u)
    (f : C(S, ℝ)) (hTf : M.kernel.action M.mu f = f) :
    ∃ c : ℝ, f = c • u :=
  fixed_eq_smul_of_positive (M.kernel.actionCLM M.mu)
    (hB2.stronglyPositivePower M) u hu hTu f hTf

theorem normalized_fixed_unique (M : CompactBJRModel S) (hB2 : M.B2)
    (u : C(S, ℝ)) (hu : ∀ x, 0 < u x) (hTu : M.kernel.action M.mu u = u)
    (hintu : (∫ x, u x ∂M.mu) = 1)
    (v : C(S, ℝ)) (hTv : M.kernel.action M.mu v = v)
    (hintv : (∫ x, v x ∂M.mu) = 1) : v = u := by
  obtain ⟨c, hc⟩ := fixed_eq_scalar_multiple M hB2 u hu hTu v hTv
  have hint : (∫ x, v x ∂M.mu) = c := by
    rw [hc]
    simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul, hintu, mul_one]
  have hc1 : c = 1 := hint.symm.trans hintv
  simpa [hc1] using hc

/-- The normalized positive Perron function is uniquely determined by
the original `(B1)`--`(B2)` assumptions. -/
theorem existsUnique_normalized_positive_fixed (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃! u : C(S, ℝ), (∀ x, 0 < u x) ∧ M.kernel.action M.mu u = u ∧
      (∫ x, u x ∂M.mu) = 1 := by
  obtain ⟨u, hu, hTu, hintu⟩ := exists_normalized_positive_fixed M hM
  refine ⟨u, ⟨hu, hTu, hintu⟩, ?_⟩
  intro v hv
  exact normalized_fixed_unique M hM.b2 u hu hTu hintu v hv.2.1 hv.2.2

end PerronWright
