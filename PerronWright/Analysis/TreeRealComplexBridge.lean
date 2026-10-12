import PerronWright.Analysis.TreeContraction
import PerronWright.Analysis.TreeCritical

/-!
# Real/complex bridge for the normalized zero-field tree equation

The real monotone-iteration map is the real slice of the analytic tree
residual. Consequently, the least real fixed point agrees near `w = 0` with
the local analytic zero-tree branch. This is a local identification only; it
does not identify the full tree power series or its convergence radius.
-/

open MeasureTheory

noncomputable section

namespace PerronWright.TreeRealComplexBridge

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Pointwise complexification of a real continuous function. -/
def complexify (V : C(S, ℝ)) : C(S, ℂ) :=
  ⟨fun x => (V x : ℂ), Complex.continuous_ofReal.comp V.continuous⟩

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem complexify_apply (V : C(S, ℝ)) (x : S) :
    complexify V x = (V x : ℂ) := rfl

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem complexify_sub (V W : C(S, ℝ)) :
    complexify (V - W) = complexify V - complexify W := by
  ext x
  simp [complexify_apply]

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem complexify_one :
    complexify (1 : C(S, ℝ)) = (1 : C(S, ℂ)) := by
  ext x
  simp [complexify_apply]

theorem complexify_action (M : CompactBJRModel S) (V : C(S, ℝ)) :
    complexify (M.kernel.action M.mu V) =
      M.kernel.complexActionCLM M.mu (complexify V) := by
  ext x
  rw [complexify_apply, ContinuousKernel.action_apply,
    ContinuousKernel.complexActionCLM_apply, ContinuousKernel.complexAction_apply]
  rw [← integral_complex_ofReal]
  congr 1
  funext y
  exact Complex.ofReal_mul _ _

omit [MeasurableSpace S] [BorelSpace S] in
private theorem exp_apply (f : C(S, ℂ)) (x : S) :
    NormedSpace.exp f x = Complex.exp (f x) := by
  simpa only [ContinuousMap.evalAlgHom_apply, ← Complex.exp_eq_exp_ℂ] using
    NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ x)
      (ContinuousMap.evalCLM ℂ x).continuous f

/-- The real normalized zero-field tree map is the zero-field complex analytic
equation, restricted to real parameters and real functions. -/
theorem normalizedZeroTreeMap_complex_eq
    (M : CompactBJRModel S) (w : ℝ) (V : C(S, ℝ)) :
    complexify (M.normalizedZeroTreeMap w V) =
      (w : ℂ) • NormedSpace.exp
        (-TreeCritical.degree M +
          M.kernel.complexActionCLM M.mu (complexify V)) := by
  ext x
  rw [complexify_apply, M.normalizedZeroTreeMap_apply]
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  rw [exp_apply]
  rw [← complexify_action M V]
  simp only [ContinuousMap.add_apply, ContinuousMap.neg_apply,
    complexify_apply, Complex.ofReal_mul]
  rw [TreeCritical.degree_apply]
  have hdegree : M.kernel.degree M.mu x = M.kernel.action M.mu (1 : C(S, ℝ)) x := by
    rw [ContinuousKernel.action_apply]
    change (∫ y, M.kernel x y ∂M.mu) =
      ∫ y, M.kernel x y * (1 : C(S, ℝ)) y ∂M.mu
    simp only [ContinuousMap.one_apply, mul_one]
  rw [hdegree]
  have hK : -(M.kernel.action M.mu (1 : C(S, ℝ)) x) +
      M.kernel.action M.mu V x = M.kernel.action M.mu (V - 1) x := by
    rw [M.kernel.realAction_sub M.mu]
    simp only [ContinuousMap.sub_apply]
    ring
  rw [← Complex.ofReal_neg, ← Complex.ofReal_add, hK, Complex.ofReal_exp]

theorem normalizedZeroTreeMap_residual_eq
    (M : CompactBJRModel S) (w : ℝ) (V : C(S, ℝ)) :
    TreeCritical.residual M (((w : ℂ), 0), complexify V) =
      complexify (V - M.normalizedZeroTreeMap w V) := by
  unfold TreeCritical.residual TreeAnalytic.residual
  simp only [zero_sub]
  rw [← normalizedZeroTreeMap_complex_eq M w V]
  simp [complexify_sub]

theorem normalizedZeroTreeMap_fixed_iff_residual_zero
    (M : CompactBJRModel S) (w : ℝ) (V : C(S, ℝ)) :
    M.normalizedZeroTreeMap w V = V ↔
      TreeCritical.residual M (((w : ℂ), 0), complexify V) = 0 := by
  rw [normalizedZeroTreeMap_residual_eq]
  constructor
  · intro h
    have hz : V - M.normalizedZeroTreeMap w V = 0 := sub_eq_zero.mpr h.symm
    rw [hz]
    ext x
    simp [complexify_apply]
  · intro h
    apply ContinuousMap.ext
    intro x
    have hx := congrArg (fun f : C(S, ℂ) => f x) h
    simp only [complexify_apply, ContinuousMap.zero_apply,
      ContinuousMap.sub_apply, Complex.ofReal_eq_zero] at hx
    exact (sub_eq_zero.mp hx).symm

/-- For sufficiently small nonnegative real parameters, the analytic zero-tree
branch is the complexification of the actual least fixed point obtained by
monotone iteration. -/
theorem least_fixed_agrees_with_zero_tree_branch
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ ψ : ℂ × C(S, ℂ) → C(S, ℂ),
      AnalyticAt ℂ ψ (0, 0) ∧ ψ (0, 0) = 0 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℝ, 0 ≤ w → w < ε →
        ∃ V : C(S, ℝ),
          Filter.Tendsto (M.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
          M.normalizedZeroTreeMap w V = V ∧
          (∀ W : C(S, ℝ), (∀ x, 0 ≤ W x) →
            M.normalizedZeroTreeMap w W = W → ∀ x, V x ≤ W x) ∧
          ψ ((w : ℂ), 0) = complexify V := by
  obtain ⟨ψ, hψanalytic, hψzero, -, hlocal⟩ :=
    TreeAnalytic.zero_tree_branch M.kernel M.mu (TreeCritical.degree M)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨ψ, hψanalytic, hψzero, min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro w hw hwε
  have hw1 : w < 1 := hwε.trans_le (min_le_right _ _)
  obtain ⟨V, hVlim, hVbounds, hVfix, hVleast⟩ :=
    M.normalizedZeroTreeIter_least_fixed hM w hw hw1
  refine ⟨V, hVlim, hVfix, hVleast, ?_⟩
  have hVw (x : S) : V x ≤ w := by
    rw [← hVfix]
    exact M.normalizedZeroTreeMap_le_w w hw V (fun y => (hVbounds y).2) x
  have hVnorm : ‖complexify V‖ ≤ w := by
    apply (ContinuousMap.norm_le _ hw).2
    intro x
    simpa only [complexify_apply, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hVbounds x).1] using hVw x
  have hpNorm : ‖((((w : ℂ), (0 : C(S, ℂ))), complexify V))‖ ≤ w := by
    simp only [Prod.norm_mk, norm_zero]
    apply max_le
    · apply max_le
      · simpa only [Complex.norm_real, Real.norm_eq_abs,
          (abs_of_nonneg hw)] using (le_refl w)
      · exact hw
    · exact hVnorm
  have hpball : (((w : ℂ), (0 : C(S, ℂ))), complexify V) ∈
      Metric.ball (((0 : ℂ), (0 : C(S, ℂ))), (0 : C(S, ℂ))) δ := by
    simpa [dist_eq_norm] using
      hpNorm.trans_lt (hwε.trans_le (min_le_left _ _))
  have hres : TreeCritical.residual M (((w : ℂ), 0), complexify V) = 0 :=
    (normalizedZeroTreeMap_fixed_iff_residual_zero M w V).mp hVfix
  exact (hball hpball).mp hres

end PerronWright.TreeRealComplexBridge
