import PerronWright.Analysis.TreePhysicalBranch

open MeasureTheory
noncomputable section

namespace PerronWright.TreeOuterNeumann

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Complex kernel action preserves Perron-function pointwise domination. -/
theorem complexAction_perron_dominated (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (c : ℝ)
    (f : C(S, ℂ))
    (hf : ∀ y, ‖f y‖ ≤ c * M.perronFunction hM y) (x : S) :
    ‖M.kernel.complexActionCLM M.mu f x‖ ≤ c * M.perronFunction hM x := by
  let g : S → ℝ := fun y => c * (M.kernel x y * M.perronFunction hM y)
  have hg : Integrable g M.mu := by
    apply (continuous_const.mul
      ((M.kernel.rows x).continuous.mul (M.perronFunction hM).continuous)).integrable_of_hasCompactSupport
    exact isClosed_closure.isCompact
  have hdom : ∀ y, ‖(M.kernel x y : ℂ) * f y‖ ≤ g y := by
    intro y
    have hκ := M.kernel.nonneg x y
    calc
      ‖(M.kernel x y : ℂ) * f y‖ = M.kernel x y * ‖f y‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
      _ ≤ M.kernel x y * (c * M.perronFunction hM y) :=
        mul_le_mul_of_nonneg_left (hf y) hκ
      _ = g y := by change _ = c * (M.kernel x y * M.perronFunction hM y); ring
  rw [ContinuousKernel.complexActionCLM_apply,
    ContinuousKernel.complexAction_apply]
  calc
    ‖∫ y, (M.kernel x y : ℂ) * f y ∂M.mu‖ ≤ ∫ y, g y ∂M.mu :=
      norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hdom)
    _ = c * M.perronFunction hM x := by
      rw [show (∫ y, g y ∂M.mu) =
          c * ∫ y, M.kernel x y * M.perronFunction hM y ∂M.mu by
        change (∫ y, c * (M.kernel x y * M.perronFunction hM y) ∂M.mu) = _
        exact integral_const_mul c _]
      have h := congrArg (fun U : C(S, ℝ) => U x) (M.perronFunction_fixed hM)
      simpa only [ContinuousKernel.action_apply] using congrArg (c * ·) h

/-- Multiplication by a complex profile after the complex kernel action. -/
def weightedComplexAction (M : CompactBJRModel S) (a : C(S, ℂ)) :
    C(S, ℂ) →L[ℂ] C(S, ℂ) :=
  (((ContinuousLinearMap.mulLeftRight ℂ (C(S, ℂ))) a) 1).comp
    (M.kernel.complexActionCLM M.mu)

theorem weightedComplexAction_apply (M : CompactBJRModel S)
    (a f : C(S, ℂ)) :
    weightedComplexAction M a f = a * M.kernel.complexActionCLM M.mu f := by
  simp [weightedComplexAction, ContinuousLinearMap.mulLeftRight_apply]

/-- A profile bounded by `q` contracts the Perron-weighted pointwise cone by `q`. -/
theorem weightedComplexAction_perron_dominated (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (a f : C(S, ℂ)) (q c : ℝ)
    (hq : 0 ≤ q) (ha : ∀ x, ‖a x‖ ≤ q)
    (hf : ∀ y, ‖f y‖ ≤ c * M.perronFunction hM y) (x : S) :
    ‖weightedComplexAction M a f x‖ ≤ (q * c) * M.perronFunction hM x := by
  rw [weightedComplexAction_apply, ContinuousMap.mul_apply, norm_mul]
  calc
    ‖a x‖ * ‖M.kernel.complexActionCLM M.mu f x‖ ≤
        q * ‖M.kernel.complexActionCLM M.mu f x‖ :=
      mul_le_mul_of_nonneg_right (ha x) (norm_nonneg _)
    _ ≤ q * (c * M.perronFunction hM x) :=
      mul_le_mul_of_nonneg_left (complexAction_perron_dominated M hM c f hf x) hq
    _ = (q * c) * M.perronFunction hM x := by ring

/-- Every iterate of the weighted action has a geometric Perron-weighted bound. -/
theorem weightedComplexAction_pow_perron_dominated (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (a f : C(S, ℂ)) (q c : ℝ)
    (hq : 0 ≤ q) (ha : ∀ x, ‖a x‖ ≤ q)
    (hf : ∀ y, ‖f y‖ ≤ c * M.perronFunction hM y) (n : ℕ) (x : S) :
    ‖((weightedComplexAction M a) ^ n) f x‖ ≤
      (q ^ n * c) * M.perronFunction hM x := by
  induction n generalizing x with
  | zero => simpa using hf x
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    have h := weightedComplexAction_perron_dominated M hM a
      (((weightedComplexAction M a) ^ n) f) q (q ^ n * c) hq ha ih x
    convert h using 1; ring

/-- The Perron gauge turns the pointwise bound into an operator-power bound. -/
theorem weightedComplexAction_pow_norm_le (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (a : C(S, ℂ)) (q m : ℝ)
    (hq : 0 ≤ q) (ha : ∀ x, ‖a x‖ ≤ q)
    (hm : 0 < m) (hmu : ∀ x, m ≤ M.perronFunction hM x)
    (n : ℕ) :
    ‖(weightedComplexAction M a) ^ n‖ ≤
      q ^ n * (‖M.perronFunction hM‖ / m) := by
  have hcoef : 0 ≤ q ^ n * (‖M.perronFunction hM‖ / m) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hcoef
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hcoef (norm_nonneg f))).2
  intro x
  have hf (y : S) : ‖f y‖ ≤ (‖f‖ / m) * M.perronFunction hM y := by
    calc
      ‖f y‖ ≤ ‖f‖ := f.norm_coe_le_norm y
      _ = (‖f‖ / m) * m := by field_simp
      _ ≤ (‖f‖ / m) * M.perronFunction hM y :=
        mul_le_mul_of_nonneg_left (hmu y) (div_nonneg (norm_nonneg _) hm.le)
  have hu : M.perronFunction hM x ≤ ‖M.perronFunction hM‖ := by
    simpa only [Real.norm_eq_abs, abs_of_pos (M.perronFunction_pos hM x)] using
      (M.perronFunction hM).norm_coe_le_norm x
  have hp := weightedComplexAction_pow_perron_dominated
    M hM a f q (‖f‖ / m) hq ha hf n x
  calc
    ‖(((weightedComplexAction M a) ^ n) f) x‖ ≤
        (q ^ n * (‖f‖ / m)) * M.perronFunction hM x := hp
    _ ≤ (q ^ n * (‖f‖ / m)) * ‖M.perronFunction hM‖ :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = (q ^ n * (‖M.perronFunction hM‖ / m)) * ‖f‖ := by ring

/-- The weighted operator has a norm-convergent Neumann series when `q < 1`. -/
theorem weightedComplexAction_pow_summable (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (a : C(S, ℂ)) (q m : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (ha : ∀ x, ‖a x‖ ≤ q)
    (hm : 0 < m) (hmu : ∀ x, m ≤ M.perronFunction hM x) :
    Summable (fun n : ℕ => (weightedComplexAction M a) ^ n) := by
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hq hq1
  have hbound : Summable (fun n : ℕ =>
      q ^ n * (‖M.perronFunction hM‖ / m)) := by
    simpa only [mul_comm] using hgeom.mul_left (‖M.perronFunction hM‖ / m)
  apply Summable.of_norm_bounded hbound
  intro n
  exact weightedComplexAction_pow_norm_le M hM a q m hq ha hm hmu n

/-- Subcritical weighted kernel actions have actual two-sided inverses. -/
theorem weightedComplexAction_one_sub_isUnit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (a : C(S, ℂ)) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (ha : ∀ x, ‖a x‖ ≤ q) :
    IsUnit (1 - weightedComplexAction M a) := by
  obtain ⟨m, hm, hmu⟩ := M.perronFunction_uniform_pos hM
  have hs := weightedComplexAction_pow_summable M hM a q m hq hq1 ha hm hmu
  refine ⟨⟨1 - weightedComplexAction M a,
    ∑' n : ℕ, (weightedComplexAction M a) ^ n, ?_, ?_⟩, rfl⟩
  · exact hs.one_sub_mul_tsum_pow
  · exact hs.tsum_pow_mul_one_sub

/-- At a real subcritical physical solution the actual implicit derivative is invertible. -/
theorem physicalTree_subcritical_partial_isUnit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1)
    (V : C(S, ℝ)) (hV : ∀ x, 0 ≤ V x ∧ V x ≤ 1)
    (hfix : M.normalizedZeroTreeMap w V = V) :
    IsUnit (fderiv ℂ (TreeCritical.residual M)
      (((w : ℂ), 0), TreeRealComplexBridge.complexify V) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ)) := by
  let U := TreeRealComplexBridge.complexify V
  let K := M.kernel.complexActionCLM M.mu
  have hres : TreeCritical.residual M (((w : ℂ), 0), U) = 0 :=
    (TreeRealComplexBridge.normalizedZeroTreeMap_fixed_iff_residual_zero M w V).mp hfix
  have htree : U = (w : ℂ) • NormedSpace.exp
      (-(TreeCritical.degree M) + K U) := by
    have hres' : U - (w : ℂ) • NormedSpace.exp
        (-(TreeCritical.degree M) + K U) = 0 := by
      simpa only [TreeCritical.residual, TreeAnalytic.residual, zero_sub] using hres
    exact sub_eq_zero.mp hres'
  have hlin : (w : ℂ) •
      (NormedSpace.exp (-(TreeCritical.degree M) + K U) • K) =
      weightedComplexAction M U := by
    ext f x
    simp only [smul_apply, ContinuousMap.smul_apply,
      smul_eq_mul, weightedComplexAction_apply, ContinuousMap.mul_apply]
    have hpt := congrArg (fun F : C(S, ℂ) => F x) htree
    simp only [ContinuousMap.smul_apply, smul_eq_mul] at hpt
    rw [hpt]
    ring
  have hpartial : fderiv ℂ (TreeCritical.residual M) (((w : ℂ), 0), U) ∘L
      ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ) =
      1 - weightedComplexAction M U := by
    change fderiv ℂ (TreeAnalytic.residual M.kernel M.mu (TreeCritical.degree M))
      (((w : ℂ), 0), U) ∘L
        ContinuousLinearMap.inr ℂ (ℂ × C(S, ℂ)) C(S, ℂ) = _
    rw [TreeAnalytic.residual_partial]
    simpa only [zero_sub, ContinuousLinearMap.one_def] using congrArg
      (fun A : C(S, ℂ) →L[ℂ] C(S, ℂ) =>
        ContinuousLinearMap.id ℂ C(S, ℂ) - A) hlin
  rw [show TreeRealComplexBridge.complexify V = U from rfl, hpartial]
  have ha (x : S) : ‖U x‖ ≤ w := by
    have hVw : V x ≤ w := by
      rw [← hfix]
      exact M.normalizedZeroTreeMap_le_w w hw V (fun y => (hV y).2) x
    simpa only [U, TreeRealComplexBridge.complexify_apply,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hV x).1] using hVw
  exact weightedComplexAction_one_sub_isUnit M hM U w hw hw1 ha

end PerronWright.TreeOuterNeumann
