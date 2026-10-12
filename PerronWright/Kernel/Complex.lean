import PerronWright.Kernel.Compact

/-!
# Complexification of a real continuous kernel

Analytic perturbation is carried out on `C(S, ℂ)`.  This file constructs
the complex-linear action of the real BJR kernel and proves the same norm and
compactness properties as for its real action.
-/

open MeasureTheory

noncomputable section

namespace PerronWright
namespace ContinuousKernel

variable {S : Type*} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- A real kernel regarded as a complex-valued continuous kernel. -/
def complexifiedMap (k : ContinuousKernel S) : C(S × S, ℂ) where
  toFun p := (k p.1 p.2 : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp k.continuous_uncurry

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem complexifiedMap_apply (k : ContinuousKernel S) (x y : S) :
    k.complexifiedMap (x, y) = (k x y : ℂ) :=
  rfl

/-- The continuous family of complexified columns `y ↦ (x ↦ κ(x,y))`. -/
def complexColumns (k : ContinuousKernel S) : C(S, C(S, ℂ)) :=
  (k.complexifiedMap.comp (ContinuousMap.prodSwap : C(S × S, S × S))).curry

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem complexColumns_apply (k : ContinuousKernel S) (y x : S) :
    k.complexColumns y x = (k x y : ℂ) :=
  rfl

/-- The continuous family of complexified rows `x ↦ (y ↦ κ(x,y))`. -/
def complexRows (k : ContinuousKernel S) : C(S, C(S, ℂ)) :=
  k.complexifiedMap.curry

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem complexRows_apply (k : ContinuousKernel S) (x y : S) :
    k.complexRows x y = (k x y : ℂ) :=
  rfl

/-- The `C(S, ℂ)`-valued integrand of the complexified kernel action. -/
def complexActionIntegrand (k : ContinuousKernel S) (f : C(S, ℂ)) : C(S, C(S, ℂ)) where
  toFun y := f y • k.complexColumns y
  continuous_toFun := f.continuous.smul k.complexColumns.continuous

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem complexActionIntegrand_apply (k : ContinuousKernel S)
    (f : C(S, ℂ)) (y x : S) :
    k.complexActionIntegrand f y x = (k x y : ℂ) * f y := by
  change f y * (k x y : ℂ) = (k x y : ℂ) * f y
  exact mul_comm _ _

omit [MeasurableSpace S] [BorelSpace S] in
theorem complexActionIntegrand_add (k : ContinuousKernel S) (f g : C(S, ℂ)) :
    k.complexActionIntegrand (f + g) =
      k.complexActionIntegrand f + k.complexActionIntegrand g := by
  ext y x
  simp only [complexActionIntegrand_apply, ContinuousMap.add_apply]
  ring

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
theorem complexActionIntegrand_smul (k : ContinuousKernel S) (c : ℂ) (f : C(S, ℂ)) :
    k.complexActionIntegrand (c • f) = c • k.complexActionIntegrand f := by
  ext y x
  simp only [complexActionIntegrand_apply, ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem integrable_complexActionIntegrand (k : ContinuousKernel S) (mu : Measure S)
    [IsFiniteMeasure mu] (f : C(S, ℂ)) : Integrable (k.complexActionIntegrand f) mu := by
  apply (k.complexActionIntegrand f).continuous.integrable_of_hasCompactSupport
  exact isClosed_closure.isCompact

/-- The action of a real kernel on complex-valued continuous functions. -/
def complexAction (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu]
    (f : C(S, ℂ)) : C(S, ℂ) :=
  ∫ y, k.complexActionIntegrand f y ∂mu

@[simp]
theorem complexAction_apply (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu]
    (f : C(S, ℂ)) (x : S) :
    k.complexAction mu f x = ∫ y, (k x y : ℂ) * f y ∂mu := by
  rw [complexAction, ContinuousMap.integral_apply (k.integrable_complexActionIntegrand mu f) x]
  simp only [complexActionIntegrand_apply]

theorem complexAction_add (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu]
    (f g : C(S, ℂ)) :
    k.complexAction mu (f + g) = k.complexAction mu f + k.complexAction mu g := by
  unfold complexAction
  rw [complexActionIntegrand_add]
  change (∫ y, k.complexActionIntegrand f y + k.complexActionIntegrand g y ∂mu) =
    (∫ y, k.complexActionIntegrand f y ∂mu) +
      ∫ y, k.complexActionIntegrand g y ∂mu
  exact integral_add (k.integrable_complexActionIntegrand mu f)
    (k.integrable_complexActionIntegrand mu g)

omit [BorelSpace S] in
theorem complexAction_smul (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu]
    (c : ℂ) (f : C(S, ℂ)) :
    k.complexAction mu (c • f) = c • k.complexAction mu f := by
  unfold complexAction
  rw [complexActionIntegrand_smul]
  change (∫ y, c • k.complexActionIntegrand f y ∂mu) =
    c • ∫ y, k.complexActionIntegrand f y ∂mu
  exact integral_smul (𝕜 := ℂ) c (fun y ↦ k.complexActionIntegrand f y)

/-- The complex-linear integral operator on `C(S, ℂ)` associated with a real kernel. -/
def complexActionLinearMap (k : ContinuousKernel S) (mu : Measure S) [IsFiniteMeasure mu] :
    C(S, ℂ) →ₗ[ℂ] C(S, ℂ) where
  toFun := k.complexAction mu
  map_add' := k.complexAction_add mu
  map_smul' := k.complexAction_smul mu

omit [MeasurableSpace S] [BorelSpace S] in
theorem norm_complexColumns_le (k : ContinuousKernel S) (y : S) :
    ‖k.complexColumns y‖ ≤ ‖k.toContinuousMap‖ := by
  apply (ContinuousMap.norm_le (k.complexColumns y) (norm_nonneg _)).2
  intro x
  simpa only [complexColumns_apply, Complex.norm_real] using
    k.toContinuousMap.norm_coe_le_norm (x, y)

omit [MeasurableSpace S] [BorelSpace S] in
theorem norm_complexActionIntegrand_le (k : ContinuousKernel S) (f : C(S, ℂ)) (y : S) :
    ‖k.complexActionIntegrand f y‖ ≤ ‖k.toContinuousMap‖ * ‖f‖ := by
  change ‖f y • k.complexColumns y‖ ≤ ‖k.toContinuousMap‖ * ‖f‖
  rw [norm_smul]
  calc
    ‖f y‖ * ‖k.complexColumns y‖ ≤ ‖f‖ * ‖k.toContinuousMap‖ := by
      gcongr
      · exact f.norm_coe_le_norm y
      · exact k.norm_complexColumns_le y
    _ = ‖k.toContinuousMap‖ * ‖f‖ := mul_comm _ _

omit [BorelSpace S] in
theorem norm_complexAction_le (k : ContinuousKernel S) (mu : Measure S)
    [IsProbabilityMeasure mu] (f : C(S, ℂ)) :
    ‖k.complexAction mu f‖ ≤ ‖k.toContinuousMap‖ * ‖f‖ := by
  unfold complexAction
  calc
    ‖∫ y, k.complexActionIntegrand f y ∂mu‖
        ≤ (‖k.toContinuousMap‖ * ‖f‖) * mu.real Set.univ :=
      norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall (fun y ↦ k.norm_complexActionIntegrand_le f y))
    _ = ‖k.toContinuousMap‖ * ‖f‖ := by simp

/-- The complexified integral operator on `C(S, ℂ)`. -/
def complexActionCLM (k : ContinuousKernel S) (mu : Measure S) [IsProbabilityMeasure mu] :
    C(S, ℂ) →L[ℂ] C(S, ℂ) :=
  (k.complexActionLinearMap mu).mkContinuous ‖k.toContinuousMap‖
    (k.norm_complexAction_le mu)

@[simp]
theorem complexActionCLM_apply (k : ContinuousKernel S) (mu : Measure S)
    [IsProbabilityMeasure mu] (f : C(S, ℂ)) :
    k.complexActionCLM mu f = k.complexAction mu f :=
  rfl

theorem norm_complexActionCLM_le (k : ContinuousKernel S) (mu : Measure S)
    [IsProbabilityMeasure mu] : ‖k.complexActionCLM mu‖ ≤ ‖k.toContinuousMap‖ := by
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) (k.norm_complexAction_le mu)

theorem dist_complexAction_apply_le (k : ContinuousKernel S) (mu : Measure S)
    [IsProbabilityMeasure mu] (f : C(S, ℂ)) (x x' : S) :
    dist (k.complexAction mu f x) (k.complexAction mu f x') ≤
      ‖k.complexRows x - k.complexRows x'‖ * ‖f‖ := by
  rw [dist_eq_norm, complexAction_apply, complexAction_apply, ← integral_sub]
  · calc
      ‖∫ y, (k x y : ℂ) * f y - (k x' y : ℂ) * f y ∂mu‖
          ≤ (‖k.complexRows x - k.complexRows x'‖ * ‖f‖) * mu.real Set.univ := by
        apply norm_integral_le_of_norm_le_const
        filter_upwards [] with y
        rw [← sub_mul, norm_mul]
        gcongr
        · exact (k.complexRows x - k.complexRows x').norm_coe_le_norm y
        · exact f.norm_coe_le_norm y
      _ = ‖k.complexRows x - k.complexRows x'‖ * ‖f‖ := by simp
  · exact ((Complex.continuous_ofReal.comp (k.continuous_left x)).mul f.continuous)
      |>.integrable_of_hasCompactSupport isClosed_closure.isCompact
  · exact ((Complex.continuous_ofReal.comp (k.continuous_left x')).mul f.continuous)
      |>.integrable_of_hasCompactSupport isClosed_closure.isCompact

/-- The complexified action of a continuous kernel is compact on `C(S, ℂ)`. -/
theorem isCompactOperator_complexActionCLM [MetricSpace S]
    (k : ContinuousKernel S) (mu : Measure S) [IsProbabilityMeasure mu] :
    IsCompactOperator (k.complexActionCLM mu) := by
  let e := ContinuousMap.linearIsometryBoundedOfCompact S ℂ ℂ
  let A : Set (BoundedContinuousFunction S ℂ) :=
    e '' ((k.complexActionCLM mu) '' Metric.closedBall 0 1)
  have hA_range : ∀ (g : BoundedContinuousFunction S ℂ) (x : S), g ∈ A →
      g x ∈ Metric.closedBall (0 : ℂ) ‖k.toContinuousMap‖ := by
    rintro g x ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖k.complexAction mu f x‖ ≤ ‖k.toContinuousMap‖
    exact le_trans (ContinuousMap.norm_coe_le_norm (k.complexAction mu f) x)
      (le_trans (k.norm_complexAction_le mu f) (mul_le_of_le_one_right (norm_nonneg _)
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hf)))
  have hA_equicont : Equicontinuous ((↑) : A → S → ℂ) := by
    intro x₀
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [k.complexRows.continuous.continuousAt.eventually
      (Metric.ball_mem_nhds _ hε)] with x hx g
    rw [dist_comm] at hx
    rcases g.property with ⟨_, ⟨f, hf, rfl⟩, hg⟩
    rw [← hg, ContinuousMap.linearIsometryBoundedOfCompact_apply_apply,
      ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]
    refine lt_of_le_of_lt (k.dist_complexAction_apply_le mu f x₀ x) ?_
    calc
      ‖k.complexRows x₀ - k.complexRows x‖ * ‖f‖ ≤
          ‖k.complexRows x₀ - k.complexRows x‖ * 1 := by
        gcongr
        simpa [Metric.mem_closedBall, dist_zero_right] using hf
      _ = dist (k.complexRows x₀) (k.complexRows x) := by rw [mul_one, dist_eq_norm]
      _ < ε := hx
  have hcompactA : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli
      (Metric.closedBall (0 : ℂ) ‖k.toContinuousMap‖)
      (isCompact_closedBall _ _) A hA_range hA_equicont
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ zero_lt_one,
    e.symm '' closure A, hcompactA.image e.symm.continuous, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  refine ⟨e (k.complexActionCLM mu f),
    subset_closure ⟨k.complexActionCLM mu f, ⟨f, hf, rfl⟩, rfl⟩, ?_⟩
  simp [e]

end ContinuousKernel
end PerronWright

