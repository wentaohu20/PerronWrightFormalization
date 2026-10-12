import PerronWright.Model.CountablePerronQuantities

/-!
# A common-Hilbert-space realization for changing atomic type laws

For `h,g ∈ L²(μ)`, the operator below has the literal kernel
`h(a) κ(a,b) g(b)` on the fixed space `L²(μ)`.  In particular `h=g` is the
weighted conjugate used for approximating probability laws.  Its continuity
estimate is proved from the bounded original kernel, not assumed.
-/

open MeasureTheory

noncomputable section

namespace PerronWright.CountableKernel

theorem featureRow_memLp (M : CountableKernel) (g : M.L2) (a : ℕ) :
    MemLp (fun b ↦ M.kernel a b * g b) 2 M.mu := by
  apply (Lp.memLp g).of_le_mul (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with b
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (M.norm_kernel_le a b) (norm_nonneg _)

def featureRow (M : CountableKernel) (g : M.L2) (a : ℕ) : M.L2 :=
  (M.featureRow_memLp g a).toLp (fun b ↦ M.kernel a b * g b)

theorem featureRow_apply (M : CountableKernel) (g : M.L2) (a b : ℕ) :
    M.featureRow g a b = M.kernel a b * g b :=
  M.forall_of_ae (M.featureRow_memLp g a).coeFn_toLp b

theorem norm_featureRow_le (M : CountableKernel) (g : M.L2) (a : ℕ) :
    ‖M.featureRow g a‖ ≤ M.upper * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [] with b
  rw [M.featureRow_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (M.norm_kernel_le a b) (norm_nonneg _)

theorem featureRow_sub (M : CountableKernel) (g k : M.L2) (a : ℕ) :
    M.featureRow (g - k) a = M.featureRow g a - M.featureRow k a := by
  apply Lp.ext
  filter_upwards [] with b
  rw [M.coe_sub_at, M.featureRow_apply, M.featureRow_apply, M.featureRow_apply, M.coe_sub_at]
  ring

def featurePointwise (M : CountableKernel) (h g v : M.L2) (a : ℕ) : ℝ :=
  h a * inner ℝ (M.featureRow g a) v

theorem norm_featurePointwise_le (M : CountableKernel) (h g v : M.L2) (a : ℕ) :
    ‖M.featurePointwise h g v a‖ ≤ (M.upper * ‖g‖ * ‖v‖) * ‖h a‖ := by
  rw [featurePointwise, norm_mul]
  calc
    ‖h a‖ * ‖inner ℝ (M.featureRow g a) v‖ ≤ ‖h a‖ * (‖M.featureRow g a‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℝ) _ _) (norm_nonneg _)
    _ ≤ ‖h a‖ * ((M.upper * ‖g‖) * ‖v‖) := by
      gcongr
      exact M.norm_featureRow_le g a
    _ = (M.upper * ‖g‖ * ‖v‖) * ‖h a‖ := by ring

theorem featurePointwise_memLp (M : CountableKernel) (h g v : M.L2) :
    MemLp (M.featurePointwise h g v) 2 M.mu :=
  (Lp.memLp h).of_le_mul (measurable_of_countable _).aestronglyMeasurable
    (Filter.Eventually.of_forall (M.norm_featurePointwise_le h g v))

def featureAction (M : CountableKernel) (h g v : M.L2) : M.L2 :=
  (M.featurePointwise_memLp h g v).toLp (M.featurePointwise h g v)

theorem featureAction_apply (M : CountableKernel) (h g v : M.L2) (a : ℕ) :
    M.featureAction h g v a = M.featurePointwise h g v a :=
  M.forall_of_ae (M.featurePointwise_memLp h g v).coeFn_toLp a

theorem featureAction_add (M : CountableKernel) (h g v w : M.L2) :
    M.featureAction h g (v + w) = M.featureAction h g v + M.featureAction h g w := by
  apply Lp.ext
  filter_upwards [] with a
  rw [M.coe_add_at, M.featureAction_apply, M.featureAction_apply, M.featureAction_apply]
  simp only [featurePointwise, inner_add_right, mul_add]

theorem featureAction_smul (M : CountableKernel) (h g v : M.L2) (c : ℝ) :
    M.featureAction h g (c • v) = c • M.featureAction h g v := by
  apply Lp.ext
  filter_upwards [] with a
  rw [M.coe_smul_at, M.featureAction_apply, M.featureAction_apply]
  simp only [featurePointwise, inner_smul_right]
  ring

theorem norm_featureAction_le (M : CountableKernel) (h g v : M.L2) :
    ‖M.featureAction h g v‖ ≤ (M.upper * ‖h‖ * ‖g‖) * ‖v‖ := by
  have hb : ∀ᵐ a ∂M.mu, ‖M.featureAction h g v a‖ ≤ (M.upper * ‖g‖ * ‖v‖) * ‖h a‖ := by
    filter_upwards [] with a
    rw [M.featureAction_apply]
    exact M.norm_featurePointwise_le h g v a
  have hn := Lp.norm_le_mul_norm_of_ae_le_mul hb
  calc
    ‖M.featureAction h g v‖ ≤ (M.upper * ‖g‖ * ‖v‖) * ‖h‖ := hn
    _ = (M.upper * ‖h‖ * ‖g‖) * ‖v‖ := by ring

def featureActionCLM (M : CountableKernel) (h g : M.L2) : M.L2 →L[ℝ] M.L2 :=
  LinearMap.mkContinuous
    { toFun := M.featureAction h g
      map_add' := M.featureAction_add h g
      map_smul' := fun c v ↦ M.featureAction_smul h g v c }
    (M.upper * ‖h‖ * ‖g‖) (M.norm_featureAction_le h g)

theorem featureActionCLM_apply (M : CountableKernel) (h g v : M.L2) (a : ℕ) :
    M.featureActionCLM h g v a = h a * inner ℝ (M.featureRow g a) v :=
  M.featureAction_apply h g v a

theorem norm_featureActionCLM_le (M : CountableKernel) (h g : M.L2) :
    ‖M.featureActionCLM h g‖ ≤ M.upper * ‖h‖ * ‖g‖ :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg (mul_nonneg M.upper_nonneg (norm_nonneg _)) (norm_nonneg _))
    (M.norm_featureAction_le h g)

def weightedActionCLM (M : CountableKernel) (h : M.L2) : M.L2 →L[ℝ] M.L2 :=
  M.featureActionCLM h h

theorem weightedActionCLM_sub (M : CountableKernel) (h g : M.L2) :
    M.weightedActionCLM h - M.weightedActionCLM g =
      M.featureActionCLM (h - g) h + M.featureActionCLM g (h - g) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [] with a
  simp only [sub_apply, add_apply]
  rw [M.coe_sub_at, M.coe_add_at]
  simp only [weightedActionCLM, M.featureActionCLM_apply, M.coe_sub_at, M.featureRow_sub,
    inner_sub_left]
  ring

/-- The actual shared-space weighted operators are norm continuous in their
`L²` density features. -/
theorem norm_weightedActionCLM_sub_le (M : CountableKernel) (h g : M.L2) :
    ‖M.weightedActionCLM h - M.weightedActionCLM g‖ ≤
      M.upper * (‖h‖ + ‖g‖) * ‖h - g‖ := by
  rw [M.weightedActionCLM_sub]
  calc
    ‖M.featureActionCLM (h - g) h + M.featureActionCLM g (h - g)‖ ≤
        ‖M.featureActionCLM (h - g) h‖ + ‖M.featureActionCLM g (h - g)‖ := norm_add_le _ _
    _ ≤ M.upper * ‖h - g‖ * ‖h‖ + M.upper * ‖g‖ * ‖h - g‖ :=
      add_le_add (M.norm_featureActionCLM_le _ _) (M.norm_featureActionCLM_le _ _)
    _ = M.upper * (‖h‖ + ‖g‖) * ‖h - g‖ := by ring

theorem weightedActionCLM_tendsto (M : CountableKernel) (h : ℕ → M.L2) (g : M.L2)
    (ht : Filter.Tendsto h Filter.atTop (nhds g)) :
    Filter.Tendsto (fun n ↦ M.weightedActionCLM (h n)) Filter.atTop
      (nhds (M.weightedActionCLM g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hn := (continuous_norm.tendsto g).comp ht
  have hd : Filter.Tendsto (fun n ↦ ‖h n - g‖) Filter.atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp ht
  have hb := ((hn.add_const ‖g‖).const_mul M.upper).mul hd
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ M.norm_weightedActionCLM_sub_le (h n) g)
  simpa using hb

end PerronWright.CountableKernel
