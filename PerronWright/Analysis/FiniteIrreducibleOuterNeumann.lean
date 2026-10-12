import PerronWright.Analysis.FiniteIrreducibleComplex
import PerronWright.Analysis.TreeOuterNeumann

/-! Actual Perron-gauge Neumann inverse for finite irreducible kernels.
The argument permits negative unit eigenvalues of the unweighted kernel. -/
open scoped BigOperators
noncomputable section
namespace PerronWright.FiniteIrreducibleOuterNeumann
variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The literal finite nonnegative matrix preserves Perron domination. -/
theorem complexAction_perron_dominated (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (c : ℝ) (f : C(S, ℂ))
    (hf : ∀ y, ‖f y‖ ≤ c * M.continuousPerronFunction hM y) (x : S) :
    ‖M.complexOperator f x‖ ≤ c * M.continuousPerronFunction hM x := by
  rw [M.complexOperator_apply]
  calc
    ‖∑ y, (M.kernel x y * M.weight y : ℝ) * f y‖ ≤
        ∑ y, ‖(M.kernel x y * M.weight y : ℝ) * f y‖ := norm_sum_le _ _
    _ ≤ ∑ y, M.kernel x y * M.weight y * (c * M.perronFunction hM y) := by
      apply Finset.sum_le_sum
      intro y _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (M.kernel_nonneg x y) (M.weight_pos y).le)]
      exact mul_le_mul_of_nonneg_left (hf y)
        (mul_nonneg (M.kernel_nonneg x y) (M.weight_pos y).le)
    _ = c * M.perronFunction hM x := by
      rw [← congrFun (M.perronFunction_fixed hM) x]
      simp only [FiniteIrreducibleModel.action, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = c * M.continuousPerronFunction hM x := rfl

/-- Multiplication by a complex profile after the complex kernel action. -/
def weightedComplexAction (M : FiniteIrreducibleModel S) (a : C(S, ℂ)) :
    C(S, ℂ) →L[ℂ] C(S, ℂ) :=
  (((ContinuousLinearMap.mulLeftRight ℂ (C(S, ℂ))) a) 1).comp
    (M.complexOperator)

theorem weightedComplexAction_apply (M : FiniteIrreducibleModel S)
    (a f : C(S, ℂ)) :
    weightedComplexAction M a f = a * M.complexOperator f := by
  simp [weightedComplexAction, ContinuousLinearMap.mulLeftRight_apply]

/-- A profile bounded by `q` contracts the Perron-weighted pointwise cone by `q`. -/
theorem weightedComplexAction_perron_dominated (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (a f : C(S, ℂ)) (q c : ℝ)
    (hq : 0 ≤ q) (ha : ∀ x, ‖a x‖ ≤ q)
    (hf : ∀ y, ‖f y‖ ≤ c * M.continuousPerronFunction hM y) (x : S) :
    ‖weightedComplexAction M a f x‖ ≤ (q * c) * M.continuousPerronFunction hM x := by
  rw [weightedComplexAction_apply, ContinuousMap.mul_apply, norm_mul]
  calc
    ‖a x‖ * ‖M.complexOperator f x‖ ≤
        q * ‖M.complexOperator f x‖ :=
      mul_le_mul_of_nonneg_right (ha x) (norm_nonneg _)
    _ ≤ q * (c * M.continuousPerronFunction hM x) :=
      mul_le_mul_of_nonneg_left (complexAction_perron_dominated M hM c f hf x) hq
    _ = (q * c) * M.continuousPerronFunction hM x := by ring

/-- Every iterate of the weighted action has a geometric Perron-weighted bound. -/
theorem weightedComplexAction_pow_perron_dominated (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (a f : C(S, ℂ)) (q c : ℝ)
    (hq : 0 ≤ q) (ha : ∀ x, ‖a x‖ ≤ q)
    (hf : ∀ y, ‖f y‖ ≤ c * M.continuousPerronFunction hM y) (n : ℕ) (x : S) :
    ‖((weightedComplexAction M a) ^ n) f x‖ ≤
      (q ^ n * c) * M.continuousPerronFunction hM x := by
  induction n generalizing x with
  | zero => simpa using hf x
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    have h := weightedComplexAction_perron_dominated M hM a
      (((weightedComplexAction M a) ^ n) f) q (q ^ n * c) hq ha ih x
    convert h using 1; ring

/-- The Perron gauge turns the pointwise bound into an operator-power bound. -/
theorem weightedComplexAction_pow_norm_le (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (a : C(S, ℂ)) (q m : ℝ)
    (hq : 0 ≤ q) (ha : ∀ x, ‖a x‖ ≤ q)
    (hm : 0 < m) (hmu : ∀ x, m ≤ M.continuousPerronFunction hM x)
    (n : ℕ) :
    ‖(weightedComplexAction M a) ^ n‖ ≤
      q ^ n * (‖M.continuousPerronFunction hM‖ / m) := by
  have hcoef : 0 ≤ q ^ n * (‖M.continuousPerronFunction hM‖ / m) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hcoef
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hcoef (norm_nonneg f))).2
  intro x
  have hf (y : S) : ‖f y‖ ≤ (‖f‖ / m) * M.continuousPerronFunction hM y := by
    calc
      ‖f y‖ ≤ ‖f‖ := f.norm_coe_le_norm y
      _ = (‖f‖ / m) * m := by field_simp
      _ ≤ (‖f‖ / m) * M.continuousPerronFunction hM y :=
        mul_le_mul_of_nonneg_left (hmu y) (div_nonneg (norm_nonneg _) hm.le)
  have hu : M.continuousPerronFunction hM x ≤ ‖M.continuousPerronFunction hM‖ := by
    have hp : 0 < M.continuousPerronFunction hM x := M.perronFunction_pos hM x
    simpa only [Real.norm_eq_abs, abs_of_pos hp] using
      (M.continuousPerronFunction hM).norm_coe_le_norm x
  have hp := weightedComplexAction_pow_perron_dominated
    M hM a f q (‖f‖ / m) hq ha hf n x
  calc
    ‖(((weightedComplexAction M a) ^ n) f) x‖ ≤
        (q ^ n * (‖f‖ / m)) * M.continuousPerronFunction hM x := hp
    _ ≤ (q ^ n * (‖f‖ / m)) * ‖M.continuousPerronFunction hM‖ :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = (q ^ n * (‖M.continuousPerronFunction hM‖ / m)) * ‖f‖ := by ring

/-- The weighted operator has a norm-convergent Neumann series when `q < 1`. -/
theorem weightedComplexAction_pow_summable (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (a : C(S, ℂ)) (q m : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (ha : ∀ x, ‖a x‖ ≤ q)
    (hm : 0 < m) (hmu : ∀ x, m ≤ M.continuousPerronFunction hM x) :
    Summable (fun n : ℕ => (weightedComplexAction M a) ^ n) := by
  have hgeom : Summable (fun n : ℕ => q ^ n) :=
    summable_geometric_of_lt_one hq hq1
  have hbound : Summable (fun n : ℕ =>
      q ^ n * (‖M.continuousPerronFunction hM‖ / m)) := by
    simpa only [mul_comm] using hgeom.mul_left (‖M.continuousPerronFunction hM‖ / m)
  apply Summable.of_norm_bounded hbound
  intro n
  exact weightedComplexAction_pow_norm_le M hM a q m hq ha hm hmu n

/-- Subcritical weighted kernel actions have actual two-sided inverses. -/
theorem weightedComplexAction_one_sub_isUnit (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (a : C(S, ℂ)) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) (ha : ∀ x, ‖a x‖ ≤ q) :
    IsUnit (1 - weightedComplexAction M a) := by
  obtain ⟨m, hm, hmu⟩ := isCompact_univ.exists_forall_le'
    (M.continuousPerronFunction hM).continuous.continuousOn
    (fun x _ => M.perronFunction_pos hM x)
  have hmu' : ∀ x, m ≤ M.continuousPerronFunction hM x :=
    fun x => hmu x (Set.mem_univ x)
  have hs := weightedComplexAction_pow_summable M hM a q m hq hq1 ha hm hmu'
  refine ⟨⟨1 - weightedComplexAction M a,
    ∑' n : ℕ, (weightedComplexAction M a) ^ n, ?_, ?_⟩, rfl⟩
  · exact hs.one_sub_mul_tsum_pow
  · exact hs.tsum_pow_mul_one_sub

end PerronWright.FiniteIrreducibleOuterNeumann
