import PerronWright.Kernel.CountableApproximationSpectral

/-!
# Actual finite-support kernel laws in the shared countable Hilbert space

Finite support makes the constructed square-root density operator a finite
sum of rank-one maps.  The accompanying finite-law action is the literal
sum `∑ κ(a,b) w(b) f(b)`, and the proved lift identity conjugates that action
to the shared-space operator.  No finite spectral approximation is assumed.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace PerronWright.CountableKernel

def featureCoordinateOutput (M : CountableKernel) (h : M.L2) (a : ℕ) :
    M.L2 →L[ℝ] M.L2 :=
  ((h a) • innerSL ℝ (M.featureRow h a)).smulRight (M.atomVector a)

theorem isCompactOperator_featureCoordinateOutput (M : CountableKernel) (h : M.L2) (a : ℕ) :
    IsCompactOperator (M.featureCoordinateOutput h a) := by
  have hi : IsCompactOperator ((h a) • innerSL ℝ (M.featureRow h a)) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact hi.clm_comp (ContinuousLinearMap.toSpanSingleton ℝ (M.atomVector a))

theorem weightedActionCLM_eq_finite_sum (M : CountableKernel) (h : M.L2) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → h a = 0) :
    M.weightedActionCLM h = ∑ a ∈ s, M.featureCoordinateOutput h a := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [] with a
  rw [sum_apply, M.coe_sum_at]
  simp only [featureCoordinateOutput, ContinuousLinearMap.smulRight_apply,
    smul_apply, M.coe_smul_at, M.atomVector_apply, innerSL_apply_apply]
  rw [weightedActionCLM, M.featureActionCLM_apply]
  by_cases ha : a ∈ s
  · simp [ha]
  · simp [ha, hzero a ha]

theorem isCompactOperator_weightedActionCLM_of_finite_support (M : CountableKernel)
    (h : M.L2) (s : Finset ℕ) (hzero : ∀ a, a ∉ s → h a = 0) :
    IsCompactOperator (M.weightedActionCLM h) := by
  classical
  rw [M.weightedActionCLM_eq_finite_sum h s hzero]
  clear hzero
  induction s using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : M.L2 →L[ℝ] M.L2))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (M.isCompactOperator_featureCoordinateOutput h a).add ih

theorem weightFeature_eq_zero (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) {a : ℕ} (ha : w a = 0) :
    M.weightFeature w hw hs a = 0 := by
  rw [M.weightFeature_apply, weightFeatureFunction, ha]
  simp

theorem isCompactOperator_weighted_probability_of_finite_support (M : CountableKernel)
    (w : ℕ → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) :
    IsCompactOperator (M.weightedActionCLM (M.weightFeature w hw hs)) :=
  M.isCompactOperator_weightedActionCLM_of_finite_support _ s
    (fun a ha ↦ M.weightFeature_eq_zero w hw hs (hzero a ha))

theorem weightedActionCLM_apply_finite_sum (M : CountableKernel) (h v : M.L2)
    (s : Finset ℕ) (hzero : ∀ b, b ∉ s → h b = 0) (a : ℕ) :
    M.weightedActionCLM h v a =
      h a * ∑ b ∈ s, M.mu.real {b} * (M.kernel a b * h b * v b) := by
  rw [weightedActionCLM, M.featureActionCLM_apply_integral, M.integral_eq_tsum_atom]
  congr 1
  apply tsum_eq_sum
  intro b hb
  rw [hzero b hb]
  simp

def finiteLawAction (M : CountableKernel) (s : Finset ℕ) (w f : ℕ → ℝ) (a : ℕ) : ℝ :=
  ∑ b ∈ s, M.kernel a b * w b * f b

def finiteLawLift (M : CountableKernel) (s : Finset ℕ) (h : M.L2) (f : ℕ → ℝ) : M.L2 :=
  ∑ a ∈ s, (h a * f a) • M.atomVector a

theorem finiteLawLift_apply (M : CountableKernel) (s : Finset ℕ) (h : M.L2)
    (f : ℕ → ℝ) (a : ℕ) :
    M.finiteLawLift s h f a = if a ∈ s then h a * f a else 0 := by
  classical
  rw [finiteLawLift, M.coe_sum_at]
  simp only [M.coe_smul_at, M.atomVector_apply]
  simp

/-- The literal finite-law kernel action is intertwined with the actual
square-root-density operator, rather than being supplied as a model field. -/
theorem finiteLawLift_intertwines (M : CountableKernel) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : HasSum w 1) (s : Finset ℕ)
    (hzero : ∀ a, a ∉ s → w a = 0) (f : ℕ → ℝ) :
    M.weightedActionCLM (M.weightFeature w hw hs) (M.finiteLawLift s (M.weightFeature w hw hs) f) =
      M.finiteLawLift s (M.weightFeature w hw hs) (M.finiteLawAction s w f) := by
  classical
  let h := M.weightFeature w hw hs
  have hz : ∀ a, a ∉ s → h a = 0 :=
    fun a ha ↦ M.weightFeature_eq_zero w hw hs (hzero a ha)
  apply Lp.ext
  filter_upwards [] with a
  rw [M.weightedActionCLM_apply_finite_sum h _ s hz, M.finiteLawLift_apply]
  by_cases ha : a ∈ s
  · rw [if_pos ha]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    rw [M.finiteLawLift_apply, if_pos hb]
    have he : M.mu.real {b} * h b ^ 2 = w b := by
      dsimp [h]
      rw [M.weightFeature_apply]
      exact M.weightFeatureFunction_square w hw b
    calc
      M.mu.real {b} * (M.kernel a b * h b * (h b * f b)) =
          (M.mu.real {b} * h b ^ 2) * (M.kernel a b * f b) := by ring
      _ = M.kernel a b * w b * f b := by rw [he]; ring
  · rw [if_neg ha, hz a ha, zero_mul]

end PerronWright.CountableKernel
