import PerronWright.Analysis.FiniteIrreducibleFieldNormalization

/-! Strict positivity comparison on the actual subcritical field branch.
These finite weighted inequalities choose the physical side of the fold. -/

open scoped BigOperators
noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]

theorem action_mono (M : FiniteIrreducibleModel S) {f h : S → ℝ}
    (hfh : ∀ a, f a ≤ h a) (a : S) : M.action f a ≤ M.action h a := by
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (hfh b) (mul_nonneg (M.kernel_nonneg a b) (M.weight_pos b).le)

variable [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

omit [MeasurableSpace S] [BorelSpace S] in
theorem field_fixed_lt_positive_profile (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) {rho w : ℝ} (hrho : 0 < rho)
    (hw : 0 ≤ w) (hw1 : w < 1) (hτfix : M.fieldTreeMap rho g τ = τ)
    (V : C(S, ℝ)) (hVle : ∀ a, V a ≤ τ a)
    (hVfix : M.fieldTreeMap (rho * w) g V = V) (a : S) : V a < τ a := by
  have heτ := congrArg (fun f : C(S, ℝ) ↦ f a) hτfix
  have heV := congrArg (fun f : C(S, ℝ) ↦ f a) hVfix
  change rho * Real.exp (g a - M.action 1 a + M.action τ a) = τ a at heτ
  change rho * w * Real.exp (g a - M.action 1 a + M.action V a) = V a at heV
  have hact := M.action_mono hVle a
  have hexp : Real.exp (g a - M.action 1 a + M.action V a) ≤
      Real.exp (g a - M.action 1 a + M.action τ a) := Real.exp_le_exp.mpr (by linarith)
  have hle : V a ≤ w * τ a := by
    rw [← heV, ← heτ]
    calc
      rho * w * Real.exp (g a - M.action 1 a + M.action V a) ≤
          rho * w * Real.exp (g a - M.action 1 a + M.action τ a) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hrho.le hw)
      _ = _ := by ring
  exact hle.trans_lt (by nlinarith [hτ a])

omit [MeasurableSpace S] [BorelSpace S] in
theorem field_physical_perron_coordinate_negative (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a)
    {rho w : ℝ} (hrho : 0 < rho) (hw : 0 ≤ w) (hw1 : w < 1)
    (hτfix : M.fieldTreeMap rho g τ = τ) (V : C(S, ℝ))
    (hVle : ∀ a, V a ≤ τ a) (hVfix : M.fieldTreeMap (rho * w) g V = V) :
    ∃ r : ℝ, r < 0 ∧
      M.normalizedPerronFunctional hcrit
        (TreeRealComplexBridge.complexify V - TreeRealComplexBridge.complexify τ) = (r : ℂ) := by
  let _ := M.nonempty
  let r : ℝ := (M.alpha hcrit)⁻¹ *
    ∑ a, M.weight a * M.perronFunction hcrit a * (V a - τ a)
  have hsum : (∑ a, M.weight a * M.perronFunction hcrit a * (V a - τ a)) < 0 := by
    apply Finset.sum_neg
    · intro a _
      exact mul_neg_of_pos_of_neg (mul_pos (M.weight_pos a) (M.perronFunction_pos hcrit a))
        (sub_neg.mpr (M.field_fixed_lt_positive_profile g τ hτ hrho hw hw1 hτfix V hVle hVfix a))
    · exact Finset.univ_nonempty
  refine ⟨r, mul_neg_of_pos_of_neg (inv_pos.mpr (M.alpha_pos hcrit)) hsum, ?_⟩
  change (M.alpha hcrit : ℂ)⁻¹ * M.weightedFunctional hcrit
    (TreeRealComplexBridge.complexify V - TreeRealComplexBridge.complexify τ) = (r : ℂ)
  rw [M.weightedFunctional_apply]
  simp only [ContinuousMap.sub_apply, TreeRealComplexBridge.complexify_apply,
    r, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sum, Complex.ofReal_sub]

end PerronWright.FiniteIrreducibleModel
