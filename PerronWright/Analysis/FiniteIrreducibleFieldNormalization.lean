import PerronWright.Model.FiniteIrreducibleTilted
import PerronWright.Analysis.FiniteIrreducibleLeastBranch

/-!
# Actual field tree maps and positive-profile normalization

The real field map is the literal finite weighted tree map. Its iteration
starts at zero. A proved positive critical profile conjugates this map to
the zero-field map of the actual tilted model, hence transfers genuine
leastness and convergence, without a primitive hypothesis.
-/

open Filter Topology
open scoped BigOperators
noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def fieldTreeMap (M : FiniteIrreducibleModel S) (z : ℝ) (g V : C(S, ℝ)) : C(S, ℝ) :=
  ⟨fun a ↦ z * Real.exp (g a - M.action 1 a + M.action V a),
    continuous_of_discreteTopology⟩

omit [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem fieldTreeMap_apply (M : FiniteIrreducibleModel S)
    (z : ℝ) (g V : C(S, ℝ)) (a : S) :
    M.fieldTreeMap z g V a = z * Real.exp (g a - M.action 1 a + M.action V a) := rfl

def fieldTreeIter (M : FiniteIrreducibleModel S) (z : ℝ) (g : C(S, ℝ)) : ℕ → C(S, ℝ)
  | 0 => 0
  | n + 1 => M.fieldTreeMap z g (M.fieldTreeIter z g n)

theorem fieldTreeMap_conjugacy (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) (rho : ℝ)
    (hfix : M.fieldTreeMap rho g τ = τ) (w : ℝ) (V : C(S, ℝ)) :
    M.fieldTreeMap (rho * w) g (τ * V) =
      τ * (M.tilted τ hτ).bjrModel.normalizedZeroTreeMap w V := by
  ext a
  rw [fieldTreeMap_apply, ContinuousMap.mul_apply,
    CompactBJRModel.normalizedZeroTreeMap_apply]
  change rho * w * Real.exp (g a - M.action 1 a + M.action (τ * V) a) =
    τ a * (w * Real.exp
      ((M.tilted τ hτ).continuousKernel.action (M.tilted τ hτ).measure (V - 1) a))
  rw [(M.tilted τ hτ).continuous_action_apply, M.tilted_action]
  have he := congrArg (fun f : C(S, ℝ) ↦ f a) hfix
  change rho * Real.exp (g a - M.action 1 a + M.action τ a) = τ a at he
  have harg : g a - M.action 1 a + M.action (τ * V) a =
      (g a - M.action 1 a + M.action τ a) +
        M.action (τ * (V - 1)) a := by
    have hd : M.action (τ * (V - 1)) a = M.action (τ * V) a - M.action τ a := by
      change (∑ b, M.kernel a b * M.weight b * (τ b * (V b - 1))) =
        (∑ b, M.kernel a b * M.weight b * (τ b * V b)) -
          ∑ b, M.kernel a b * M.weight b * τ b
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [hd]
    ring
  rw [harg, Real.exp_add]
  calc
    rho * w * (Real.exp (g a - M.action 1 a + M.action τ a) *
        Real.exp (M.action (τ * (V - 1)) a)) =
      (rho * Real.exp (g a - M.action 1 a + M.action τ a)) *
        (w * Real.exp (M.action (τ * (V - 1)) a)) := by ring
    _ = _ := by rw [he]; rfl

theorem fieldTreeIter_conjugacy (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) (rho : ℝ)
    (hfix : M.fieldTreeMap rho g τ = τ) (w : ℝ) (n : ℕ) :
    M.fieldTreeIter (rho * w) g n =
      τ * (M.tilted τ hτ).bjrModel.normalizedZeroTreeIter w n := by
  induction n with
  | zero => simp [fieldTreeIter, CompactBJRModel.normalizedZeroTreeIter]
  | succ n ih =>
    simp only [fieldTreeIter, ih, CompactBJRModel.normalizedZeroTreeIter]
    exact M.fieldTreeMap_conjugacy g τ hτ rho hfix w _

theorem fieldTreeIter_least_fixed_of_positive_profile (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) (rho : ℝ)
    (hfix : M.fieldTreeMap rho g τ = τ) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    ∃ V : C(S, ℝ), Tendsto (M.fieldTreeIter (rho * w) g) atTop (𝓝 V) ∧
      (∀ a, 0 ≤ V a ∧ V a ≤ τ a) ∧ M.fieldTreeMap (rho * w) g V = V ∧
      ∀ W : C(S, ℝ), (∀ a, 0 ≤ W a) →
        M.fieldTreeMap (rho * w) g W = W → ∀ a, V a ≤ W a := by
  obtain ⟨U, hUlim, hUbounds, hUfix, hUleast⟩ :=
    (M.tilted τ hτ).normalizedZeroTreeIter_least_fixed w hw hw1
  refine ⟨τ * U, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous (fun f : C(S, ℝ) ↦ τ * f) := continuous_const.mul continuous_id
    have he : M.fieldTreeIter (rho * w) g =
        fun n ↦ τ * (M.tilted τ hτ).bjrModel.normalizedZeroTreeIter w n :=
      funext (M.fieldTreeIter_conjugacy g τ hτ rho hfix w)
    rw [he]
    exact (hc.tendsto U).comp hUlim
  · intro a
    change 0 ≤ τ a * U a ∧ τ a * U a ≤ τ a
    exact ⟨mul_nonneg (hτ a).le (hUbounds a).1,
      by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hUbounds a).2 (hτ a).le⟩
  · rw [M.fieldTreeMap_conjugacy g τ hτ rho hfix, hUfix]
  · intro W hW hWfix a
    let Q : C(S, ℝ) := ⟨fun b ↦ W b / τ b, continuous_of_discreteTopology⟩
    have hτQ : τ * Q = W := by
      ext b
      exact mul_div_cancel₀ _ (hτ b).ne'
    have hQfix : (M.tilted τ hτ).bjrModel.normalizedZeroTreeMap w Q = Q := by
      have he := M.fieldTreeMap_conjugacy g τ hτ rho hfix w Q
      rw [hτQ, hWfix, ← hτQ] at he
      ext b
      exact (mul_left_cancel₀ (hτ b).ne' (congrArg (fun f : C(S, ℝ) ↦ f b) he)).symm
    have hQnonneg (b : S) : 0 ≤ Q b := div_nonneg (hW b) (hτ b).le
    have hle := mul_le_mul_of_nonneg_left (hUleast Q hQnonneg hQfix a) (hτ a).le
    simpa only [ContinuousMap.mul_apply, Q, ContinuousMap.coe_mk,
      mul_div_cancel₀ _ (hτ a).ne'] using hle

theorem fieldTreeIter_critical_converges_of_positive_profile (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) (rho : ℝ)
    (hfix : M.fieldTreeMap rho g τ = τ) (hcritical : (M.tilted τ hτ).IsCritical) :
    Tendsto (M.fieldTreeIter rho g) atTop (𝓝 τ) := by
  have hc : Continuous (fun f : C(S, ℝ) ↦ τ * f) := continuous_const.mul continuous_id
  have he : M.fieldTreeIter rho g =
      fun n ↦ τ * (M.tilted τ hτ).bjrModel.normalizedZeroTreeIter 1 n := by
    funext n
    simpa only [mul_one] using M.fieldTreeIter_conjugacy g τ hτ rho hfix 1 n
  rw [he]
  have hh := (hc.tendsto (1 : C(S, ℝ))).comp
    ((M.tilted τ hτ).normalizedZeroTreeIter_one_converges hcritical)
  rw [mul_one] at hh
  exact hh

end PerronWright.FiniteIrreducibleModel
