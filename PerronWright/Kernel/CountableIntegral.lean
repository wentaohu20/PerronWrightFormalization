import PerronWright.Model.CountableKernel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The actual countable integral operator on `L²(μ)`

Each bounded kernel row is an `L²` vector.  Its inner product with an input
vector gives the actual integral action, whose uniformly bounded output is
again an `L²` vector.  The continuous linear operator is constructed from
these functions, rather than assumed as model data.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace PerronWright.CountableKernel

abbrev L2 (M : CountableKernel) := Lp ℝ 2 M.mu

/-- Positivity of every atom turns an almost-everywhere assertion into an
assertion at every type; no choice of a pointwise representative is lost. -/
theorem forall_of_ae (M : CountableKernel) {p : ℕ → Prop} (h : ∀ᵐ a ∂M.mu, p a) :
    ∀ a, p a := by
  intro a
  by_contra hn
  have hs : {a} ⊆ {b | ¬p b} := by
    intro b hb
    have hba : b = a := Set.mem_singleton_iff.mp hb
    simpa [hba] using hn
  have hz : M.mu {a} = 0 := measure_mono_null hs (ae_iff.mp h)
  exact (M.atom_pos a).ne' hz

theorem row_memLp (M : CountableKernel) (a : ℕ) : MemLp (M.kernel a) 2 M.mu :=
  MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable M.upper
    (Filter.Eventually.of_forall (M.norm_kernel_le a))

def row (M : CountableKernel) (a : ℕ) : M.L2 :=
  (M.row_memLp a).toLp (M.kernel a)

theorem row_coe_ae (M : CountableKernel) (a : ℕ) :
    M.row a =ᵐ[M.mu] M.kernel a := (M.row_memLp a).coeFn_toLp

theorem norm_row_le (M : CountableKernel) (a : ℕ) : ‖M.row a‖ ≤ M.upper := by
  have hb : ∀ᵐ b ∂M.mu, ‖M.row a b‖ ≤ M.upper := by
    filter_upwards [M.row_coe_ae a] with b hb
    rw [hb]
    exact M.norm_kernel_le a b
  simpa [measureUnivNNReal, measure_univ] using
    (Lp.norm_le_of_ae_bound M.upper_nonneg hb)

def pointwiseAction (M : CountableKernel) (v : M.L2) (a : ℕ) : ℝ :=
  inner ℝ (M.row a) v

theorem pointwiseAction_eq_integral (M : CountableKernel) (v : M.L2) (a : ℕ) :
    M.pointwiseAction v a = ∫ b, M.kernel a b * v b ∂M.mu := by
  rw [pointwiseAction, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [M.row_coe_ae a] with b hb
  simp [hb, mul_comm]

theorem norm_pointwiseAction_le (M : CountableKernel) (v : M.L2) (a : ℕ) :
    ‖M.pointwiseAction v a‖ ≤ M.upper * ‖v‖ := by
  exact (norm_inner_le_norm (𝕜 := ℝ) (M.row a) v).trans
    (mul_le_mul_of_nonneg_right (M.norm_row_le a) (norm_nonneg _))

theorem pointwiseAction_memLp (M : CountableKernel) (v : M.L2) :
    MemLp (M.pointwiseAction v) 2 M.mu :=
  MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable (M.upper * ‖v‖)
    (Filter.Eventually.of_forall (M.norm_pointwiseAction_le v))

def action (M : CountableKernel) (v : M.L2) : M.L2 :=
  (M.pointwiseAction_memLp v).toLp (M.pointwiseAction v)

theorem action_coe_ae (M : CountableKernel) (v : M.L2) :
    M.action v =ᵐ[M.mu] M.pointwiseAction v := (M.pointwiseAction_memLp v).coeFn_toLp

theorem action_add (M : CountableKernel) (v w : M.L2) :
    M.action (v + w) = M.action v + M.action w := by
  apply Lp.ext
  filter_upwards [M.action_coe_ae (v + w), M.action_coe_ae v, M.action_coe_ae w,
    Lp.coeFn_add (M.action v) (M.action w)] with a hvw hv hw hsum
  rw [hvw, hsum]
  change M.pointwiseAction (v + w) a = M.action v a + M.action w a
  rw [hv, hw]
  exact inner_add_right _ _ _

theorem action_smul (M : CountableKernel) (c : ℝ) (v : M.L2) :
    M.action (c • v) = c • M.action v := by
  apply Lp.ext
  filter_upwards [M.action_coe_ae (c • v), M.action_coe_ae v,
    Lp.coeFn_smul c (M.action v)] with a hcv hv hsmul
  simp [hcv, hsmul, hv, pointwiseAction, inner_smul_right]

theorem norm_action_le (M : CountableKernel) (v : M.L2) :
    ‖M.action v‖ ≤ M.upper * ‖v‖ := by
  have hb : ∀ᵐ a ∂M.mu, ‖M.action v a‖ ≤ M.upper * ‖v‖ := by
    filter_upwards [M.action_coe_ae v] with a ha
    rw [ha]
    exact M.norm_pointwiseAction_le v a
  simpa [measureUnivNNReal, measure_univ] using
    (Lp.norm_le_of_ae_bound (mul_nonneg M.upper_nonneg (norm_nonneg v)) hb)

def actionCLM (M : CountableKernel) : M.L2 →L[ℝ] M.L2 :=
  LinearMap.mkContinuous
    { toFun := M.action
      map_add' := M.action_add
      map_smul' := M.action_smul }
    M.upper M.norm_action_le

@[simp] theorem actionCLM_apply (M : CountableKernel) (v : M.L2) :
    M.actionCLM v = M.action v := rfl

theorem norm_actionCLM_le (M : CountableKernel) : ‖M.actionCLM‖ ≤ M.upper :=
  LinearMap.mkContinuous_norm_le _ M.upper_nonneg M.norm_action_le

theorem actionCLM_eq_integral_ae (M : CountableKernel) (v : M.L2) :
    M.actionCLM v =ᵐ[M.mu] (fun a ↦ ∫ b, M.kernel a b * v b ∂M.mu) := by
  exact (M.action_coe_ae v).trans (Filter.Eventually.of_forall (M.pointwiseAction_eq_integral v))

theorem actionCLM_apply_integral (M : CountableKernel) (v : M.L2) (a : ℕ) :
    M.actionCLM v a = ∫ b, M.kernel a b * v b ∂M.mu :=
  M.forall_of_ae (M.actionCLM_eq_integral_ae v) a

/-- The constructed operator has the literal weighted countable-sum formula. -/
theorem actionCLM_apply_tsum (M : CountableKernel) (v : M.L2) (a : ℕ) :
    M.actionCLM v a = ∑' b, M.kernel a b * v b * (M.mu {b}).toReal := by
  rw [M.actionCLM_apply_integral]
  let f : ℕ → ℝ := fun b ↦ M.kernel a b * v b
  have hi := integral_sum_dirac (f := f) (x := fun b : ℕ ↦ b)
    (c := fun b ↦ M.mu {b}) (fun b ↦ measure_ne_top M.mu {b})
  rw [M.mu.sum_smul_dirac] at hi
  simpa [f, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hi

end PerronWright.CountableKernel
