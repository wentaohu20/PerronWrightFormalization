import PerronWright.Analysis.TreeContraction
import PerronWright.Analysis.PerronFunctional

/-! Uniqueness at the normalized critical tree equation, proved by Perron integration. -/

open MeasureTheory
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem CompactBJRModel.normalizedZeroTreeMap_one_unique
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (V : C(S, ℝ)) (hfix : M.normalizedZeroTreeMap 1 V = V) :
    V = 1 := by
  let q : C(S, ℝ) := 1 - V
  let Kq : C(S, ℝ) := M.kernel.action M.mu q
  let u := M.perronFunction hM
  have hVsub : (V - 1 : C(S, ℝ)) = -q := by dsimp [q]; abel
  have hKneg (x : S) : M.kernel.action M.mu (V - 1) x = -Kq x := by
    rw [hVsub]
    change ((M.kernel.actionLinearMap M.mu) (-q)) x = -Kq x
    rw [map_neg]
    rfl
  have hfixed (x : S) : q x = 1 - Real.exp (-Kq x) := by
    have hx := congrArg (fun U : C(S, ℝ) => U x) hfix
    rw [M.normalizedZeroTreeMap_apply, hKneg] at hx
    simp only [one_mul] at hx
    change 1 - V x = 1 - Real.exp (-Kq x)
    rw [hx]
  have hgap_nonneg (x : S) : 0 ≤ Kq x - q x := by
    rw [hfixed]
    have h := Real.one_sub_le_exp_neg (Kq x)
    linarith
  have hweighted : (∫ x, u x * Kq x ∂M.mu) =
      ∫ x, u x * q x ∂M.mu :=
    M.weightedIntegral_action hM q
  have hcontK : Continuous (fun x : S => u x * Kq x) := u.continuous.mul Kq.continuous
  have hcontq : Continuous (fun x : S => u x * q x) := u.continuous.mul q.continuous
  have hintK : Integrable (fun x : S => u x * Kq x) M.mu :=
    hcontK.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hintq : Integrable (fun x : S => u x * q x) M.mu :=
    hcontq.integrable_of_hasCompactSupport isClosed_closure.isCompact
  let gap : S → ℝ := fun x => u x * (Kq x - q x)
  have hcont : Continuous gap := u.continuous.mul (Kq.continuous.sub q.continuous)
  have hint : Integrable gap M.mu :=
    hcont.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hgap0 : (∫ x, gap x ∂M.mu) = 0 := by
    change (∫ x, u x * (Kq x - q x) ∂M.mu) = 0
    simp_rw [mul_sub]
    rw [integral_sub hintK hintq]
    exact sub_eq_zero.mpr hweighted
  have hgap (x : S) : gap x = 0 := by
    by_contra hx
    have hpos : 0 < ∫ y, gap y ∂M.mu :=
      integral_pos_of_integrable_nonneg_nonzero hcont hint
        (fun y => mul_nonneg (M.perronFunction_pos hM y).le (hgap_nonneg y)) hx
    linarith
  apply ContinuousMap.ext
  intro x
  have hKq0 : Kq x = 0 := by
    have hprod := hgap x
    have hgap0x : Kq x - q x = 0 := by
      exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt (M.perronFunction_pos hM x))
    by_contra hk
    have hstrict := Real.one_sub_lt_exp_neg hk
    rw [hfixed x] at hgap0x
    linarith
  have hqx : q x = 0 := by simpa [hKq0] using hfixed x
  change V x = (1 : C(S, ℝ)) x
  change V x = 1
  change 1 - V x = 0 at hqx
  linarith

end PerronWright
