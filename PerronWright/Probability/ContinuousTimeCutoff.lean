import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Concrete bounded continuous cutoff on nonnegative time -/

open Set
open scoped NNReal BoundedContinuousFunction
noncomputable section

namespace PerronWright.ContinuousTimeCutoff

theorem exists_timeCutoff (r b : ℝ≥0) (hrb : r < b) :
    ∃ κ : ℝ≥0 →ᵇ ℝ, (∀ t, 0 ≤ κ t ∧ κ t ≤ 1) ∧
      (∀ t, t ≤ r → κ t = 1) ∧ (∀ t, b ≤ t → κ t = 0) := by
  have hd : Disjoint (Ici b) (Iic r) := disjoint_left.mpr (by
    intro t hb ht
    exact (not_le_of_gt hrb) (hb.trans ht))
  obtain ⟨f,hzero,hone,hbounds⟩ := exists_continuous_zero_one_of_isClosed
    isClosed_Ici isClosed_Iic hd
  let κ : ℝ≥0 →ᵇ ℝ := ⟨f,⟨1,by
    intro t u
    change dist (f t) (f u) ≤ (1 : ℝ)
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith [(hbounds t).1,(hbounds u).2],
      by linarith [(hbounds t).2,(hbounds u).1]⟩⟩⟩
  exact ⟨κ,hbounds,fun t ht ↦ hone ht,fun t ht ↦ hzero ht⟩

end PerronWright.ContinuousTimeCutoff
