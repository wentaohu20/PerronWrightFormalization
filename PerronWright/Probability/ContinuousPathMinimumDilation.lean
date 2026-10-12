import PerronWright.Probability.BrownianPathDilationLaw
import PerronWright.Probability.ContinuousPathLeastMinimum

/-! # Exact least minimum scaling for every continuous path

Positive height dilation preserves the true minimum and its earliest
attaining time. These deterministic identities also hold with multiple
minima; almost-sure uniqueness is not needed as an interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.ContinuousPathMinimumDilation

open BrownianPathLaw BrownianPathDilationLaw ContinuousPathLeastMinimum

theorem minimumValue_dilatePath (T : ℝ≥0) (hT : 0 < T) (c : ℝ) (hc : 0 < c) (f : Path) :
    minimumValue T (dilatePath T c f) = c*minimumValue 1 f := by
  have hm : T*leastMinimizer 1 f ≤ T := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (leastMinimizer_le_time 1 f) (show 0 ≤ T from zero_le)
  apply le_antisymm
  · calc minimumValue T (dilatePath T c f) ≤ dilatePath T c f (T*leastMinimizer 1 f) :=
          minimumValue_le T _ _ hm
      _ = c*minimumValue 1 f := by
        change c*f ((T*leastMinimizer 1 f)/T) = _
        rw [mul_comm T,mul_div_cancel_right₀ _ (ne_of_gt hT),leastMinimizer_value]
  · obtain ⟨t,ht,he,_⟩ := exists_minimumValue T (dilatePath T c f)
    rw [he]
    change c*minimumValue 1 f ≤ c*f (t/T)
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply minimumValue_le 1 f
    exact (div_le_iff₀ hT).mpr (by simpa only [one_mul] using ht)

theorem leastMinimizer_dilatePath (T : ℝ≥0) (hT : 0 < T) (c : ℝ) (hc : 0 < c) (f : Path) :
    leastMinimizer T (dilatePath T c f) = T*leastMinimizer 1 f := by
  have hm : T*leastMinimizer 1 f ≤ T := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (leastMinimizer_le_time 1 f) (show 0 ≤ T from zero_le)
  have hunit : leastMinimizer T (dilatePath T c f)/T ≤ 1 :=
    (div_le_iff₀ hT).mpr (by simpa only [one_mul] using leastMinimizer_le_time T (dilatePath T c f))
  apply le_antisymm
  · apply leastMinimizer_le T _ _ hm
    change c*f ((T*leastMinimizer 1 f)/T) = _
    rw [mul_comm T,mul_div_cancel_right₀ _ (ne_of_gt hT),leastMinimizer_value,
      minimumValue_dilatePath T hT c hc f]
  · have he := leastMinimizer_value T (dilatePath T c f)
    change c*f (leastMinimizer T (dilatePath T c f)/T) = minimumValue T (dilatePath T c f) at he
    rw [minimumValue_dilatePath T hT c hc f] at he
    have hat : f (leastMinimizer T (dilatePath T c f)/T) = minimumValue 1 f :=
      mul_left_cancel₀ (ne_of_gt hc) he
    have hleast := leastMinimizer_le 1 f _ hunit hat
    simpa only [mul_comm] using (le_div_iff₀ hT).mp hleast

end PerronWright.ContinuousPathMinimumDilation
