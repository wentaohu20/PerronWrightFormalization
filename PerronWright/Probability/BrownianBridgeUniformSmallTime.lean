import PerronWright.Probability.BrownianCircleUniformTime
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Exact scaling of a literal uniform small time

The normalized Lebesgue law on (0,ε] is the actual pushforward of the
normalized Lebesgue law on (0,1] by multiplication by ε.
-/

open MeasureTheory Set
open scoped Classical ENNReal
noncomputable section

namespace PerronWright.BrownianBridgeUniformSmallTime

open BrownianCircleUniformTime

theorem intervalUniform_one_map_mul (ε : ℝ) (hε : 0 < ε) :
    (intervalUniform 1).map (fun s : ℝ ↦ ε*s) = intervalUniform ε := by
  have hpre : (fun s : ℝ ↦ ε*s) ⁻¹' Ioc 0 ε = Ioc 0 1 := by
    ext s
    simp only [Set.mem_preimage,Set.mem_Ioc]
    constructor
    · intro hs
      refine ⟨(mul_pos_iff_of_pos_left hε).mp hs.1,?_⟩
      apply (mul_le_mul_iff_right₀ hε).mp
      simpa only [mul_one] using hs.2
    · intro hs
      refine ⟨mul_pos hε hs.1,?_⟩
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left hs.2 hε.le)
  rw [intervalUniform,ENNReal.ofReal_one,inv_one,one_smul,← hpre,
    ← Measure.restrict_map (measurable_const_mul ε) measurableSet_Ioc,
    Real.map_volume_mul_left hε.ne',Measure.restrict_smul,abs_of_pos (inv_pos.mpr hε),
    ENNReal.ofReal_inv_of_pos hε]
  rfl

end PerronWright.BrownianBridgeUniformSmallTime
