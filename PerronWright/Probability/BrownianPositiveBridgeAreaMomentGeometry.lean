import PerronWright.Probability.BrownianBridgeCyclicArea
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-! # Pathwise area powers bounded by genuine coordinate integrals

Jensen's inequality is applied to each continuous path on its actual
time interval.  In particular this does not require any probability
moment or uniform-integrability premise.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeAreaMomentGeometry

open BrownianPathLaw BrownianBridgeCyclicArea

theorem pathArea_even_pow_le_integral (T : ℝ≥0) (hT : 0 < T) (f : Path) (n : ℕ) :
    |pathArea T f|^(2*n+2) ≤
      (T : ℝ)^(2*n+1) * ∫ r in Ioc (0 : ℝ) (T : ℝ), |f (Real.toNNReal r)|^(2*n+2) := by
  let v : ℝ → ℝ := fun r ↦ f (Real.toNNReal r)
  have hc : Continuous v := (continuous_path f).comp continuous_real_toNNReal
  have hev : Even (2*n+2) := ⟨n+1,by omega⟩
  have hvol : volume (Ioc (0 : ℝ) (T : ℝ)) = ENNReal.ofReal (T : ℝ) := by
    simp only [Real.volume_Ioc,sub_zero]
  have hvr : volume.real (Ioc (0 : ℝ) (T : ℝ)) = (T : ℝ) := by
    rw [measureReal_def,hvol]
    exact ENNReal.toReal_ofReal (show 0 ≤ (T : ℝ) from T.property)
  have hj := (hev.convexOn_pow (𝕜 := ℝ)).map_set_average_le
    (continuous_id.pow (2*n+2)).continuousOn isClosed_univ
    (by rw [hvol]; exact ENNReal.ofReal_ne_zero_iff.mpr hT)
    (by rw [hvol]; exact ENNReal.ofReal_ne_top)
    (ae_of_all _ (fun _ ↦ mem_univ _))
    (hc.intervalIntegrable 0 T).1
    ((hc.pow (2*n+2)).intervalIntegrable 0 T).1
  simp only [setAverage_eq,hvr,smul_eq_mul] at hj
  have hA : (∫ r in Ioc (0 : ℝ) (T : ℝ), v r) = pathArea T f := by
    symm
    exact intervalIntegral.integral_of_le T.property
  rw [hA,mul_pow] at hj
  have hpow : (0 : ℝ) < (T : ℝ)^(2*n+2) := pow_pos hT _
  have hJ := mul_le_mul_of_nonneg_left hj hpow.le
  have hi : ∫ r in Ioc (0 : ℝ) (T : ℝ), v r^(2*n+2) =
      ∫ r in Ioc (0 : ℝ) (T : ℝ), |v r|^(2*n+2) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun r ↦ (hev.pow_abs (v r)).symm)
  rw [hi] at hJ
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hT
  have hl : (T : ℝ)^(2*n+2)*((T : ℝ)⁻¹)^(2*n+2) = 1 := by
    rw [← mul_pow,mul_inv_cancel₀ hTne,one_pow]
  have hr : (T : ℝ)^(2*n+2)*(T : ℝ)⁻¹ = (T : ℝ)^(2*n+1) := by
    rw [show 2*n+2 = (2*n+1)+1 by omega,pow_succ]
    field_simp
  simpa only [← mul_assoc,hl,hr,one_mul,← hev.pow_abs (pathArea T f)] using hJ

theorem pathArea_even_pow_lintegral_bound (T : ℝ≥0) (hT : 0 < T) (f : Path) (n : ℕ) :
    ENNReal.ofReal (|pathArea T f|^(2*n+2)) ≤
      ENNReal.ofReal ((T : ℝ)^(2*n+1)) *
        ∫⁻ r in Ioc (0 : ℝ) (T : ℝ), ENNReal.ofReal (|f (Real.toNNReal r)|^(2*n+2)) := by
  have hc : Continuous (fun r : ℝ ↦ |f (Real.toNNReal r)|^(2*n+2)) :=
    ((continuous_path f).comp continuous_real_toNNReal).abs.pow _
  have hi : IntegrableOn (fun r : ℝ ↦ |f (Real.toNNReal r)|^(2*n+2))
      (Ioc (0 : ℝ) (T : ℝ)) := (hc.intervalIntegrable 0 T).1
  calc
    _ ≤ ENNReal.ofReal ((T : ℝ)^(2*n+1) *
        ∫ r in Ioc (0 : ℝ) (T : ℝ), |f (Real.toNNReal r)|^(2*n+2)) :=
      ENNReal.ofReal_le_ofReal (pathArea_even_pow_le_integral T hT f n)
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity),ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ (fun _ ↦ by positivity))]

end PerronWright.BrownianPositiveBridgeAreaMomentGeometry
