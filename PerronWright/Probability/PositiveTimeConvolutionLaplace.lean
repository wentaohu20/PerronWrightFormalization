import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Positive-time convolution and its nonnegative Laplace transform

The triangular time domain is changed to the positive quadrant by the
actual Lebesgue-preserving shear. Tonelli then proves the convolution
formula without any integrability or finite-transform premise.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.PositiveTimeConvolutionLaplace

theorem triangle_lintegral_eq_quadrant {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ T : ℝ, ∫⁻ s in Ioo 0 T, F (s,T-s)) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), F (s,t) := by
  let G : ℝ × ℝ → ℝ≥0∞ := fun p ↦
    if 0 < p.1 ∧ p.1 < p.2 then F (p.1,p.2-p.1) else 0
  have hG : Measurable G := Measurable.ite
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd))
    (hF.comp (measurable_fst.prodMk (measurable_snd.sub measurable_fst))) measurable_const
  have hGT (T : ℝ) : (∫⁻ s in Ioo 0 T, F (s,T-s)) = ∫⁻ s : ℝ, G (s,T) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro s
    simp only [indicator,mem_Ioo,G]
  simp_rw [hGT]
  rw [← lintegral_lintegral_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ)) (f := fun s T : ℝ ↦ G (s,T)) hG.aemeasurable]
  have he := (measurePreserving_prod_add (volume : Measure ℝ) (volume : Measure ℝ)).lintegral_comp hG
  have hGs : Measurable (fun q : ℝ × ℝ ↦ G (q.1,q.1+q.2)) :=
    hG.comp (measurable_fst.prodMk (measurable_fst.add measurable_snd))
  change (∫⁻ q : ℝ × ℝ, G (q.1,q.1+q.2) ∂volume.prod volume) = ∫⁻ q : ℝ × ℝ, G q ∂volume.prod volume at he
  rw [lintegral_prod _ hG.aemeasurable,lintegral_prod _ hGs.aemeasurable] at he
  rw [← he]
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro s
  by_cases hs : 0 < s
  · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs),← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro t
    have ht : s < s+t ↔ 0 < t := by constructor <;> intro h <;> linarith
    by_cases hp : 0 < t
    · simp only [G,ht,hs,hp,true_and,if_true,
        indicator_of_mem (show t ∈ Ioi (0 : ℝ) from hp),add_sub_cancel_left]
    · simp only [G,ht,hs,hp,true_and,if_false,
        indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from hp)]
  · simp only [G,hs,false_and,if_false,lintegral_zero,
      indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]

def laplaceWeight (p t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-p*t))

theorem measurable_laplaceWeight (p : ℝ) : Measurable (laplaceWeight p) := by
  exact (Real.continuous_exp.comp (by fun_prop : Continuous (fun t : ℝ ↦ -p*t))).measurable.ennreal_ofReal

theorem laplaceWeight_add (p s t : ℝ) :
    laplaceWeight p (s+t) = laplaceWeight p s*laplaceWeight p t := by
  unfold laplaceWeight
  rw [show -p*(s+t) = -p*s+ -p*t by ring,Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)]

theorem laplace_triangle_lintegral {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) (p : ℝ) :
    (∫⁻ T : ℝ, laplaceWeight p T*(∫⁻ s in Ioo 0 T, F (s,T-s))) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ),
        laplaceWeight p s*laplaceWeight p t*F (s,t) := by
  have hH : Measurable (fun q : ℝ × ℝ ↦ laplaceWeight p (q.1+q.2)*F q) :=
    ((measurable_laplaceWeight p).comp (measurable_fst.add measurable_snd)).mul hF
  have he := triangle_lintegral_eq_quadrant hH
  simp only [laplaceWeight_add] at he
  convert he using 1
  apply lintegral_congr
  intro T
  have hFT : Measurable (fun s : ℝ ↦ F (s,T-s)) :=
    hF.comp (measurable_id.prodMk (measurable_const.sub measurable_id))
  rw [← lintegral_const_mul _ hFT]
  apply lintegral_congr
  intro s
  rw [← laplaceWeight_add]
  congr 2
  ring

theorem laplace_convolution {A B : ℝ → ℝ≥0∞} (hA : Measurable A) (hB : Measurable B) (p : ℝ) :
    (∫⁻ T : ℝ, laplaceWeight p T*(∫⁻ s in Ioo 0 T, A s*B (T-s))) =
      (∫⁻ s in Ioi (0 : ℝ), laplaceWeight p s*A s)*
        (∫⁻ t in Ioi (0 : ℝ), laplaceWeight p t*B t) := by
  have he := laplace_triangle_lintegral (F := fun q : ℝ × ℝ ↦ A q.1*B q.2)
    ((hA.comp measurable_fst).mul (hB.comp measurable_snd)) p
  rw [he]
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ), (laplaceWeight p s*A s)*
        (∫⁻ t in Ioi (0 : ℝ), laplaceWeight p t*B t) := by
      apply lintegral_congr
      intro s
      calc
        _ = ∫⁻ t in Ioi (0 : ℝ), (laplaceWeight p s*A s)*(laplaceWeight p t*B t) := by
          apply lintegral_congr
          intro t
          ac_rfl
        _ = _ := lintegral_const_mul _
          (show Measurable (fun t : ℝ ↦ laplaceWeight p t*B t) from (measurable_laplaceWeight p).mul hB)
    _ = _ := lintegral_mul_const _ ((measurable_laplaceWeight p).mul hA)

end PerronWright.PositiveTimeConvolutionLaplace
