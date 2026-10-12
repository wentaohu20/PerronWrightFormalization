import PerronWright.Probability.PositiveTimeConvolutionLaplace
import PerronWright.Probability.BrownianKilledAreaMomentDensityBoundary

/-! # Genuine killed-area duration resolvents

These are transforms of the proved densities of actual surviving
Brownian area-moment measures. Their time-quadrant insertion formula
follows from the actual Kac equation and the Lebesgue-preserving shear.
No Green-kernel formula, boundary derivative, or nonlinear moment
recurrence is imposed.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentResolvent

open BrownianKilledAreaMomentDensity BrownianKilledAreaMomentDensityLaw
open BrownianKilledAreaMomentKernel PositiveTimeConvolutionLaplace

def realDensity (n : ℕ) (t x y : ℝ) : ℝ≥0∞ :=
  if 0 < t then density n (Real.toNNReal t,(x,y)) else 0

theorem measurable_realDensity (n : ℕ) :
    Measurable (fun q : ℝ × (ℝ × ℝ) ↦ realDensity n q.1 q.2.1 q.2.2) := by
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    ((measurable_density n).comp
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)) measurable_const

theorem realDensity_succ (n : ℕ) (T x y : ℝ) :
    realDensity (n+1) T x y = ((n+1 : ℕ) : ℝ≥0∞)*∫⁻ s in Ioo 0 T, ∫⁻ z : ℝ,
      realDensity 0 s x z*ENNReal.ofReal z*realDensity n (T-s) z y := by
  by_cases hT : 0 < T
  · rw [realDensity,if_pos hT,density_succ,Real.coe_toNNReal _ hT.le]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have ht : 0 < T-s := sub_pos.mpr hs.2
    have he : Real.toNNReal T-Real.toNNReal s = Real.toNNReal (T-s) := by
      rw [NNReal.sub_def,Real.coe_toNNReal _ hT.le,Real.coe_toNNReal _ hs.1.le]
    apply lintegral_congr
    intro z
    simp only [realDensity,if_pos hs.1,if_pos ht,density_zero,he]
  · have he : Ioo (0 : ℝ) T = ∅ := Ioo_eq_empty hT
    simp only [realDensity,if_neg hT,he,Measure.restrict_empty,lintegral_zero_measure,mul_zero]

def resolvent (n : ℕ) (p x y : ℝ) : ℝ≥0∞ :=
  ∫⁻ T : ℝ, laplaceWeight p T*realDensity n T x y

theorem resolvent_eq_positive_time_integral (n : ℕ) (p x y : ℝ) :
    resolvent n p x y = ∫⁻ T in Ioi (0 : ℝ),
      laplaceWeight p T*density n (Real.toNNReal T,(x,y)) := by
  rw [resolvent,← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro T
  by_cases hT : 0 < T
  · simp only [realDensity,if_pos hT,indicator_of_mem (show T ∈ Ioi (0 : ℝ) from hT)]
  · simp only [realDensity,if_neg hT,mul_zero,
      indicator_of_notMem (show T ∉ Ioi (0 : ℝ) from hT)]

theorem resolvent_eq_positive_realDensity (n : ℕ) (p x y : ℝ) :
    resolvent n p x y = ∫⁻ T in Ioi (0 : ℝ), laplaceWeight p T*realDensity n T x y := by
  rw [resolvent_eq_positive_time_integral]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  rw [realDensity,if_pos (show 0 < T from hT)]

theorem measurable_resolvent (n : ℕ) (p : ℝ) :
    Measurable (fun q : ℝ × ℝ ↦ resolvent n p q.1 q.2) := by
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ ↦ laplaceWeight p q.2*
      realDensity n q.2 q.1.1 q.1.2) :=
    ((measurable_laplaceWeight p).comp measurable_snd).mul
      ((measurable_realDensity n).comp (measurable_snd.prodMk measurable_fst))
  exact hm.lintegral_prod_right'

theorem resolvent_succ_time_quadrant (n : ℕ) (p x y : ℝ) :
    resolvent (n+1) p x y = ((n+1 : ℕ) : ℝ≥0∞)*
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ),
        laplaceWeight p s*laplaceWeight p t*(∫⁻ z : ℝ,
          realDensity 0 s x z*ENNReal.ofReal z*realDensity n t z y) := by
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ ↦
      realDensity 0 q.1.1 x q.2*ENNReal.ofReal q.2*realDensity n q.1.2 q.2 y) :=
    (((measurable_realDensity 0).comp
      ((measurable_fst.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))).mul
        measurable_snd.ennreal_ofReal).mul ((measurable_realDensity n).comp
          ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.prodMk measurable_const)))
  have hF : Measurable (fun q : ℝ × ℝ ↦ ∫⁻ z : ℝ,
      realDensity 0 q.1 x z*ENNReal.ofReal z*realDensity n q.2 z y) := hm.lintegral_prod_right'
  have he := laplace_triangle_lintegral hF p
  calc
    _ = ((n+1 : ℕ) : ℝ≥0∞)*(∫⁻ T : ℝ, laplaceWeight p T*
        (∫⁻ s in Ioo 0 T, ∫⁻ z : ℝ,
          realDensity 0 s x z*ENNReal.ofReal z*realDensity n (T-s) z y)) := by
      rw [resolvent,← lintegral_const_mul' _ _ (by simp)]
      apply lintegral_congr
      intro T
      rw [realDensity_succ]
      ac_rfl
    _ = _ := by rw [he]

/-- Actual killed moment resolvent insertion, with the two duration
transforms independently factored by Tonelli. Infinite transforms cause
no problem: no resolvent-finiteness assertion is used here. -/
theorem resolvent_succ (n : ℕ) (p x y : ℝ) :
    resolvent (n+1) p x y = ((n+1 : ℕ) : ℝ≥0∞)*∫⁻ z : ℝ,
      resolvent 0 p x z*ENNReal.ofReal z*resolvent n p z y := by
  rw [resolvent_succ_time_quadrant]
  congr 1
  have hDn (t : ℝ) : Measurable (fun z : ℝ ↦ realDensity n t z y) :=
    (measurable_realDensity n).comp (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  have hD0 (s : ℝ) : Measurable (fun z : ℝ ↦ realDensity 0 s x z) :=
    (measurable_realDensity 0).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hRn : Measurable (fun z : ℝ ↦ resolvent n p z y) :=
    (measurable_resolvent n p).comp (measurable_id.prodMk measurable_const)
  have hU (s : ℝ) : Measurable (fun q : ℝ × ℝ ↦
      laplaceWeight p s*laplaceWeight p q.1*
        (realDensity 0 s x q.2*ENNReal.ofReal q.2*realDensity n q.1 q.2 y)) :=
    (measurable_const.mul ((measurable_laplaceWeight p).comp measurable_fst)).mul
      ((((hD0 s).comp measurable_snd).mul measurable_snd.ennreal_ofReal).mul
        ((measurable_realDensity n).comp
          (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))))
  have hV : Measurable (fun q : ℝ × ℝ ↦
      laplaceWeight p q.1*realDensity 0 q.1 x q.2*ENNReal.ofReal q.2*resolvent n p q.2 y) :=
    ((((measurable_laplaceWeight p).comp measurable_fst).mul
      ((measurable_realDensity 0).comp (measurable_fst.prodMk
        (measurable_const.prodMk measurable_snd)))).mul measurable_snd.ennreal_ofReal).mul
          (hRn.comp measurable_snd)
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ), ∫⁻ z : ℝ,
        laplaceWeight p s*realDensity 0 s x z*ENNReal.ofReal z*resolvent n p z y := by
      apply lintegral_congr
      intro s
      calc
        _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ z : ℝ,
            laplaceWeight p s*laplaceWeight p t*
              (realDensity 0 s x z*ENNReal.ofReal z*realDensity n t z y) := by
          apply lintegral_congr
          intro t
          exact (lintegral_const_mul _ (((hD0 s).mul measurable_id.ennreal_ofReal).mul (hDn t))).symm
        _ = ∫⁻ z : ℝ, ∫⁻ t in Ioi (0 : ℝ),
            laplaceWeight p s*laplaceWeight p t*
              (realDensity 0 s x z*ENNReal.ofReal z*realDensity n t z y) :=
          lintegral_lintegral_swap (hU s).aemeasurable
        _ = _ := by
          apply lintegral_congr
          intro z
          rw [resolvent_eq_positive_realDensity]
          calc
            _ = ∫⁻ t in Ioi (0 : ℝ),
                (laplaceWeight p s*realDensity 0 s x z*ENNReal.ofReal z)*
                  (laplaceWeight p t*realDensity n t z y) := by
              apply lintegral_congr
              intro t
              ac_rfl
            _ = _ := lintegral_const_mul _
              (((measurable_laplaceWeight p).mul
                ((measurable_realDensity n).comp (measurable_id.prodMk
                  (measurable_const.prodMk measurable_const)))))
    _ = ∫⁻ z : ℝ, ∫⁻ s in Ioi (0 : ℝ),
        laplaceWeight p s*realDensity 0 s x z*ENNReal.ofReal z*resolvent n p z y :=
      lintegral_lintegral_swap hV.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      rw [resolvent_eq_positive_realDensity 0 p x z]
      calc
        _ = ∫⁻ s in Ioi (0 : ℝ), (laplaceWeight p s*realDensity 0 s x z)*
            (ENNReal.ofReal z*resolvent n p z y) := by
          apply lintegral_congr
          intro s
          ac_rfl
        _ = _ := by
          have hm : Measurable (fun s : ℝ ↦ laplaceWeight p s*realDensity 0 s x z) :=
            (measurable_laplaceWeight p).mul ((measurable_realDensity 0).comp
              (measurable_id.prodMk (measurable_const.prodMk measurable_const)))
          calc
            _ = (∫⁻ s in Ioi (0 : ℝ), laplaceWeight p s*realDensity 0 s x z)*
                (ENNReal.ofReal z*resolvent n p z y) := lintegral_mul_const _ hm
            _ = _ := by ac_rfl

/-- Every nonnegative Borel endpoint test is a genuine time transform
of the surviving Brownian path-area moment measure. -/
theorem resolvent_lintegral_eq_actual_momentLaw (n : ℕ) (p x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y : ℝ, resolvent n p x y*F y) =
      ∫⁻ T in Ioi (0 : ℝ), laplaceWeight p T*
        (∫⁻ y : ℝ, F y ∂momentLaw 0 n (Real.toNNReal T) x) := by
  have hD (y : ℝ) : Measurable (fun T : ℝ ↦ laplaceWeight p T*realDensity n T x y) :=
    (measurable_laplaceWeight p).mul ((measurable_realDensity n).comp
      (measurable_id.prodMk (measurable_const.prodMk measurable_const)))
  have hm : Measurable (fun q : ℝ × ℝ ↦ laplaceWeight p q.1*realDensity n q.1 x q.2*F q.2) :=
    (((measurable_laplaceWeight p).comp measurable_fst).mul
      ((measurable_realDensity n).comp (measurable_fst.prodMk
        (measurable_const.prodMk measurable_snd)))).mul (hF.comp measurable_snd)
  calc
    _ = ∫⁻ y : ℝ, ∫⁻ T : ℝ, laplaceWeight p T*realDensity n T x y*F y := by
      apply lintegral_congr
      intro y
      exact (lintegral_mul_const (F y) (hD y)).symm
    _ = ∫⁻ T : ℝ, ∫⁻ y : ℝ, laplaceWeight p T*realDensity n T x y*F y :=
      (lintegral_lintegral_swap hm.aemeasurable).symm
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro T
      by_cases hT : 0 < T
      · rw [indicator_of_mem (show T ∈ Ioi (0 : ℝ) from hT),
          momentLaw_lintegral_eq_density n (Real.toNNReal T) (Real.toNNReal_pos.mpr hT) x hF]
        calc
          _ = ∫⁻ y : ℝ, laplaceWeight p T*(density n (Real.toNNReal T,(x,y))*F y) := by
            apply lintegral_congr
            intro y
            rw [realDensity,if_pos hT]
            ac_rfl
          _ = _ := lintegral_const_mul _
            ((measurable_density_state n (Real.toNNReal T) x).mul hF)
      · simp only [realDensity,if_neg hT,mul_zero,zero_mul,lintegral_zero,
          indicator_of_notMem (show T ∉ Ioi (0 : ℝ) from hT)]

theorem resolvent_zero_of_nonpos_target (n : ℕ) (p x y : ℝ) (hy : y ≤ 0) :
    resolvent n p x y = 0 := by
  rw [resolvent_eq_positive_time_integral]
  simp only [BrownianKilledAreaMomentDensityBoundary.density_zero_of_nonpos_target n _ x y hy,
    mul_zero,lintegral_zero]

theorem resolvent_zero_of_nonpos_initial (n : ℕ) (p x y : ℝ) (hx : x ≤ 0) :
    resolvent n p x y = 0 := by
  rw [resolvent_eq_positive_time_integral]
  rw [← lintegral_zero (μ := volume.restrict (Ioi (0 : ℝ)))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
  rw [BrownianKilledAreaMomentDensityBoundary.density_zero_of_nonpos_initial n _
    (Real.toNNReal_pos.mpr hT) x y hx,mul_zero]

end PerronWright.BrownianKilledAreaMomentResolvent
