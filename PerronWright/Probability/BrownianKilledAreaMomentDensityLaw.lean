import PerronWright.Probability.BrownianKilledAreaMomentDensity

/-! # Density of the actual all-order surviving Brownian area moment law

The literal recursively constructed density is identified with the actual
path-area moment measure, using the proved all-order Kac insertion and
the actual Gaussian-difference transition law. No moment-finiteness or
moment-density identity is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentDensityLaw

open BrownianPathLaw BrownianKilledSemigroup BrownianKilledTransitionKernel
open BrownianKilledAreaMomentKernel BrownianKilledAreaMomentRecursion
open BrownianPositiveKilledKernel BrownianKilledAreaMomentDensity

theorem measurable_raw_insertion_test (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : ℝ × (ℝ × ℝ) ↦
      BrownianPositiveKilledEndpoint.density x (Real.toNNReal p.1) p.2.1*
        ENNReal.ofReal p.2.1*density n (T-Real.toNNReal p.1,(p.2.1,p.2.2))*F p.2.2) := by
  have hs : Measurable (fun p : ℝ × (ℝ × ℝ) ↦ Real.toNNReal p.1) :=
    continuous_real_toNNReal.measurable.comp measurable_fst
  have hz : Measurable (fun p : ℝ × (ℝ × ℝ) ↦ p.2.1) := measurable_fst.comp measurable_snd
  have hy : Measurable (fun p : ℝ × (ℝ × ℝ) ↦ p.2.2) := measurable_snd.comp measurable_snd
  exact (((measurable_time_joint_density.comp
    (hs.prodMk (measurable_const.prodMk hz))).mul hz.ennreal_ofReal).mul
    ((measurable_density n).comp ((measurable_const.sub hs).prodMk (hz.prodMk hy)))).mul (hF.comp hy)

theorem density_lintegral_succ (n : ℕ) (T : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, density (n+1) (T,(x,y))*F y) =
      ((n+1 : ℕ) : ℝ≥0∞)*∫⁻ r in Ioo 0 (T : ℝ), ∫⁻ z : ℝ,
        BrownianPositiveKilledEndpoint.density x (Real.toNNReal r) z*ENNReal.ofReal z*
          (∫⁻ y, density n (T-Real.toNNReal r,(z,y))*F y) := by
  have hm := measurable_raw_insertion_test n T x hF
  have heY (y : ℝ) :
      (∫⁻ r in Ioo 0 (T : ℝ), ∫⁻ z : ℝ,
        BrownianPositiveKilledEndpoint.density x (Real.toNNReal r) z*ENNReal.ofReal z*
          density n (T-Real.toNNReal r,(z,y)))*F y =
      ∫⁻ r in Ioo 0 (T : ℝ), ∫⁻ z : ℝ,
        BrownianPositiveKilledEndpoint.density x (Real.toNNReal r) z*ENNReal.ofReal z*
          density n (T-Real.toNNReal r,(z,y))*F y := by
    have hs : Measurable (fun p : ℝ × ℝ ↦ Real.toNNReal p.1) :=
      continuous_real_toNNReal.measurable.comp measurable_fst
    have hp : Measurable (fun p : ℝ × ℝ ↦
        BrownianPositiveKilledEndpoint.density x (Real.toNNReal p.1) p.2*ENNReal.ofReal p.2*
          density n (T-Real.toNNReal p.1,(p.2,y))) :=
      ((measurable_time_joint_density.comp
        (hs.prodMk (measurable_const.prodMk measurable_snd))).mul
          measurable_snd.ennreal_ofReal).mul ((measurable_density n).comp
            ((measurable_const.sub hs).prodMk (measurable_snd.prodMk measurable_const)))
    rw [← lintegral_mul_const _ hp.lintegral_prod_right']
    apply lintegral_congr
    intro r
    exact (lintegral_mul_const (F y)
      (hp.comp (measurable_const.prodMk measurable_id : Measurable (fun z : ℝ ↦ (r,z))))).symm
  have hrY : Measurable (fun p : ℝ × ℝ ↦ ∫⁻ z : ℝ,
      BrownianPositiveKilledEndpoint.density x (Real.toNNReal p.1) z*ENNReal.ofReal z*
        density n (T-Real.toNNReal p.1,(z,p.2))*F p.2) :=
    (hm.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)) :
        Measurable (fun p : (ℝ × ℝ) × ℝ ↦ (p.1.1,(p.2,p.1.2))))).lintegral_prod_right'
  calc
    _ = ((n+1 : ℕ) : ℝ≥0∞)*∫⁻ y, ∫⁻ r in Ioo 0 (T : ℝ), ∫⁻ z : ℝ,
        BrownianPositiveKilledEndpoint.density x (Real.toNNReal r) z*ENNReal.ofReal z*
          density n (T-Real.toNNReal r,(z,y))*F y := by
      rw [← lintegral_const_mul' _ _ (by simp)]
      apply lintegral_congr
      intro y
      rw [density_succ,← heY,mul_assoc]
    _ = ((n+1 : ℕ) : ℝ≥0∞)*∫⁻ r in Ioo 0 (T : ℝ), ∫⁻ y : ℝ, ∫⁻ z : ℝ,
        BrownianPositiveKilledEndpoint.density x (Real.toNNReal r) z*ENNReal.ofReal z*
          density n (T-Real.toNNReal r,(z,y))*F y := by
      rw [← lintegral_lintegral_swap (μ := volume.restrict (Ioo (0 : ℝ) (T : ℝ)))
        (ν := (volume : Measure ℝ))
        (f := fun r : ℝ ↦ fun y : ℝ ↦ ∫⁻ z : ℝ,
          BrownianPositiveKilledEndpoint.density x (Real.toNNReal r) z*ENNReal.ofReal z*
            density n (T-Real.toNNReal r,(z,y))*F y) hrY.aemeasurable]
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro r
      have hp : Measurable (fun p : ℝ × ℝ ↦
          BrownianPositiveKilledEndpoint.density x (Real.toNNReal r) p.1*ENNReal.ofReal p.1*
            density n (T-Real.toNNReal r,(p.1,p.2))*F p.2) :=
        (((measurable_time_joint_density.comp
          (measurable_const.prodMk (measurable_const.prodMk measurable_fst))).mul
            measurable_fst.ennreal_ofReal).mul ((measurable_density n).comp
              (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))).mul
                (hF.comp measurable_snd)
      rw [← lintegral_lintegral_swap (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ))
        (f := fun z : ℝ ↦ fun y : ℝ ↦
          BrownianPositiveKilledEndpoint.density x (Real.toNNReal r) z*ENNReal.ofReal z*
            density n (T-Real.toNNReal r,(z,y))*F y) hp.aemeasurable]
      apply lintegral_congr
      intro z
      simpa only [mul_assoc,Pi.mul_apply] using lintegral_const_mul (μ := (volume : Measure ℝ))
        (f := fun y : ℝ ↦ density n (T-Real.toNNReal r,(z,y))*F y)
        (BrownianPositiveKilledEndpoint.density x (Real.toNNReal r) z*ENNReal.ofReal z)
        ((measurable_density_state n (T-Real.toNNReal r) z).mul hF)

/-- Every positive-duration actual surviving Brownian area-moment law
has the displayed recursively constructed Gaussian-insertion density. -/
theorem momentLaw_lintegral_eq_density (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (x : ℝ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂momentLaw 0 n T x) = ∫⁻ y, density n (T,(x,y))*F y := by
  induction n generalizing T x with
  | zero =>
    rw [momentLaw_zero,transitionLaw_zero_eq_law,
      BrownianPositiveKilledKernel.law_eq_withDensity_all x T hT,
      lintegral_withDensity_eq_lintegral_mul volume
        (BrownianPositiveKilledEndpoint.measurable_density x T) hF]
    rfl
  | succ n ih =>
    rw [momentLaw_lintegral_insertion 0 T x n hF,density_lintegral_succ n T x hF,
      ← restrict_Ioo_eq_restrict_Ioc (μ := volume) (a := (0 : ℝ)) (b := (T : ℝ))]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hs : 0 < Real.toNNReal r := Real.toNNReal_pos.mpr hr.1
    have hlt : Real.toNNReal r < T := by
      have he : (Real.toNNReal r : ℝ) < T := by
        rw [Real.coe_toNNReal _ hr.1.le]
        exact hr.2
      exact_mod_cast he
    have htail : 0 < T-Real.toNNReal r := tsub_pos_iff_lt.mpr hlt
    have hH : Measurable (fun z : ℝ ↦ ENNReal.ofReal (z-0)*
        (∫⁻ y, F y ∂momentLaw 0 n (T-Real.toNNReal r) z)) :=
      (measurable_id.sub_const 0).ennreal_ofReal.mul
        (measurable_momentLaw_lintegral 0 n (T-Real.toNNReal r) hF)
    rw [transitionLaw_zero_eq_law,BrownianPositiveKilledKernel.law_eq_withDensity_all x _ hs,
      lintegral_withDensity_eq_lintegral_mul volume
        (BrownianPositiveKilledEndpoint.measurable_density x _) hH]
    apply lintegral_congr
    intro z
    simp only [Pi.mul_apply]
    rw [ih _ htail z,sub_zero,mul_assoc]

theorem momentLaw_eq_withDensity (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    momentLaw 0 n T x = volume.withDensity (fun y : ℝ ↦ density n (T,(x,y))) := by
  ext B hB
  rw [← lintegral_indicator_one hB,← lintegral_indicator_one hB,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_density_state n T x)
      (measurable_one.indicator hB)]
  exact momentLaw_lintegral_eq_density n T hT x (measurable_one.indicator hB)

end PerronWright.BrownianKilledAreaMomentDensityLaw
