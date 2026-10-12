import PerronWright.Probability.BrownianKilledAreaTimeKernel

/-! # Actual survival-gated exponential area insertion

The nonnegative insertion identity is obtained from literal path calculus.
Both consecutive segments retain their actual survival gates. Nothing
about an endpoint-conditioned bridge or a stochastic insertion formula
is presumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaDuhamelPath

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianKilledAreaGeometry BrownianKilledAreaKernel BrownianKilledAreaSemigroup
open BrownianKilledAreaDuhamelGeometry BrownianKilledSemigroup

theorem head_height_nonneg (level x : ℝ) (T : ℝ≥0) (f : Path)
    (hf : f ∈ survival (level-x) T) (r : ℝ) (hr : r ≤ (T : ℝ)) :
    0 ≤ x-level+f (Real.toNNReal r) := by
  have he := (mem_survival_iff (level-x) T f).mp hf (Real.toNNReal r)
    (Real.toNNReal_le_iff_le_coe.mpr hr)
  linarith

theorem mixed_weights_eq_survival_indicator (level : ℝ) (u s t : ℝ≥0) (x : ℝ) (f : Path) :
    weight level u s x f*weight level 0 t (x+f s) (futurePath s f) =
      (survival (level-x) (s+t)).indicator
        (fun g : Path ↦ ENNReal.ofReal (Real.exp (-(u : ℝ)*shiftedArea level x s g))) f := by
  have hl : level-x-f s = level-(x+f s) := by ring
  by_cases hs : f ∈ survival (level-x) s
  · by_cases ht : futurePath s f ∈ survival (level-(x+f s)) t
    · have hst := (survival_add_iff (level-x) s t f).mpr ⟨hs,by simpa only [hl] using ht⟩
      rw [weight,weight,indicator_of_mem hs,indicator_of_mem ht,indicator_of_mem hst]
      simp only [NNReal.coe_zero,neg_zero,zero_mul,Real.exp_zero,ENNReal.ofReal_one,mul_one]
    · have hst : f ∉ survival (level-x) (s+t) := by
        intro h
        exact ht (by simpa only [hl] using ((survival_add_iff (level-x) s t f).mp h).2)
      simp only [weight,indicator_of_notMem ht,indicator_of_notMem hst,mul_zero]
  · have hst : f ∉ survival (level-x) (s+t) :=
      fun h ↦ hs ((survival_add_iff (level-x) s t f).mp h).1
    simp only [weight,indicator_of_notMem hs,indicator_of_notMem hst,zero_mul]

theorem exp_depletion_enn_of_survival (level : ℝ) (u T : ℝ≥0) (x : ℝ) (f : Path)
    (hf : f ∈ survival (level-x) T) :
    (1 : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-(u : ℝ)*shiftedArea level x T f)) +
      ENNReal.ofReal (u : ℝ)*∫⁻ r in Ioc 0 (T : ℝ),
        ENNReal.ofReal (x-level+f (Real.toNNReal r))*
          ENNReal.ofReal (Real.exp (-(u : ℝ)*realArea level x f r)) := by
  let g : ℝ → ℝ := fun r ↦
    (x-level+f (Real.toNNReal r))*Real.exp (-(u : ℝ)*realArea level x f r)
  have hc : Continuous g :=
    (continuous_const.add ((continuous_path f).comp continuous_real_toNNReal)).mul
      (Real.continuous_exp.comp ((continuous_realArea level x f).const_mul (-(u : ℝ))))
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) T)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg (head_height_nonneg level x T f hf r hr.2) (Real.exp_pos _).le
  have hi : Integrable g (volume.restrict (Ioc (0 : ℝ) T)) :=
    (hc.intervalIntegrable 0 T).1
  have hnn : 0 ≤ ∫ r in Ioc (0 : ℝ) T, g r := integral_nonneg_of_ae hn
  have hd := exp_area_depletion level x (u : ℝ) T f
  rw [intervalIntegral.integral_of_le T.coe_nonneg] at hd
  change 1-Real.exp (-(u : ℝ)*shiftedArea level x T f) =
    (u : ℝ)*∫ r in Ioc (0 : ℝ) T, g r at hd
  have he : 1 = Real.exp (-(u : ℝ)*shiftedArea level x T f)+
      (u : ℝ)*∫ r in Ioc (0 : ℝ) T, g r := by linarith
  have he' := congrArg ENNReal.ofReal he
  rw [ENNReal.ofReal_one,ENNReal.ofReal_add (Real.exp_pos _).le (mul_nonneg u.coe_nonneg hnn),
    ENNReal.ofReal_mul u.coe_nonneg,ofReal_integral_eq_lintegral_ofReal hi hn] at he'
  rw [he']
  congr 2
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact ENNReal.ofReal_mul (head_height_nonneg level x T f hf r hr.2)

def insertionWeight (level : ℝ) (u T : ℝ≥0) (x : ℝ) (r : ℝ) (f : Path) : ℝ≥0∞ :=
  weight level u (Real.toNNReal r) x f*
    weight level 0 (T-Real.toNNReal r) (x+f (Real.toNNReal r))
      (futurePath (Real.toNNReal r) f)*ENNReal.ofReal (x+f (Real.toNNReal r)-level)

/-- The literal surviving path weight splits into the fully weighted
endpoint weight and a time insertion with both actual segment gates. -/
theorem weight_depletion (level : ℝ) (u T : ℝ≥0) (x : ℝ) (f : Path) :
    weight level 0 T x f = weight level u T x f+
      ENNReal.ofReal (u : ℝ)*∫⁻ r in Ioc 0 (T : ℝ), insertionWeight level u T x r f := by
  by_cases hf : f ∈ survival (level-x) T
  · have hi : (∫⁻ r in Ioc 0 (T : ℝ),
        ENNReal.ofReal (x-level+f (Real.toNNReal r))*
          ENNReal.ofReal (Real.exp (-(u : ℝ)*realArea level x f r))) =
        ∫⁻ r in Ioc 0 (T : ℝ), insertionWeight level u T x r f := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hs : Real.toNNReal r ≤ T := Real.toNNReal_le_iff_le_coe.mpr hr.2
      rw [insertionWeight,mixed_weights_eq_survival_indicator,
        add_tsub_cancel_of_le hs,indicator_of_mem hf]
      rw [← realArea_at_nonnegative,Real.coe_toNNReal _ hr.1.le,
        show x+f (Real.toNNReal r)-level = x-level+f (Real.toNNReal r) by ring]
      exact mul_comm _ _
    rw [weight,weight,indicator_of_mem hf,indicator_of_mem hf]
    simp only [NNReal.coe_zero,neg_zero,zero_mul,Real.exp_zero,ENNReal.ofReal_one]
    rw [← hi]
    exact exp_depletion_enn_of_survival level u T x f hf
  · have hi : (∫⁻ r in Ioc 0 (T : ℝ), insertionWeight level u T x r f) = 0 := by
      calc
        (∫⁻ r in Ioc 0 (T : ℝ), insertionWeight level u T x r f) =
            ∫⁻ _r in Ioc 0 (T : ℝ), (0 : ℝ≥0∞) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          have hs : Real.toNNReal r ≤ T := Real.toNNReal_le_iff_le_coe.mpr hr.2
          rw [insertionWeight,mixed_weights_eq_survival_indicator,
            add_tsub_cancel_of_le hs,indicator_of_notMem hf,zero_mul]
        _ = 0 := by simp
    simp only [weight,indicator_of_notMem hf,hi,mul_zero,zero_add]

end PerronWright.BrownianKilledAreaDuhamelPath
