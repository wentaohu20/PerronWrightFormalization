import PerronWright.Probability.BrownianMinimumWindowLevelAverage
import PerronWright.Probability.BrownianPathFiniteReversal

/-! # Actual normalized level windows converge to the Brownian minimum law

The negative-level restriction truncates the unit band, but it disappears
pathwise because the actual Brownian minimum is negative. A uniform
bounded-test estimate permits dominated convergence under the actual path
law. The limiting time, depth and entire future are identified from first
passage convergence, not assumed as a distributional interface.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumWindowActualLimit

open BrownianPathLaw ContinuousPathLeastMinimum
open BrownianMinimumWindowLevelAverage ContinuousPathMinimumFutureBandAverage

theorem measurable_truncatedUnitBandAverage (T : ℝ≥0)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) :
    Measurable (fun q : ℝ × Path ↦ truncatedUnitBandAverage T Ψ q.1 q.2) := by
  have hb := measurable_joint_bandPoint T
  have hl := hb.snd.fst
  have htest : Measurable (fun q : (ℝ × Path) × ℝ ↦
      if minimumValue T q.1.2+q.1.1*q.2 < 0 then
        Ψ (bandPoint T q.1.1 q.1.2 q.2) else (0 : ℝ)) :=
    Measurable.ite (measurableSet_lt hl measurable_const)
      (Ψ.continuous.measurable.comp hb) measurable_const
  exact (htest.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable

theorem norm_truncatedUnitBandAverage_le (T : ℝ≥0)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (δ : ℝ) (f : Path) :
    ‖truncatedUnitBandAverage T Ψ δ f‖ ≤ ‖Ψ‖ := by
  let : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])
  have hb (θ : ℝ) :
      ‖if minimumValue T f+δ*θ < 0 then Ψ (bandPoint T δ f θ) else 0‖ ≤ ‖Ψ‖ := by
    split_ifs
    · exact Ψ.norm_coe_le_norm _
    · simp
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (Eventually.of_forall hb)
  simpa only [truncatedUnitBandAverage,Measure.real,Measure.restrict_apply_univ,
    Real.volume_Ioc,sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,mul_one] using h

theorem integrable_truncatedUnitBandAverage (T : ℝ≥0)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (δ : ℝ) (μ : Measure Path) [IsFiniteMeasure μ] :
    Integrable (truncatedUnitBandAverage T Ψ δ) μ := by
  apply (integrable_const ‖Ψ‖).mono'
  · exact ((measurable_truncatedUnitBandAverage T Ψ).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact Eventually.of_forall (norm_truncatedUnitBandAverage_le T Ψ δ)

theorem truncatedUnitBandAverage_eq_unit (T : ℝ≥0)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (δ : ℝ) (hδ : 0 < δ) (f : Path)
    (hdepth : δ < -minimumValue T f) :
    truncatedUnitBandAverage T Ψ δ f = unitBandAverage T Ψ δ f := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  have ht : δ*θ ≤ δ := by nlinarith [hθ.2]
  have hn : minimumValue T f+δ*θ < 0 := by linarith
  simp only [if_pos hn]

theorem tendsto_truncatedUnitBandAverage (T : ℝ≥0) (f : Path)
    (hnegative : minimumValue T f < 0) (hstart : minimumValue T f < f 0)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) :
    Tendsto (fun δ : ℝ ↦ truncatedUnitBandAverage T Ψ δ f) (𝓝[>] 0)
      (𝓝 (Ψ (minimumPoint T f))) := by
  apply (tendsto_unitBandAverage T f hstart Ψ).congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (neg_pos.mpr hnegative)).filter_mono nhdsWithin_le_nhds]
      with δ hδ hdepth
  exact (truncatedUnitBandAverage_eq_unit T Ψ δ hδ f hdepth).symm

theorem tendsto_integral_truncatedUnitBandAverage (T : ℝ≥0)
    (μ : Measure Path) [IsFiniteMeasure μ]
    (hnegative : ∀ᵐ f ∂μ, minimumValue T f < 0)
    (hstart : ∀ᵐ f ∂μ, minimumValue T f < f 0)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) :
    Tendsto (fun δ : ℝ ↦ ∫ f, truncatedUnitBandAverage T Ψ δ f ∂μ) (𝓝[>] 0)
      (𝓝 (∫ f, Ψ (minimumPoint T f) ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖Ψ‖)
  · exact Eventually.of_forall (fun δ ↦ ((measurable_truncatedUnitBandAverage T Ψ).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun δ ↦ Eventually.of_forall
      (norm_truncatedUnitBandAverage_le T Ψ δ))
  · exact integrable_const ‖Ψ‖
  · filter_upwards [hnegative,hstart] with f hn hs
    exact tendsto_truncatedUnitBandAverage T f hn hs Ψ

theorem ae_levelWindowAverage_eq_truncated (T : ℝ≥0) (hT : 0 < T)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (δ : ℝ) (hδ : 0 < δ) :
    levelWindowAverage T Ψ δ =ᵐ[pathLaw] truncatedUnitBandAverage T Ψ δ := by
  filter_upwards [BrownianPathFiniteReversal.ae_leastMinimizer_interior T hT] with f hf
  exact levelWindowAverage_eq_truncated T Ψ δ hδ f hf.2

theorem integrable_levelWindowAverage (T : ℝ≥0) (hT : 0 < T)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (δ : ℝ) (hδ : 0 < δ) :
    Integrable (levelWindowAverage T Ψ δ) pathLaw :=
  (integrable_truncatedUnitBandAverage T Ψ δ pathLaw).congr
    (ae_levelWindowAverage_eq_truncated T hT Ψ δ hδ).symm

theorem actual_level_window_limit (T : ℝ≥0) (hT : 0 < T)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) :
    Tendsto (fun δ : ℝ ↦ ∫ f, levelWindowAverage T Ψ δ f ∂pathLaw) (𝓝[>] 0)
      (𝓝 (∫ f, Ψ (minimumPoint T f) ∂pathLaw)) := by
  apply (tendsto_integral_truncatedUnitBandAverage T pathLaw
    (BrownianMinimumNegative.ae_minimumValue_negative T hT)
    (BrownianMinimumNegative.ae_minimumValue_lt_start T hT) Ψ).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (integral_congr_ae (ae_levelWindowAverage_eq_truncated T hT Ψ δ hδ)).symm

end PerronWright.BrownianMinimumWindowActualLimit
