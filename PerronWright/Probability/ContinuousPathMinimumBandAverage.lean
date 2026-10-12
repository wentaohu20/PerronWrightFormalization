import PerronWright.Probability.BrownianFirstPassageMinimumApproximation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual minimum-band averaging limit

A unit interval parametrizes the genuine height band just above a path's
minimum. First hits converge to its earliest minimizer, and bounded
continuous tests pass through the band integral by dominated convergence.
The same bound permits integration over any finite path measure. No
minimum uniqueness, pathwise limit or uniform-integrability premise is
inserted into the conclusion.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.ContinuousPathMinimumBandAverage

open BrownianPathLaw ContinuousPathFirstPassage ContinuousPathLeastMinimum
open BrownianFirstPassageUncappedLaw BrownianFirstPassageMinimumApproximation

def bandPoint (T : ℝ≥0) (δ : ℝ) (f : Path) (θ : ℝ) : ℝ≥0 × ℝ × ℝ :=
  (passageTime (minimumValue T f+δ*θ) f,minimumValue T f+δ*θ,f T)

theorem measurable_joint_bandPoint (T : ℝ≥0) :
    Measurable (fun q : (ℝ × Path) × ℝ ↦ bandPoint T q.1.1 q.1.2 q.2) := by
  have hf : Measurable (fun q : (ℝ × Path) × ℝ ↦ q.1.2) :=
    measurable_snd.comp measurable_fst
  have hl : Measurable (fun q : (ℝ × Path) × ℝ ↦ minimumValue T q.1.2+q.1.1*q.2) :=
    ((continuous_minimumValue T).measurable.comp hf).add
      ((measurable_fst.comp measurable_fst).mul measurable_snd)
  exact (measurable_joint_firstPassage.comp (hl.prodMk hf)).ennreal_toNNReal.prodMk
    (hl.prodMk ((continuous_eval T).measurable.comp hf))

def unitBandAverage (T : ℝ≥0) (Ψ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (δ : ℝ) (f : Path) : ℝ :=
  ∫ θ : ℝ in Ioc 0 1, Ψ (bandPoint T δ f θ)

theorem measurable_unitBandAverage (T : ℝ≥0) (Ψ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) :
    Measurable (fun q : ℝ × Path ↦ unitBandAverage T Ψ q.1 q.2) :=
  ((Ψ.continuous.measurable.comp (measurable_joint_bandPoint T)).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable

theorem norm_unitBandAverage_le (T : ℝ≥0) (Ψ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ)
    (δ : ℝ) (f : Path) : ‖unitBandAverage T Ψ δ f‖ ≤ ‖Ψ‖ := by
  let : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (Eventually.of_forall (fun θ ↦ Ψ.norm_coe_le_norm (bandPoint T δ f θ)))
  simpa only [unitBandAverage,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
    sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,mul_one] using h

theorem tendsto_bandPoint (T : ℝ≥0) (f : Path)
    (hstart : minimumValue T f < f 0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto (fun δ : ℝ ↦ bandPoint T δ f θ) (𝓝[>] 0)
      (𝓝 (leastMinimizer T f,minimumValue T f,f T)) := by
  have hl : Tendsto (fun δ : ℝ ↦ minimumValue T f+δ*θ) (𝓝[>] 0)
      (𝓝 (minimumValue T f)) := by
    have hi : Tendsto (fun δ : ℝ ↦ δ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_mul,add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ minimumValue T f) (𝓝[>] 0)
        (𝓝 (minimumValue T f))).add (hi.mul_const θ)
  have hge : ∀ᶠ δ : ℝ in 𝓝[>] 0, minimumValue T f ≤ minimumValue T f+δ*θ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact le_add_of_nonneg_right (mul_nonneg hδ.le hθ)
  exact (tendsto_passageTime_to_leastMinimizer T f _ hl hge hstart).prodMk_nhds
    (hl.prodMk_nhds tendsto_const_nhds)

theorem tendsto_unitBandAverage (T : ℝ≥0) (f : Path)
    (hstart : minimumValue T f < f 0) (Ψ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) :
    Tendsto (fun δ : ℝ ↦ unitBandAverage T Ψ δ f) (𝓝[>] 0)
      (𝓝 (Ψ (leastMinimizer T f,minimumValue T f,f T))) := by
  let : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])
  have he : (∫ θ : ℝ in Ioc 0 1, Ψ (leastMinimizer T f,minimumValue T f,f T)) =
      Ψ (leastMinimizer T f,minimumValue T f,f T) := by
    simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
      sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,one_smul]
  rw [← he]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖Ψ‖)
  · exact Eventually.of_forall (fun δ ↦
      ((Ψ.continuous.measurable.comp (measurable_joint_bandPoint T)).comp
        ((measurable_const.prodMk measurable_const).prodMk measurable_id)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun _ ↦ Eventually.of_forall (fun θ ↦ Ψ.norm_coe_le_norm _))
  · exact integrable_const ‖Ψ‖
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact Ψ.continuous.tendsto _ |>.comp (tendsto_bandPoint T f hstart θ hθ.1.le)

theorem tendsto_integral_unitBandAverage (T : ℝ≥0) (μ : Measure Path) [IsFiniteMeasure μ]
    (hstart : ∀ᵐ f ∂μ, minimumValue T f < f 0) (Ψ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) :
    Tendsto (fun δ : ℝ ↦ ∫ f, unitBandAverage T Ψ δ f ∂μ) (𝓝[>] 0)
      (𝓝 (∫ f, Ψ (leastMinimizer T f,minimumValue T f,f T) ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖Ψ‖)
  · exact Eventually.of_forall (fun δ ↦ ((measurable_unitBandAverage T Ψ).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun δ ↦ Eventually.of_forall (norm_unitBandAverage_le T Ψ δ))
  · exact integrable_const ‖Ψ‖
  · exact hstart.mono (fun f hf ↦ tendsto_unitBandAverage T f hf Ψ)

end PerronWright.ContinuousPathMinimumBandAverage
