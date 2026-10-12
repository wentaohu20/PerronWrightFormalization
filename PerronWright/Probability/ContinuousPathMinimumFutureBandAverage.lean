import PerronWright.Probability.ContinuousPathMinimumBandAverage

/-! # Genuine minimum-band averages retaining the entire future path

The true passage future is evaluated along the levels in the unit band
above a continuous path's minimum. The proved first-hit convergence and
joint continuity of the future-path map identify the actual limiting
whole future at the earliest minimizer. Bounded continuous tests pass
through both the unit-band integral and any finite path measure. Neither
minimum uniqueness nor a pathwise or distributional limit is assumed.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.ContinuousPathMinimumFutureBandAverage

open BrownianPathLaw ContinuousPathFirstPassage ContinuousPathLeastMinimum
open BrownianFirstPassageUncappedLaw BrownianPathIndependentIncrements
open BrownianFirstPassagePastFibers

def bandPoint (T : ℝ≥0) (δ : ℝ) (f : Path) (θ : ℝ) : ℝ≥0 × ℝ × Path :=
  (passageTime (minimumValue T f+δ*θ) f,minimumValue T f+δ*θ,
    passageFuture (minimumValue T f+δ*θ) f)

def minimumPoint (T : ℝ≥0) (f : Path) : ℝ≥0 × ℝ × Path :=
  (leastMinimizer T f,minimumValue T f,futurePath (leastMinimizer T f) f)

theorem measurable_joint_bandPoint (T : ℝ≥0) :
    Measurable (fun q : (ℝ × Path) × ℝ ↦ bandPoint T q.1.1 q.1.2 q.2) := by
  have h := ContinuousPathMinimumBandAverage.measurable_joint_bandPoint T
  have hf : Measurable (fun q : (ℝ × Path) × ℝ ↦ q.1.2) :=
    measurable_snd.comp measurable_fst
  exact h.fst.prodMk (h.snd.fst.prodMk
    (continuous_joint_futurePath.measurable.comp (h.fst.prodMk hf)))

theorem measurable_minimumPoint (T : ℝ≥0) : Measurable (minimumPoint T) :=
  (measurable_leastMinimizer T).prodMk ((continuous_minimumValue T).measurable.prodMk
    (continuous_joint_futurePath.measurable.comp
      ((measurable_leastMinimizer T).prodMk measurable_id)))

def unitBandAverage (T : ℝ≥0) (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (δ : ℝ) (f : Path) : ℝ :=
  ∫ θ : ℝ in Ioc 0 1, Ψ (bandPoint T δ f θ)

theorem measurable_unitBandAverage (T : ℝ≥0) (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) :
    Measurable (fun q : ℝ × Path ↦ unitBandAverage T Ψ q.1 q.2) :=
  ((Ψ.continuous.measurable.comp (measurable_joint_bandPoint T)).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable

theorem norm_unitBandAverage_le (T : ℝ≥0) (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ)
    (δ : ℝ) (f : Path) : ‖unitBandAverage T Ψ δ f‖ ≤ ‖Ψ‖ := by
  let : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (Eventually.of_forall (fun θ ↦ Ψ.norm_coe_le_norm (bandPoint T δ f θ)))
  simpa only [unitBandAverage,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
    sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,mul_one] using h

theorem tendsto_bandPoint (T : ℝ≥0) (f : Path)
    (hstart : minimumValue T f < f 0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Tendsto (fun δ : ℝ ↦ bandPoint T δ f θ) (𝓝[>] 0) (𝓝 (minimumPoint T f)) := by
  have h := ContinuousPathMinimumBandAverage.tendsto_bandPoint T f hstart θ hθ
  have ht := h.fst_nhds
  have hl := h.snd_nhds.fst_nhds
  have hf := continuous_joint_futurePath.tendsto (leastMinimizer T f,f) |>.comp
    (ht.prodMk_nhds tendsto_const_nhds)
  exact ht.prodMk_nhds (hl.prodMk_nhds hf)

theorem tendsto_unitBandAverage (T : ℝ≥0) (f : Path)
    (hstart : minimumValue T f < f 0) (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) :
    Tendsto (fun δ : ℝ ↦ unitBandAverage T Ψ δ f) (𝓝[>] 0)
      (𝓝 (Ψ (minimumPoint T f))) := by
  let : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.mpr (by simp [Real.volume_Ioc])
  have he : (∫ θ : ℝ in Ioc 0 1, Ψ (minimumPoint T f)) = Ψ (minimumPoint T f) := by
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
    (hstart : ∀ᵐ f ∂μ, minimumValue T f < f 0) (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) :
    Tendsto (fun δ : ℝ ↦ ∫ f, unitBandAverage T Ψ δ f ∂μ) (𝓝[>] 0)
      (𝓝 (∫ f, Ψ (minimumPoint T f) ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖Ψ‖)
  · exact Eventually.of_forall (fun δ ↦ ((measurable_unitBandAverage T Ψ).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun δ ↦ Eventually.of_forall (norm_unitBandAverage_le T Ψ δ))
  · exact integrable_const ‖Ψ‖
  · exact hstart.mono (fun f hf ↦ tendsto_unitBandAverage T f hf Ψ)

end PerronWright.ContinuousPathMinimumFutureBandAverage
