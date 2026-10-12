import PerronWright.Probability.BrownianMinimumFutureCoordinates
import PerronWright.Probability.BrownianMinimumEndpointTimeLimit
import PerronWright.Probability.BrownianMinimumEndpointJointLaw
import PerronWright.Probability.BrownianMinimumWindowNonnegativeLimit

/-! # Actual minimum and original future-observation numerical density

For bounded continuous tests supported before the first observation,
the genuine whole-future window formula and killed free-tuple entrance
limit identify the literal original path observations after the minimum.
Both depth and time exchanges use proved survival majorants.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumFutureCoordinateDensity

open BrownianPathLaw ContinuousPathFirstPassage ContinuousPathLeastMinimum
open BrownianFirstPassageEndpointGeometry BrownianMinimumFutureCoordinates
open BrownianMinimumWindowSurvivalBounds BrownianMinimumWindowNonnegativeLimit
open BrownianMinimumEndpointJointLaw BrownianKilledFreeEntranceTests
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledFiniteDimensionalOrderedDensity
open ContinuousPathMinimumFutureBandAverage

def coordinateKernel (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (δ s a : ℝ) : ℝ≥0∞ :=
  (∫⁻ g in survival (-δ) (remainingTime (times (Fin.last n)) s),
    ENNReal.ofReal (Φ (Real.toNNReal s,-a,fun i ↦ g (times i-Real.toNNReal s))) ∂pathLaw)/
    ENNReal.ofReal δ

theorem measurable_joint_coordinateKernel (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (δ : ℝ) :
    Measurable (fun p : ℝ × ℝ ↦ coordinateKernel n times Φ δ p.1 p.2) := by
  let T := times (Fin.last n)
  have hr : Measurable (fun q : (ℝ × ℝ) × Path ↦ remainingTime T q.1.1) :=
    (continuous_remainingTime T).measurable.comp measurable_fst.fst
  have hs : MeasurableSet {q : (ℝ × ℝ) × Path | q.2 ∈ survival (-δ) (remainingTime T q.1.1)} := by
    change MeasurableSet {q : (ℝ × ℝ) × Path | -δ <
      ContinuousPathReflection.runningMinimum q.2 (remainingTime T q.1.1)}
    exact measurableSet_lt measurable_const
      (BrownianPathReflectionLaw.continuous_joint_minimum.measurable.comp (measurable_snd.prodMk hr))
  have he : Measurable (fun q : (ℝ × ℝ) × Path ↦
      (Real.toNNReal q.1.1,-q.1.2,fun i : Fin (n+1) ↦ q.2 (times i-Real.toNNReal q.1.1))) :=
    measurable_fst.fst.real_toNNReal.prodMk (measurable_fst.snd.neg.prodMk
      (measurable_pi_lambda _ (fun i ↦ continuous_joint_eval.measurable.comp
        (measurable_snd.prodMk (measurable_const.sub measurable_fst.fst.real_toNNReal)))))
  have hm : Measurable (fun q : (ℝ × ℝ) × Path ↦
      if q.2 ∈ survival (-δ) (remainingTime T q.1.1) then
        ENNReal.ofReal (Φ (Real.toNNReal q.1.1,-q.1.2,
          fun i : Fin (n+1) ↦ q.2 (times i-Real.toNNReal q.1.1))) else 0) :=
    Measurable.ite hs (Φ.continuous.measurable.comp he).ennreal_ofReal measurable_const
  have h := hm.lintegral_prod_right' (ν := pathLaw) |>.div_const (ENNReal.ofReal δ)
  convert h using 1
  funext p
  rw [coordinateKernel,← lintegral_indicator (measurableSet_survival (-δ) (remainingTime T p.1))]
  rfl

theorem coordinateKernel_tendsto (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hstrict : StrictMono times) (s : ℝ) (hs : s ∈ Ioo 0 (times (Fin.last n) : ℝ))
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p)
    (hcut : ∀ t : ℝ≥0, times 0 ≤ t → ∀ a v, Φ (t,a,v) = 0) (a : ℝ) :
    Tendsto (fun δ : ℝ ↦ coordinateKernel n times Φ δ s a) (𝓝[>] 0)
      (𝓝 (∫⁻ v, ENNReal.ofReal (Φ (Real.toNNReal s,-a,v))
        ∂freeEntranceLaw n (orderedGaps (n+1) (residualSchedule n times (Real.toNNReal s))))) := by
  by_cases hbefore : Real.toNNReal s < times 0
  · have h := actual_residual_coordinates_entrance_tendsto n times hstrict
      (Real.toNNReal s) hbefore a Φ hΦ
    simpa only [coordinateKernel,remainingTime_eq_nnreal_sub _ s hs.1.le hs.2.le] using h
  · have he (v : FreeVector (n+1)) : Φ (Real.toNNReal s,-a,v) = 0 :=
      hcut _ (le_of_not_gt hbefore) _ _
    simp only [coordinateKernel,he,ENNReal.ofReal_zero,lintegral_zero,ENNReal.zero_div]
    exact tendsto_const_nhds

private theorem coordinateKernel_bound (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (δ : ℝ) (hδ : 0 < δ)
    (s a : ℝ) (hs : s < (times (Fin.last n) : ℝ)) :
    coordinateKernel n times Φ δ s a ≤ ENNReal.ofReal
      (‖Φ‖*(BrownianKilledSurvivalMoment.survivalCoefficient/
        Real.sqrt (remainingTime (times (Fin.last n)) s : ℝ))) := by
  have ht : 0 < remainingTime (times (Fin.last n)) s :=
    Real.toNNReal_pos.mpr (sub_pos.mpr hs)
  calc
    _ ≤ ENNReal.ofReal ‖Φ‖*(pathLaw (survival (-δ) (remainingTime (times (Fin.last n)) s))/
        ENNReal.ofReal δ) :=
      normalized_survival_test_bound δ _ ‖Φ‖ _ (fun g ↦ ENNReal.ofReal_le_ofReal
        ((le_abs_self _).trans (Φ.norm_coe_le_norm _)))
    _ ≤ ENNReal.ofReal ‖Φ‖*ENNReal.ofReal
        (BrownianKilledSurvivalMoment.survivalCoefficient/
          Real.sqrt (remainingTime (times (Fin.last n)) s : ℝ)) :=
      mul_le_mul' le_rfl (normalized_survival_path_mass_bound δ hδ _ ht)
    _ = _ := (ENNReal.ofReal_mul (norm_nonneg _)).symm

private theorem measurable_coordinateCandidate (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hstrict : StrictMono times) (s : ℝ)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ)
    (hcut : ∀ t : ℝ≥0, times 0 ≤ t → ∀ a v, Φ (t,a,v) = 0) :
    Measurable (fun a : ℝ ↦ ∫⁻ v,
      ENNReal.ofReal (Φ (Real.toNNReal s,-a,v))
        ∂freeEntranceLaw n (orderedGaps (n+1) (residualSchedule n times (Real.toNNReal s)))) := by
  by_cases hbefore : Real.toNNReal s < times 0
  · let := freeEntranceLaw_isFinite n
      (orderedGaps (n+1) (residualSchedule n times (Real.toNNReal s)))
      (orderedGaps_positive (n+1) _ (residualSchedule_strictMono n times hstrict _ hbefore))
    have hp : Measurable (fun p : ℝ × FreeVector (n+1) ↦
        ENNReal.ofReal (Φ (Real.toNNReal s,-p.1,p.2))) :=
      (Φ.continuous.measurable.comp (measurable_const.prodMk
        (measurable_fst.neg.prodMk measurable_snd))).ennreal_ofReal
    exact hp.lintegral_prod_right'
  · simp only [hcut _ (le_of_not_gt hbefore),ENNReal.ofReal_zero,lintegral_zero]
    exact measurable_const

private theorem tendsto_weighted_depth {d : ℝ → ℝ≥0∞} (hd : Measurable d)
    {F : ℝ → ℝ → ℝ≥0∞} {q : ℝ → ℝ≥0∞}
    (hF : ∀ δ, Measurable (F δ)) (hq : Measurable q)
    (h : Tendsto (fun δ ↦ ∫⁻ a, F δ a ∂(volume.restrict (Ioi (0 : ℝ))).withDensity d)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫⁻ a, q a ∂(volume.restrict (Ioi (0 : ℝ))).withDensity d))) :
    Tendsto (fun δ ↦ ∫⁻ a in Ioi (0 : ℝ), d a*F δ a) (𝓝[>] (0 : ℝ))
      (𝓝 (∫⁻ a in Ioi (0 : ℝ), d a*q a)) := by
  conv at h =>
    enter [3,1]
    rw [lintegral_withDensity_eq_lintegral_mul _ hd hq]
  exact h.congr (fun δ ↦ lintegral_withDensity_eq_lintegral_mul _ hd (hF δ))

private theorem depth_dominated_limit (s : ℝ) (hs : 0 < s) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (F : ℝ → ℝ → ℝ≥0∞) (q : ℝ → ℝ≥0∞) (hF : ∀ δ, Measurable (F δ))
    (hq : Measurable q) (hb : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ a, F δ a ≤ C)
    (hl : ∀ a, Tendsto (fun δ : ℝ ↦ F δ a) (𝓝[>] 0) (𝓝 (q a))) :
    Tendsto (fun δ : ℝ ↦ ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*F δ a) (𝓝[>] 0)
      (𝓝 (∫⁻ a in Ioi (0 : ℝ), BrownianFirstPassageDensityGeometry.density a s*q a)) := by
  let d := fun a : ℝ ↦ BrownianFirstPassageDensityGeometry.density a s
  have hd : Measurable d := BrownianHeatResolvent.measurable_joint_passageDensity.comp
    (measurable_id.prodMk measurable_const)
  let μ : Measure ℝ := (volume.restrict (Ioi (0 : ℝ))).withDensity d
  have hmass : μ univ = ENNReal.ofReal (1/(Real.sqrt (2*Real.pi)*Real.sqrt s)) := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact passage_level_mass s hs
  let : IsFiniteMeasure μ := ⟨by rw [hmass]; exact ENNReal.ofReal_lt_top⟩
  have hbd : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ a ∂μ, F δ a ≤ C := by
    filter_upwards [hb] with δ hδ
    exact Eventually.of_forall hδ
  have hfin : (∫⁻ _a, C ∂μ) ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top hC (measure_ne_top _ _)
  have ht := tendsto_lintegral_filter_of_dominated_convergence (μ := μ) (fun _ ↦ C)
    (Eventually.of_forall hF) hbd hfin (Eventually.of_forall hl)
  exact tendsto_weighted_depth hd hF hq ht

theorem level_coordinateKernel_tendsto (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hstrict : StrictMono times) (s : ℝ) (hs : s ∈ Ioo 0 (times (Fin.last n) : ℝ))
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p)
    (hcut : ∀ t : ℝ≥0, times 0 ≤ t → ∀ a v, Φ (t,a,v) = 0) :
    Tendsto (fun δ : ℝ ↦ ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*coordinateKernel n times Φ δ s a) (𝓝[>] 0)
      (𝓝 (∫⁻ a in Ioi (0 : ℝ), BrownianFirstPassageDensityGeometry.density a s*
        ∫⁻ v, ENNReal.ofReal (Φ (Real.toNNReal s,-a,v))
          ∂freeEntranceLaw n (orderedGaps (n+1) (residualSchedule n times (Real.toNNReal s))))) := by
  have hm (δ : ℝ) : Measurable (fun a : ℝ ↦ coordinateKernel n times Φ δ s a) := by
    have h := (measurable_joint_coordinateKernel n times Φ δ).comp
      (measurable_const.prodMk measurable_id : Measurable (fun a : ℝ ↦ (s,a)))
    simpa only [Function.comp_def] using h
  apply depth_dominated_limit s hs.1 (ENNReal.ofReal
    (‖Φ‖*(BrownianKilledSurvivalMoment.survivalCoefficient/
      Real.sqrt (remainingTime (times (Fin.last n)) s : ℝ)))) ENNReal.ofReal_ne_top
    _ _ hm (measurable_coordinateCandidate n times hstrict s Φ hcut)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    intro a
    exact coordinateKernel_bound n times Φ δ hδ s a hs.2
  · exact coordinateKernel_tendsto n times hstrict s hs Φ hΦ hcut

theorem measurable_levelCoordinateKernel (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (δ : ℝ) :
    Measurable (fun s : ℝ ↦ ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*coordinateKernel n times Φ δ s a) :=
  ((BrownianHeatResolvent.measurable_joint_passageDensity.comp measurable_swap).mul
    (measurable_joint_coordinateKernel n times Φ δ)).lintegral_prod_right'

theorem time_coordinateKernel_tendsto (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hstrict : StrictMono times) (hT : 0 < times (Fin.last n))
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p)
    (hcut : ∀ t : ℝ≥0, times 0 ≤ t → ∀ a v, Φ (t,a,v) = 0) :
    Tendsto (fun δ : ℝ ↦ ∫⁻ s in Ioo 0 (times (Fin.last n) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*coordinateKernel n times Φ δ s a) (𝓝[>] 0)
      (𝓝 (∫⁻ s in Ioo 0 (times (Fin.last n) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          ∫⁻ v, ENNReal.ofReal (Φ (Real.toNNReal s,-a,v))
            ∂freeEntranceLaw n (orderedGaps (n+1) (residualSchedule n times (Real.toNNReal s))))) := by
  let T := times (Fin.last n)
  let C : ℝ := ‖Φ‖*majorantCoefficient
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) majorantCoefficient_nonneg
  have hm : ∀ᶠ δ : ℝ in 𝓝[>] 0, Measurable (fun s : ℝ ↦ ∫⁻ a in Ioi (0 : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*coordinateKernel n times Φ δ s a) :=
    Eventually.of_forall (measurable_levelCoordinateKernel n times Φ)
  have hb : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ᵐ s ∂volume.restrict (Ioo 0 (T : ℝ)),
      (∫⁻ a in Ioi (0 : ℝ), BrownianFirstPassageDensityGeometry.density a s*
        coordinateKernel n times Φ δ s a) ≤ ENNReal.ofReal (C*timeMajorant T s) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact normalized_level_survival_test_bound T s hs δ hδ ‖Φ‖ (norm_nonneg _) _
      (fun a _ g ↦ ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (Φ.norm_coe_le_norm _)))
  have hfin : (∫⁻ s in Ioo 0 (T : ℝ), ENNReal.ofReal (C*timeMajorant T s)) ≠ ∞ := by
    simp_rw [ENNReal.ofReal_mul hC]
    rw [lintegral_const_mul _ (measurable_timeMajorant T).ennreal_ofReal]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_timeMajorant_ne_top T hT)
  apply tendsto_lintegral_filter_of_dominated_convergence
    (fun s ↦ ENNReal.ofReal (C*timeMajorant T s)) hm hb hfin
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact level_coordinateKernel_tendsto n times hstrict s hs Φ hΦ hcut

theorem actual_window_eq_coordinateKernel (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (δ : ℝ) (hδ : 0 < δ) :
    (∫⁻ a in Ioi (0 : ℝ), ∫⁻ s in Iio (times (Fin.last n) : ℝ),
      BrownianFirstPassageDensityGeometry.density a s*
        ∫⁻ g in survival (-δ) (remainingTime (times (Fin.last n)) s),
          sourceTest (coordinateTest n times Φ) (a,s,g) ∂pathLaw)/ENNReal.ofReal δ =
      ∫⁻ s in Ioo 0 (times (Fin.last n) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*coordinateKernel n times Φ δ s a := by
  let T := times (Fin.last n)
  have hc : (ENNReal.ofReal δ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hδ)
  have he (a : ℝ) :
      (∫⁻ s in Iio (T : ℝ), BrownianFirstPassageDensityGeometry.density a s*
        ∫⁻ g in survival (-δ) (remainingTime T s),
          sourceTest (coordinateTest n times Φ) (a,s,g) ∂pathLaw)/ENNReal.ofReal δ =
      ∫⁻ s in Ioo 0 (T : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*coordinateKernel n times Φ δ s a := by
    rw [div_eq_mul_inv,← lintegral_mul_const' _ _ hc]
    rw [show Ioo 0 (T : ℝ) = Ioi 0 ∩ Iio (T : ℝ) by ext s; rfl,
      ← setLIntegral_indicator measurableSet_Ioi]
    apply setLIntegral_congr_fun measurableSet_Iio
    intro s hsT
    by_cases hs : 0 < s
    · simp only [indicator_of_mem (show s ∈ Ioi 0 from hs),sourceTest,coordinateTest,
        BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,coordinateMap,
        coordinateKernel,div_eq_mul_inv,mul_assoc,T]
    · have hd : BrownianFirstPassageDensityGeometry.density a s = 0 := by
        rw [BrownianFirstPassageDensityGeometry.density,
          BrownianFirstPassageDensityGeometry.densityReal_eq_zero_of_nonpos a s (le_of_not_gt hs),
          ENNReal.ofReal_zero]
      simp only [indicator_of_notMem (show s ∉ Ioi 0 from hs),hd,zero_mul]
  calc
    _ = ∫⁻ a in Ioi (0 : ℝ),
        (∫⁻ s in Iio (T : ℝ), BrownianFirstPassageDensityGeometry.density a s*
          ∫⁻ g in survival (-δ) (remainingTime T s),
            sourceTest (coordinateTest n times Φ) (a,s,g) ∂pathLaw)/ENNReal.ofReal δ := by
      simp only [div_eq_mul_inv]
      exact (lintegral_mul_const' _ _ hc).symm
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ s in Ioo 0 (T : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*coordinateKernel n times Φ δ s a :=
      lintegral_congr he
    _ = _ := (lintegral_lintegral_swap
      ((BrownianHeatResolvent.measurable_joint_passageDensity.comp measurable_swap).mul
        (measurable_joint_coordinateKernel n times Φ δ)).aemeasurable).symm

theorem coordinateTest_minimumPoint_of_support (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hstrict : StrictMono times) (T : ℝ≥0)
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ)
    (hcut : ∀ t : ℝ≥0, times 0 ≤ t → ∀ a v, Φ (t,a,v) = 0) (f : Path) :
    coordinateTest n times Φ (minimumPoint T f) =
      Φ (leastMinimizer T f,minimumValue T f,fun i ↦ f (times i)-minimumValue T f) := by
  by_cases hbefore : leastMinimizer T f < times 0
  · exact coordinateTest_minimumPoint n times Φ T f (fun i ↦
      hbefore.le.trans (hstrict.monotone (Fin.zero_le i)))
  · change Φ (leastMinimizer T f,minimumValue T f,_) = _
    rw [hcut _ (le_of_not_gt hbefore),hcut _ (le_of_not_gt hbefore)]

theorem actual_minimum_original_coordinate_density (n : ℕ) (times : Fin (n+1) → ℝ≥0)
    (hstrict : StrictMono times) (hT : 0 < times (Fin.last n))
    (Φ : (ℝ≥0 × ℝ × FreeVector (n+1)) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p)
    (hcut : ∀ t : ℝ≥0, times 0 ≤ t → ∀ a v, Φ (t,a,v) = 0) :
    (∫⁻ f, ENNReal.ofReal (Φ (leastMinimizer (times (Fin.last n)) f,
      minimumValue (times (Fin.last n)) f,
      fun i ↦ f (times i)-minimumValue (times (Fin.last n)) f)) ∂pathLaw) =
      ∫⁻ s in Ioo 0 (times (Fin.last n) : ℝ), ∫⁻ a in Ioi (0 : ℝ),
        BrownianFirstPassageDensityGeometry.density a s*
          ∫⁻ v, ENNReal.ofReal (Φ (Real.toNNReal s,-a,v))
            ∂freeEntranceLaw n (orderedGaps (n+1) (residualSchedule n times (Real.toNNReal s))) := by
  have h := actual_future_density_limit (times (Fin.last n)) hT (coordinateTest n times Φ)
    (fun p ↦ hΦ _)
  simp_rw [coordinateTest_minimumPoint_of_support n times hstrict _ Φ hcut] at h
  have he := time_coordinateKernel_tendsto n times hstrict hT Φ hΦ hcut
  have hh := he.congr' (show ∀ᶠ δ : ℝ in 𝓝[>] 0, _ = _ from by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (actual_window_eq_coordinateKernel n times Φ δ hδ).symm)
  exact tendsto_nhds_unique h hh

end PerronWright.BrownianMinimumFutureCoordinateDensity
