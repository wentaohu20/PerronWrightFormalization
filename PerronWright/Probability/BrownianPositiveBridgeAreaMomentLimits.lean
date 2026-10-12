import PerronWright.Probability.BrownianPositiveBridgeAreaOrderedTimes

/-! # All-order actual positive-bridge area moment limits

The target is the literal entrance-kernel moment integrated over the
whole finite time cube. Sorting is only used off the proved null set of
boundary and repeated times. The actual all-time moment bound supplies
dominated convergence; no path-limit or uniform-integrability input is
used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeAreaMomentLimits

open BrownianPathLaw BrownianBridgeCyclicArea BrownianPositiveBridgeConditioning
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianKilledFiniteDimensionalOrderedTimes BrownianKilledFiniteDimensionalOrderedDensity
open BrownianPositiveBridgeMultiPointCoordinates BrownianPositiveBridgeMultiPointOrderedLaw
open BrownianPositiveBridgeMultiPointEntrance BrownianPositiveBridgeMultiPointMass
open BrownianPositiveBridgeFiniteCoordinateMoments BrownianPositiveBridgeJointMomentLimits
open BrownianPositiveBridgeAreaMomentBounds BrownianPositiveBridgeAreaTimeMoments
open BrownianPositiveBridgeAreaOrderedTimes

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

def orderedEntranceTimeMoment (n : ℕ) (T : ℝ≥0) (τ : Fin (n+1) → ℝ) : ℝ≥0∞ :=
  ∫⁻ v : FreeVector (n+1), ENNReal.ofReal (∏ i, v i)
    ∂entranceLaw n (orderedGaps (n+2) (paddedTimes T τ))

def entranceTimeMoment (n : ℕ) (T : ℝ≥0) (τ : Fin (n+1) → ℝ) : ℝ≥0∞ :=
  if GoodTimes T τ then orderedEntranceTimeMoment n T τ else 0

def entranceAreaMoment (T : ℝ≥0) : ℕ → ℝ≥0∞
  | 0 => 1
  | n+1 => ∫⁻ τ, entranceTimeMoment n T τ ∂timeCube T (n+1)

theorem orderedEntranceTimeMoment_eq_kernel_integral (n : ℕ) (T : ℝ≥0) (τ : Fin (n+1) → ℝ) :
    orderedEntranceTimeMoment n T τ =
      ∫⁻ v : FreeVector (n+1), entranceProduct n (orderedGaps (n+2) (paddedTimes T τ)) v*
        ENNReal.ofReal (∏ i, v i) := by
  unfold orderedEntranceTimeMoment entranceLaw
  exact lintegral_withDensity_eq_lintegral_mul volume (measurable_entranceProduct n _)
    ((continuous_finsetProd _ (fun i _ ↦ continuous_apply i)).measurable.ennreal_ofReal)

theorem entranceAreaMoment_succ_eq_kernel_time_integral (n : ℕ) (T : ℝ≥0) :
    entranceAreaMoment T (n+1) = ∫⁻ τ : Fin (n+1) → ℝ,
      (if GoodTimes T τ then ∫⁻ v : FreeVector (n+1),
        entranceProduct n (orderedGaps (n+2) (paddedTimes T τ)) v*ENNReal.ofReal (∏ i, v i)
       else 0) ∂timeCube T (n+1) := by
  apply lintegral_congr
  intro τ
  unfold entranceTimeMoment
  by_cases h : GoodTimes T τ
  · simp only [if_pos h,orderedEntranceTimeMoment_eq_kernel_integral]
  · simp only [if_neg h]

theorem sourceTimeMoment_tendsto_at_good_times (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (τ : Fin (n+1) → ℝ) (hg : GoodTimes T τ) :
    Tendsto (fun a : ℝ ↦ sourceTimeMoment a T (n+1) τ) (𝓝[>] 0)
      (𝓝 (orderedEntranceTimeMoment n T τ)) := by
  have hs := strictMono_paddedTimes n T hT τ hg
  have hz := paddedTimes_zero T τ
  have hp : ∀ j < n+2, 0 < orderedGaps (n+2) (paddedTimes T τ) j :=
    fun j hj ↦ orderedGaps_positive (n+2) _ hs j hj
  let Ψ : FreeVector (n+1) → ℝ≥0∞ := fun v ↦ ENNReal.ofReal (∏ i, v i)
  have hm : Measurable Ψ :=
    (continuous_finsetProd _ (fun i _ ↦ continuous_apply i)).measurable.ennreal_ofReal
  have hb (v : FreeVector (n+1)) : Ψ v ≤ ENNReal.ofReal (1 : ℝ)*ENNReal.ofReal (radius v^(n+1)) := by
    rw [ENNReal.ofReal_one,one_mul]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ |∏ i, v i| := le_abs_self _
      _ ≤ _ := by simpa [monomial] using abs_monomial_le_radius_pow (fun _ : Fin (n+1) ↦ 1) v
  have he := actual_growth_test_lintegral_tendsto n (orderedGaps (n+2) (paddedTimes T τ))
    hp 1 (by norm_num) (n+1) Ψ hm hb
  have hfinal := sampleTime_orderedGaps (n+2) (paddedTimes T τ) hs.monotone hz (Fin.last (n+2))
  simp only [Fin.val_last,paddedTimes_last] at hfinal
  rw [hfinal,internalEval_orderedGaps (n+1) (paddedTimes T τ) hs.monotone hz] at he
  simpa only [Ψ,paddedTimes_internal,heightProduct_sorted,sourceTimeMoment,orderedEntranceTimeMoment] using he

theorem sourceTimeMoment_tendsto_ae (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ τ ∂timeCube T (n+1), Tendsto (fun a : ℝ ↦ sourceTimeMoment a T (n+1) τ)
      (𝓝[>] 0) (𝓝 (entranceTimeMoment n T τ)) := by
  filter_upwards [ae_timeCube_goodTimes T (n+1)] with τ hg
  simpa only [entranceTimeMoment,if_pos hg] using sourceTimeMoment_tendsto_at_good_times n T hT τ hg

theorem eventually_uniform_good_sourceTimeMoment_bound (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ τ : Fin d → ℝ, GoodTimes T τ →
      sourceTimeMoment a T d τ ≤ jointMomentBound T d d := by
  filter_upwards [eventually_uniform_finite_coordinate_moment T hT d d] with a hb
  intro τ hg
  exact (lintegral_mono (fun g ↦ heightProduct_le_radius_pow d τ g)).trans
    (hb (fun i ↦ Real.toNNReal (τ i))
      (fun i ↦ Real.toNNReal_le_iff_le_coe.mpr (hg.1 i).2.le))

theorem entranceTimeMoment_le_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T) (τ : Fin (n+1) → ℝ) :
    entranceTimeMoment n T τ ≤ jointMomentBound T (n+1) (n+1) := by
  by_cases hg : GoodTimes T τ
  · rw [entranceTimeMoment,if_pos hg]
    apply le_of_tendsto (sourceTimeMoment_tendsto_at_good_times n T hT τ hg)
    exact (eventually_uniform_good_sourceTimeMoment_bound T hT (n+1)).mono (fun a ha ↦ ha τ hg)
  · rw [entranceTimeMoment,if_neg hg]
    exact zero_le

theorem entranceAreaMoment_succ_bound (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    entranceAreaMoment T (n+1) ≤
      jointMomentBound T (n+1) (n+1)*ENNReal.ofReal (T : ℝ)^(n+1) := by
  calc
    _ ≤ ∫⁻ τ : Fin (n+1) → ℝ, jointMomentBound T (n+1) (n+1) ∂timeCube T (n+1) :=
      lintegral_mono (entranceTimeMoment_le_bound n T hT)
    _ = _ := by rw [lintegral_const,timeCube_univ]

theorem entranceAreaMoment_lt_top (T : ℝ≥0) (hT : 0 < T) (d : ℕ) : entranceAreaMoment T d < ∞ := by
  cases d with
  | zero => simp [entranceAreaMoment]
  | succ n =>
    apply lt_of_le_of_lt (entranceAreaMoment_succ_bound n T hT)
    exact ENNReal.mul_lt_top (jointMomentBound_lt_top T hT _ _) (by finiteness)

theorem aemeasurable_entranceTimeMoment (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    AEMeasurable (entranceTimeMoment n T) (timeCube T (n+1)) := by
  have hz : Tendsto (fun k : ℕ ↦ (1 : ℝ)/((k : ℝ)+1)) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat,?_⟩
    apply Eventually.of_forall
    intro k
    change 0 < (1 : ℝ)/((k : ℝ)+1)
    positivity
  apply ENNReal.aemeasurable_of_tendsto
    (f := fun k : ℕ ↦ sourceTimeMoment ((1 : ℝ)/((k : ℝ)+1)) T (n+1))
  · intro k
    exact (measurable_sourceTimeMoment _ (by positivity) T hT (n+1)).aemeasurable
  · exact (sourceTimeMoment_tendsto_ae n T hT).mono (fun _ ht ↦ ht.comp hz)

theorem actual_area_succ_moment_tendsto (n : ℕ) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun a : ℝ ↦ ∫⁻ g : Path, ENNReal.ofReal (pathArea T g^(n+1)) ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (entranceAreaMoment T (n+1))) := by
  have hfin : (∫⁻ τ : Fin (n+1) → ℝ, jointMomentBound T (n+1) (n+1) ∂timeCube T (n+1)) ≠ ∞ := by
    rw [lintegral_const,timeCube_univ]
    exact ENNReal.mul_ne_top (jointMomentBound_lt_top T hT _ _).ne (by finiteness)
  have hmeas : ∀ᶠ a : ℝ in 𝓝[>] 0, Measurable (sourceTimeMoment a T (n+1)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact measurable_sourceTimeMoment a ha T hT (n+1)
  have he := tendsto_lintegral_filter_of_dominated_convergence
    (μ := timeCube T (n+1)) (fun _ ↦ jointMomentBound T (n+1) (n+1))
    hmeas
    (eventually_uniform_sourceTimeMoment_bound T hT (n+1)) hfin (sourceTimeMoment_tendsto_ae n T hT)
  apply he.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (actual_area_moment_eq_time_integral a ha T hT (n+1)).symm

theorem actual_area_moment_tendsto (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    Tendsto (fun a : ℝ ↦ ∫⁻ g : Path, ENNReal.ofReal (pathArea T g^d) ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (entranceAreaMoment T d)) := by
  cases d with
  | succ n => exact actual_area_succ_moment_tendsto n T hT
  | zero =>
    apply (tendsto_const_nhds (x := (1 : ℝ≥0∞))).congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    let := positiveBridgeLaw_isProbability a ha T hT
    simp

theorem ae_area_pow_nonneg (a : ℝ) (T : ℝ≥0) (d : ℕ) :
    ∀ᵐ g : Path ∂positiveBridgeLaw a T, 0 ≤ pathArea T g^d := by
  filter_upwards [ae_positiveBridgeLaw_strictly_positive a T] with g hg
  rw [pathArea_pow_eq_cube_integral]
  apply integral_nonneg_of_ae
  filter_upwards [ae_timeCube_coordinates T d] with τ hτ
  exact heightProduct_nonneg T τ g hτ (fun t ht ↦ (hg t ht).le)

theorem actual_area_real_moment_tendsto (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    Tendsto (fun a : ℝ ↦ ∫ g : Path, pathArea T g^d ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (entranceAreaMoment T d).toReal) := by
  have he := (ENNReal.tendsto_toReal (entranceAreaMoment_lt_top T hT d).ne).comp
    (actual_area_moment_tendsto T hT d)
  apply he.congr
  intro a
  exact (integral_eq_lintegral_of_nonneg_ae (ae_area_pow_nonneg a T d)
    ((measurable_pathArea T).pow_const d).aestronglyMeasurable).symm

theorem eventually_actual_area_pow_integrable (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, Integrable (fun g : Path ↦ pathArea T g^d) (positiveBridgeLaw a T) := by
  filter_upwards [eventually_area_pow_integrable T hT d] with a ha
  apply ha.mono' ((measurable_pathArea T).pow_const d).aestronglyMeasurable
  exact ae_of_all _ (fun g ↦ by simp only [Real.norm_eq_abs,abs_pow,le_refl])

theorem actual_absolute_area_real_moment_tendsto (T : ℝ≥0) (hT : 0 < T) (d : ℕ) :
    Tendsto (fun a : ℝ ↦ ∫ g : Path, |pathArea T g|^d ∂positiveBridgeLaw a T)
      (𝓝[>] 0) (𝓝 (entranceAreaMoment T d).toReal) := by
  apply (actual_area_real_moment_tendsto T hT d).congr
  intro a
  apply integral_congr_ae
  filter_upwards [ae_area_pow_nonneg a T 1] with g hg
  simp only [pow_one] at hg
  rw [abs_of_nonneg hg]

end PerronWright.BrownianPositiveBridgeAreaMomentLimits
