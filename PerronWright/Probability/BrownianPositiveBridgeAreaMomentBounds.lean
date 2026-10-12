import PerronWright.Probability.BrownianPositiveBridgeAllTimeMoments
import PerronWright.Probability.BrownianPositiveBridgeAreaMomentGeometry

/-! # Actual small-positive-endpoint bridge area moments

The all-time coordinate bounds are integrated against time by Tonelli.
Jensen then controls the literal path area.  The constants are finite
and independent of the positive endpoint near zero.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeAreaMomentBounds

open BrownianPathLaw BrownianBridgeCyclicArea BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeAllTimeMoments BrownianPositiveBridgeAreaMomentGeometry

def areaEvenBound (T : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((T : ℝ)^(2*n+1))*ENNReal.ofReal (T : ℝ)*coordinateBound T (n+1)

def areaBound (T : ℝ≥0) (n : ℕ) : ℝ≥0∞ := 1+areaEvenBound T n

theorem areaEvenBound_lt_top (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : areaEvenBound T n < ∞ := by
  unfold areaEvenBound
  have := coordinateBound_lt_top T hT (n+1)
  finiteness

theorem areaBound_lt_top (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : areaBound T n < ∞ := by
  unfold areaBound
  exact ENNReal.add_lt_top.mpr ⟨by simp,areaEvenBound_lt_top T hT n⟩

theorem measurable_joint_coordinate_power (k : ℕ) :
    Measurable (fun p : Path×ℝ ↦ ENNReal.ofReal (|p.1 (Real.toNNReal p.2)|^k)) := by
  have hc : Continuous (fun p : Path×ℝ ↦ p.1 (Real.toNNReal p.2)) :=
    continuous_joint_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  exact (hc.abs.pow k).measurable.ennreal_ofReal

theorem eventually_area_even_moment_bound (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ g : Path, ENNReal.ofReal (|pathArea T g|^(2*n+2)) ∂positiveBridgeLaw a T) ≤ areaEvenBound T n := by
  filter_upwards [self_mem_nhdsWithin,eventually_uniform_coordinate_moment_bound T hT (n+1)]
    with a ha hb
  let := positiveBridgeLaw_isProbability a ha T hT
  have hm : Measurable (fun p : Path×ℝ ↦ ENNReal.ofReal (|p.1 (Real.toNNReal p.2)|^(2*n+2))) :=
    measurable_joint_coordinate_power _
  have htime : (∫⁻ r in Ioc (0 : ℝ) (T : ℝ),
      ∫⁻ g : Path, ENNReal.ofReal (|g (Real.toNNReal r)|^(2*n+2)) ∂positiveBridgeLaw a T) ≤
      ENNReal.ofReal (T : ℝ)*coordinateBound T (n+1) := by
    calc
      _ ≤ ∫⁻ r in Ioc (0 : ℝ) (T : ℝ), coordinateBound T (n+1) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        have hle : Real.toNNReal r ≤ T := Real.toNNReal_le_iff_le_coe.mpr hr.2
        simpa only [show 2*(n+1) = 2*n+2 by omega] using hb (Real.toNNReal r) hle
      _ = _ := by simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero]; ac_rfl
  calc
    _ ≤ ∫⁻ g : Path, ENNReal.ofReal ((T : ℝ)^(2*n+1))*
        (∫⁻ r in Ioc (0 : ℝ) (T : ℝ), ENNReal.ofReal (|g (Real.toNNReal r)|^(2*n+2)))
        ∂positiveBridgeLaw a T := lintegral_mono (fun g ↦ pathArea_even_pow_lintegral_bound T hT g n)
    _ = ENNReal.ofReal ((T : ℝ)^(2*n+1)) * ∫⁻ g : Path,
        (∫⁻ r in Ioc (0 : ℝ) (T : ℝ), ENNReal.ofReal (|g (Real.toNNReal r)|^(2*n+2)))
        ∂positiveBridgeLaw a T := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal ((T : ℝ)^(2*n+1)) * ∫⁻ r in Ioc (0 : ℝ) (T : ℝ),
        (∫⁻ g : Path, ENNReal.ofReal (|g (Real.toNNReal r)|^(2*n+2)) ∂positiveBridgeLaw a T) := by
      rw [lintegral_lintegral_swap hm.aemeasurable]
    _ ≤ _ := by unfold areaEvenBound; simpa only [mul_assoc] using mul_le_mul' le_rfl htime

theorem abs_pow_le_one_add_even_pow (x : ℝ) (n : ℕ) :
    |x|^n ≤ 1+|x|^(2*n+2) := by
  by_cases hx : |x| ≤ 1
  · exact (pow_le_one₀ (abs_nonneg x) hx).trans (le_add_of_nonneg_right (by positivity))
  · exact (pow_le_pow_right₀ (le_of_not_ge hx) (by omega : n ≤ 2*n+2)).trans
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))

theorem eventually_area_moment_bound (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫⁻ g : Path, ENNReal.ofReal (|pathArea T g|^n) ∂positiveBridgeLaw a T) ≤ areaBound T n := by
  filter_upwards [self_mem_nhdsWithin,eventually_area_even_moment_bound T hT n] with a ha hb
  let := positiveBridgeLaw_isProbability a ha T hT
  calc
    _ ≤ ∫⁻ g : Path, 1+ENNReal.ofReal (|pathArea T g|^(2*n+2)) ∂positiveBridgeLaw a T := by
      apply lintegral_mono
      intro g
      calc
        _ ≤ ENNReal.ofReal (1+|pathArea T g|^(2*n+2)) :=
          ENNReal.ofReal_le_ofReal (abs_pow_le_one_add_even_pow _ _)
        _ = _ := by rw [ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_one]
    _ = 1+∫⁻ g : Path, ENNReal.ofReal (|pathArea T g|^(2*n+2)) ∂positiveBridgeLaw a T := by
      rw [lintegral_add_left measurable_const]
      simp only [lintegral_const,measure_univ,mul_one]
    _ ≤ _ := add_le_add le_rfl hb

theorem eventually_area_pow_integrable (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, Integrable (fun g : Path ↦ |pathArea T g|^n) (positiveBridgeLaw a T) := by
  filter_upwards [eventually_area_moment_bound T hT n] with a hb
  refine ⟨((measurable_pathArea T).abs.pow_const n).aestronglyMeasurable,?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _ ↦ by positivity))).mpr
    (lt_of_le_of_lt hb (areaBound_lt_top T hT n))

theorem eventually_area_real_moment_bound (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      (∫ g : Path, |pathArea T g|^n ∂positiveBridgeLaw a T) ≤ (areaBound T n).toReal := by
  filter_upwards [eventually_area_moment_bound T hT n] with a hb
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ ↦ by positivity))
    ((measurable_pathArea T).abs.pow_const n).aestronglyMeasurable]
  exact ENNReal.toReal_mono (areaBound_lt_top T hT n).ne hb

end PerronWright.BrownianPositiveBridgeAreaMomentBounds
