import PerronWright.Probability.BrownianPositiveBridgeAreaMomentBounds

/-! # One actual endpoint neighborhood for every even area moment

The endpoint and normalization restrictions in the Gaussian-kernel proof
do not depend on the moment order. Here they are made simultaneous before
any exponential series is integrated.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeCommonAreaMoments

open BrownianPathLaw BrownianBridgeCyclicArea BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeAllTimeMoments BrownianPositiveBridgeAreaMomentGeometry
open BrownianPositiveBridgeAreaMomentBounds BrownianPositiveBridgeFiniteDimensionalLaw
open BrownianPositiveBridgeFiniteDimensionalEntrance BrownianPositiveBridgeTwoPointKernelBounds

def SmallEndpoint (a : ℝ) (T : ℝ≥0) : Prop :=
  0 < a ∧ a ≤ 1 ∧
    (normalization a T)⁻¹*(ENNReal.ofReal a*ENNReal.ofReal a) ≤ ENNReal.ofReal (T:ℝ)

theorem eventually_smallEndpoint (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, SmallEndpoint a T := by
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin,hsmall,eventually_normalization_sq_ratio_bound T hT]
    with a ha ha1 hr
  exact ⟨ha,ha1.le,hr⟩

private theorem coordinate_moment_bound (T : ℝ≥0) (hT : 0 < T) (a : ℝ)
    (ha : SmallEndpoint a T) (n : ℕ) (s : ℝ≥0) (hsT : s ≤ T) :
    (∫⁻ g : Path, ENNReal.ofReal (|g s|^(2*n)) ∂positiveBridgeLaw a T) ≤ coordinateBound T n := by
  let := positiveBridgeLaw_isProbability a ha.1 T hT
  by_cases hs0 : s = 0
  · subst s
    have he : (∫⁻ g : Path, ENNReal.ofReal (|g 0|^(2*n)) ∂positiveBridgeLaw a T) =
        ENNReal.ofReal (a^(2*n)) := by
      calc
        _ = ∫⁻ g : Path, ENNReal.ofReal (a^(2*n)) ∂positiveBridgeLaw a T := by
          apply lintegral_congr_ae
          filter_upwards [ae_positiveBridgeLaw_endpoints a T hT] with g hg
          rw [hg.1,abs_of_pos ha.1]
        _ = _ := by simp
    rw [he]
    exact (ENNReal.ofReal_le_one.mpr (pow_le_one₀ ha.1.le ha.2.1)).trans
      (le_add_of_nonneg_right (zero_le : (0:ℝ≥0∞) ≤ _))
  by_cases hsEnd : s = T
  · subst s
    have he : (∫⁻ g : Path, ENNReal.ofReal (|g T|^(2*n)) ∂positiveBridgeLaw a T) =
        ENNReal.ofReal (a^(2*n)) := by
      calc
        _ = ∫⁻ g : Path, ENNReal.ofReal (a^(2*n)) ∂positiveBridgeLaw a T := by
          apply lintegral_congr_ae
          filter_upwards [ae_positiveBridgeLaw_endpoints a T hT] with g hg
          rw [hg.2,abs_of_pos ha.1]
        _ = _ := by simp
    rw [he]
    exact (ENNReal.ofReal_le_one.mpr (pow_le_one₀ ha.1.le ha.2.1)).trans
      (le_add_of_nonneg_right (zero_le : (0:ℝ≥0∞) ≤ _))
  have hs : 0 < s := pos_iff_ne_zero.mpr hs0
  let t := T-s
  have ht : 0 < t := tsub_pos_iff_lt.mpr (lt_of_le_of_ne hsT hsEnd)
  have hadd : s+t = T := add_tsub_cancel_of_le hsT
  have hm : Measurable (fun y : ℝ ↦ ENNReal.ofReal (|y|^(2*n))) := by fun_prop
  conv_lhs => rw [← hadd,onePoint_lintegral a ha.1 s t hs ht _ hm]
  by_cases hlong : T/2 ≤ t
  · exact onePoint_moment_bound_long_exit a ha.1 ha.2.1 T hT ha.2.2 s t hs hlong hadd n
  · have hlong' : T/2 ≤ s := by
      have hsum : (s:ℝ)+(t:ℝ) = (T:ℝ) := by exact_mod_cast hadd
      have hlt : (t:ℝ) < (T:ℝ)/2 := by exact_mod_cast lt_of_not_ge hlong
      change (T:ℝ)/2 ≤ (s:ℝ)
      linarith
    simp_rw [onePointDensity_time_symm a s t hs ht]
    exact onePoint_moment_bound_long_exit a ha.1 ha.2.1 T hT ha.2.2 t s ht hlong'
      (by simpa [add_comm] using hadd) n

theorem all_coordinate_moment_bound (T : ℝ≥0) (hT : 0 < T) (a : ℝ)
    (ha : SmallEndpoint a T) :
    ∀ n : ℕ, ∀ s : ℝ≥0, s ≤ T →
      (∫⁻ g : Path, ENNReal.ofReal (|g s|^(2*n)) ∂positiveBridgeLaw a T) ≤ coordinateBound T n :=
  fun n s hs ↦ coordinate_moment_bound T hT a ha n s hs

theorem all_area_even_moment_bound (T : ℝ≥0) (hT : 0 < T) (a : ℝ)
    (ha : SmallEndpoint a T) (n : ℕ) :
    (∫⁻ g : Path, ENNReal.ofReal (|pathArea T g|^(2*n+2)) ∂positiveBridgeLaw a T) ≤
      areaEvenBound T n := by
  let := positiveBridgeLaw_isProbability a ha.1 T hT
  have hm := measurable_joint_coordinate_power (2*n+2)
  have htime : (∫⁻ r in Ioc (0:ℝ) (T:ℝ),
      ∫⁻ g : Path, ENNReal.ofReal (|g (Real.toNNReal r)|^(2*n+2)) ∂positiveBridgeLaw a T) ≤
      ENNReal.ofReal (T:ℝ)*coordinateBound T (n+1) := by
    calc
      _ ≤ ∫⁻ r in Ioc (0:ℝ) (T:ℝ), coordinateBound T (n+1) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        have hle : Real.toNNReal r ≤ T := Real.toNNReal_le_iff_le_coe.mpr hr.2
        simpa only [show 2*(n+1) = 2*n+2 by omega] using
          coordinate_moment_bound T hT a ha (n+1) (Real.toNNReal r) hle
      _ = _ := by
        simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero]
        ac_rfl
  calc
    _ ≤ ∫⁻ g : Path, ENNReal.ofReal ((T:ℝ)^(2*n+1))*
        (∫⁻ r in Ioc (0:ℝ) (T:ℝ), ENNReal.ofReal (|g (Real.toNNReal r)|^(2*n+2)))
        ∂positiveBridgeLaw a T := lintegral_mono (fun g ↦ pathArea_even_pow_lintegral_bound T hT g n)
    _ = ENNReal.ofReal ((T:ℝ)^(2*n+1))*∫⁻ g : Path,
        (∫⁻ r in Ioc (0:ℝ) (T:ℝ), ENNReal.ofReal (|g (Real.toNNReal r)|^(2*n+2)))
        ∂positiveBridgeLaw a T := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal ((T:ℝ)^(2*n+1))*∫⁻ r in Ioc (0:ℝ) (T:ℝ),
        (∫⁻ g : Path, ENNReal.ofReal (|g (Real.toNNReal r)|^(2*n+2)) ∂positiveBridgeLaw a T) := by
      rw [lintegral_lintegral_swap hm.aemeasurable]
    _ ≤ _ := by
      unfold areaEvenBound
      simpa only [mul_assoc] using mul_le_mul' le_rfl htime

theorem eventually_all_area_even_moment_bound (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ n : ℕ,
      (∫⁻ g : Path, ENNReal.ofReal (|pathArea T g|^(2*n+2)) ∂positiveBridgeLaw a T) ≤
        areaEvenBound T n :=
  (eventually_smallEndpoint T hT).mono (fun a ha n ↦ all_area_even_moment_bound T hT a ha n)

end PerronWright.BrownianPositiveBridgeCommonAreaMoments
