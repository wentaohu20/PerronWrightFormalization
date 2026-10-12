import PerronWright.Probability.BrownianPositiveBridgeEntranceMomentBounds

/-! # Actual positive-bridge moments uniformly over the whole time interval

The long transition supplies a linear boundary factor.  The short one
uses the proved entrance integral, split at its Gaussian standard
deviation.  Endpoints are handled by the actual almost-sure endpoint
identity, not an interior estimate.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeAllTimeMoments

open BrownianPathLaw BrownianPositiveKilledEndpoint BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeGaussianBounds BrownianPositiveBridgeFiniteDimensionalLaw
open BrownianPositiveBridgeFiniteDimensionalEntrance BrownianPositiveBridgeTwoPointKernelBounds
open BrownianPositiveBridgeEntranceMomentBounds

def coordinateBound (T : ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  1 + ENNReal.ofReal (T : ℝ)/gaussianPDF 0 T 0 *
    ENNReal.ofReal (envelopeCoefficient (T/2)) * ENNReal.ofReal (entranceBound T n)

theorem coordinateBound_lt_top (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    coordinateBound T n < ∞ := by
  unfold coordinateBound
  have hp : gaussianPDF 0 T 0 ≠ 0 := (gaussianPDF_pos 0 hT.ne' 0).ne'
  finiteness

theorem envelopeReal_le_linear (δ T : ℝ≥0) (hT : 0 < T) (y : ℝ) :
    envelopeReal δ T y ≤ envelopeCoefficient δ*|y| := by
  have hC := envelopeCoefficient_nonneg δ
  have hexp : Real.exp (-y^2/(4*(T : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg y)) (by positivity)
  unfold envelopeReal
  calc
    _ ≤ envelopeCoefficient δ*max y 0 := by nlinarith [mul_nonneg hC (le_max_right y 0)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (max_le (le_abs_self y) (abs_nonneg y)) hC

theorem long_density_linear_bound (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (T : ℝ≥0) (hT : 0 < T) (t : ℝ≥0) (ht : T/2 ≤ t) (htT : t ≤ T) (y : ℝ) :
    density y t a ≤ ENNReal.ofReal a*ENNReal.ofReal (envelopeCoefficient (T/2))*ENNReal.ofReal |y| := by
  have hδ : 0 < T/2 := div_pos hT (by norm_num)
  rw [density_symm y a t (hδ.trans_le ht)]
  calc
    _ ≤ ENNReal.ofReal a*envelope (T/2) T y :=
      density_le_start_mul_envelope a ha ha1 (T/2) t T hδ ht htT y
    _ ≤ ENNReal.ofReal a*ENNReal.ofReal (envelopeCoefficient (T/2)*|y|) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (envelopeReal_le_linear (T/2) T hT y))
    _ = _ := by rw [ENNReal.ofReal_mul (envelopeCoefficient_nonneg _)]; ac_rfl

theorem onePointDensity_time_symm (a : ℝ) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) (y : ℝ) :
    onePointDensity a s t y = onePointDensity a t s y := by
  unfold onePointDensity
  rw [add_comm s t,density_symm a y s hs,density_symm y a t ht]
  ac_rfl

theorem onePoint_moment_bound_long_exit (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (T : ℝ≥0) (hT : 0 < T)
    (hratio : (normalization a T)⁻¹*(ENNReal.ofReal a*ENNReal.ofReal a) ≤ ENNReal.ofReal (T : ℝ))
    (s t : ℝ≥0) (hs : 0 < s) (ht : T/2 ≤ t) (hadd : s+t = T) (n : ℕ) :
    (∫⁻ y : ℝ, onePointDensity a s t y*ENNReal.ofReal (|y|^(2*n))) ≤ coordinateBound T n := by
  have hsT : s ≤ T := by rw [← hadd]; exact le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ t)
  have htT : t ≤ T := by rw [← hadd]; exact le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ s)
  have hA : ENNReal.ofReal a ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr ha
  have hpoint (y : ℝ) : onePointDensity a s t y*ENNReal.ofReal (|y|^(2*n)) ≤
      (ENNReal.ofReal (T : ℝ)/gaussianPDF 0 T 0 *ENNReal.ofReal (envelopeCoefficient (T/2))) *
        ((density a s y/ENNReal.ofReal a)*ENNReal.ofReal (|y|^(2*n+1))) := by
    have he : density a s y = (density a s y/ENNReal.ofReal a)*ENNReal.ofReal a :=
      (ENNReal.div_mul_cancel hA ENNReal.ofReal_ne_top).symm
    have hp : ENNReal.ofReal (|y|^(2*n+1)) = ENNReal.ofReal |y| * ENNReal.ofReal (|y|^(2*n)) := by
      rw [pow_succ,ENNReal.ofReal_mul (by positivity)]; ac_rfl
    unfold onePointDensity
    rw [hadd]
    calc
      _ ≤ (normalization a T)⁻¹*(density a s y*(ENNReal.ofReal a*
          ENNReal.ofReal (envelopeCoefficient (T/2))*ENNReal.ofReal |y|))/gaussianPDF 0 T 0*
          ENNReal.ofReal (|y|^(2*n)) :=
        mul_le_mul' (ENNReal.div_le_div_right (mul_le_mul' le_rfl
          (mul_le_mul' le_rfl (long_density_linear_bound a ha ha1 T hT t ht htT y))) _) le_rfl
      _ = (((normalization a T)⁻¹*(ENNReal.ofReal a*ENNReal.ofReal a))/gaussianPDF 0 T 0*
          ENNReal.ofReal (envelopeCoefficient (T/2))) *
          ((density a s y/ENNReal.ofReal a)*ENNReal.ofReal (|y|^(2*n+1))) := by
        conv_lhs => rw [he]
        rw [hp]
        simp only [div_eq_mul_inv]
        ac_rfl
      _ ≤ _ := mul_le_mul' (mul_le_mul' (ENNReal.div_le_div_right hratio _) le_rfl) le_rfl
  calc
    _ ≤ ∫⁻ y : ℝ, (ENNReal.ofReal (T : ℝ)/gaussianPDF 0 T 0*ENNReal.ofReal (envelopeCoefficient (T/2))) *
        ((density a s y/ENNReal.ofReal a)*ENNReal.ofReal (|y|^(2*n+1))) := lintegral_mono hpoint
    _ = (ENNReal.ofReal (T : ℝ)/gaussianPDF 0 T 0*ENNReal.ofReal (envelopeCoefficient (T/2))) *
        ∫⁻ y : ℝ, (density a s y/ENNReal.ofReal a)*ENNReal.ofReal (|y|^(2*n+1)) := by
      have hm : Measurable (fun y : ℝ ↦ (density a s y/ENNReal.ofReal a)*ENNReal.ofReal (|y|^(2*n+1))) :=
        ((measurable_density a s).div_const _).mul (by fun_prop)
      exact lintegral_const_mul _ hm
    _ ≤ ENNReal.ofReal (T : ℝ)/gaussianPDF 0 T 0 *
        ENNReal.ofReal (envelopeCoefficient (T/2))*ENNReal.ofReal (entranceBound T n) :=
      mul_le_mul' le_rfl (uniform_entrance_moment_bound a ha ha1 s T hs hsT n)
    _ ≤ _ := le_add_of_nonneg_left (zero_le : (0 : ℝ≥0∞) ≤ 1)

theorem eventually_uniform_coordinate_moment_bound (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ s : ℝ≥0, s ≤ T →
      (∫⁻ g : Path, ENNReal.ofReal (|g s|^(2*n)) ∂positiveBridgeLaw a T) ≤ coordinateBound T n := by
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin,hsmall,eventually_normalization_sq_ratio_bound T hT]
    with a ha ha1 hratio
  intro s hsT
  let := positiveBridgeLaw_isProbability a ha T hT
  by_cases hs0 : s = 0
  · subst s
    have he : (∫⁻ g : Path, ENNReal.ofReal (|g 0|^(2*n)) ∂positiveBridgeLaw a T) = ENNReal.ofReal (a^(2*n)) := by
      calc
        _ = ∫⁻ g : Path, ENNReal.ofReal (a^(2*n)) ∂positiveBridgeLaw a T := by
          apply lintegral_congr_ae
          filter_upwards [ae_positiveBridgeLaw_endpoints a T hT] with g hg
          rw [hg.1,abs_of_pos ha]
        _ = _ := by simp
    rw [he]
    exact (ENNReal.ofReal_le_one.mpr (pow_le_one₀ ha.le ha1.le)).trans (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ _))
  by_cases hsEnd : s = T
  · subst s
    have he : (∫⁻ g : Path, ENNReal.ofReal (|g T|^(2*n)) ∂positiveBridgeLaw a T) = ENNReal.ofReal (a^(2*n)) := by
      calc
        _ = ∫⁻ g : Path, ENNReal.ofReal (a^(2*n)) ∂positiveBridgeLaw a T := by
          apply lintegral_congr_ae
          filter_upwards [ae_positiveBridgeLaw_endpoints a T hT] with g hg
          rw [hg.2,abs_of_pos ha]
        _ = _ := by simp
    rw [he]
    exact (ENNReal.ofReal_le_one.mpr (pow_le_one₀ ha.le ha1.le)).trans (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0∞) ≤ _))
  have hs : 0 < s := pos_iff_ne_zero.mpr hs0
  let t := T-s
  have ht : 0 < t := tsub_pos_iff_lt.mpr (lt_of_le_of_ne hsT hsEnd)
  have hadd : s+t = T := add_tsub_cancel_of_le hsT
  have hm : Measurable (fun y : ℝ ↦ ENNReal.ofReal (|y|^(2*n))) := by fun_prop
  conv_lhs => rw [← hadd,onePoint_lintegral a ha s t hs ht _ hm]
  by_cases hlong : T/2 ≤ t
  · exact onePoint_moment_bound_long_exit a ha ha1.le T hT hratio s t hs hlong hadd n
  · have hlong' : T/2 ≤ s := by
      have hsum : (s : ℝ)+(t : ℝ) = (T : ℝ) := by exact_mod_cast hadd
      have hlt : (t : ℝ) < (T : ℝ)/2 := by exact_mod_cast lt_of_not_ge hlong
      change (T : ℝ)/2 ≤ (s : ℝ)
      linarith
    simp_rw [onePointDensity_time_symm a s t hs ht]
    exact onePoint_moment_bound_long_exit a ha ha1.le T hT hratio t s ht hlong' (by simpa [add_comm] using hadd) n

end PerronWright.BrownianPositiveBridgeAllTimeMoments
