import PerronWright.Probability.BrownianGaussianSquareMomentGrowth
import PerronWright.Probability.BrownianPositiveBridgeCommonAreaMoments

/-! # Explicit factorial growth of genuine area even moments

All constants depend only on the fixed duration. The actual Gaussian
entrance integrals give a common endpoint neighborhood for every order.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianPositiveBridgeAreaFactorialGrowth

open BrownianPathLaw BrownianBridgeCyclicArea BrownianPositiveBridgeConditioning
open BrownianPositiveBridgeAllTimeMoments BrownianPositiveBridgeAreaMomentBounds
open BrownianPositiveBridgeEntranceMomentBounds BrownianPositiveBridgeGaussianBounds
open BrownianPositiveBridgeGaussianMomentBounds
open BrownianGaussianSquareMomentGrowth BrownianPositiveBridgeCommonAreaMoments

def coordinateCoefficient (T : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (T:ℝ)/gaussianPDF 0 T 0*ENNReal.ofReal (envelopeCoefficient (T/2))

def areaGrowthConstant (T : ℝ≥0) : ℝ :=
  1+96*gaussianSquareConstant*(coordinateCoefficient T).toReal

def areaGrowthBase (T : ℝ≥0) : ℝ := 16*(max 1 (T:ℝ))^3

theorem coordinateCoefficient_ne_top (T : ℝ≥0) (hT : 0 < T) :
    coordinateCoefficient T ≠ ⊤ := by
  unfold coordinateCoefficient
  have hp : gaussianPDF 0 T 0 ≠ 0 := (gaussianPDF_pos 0 hT.ne' 0).ne'
  finiteness

theorem areaGrowthConstant_ge_one (T : ℝ≥0) : 1 ≤ areaGrowthConstant T := by
  have := gaussianSquareConstant_pos
  unfold areaGrowthConstant
  exact le_add_of_nonneg_right (by positivity)

theorem areaGrowthBase_pos (T : ℝ≥0) : 0 < areaGrowthBase T := by
  unfold areaGrowthBase
  have hm : (0:ℝ) < max 1 (T:ℝ) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  positivity

theorem entranceBound_factorial_growth (T : ℝ≥0) (n : ℕ) :
    entranceBound T n ≤
      96*gaussianSquareConstant*(16*max 1 (T:ℝ))^n*((n+1).factorial:ℝ) := by
  let A := (4:ℝ)^(n+1)*((n+1).factorial:ℝ)*gaussianSquareConstant
  let V := max 1 (T:ℝ)
  have hV : 1 ≤ V := le_max_left _ _
  have hTV : (T:ℝ) ≤ V := le_max_right _ _
  have hpow : 1 ≤ (4:ℝ)^(n+1) := one_le_pow₀ (by norm_num)
  have hfac : 1 ≤ ((n+1).factorial:ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos (n+1))
  have hA : 1 ≤ A := by
    dsimp [A]
    calc
      1 = (1:ℝ)*1*1 := by norm_num
      _ ≤ _ := mul_le_mul (mul_le_mul hpow hfac (by norm_num) (by positivity))
        gaussianSquareConstant_ge_one (by norm_num) (by positivity)
  have heven : standardMoment (2*n+2) ≤ A := by
    simpa only [show 2*(n+1) = 2*n+2 by omega] using standardMoment_even_factorial_bound (n+1)
  have hodd : standardMoment (2*n+1) ≤ 1+A := standardMoment_odd_factorial_bound n
  have hfirst : 1+standardMoment (2*n+1) ≤ 3*A := by linarith
  have hsecond : 1+standardMoment (2*n+2) ≤ 2*A := by linarith
  have hp1 : (2:ℝ)^(2*n+1) = 2*4^n := by
    rw [pow_add,pow_mul]
    norm_num
    ring
  have hp3 : (2:ℝ)^(2*n+3) = 8*4^n := by
    rw [pow_add,pow_mul]
    norm_num
    ring
  calc
    _ ≤ 2^(2*n+1)*(3*A)+2^(2*n+3)*(T:ℝ)^n*(2*A) := by
      unfold entranceBound
      exact add_le_add (mul_le_mul_of_nonneg_left hfirst (by positivity))
        (mul_le_mul_of_nonneg_left hsecond (by positivity))
    _ = 6*4^n*A+16*4^n*(T:ℝ)^n*A := by rw [hp1,hp3]; ring
    _ ≤ 6*4^n*V^n*A+16*4^n*V^n*A := by
      apply add_le_add
      · have hvn : 1 ≤ V^n := one_le_pow₀ hV
        nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 6*4^n*A) (sub_nonneg.mpr hvn)]
      · gcongr
    _ ≤ 24*4^n*V^n*A := by nlinarith [show 0 ≤ 4^n*V^n*A by positivity]
    _ = _ := by
      dsimp [A,V]
      rw [mul_pow,pow_succ]
      have h4 : (4:ℝ)^n*(4:ℝ)^n = (16:ℝ)^n := by rw [← mul_pow]; norm_num
      calc
        _ = 96*gaussianSquareConstant*(max 1 (T:ℝ))^n*((4:ℝ)^n*4^n)*
            ((n+1).factorial:ℝ) := by ring
        _ = _ := by rw [h4]; ring

theorem coordinateBound_factorial_growth (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    coordinateBound T n ≤ ENNReal.ofReal
      (areaGrowthConstant T*(16*max 1 (T:ℝ))^n*((n+1).factorial:ℝ)) := by
  let B := (16*max 1 (T:ℝ))^n*((n+1).factorial:ℝ)
  have hG := gaussianSquareConstant_pos
  have hB : 1 ≤ B := by
    have hm : (1:ℝ) ≤ 16*max 1 (T:ℝ) := by nlinarith [le_max_left (1:ℝ) (T:ℝ)]
    have hf : (1:ℝ) ≤ ((n+1).factorial:ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos (n+1))
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hm) hf
  have hQ : coordinateCoefficient T = ENNReal.ofReal (coordinateCoefficient T).toReal :=
    (ENNReal.ofReal_toReal (coordinateCoefficient_ne_top T hT)).symm
  calc
    _ = 1+coordinateCoefficient T*ENNReal.ofReal (entranceBound T n) := rfl
    _ ≤ 1+coordinateCoefficient T*ENNReal.ofReal (96*gaussianSquareConstant*B) :=
      add_le_add le_rfl (mul_le_mul' le_rfl
        (ENNReal.ofReal_le_ofReal (by
          simpa only [B,mul_assoc] using entranceBound_factorial_growth T n)))
    _ = ENNReal.ofReal (1+(coordinateCoefficient T).toReal*(96*gaussianSquareConstant*B)) := by
      rw [hQ,← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ← ENNReal.ofReal_one,← ENNReal.ofReal_add (by norm_num) (by positivity)]
      rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      unfold areaGrowthConstant
      dsimp [B] at hB ⊢
      nlinarith

theorem areaEvenBound_factorial_growth (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    areaEvenBound T n ≤ ENNReal.ofReal
      (areaGrowthConstant T*(areaGrowthBase T)^(n+1)*((n+2).factorial:ℝ)) := by
  have hC : 0 ≤ areaGrowthConstant T := (le_trans (by norm_num) (areaGrowthConstant_ge_one T))
  have hpow : (T:ℝ)^(2*n+2) ≤ (max 1 (T:ℝ))^(2*(n+1)) := by
    convert! pow_le_pow_left₀ T.property (le_max_right 1 (T:ℝ)) (2*n+2) using 1
  calc
    _ = ENNReal.ofReal ((T:ℝ)^(2*n+2))*coordinateBound T (n+1) := by
      unfold areaEvenBound
      rw [← ENNReal.ofReal_mul (by positivity),← pow_succ]
    _ ≤ ENNReal.ofReal ((T:ℝ)^(2*n+2))*ENNReal.ofReal
        (areaGrowthConstant T*(16*max 1 (T:ℝ))^(n+1)*((n+2).factorial:ℝ)) :=
      mul_le_mul' le_rfl (coordinateBound_factorial_growth T hT (n+1))
    _ = ENNReal.ofReal ((T:ℝ)^(2*n+2)*
        (areaGrowthConstant T*(16*max 1 (T:ℝ))^(n+1)*((n+2).factorial:ℝ))) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal ((max 1 (T:ℝ))^(2*(n+1))*
        (areaGrowthConstant T*(16*max 1 (T:ℝ))^(n+1)*((n+2).factorial:ℝ))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpow (by positivity))
    _ = _ := by
      congr 1
      unfold areaGrowthBase
      rw [mul_pow,mul_pow]
      rw [← pow_mul,show 3*(n+1) = 2*(n+1)+(n+1) by omega,pow_add]
      ring

theorem eventually_all_area_even_factorial_growth (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ n : ℕ,
      (∫⁻ g : Path, ENNReal.ofReal (|pathArea T g|^(2*n+2)) ∂positiveBridgeLaw a T) ≤
        ENNReal.ofReal (areaGrowthConstant T*(areaGrowthBase T)^(n+1)*((n+2).factorial:ℝ)) :=
  (eventually_all_area_even_moment_bound T hT).mono
    (fun _a ha n ↦ (ha n).trans (areaEvenBound_factorial_growth T hT n))

theorem eventually_all_area_even_factorial_growth_including_zero (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ n : ℕ,
      (∫⁻ g : Path, ENNReal.ofReal (|pathArea T g|^(2*n)) ∂positiveBridgeLaw a T) ≤
        ENNReal.ofReal (areaGrowthConstant T*(areaGrowthBase T)^n*((n+1).factorial:ℝ)) := by
  filter_upwards [self_mem_nhdsWithin,eventually_all_area_even_factorial_growth T hT] with a ha hb
  intro n
  cases n with
  | zero =>
    let := positiveBridgeLaw_isProbability a ha T hT
    simp only [mul_zero,pow_zero,ENNReal.ofReal_one,lintegral_one,measure_univ,
      mul_one,Nat.zero_add,Nat.factorial_one,Nat.cast_one]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (areaGrowthConstant_ge_one T)
  | succ n =>
    simpa only [show 2*(n+1) = 2*n+2 by omega] using hb n

end PerronWright.BrownianPositiveBridgeAreaFactorialGrowth
