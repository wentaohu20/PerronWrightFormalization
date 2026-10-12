import PerronWright.Enumeration.PositiveSurplusNoncubicCoefficientAsymptotic
import PerronWright.Enumeration.PositiveSurplusCubicFieldWeightAsymptotic

/-!
# Field-uniform labelled bounds for the positive-surplus noncubic part

The normalized noncubic EGF is one half-step below the cubic singularity.
This file first multiplies its coefficient by `k!`, without division by any
noncubic leading term.  The denominator is always the nonzero cubic exact
factorial coefficient or the corresponding physical factorial/Gamma main
term.  Thus the lower-order estimate remains meaningful even when the
noncubic contribution itself vanishes.
-/

open Filter Topology Set Asymptotics
open scoped Classical Topology BigOperators ENNReal NNReal Real Nat

noncomputable section

namespace PerronWright.PositiveSurplusNoncubicFieldWeightAsymptotic

open PerronWright.GraphCore

namespace Coeff

export PerronWright.PositiveSurplusNoncubicCoefficientAsymptotic
  (exists_normalizedFieldNoncubicPart_coefficient_local_relative_bound
   positiveSurplusCubicExactPurePowerCoefficient_ne_zero)

end Coeff

namespace Global

export PerronWright.PositiveSurplusNoncubicGlobalContinuation
  (normalizedFieldNoncubicPartFMS
   normalizedFieldNoncubicPartFMS_coeff)

end Global

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The labelled connected-weight contribution carried by noncubic
positive-surplus cores. -/
def complexFieldNoncubicPartConnectedWeight
    (M : CompactBJRModel S) (g : C(S, ℂ))
    (ell k : ℕ) : ℂ :=
  (k.factorial : ℂ) *
    PowerSeries.coeff k (complexFieldNoncubicPartEGF M g ell)

@[simp] theorem complexFieldNoncubicPartConnectedWeight_eq
    (M : CompactBJRModel S) (g : C(S, ℂ))
    (ell k : ℕ) :
    complexFieldNoncubicPartConnectedWeight M g ell k =
      (k.factorial : ℂ) *
        noncubicFixedSurplusProfileCompositionCoeff M
          (FieldRootedTree.series M g) ell k := by
  simp [complexFieldNoncubicPartConnectedWeight]

/-- Division-free coefficient bridge from the normalized noncubic FMS to
the labelled noncubic contribution. -/
theorem radius_pow_mul_complexFieldNoncubicPartConnectedWeight
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (g : C(S, ℂ)) (ell k : ℕ) :
    (RadiusResponse.radius M hM g) ^ k *
        complexFieldNoncubicPartConnectedWeight M g ell k =
      (k.factorial : ℂ) *
        (Global.normalizedFieldNoncubicPartFMS M hM g ell).coeff k := by
  rw [complexFieldNoncubicPartConnectedWeight,
    Global.normalizedFieldNoncubicPartFMS_coeff]
  ring

/-- Multiplication by `k!` preserves the half-step estimate when the
comparison scale is the exact cubic factorial coefficient. -/
theorem exists_complexFieldNoncubicPartConnectedWeight_exactCubic_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ epsilon K : ℝ, 0 < epsilon ∧ 0 < K ∧
      ∀ᶠ k : ℕ in atTop, ∀ g : C(S, ℂ),
        ‖g‖ ≤ epsilon →
        ‖(RadiusResponse.radius M hM g) ^ k *
              complexFieldNoncubicPartConnectedWeight M g ell k /
              positiveSurplusCubicExactFactorialCoefficient ell k‖ ≤
          K * (‖g‖ + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨epsilon, K, hepsilon, hK, hcoeff⟩ :=
    Coeff.exists_normalizedFieldNoncubicPart_coefficient_local_relative_bound
      M hM hell
  refine ⟨epsilon, K, hepsilon, hK, ?_⟩
  filter_upwards [hcoeff] with k hk
  intro g hg
  let N : ℂ :=
    (Global.normalizedFieldNoncubicPartFMS M hM g ell).coeff k
  let E : ℂ := positiveSurplusCubicExactPurePowerCoefficient ell k
  let W : ℂ := complexFieldNoncubicPartConnectedWeight M g ell k
  have hE : E ≠ 0 := by
    dsimp only [E]
    exact Coeff.positiveSurplusCubicExactPurePowerCoefficient_ne_zero
      ell k hell
  have hfact : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast k.factorial_ne_zero
  have hbridge :=
    radius_pow_mul_complexFieldNoncubicPartConnectedWeight
      M hM g ell k
  have hratio :
      (RadiusResponse.radius M hM g) ^ k * W /
          positiveSurplusCubicExactFactorialCoefficient ell k = N / E := by
    rw [hbridge]
    dsimp only [W, N, E,
      positiveSurplusCubicExactFactorialCoefficient]
    field_simp [hfact, hE]
  rw [hratio]
  simpa only [N, E] using hk g hg

/-- The noncubic labelled contribution is uniformly one half-step below
the physical cubic Perron--Wright main term on a genuine complex field
ball.  No noncubic quantity appears in the denominator. -/
theorem exists_complexFieldNoncubicPartConnectedWeight_cubicMain_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ epsilon K : ℝ, 0 < epsilon ∧ 0 < K ∧
      ∀ᶠ k : ℕ in atTop, ∀ g : C(S, ℂ),
        ‖g‖ ≤ epsilon →
        ‖(RadiusResponse.radius M hM g) ^ k *
              complexFieldNoncubicPartConnectedWeight M g ell k /
              ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
                positiveSurplusCubicFactorialMain ell k)‖ ≤
          K * (‖g‖ + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨epsilon, Kcoeff, hepsilon, hKcoeff, hexact⟩ :=
    exists_complexFieldNoncubicPartConnectedWeight_exactCubic_bound
      M hM hell
  have hfactorO :=
    PerronWright.PositiveSurplusCubicFieldWeightAsymptotic.exactFactorial_div_main_sub_one_isBigO_half
      ell hell
  rw [isBigO_iff] at hfactorO
  obtain ⟨Cfactor₀, hfactor₀⟩ := hfactorO
  let Cfactor : ℝ := max Cfactor₀ 0
  let Bfactor : ℝ := Cfactor + 1
  have hBfactor : 0 < Bfactor := by
    dsimp only [Bfactor, Cfactor]
    linarith [le_max_right Cfactor₀ 0]
  have hfactor : ∀ᶠ k : ℕ in atTop,
      ‖positiveSurplusCubicExactFactorialCoefficient ell k /
          positiveSurplusCubicFactorialMain ell k‖ ≤ Bfactor := by
    filter_upwards [hfactor₀, eventually_ge_atTop (1 : ℕ)] with k hk hkone
    have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hkone
    let x : ℝ := (k : ℝ) ^ (-(1 / 2 : ℝ))
    have hx : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg k) _
    have hxone : x ≤ 1 := by
      dsimp only [x]
      exact Real.rpow_le_one_of_one_le_of_nonpos hkreal (by norm_num)
    have herr :
        ‖positiveSurplusCubicExactFactorialCoefficient ell k /
            positiveSurplusCubicFactorialMain ell k - 1‖ ≤
          Cfactor₀ * x := by
      simpa only [x, Real.norm_eq_abs,
        abs_of_nonneg hx] using hk
    calc
      ‖positiveSurplusCubicExactFactorialCoefficient ell k /
          positiveSurplusCubicFactorialMain ell k‖ =
          ‖(positiveSurplusCubicExactFactorialCoefficient ell k /
            positiveSurplusCubicFactorialMain ell k - 1) + 1‖ := by
            congr 1
            ring
      _ ≤ ‖positiveSurplusCubicExactFactorialCoefficient ell k /
            positiveSurplusCubicFactorialMain ell k - 1‖ + 1 := by
          simpa using norm_add_le
            (positiveSurplusCubicExactFactorialCoefficient ell k /
              positiveSurplusCubicFactorialMain ell k - 1) (1 : ℂ)
      _ ≤ Cfactor₀ * x + 1 := by
        simpa only [add_comm] using add_le_add_right herr 1
      _ ≤ Cfactor + 1 := by
        have hC : Cfactor₀ ≤ Cfactor := le_max_left _ _
        have hCx : Cfactor₀ * x ≤ Cfactor := by
          calc
            Cfactor₀ * x ≤ Cfactor * x :=
              mul_le_mul_of_nonneg_right hC hx
            _ ≤ Cfactor * 1 :=
              mul_le_mul_of_nonneg_left hxone
                (le_max_right Cfactor₀ 0)
            _ = Cfactor := mul_one _
        linarith
      _ = Bfactor := rfl
  let b : ℂ := (Real.sqrt (M.beta hM) : ℂ) ^ ell
  have hb : b ≠ 0 := by
    dsimp only [b]
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.2 (M.beta_pos hM)).ne')
  have hbnorm : 0 < ‖b‖ := norm_pos_iff.mpr hb
  let K : ℝ := Kcoeff * Bfactor / ‖b‖
  have hK : 0 < K := div_pos (mul_pos hKcoeff hBfactor) hbnorm
  refine ⟨epsilon, K, hepsilon, hK, ?_⟩
  filter_upwards [hexact, hfactor, eventually_ge_atTop (1 : ℕ)]
    with k hkexact hkfactor hkone
  intro g hg
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  let EF : ℂ := positiveSurplusCubicExactFactorialCoefficient ell k
  let FM : ℂ := positiveSurplusCubicFactorialMain ell k
  let W : ℂ := complexFieldNoncubicPartConnectedWeight M g ell k
  have hEF : EF ≠ 0 := by
    dsimp only [EF, positiveSurplusCubicExactFactorialCoefficient]
    exact mul_ne_zero (by exact_mod_cast k.factorial_ne_zero)
      (Coeff.positiveSurplusCubicExactPurePowerCoefficient_ne_zero
        ell k hell)
  have hFM : FM ≠ 0 := by
    dsimp only [FM]
    rw [positiveSurplusCubicFactorialMain_eq_exp_rpow ell hell hkpos]
    apply mul_ne_zero (positiveSurplusWrightConstant_ne_zero ell hell)
    exact Complex.ofReal_ne_zero.mpr
      (mul_pos (Real.exp_pos _)
        (Real.rpow_pos_of_pos (by exact_mod_cast hkpos) _)).ne'
  have hratio :
      (RadiusResponse.radius M hM g) ^ k * W / (b * FM) =
        (((RadiusResponse.radius M hM g) ^ k * W) / EF) *
          (EF / FM) / b := by
    field_simp [hb, hEF, hFM]
  rw [hratio, norm_div, norm_mul]
  have hraw := hkexact g hg
  calc
    ‖(RadiusResponse.radius M hM g) ^ k * W / EF‖ *
          ‖EF / FM‖ / ‖b‖ ≤
        (Kcoeff * (‖g‖ + (k : ℝ) ^ (-(1 / 2 : ℝ)))) *
          Bfactor / ‖b‖ := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul hraw (by simpa only [EF, FM] using hkfactor)
          (norm_nonneg _) (by positivity)) hbnorm.le
    _ = K * (‖g‖ + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
      dsimp only [K]
      ring

end PerronWright.PositiveSurplusNoncubicFieldWeightAsymptotic
