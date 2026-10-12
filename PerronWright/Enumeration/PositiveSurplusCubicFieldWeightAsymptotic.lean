import PerronWright.Enumeration.PositiveSurplusCubicCoefficientAsymptotic
import PerronWright.Transfer.PositiveHalfIntegerRate
import PerronWright.Transfer.QuantitativeStirling

/-!
# Field-uniform labelled asymptotics for the positive-surplus cubic part

The coefficient theorem for the normalized cubic-part EGF is converted here
to the corresponding labelled cubic contribution.  This file deliberately
keeps that contribution separate from the total connected weight: the latter
also contains the noncubic fixed-surplus summand.

Two elementary quantitative corrections enter the conversion.  The exact
pure-power coefficient is replaced by its Gamma main term, and the exact
factorial is replaced by its Stirling main term.  Both relative corrections
are `O(k⁻¹)`, hence are absorbed by the half-step error already present in the
joint cubic transfer.
-/

open Filter Topology Set Asymptotics
open scoped Classical Topology BigOperators ENNReal NNReal Real Nat

noncomputable section

namespace PerronWright.PositiveSurplusCubicFieldWeightAsymptotic

open PerronWright.GraphCore

namespace Coeff

export PerronWright.PositiveSurplusCubicCoefficientAsymptotic
  (exists_normalizedFieldCubicPart_coefficient_local_relative_bound
   positiveSurplusCubicExactPurePowerCoefficient_ne_zero)

end Coeff

namespace Global

export PerronWright.PositiveSurplusCubicGlobalContinuation
  (normalizedFieldCubicPartFMS
   normalizedFieldCubicPartFMS_coeff)

end Global

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The labelled connected-weight contribution carried by cubic admissible
cores.  This is the cubic summand only, not the total connected weight. -/
def complexFieldCubicPartConnectedWeight
    (M : CompactBJRModel S) (g : C(S, ℂ))
    (ell k : ℕ) : ℂ :=
  (k.factorial : ℂ) *
    PowerSeries.coeff k (complexFieldCubicPartEGF M g ell)

@[simp] theorem complexFieldCubicPartConnectedWeight_eq
    (M : CompactBJRModel S) (g : C(S, ℂ))
    (ell k : ℕ) :
    complexFieldCubicPartConnectedWeight M g ell k =
      (k.factorial : ℂ) *
        cubicFixedSurplusProfileCompositionCoeff M
          (FieldRootedTree.series M g) ell k := by
  simp [complexFieldCubicPartConnectedWeight]

/-- Division-free coefficient bridge from the normalized cubic-part FMS to
the labelled cubic contribution. -/
theorem radius_pow_mul_complexFieldCubicPartConnectedWeight
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (g : C(S, ℂ)) (ell k : ℕ) :
    (RadiusResponse.radius M hM g) ^ k *
        complexFieldCubicPartConnectedWeight M g ell k =
      (k.factorial : ℂ) *
        (Global.normalizedFieldCubicPartFMS M hM g ell).coeff k := by
  rw [complexFieldCubicPartConnectedWeight,
    Global.normalizedFieldCubicPartFMS_coeff]
  ring

private theorem rpow_neg_one_isBigO_neg_half :
    (fun k : ℕ ↦ (k : ℝ)⁻¹) =O[atTop]
      (fun k : ℕ ↦ (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnonneg : (0 : ℝ) ≤ k := le_trans zero_le_one hkreal
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnonneg),
    Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hnonneg _), one_mul,
    ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hkreal (by norm_num)

private theorem rpow_neg_one_isBigO_one :
    (fun k : ℕ ↦ (k : ℝ)⁻¹) =O[atTop]
      (fun _ : ℕ ↦ (1 : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hinv : 0 ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg k)
  rw [Real.norm_eq_abs, abs_of_nonneg hinv, norm_one, mul_one]
  exact inv_le_one_of_one_le₀ hkreal

/-- The exact pure-power coefficient divided by its Gamma main term is the
standard normalized power coefficient. -/
private theorem exactPurePower_div_main_eq_normalizedPower
    (ell k : ℕ) (hell : 0 < ell) (hk : 0 < k) :
    positiveSurplusCubicExactPurePowerCoefficient ell k /
        positiveSurplusCubicPurePowerCoefficientMain ell k =
      (PerronWright.Transfer.normalizedPowerCoefficient
        (positiveSurplusCubicExponent ell) k : ℂ) := by
  let sigma : ℝ := positiveSurplusCubicExponent ell
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hpowInv :
      ((k : ℝ) ^ (sigma - 1))⁻¹ =
        (k : ℝ) ^ (1 - sigma) := by
    rw [show 1 - sigma = -(sigma - 1) by ring,
      Real.rpow_neg hkreal.le]
  have hreal :
      PerronWright.Transfer.coefficient sigma k /
          ((k : ℝ) ^ (sigma - 1) / Real.Gamma sigma) =
        PerronWright.Transfer.normalizedPowerCoefficient sigma k := by
    unfold PerronWright.Transfer.normalizedPowerCoefficient
    rw [div_div_eq_mul_div, div_eq_mul_inv, hpowInv]
  have hc : positiveSurplusCubicEGFConstant ell ≠ 0 :=
    positiveSurplusCubicEGFConstant_ne_zero ell hell
  unfold positiveSurplusCubicExactPurePowerCoefficient
    positiveSurplusCubicPurePowerCoefficientMain
  rw [mul_div_mul_left _ _ hc]
  exact_mod_cast hreal

/-- Exact algebraic identification of the two relative corrections between
the factorial exact term and the factorial/Gamma main term. -/
private theorem exactFactorial_div_main_eq_normalizedFactors
    (ell k : ℕ) (hell : 0 < ell) (hk : 0 < k) :
    positiveSurplusCubicExactFactorialCoefficient ell k /
        positiveSurplusCubicFactorialMain ell k =
      ((((k.factorial : ℝ) /
          PerronWright.Transfer.factorialStirlingMainTerm k) *
        PerronWright.Transfer.normalizedPowerCoefficient
          (positiveSurplusCubicExponent ell) k : ℝ) : ℂ) := by
  unfold positiveSurplusCubicExactFactorialCoefficient
    positiveSurplusCubicFactorialMain
  rw [mul_div_mul_comm,
    exactPurePower_div_main_eq_normalizedPower ell k hell hk]
  push_cast
  rfl

/-- The exact factorial coefficient differs from the factorial/Gamma main
term only by a relative `O(k⁻¹)` correction. -/
private theorem exactFactorial_div_main_sub_one_isBigO
    (ell : ℕ) (hell : 0 < ell) :
    (fun k : ℕ ↦
      positiveSurplusCubicExactFactorialCoefficient ell k /
          positiveSurplusCubicFactorialMain ell k - 1) =O[atTop]
      (fun k : ℕ ↦ (k : ℝ)⁻¹) := by
  let u : ℕ → ℝ := fun k ↦
    (k.factorial : ℝ) /
      PerronWright.Transfer.factorialStirlingMainTerm k - 1
  let v : ℕ → ℝ := fun k ↦
    PerronWright.Transfer.normalizedPowerCoefficient
      (positiveSurplusCubicExponent ell) k - 1
  have hu : u =O[atTop] (fun k : ℕ ↦ (k : ℝ)⁻¹) := by
    simpa only [u] using
      PerronWright.Transfer.factorial_stirling_relative_error_isBigO
  have hv : v =O[atTop] (fun k : ℕ ↦ (k : ℝ)⁻¹) := by
    have h :=
      PerronWright.Transfer.normalizedPowerCoefficient_three_halves_mul_error_isBigO
        ell hell
    simpa only [v, positiveSurplusCubicExponent,
      Nat.cast_mul, Nat.cast_ofNat] using h
  have huOne : u =O[atTop] (fun _ : ℕ ↦ (1 : ℝ)) :=
    hu.trans rpow_neg_one_isBigO_one
  have huv : (u * v) =O[atTop] (fun k : ℕ ↦ (k : ℝ)⁻¹) := by
    have hmul := huOne.mul hv
    change (fun k ↦ u k * v k) =O[atTop]
      (fun k : ℕ ↦ (k : ℝ)⁻¹)
    simpa only [one_mul] using hmul
  have hreal :
      (fun k : ℕ ↦
        ((u k + 1) * (v k + 1) - 1 : ℝ)) =O[atTop]
        (fun k : ℕ ↦ (k : ℝ)⁻¹) := by
    have hsum := (hu.add hv).add huv
    apply hsum.congr' ?_ (Filter.EventuallyEq.refl _ _)
    exact Filter.Eventually.of_forall fun k ↦ by
      simp only [Pi.mul_apply]
      ring
  have hcast :
      (fun k : ℕ ↦ (((u k + 1) * (v k + 1) - 1 : ℝ) : ℂ))
        =O[atTop] (fun k : ℕ ↦ (k : ℝ)⁻¹) := by
    exact Complex.isBigO_ofReal_left.mpr hreal
  apply hcast.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hk
  rw [exactFactorial_div_main_eq_normalizedFactors ell k hell hkpos]
  dsimp only [u, v]
  push_cast
  ring

/-- The exact cubic factorial coefficient differs from the physical
factorial/Gamma main term by a relative half-step error.  This public form
is also the normalization bridge used for lower-order kernel classes. -/
theorem exactFactorial_div_main_sub_one_isBigO_half
    (ell : ℕ) (hell : 0 < ell) :
    (fun k : ℕ ↦
      positiveSurplusCubicExactFactorialCoefficient ell k /
          positiveSurplusCubicFactorialMain ell k - 1) =O[atTop]
      (fun k : ℕ ↦ (k : ℝ) ^ (-(1 / 2 : ℝ))) :=
  (exactFactorial_div_main_sub_one_isBigO ell hell).trans
    rpow_neg_one_isBigO_neg_half

/-- The labelled cubic-part connected weight has the positive-surplus
Perron--Wright main term uniformly on one genuine complex field ball.

The theorem concerns only the cubic summand.  No equality with the total
connected weight is asserted here. -/
theorem exists_complexFieldCubicPartConnectedWeight_local_relative_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ epsilon K : ℝ, 0 < epsilon ∧ 0 < K ∧
      ∀ᶠ k : ℕ in atTop, ∀ g : C(S, ℂ),
        ‖g‖ ≤ epsilon →
        ‖(RadiusResponse.radius M hM g) ^ k *
              complexFieldCubicPartConnectedWeight M g ell k /
              ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
                positiveSurplusCubicFactorialMain ell k) - 1‖ ≤
          K * (‖g‖ + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨epsilon, Kcoeff, hepsilon, hKcoeff, hcoeff⟩ :=
    Coeff.exists_normalizedFieldCubicPart_coefficient_local_relative_bound
      M hM hell
  have hfactorO :=
    exactFactorial_div_main_sub_one_isBigO_half ell hell
  rw [isBigO_iff] at hfactorO
  obtain ⟨Kfactor₀, hfactor₀⟩ := hfactorO
  let Kfactor : ℝ := max Kfactor₀ 1
  have hKfactor : 0 < Kfactor :=
    lt_of_lt_of_le zero_lt_one (le_max_right Kfactor₀ 1)
  have hfactor : ∀ᶠ k : ℕ in atTop,
      ‖positiveSurplusCubicExactFactorialCoefficient ell k /
          positiveSurplusCubicFactorialMain ell k - 1‖ ≤
        Kfactor * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [hfactor₀] with k hk
    have hx : 0 ≤ (k : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg k) _
    have hk' :
        ‖positiveSurplusCubicExactFactorialCoefficient ell k /
            positiveSurplusCubicFactorialMain ell k - 1‖ ≤
          Kfactor₀ * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hx] using hk
    exact hk'.trans
      (mul_le_mul_of_nonneg_right (le_max_left Kfactor₀ 1) hx)

  let b : ℂ := (Real.sqrt (M.beta hM) : ℂ) ^ ell
  have hb : b ≠ 0 := by
    dsimp only [b]
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.2 (M.beta_pos hM)).ne')
  have hbnorm : 0 < ‖b‖ := norm_pos_iff.mpr hb
  let Kamp : ℝ := Kcoeff / ‖b‖
  have hKamp : 0 < Kamp := div_pos hKcoeff hbnorm
  let K : ℝ := Kamp + Kfactor + Kamp * Kfactor + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨epsilon, K, hepsilon, hK, ?_⟩
  filter_upwards [hcoeff, hfactor, eventually_ge_atTop (1 : ℕ)]
    with k hkcoeff hkfactor hkone
  intro g hg
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hkone
  let x : ℝ := (k : ℝ) ^ (-(1 / 2 : ℝ))
  have hx : 0 ≤ x := by
    dsimp only [x]
    exact Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hxone : x ≤ 1 := by
    dsimp only [x]
    exact Real.rpow_le_one_of_one_le_of_nonpos hkreal (by norm_num)
  let delta : ℝ := ‖g‖ + x
  have hdelta : 0 ≤ delta := add_nonneg (norm_nonneg g) hx
  have hxdelta : x ≤ delta := by
    dsimp only [delta]
    linarith [norm_nonneg g]
  let N : ℂ :=
    (Global.normalizedFieldCubicPartFMS M hM g ell).coeff k
  let E : ℂ := positiveSurplusCubicExactPurePowerCoefficient ell k
  let EF : ℂ := positiveSurplusCubicExactFactorialCoefficient ell k
  let FM : ℂ := positiveSurplusCubicFactorialMain ell k
  let W : ℂ := complexFieldCubicPartConnectedWeight M g ell k
  let A : ℂ := N / (b * E) - 1
  let D : ℂ := EF / FM - 1
  have hE : E ≠ 0 := by
    dsimp only [E]
    exact Coeff.positiveSurplusCubicExactPurePowerCoefficient_ne_zero
      ell k hell
  have hfact : (k.factorial : ℂ) ≠ 0 := by
    exact_mod_cast k.factorial_ne_zero
  have hFM : FM ≠ 0 := by
    dsimp only [FM]
    rw [positiveSurplusCubicFactorialMain_eq_exp_rpow ell hell hkpos]
    apply mul_ne_zero (positiveSurplusWrightConstant_ne_zero ell hell)
    exact Complex.ofReal_ne_zero.mpr
      (mul_pos (Real.exp_pos _)
        (Real.rpow_pos_of_pos (by exact_mod_cast hkpos) _)).ne'
  have hAeq : A = (N / E - b) / b := by
    dsimp only [A]
    field_simp [hb, hE]
  have hA : ‖A‖ ≤ Kamp * delta := by
    rw [hAeq, norm_div]
    have hraw := hkcoeff g hg
    calc
      ‖N / E - b‖ / ‖b‖ ≤
          (Kcoeff * delta) / ‖b‖ := by
        exact div_le_div_of_nonneg_right
          (by simpa only [N, E, b, delta, x] using hraw) hbnorm.le
      _ = Kamp * delta := by
        dsimp only [Kamp]
        ring
  have hD : ‖D‖ ≤ Kfactor * x := by
    simpa only [D, EF, FM, x] using hkfactor
  have hratio :
      (RadiusResponse.radius M hM g) ^ k * W /
          (b * FM) = (A + 1) * (D + 1) := by
    have hbridge :=
      radius_pow_mul_complexFieldCubicPartConnectedWeight
        M hM g ell k
    rw [hbridge]
    dsimp only [A, D, EF,
      positiveSurplusCubicExactFactorialCoefficient]
    field_simp [hb, hE, hFM, hfact]
    ring
  rw [hratio]
  have hdecomp : (A + 1) * (D + 1) - 1 = A + D + A * D := by
    ring
  rw [hdecomp]
  calc
    ‖A + D + A * D‖ ≤ ‖A‖ + ‖D‖ + ‖A‖ * ‖D‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (norm_mul_le _ _))
    _ ≤ Kamp * delta + Kfactor * x +
          (Kamp * delta) * (Kfactor * x) := by
      exact add_le_add (add_le_add hA hD)
        (mul_le_mul hA hD (norm_nonneg _) (by positivity))
    _ ≤ Kamp * delta + Kfactor * delta +
          (Kamp * Kfactor) * delta := by
      have hDmono : Kfactor * x ≤ Kfactor * delta :=
        mul_le_mul_of_nonneg_left hxdelta hKfactor.le
      have hprod :
          (Kamp * delta) * (Kfactor * x) ≤
            (Kamp * Kfactor) * delta := by
        calc
          (Kamp * delta) * (Kfactor * x) =
              (Kamp * Kfactor) * delta * x := by ring
          _ ≤ (Kamp * Kfactor) * delta * 1 := by
            exact mul_le_mul_of_nonneg_left hxone
              (mul_nonneg (mul_pos hKamp hKfactor).le hdelta)
          _ = (Kamp * Kfactor) * delta := by ring
      exact add_le_add
        (add_le_add_right hDmono (Kamp * delta)) hprod
    _ ≤ K * delta := by
      dsimp only [K]
      nlinarith [hKamp.le, hKfactor.le, hdelta]

end PerronWright.PositiveSurplusCubicFieldWeightAsymptotic
