import PerronWright.Enumeration.ZeroFieldTreeCoefficientAsymptotic
import PerronWright.Transfer.NegativeHalfRate
import PerronWright.Transfer.QuantitativeStirling

/-!
# Zero-field tree connected-weight asymptotics

This file converts the analytic coefficient theorem for the genuine
zero-field tree EGF back to the literal finite connected-tree weights.
There are no formal coefficient hypotheses: the coefficient identity is
proved directly from `CompactBJRModel.treeEGF` and the formal multilinear
series whose sum defines `zeroFieldTreeSeries`.

The quantitative half-integer coefficient estimate gives relative
`O(n^(-1/2))` for the EGF coefficient.  Combining this with the proved
quantitative Stirling estimate gives the same relative error for the
Perron--Wright main term

`(gamma / sqrt 2) * n^(-2) * (n / e)^n`.
-/

open Filter Topology PerronWright Set Asymptotics
open scoped Classical Topology ENNReal NNReal Real Nat

noncomputable section

namespace PerronWright.ZeroFieldTreeConnectedWeightAsymptotic

namespace CA

export PerronWright.ZeroFieldTreeCoefficientAsymptotic
  (zeroFieldTree_taylorCoefficient_error_isBigO)

end CA

namespace ZF

export PerronWright.ZeroFieldTreeEGFMatching
  (complexTreeEGF complexTreeEGF_coeff zeroFieldTreeFMS zeroFieldTreeSeries
    one_le_zeroFieldTreeFMS_radius)

end ZF

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- A one-dimensional formal multilinear series is determined by the
ordinary power-series coefficients from which it was constructed. -/
private theorem oneDimensionalFormalMultilinearSeries_eq_ofScalars
    (p : PowerSeries ℂ) :
    oneDimensionalFormalMultilinearSeries p =
      FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ PowerSeries.coeff n p) := by
  let c : ℕ → ℂ := fun n ↦ PowerSeries.coeff n p
  have hpower :
      oneDimensionalPowerSeries
          (FormalMultilinearSeries.ofScalars ℂ
            c) = p := by
    apply PowerSeries.ext
    intro n
    simp only [oneDimensionalPowerSeries_coeff,
      FormalMultilinearSeries.coeff_ofScalars, c]
  calc
    oneDimensionalFormalMultilinearSeries p =
        oneDimensionalFormalMultilinearSeries
          (oneDimensionalPowerSeries
            (FormalMultilinearSeries.ofScalars ℂ c)) :=
      congrArg oneDimensionalFormalMultilinearSeries hpower.symm
    _ = FormalMultilinearSeries.ofScalars ℂ c :=
      oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries _
    _ = FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ PowerSeries.coeff n p) := by rfl

/-- The Taylor coefficient of the genuine analytic tree series is literally
the complexification of the coefficient in `CompactBJRModel.treeEGF`. -/
theorem zeroFieldTree_taylorCoefficient_eq_treeEGF_coeff
    (M : CompactBJRModel S) (n : ℕ) :
    Transfer.taylorCoefficient (ZF.zeroFieldTreeSeries M) n =
      Complex.ofReal (PowerSeries.coeff n (M.treeEGF 0)) := by
  have hpos : 0 < (ZF.zeroFieldTreeFMS M).radius :=
    (by norm_num : (0 : ℝ≥0∞) < 1).trans_le
      (ZF.one_le_zeroFieldTreeFMS_radius M)
  have hp : HasFPowerSeriesAt
      (ZF.zeroFieldTreeSeries M) (ZF.zeroFieldTreeFMS M) 0 :=
    (ZF.zeroFieldTreeFMS M).hasFPowerSeriesOnBall hpos
      |>.hasFPowerSeriesAt
  have hseries : ZF.zeroFieldTreeFMS M =
      FormalMultilinearSeries.ofScalars ℂ
        (fun k ↦ PowerSeries.coeff k (ZF.complexTreeEGF M)) := by
    rw [ZF.zeroFieldTreeFMS,
      oneDimensionalFormalMultilinearSeries_eq_ofScalars]
  rw [hseries] at hp
  rw [Transfer.taylorCoefficient_eq_seriesCoefficient hp n,
    ZF.complexTreeEGF_coeff]

/-- For every positive size, the Taylor coefficient is the literal
zero-field connected-tree weight divided by the vertex factorial. -/
theorem zeroFieldTree_taylorCoefficient_eq_connectedWeight
    (M : CompactBJRModel S) {n : ℕ} (hn : 0 < n) :
    Transfer.taylorCoefficient (ZF.zeroFieldTreeSeries M) n =
      (M.fieldConnectedWeight (0 : C(S, ℝ)) n 0 /
        (n.factorial : ℝ) : ℂ) := by
  rw [zeroFieldTree_taylorCoefficient_eq_treeEGF_coeff]
  simp only [CompactBJRModel.treeEGF, PowerSeries.coeff_mk,
    hn.ne', ↓reduceIte, Complex.ofReal_div, Complex.ofReal_natCast]

/-- The real EGF coefficient inherits the analytic `O(n⁻³)` remainder. -/
theorem zeroFieldTree_connectedWeight_div_factorial_error_isBigO
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fun n : ℕ ↦
      M.fieldConnectedWeight (0 : C(S, ℝ)) n 0 /
          (n.factorial : ℝ) -
        (2 * FoldCoefficients.gamma M hM / 3) *
          Transfer.coefficient (-(3 / 2)) n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 : ℝ))) := by
  have hc := CA.zeroFieldTree_taylorCoefficient_error_isBigO M hM
  obtain ⟨c, hc⟩ := hc.bound
  apply IsBigO.of_bound c
  filter_upwards [hc, eventually_ge_atTop (1 : ℕ)] with n hcn hn
  have hnpos : 0 < n := by omega
  have hcoeff := zeroFieldTree_taylorCoefficient_eq_connectedWeight
    M hnpos
  have heq :
      ((M.fieldConnectedWeight (0 : C(S, ℝ)) n 0 /
          (n.factorial : ℝ) -
        (2 * FoldCoefficients.gamma M hM / 3) *
          Transfer.coefficient (-(3 / 2)) n : ℝ) : ℂ) =
        Transfer.taylorCoefficient (ZF.zeroFieldTreeSeries M) n -
          (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) *
            (Transfer.coefficient (-(3 / 2)) n : ℂ) := by
    rw [hcoeff]
    push_cast
    ring
  rw [← heq] at hcn
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hcn

/-- The natural asymptotic scale of the zero-field tree EGF coefficient. -/
def treeCoefficientMainTerm
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (n : ℕ) : ℝ :=
  FoldCoefficients.gamma M hM / (2 * Real.sqrt Real.pi) *
    (n : ℝ) ^ (-(5 / 2 : ℝ))

private theorem treeCoefficientMainTerm_pos
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (hn : 0 < n) :
    0 < treeCoefficientMainTerm M hM n := by
  unfold treeCoefficientMainTerm
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos
    (div_pos (FoldCoefficients.gamma_pos M hM)
      (mul_pos (by norm_num) (Real.sqrt_pos.2 Real.pi_pos)))
    (Real.rpow_pos_of_pos hnreal _)

private theorem inv_treeCoefficientMainTerm_eq
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (hn : 0 < n) :
    (treeCoefficientMainTerm M hM n)⁻¹ =
      (2 * Real.sqrt Real.pi / FoldCoefficients.gamma M hM) *
        (n : ℝ) ^ (5 / 2 : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hgamma : FoldCoefficients.gamma M hM ≠ 0 :=
    (FoldCoefficients.gamma_pos M hM).ne'
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpow : (n : ℝ) ^ (5 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hnreal _).ne'
  unfold treeCoefficientMainTerm
  rw [Real.rpow_neg hnreal.le]
  field_simp [hgamma, hsqrt, hpow]

private theorem leading_div_treeCoefficientMainTerm_eq
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (hn : 0 < n) :
    ((2 * FoldCoefficients.gamma M hM / 3) *
        Transfer.coefficient (-(3 / 2)) n) /
        treeCoefficientMainTerm M hM n =
      Transfer.coefficient (-(3 / 2)) n *
        (4 * Real.sqrt Real.pi * (n : ℝ) ^ 2 *
          Real.sqrt (n : ℝ) / 3) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hgamma : FoldCoefficients.gamma M hM ≠ 0 :=
    (FoldCoefficients.gamma_pos M hM).ne'
  have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hpow : (n : ℝ) ^ (5 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hnreal _).ne'
  have hpowEq : (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) =
      (n : ℝ) ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_two, Real.sqrt_eq_rpow,
      ← Real.rpow_add hnreal]
    norm_num
  calc
    ((2 * FoldCoefficients.gamma M hM / 3) *
          Transfer.coefficient (-(3 / 2)) n) /
          treeCoefficientMainTerm M hM n =
        (2 * FoldCoefficients.gamma M hM / 3) *
          Transfer.coefficient (-(3 / 2)) n *
            ((2 * Real.sqrt Real.pi / FoldCoefficients.gamma M hM) *
              (n : ℝ) ^ (5 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, inv_treeCoefficientMainTerm_eq M hM hn]
    _ = Transfer.coefficient (-(3 / 2)) n *
          (4 * Real.sqrt Real.pi * (n : ℝ) ^ (5 / 2 : ℝ) / 3) := by
      field_simp [hgamma]
      ring
    _ = Transfer.coefficient (-(3 / 2)) n *
          (4 * Real.sqrt Real.pi * (n : ℝ) ^ 2 *
            Real.sqrt (n : ℝ) / 3) := by
      rw [← hpowEq]
      ring

private theorem rpow_neg_one_isBigO_neg_half :
    (fun n : ℕ ↦ (n : ℝ)⁻¹) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnonneg : (0 : ℝ) ≤ n := le_trans zero_le_one hnreal
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnonneg),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnonneg _), one_mul,
    ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hnreal (by norm_num)

/-- Quantitative relative asymptotics of the literal EGF coefficient. -/
theorem zeroFieldTree_connectedWeight_div_factorial_relative_error_isBigO
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fun n : ℕ ↦
      (M.fieldConnectedWeight (0 : C(S, ℝ)) n 0 /
          (n.factorial : ℝ)) /
          treeCoefficientMainTerm M hM n - 1) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let a : ℕ → ℝ := fun n ↦
    M.fieldConnectedWeight (0 : C(S, ℝ)) n 0 /
      (n.factorial : ℝ)
  let b : ℕ → ℝ := fun n ↦
    (2 * FoldCoefficients.gamma M hM / 3) *
      Transfer.coefficient (-(3 / 2)) n
  let q : ℕ → ℝ := fun n ↦ treeCoefficientMainTerm M hM n

  have hab : (fun n ↦ a n - b n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(3 : ℝ))) := by
    simpa only [a, b] using
      zeroFieldTree_connectedWeight_div_factorial_error_isBigO M hM
  have hqinv : (fun n : ℕ ↦ (q n)⁻¹) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (5 / 2 : ℝ)) := by
    have hbase :
        (fun n : ℕ ↦ (n : ℝ) ^ (5 / 2 : ℝ)) =O[atTop]
          (fun n : ℕ ↦ (n : ℝ) ^ (5 / 2 : ℝ)) :=
      isBigO_refl _ _
    have hscaled := hbase.const_mul_left
      (2 * Real.sqrt Real.pi / FoldCoefficients.gamma M hM)
    apply hscaled.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact (inv_treeCoefficientMainTerm_eq M hM (by omega)).symm
  have hresidual : (fun n : ℕ ↦ (a n - b n) / q n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    have hmul := Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (-(3 : ℝ)) (5 / 2 : ℝ) (-(1 / 2 : ℝ)) hab hqinv (by norm_num)
    apply hmul.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards with n
    simp only [Pi.mul_apply, div_eq_mul_inv]
  have hleading : (fun n : ℕ ↦ b n / q n - 1) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ)⁻¹) := by
    have h := Transfer.coefficient_neg_three_halves_relative_error_isBigO
    apply h.congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [leading_div_treeCoefficientMainTerm_eq M hM (by omega)]
  have hleading' : (fun n : ℕ ↦ b n / q n - 1) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ))) :=
    hleading.trans rpow_neg_one_isBigO_neg_half
  have hsum := hresidual.add hleading'
  apply hsum.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hqne : q n ≠ 0 :=
    (treeCoefficientMainTerm_pos M hM (by omega)).ne'
  dsimp only [a, b, q]
  field_simp [hqne]
  ring

/-- The classical zero-surplus Perron--Wright main term. -/
def treePerronWrightMainTerm
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (n : ℕ) : ℝ :=
  FoldCoefficients.gamma M hM / Real.sqrt 2 *
    (n : ℝ) ^ (-(2 : ℝ)) *
      ((n : ℝ) / Real.exp 1) ^ n

/-- The product of the Stirling main term and the singularity-analysis main
coefficient is exactly the classical Perron--Wright expression. -/
theorem factorialStirlingMainTerm_mul_treeCoefficientMainTerm_eq
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (hn : 0 < n) :
    Transfer.factorialStirlingMainTerm n *
        treeCoefficientMainTerm M hM n =
      treePerronWrightMainTerm M hM n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hroot : Real.sqrt (2 * Real.pi * (n : ℝ)) =
      Real.sqrt 2 * Real.sqrt Real.pi * Real.sqrt (n : ℝ) := by
    rw [show 2 * Real.pi * (n : ℝ) = (2 * Real.pi) * (n : ℝ) by ring,
      Real.sqrt_mul (mul_nonneg (by norm_num) Real.pi_pos.le),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow : Real.sqrt (n : ℝ) *
      (n : ℝ) ^ (-(5 / 2 : ℝ)) =
        (n : ℝ) ^ (-(2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnreal]
    norm_num
  have hsqrt2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold Transfer.factorialStirlingMainTerm treeCoefficientMainTerm
    treePerronWrightMainTerm
  rw [hroot]
  rw [show (Real.sqrt 2 * Real.sqrt Real.pi * Real.sqrt (n : ℝ)) *
      ((n : ℝ) / Real.exp 1) ^ n *
        (FoldCoefficients.gamma M hM / (2 * Real.sqrt Real.pi) *
          (n : ℝ) ^ (-(5 / 2 : ℝ))) =
      (FoldCoefficients.gamma M hM * Real.sqrt 2 / 2) *
        (Real.sqrt (n : ℝ) * (n : ℝ) ^ (-(5 / 2 : ℝ))) *
          ((n : ℝ) / Real.exp 1) ^ n by
        field_simp [hsqrtpi]
        ]
  rw [hpow]
  field_simp [hsqrt2]
  rw [pow_two, hsqrt2sq]

private theorem rpow_neg_one_isBigO_one :
    (fun n : ℕ ↦ (n : ℝ)⁻¹) =O[atTop] (fun _ : ℕ ↦ (1 : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinvnonneg : 0 ≤ (n : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg n)
  rw [Real.norm_eq_abs, abs_of_nonneg hinvnonneg, norm_one, mul_one]
  exact inv_le_one_of_one_le₀ hnreal

/-- Perron--Wright asymptotics for the literal zero-field connected-tree
weight, with relative `O(n^(-1/2))` error. -/
theorem zeroFieldTree_connectedWeight_perronWright_relative_error_isBigO
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (fun n : ℕ ↦
      M.fieldConnectedWeight (0 : C(S, ℝ)) n 0 /
          treePerronWrightMainTerm M hM n - 1) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let s : ℕ → ℝ := fun n ↦
    (n.factorial : ℝ) / Transfer.factorialStirlingMainTerm n - 1
  let e : ℕ → ℝ := fun n ↦
    (M.fieldConnectedWeight (0 : C(S, ℝ)) n 0 /
        (n.factorial : ℝ)) /
        treeCoefficientMainTerm M hM n - 1
  have hs : s =O[atTop] (fun n : ℕ ↦ (n : ℝ)⁻¹) := by
    simpa only [s] using Transfer.factorial_stirling_relative_error_isBigO
  have hsHalf : s =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ))) :=
    hs.trans rpow_neg_one_isBigO_neg_half
  have hsOne : s =O[atTop] (fun _ : ℕ ↦ (1 : ℝ)) :=
    hs.trans rpow_neg_one_isBigO_one
  have he : e =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    simpa only [e] using
      zeroFieldTree_connectedWeight_div_factorial_relative_error_isBigO M hM
  have hse : (s * e) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    have hmul := hsOne.mul he
    change (fun n ↦ s n * e n) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ)))
    simpa only [one_mul] using hmul
  have hsum := (hsHalf.add he).add hse
  apply hsum.congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < n := by omega
  have hfact : (n.factorial : ℝ) ≠ 0 := by positivity
  have hstirling : Transfer.factorialStirlingMainTerm n ≠ 0 := by
    unfold Transfer.factorialStirlingMainTerm
    positivity
  have hcoeffMain : treeCoefficientMainTerm M hM n ≠ 0 :=
    (treeCoefficientMainTerm_pos M hM hnpos).ne'
  have hPW : treePerronWrightMainTerm M hM n ≠ 0 := by
    rw [← factorialStirlingMainTerm_mul_treeCoefficientMainTerm_eq
      M hM hnpos]
    exact mul_ne_zero hstirling hcoeffMain
  rw [← factorialStirlingMainTerm_mul_treeCoefficientMainTerm_eq
    M hM hnpos]
  dsimp only [s, e]
  simp only [Pi.mul_apply]
  field_simp [hfact, hstirling, hcoeffMain, hPW]
  ring

end PerronWright.ZeroFieldTreeConnectedWeightAsymptotic
