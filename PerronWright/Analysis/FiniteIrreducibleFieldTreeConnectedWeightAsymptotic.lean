import PerronWright.Analysis.FiniteIrreducibleFieldTreeUniformCoefficientAsymptotic
import PerronWright.Analysis.FiniteIrreducibleTreeMainTerm
import PerronWright.Transfer.NegativeHalfRate

/-!
# Field-uniform connected-tree Perron--Wright asymptotics

This file performs the last coefficient-to-weight conversion for trees.  The
first theorem is an exact identity: the coefficient of the normalized
complex-field tree series is the literal connected-tree weight, multiplied
by the genuine critical-radius factor and divided by the vertex factorial.

The analytic cubic amplitude is only used through its Frechet
differentiability at the zero field.  Together with the common `n^(-3)`
coefficient remainder, the explicit half-integer coefficient estimate, and
quantitative Stirling, this gives one relative-error constant for all fields
in a shrinking ball `‖g‖ <= U n^(-1/2)`.  The field ball is never treated as
compact.
-/

open Filter Topology Set Asymptotics
open scoped Classical Topology ENNReal NNReal Real Nat

noncomputable section

namespace PerronWright.FiniteIrreducibleFieldTreeConnectedWeightAsymptotic

namespace Uniform

export PerronWright.FiniteIrreducibleFieldTreeUniformCoefficientAsymptotic
  (exists_normalizedFieldTree_coefficient_uniform_bound)

end Uniform

namespace FT

export PerronWright.FiniteIrreducibleFieldTreeEGFMatching
  (complexFieldTreeEGF complexFieldTreeEGF_coeff fieldTreeFMS
    normalizedFieldTreeFMS comp_smul_id_coeff)

end FT

namespace Zero

export PerronWright.FiniteIrreducibleTreeMainTerm
  (treeCoefficientMainTerm factorialStirlingMainTerm_mul_treeCoefficientMainTerm_eq)

end Zero

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The normalized formal coefficient is exactly the literal complex-field
connected-tree weight, with the critical-radius change of activity made
explicit. -/
theorem normalizedFieldTreeFMS_coeff_eq_connectedWeight
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (g : C(S, ℂ)) {n : ℕ} (hn : 0 < n) :
    (FT.normalizedFieldTreeFMS M hM g).coeff n =
      (FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
        M.bjrModel.complexFieldConnectedWeight g n 0 / (n.factorial : ℂ) := by
  rw [FT.normalizedFieldTreeFMS, FT.comp_smul_id_coeff]
  simp only [FT.fieldTreeFMS,
    oneDimensionalFormalMultilinearSeries_coeff,
    FT.complexFieldTreeEGF_coeff, if_neg hn.ne', smul_eq_mul]
  ring

/-- The final tree main term, written with Wright's constant in the requested
`beta^(-1/2)` normalization. -/
def fieldTreePerronWrightMainTerm
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (n : ℕ) : ℝ :=
  (M.beta hM) ^ (-(1 / 2 : ℝ)) *
    (n : ℝ) ^ (-(2 : ℝ)) *
      ((n : ℝ) / Real.exp 1) ^ n

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
private theorem gamma_div_sqrt_two_eq_beta_rpow
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    FiniteIrreducibleFoldCoefficients.gamma M hM / Real.sqrt 2 =
      (M.beta hM) ^ (-(1 / 2 : ℝ)) := by
  have hb : 0 < M.beta hM := M.beta_pos hM
  have hsqrtb : Real.sqrt (M.beta hM) ≠ 0 := by positivity
  have hsqrt2 : Real.sqrt 2 ≠ 0 := by positivity
  unfold FiniteIrreducibleFoldCoefficients.gamma
  rw [Real.sqrt_div (by positivity), Real.rpow_neg hb.le,
    ← Real.sqrt_eq_rpow]
  field_simp [hsqrtb, hsqrt2]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
private theorem zeroTreePerronWrightMainTerm_eq_field
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (n : ℕ) :
    PerronWright.FiniteIrreducibleTreeMainTerm.treePerronWrightMainTerm
        M hM n = fieldTreePerronWrightMainTerm M hM n := by
  unfold PerronWright.FiniteIrreducibleTreeMainTerm.treePerronWrightMainTerm
    fieldTreePerronWrightMainTerm
  rw [gamma_div_sqrt_two_eq_beta_rpow]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
/-- Stirling's main term times the tree coefficient main term is the
`beta^(-1/2)` Perron--Wright main term. -/
theorem factorialStirlingMainTerm_mul_treeCoefficientMainTerm_eq_field
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (hn : 0 < n) :
    Transfer.factorialStirlingMainTerm n *
        Zero.treeCoefficientMainTerm M hM n =
      fieldTreePerronWrightMainTerm M hM n := by
  rw [Zero.factorialStirlingMainTerm_mul_treeCoefficientMainTerm_eq
    M hM hn, zeroTreePerronWrightMainTerm_eq_field]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
private theorem treeCoefficientMainTerm_pos
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (hn : 0 < n) :
    0 < Zero.treeCoefficientMainTerm M hM n := by
  unfold PerronWright.FiniteIrreducibleTreeMainTerm.treeCoefficientMainTerm
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos
    (div_pos (FiniteIrreducibleFoldCoefficients.gamma_pos M hM)
      (mul_pos (by norm_num) (Real.sqrt_pos.2 Real.pi_pos)))
    (Real.rpow_pos_of_pos hnreal _)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
private theorem leading_div_treeCoefficientMainTerm_eq
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (hn : 0 < n) :
    ((2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) *
        Transfer.coefficient (-(3 / 2)) n) /
        Zero.treeCoefficientMainTerm M hM n =
      Transfer.coefficient (-(3 / 2)) n *
        (4 * Real.sqrt Real.pi * (n : ℝ) ^ 2 *
          Real.sqrt (n : ℝ) / 3) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hgamma : FiniteIrreducibleFoldCoefficients.gamma M hM ≠ 0 :=
    (FiniteIrreducibleFoldCoefficients.gamma_pos M hM).ne'
  have hsqrtpi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpow : (n : ℝ) ^ (5 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hnreal _).ne'
  have hpowEq : (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) =
      (n : ℝ) ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_two, Real.sqrt_eq_rpow,
      ← Real.rpow_add hnreal]
    norm_num
  unfold PerronWright.FiniteIrreducibleTreeMainTerm.treeCoefficientMainTerm
  rw [Real.rpow_neg hnreal.le]
  rw [← hpowEq]
  field_simp [hgamma, hsqrtpi, hpow]
  ring

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
private theorem inv_treeCoefficientMainTerm_eq
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (hn : 0 < n) :
    (Zero.treeCoefficientMainTerm M hM n)⁻¹ =
      (2 * Real.sqrt Real.pi / FiniteIrreducibleFoldCoefficients.gamma M hM) *
        (n : ℝ) ^ (5 / 2 : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hgamma : FiniteIrreducibleFoldCoefficients.gamma M hM ≠ 0 :=
    (FiniteIrreducibleFoldCoefficients.gamma_pos M hM).ne'
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  have hpow : (n : ℝ) ^ (5 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hnreal _).ne'
  unfold PerronWright.FiniteIrreducibleTreeMainTerm.treeCoefficientMainTerm
  rw [Real.rpow_neg hnreal.le]
  field_simp [hgamma, hsqrt, hpow]

private theorem rpow_neg_one_le_neg_half {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ)⁻¹ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hnreal (by norm_num)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
private theorem rpow_neg_three_mul_main_inverse
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (-(3 : ℝ)) *
        (Zero.treeCoefficientMainTerm M hM n)⁻¹ =
      (2 * Real.sqrt Real.pi / FiniteIrreducibleFoldCoefficients.gamma M hM) *
        (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  rw [inv_treeCoefficientMainTerm_eq M hM hn]
  calc
    (n : ℝ) ^ (-(3 : ℝ)) *
          ((2 * Real.sqrt Real.pi / FiniteIrreducibleFoldCoefficients.gamma M hM) *
            (n : ℝ) ^ (5 / 2 : ℝ)) =
        (2 * Real.sqrt Real.pi / FiniteIrreducibleFoldCoefficients.gamma M hM) *
          ((n : ℝ) ^ (-(3 : ℝ)) *
            (n : ℝ) ^ (5 / 2 : ℝ)) := by ring
    _ = (2 * Real.sqrt Real.pi / FiniteIrreducibleFoldCoefficients.gamma M hM) *
          (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hnreal]
      norm_num

/-- Uniform relative coefficient estimate in every fixed shrinking field
window.  The eventual threshold and the constant are common to all fields
in that window. -/
theorem exists_normalizedFieldTree_coefficient_shrinking_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (U : ℝ) (hU : 0 ≤ U) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ g : C(S, ℂ),
        ‖g‖ ≤ U * (n : ℝ) ^ (-(1 / 2 : ℝ)) →
        ‖(FT.normalizedFieldTreeFMS M hM g).coeff n /
              (Zero.treeCoefficientMainTerm M hM n : ℂ) - 1‖ ≤
          K * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨A₃, s, K₀, N₀, hs, hK₀, hA₃, hA₃zero, hcoeff⟩ :=
    Uniform.exists_normalizedFieldTree_coefficient_uniform_bound M hM
  have hzero : (0 : C(S, ℂ)) ∈ Metric.ball 0 s := by
    simpa only [Metric.mem_ball, dist_self] using hs
  have hA₃at : AnalyticAt ℂ A₃ 0 := hA₃ 0 hzero
  have hA₃O : (fun g : C(S, ℂ) ↦ A₃ g - A₃ 0) =O[nhds 0]
      (fun g : C(S, ℂ) ↦ g) := by
    simpa only [sub_zero] using hA₃at.differentiableAt.isBigO_sub
  obtain ⟨L₀, hL₀⟩ := isBigO_iff.mp hA₃O
  let L : ℝ := max L₀ 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right L₀ 1)
  have hLipEventually : ∀ᶠ g : C(S, ℂ) in nhds 0,
      ‖A₃ g - A₃ 0‖ ≤ L * ‖g‖ := by
    filter_upwards [hL₀] with g hg
    exact hg.trans (mul_le_mul_of_nonneg_right (le_max_left L₀ 1) (norm_nonneg g))
  obtain ⟨s₁, hs₁, hLipBall⟩ := Metric.mem_nhds_iff.mp hLipEventually
  let r : ℝ := min s s₁
  have hr : 0 < r := lt_min hs hs₁
  let gamma : ℝ := FiniteIrreducibleFoldCoefficients.gamma M hM
  let Krem : ℝ := 2 * Real.sqrt Real.pi * K₀ / gamma
  let Kamp : ℝ := 3 * L * U / gamma
  let K : ℝ := Krem + Kamp + 6
  have hgamma : 0 < gamma := FiniteIrreducibleFoldCoefficients.gamma_pos M hM
  have hKrem : 0 < Krem := by
    dsimp only [Krem, gamma]
    positivity
  have hKamp : 0 ≤ Kamp := by
    dsimp only [Kamp, gamma]
    positivity
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  have hhalf : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have hwindow : Tendsto
      (fun n : ℕ ↦ U * (n : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hhalf
  have hnear : ∀ᶠ n : ℕ in atTop,
      U * (n : ℝ) ^ (-(1 / 2 : ℝ)) < r :=
    hwindow.eventually (isOpen_Iio.mem_nhds hr)
  filter_upwards [eventually_ge_atTop (max N₀ 6), hnear]
    with n hn hnnear
  intro g hg
  have hn₀ : N₀ ≤ n := (le_max_left N₀ 6).trans hn
  have hn6 : 6 ≤ n := (le_max_right N₀ 6).trans hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hgr : ‖g‖ < r := hg.trans_lt hnnear
  have hgs : g ∈ Metric.ball (0 : C(S, ℂ)) s := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hgr.trans_le (min_le_left s s₁)
  have hgs₁ : g ∈ Metric.ball (0 : C(S, ℂ)) s₁ := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hgr.trans_le (min_le_right s s₁)
  have hAmp : ‖A₃ g - A₃ 0‖ ≤
      L * U * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖A₃ g - A₃ 0‖ ≤ L * ‖g‖ := hLipBall hgs₁
      _ ≤ L * (U * (n : ℝ) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hg hL.le
      _ = L * U * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
  have hCoeff := hcoeff g hgs n hn₀
  let q : ℝ := Zero.treeCoefficientMainTerm M hM n
  let c : ℝ := Transfer.coefficient (-(3 / 2)) n
  let D : ℝ :=
    4 * Real.sqrt Real.pi * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 3
  have hq : 0 < q := treeCoefficientMainTerm_pos M hM hnpos
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hsing := Transfer.coefficient_neg_three_halves_relative_error_bound
    n (by omega : 3 ≤ n)
  have hnormCD : |c * D| ≤ 2 := by
    have hone : 6 * (n : ℝ)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hnreal]
      simpa only [one_mul] using
        (show (6 : ℝ) ≤ n by exact_mod_cast hn6)
    have herror : |c * D - 1| ≤ 1 := by
      dsimp only [c, D]
      exact hsing.trans hone
    calc
      |c * D| = |(c * D - 1) + 1| := by
        congr 1
        ring
      _ ≤ |c * D - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ 2 := by norm_num at herror ⊢; linarith
  have hleadRatio :
      ((2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) * c) / q = c * D := by
    simpa only [q, c, D] using
      leading_div_treeCoefficientMainTerm_eq M hM hnpos
  have hcq : ‖(c : ℂ) / (q : ℂ)‖ ≤ 3 / gamma := by
    have hA₀ : 0 < 2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3 := by positivity
    have hrealEq : (2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) * (c / q) =
        c * D := by
      calc
        (2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) * (c / q) =
            ((2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) * c) / q := by ring
        _ = c * D := hleadRatio
    have hnormEq :
        (2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) * |c / q| = |c * D| := by
      rw [← abs_of_pos hA₀, ← abs_mul, hrealEq]
    rw [norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq]
    calc
      |c| / q = |c / q| := by rw [abs_div, abs_of_pos hq]
      _ = |c * D| / (2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) := by
        apply (eq_div_iff hA₀.ne').2
        nlinarith [hnormEq]
      _ ≤ 2 / (2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) :=
        div_le_div_of_nonneg_right hnormCD hA₀.le
      _ = 3 / gamma := by
        dsimp only [gamma]
        field_simp [(FiniteIrreducibleFoldCoefficients.gamma_pos M hM).ne']
  have hrem :
      ‖((FT.normalizedFieldTreeFMS M hM g).coeff n - A₃ g * (c : ℂ)) /
          (q : ℂ)‖ ≤
        Krem * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    calc
      ‖(FT.normalizedFieldTreeFMS M hM g).coeff n - A₃ g * (c : ℂ)‖ /
          q ≤ (K₀ * (n : ℝ) ^ (-(3 : ℝ))) / q :=
        div_le_div_of_nonneg_right (by simpa only [c] using hCoeff) hq.le
      _ = Krem * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [div_eq_mul_inv, mul_assoc,
          rpow_neg_three_mul_main_inverse M hM hnpos]
        dsimp only [Krem, gamma]
        ring
  have hampTerm :
      ‖(A₃ g - A₃ 0) * ((c : ℂ) / (q : ℂ))‖ ≤
        Kamp * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul]
    calc
      ‖A₃ g - A₃ 0‖ * ‖(c : ℂ) / (q : ℂ)‖ ≤
          (L * U * (n : ℝ) ^ (-(1 / 2 : ℝ))) * (3 / gamma) :=
        mul_le_mul hAmp hcq (norm_nonneg _) (by positivity)
      _ = Kamp * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        dsimp only [Kamp]
        ring
  have hleadTerm :
      ‖((A₃ 0 * (c : ℂ)) / (q : ℂ)) - 1‖ ≤
        6 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hcast :
        (A₃ 0 * (c : ℂ)) / (q : ℂ) = (c * D : ℝ) := by
      rw [hA₃zero]
      exact_mod_cast hleadRatio
    rw [hcast]
    have hrealSub : (((c * D : ℝ) : ℂ) - 1) =
        ((c * D - 1 : ℝ) : ℂ) := by
      norm_num
    rw [hrealSub, Complex.norm_real, Real.norm_eq_abs]
    calc
      |c * D - 1| ≤ 6 * (n : ℝ)⁻¹ := by
        simpa only [c, D] using hsing
      _ ≤ 6 * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (rpow_neg_one_le_neg_half (by omega : 1 ≤ n)) (by norm_num)
  have hdecomp :
      (FT.normalizedFieldTreeFMS M hM g).coeff n / (q : ℂ) - 1 =
        ((FT.normalizedFieldTreeFMS M hM g).coeff n - A₃ g * (c : ℂ)) /
            (q : ℂ) +
          (A₃ g - A₃ 0) * ((c : ℂ) / (q : ℂ)) +
          ((A₃ 0 * (c : ℂ)) / (q : ℂ) - 1) := by
    have hqne : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    field_simp [hqne]
    ring
  rw [hdecomp]
  calc
    ‖((FT.normalizedFieldTreeFMS M hM g).coeff n - A₃ g * (c : ℂ)) /
          (q : ℂ) +
        (A₃ g - A₃ 0) * ((c : ℂ) / (q : ℂ)) +
        ((A₃ 0 * (c : ℂ)) / (q : ℂ) - 1)‖ ≤
        ‖((FT.normalizedFieldTreeFMS M hM g).coeff n - A₃ g * (c : ℂ)) /
          (q : ℂ)‖ +
        ‖(A₃ g - A₃ 0) * ((c : ℂ) / (q : ℂ))‖ +
        ‖((A₃ 0 * (c : ℂ)) / (q : ℂ) - 1)‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add_left (norm_add_le _ _) _)
    _ ≤ Krem * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
        Kamp * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
        6 * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
      add_le_add (add_le_add hrem hampTerm) hleadTerm
    _ = K * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      dsimp only [K]
      ring

/-- Local relative coefficient estimate with the field displacement and the
coefficient-transfer error kept separate.  This is the form needed for an
arbitrary shrinking field window, rather than only the square-root window. -/
theorem exists_normalizedFieldTree_coefficient_local_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ g : C(S, ℂ),
        ‖g‖ ≤ ε →
        ‖(FT.normalizedFieldTreeFMS M hM g).coeff n /
              (Zero.treeCoefficientMainTerm M hM n : ℂ) - 1‖ ≤
          K * (‖g‖ + (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨A₃, s, K₀, N₀, hs, hK₀, hA₃, hA₃zero, hcoeff⟩ :=
    Uniform.exists_normalizedFieldTree_coefficient_uniform_bound M hM
  have hzero : (0 : C(S, ℂ)) ∈ Metric.ball 0 s := by
    simpa only [Metric.mem_ball, dist_self] using hs
  have hA₃at : AnalyticAt ℂ A₃ 0 := hA₃ 0 hzero
  have hA₃O : (fun g : C(S, ℂ) ↦ A₃ g - A₃ 0) =O[nhds 0]
      (fun g : C(S, ℂ) ↦ g) := by
    simpa only [sub_zero] using hA₃at.differentiableAt.isBigO_sub
  obtain ⟨L₀, hL₀⟩ := isBigO_iff.mp hA₃O
  let L : ℝ := max L₀ 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right L₀ 1)
  have hLipEventually : ∀ᶠ g : C(S, ℂ) in nhds 0,
      ‖A₃ g - A₃ 0‖ ≤ L * ‖g‖ := by
    filter_upwards [hL₀] with g hg
    exact hg.trans (mul_le_mul_of_nonneg_right (le_max_left L₀ 1) (norm_nonneg g))
  obtain ⟨s₁, hs₁, hLipBall⟩ := Metric.mem_nhds_iff.mp hLipEventually
  let r : ℝ := min s s₁
  have hr : 0 < r := lt_min hs hs₁
  let ε : ℝ := r / 2
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  let gamma : ℝ := FiniteIrreducibleFoldCoefficients.gamma M hM
  let Krem : ℝ := 2 * Real.sqrt Real.pi * K₀ / gamma
  let Kamp : ℝ := 3 * L / gamma
  let K : ℝ := Krem + Kamp + 6
  have hgamma : 0 < gamma := FiniteIrreducibleFoldCoefficients.gamma_pos M hM
  have hKrem : 0 < Krem := by
    dsimp only [Krem, gamma]
    positivity
  have hKamp : 0 < Kamp := by
    dsimp only [Kamp, gamma]
    positivity
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨ε, K, hε, hK, ?_⟩
  filter_upwards [eventually_ge_atTop (max N₀ 6)] with n hn
  intro g hg
  have hn₀ : N₀ ≤ n := (le_max_left N₀ 6).trans hn
  have hn6 : 6 ≤ n := (le_max_right N₀ 6).trans hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hεr : ε < r := by
    dsimp only [ε]
    linarith
  have hgr : ‖g‖ < r := hg.trans_lt hεr
  have hgs : g ∈ Metric.ball (0 : C(S, ℂ)) s := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hgr.trans_le (min_le_left s s₁)
  have hgs₁ : g ∈ Metric.ball (0 : C(S, ℂ)) s₁ := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hgr.trans_le (min_le_right s s₁)
  have hAmp : ‖A₃ g - A₃ 0‖ ≤ L * ‖g‖ := hLipBall hgs₁
  have hCoeff := hcoeff g hgs n hn₀
  let q : ℝ := Zero.treeCoefficientMainTerm M hM n
  let c : ℝ := Transfer.coefficient (-(3 / 2)) n
  let D : ℝ :=
    4 * Real.sqrt Real.pi * (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 3
  have hq : 0 < q := treeCoefficientMainTerm_pos M hM hnpos
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hsing := Transfer.coefficient_neg_three_halves_relative_error_bound
    n (by omega : 3 ≤ n)
  have hnormCD : |c * D| ≤ 2 := by
    have hone : 6 * (n : ℝ)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hnreal]
      simpa only [one_mul] using
        (show (6 : ℝ) ≤ n by exact_mod_cast hn6)
    have herror : |c * D - 1| ≤ 1 := by
      dsimp only [c, D]
      exact hsing.trans hone
    calc
      |c * D| = |(c * D - 1) + 1| := by
        congr 1
        ring
      _ ≤ |c * D - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ 2 := by norm_num at herror ⊢; linarith
  have hleadRatio :
      ((2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) * c) / q = c * D := by
    simpa only [q, c, D] using
      leading_div_treeCoefficientMainTerm_eq M hM hnpos
  have hcq : ‖(c : ℂ) / (q : ℂ)‖ ≤ 3 / gamma := by
    have hA₀ : 0 < 2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3 := by positivity
    have hrealEq : (2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) * (c / q) =
        c * D := by
      calc
        (2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) * (c / q) =
            ((2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) * c) / q := by ring
        _ = c * D := hleadRatio
    have hnormEq :
        (2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) * |c / q| = |c * D| := by
      rw [← abs_of_pos hA₀, ← abs_mul, hrealEq]
    rw [norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq]
    calc
      |c| / q = |c / q| := by rw [abs_div, abs_of_pos hq]
      _ = |c * D| / (2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) := by
        apply (eq_div_iff hA₀.ne').2
        nlinarith [hnormEq]
      _ ≤ 2 / (2 * FiniteIrreducibleFoldCoefficients.gamma M hM / 3) :=
        div_le_div_of_nonneg_right hnormCD hA₀.le
      _ = 3 / gamma := by
        dsimp only [gamma]
        field_simp [(FiniteIrreducibleFoldCoefficients.gamma_pos M hM).ne']
  have hrem :
      ‖((FT.normalizedFieldTreeFMS M hM g).coeff n - A₃ g * (c : ℂ)) /
          (q : ℂ)‖ ≤
        Krem * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    calc
      ‖(FT.normalizedFieldTreeFMS M hM g).coeff n - A₃ g * (c : ℂ)‖ /
          q ≤ (K₀ * (n : ℝ) ^ (-(3 : ℝ))) / q :=
        div_le_div_of_nonneg_right (by simpa only [c] using hCoeff) hq.le
      _ = Krem * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [div_eq_mul_inv, mul_assoc,
          rpow_neg_three_mul_main_inverse M hM hnpos]
        dsimp only [Krem, gamma]
        ring
  have hampTerm :
      ‖(A₃ g - A₃ 0) * ((c : ℂ) / (q : ℂ))‖ ≤
        Kamp * ‖g‖ := by
    rw [norm_mul]
    calc
      ‖A₃ g - A₃ 0‖ * ‖(c : ℂ) / (q : ℂ)‖ ≤
          (L * ‖g‖) * (3 / gamma) :=
        mul_le_mul hAmp hcq (norm_nonneg _) (by positivity)
      _ = Kamp * ‖g‖ := by
        dsimp only [Kamp]
        ring
  have hleadTerm :
      ‖((A₃ 0 * (c : ℂ)) / (q : ℂ)) - 1‖ ≤
        6 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hcast :
        (A₃ 0 * (c : ℂ)) / (q : ℂ) = (c * D : ℝ) := by
      rw [hA₃zero]
      exact_mod_cast hleadRatio
    rw [hcast]
    have hrealSub : (((c * D : ℝ) : ℂ) - 1) =
        ((c * D - 1 : ℝ) : ℂ) := by
      norm_num
    rw [hrealSub, Complex.norm_real, Real.norm_eq_abs]
    calc
      |c * D - 1| ≤ 6 * (n : ℝ)⁻¹ := by
        simpa only [c, D] using hsing
      _ ≤ 6 * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (rpow_neg_one_le_neg_half (by omega : 1 ≤ n)) (by norm_num)
  have hdecomp :
      (FT.normalizedFieldTreeFMS M hM g).coeff n / (q : ℂ) - 1 =
        ((FT.normalizedFieldTreeFMS M hM g).coeff n - A₃ g * (c : ℂ)) /
            (q : ℂ) +
          (A₃ g - A₃ 0) * ((c : ℂ) / (q : ℂ)) +
          ((A₃ 0 * (c : ℂ)) / (q : ℂ) - 1) := by
    have hqne : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    field_simp [hqne]
    ring
  rw [hdecomp]
  have hg0 : 0 ≤ ‖g‖ := norm_nonneg g
  have hpow0 : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  calc
    ‖((FT.normalizedFieldTreeFMS M hM g).coeff n - A₃ g * (c : ℂ)) /
          (q : ℂ) +
        (A₃ g - A₃ 0) * ((c : ℂ) / (q : ℂ)) +
        ((A₃ 0 * (c : ℂ)) / (q : ℂ) - 1)‖ ≤
        ‖((FT.normalizedFieldTreeFMS M hM g).coeff n - A₃ g * (c : ℂ)) /
          (q : ℂ)‖ +
        ‖(A₃ g - A₃ 0) * ((c : ℂ) / (q : ℂ))‖ +
        ‖((A₃ 0 * (c : ℂ)) / (q : ℂ) - 1)‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add_left (norm_add_le _ _) _)
    _ ≤ Krem * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
        Kamp * ‖g‖ +
        6 * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
      add_le_add (add_le_add hrem hampTerm) hleadTerm
    _ ≤ Krem * (‖g‖ + (n : ℝ) ^ (-(1 / 2 : ℝ))) +
        Kamp * (‖g‖ + (n : ℝ) ^ (-(1 / 2 : ℝ))) +
        6 * (‖g‖ + (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
      have hpow_le : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
          ‖g‖ + (n : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
      have hg_le : ‖g‖ ≤
          ‖g‖ + (n : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hpow_le hKrem.le)
          (mul_le_mul_of_nonneg_left hg_le hKamp.le))
        (mul_le_mul_of_nonneg_left hpow_le (by norm_num))
    _ = K * (‖g‖ + (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
      dsimp only [K]
      ring

/-- Perron--Wright asymptotics for the literal complex-field connected-tree
weight, uniformly in every fixed `n^(-1/2)` field window.  Both the constant
and the eventual threshold are independent of the field. -/
theorem exists_complexFieldConnectedWeight_perronWright_shrinking_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (U : ℝ) (hU : 0 ≤ U) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ g : C(S, ℂ),
        ‖g‖ ≤ U * (n : ℝ) ^ (-(1 / 2 : ℝ)) →
        ‖((FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
              M.bjrModel.complexFieldConnectedWeight g n 0) /
              (fieldTreePerronWrightMainTerm M hM n : ℂ) - 1‖ ≤
          K * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K₀, hK₀, hcoeff⟩ :=
    exists_normalizedFieldTree_coefficient_shrinking_relative_bound
      M hM U hU
  let K : ℝ := 1 + 2 * K₀
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcoeff, eventually_ge_atTop 3] with n hn hn3
  intro g hg
  have hnpos : 0 < n := by omega
  let q : ℝ := Zero.treeCoefficientMainTerm M hM n
  let S₀ : ℝ := Transfer.factorialStirlingMainTerm n
  let P : ℝ := fieldTreePerronWrightMainTerm M hM n
  let a : ℂ := (FT.normalizedFieldTreeFMS M hM g).coeff n / (q : ℂ) - 1
  let b : ℝ := (n.factorial : ℝ) / S₀ - 1
  have hq : 0 < q := treeCoefficientMainTerm_pos M hM hnpos
  have hS₀ : 0 < S₀ := by
    dsimp only [S₀, Transfer.factorialStirlingMainTerm]
    positivity
  have ha : ‖a‖ ≤ K₀ * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simpa only [a, q] using hn g hg
  have hb := Transfer.factorial_stirling_relative_error_bound n hnpos
  have hbhalf : |b| ≤ (1 / 6 : ℝ) *
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      |b| ≤ 1 / (6 * (n : ℝ)) := by
        simpa only [b, S₀] using hb
      _ = (1 / 6 : ℝ) * (n : ℝ)⁻¹ := by ring
      _ ≤ (1 / 6 : ℝ) *
          (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (rpow_neg_one_le_neg_half (by omega : 1 ≤ n)) (by norm_num)
  have hbone : |b| ≤ 1 / 6 := by
    calc
      |b| ≤ 1 / (6 * (n : ℝ)) := by
        simpa only [b, S₀] using hb
      _ ≤ 1 / 6 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        nlinarith
  have hexact := normalizedFieldTreeFMS_coeff_eq_connectedWeight
    M hM g hnpos
  have hPS : S₀ * q = P := by
    simpa only [S₀, q, P] using
      factorialStirlingMainTerm_mul_treeCoefficientMainTerm_eq_field
        M hM hnpos
  have hdecomp :
      ((FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
          M.bjrModel.complexFieldConnectedWeight g n 0) / (P : ℂ) - 1 =
        (b : ℂ) + a + (b : ℂ) * a := by
    have hfact : (n.factorial : ℂ) ≠ 0 := by
      exact_mod_cast n.factorial_ne_zero
    have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    have hSc : (S₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS₀.ne'
    have hweight :
        (FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
            M.bjrModel.complexFieldConnectedWeight g n 0 =
          (n.factorial : ℂ) *
            (FT.normalizedFieldTreeFMS M hM g).coeff n := by
      have h := (div_eq_iff hfact).mp hexact.symm
      simpa only [mul_comm] using h
    have hPSc : (S₀ : ℂ) * (q : ℂ) = (P : ℂ) := by
      exact_mod_cast hPS
    have hfactRatio :
        (n.factorial : ℂ) / (S₀ : ℂ) = (b : ℂ) + 1 := by
      dsimp only [b]
      push_cast
      ring
    have hcoeffRatio :
        (FT.normalizedFieldTreeFMS M hM g).coeff n / (q : ℂ) =
          a + 1 := by
      dsimp only [a]
      ring
    calc
      ((FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
            M.bjrModel.complexFieldConnectedWeight g n 0) / (P : ℂ) - 1 =
          ((n.factorial : ℂ) *
            (FT.normalizedFieldTreeFMS M hM g).coeff n) /
              ((S₀ : ℂ) * (q : ℂ)) - 1 := by
        rw [hweight, hPSc]
      _ = ((n.factorial : ℂ) / (S₀ : ℂ)) *
            ((FT.normalizedFieldTreeFMS M hM g).coeff n / (q : ℂ)) - 1 := by
        field_simp [hSc, hqc]
      _ = ((b : ℂ) + 1) * (a + 1) - 1 := by
        rw [hfactRatio, hcoeffRatio]
      _ = (b : ℂ) + a + (b : ℂ) * a := by ring
  rw [hdecomp]
  calc
    ‖(b : ℂ) + a + (b : ℂ) * a‖ ≤
        ‖(b : ℂ)‖ + ‖a‖ + ‖(b : ℂ)‖ * ‖a‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (norm_mul_le _ _))
    _ ≤ (1 / 6 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
        K₀ * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
        (1 / 6 : ℝ) *
          (K₀ * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (add_le_add hbhalf ha)
        (mul_le_mul hbone ha (norm_nonneg _) (by norm_num))
    _ ≤ K * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hpow : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg (Nat.cast_nonneg n) _
      dsimp only [K]
      nlinarith [mul_nonneg hK₀.le hpow]

/-- Local Perron--Wright estimate for the literal complex-field tree weight.
The relative error is linear in the field norm, up to the universal
coefficient and Stirling error of order `n^(-1/2)`. -/
theorem exists_complexFieldConnectedWeight_perronWright_local_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∀ g : C(S, ℂ),
        ‖g‖ ≤ ε →
        ‖((FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
              M.bjrModel.complexFieldConnectedWeight g n 0) /
              (fieldTreePerronWrightMainTerm M hM n : ℂ) - 1‖ ≤
          K * (‖g‖ + (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨ε, K₀, hε, hK₀, hcoeff⟩ :=
    exists_normalizedFieldTree_coefficient_local_relative_bound M hM
  let K : ℝ := 1 + 2 * K₀
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨ε, K, hε, hK, ?_⟩
  filter_upwards [hcoeff, eventually_ge_atTop 3] with n hn hn3
  intro g hg
  have hnpos : 0 < n := by omega
  let q : ℝ := Zero.treeCoefficientMainTerm M hM n
  let S₀ : ℝ := Transfer.factorialStirlingMainTerm n
  let P : ℝ := fieldTreePerronWrightMainTerm M hM n
  let a : ℂ := (FT.normalizedFieldTreeFMS M hM g).coeff n / (q : ℂ) - 1
  let b : ℝ := (n.factorial : ℝ) / S₀ - 1
  have hq : 0 < q := treeCoefficientMainTerm_pos M hM hnpos
  have hS₀ : 0 < S₀ := by
    dsimp only [S₀, Transfer.factorialStirlingMainTerm]
    positivity
  have ha : ‖a‖ ≤
      K₀ * (‖g‖ + (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    simpa only [a, q] using hn g hg
  have hb := Transfer.factorial_stirling_relative_error_bound n hnpos
  have hbhalf : |b| ≤ (1 / 6 : ℝ) *
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      |b| ≤ 1 / (6 * (n : ℝ)) := by
        simpa only [b, S₀] using hb
      _ = (1 / 6 : ℝ) * (n : ℝ)⁻¹ := by ring
      _ ≤ (1 / 6 : ℝ) *
          (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (rpow_neg_one_le_neg_half (by omega : 1 ≤ n)) (by norm_num)
  have hbone : |b| ≤ 1 / 6 := by
    calc
      |b| ≤ 1 / (6 * (n : ℝ)) := by
        simpa only [b, S₀] using hb
      _ ≤ 1 / 6 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        have hnone : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        nlinarith
  have hexact := normalizedFieldTreeFMS_coeff_eq_connectedWeight
    M hM g hnpos
  have hPS : S₀ * q = P := by
    simpa only [S₀, q, P] using
      factorialStirlingMainTerm_mul_treeCoefficientMainTerm_eq_field
        M hM hnpos
  have hdecomp :
      ((FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
          M.bjrModel.complexFieldConnectedWeight g n 0) / (P : ℂ) - 1 =
        (b : ℂ) + a + (b : ℂ) * a := by
    have hfact : (n.factorial : ℂ) ≠ 0 := by
      exact_mod_cast n.factorial_ne_zero
    have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    have hSc : (S₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS₀.ne'
    have hweight :
        (FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
            M.bjrModel.complexFieldConnectedWeight g n 0 =
          (n.factorial : ℂ) *
            (FT.normalizedFieldTreeFMS M hM g).coeff n := by
      have h := (div_eq_iff hfact).mp hexact.symm
      simpa only [mul_comm] using h
    have hPSc : (S₀ : ℂ) * (q : ℂ) = (P : ℂ) := by
      exact_mod_cast hPS
    have hfactRatio :
        (n.factorial : ℂ) / (S₀ : ℂ) = (b : ℂ) + 1 := by
      dsimp only [b]
      push_cast
      ring
    have hcoeffRatio :
        (FT.normalizedFieldTreeFMS M hM g).coeff n / (q : ℂ) =
          a + 1 := by
      dsimp only [a]
      ring
    calc
      ((FiniteIrreducibleRadiusResponse.radius M hM g) ^ n *
            M.bjrModel.complexFieldConnectedWeight g n 0) / (P : ℂ) - 1 =
          ((n.factorial : ℂ) *
            (FT.normalizedFieldTreeFMS M hM g).coeff n) /
              ((S₀ : ℂ) * (q : ℂ)) - 1 := by
        rw [hweight, hPSc]
      _ = ((n.factorial : ℂ) / (S₀ : ℂ)) *
            ((FT.normalizedFieldTreeFMS M hM g).coeff n / (q : ℂ)) - 1 := by
        field_simp [hSc, hqc]
      _ = ((b : ℂ) + 1) * (a + 1) - 1 := by
        rw [hfactRatio, hcoeffRatio]
      _ = (b : ℂ) + a + (b : ℂ) * a := by ring
  rw [hdecomp]
  let x : ℝ := ‖g‖ + (n : ℝ) ^ (-(1 / 2 : ℝ))
  have hpow : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hx : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hpowx : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ x := by
    dsimp only [x]
    linarith [norm_nonneg g]
  calc
    ‖(b : ℂ) + a + (b : ℂ) * a‖ ≤
        ‖(b : ℂ)‖ + ‖a‖ + ‖(b : ℂ)‖ * ‖a‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (norm_mul_le _ _))
    _ ≤ (1 / 6 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
        K₀ * x +
        (1 / 6 : ℝ) * (K₀ * x) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (add_le_add hbhalf (by simpa only [x] using ha))
        (mul_le_mul hbone (by simpa only [x] using ha)
          (norm_nonneg _) (by norm_num))
    _ ≤ K * x := by
      dsimp only [K]
      nlinarith [mul_nonneg hK₀.le hx]

end PerronWright.FiniteIrreducibleFieldTreeConnectedWeightAsymptotic
