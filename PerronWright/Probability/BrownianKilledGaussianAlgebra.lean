import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Literal Gaussian algebra for a lower absorbing barrier

These are exact identities for the actual Gaussian density. They do not
assert a killed Brownian transition law or a bridge reflection formula.
The continuous survival factor is available to upgrade such a proved
almost-everywhere formula without assigning arbitrary endpoint versions.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
noncomputable section

namespace PerronWright.BrownianKilledGaussianAlgebra

theorem gaussianPDFReal_reflected_eq (level : ℝ) (T : ℝ≥0)
    (hT : 0 < T) (x : ℝ) :
    gaussianPDFReal (2 * level) T x = gaussianPDFReal 0 T x *
      Real.exp (2 * level * (x - level) / (T : ℝ)) := by
  have hne : (T : ℝ) ≠ 0 := ne_of_gt (show 0 < (T : ℝ) from hT)
  have he : -(x - 2 * level) ^ 2 / (2 * (T : ℝ)) =
      -x ^ 2 / (2 * (T : ℝ)) + 2 * level * (x - level) / (T : ℝ) := by
    field_simp [hne]
    ring
  simp only [gaussianPDFReal,sub_zero]
  rw [he,Real.exp_add]
  ring

theorem gaussianPDFReal_reflected_ratio (level : ℝ) (T : ℝ≥0)
    (hT : 0 < T) (x : ℝ) :
    gaussianPDFReal (2 * level) T x / gaussianPDFReal 0 T x =
      Real.exp (2 * level * (x - level) / (T : ℝ)) := by
  rw [gaussianPDFReal_reflected_eq level T hT]
  exact mul_div_cancel_left₀ _ (ne_of_gt (gaussianPDFReal_pos 0 T x (ne_of_gt hT)))

theorem gaussianPDFReal_reflected_difference (level : ℝ) (T : ℝ≥0)
    (hT : 0 < T) (x : ℝ) :
    gaussianPDFReal 0 T x - gaussianPDFReal (2 * level) T x =
      gaussianPDFReal 0 T x *
        (1 - Real.exp (2 * level * (x - level) / (T : ℝ))) := by
  rw [gaussianPDFReal_reflected_eq level T hT]
  ring

def survivalFactorReal (level : ℝ) (T : ℝ≥0) (x : ℝ) : ℝ :=
  if level < x then 1 - Real.exp (2 * level * (x - level) / (T : ℝ)) else 0

theorem survivalFactorReal_eq_clipped (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (_hT : 0 < T) (x : ℝ) :
    survivalFactorReal level T x =
      1 - Real.exp (min 0 (2 * level * (x - level) / (T : ℝ))) := by
  unfold survivalFactorReal
  by_cases hx : level < x
  · rw [if_pos hx,min_eq_right]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hx.le)) T.coe_nonneg
  · have he : 0 ≤ 2 * level * (x - level) / (T : ℝ) :=
      div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith)
        (sub_nonpos.mpr (le_of_not_gt hx))) T.coe_nonneg
    rw [if_neg hx,min_eq_left he,Real.exp_zero,sub_self]

theorem continuous_survivalFactorReal (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) : Continuous (survivalFactorReal level T) := by
  have he : survivalFactorReal level T =
      fun x ↦ 1 - Real.exp (min 0 (2 * level * (x - level) / (T : ℝ))) :=
    funext (survivalFactorReal_eq_clipped level hlevel T hT)
  rw [he]
  fun_prop

theorem survivalFactorReal_bounds (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    0 ≤ survivalFactorReal level T x ∧ survivalFactorReal level T x ≤ 1 := by
  rw [survivalFactorReal_eq_clipped level hlevel T hT]
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (min_le_left _ _))
  · linarith [Real.exp_pos (min 0 (2 * level * (x - level) / (T : ℝ)))]

def survivalFactor (level : ℝ) (T : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (survivalFactorReal level T x)

theorem continuous_survivalFactor (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) : Continuous (survivalFactor level T) :=
  ENNReal.continuous_ofReal.comp (continuous_survivalFactorReal level hlevel T hT)

theorem survivalFactor_le_one (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) : survivalFactor level T x ≤ 1 := by
  unfold survivalFactor
  exact ENNReal.ofReal_le_one.mpr (survivalFactorReal_bounds level hlevel T hT x).2

theorem survivalFactor_of_le (level : ℝ) (T : ℝ≥0) {x : ℝ} (hx : x ≤ level) :
    survivalFactor level T x = 0 := by
  simp [survivalFactor,survivalFactorReal,not_lt.mpr hx]

theorem gaussianPDFReal_reflected_le (level : ℝ) (hlevel : level < 0)
    (T : ℝ≥0) (hT : 0 < T) {x : ℝ} (hx : level < x) :
    gaussianPDFReal (2 * level) T x ≤ gaussianPDFReal 0 T x := by
  have hfac : 0 ≤ 1 - Real.exp (2 * level * (x - level) / (T : ℝ)) := by
    simpa only [survivalFactorReal,if_pos hx] using
      (survivalFactorReal_bounds level hlevel T hT x).1
  have hd := gaussianPDFReal_reflected_difference level T hT x
  exact sub_nonneg.mp (hd ▸ mul_nonneg (gaussianPDFReal_nonneg 0 T x) hfac)

theorem gaussianPDF_reflected_difference (level : ℝ) (T : ℝ≥0)
    (hT : 0 < T) {x : ℝ} (hx : level < x) :
    gaussianPDF 0 T x - gaussianPDF (2 * level) T x =
      gaussianPDF 0 T x * survivalFactor level T x := by
  rw [gaussianPDF,gaussianPDF,← ENNReal.ofReal_sub _
    (gaussianPDFReal_nonneg (2 * level) T x),
    gaussianPDFReal_reflected_difference level T hT,
    ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 T x)]
  simp only [survivalFactor,survivalFactorReal,if_pos hx]

def reflectedWeight (level : ℝ) (T : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (2 * level * (x - level) / (T : ℝ)))

theorem measurable_reflectedWeight (level : ℝ) (T : ℝ≥0) :
    Measurable (reflectedWeight level T) := by
  unfold reflectedWeight
  fun_prop

theorem gaussianPDF_reflected_eq (level : ℝ) (T : ℝ≥0)
    (hT : 0 < T) (x : ℝ) :
    gaussianPDF (2 * level) T x = gaussianPDF 0 T x * reflectedWeight level T x := by
  rw [gaussianPDF,gaussianPDFReal_reflected_eq level T hT,
    ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 T x)]
  rfl

theorem gaussianReal_reflected_eq_withDensity (level : ℝ) (T : ℝ≥0)
    (hT : 0 < T) :
    gaussianReal (2 * level) T =
      (gaussianReal 0 T).withDensity (reflectedWeight level T) := by
  rw [gaussianReal_of_var_ne_zero _ (ne_of_gt hT),
    gaussianReal_of_var_ne_zero _ (ne_of_gt hT)]
  rw [← withDensity_mul volume (measurable_gaussianPDF 0 T)
    (measurable_reflectedWeight level T)]
  apply withDensity_congr_ae
  exact Eventually.of_forall (gaussianPDF_reflected_eq level T hT)

theorem gaussianReal_reflected_restrict_eq_withDensity (level : ℝ) (T : ℝ≥0)
    (hT : 0 < T) :
    (gaussianReal (2 * level) T).restrict (Ioi level) =
      (gaussianReal 0 T).withDensity ((Ioi level).indicator (reflectedWeight level T)) := by
  rw [gaussianReal_reflected_eq_withDensity level T hT,
    restrict_withDensity measurableSet_Ioi,
    ← withDensity_indicator measurableSet_Ioi]

end PerronWright.BrownianKilledGaussianAlgebra
