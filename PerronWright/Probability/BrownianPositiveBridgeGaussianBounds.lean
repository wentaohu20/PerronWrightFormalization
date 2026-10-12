import PerronWright.Probability.BrownianPositiveBridgeFiniteDimensionalEntrance
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Genuine Gaussian envelopes for positive bridge entrance kernels

The bounds retain Gaussian decay on the whole real line. They hold for
every small positive endpoint and every time in a fixed interior range.
They are consequences of the actual killed Gaussian difference, not
assumptions about conditioned bridges or excursion tightness.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeGaussianBounds

open BrownianPositiveKilledEndpoint BrownianKilledBoundaryEntrance
open BrownianPositiveBridgeFiniteDimensionalEntrance

def envelopeCoefficient (δ : ℝ≥0) : ℝ :=
  (2/(δ : ℝ))*(Real.sqrt (2*Real.pi*(δ : ℝ)))⁻¹*Real.exp (1/(2*(δ : ℝ)))

def envelopeReal (δ T : ℝ≥0) (y : ℝ) : ℝ :=
  envelopeCoefficient δ*max y 0*Real.exp (-y^2/(4*(T : ℝ)))

def envelope (δ T : ℝ≥0) (y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (envelopeReal δ T y)

def envelopeSup (δ T : ℝ≥0) : ℝ := envelopeCoefficient δ*(1+4*(T : ℝ))

theorem envelopeCoefficient_nonneg (δ : ℝ≥0) : 0 ≤ envelopeCoefficient δ := by
  unfold envelopeCoefficient
  positivity

theorem envelopeReal_nonneg (δ T : ℝ≥0) (y : ℝ) : 0 ≤ envelopeReal δ T y :=
  mul_nonneg (mul_nonneg (envelopeCoefficient_nonneg δ) (le_max_right y 0)) (Real.exp_pos _).le

theorem measurable_envelopeReal (δ T : ℝ≥0) : Measurable (envelopeReal δ T) := by
  unfold envelopeReal
  fun_prop

theorem measurable_envelope (δ T : ℝ≥0) : Measurable (envelope δ T) :=
  (measurable_envelopeReal δ T).ennreal_ofReal

theorem densityReal_div_start_le_gaussian (a : ℝ) (ha : 0 < a) (t : ℝ≥0)
    (ht : 0 < t) (y : ℝ) (hy : 0 < y) :
    densityReal a t y/a ≤ (2*y/(t : ℝ))*gaussianPDFReal a t y := by
  apply (div_le_iff₀ ha).mpr
  rw [densityReal_eq_factor a t ht y hy]
  have hb : 1-Real.exp (-2*a*y/(t : ℝ)) ≤ 2*a*y/(t : ℝ) := by
    have he := Real.add_one_le_exp (-2*a*y/(t : ℝ))
    rw [show -2*a*y/(t : ℝ) = -(2*a*y/(t : ℝ)) by ring] at he ⊢
    linarith
  calc
    _ ≤ gaussianPDFReal a t y*(2*a*y/(t : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (gaussianPDFReal_nonneg a t y)
    _ = _ := by ring

theorem gaussianPDFReal_uniform_envelope (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (δ t T : ℝ≥0) (hδ : 0 < δ) (hδt : δ ≤ t) (htT : t ≤ T) (y : ℝ) :
    gaussianPDFReal a t y ≤ (Real.sqrt (2*Real.pi*(δ : ℝ)))⁻¹*
      Real.exp (1/(2*(δ : ℝ)))*Real.exp (-y^2/(4*(T : ℝ))) := by
  have ht : 0 < t := hδ.trans_le hδt
  have hT : 0 < T := ht.trans_le htT
  have hδR : (0 : ℝ) < δ := hδ
  have htR : (0 : ℝ) < t := ht
  have hTR : (0 : ℝ) < T := hT
  have hδtR : (δ : ℝ) ≤ t := hδt
  have htTR : (t : ℝ) ≤ T := htT
  have ha2 : a^2 ≤ 1 := by nlinarith
  have he1 : -(y-a)^2/(2*(t : ℝ)) ≤ a^2/(2*(t : ℝ))-y^2/(4*(t : ℝ)) := by
    rw [show a^2/(2*(t : ℝ))-y^2/(4*(t : ℝ)) = (2*a^2-y^2)/(4*(t : ℝ)) by ring,
      show -(y-a)^2/(2*(t : ℝ)) = (-2*(y-a)^2)/(4*(t : ℝ)) by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [sq_nonneg (y-2*a)]
  have haBound : a^2/(2*(t : ℝ)) ≤ 1/(2*(δ : ℝ)) := by
    exact (div_le_div_of_nonneg_right ha2 (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith))
  have hyBound : y^2/(4*(T : ℝ)) ≤ y^2/(4*(t : ℝ)) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  have he : -(y-a)^2/(2*(t : ℝ)) ≤ 1/(2*(δ : ℝ))-y^2/(4*(T : ℝ)) := by linarith
  have hp : (Real.sqrt (2*Real.pi*(t : ℝ)))⁻¹ ≤ (Real.sqrt (2*Real.pi*(δ : ℝ)))⁻¹ := by
    apply (inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by positivity))).mpr
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hδtR (by positivity))
  unfold gaussianPDFReal
  calc
    _ ≤ (Real.sqrt (2*Real.pi*(δ : ℝ)))⁻¹*
        Real.exp (1/(2*(δ : ℝ))-y^2/(4*(T : ℝ))) :=
      mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [show 1/(2*(δ : ℝ))-y^2/(4*(T : ℝ)) =
        1/(2*(δ : ℝ))+(-y^2/(4*(T : ℝ))) by ring,Real.exp_add]
      simp only [mul_assoc]

theorem densityReal_div_start_le_envelope (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (δ t T : ℝ≥0) (hδ : 0 < δ) (hδt : δ ≤ t) (htT : t ≤ T) (y : ℝ) :
    densityReal a t y/a ≤ envelopeReal δ T y := by
  by_cases hy : 0 < y
  · have ht := hδ.trans_le hδt
    have hcoef : 2*y/(t : ℝ) ≤ 2*y/(δ : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (show (0 : ℝ) < δ from hδ) hδt
    have hb := mul_le_mul hcoef (gaussianPDFReal_uniform_envelope a ha ha1 δ t T hδ hδt htT y)
      (gaussianPDFReal_nonneg a t y) (by positivity)
    calc
      _ ≤ _ := (densityReal_div_start_le_gaussian a ha t ht y hy).trans hb
      _ = _ := by unfold envelopeReal envelopeCoefficient; rw [max_eq_left hy.le]; ring
  · simp only [densityReal,Set.indicator,mem_Ioi,if_neg hy,zero_div]
    exact envelopeReal_nonneg δ T y

theorem normalized_density_le_envelope (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (δ t T : ℝ≥0) (hδ : 0 < δ) (hδt : δ ≤ t) (htT : t ≤ T) (y : ℝ) :
    density a t y/ENNReal.ofReal a ≤ envelope δ T y := by
  rw [density,← ENNReal.ofReal_div_of_pos ha]
  exact ENNReal.ofReal_le_ofReal (densityReal_div_start_le_envelope a ha ha1 δ t T hδ hδt htT y)

theorem envelopeReal_le_sup (δ T : ℝ≥0) (hT : 0 < T) (y : ℝ) :
    envelopeReal δ T y ≤ envelopeSup δ T := by
  have hTR : (0 : ℝ) < T := hT
  have he : Real.exp (-y^2/(4*(T : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  have hq : y^2*Real.exp (-y^2/(4*(T : ℝ))) ≤ 4*(T : ℝ) := by
    have hm := (Real.mul_exp_neg_le_exp_neg_one (y^2/(4*(T : ℝ)))).trans
      (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
    have heq : -(y^2/(4*(T : ℝ))) = -y^2/(4*(T : ℝ)) := by ring
    rw [heq] at hm
    have hp := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4*(T : ℝ) by positivity)
    field_simp [ne_of_gt hTR] at hp
    simpa only [neg_div] using hp
  have hy : max y 0 ≤ 1+y^2 := by
    apply max_le
    · nlinarith [sq_nonneg (y-1/2)]
    · positivity
  have hb : max y 0*Real.exp (-y^2/(4*(T : ℝ))) ≤ 1+4*(T : ℝ) := by
    calc
      _ ≤ (1+y^2)*Real.exp (-y^2/(4*(T : ℝ))) :=
        mul_le_mul_of_nonneg_right hy (Real.exp_pos _).le
      _ = Real.exp (-y^2/(4*(T : ℝ)))+y^2*Real.exp (-y^2/(4*(T : ℝ))) := by ring
      _ ≤ _ := add_le_add he hq
  unfold envelopeReal envelopeSup
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hb (envelopeCoefficient_nonneg δ)

theorem envelope_le_sup (δ T : ℝ≥0) (hT : 0 < T) (y : ℝ) :
    envelope δ T y ≤ ENNReal.ofReal (envelopeSup δ T) :=
  ENNReal.ofReal_le_ofReal (envelopeReal_le_sup δ T hT y)

end PerronWright.BrownianPositiveBridgeGaussianBounds
