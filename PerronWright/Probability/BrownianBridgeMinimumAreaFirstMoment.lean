import PerronWright.Probability.BrownianBridgeMinimumAreaIntegrability
import PerronWright.Enumeration.PerronWrightFormulaMainTerm

/-! # First literal minimum-shift area moment and the actual Wright constant

The exact bridge minimum tail, layercake and the Gaussian half-line
integral compute the genuine first moment. This proves its equality with
the project's unchanged surplus-one Wright constant. It does not claim
the remaining area moments or a conditioned positive-excursion identity.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
noncomputable section

namespace PerronWright.BrownianBridgeMinimumAreaFirstMoment

open BrownianPathLaw BrownianPinnedBridgeArea BrownianBridgeMinimumTail
open BrownianBridgeMinimumArea BrownianBridgeMinimumAreaIntegrability

theorem integrable_negativeMinimum (T : ℝ≥0) (hT : 0 < T) :
    Integrable (negativeMinimum T) pathLaw := by
  simpa only [pow_one] using integrable_pow_negativeMinimum T hT 1

theorem integral_negativeMinimum (T : ℝ≥0) (hT : 0 < T) :
    (∫ f : Path, negativeMinimum T f ∂pathLaw) =
      Real.sqrt (Real.pi/(2/(T : ℝ)))/2 := by
  rw [(integrable_negativeMinimum T hT).integral_eq_integral_meas_le
    (Eventually.of_forall (negativeMinimum_nonneg T))]
  calc
    (∫ t in Ioi (0 : ℝ), pathLaw.real {f : Path | t ≤ negativeMinimum T f}) =
        ∫ t in Ioi (0 : ℝ), Real.exp (-(2/(T : ℝ))*t^2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change (pathLaw {f : Path | t ≤ negativeMinimum T f}).toReal = _
      rw [negativeMinimum_tail t ht T hT,ENNReal.toReal_ofReal (Real.exp_pos _).le]
      congr 1
      ring
    _ = _ := integral_gaussian_Ioi (2/(T : ℝ))

theorem integral_minimumShiftArea (T : ℝ≥0) (hT : 0 < T) :
    (∫ f : Path, minimumShiftArea T hT f ∂pathLaw) =
      (T : ℝ)*(Real.sqrt (Real.pi/(2/(T : ℝ)))/2) := by
  have he : minimumShiftArea T hT =ᵐ[pathLaw]
      fun f : Path ↦ area T f+(T : ℝ)*negativeMinimum T f := by
    filter_upwards [ae_minimumShiftArea_eq_area_sub_minimum T hT] with f hf
    rw [hf,negativeMinimum]
    ring
  rw [integral_congr_ae he,integral_add (area_hasGaussianLaw T hT).integrable
    ((integrable_negativeMinimum T hT).const_mul (T : ℝ)),
    integral_area T hT,zero_add,integral_const_mul,integral_negativeMinimum T hT]

/-- Genuine first area moment equals the unchanged enumerative constant;
the all-order Wright area identity remains a separate obligation. -/
theorem integral_unit_minimumShiftArea_eq_wrightConstant_one :
    (∫ f : Path, minimumShiftArea 1 zero_lt_one f ∂pathLaw) =
      PerronWrightFormulaMainTerm.wrightConstant 1 := by
  rw [integral_minimumShiftArea 1 zero_lt_one]
  change 1*(Real.sqrt (Real.pi/(2/1))/2) = Real.sqrt (2*Real.pi)/4
  norm_num only [div_one,one_mul]
  have hs : Real.sqrt (2*Real.pi) = 2*Real.sqrt (Real.pi/2) := by
    calc
      Real.sqrt (2*Real.pi) = Real.sqrt (4*(Real.pi/2)) := by congr 1; ring
      _ = Real.sqrt 4*Real.sqrt (Real.pi/2) := Real.sqrt_mul (by norm_num) _
      _ = _ := by norm_num
  rw [hs]
  ring

end PerronWright.BrownianBridgeMinimumAreaFirstMoment
