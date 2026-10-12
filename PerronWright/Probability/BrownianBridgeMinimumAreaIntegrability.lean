import PerronWright.Probability.BrownianBridgeMinimumTail
import PerronWright.Probability.BrownianBridgeMinimumAreaDilation
import PerronWright.Probability.BrownianPinnedBridgeAreaTilt

/-! # Every exponential and power moment of the actual minimum-shift area

The signed Gaussian area and the literal bridge minimum are not assumed
independent. Young's elementary inequality combines their proved exponential
integrability. Thus all moments of the actual positive shifted path area
are genuine finite Bochner integrals. The actual Brownian path dilation
also gives their exact duration scaling. No Wright moment identity or
conditioned-excursion identification is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
noncomputable section

namespace PerronWright.BrownianBridgeMinimumAreaIntegrability

open BrownianPathLaw BrownianPinnedBridgeArea BrownianPinnedBridgeAreaTilt
open BrownianBridgeMinimumArea BrownianBridgeMinimumTail
open BrownianBridgeMinimumAreaDilation BrownianPathDilationLaw

theorem exp_add_le_exp_double (a b : ℝ) :
    Real.exp (a+b) ≤ Real.exp (2*a)+Real.exp (2*b) := by
  rw [Real.exp_add]
  have ha : Real.exp (2*a) = Real.exp a ^ 2 := by
    rw [show 2*a = a+a from by ring,Real.exp_add,pow_two]
  have hb : Real.exp (2*b) = Real.exp b ^ 2 := by
    rw [show 2*b = b+b from by ring,Real.exp_add,pow_two]
  rw [ha,hb]
  nlinarith [sq_nonneg (Real.exp a-Real.exp b),Real.exp_pos a,Real.exp_pos b]

theorem integrable_exp_mul_minimumShiftArea (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    Integrable (fun f : Path ↦ Real.exp (u*minimumShiftArea T hT f)) pathLaw := by
  have hsum := (integrable_exp_mul_area T hT (2*u)).add
    (integrable_exp_mul_negativeMinimum T hT (2*u*(T : ℝ)))
  apply hsum.mono' ((Real.continuous_exp.measurable.comp
    (measurable_const.mul (measurable_minimumShiftArea T hT))).aestronglyMeasurable)
  filter_upwards [ae_minimumShiftArea_eq_area_sub_minimum T hT] with f hf
  change ‖Real.exp (u*minimumShiftArea T hT f)‖ ≤
    Real.exp (2*u*area T f)+Real.exp (2*u*(T : ℝ)*negativeMinimum T f)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,hf]
  have he : u*(area T f-(T : ℝ)*BrownianBridgeMinimumShift.bridgeMinimumValue T f) =
      u*area T f+u*(T : ℝ)*negativeMinimum T f := by
    unfold negativeMinimum
    ring
  rw [he]
  simpa only [mul_assoc] using
    exp_add_le_exp_double (u*area T f) (u*(T : ℝ)*negativeMinimum T f)

theorem integrableExpSet_minimumShiftArea (T : ℝ≥0) (hT : 0 < T) :
    integrableExpSet (minimumShiftArea T hT) pathLaw = univ := by
  ext u
  simp only [mem_univ,iff_true,integrableExpSet,mem_ofPred_eq]
  exact integrable_exp_mul_minimumShiftArea T hT u

theorem integrable_pow_minimumShiftArea (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    Integrable (fun f : Path ↦ minimumShiftArea T hT f ^ n) pathLaw := by
  apply integrable_pow_of_mem_interior_integrableExpSet
  rw [integrableExpSet_minimumShiftArea T hT,interior_univ]
  exact mem_univ _

theorem memLp_minimumShiftArea (T : ℝ≥0) (hT : 0 < T) (p : ℝ≥0) :
    MemLp (minimumShiftArea T hT) p pathLaw := by
  apply memLp_of_mem_interior_integrableExpSet
  rw [integrableExpSet_minimumShiftArea T hT,interior_univ]
  exact mem_univ _

theorem integral_minimumShiftArea_pow_duration_scaling (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ f : Path, minimumShiftArea T hT f ^ n ∂pathLaw) =
      ((T : ℝ)^(3/2 : ℝ))^n *
        ∫ f : Path, minimumShiftArea 1 zero_lt_one f ^ n ∂pathLaw := by
  calc
    (∫ f : Path, minimumShiftArea T hT f ^ n ∂pathLaw) =
        ∫ f : Path, minimumShiftArea T hT f ^ n ∂(pathLaw.map (brownianDilation T)) := by
      rw [pathLaw_brownianDilation T hT]
    _ = ∫ f : Path, minimumShiftArea T hT (brownianDilation T f) ^ n ∂pathLaw := by
      exact integral_map (measurable_brownianDilation T).aemeasurable
        ((measurable_minimumShiftArea T hT).pow_const n).aestronglyMeasurable
    _ = ∫ f : Path, ((T : ℝ)^(3/2 : ℝ))^n *minimumShiftArea 1 zero_lt_one f ^ n ∂pathLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun f ↦ by
        dsimp only
        rw [minimumShiftArea_brownianDilation T hT f,mul_pow])
    _ = _ := integral_const_mul _ _

theorem integral_exp_minimumShiftArea_duration_scaling (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (∫ f : Path, Real.exp (u*minimumShiftArea T hT f) ∂pathLaw) =
      ∫ f : Path, Real.exp ((u*(T : ℝ)^(3/2 : ℝ))*minimumShiftArea 1 zero_lt_one f) ∂pathLaw := by
  calc
    (∫ f : Path, Real.exp (u*minimumShiftArea T hT f) ∂pathLaw) =
        ∫ f : Path, Real.exp (u*minimumShiftArea T hT f) ∂(pathLaw.map (brownianDilation T)) := by
      rw [pathLaw_brownianDilation T hT]
    _ = ∫ f : Path, Real.exp (u*minimumShiftArea T hT (brownianDilation T f)) ∂pathLaw := by
      exact integral_map (measurable_brownianDilation T).aemeasurable
        (Real.continuous_exp.measurable.comp
          (measurable_const.mul (measurable_minimumShiftArea T hT))).aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun f ↦ by
        dsimp only
        rw [minimumShiftArea_brownianDilation T hT f,mul_assoc])

end PerronWright.BrownianBridgeMinimumAreaIntegrability
