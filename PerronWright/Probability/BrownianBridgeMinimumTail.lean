import PerronWright.Probability.BrownianBridgeSurvivalLaw
import PerronWright.Probability.BrownianBridgeMinimumShift
import PerronWright.Probability.GaussianQuadraticTailIntegrability

/-! # Actual bridge minimum tail and every exponential moment

The true zero-endpoint bridge survival formula gives the literal
quadratic tail of minus the closed bridge minimum. Layercake then gives
all exponential moments and finite power moments, with no minimum-law
or integrability premise added to the Brownian model.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
noncomputable section

namespace PerronWright.BrownianBridgeMinimumTail

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeCyclicPath
open BrownianBridgeMinimumShift BrownianFirstPassageBridgeLaw
open BrownianBridgeAreaTiltPathLaw BrownianBridgeSurvivalLaw

def negativeMinimum (T : ℝ≥0) (f : Path) : ℝ := -bridgeMinimumValue T f

theorem measurable_negativeMinimum (T : ℝ≥0) : Measurable (negativeMinimum T) :=
  (measurable_bridgeMinimumValue T).neg

theorem negativeMinimum_nonneg (T : ℝ≥0) (f : Path) : 0 ≤ negativeMinimum T f := by
  have h := bridgeMinimumValue_le T f 0 zero_le
  rw [closedBridge_zero] at h
  exact neg_nonneg.mpr h

theorem minimum_above_probability (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | -a < bridgeMinimumValue T f} =
      ENNReal.ofReal (1-Real.exp (-2*a^2/(T : ℝ))) := by
  have he : {f : Path | -a < bridgeMinimumValue T f} =ᵐ[pathLaw]
      (stoppedBridgePath T) ⁻¹' bridgeConstraint (-a) T 0 := by
    filter_upwards [ae_closedBridge_eq_bridge T] with f hf
    apply propext
    change -a < bridgeMinimumValue T f ↔
      stoppedBridgePath T f ∈ bridgeConstraint (-a) T 0
    rw [mem_bridgeConstraint_iff]
    constructor
    · intro h t ht
      change -a < bridge T (min t T) f+(t : ℝ)/(T : ℝ)*0
      rw [min_eq_left ht,mul_zero,add_zero,← hf t]
      exact h.trans_le (bridgeMinimumValue_le T f t ht)
    · intro h
      have hm := h (bridgeMinimumTime T f) (bridgeMinimumTime_le T f)
      change -a < bridge T (min (bridgeMinimumTime T f) T) f+
        (bridgeMinimumTime T f : ℝ≥0)/(T : ℝ)*0 at hm
      rw [min_eq_left (bridgeMinimumTime_le T f),mul_zero,add_zero,
        ← hf (bridgeMinimumTime T f),bridgeMinimumTime_value] at hm
      exact hm
  rw [measure_congr he,← Measure.map_apply (measurable_stoppedBridgePath T)
    (measurableSet_bridgeConstraint (-a) T 0)]
  exact bridgeConstraint_probability_zero_endpoint a ha T hT

theorem negativeMinimum_tail (a : ℝ) (ha : 0 < a) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw {f : Path | a ≤ negativeMinimum T f} =
      ENNReal.ofReal (Real.exp (-2*a^2/(T : ℝ))) := by
  have he : {f : Path | a ≤ negativeMinimum T f} =
      {f : Path | -a < bridgeMinimumValue T f}ᶜ := by
    ext f
    simp only [mem_ofPred_eq,mem_compl_iff,not_lt,negativeMinimum]
    constructor <;> intro h <;> linarith
  have hp : Real.exp (-2*a^2/(T : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (by nlinarith [sq_nonneg a]) T.coe_nonneg)
  rw [he,prob_compl_eq_one_sub (measurableSet_lt measurable_const (measurable_bridgeMinimumValue T)),
    minimum_above_probability a ha T hT,
    ENNReal.ofReal_sub _ (Real.exp_pos _).le,ENNReal.ofReal_one]
  exact ENNReal.sub_sub_cancel (by simp) (ENNReal.ofReal_le_one.mpr hp)

theorem integrable_exp_mul_negativeMinimum (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    Integrable (fun f : Path ↦ Real.exp (u*negativeMinimum T f)) pathLaw := by
  apply GaussianQuadraticTailIntegrability.integrable_exp_mul_of_quadratic_tail pathLaw
    (negativeMinimum T) (measurable_negativeMinimum T) (negativeMinimum_nonneg T)
    (2/(T : ℝ)) (by positivity) _ u
  intro a ha
  rw [negativeMinimum_tail a ha T hT]
  congr 2
  ring

theorem integrableExpSet_negativeMinimum (T : ℝ≥0) (hT : 0 < T) :
    integrableExpSet (negativeMinimum T) pathLaw = univ := by
  ext u
  simp only [mem_univ,iff_true,integrableExpSet,mem_ofPred_eq]
  exact integrable_exp_mul_negativeMinimum T hT u

theorem integrable_pow_negativeMinimum (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    Integrable (fun f : Path ↦ negativeMinimum T f ^ n) pathLaw := by
  apply integrable_pow_of_mem_interior_integrableExpSet
  rw [integrableExpSet_negativeMinimum T hT,interior_univ]
  exact mem_univ _

end PerronWright.BrownianBridgeMinimumTail
