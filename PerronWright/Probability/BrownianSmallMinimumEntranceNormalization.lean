import PerronWright.Probability.BrownianMinimumTupleEndpointGeometry
import PerronWright.Probability.BrownianPositiveBridgeMultiPointMass
import PerronWright.Probability.BrownianPositiveBridgeMultiPointOrderedLaw

/-! # Literal half-passage/bridge normalization of the entrance density

The minimum-time normalization and the one-half passage contraction combine
to exactly the already proved probability entrance product. The total
duration is the actual terminal observation time.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianSmallMinimumEntranceNormalization

open BrownianMinimumTupleEndpointGeometry BrownianKilledFreeEntranceGeometry
open BrownianPositiveBridgeMultiPointEntrance BrownianPositiveBridgeMultiPointMass
open BrownianPositiveBridgeMultiPointOrderedLaw BrownianKilledBoundaryEntrance
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalDensityCoordinates

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

theorem fixedGaps_sampleTime (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0) :
    sampleTime (fixedGaps n times) (n+2) = times (Fin.last (n+1)) := by
  have hs : StrictMono (Fin.cons (0 : ℝ≥0) times) :=
    Fin.strictMono_cons.mpr ⟨fun i ↦ hfirst.trans_le (hstrict.monotone (Fin.zero_le i)),hstrict⟩
  have he := sampleTime_orderedGaps (n+2) (Fin.cons 0 times) hs.monotone rfl (Fin.last (n+2))
  simpa only [fixedGaps,Fin.val_last,Fin.val_succ,Fin.cons_succ,
    show Fin.last (n+2) = (Fin.last (n+1)).succ from rfl] using he

theorem entranceProduct_eq_half_bridge_normalization (n : ℕ)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hfirst : 0 < times 0)
    (v : FreeVector (n+1)) :
    entranceProduct n (fixedGaps n times) v =
      ENNReal.ofReal (times (Fin.last (n+1)) : ℝ)*
        (gaussianPDF 0 (times (Fin.last (n+1))) 0)⁻¹*ENNReal.ofReal (1/2 : ℝ)*
          (entranceJoint n (fixedGaps n times) v*
            entrance (fixedGaps n times (n+1)) (v (Fin.last n))) := by
  let T := times (Fin.last (n+1))
  have hT : 0 < T := hfirst.trans_le (hstrict.monotone (Fin.zero_le _))
  have hp := gaussianPDFReal_pos 0 T 0 (ne_of_gt hT)
  have hd : 0 < (2/(T : ℝ))*gaussianPDFReal 0 T 0 := by positivity
  have he : (((2/(T : ℝ))*gaussianPDFReal 0 T 0)⁻¹) =
      (T : ℝ)*(gaussianPDFReal 0 T 0)⁻¹*(1/2 : ℝ) := by
    field_simp
  have hc : (ENNReal.ofReal ((2/(T : ℝ))*gaussianPDFReal 0 T 0))⁻¹ =
      ENNReal.ofReal (T : ℝ)*(gaussianPDF 0 T 0)⁻¹*ENNReal.ofReal (1/2 : ℝ) := by
    rw [← ENNReal.ofReal_inv_of_pos hd,he,
      ENNReal.ofReal_mul (show 0 ≤ (T : ℝ)*(gaussianPDFReal 0 T 0)⁻¹ by positivity),
      ENNReal.ofReal_mul (show 0 ≤ (T : ℝ) from hT.le),ENNReal.ofReal_inv_of_pos hp]
    rfl
  rw [entranceProduct_eq_factors n _ (by rw [fixedGaps_sampleTime n times hstrict hfirst]; exact hT),
    fixedGaps_sampleTime n times hstrict hfirst,div_eq_mul_inv,hc]
  change (_*_)*_ = _*(entranceJoint n (fixedGaps n times) v*_)
  rw [entranceJoint]
  ac_rfl

theorem normalized_joint_test_lintegral (n : ℕ) (times : Fin (n+2) → ℝ≥0)
    (hstrict : StrictMono times) (hfirst : 0 < times 0)
    (Ψ : FreeVector (n+1) → ℝ≥0∞) :
    ENNReal.ofReal (times (Fin.last (n+1)) : ℝ)*
      (gaussianPDF 0 (times (Fin.last (n+1))) 0)⁻¹*
        (ENNReal.ofReal (1/2 : ℝ)*∫⁻ v : FreeVector (n+1),
          entranceJoint n (fixedGaps n times) v*
            entrance (fixedGaps n times (n+1)) (v (Fin.last n))*Ψ v) =
        ∫⁻ v, entranceProduct n (fixedGaps n times) v*Ψ v := by
  have hT : 0 < times (Fin.last (n+1)) := hfirst.trans_le (hstrict.monotone (Fin.zero_le _))
  have hp0 := ne_of_gt (gaussianPDF_pos 0 (ne_of_gt hT) 0)
  have hc : ENNReal.ofReal (times (Fin.last (n+1)) : ℝ)*
      (gaussianPDF 0 (times (Fin.last (n+1))) 0)⁻¹*ENNReal.ofReal (1/2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hp0))
      ENNReal.ofReal_ne_top
  rw [← mul_assoc,← lintegral_const_mul' _ _ hc]
  apply lintegral_congr
  intro v
  rw [entranceProduct_eq_half_bridge_normalization n times hstrict hfirst v]
  ac_rfl

end PerronWright.BrownianSmallMinimumEntranceNormalization
