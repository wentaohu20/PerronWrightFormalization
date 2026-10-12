import PerronWright.Probability.BrownianEntranceExitNormalization
import PerronWright.Probability.BrownianPositiveBridgeMultiPointEntrance

/-! # Genuine probability normalization of every finite entrance product

Finite product Lebesgue measure is split at the first free coordinate.
The remaining actual killed-chain product integrates against the entrance
kernel by the proved boundary convolution. The final scalar integral is
the directly computed entrance--exit normalization. No mass or entrance
convolution is postulated.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeMultiPointMass

open BrownianKilledBoundaryEntrance BrownianPositiveBridgeFiniteDimensionalEntrance
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianPositiveBridgeMultiPointEntrance BrownianEntranceConvolution BrownianEntranceExitNormalization

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

def freeCons (n : ℕ) (p : ℝ × FreeVector n) : FreeVector (n+1) := Fin.cons p.1 p.2

theorem continuous_freeCons (n : ℕ) : Continuous (freeCons n) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [freeCons,Fin.cons_zero] using continuous_fst
  · simpa only [freeCons,Fin.cons_succ,Function.comp_def] using
      (continuous_apply j).comp continuous_snd

theorem volume_preserving_freeCons (n : ℕ) :
    MeasurePreserving (freeCons n)
      ((volume : Measure ℝ).prod (volume : Measure (FreeVector n))) volume := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ ℝ) (0 : Fin (n+1))).symm
  change MeasurePreserving (fun p : ℝ × FreeVector n ↦ (Fin.cons p.1 p.2 : FreeVector (n+1)))
    ((volume : Measure ℝ).prod (volume : Measure (FreeVector n))) volume
  simpa only [volume_pi,Measure.volume_eq_prod,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero',
    Equiv.coe_fn_mk,freeCons] using h

theorem lintegral_volume_freeCons (n : ℕ) {F : FreeVector (n+1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v) = ∫⁻ x : ℝ, ∫⁻ v : FreeVector n, F (freeCons n (x,v)) := by
  rw [← (volume_preserving_freeCons n).lintegral_comp hF]
  exact lintegral_prod _ (hF.comp (continuous_freeCons n).measurable).aemeasurable

def tailGaps (gaps : ℕ → ℝ≥0) (j : ℕ) : ℝ≥0 := gaps (j+1)

theorem sampleTime_tailGaps (n : ℕ) (gaps : ℕ → ℝ≥0) :
    sampleTime gaps (n+1) = gaps 0+sampleTime (tailGaps gaps) n := by
  unfold sampleTime tailGaps
  rw [Finset.sum_range_succ']
  exact add_comm _ _

theorem internalDensity_freeCons (n : ℕ) (gaps : ℕ → ℝ≥0) (x : ℝ) (v : FreeVector n) :
    internalDensity n gaps (freeCons n (x,v)) = jointDensity n x (tailGaps gaps) v := by
  simp only [internalDensity,freeCons,jointDensity,prependInitial,tailGaps,Fin.cons_succ]

theorem entranceProduct_freeCons (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hT : 0 < sampleTime gaps (n+2)) (x : ℝ) (v : FreeVector n) :
    entranceProduct n gaps (freeCons n (x,v)) =
      (entrance (gaps 0) x/
        ENNReal.ofReal ((2/(sampleTime gaps (n+2) : ℝ))*gaussianPDFReal 0 (sampleTime gaps (n+2)) 0))*
          (jointDensity n x (tailGaps gaps) v*entrance (gaps (n+1)) (lastState n x v)) := by
  rw [entranceProduct_eq_factors n gaps hT,internalDensity_freeCons]
  change entrance (gaps 0) x*jointDensity n x (tailGaps gaps) v*
    entrance (gaps (n+1)) (lastState n x v)/_ = _
  simp only [div_eq_mul_inv]
  ac_rfl

theorem entranceProduct_integral_eq_one (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) : (∫⁻ v, entranceProduct n gaps v) = 1 := by
  let t := sampleTime (tailGaps gaps) (n+1)
  let T := sampleTime gaps (n+2)
  let d := ENNReal.ofReal ((2/(T : ℝ))*gaussianPDFReal 0 T 0)
  have hs : 0 < gaps 0 := hgaps 0 (by omega)
  have ht : 0 < t := by
    rw [show t = sampleTime (tailGaps gaps) (n+1) by rfl,sampleTime_succ]
    exact (hgaps (n+1) (by omega)).trans_le (le_add_of_nonneg_left (zero_le : (0 : ℝ≥0) ≤ _))
  have hsum : T = gaps 0+t := sampleTime_tailGaps (n+1) gaps
  have hT : 0 < T := by rw [hsum]; exact hs.trans_le (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ t))
  have hdR : 0 < (2/(T : ℝ))*gaussianPDFReal 0 T 0 := by
    have hp := gaussianPDFReal_pos 0 T 0 (ne_of_gt hT)
    positivity
  have hd0 : d ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hdR
  have htail : ∀ j < n+1, 0 < tailGaps gaps j := fun j hj ↦ hgaps (j+1) (by omega)
  have hinner (x : ℝ) :
      (∫⁻ v : FreeVector n, entranceProduct n gaps (freeCons n (x,v))) =
        (entrance (gaps 0) x*entrance t x)/d := by
    have hmE : Measurable (fun v : FreeVector n ↦ entrance (gaps (n+1)) (lastState n x v)) := by
      simpa only [Function.comp_def] using
        (measurable_entrance (gaps (n+1))).comp (continuous_lastState n x).measurable
    have hmJ : Measurable (fun v : FreeVector n ↦ jointDensity n x (tailGaps gaps) v*
        entrance (gaps (n+1)) (lastState n x v)) :=
      (measurable_jointDensity n x (tailGaps gaps)).mul hmE
    simp_rw [entranceProduct_freeCons n gaps hT]
    rw [lintegral_const_mul _ hmJ]
    by_cases hx : 0 < x
    · have hi := jointDensity_entrance_integral n x hx (tailGaps gaps) htail
      change (entrance (gaps 0) x/d)*(∫⁻ v : FreeVector n,
        jointDensity n x (tailGaps gaps) v*entrance (tailGaps gaps n) (lastState n x v)) = _
      rw [hi]
      dsimp only [t]
      simp only [div_eq_mul_inv]
      ac_rfl
    · have he : entrance (gaps 0) x = 0 := by
        simp only [entrance,entranceReal,Set.indicator,mem_Ioi,if_neg hx,ENNReal.ofReal_zero]
      rw [he,ENNReal.zero_div,zero_mul,zero_mul,ENNReal.zero_div]
  rw [lintegral_volume_freeCons n (measurable_entranceProduct n gaps)]
  simp_rw [hinner,div_eq_mul_inv]
  have hmP : Measurable (fun x : ℝ ↦ entrance (gaps 0) x*entrance t x) :=
    (measurable_entrance (gaps 0)).mul (measurable_entrance t)
  rw [lintegral_mul_const _ hmP,
    entrance_exit_convolution (gaps 0) t hs ht,← hsum]
  exact ENNReal.mul_inv_cancel hd0 ENNReal.ofReal_ne_top

def entranceLaw (n : ℕ) (gaps : ℕ → ℝ≥0) : Measure (FreeVector (n+1)) :=
  volume.withDensity (entranceProduct n gaps)

theorem entranceLaw_isProbability (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hgaps : ∀ j < n+2, 0 < gaps j) : IsProbabilityMeasure (entranceLaw n gaps) := by
  constructor
  rw [entranceLaw,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ]
  exact entranceProduct_integral_eq_one n gaps hgaps

end PerronWright.BrownianPositiveBridgeMultiPointMass
