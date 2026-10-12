import PerronWright.Probability.BrownianAreaGapSchedule
import PerronWright.Probability.BrownianEntranceProductGeometry
import PerronWright.Probability.BrownianEntranceAreaGammaTransform

/-! # The actual entrance area integral on its ordered time simplex

The sorted finite-coordinate moment defining the genuine entrance area
moment is factorial times its ordered chamber integral. The cumulative
positive-gap schedule is exactly the original killed schedule.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianEntranceAreaOrderedIntegral

open BrownianAreaGapSchedule BrownianAreaTimeGaps BrownianAreaTimeCubeSorting
open BrownianPositiveBridgeAreaTimeMoments BrownianPositiveBridgeAreaOrderedTimes
open BrownianPositiveBridgeAreaMomentLimits BrownianKilledFiniteDimensionalOrderedTimes
open BrownianPositiveBridgeMultiPointEntrance BrownianPositiveBridgeMultiPointOrderedLaw
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianEntranceProductGeometry
open BrownianEntranceAreaGammaTransform

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

theorem measurable_plainPaddedTimes (d : ℕ) :
    Measurable (fun p : ℝ × (Fin d → ℝ) ↦ plainPaddedTimes d (Real.toNNReal p.1) p.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp only [plainPaddedTimes,Fin.cons_zero]
    exact measurable_const
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp only [plainPaddedTimes,Fin.cons_succ,Fin.snoc_last]
      exact measurable_fst.real_toNNReal
    · simp only [plainPaddedTimes,Fin.cons_succ,Fin.snoc_castSucc]
      exact ((measurable_pi_apply k).comp measurable_snd).real_toNNReal

def plainGaps (n : ℕ) (p : ℝ × (Fin (n+1) → ℝ)) : ℕ → ℝ≥0 :=
  orderedGaps (n+2) (plainPaddedTimes (n+1) (Real.toNNReal p.1) p.2)

theorem measurable_plainGaps (n : ℕ) : Measurable (plainGaps n) := by
  apply measurable_pi_lambda
  intro j
  unfold plainGaps orderedGaps finiteTimeExtension
  exact (((measurable_pi_apply _).comp (measurable_plainPaddedTimes (n+1))).sub
    ((measurable_pi_apply _).comp (measurable_plainPaddedTimes (n+1))))

def heightWeight (n : ℕ) (v : FreeVector (n+1)) : ℝ≥0∞ := ENNReal.ofReal (∏ i, v i)

theorem measurable_heightWeight (n : ℕ) : Measurable (heightWeight n) :=
  (continuous_finsetProd _ (fun i _ ↦ continuous_apply i)).measurable.ennreal_ofReal

def plainMoment (n : ℕ) (p : ℝ × (Fin (n+1) → ℝ)) : ℝ≥0∞ :=
  ∫⁻ v, entranceProduct n (plainGaps n p) v*heightWeight n v

theorem measurable_plainMoment (n : ℕ) : Measurable (plainMoment n) := by
  have hK : Measurable (fun q : (ℝ × (Fin (n+1) → ℝ)) × FreeVector (n+1) ↦
      entranceProduct n (plainGaps n q.1) q.2*heightWeight n q.2) :=
    ((measurable_joint_entranceProduct n).comp
      (((measurable_plainGaps n).comp measurable_fst).prodMk measurable_snd)).mul
        ((measurable_heightWeight n).comp measurable_snd)
  exact hK.lintegral_prod_right'

theorem plainMoment_sorted (n : ℕ) (T : ℝ≥0) (τ : Fin (n+1) → ℝ) :
    plainMoment n (T,τ ∘ Tuple.sort τ) = orderedEntranceTimeMoment n T τ := by
  rw [orderedEntranceTimeMoment_eq_kernel_integral]
  simp only [plainMoment,plainGaps,plainPaddedTimes,paddedTimes,
    Function.comp_apply,Real.toNNReal_coe,heightWeight]
  rfl

theorem entranceAreaMoment_eq_factorial_ordered (n : ℕ) (T : ℝ≥0) :
    entranceAreaMoment T (n+1) = ((n+1).factorial : ℝ≥0∞)*
      ∫⁻ τ : Fin (n+1) → ℝ,
        {r | StrictMono r}.indicator (fun r ↦ plainMoment n (T,r)) τ ∂timeCube T (n+1) := by
  calc
    _ = ∫⁻ τ : Fin (n+1) → ℝ, plainMoment n (T,τ ∘ Tuple.sort τ) ∂timeCube T (n+1) := by
      apply lintegral_congr_ae
      filter_upwards [ae_timeCube_goodTimes T (n+1)] with τ hτ
      simp only [entranceTimeMoment,if_pos hτ,plainMoment_sorted]
    _ = _ := lintegral_sorted_timeCube (n+1) T _
      ((measurable_plainMoment n).comp (measurable_const.prodMk measurable_id))

theorem plainGaps_positive_gaps (n : ℕ) (σ : Fin (n+2) → ℝ)
    (hσ : ∀ i, 0 < σ i) :
    plainGaps n (∑ i, σ i,Fin.init (cumulativeTimes (n+2) σ)) = finiteGaps n σ := by
  unfold plainGaps
  rw [plainPaddedTimes_positive_gaps]
  funext j
  by_cases hj : j < n+2
  · have h := orderedGaps_prefixSchedule_at (n+2) σ hσ (⟨j,hj⟩ : Fin (n+2))
    simpa only [finiteGaps,dif_pos hj] using h
  · rw [orderedGaps_prefixSchedule_after _ _ j (by omega),finiteGaps,dif_neg hj]

theorem sampleTime_finiteGaps_eq_duration (n : ℕ) (σ : Fin (n+2) → ℝ)
    (hσ : ∀ i, 0 < σ i) :
    BrownianKilledFiniteDimensionalCoordinates.sampleTime (finiteGaps n σ) (n+2) =
      Real.toNNReal (∑ i, σ i) := by
  have he := plainGaps_positive_gaps n σ hσ
  unfold plainGaps at he
  rw [plainPaddedTimes_positive_gaps] at he
  rw [← he]
  have h := sampleTime_orderedGaps (n+2) (prefixSchedule (n+2) σ)
    (strictMono_prefixSchedule (n+2) σ hσ).monotone
    (prefixSchedule_zero (n+2) σ) (Fin.last (n+2))
  simp only [Fin.val_last] at h
  simpa only [show Fin.last (n+2) = (Fin.last (n+1)).succ by rfl,
    prefixSchedule_succ,cumulativeTimes_last_eq_sum] using h

theorem normalization_plainMoment_positive_gaps (n : ℕ) (σ : Fin (n+2) → ℝ)
    (hσ : ∀ i, 0 < σ i) :
    ENNReal.ofReal (boundaryHeatCoefficient (Real.toNNReal (∑ i, σ i)))*
      plainMoment n (∑ i, σ i,Fin.init (cumulativeTimes (n+2) σ)) =
        ∫⁻ v, rawNumerator n σ v*heightWeight n v := by
  have hs : 0 < ∑ i, σ i := Finset.sum_pos (fun i _ ↦ hσ i) Finset.univ_nonempty
  have hT : 0 < BrownianKilledFiniteDimensionalCoordinates.sampleTime (finiteGaps n σ) (n+2) := by
    rw [sampleTime_finiteGaps_eq_duration n σ hσ]
    exact Real.toNNReal_pos.mpr hs
  unfold plainMoment
  rw [plainGaps_positive_gaps n σ hσ]
  rw [← lintegral_const_mul' _
    (fun v : FreeVector (n+1) ↦ entranceProduct n (finiteGaps n σ) v*heightWeight n v)
    ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro v
  have he := entranceProduct_mul_normalization n σ hT v
  rw [sampleTime_finiteGaps_eq_duration n σ hσ] at he
  change _*(_*_) = _
  calc
    _ = (entranceProduct n (finiteGaps n σ) v*
        ENNReal.ofReal (boundaryHeatCoefficient (Real.toNNReal (∑ i, σ i))))*heightWeight n v := by ac_rfl
    _ = _ := by rw [show entranceProduct n (finiteGaps n σ) v*
      ENNReal.ofReal (boundaryHeatCoefficient (Real.toNNReal (∑ i, σ i))) = rawNumerator n σ v from he]

end PerronWright.BrownianEntranceAreaOrderedIntegral
