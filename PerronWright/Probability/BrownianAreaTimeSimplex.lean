import PerronWright.Probability.BrownianAreaTimeGaps
import Mathlib.Order.Fin.InsertNth

/-! # The actual duration--ordered-time simplex

Product Lebesgue duration and ordered internal times become a single
positive ordered time vector by appending the duration. The open and
half-open cube versions agree as measures, including empty time tuples.
-/

open MeasureTheory Filter Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianAreaTimeSimplex

open BrownianAreaTimeGaps BrownianPositiveBridgeAreaTimeMoments

theorem timeCube_eq_restrict_open_box (T : ℝ≥0) (d : ℕ) :
    timeCube T d = (volume : Measure (Fin d → ℝ)).restrict
      (univ.pi (fun _ : Fin d ↦ Ioo (0 : ℝ) (T : ℝ))) := by
  rw [volume_pi,Measure.restrict_congr_set (Measure.pi_Ioo_ae_eq_pi_Ioc
    (μ := fun _ : Fin d ↦ (volume : Measure ℝ))),
    Measure.restrict_pi_pi]
  rfl

def finalCons (d : ℕ) (p : ℝ × (Fin d → ℝ)) : Fin (d+1) → ℝ := Fin.snoc p.2 p.1

theorem volume_preserving_finalCons (d : ℕ) :
    MeasurePreserving (finalCons d)
      ((volume : Measure ℝ).prod (volume : Measure (Fin d → ℝ))) volume := by
  convert! (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) ↦ ℝ) (Fin.last d)).symm using 1
  ext p i
  simp only [finalCons,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
    Equiv.coe_fn_mk,Fin.insertNth_last']

theorem positiveOrdered_finalCons_iff (d : ℕ) (T : ℝ) (τ : Fin d → ℝ) :
    PositiveOrdered (finalCons d (T,τ)) ↔
      0 < T ∧ (∀ i, τ i ∈ Ioo (0 : ℝ) T) ∧ StrictMono τ := by
  constructor
  · rintro ⟨hp,hs⟩
    refine ⟨?_,?_,?_⟩
    · simpa only [finalCons,Fin.snoc_last] using hp (Fin.last d)
    · intro i
      constructor
      · simpa only [finalCons,Fin.snoc_castSucc] using hp i.castSucc
      · simpa only [finalCons,Fin.snoc_last,Fin.snoc_castSucc] using hs i.castSucc_lt_last
    · intro i j hij
      simpa only [finalCons,Fin.snoc_castSucc] using hs (Fin.castSucc_lt_castSucc_iff.mpr hij)
  · rintro ⟨hT,hτ,hs⟩
    constructor
    · intro i
      rcases i.eq_castSucc_or_eq_last with ⟨i,rfl⟩ | rfl
      · simpa only [finalCons,Fin.snoc_castSucc] using (hτ i).1
      · simpa only [finalCons,Fin.snoc_last] using hT
    · change StrictMono (Fin.snoc τ T)
      rw [← Fin.insertNth_last',Fin.strictMono_insertNth_iff]
      refine ⟨hs,fun i _ ↦ (hτ i).2,?_⟩
      intro i hi
      exact (not_le_of_gt i.castSucc_lt_last hi).elim

theorem lintegral_finalCons (d : ℕ) (F : (Fin (d+1) → ℝ) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ t : Fin (d+1) → ℝ, F t) =
      ∫⁻ T : ℝ, ∫⁻ τ : Fin d → ℝ, F (finalCons d (T,τ)) := by
  rw [← (volume_preserving_finalCons d).lintegral_comp hF]
  exact lintegral_prod _ (hF.comp (volume_preserving_finalCons d).measurable).aemeasurable

theorem lintegral_duration_timeCube_eq_ordered (d : ℕ)
    (F : (ℝ × (Fin d → ℝ)) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ T : ℝ in Ioi 0, ∫⁻ τ : Fin d → ℝ,
      {r : Fin d → ℝ | StrictMono r}.indicator (fun r ↦ F (T,r)) τ
        ∂timeCube (Real.toNNReal T) d) =
      ∫⁻ t : Fin (d+1) → ℝ in {t | PositiveOrdered t}, F (t (Fin.last d),Fin.init t) := by
  let H : (Fin (d+1) → ℝ) → ℝ≥0∞ := fun t ↦ F (t (Fin.last d),Fin.init t)
  have hmH : Measurable H := hF.comp ((measurable_pi_apply _).prodMk
    (measurable_pi_lambda _ (fun i ↦ measurable_pi_apply i.castSucc)))
  have hmP := hmH.indicator (measurableSet_positiveOrdered (d+1))
  calc
    _ = ∫⁻ T : ℝ, ∫⁻ τ : Fin d → ℝ,
        {t : Fin (d+1) → ℝ | PositiveOrdered t}.indicator H (finalCons d (T,τ)) := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro T
      by_cases hT : 0 < T
      · rw [indicator_of_mem (show T ∈ Ioi (0 : ℝ) from hT),
          timeCube_eq_restrict_open_box,← lintegral_indicator
            (MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ioo))]
        apply lintegral_congr
        intro τ
        have hp : PositiveOrdered (Fin.snoc τ T) ↔
            0 < T ∧ (∀ i, τ i ∈ Ioo (0 : ℝ) T) ∧ StrictMono τ :=
          positiveOrdered_finalCons_iff d T τ
        simp only [Set.indicator,Set.mem_pi,Set.mem_univ,true_implies,mem_ofPred_eq,
          Real.coe_toNNReal _ hT.le,H,finalCons,Fin.snoc_last,Fin.init_snoc,hp,hT,true_and]
        by_cases hb : ∀ i, τ i ∈ Ioo (0 : ℝ) T <;>
          by_cases hs : StrictMono τ <;> simp_all
      · rw [indicator_of_notMem (show T ∉ Ioi (0 : ℝ) from hT)]
        symm
        apply lintegral_eq_zero_of_ae_eq_zero
        exact Eventually.of_forall (fun τ ↦ by
          apply indicator_of_notMem
          intro hp
          exact hT ((positiveOrdered_finalCons_iff d T τ).mp hp).1)
    _ = ∫⁻ t : Fin (d+1) → ℝ, {t | PositiveOrdered t}.indicator H t :=
      (lintegral_finalCons d _ hmP).symm
    _ = _ := lintegral_indicator (measurableSet_positiveOrdered (d+1)) H

theorem lintegral_duration_timeCube_eq_positive_gaps (d : ℕ)
    (F : (ℝ × (Fin d → ℝ)) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ T : ℝ in Ioi 0, ∫⁻ τ : Fin d → ℝ,
      {r : Fin d → ℝ | StrictMono r}.indicator (fun r ↦ F (T,r)) τ
        ∂timeCube (Real.toNNReal T) d) =
      ∫⁻ g : Fin (d+1) → ℝ in {g | ∀ i, 0 < g i},
        F (∑ i, g i,Fin.init (cumulativeTimes (d+1) g)) := by
  rw [lintegral_duration_timeCube_eq_ordered d F hF]
  calc
    _ = ∫⁻ g : Fin (d+1) → ℝ in {g | ∀ i, 0 < g i},
        F (cumulativeTimes (d+1) g (Fin.last d),Fin.init (cumulativeTimes (d+1) g)) := by
      apply lintegral_positiveOrdered_eq_positive_gaps
      exact hF.comp ((measurable_pi_apply (Fin.last d)).prodMk
        (measurable_pi_lambda _ (fun i ↦ measurable_pi_apply i.castSucc)))
    _ = _ := lintegral_congr (fun g ↦ by rw [cumulativeTimes_last_eq_sum])

end PerronWright.BrownianAreaTimeSimplex
