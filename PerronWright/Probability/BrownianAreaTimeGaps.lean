import PerronWright.Probability.BrownianKilledFreeEntranceGeometry
import PerronWright.Probability.BrownianAreaTimeCubeSorting
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Order.Fin.Tuple

/-! # The actual cumulative-time change of variables

Finite prefix sums preserve Lebesgue measure by successive measurable
translation shears. Positive gaps give precisely positive strictly
ordered nonzero times, with no determinant or change-of-variables premise.
-/

open MeasureTheory Filter Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianAreaTimeGaps

open BrownianKilledFreeEntranceGeometry

def cumulativeTimes : (d : ℕ) → (Fin d → ℝ) → (Fin d → ℝ)
  | 0, v => v
  | d+1, v => Fin.cons (v 0) (fun i ↦ v 0+cumulativeTimes d (Fin.tail v) i)

theorem volume_preserving_head_tail (d : ℕ) :
    MeasurePreserving (fun v : Fin (d+1) → ℝ ↦ (v 0,Fin.tail v))
      volume ((volume : Measure ℝ).prod (volume : Measure (Fin d → ℝ))) := by
  convert! (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) ↦ ℝ) 0) using 1

theorem volume_preserving_constant_shear (d : ℕ) :
    MeasurePreserving (fun p : ℝ × (Fin d → ℝ) ↦ (p.1,fun i ↦ p.1+p.2 i))
      ((volume : Measure ℝ).prod (volume : Measure (Fin d → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin d → ℝ))) := by
  apply (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun a (v : Fin d → ℝ) ↦ fun i ↦ a+v i)
  · exact measurable_pi_lambda _ (fun i ↦ measurable_fst.add
      ((measurable_pi_apply i).comp measurable_snd))
  · exact Eventually.of_forall (fun a ↦
      Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := (volume : Measure (Fin d → ℝ)))
        (fun _ : Fin d ↦ a))

theorem volume_preserving_cumulativeTimes (d : ℕ) :
    MeasurePreserving (cumulativeTimes d) volume volume := by
  induction d with
  | zero =>
    change MeasurePreserving (id : (Fin 0 → ℝ) → (Fin 0 → ℝ)) volume volume
    exact MeasurePreserving.id volume
  | succ d ih =>
    have h := (volume_preserving_freeCons d).comp
      ((volume_preserving_constant_shear d).comp
        (((MeasurePreserving.id (volume : Measure ℝ)).prod ih).comp
          (volume_preserving_head_tail d)))
    convert! h using 1

def PositiveOrdered {d : ℕ} (t : Fin d → ℝ) : Prop :=
  (∀ i, 0 < t i) ∧ StrictMono t

theorem positiveOrdered_cumulativeTimes_iff (d : ℕ) (v : Fin d → ℝ) :
    PositiveOrdered (cumulativeTimes d v) ↔ ∀ i, 0 < v i := by
  induction d with
  | zero => simp [PositiveOrdered,StrictMono]
  | succ d ih =>
    rw [cumulativeTimes,PositiveOrdered,Fin.strictMono_cons]
    constructor
    · rintro ⟨hp,hs,ht⟩
      have hc : PositiveOrdered (cumulativeTimes d (Fin.tail v)) := by
        constructor
        · intro i
          have h := hs i
          simpa only [lt_add_iff_pos_right] using h
        · intro i j hij
          have h := ht hij
          exact (add_lt_add_iff_left (v 0)).mp h
      have hv := (ih (Fin.tail v)).mp hc
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [Fin.cons_zero] using hp 0
      · exact hv j
    · intro hv
      have hc := (ih (Fin.tail v)).mpr (fun i ↦ hv i.succ)
      refine ⟨?_,?_,?_⟩
      · intro i
        refine Fin.cases (by simpa only [Fin.cons_zero] using hv 0) (fun j ↦ ?_) i
        simpa only [Fin.cons_succ] using add_pos (hv 0) (hc.1 j)
      · intro i
        exact lt_add_of_pos_right (v 0) (hc.1 i)
      · intro i j hij
        exact (add_lt_add_iff_left (v 0)).mpr (hc.2 hij)

theorem measurableSet_positiveOrdered (d : ℕ) :
    MeasurableSet {t : Fin d → ℝ | PositiveOrdered t} := by
  have he : {t : Fin d → ℝ | ∀ i, 0 < t i} =
      ⋂ i : Fin d, {t | (0 : ℝ) < t i} := by
    ext t
    simp only [mem_iInter,mem_ofPred_eq]
  have hp : MeasurableSet {t : Fin d → ℝ | ∀ i, 0 < t i} := by
    rw [he]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_lt measurable_const (measurable_pi_apply i))
  exact hp.inter (BrownianAreaTimeCubeSorting.measurableSet_strictMono d)

theorem lintegral_positiveOrdered_eq_positive_gaps (d : ℕ)
    (F : (Fin d → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t : Fin d → ℝ in {t | PositiveOrdered t}, F t) =
      ∫⁻ g : Fin d → ℝ in {g | ∀ i, 0 < g i}, F (cumulativeTimes d g) := by
  have he : cumulativeTimes d ⁻¹' {t | PositiveOrdered t} =
      {g | ∀ i, 0 < g i} := by
    ext g
    exact positiveOrdered_cumulativeTimes_iff d g
  rw [← (volume_preserving_cumulativeTimes d).setLIntegral_comp_preimage
    (measurableSet_positiveOrdered d) hF,he]

theorem cumulativeTimes_last_eq_sum (d : ℕ) (v : Fin (d+1) → ℝ) :
    cumulativeTimes (d+1) v (Fin.last d) = ∑ i, v i := by
  induction d with
  | zero => simp [cumulativeTimes]
  | succ d ih =>
    rw [cumulativeTimes,show Fin.last (d+1) = (Fin.last d).succ by rfl,
      Fin.cons_succ,ih]
    simpa only [Fin.tail] using (Fin.sum_univ_succ v).symm

theorem cumulativeTimes_adjacent_difference (d : ℕ) (v : Fin (d+1) → ℝ) (i : Fin d) :
    cumulativeTimes (d+1) v i.succ-cumulativeTimes (d+1) v i.castSucc = v i.succ := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [cumulativeTimes,Fin.cons_zero,Fin.cons_succ,Fin.castSucc_zero,
        Fin.tail]
      ring
    · have h := ih (Fin.tail v) j
      simp only [cumulativeTimes,Fin.cons_succ,Fin.castSucc_succ] at h ⊢
      dsimp only [Fin.tail] at h ⊢
      linarith

end PerronWright.BrownianAreaTimeGaps
