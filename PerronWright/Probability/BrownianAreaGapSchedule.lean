import PerronWright.Probability.BrownianAreaTimeSimplex
import PerronWright.Probability.BrownianKilledFiniteDimensionalOrderedTimes

/-! # The literal killed schedule after the positive-gap change of variables

Prepending zero to positive cumulative times recovers exactly the input
gaps in the actual killed finite-coordinate schedule, including its
constant extension after the terminal time.
-/

open MeasureTheory Filter Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianAreaGapSchedule

open BrownianAreaTimeGaps BrownianKilledFiniteDimensionalOrderedTimes

def prefixSchedule (d : ℕ) (g : Fin d → ℝ) : Fin (d+1) → ℝ≥0 :=
  Fin.cons 0 (fun i ↦ Real.toNNReal (cumulativeTimes d g i))

@[simp] theorem prefixSchedule_zero (d : ℕ) (g : Fin d → ℝ) :
    prefixSchedule d g 0 = 0 := by simp [prefixSchedule]

@[simp] theorem prefixSchedule_succ (d : ℕ) (g : Fin d → ℝ) (i : Fin d) :
    prefixSchedule d g i.succ = Real.toNNReal (cumulativeTimes d g i) := by
  simp [prefixSchedule]

theorem strictMono_prefixSchedule (d : ℕ) (g : Fin d → ℝ)
    (hg : ∀ i, 0 < g i) : StrictMono (prefixSchedule d g) := by
  have hp := (positiveOrdered_cumulativeTimes_iff d g).mpr hg
  apply Fin.strictMono_cons.mpr
  constructor
  · intro i
    exact Real.toNNReal_pos.mpr (hp.1 i)
  · intro i j hij
    exact (Real.toNNReal_lt_toNNReal_iff (hp.1 j)).mpr (hp.2 hij)

theorem prefixSchedule_adjacent_difference (d : ℕ) (g : Fin d → ℝ)
    (hg : ∀ i, 0 < g i) (i : Fin d) :
    prefixSchedule d g i.succ-prefixSchedule d g i.castSucc = Real.toNNReal (g i) := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ d =>
    have hp := (positiveOrdered_cumulativeTimes_iff (d+1) g).mpr hg
    have hm := (strictMono_prefixSchedule (d+1) g hg).monotone
    apply NNReal.coe_injective
    rw [NNReal.coe_sub (hm (Fin.castSucc_le_succ i)),Real.coe_toNNReal _ (hg i).le]
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [prefixSchedule,Fin.cons_zero,Fin.cons_succ,Fin.castSucc_zero,
        cumulativeTimes,Real.coe_toNNReal _ (hg 0).le,NNReal.coe_zero,sub_zero]
    · simp only [prefixSchedule,Fin.cons_succ,Fin.castSucc_succ]
      rw [Real.coe_toNNReal _ (hp.1 j.succ).le,
        Real.coe_toNNReal _ (hp.1 j.castSucc).le]
      exact cumulativeTimes_adjacent_difference d g j

theorem orderedGaps_prefixSchedule_at (d : ℕ) (g : Fin d → ℝ)
    (hg : ∀ i, 0 < g i) (i : Fin d) :
    orderedGaps d (prefixSchedule d g) i.val = Real.toNNReal (g i) := by
  have hs : finiteTimeExtension d (prefixSchedule d g) (i.val+1) =
      prefixSchedule d g i.succ := finiteTimeExtension_at d _ i.succ
  have hc : finiteTimeExtension d (prefixSchedule d g) i.val =
      prefixSchedule d g i.castSucc := finiteTimeExtension_at d _ i.castSucc
  rw [orderedGaps,hs,hc]
  exact prefixSchedule_adjacent_difference d g hg i

theorem orderedGaps_prefixSchedule_after (d : ℕ) (g : Fin d → ℝ)
    (j : ℕ) (hj : d ≤ j) : orderedGaps d (prefixSchedule d g) j = 0 := by
  simp only [orderedGaps,finiteTimeExtension,min_eq_right hj,
    min_eq_right (by omega : d ≤ j+1),tsub_self]

def plainPaddedTimes (d : ℕ) (T : ℝ≥0) (τ : Fin d → ℝ) : Fin (d+2) → ℝ≥0 :=
  Fin.cons 0 (Fin.snoc (fun i ↦ Real.toNNReal (τ i)) T)

theorem plainPaddedTimes_positive_gaps (d : ℕ) (g : Fin (d+1) → ℝ) :
    plainPaddedTimes d (Real.toNNReal (∑ i, g i)) (Fin.init (cumulativeTimes (d+1) g)) =
      prefixSchedule (d+1) g := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [plainPaddedTimes,prefixSchedule]
  · rcases j.eq_castSucc_or_eq_last with ⟨j,rfl⟩ | rfl
    · simp [plainPaddedTimes,prefixSchedule,Fin.init]
    · simp [plainPaddedTimes,prefixSchedule,cumulativeTimes_last_eq_sum]

end PerronWright.BrownianAreaGapSchedule
