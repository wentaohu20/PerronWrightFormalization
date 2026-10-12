import PerronWright.Probability.BrownianPositiveBridgeAreaTimeMoments
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Fin.Tuple
import Mathlib.Order.Fin.InsertNth

/-! # Almost every area time tuple has genuine distinct internal times

The repeated-time diagonals are null by splitting one coordinate from
the finite product measure and using the actual null singleton measure.
Sorting a good tuple therefore gives strictly ordered internal times.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeAreaOrderedTimes

open BrownianPositiveBridgeAreaTimeMoments
open BrownianKilledFiniteDimensionalOrderedTimes BrownianKilledFiniteDimensionalOrderedDensity

def GoodTimes {d : ℕ} (T : ℝ≥0) (τ : Fin d → ℝ) : Prop :=
  (∀ i, τ i ∈ Ioo (0 : ℝ) (T : ℝ)) ∧ Function.Injective τ

theorem ae_timeCube_coordinates_distinct (T : ℝ≥0) (d : ℕ) (i j : Fin d) (hij : i ≠ j) :
    ∀ᵐ τ ∂timeCube T d, τ i ≠ τ j := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ n =>
    obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hij.symm
    let μ : Fin (n+1) → Measure ℝ := fun _ ↦ volume.restrict (Ioc (0 : ℝ) (T : ℝ))
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ ℝ) i
    have hmp := measurePreserving_piFinSuccAbove μ i
    have hp : ∀ᵐ p : ℝ×(Fin n → ℝ) ∂(μ i).prod (Measure.pi (fun z ↦ μ (i.succAbove z))),
        p.1 ≠ p.2 k := by
      apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst
        ((continuous_apply k).comp continuous_snd)).measurableSet.compl).mpr
      apply ae_of_all
      intro r
      exact (Measure.ae_eval_ne (fun z ↦ μ (i.succAbove z)) k r).mono (fun _ h ↦ h.symm)
    have hmap : ∀ᵐ p ∂(Measure.pi μ).map e, p.1 ≠ p.2 k := by
      rw [hmp.map_eq]
      exact hp
    have hpre := ae_of_ae_map e.measurable.aemeasurable hmap
    change ∀ᵐ τ ∂Measure.pi μ, τ i ≠ τ (i.succAbove k) at hpre
    rw [hk] at hpre
    exact hpre

theorem ae_timeCube_injective (T : ℝ≥0) (d : ℕ) :
    ∀ᵐ τ ∂timeCube T d, Function.Injective τ := by
  have h : ∀ᵐ τ ∂timeCube T d, ∀ i j : Fin d, i ≠ j → τ i ≠ τ j := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact ae_of_all _ (fun _ h ↦ (h hij).elim)
    · exact (ae_timeCube_coordinates_distinct T d i j hij).mono (fun _ h _ ↦ h)
  filter_upwards [h] with τ hτ
  intro i j he
  by_contra hij
  exact hτ i j hij he

theorem ae_timeCube_goodTimes (T : ℝ≥0) (d : ℕ) :
    ∀ᵐ τ ∂timeCube T d, GoodTimes T τ := by
  have hn : ∀ᵐ τ ∂timeCube T d, ∀ i, τ i ≠ (T : ℝ) := by
    apply eventually_all.mpr
    intro i
    exact Measure.ae_eval_ne (fun _ : Fin d ↦ volume.restrict (Ioc (0 : ℝ) (T : ℝ))) i T
  filter_upwards [ae_timeCube_coordinates T d,ae_timeCube_injective T d,hn] with τ hτ hi hnτ
  exact ⟨fun i ↦ ⟨(hτ i).1,lt_of_le_of_ne (hτ i).2 (hnτ i)⟩,hi⟩

def sortedInternalTimes {d : ℕ} (τ : Fin d → ℝ) : Fin d → ℝ≥0 :=
  fun i ↦ Real.toNNReal (τ (Tuple.sort τ i))

def paddedTimes {d : ℕ} (T : ℝ≥0) (τ : Fin d → ℝ) : Fin (d+2) → ℝ≥0 :=
  Fin.cons 0 (Fin.snoc (sortedInternalTimes τ) T)

theorem strictMono_sortedInternalTimes {d : ℕ} (T : ℝ≥0) (τ : Fin d → ℝ)
    (hg : GoodTimes T τ) : StrictMono (sortedInternalTimes τ) := by
  have hr : StrictMono (τ ∘ Tuple.sort τ) :=
    (Tuple.monotone_sort τ).strictMono_iff_injective.mpr (hg.2.comp (Tuple.sort τ).injective)
  intro i j hij
  exact (Real.toNNReal_lt_toNNReal_iff (hg.1 (Tuple.sort τ j)).1).mpr (hr hij)

theorem strictMono_paddedTimes (n : ℕ) (T : ℝ≥0) (hT : 0 < T)
    (τ : Fin (n+1) → ℝ) (hg : GoodTimes T τ) : StrictMono (paddedTimes T τ) := by
  have hs := strictMono_sortedInternalTimes T τ hg
  have hlast : sortedInternalTimes τ (Fin.last n) < T :=
    (Real.toNNReal_lt_iff_lt_coe (hg.1 (Tuple.sort τ (Fin.last n))).1.le).mpr
      (hg.1 (Tuple.sort τ (Fin.last n))).2
  have hn : StrictMono (Fin.snoc (sortedInternalTimes τ) T) := by
    simpa only [Fin.insertNth_last'] using Fin.strictMono_insertNth_last hs T hlast
  apply Fin.strictMono_cons.mpr
  refine ⟨?_,hn⟩
  intro j
  rcases j.eq_castSucc_or_eq_last with ⟨j,rfl⟩ | rfl
  · simpa only [Fin.snoc_castSucc,sortedInternalTimes] using
      Real.toNNReal_pos.mpr (hg.1 (Tuple.sort τ j)).1
  · simpa only [Fin.snoc_last] using hT

theorem paddedTimes_zero {d : ℕ} (T : ℝ≥0) (τ : Fin d → ℝ) :
    paddedTimes T τ 0 = 0 := by simp [paddedTimes]

theorem paddedTimes_last {d : ℕ} (T : ℝ≥0) (τ : Fin d → ℝ) :
    paddedTimes T τ (Fin.last (d+1)) = T := by
  unfold paddedTimes
  rw [show Fin.last (d+1) = (Fin.last d).succ by rfl,Fin.cons_succ,Fin.snoc_last]

theorem paddedTimes_internal {d : ℕ} (T : ℝ≥0) (τ : Fin d → ℝ) (i : Fin d) :
    paddedTimes T τ i.succ.castSucc = sortedInternalTimes τ i := by
  simp [paddedTimes,Fin.castSucc_succ]

theorem heightProduct_sorted {d : ℕ} (τ : Fin d → ℝ) (g : BrownianPathLaw.Path) :
    (∏ i, g (sortedInternalTimes τ i)) = heightProduct τ g := by
  exact Equiv.prod_comp (Tuple.sort τ) (fun i ↦ g (Real.toNNReal (τ i)))

end PerronWright.BrownianPositiveBridgeAreaOrderedTimes
