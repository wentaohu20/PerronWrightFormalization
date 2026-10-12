import PerronWright.Probability.BrownianEntranceKilledChainConcatenation

/-! # Extracting the unit split from actual ordered observation times

A strictly increasing schedule containing zero and one splits into its
unit prefix and its positive post-unit gaps. The original active tuple is
exactly zero followed by the concatenated prefix and future coordinates.
This is deterministic bookkeeping, not an excursion law assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianCompletedExcursionObservationTimes

open BrownianEntranceKilledChainConcatenation

def prefixTimes (N k : ℕ) (times : Fin N → ℝ≥0) (hk : k+2 ≤ N) :
    Fin (k+2) → ℝ≥0 := fun i ↦ times ⟨i.val,by omega⟩

theorem prefixTimes_strictMono (N k : ℕ) (times : Fin N → ℝ≥0) (hk : k+2 ≤ N)
    (ht : StrictMono times) : StrictMono (prefixTimes N k times hk) := by
  intro i j hij
  exact ht (show (⟨i.val,by omega⟩ : Fin N) < ⟨j.val,by omega⟩ from hij)

theorem prefixTimes_zero (N k : ℕ) (times : Fin N → ℝ≥0) (hk : k+2 ≤ N)
    (hzero : times ⟨0,by omega⟩ = 0) : prefixTimes N k times hk 0 = 0 := hzero

theorem prefixTimes_last (N k : ℕ) (times : Fin N → ℝ≥0) (hk : k+2 ≤ N)
    (hone : times ⟨k+1,by omega⟩ = 1) :
    prefixTimes N k times hk (Fin.last (k+1)) = 1 := hone

def postTimes (N k n : ℕ) (times : Fin N → ℝ≥0) (hkn : k+n+3 ≤ N) :
    Fin (n+2) → ℝ≥0 := fun i ↦ times ⟨k+1+i.val,by omega⟩-1

theorem postTimes_absolute (N k n : ℕ) (times : Fin N → ℝ≥0) (hkn : k+n+3 ≤ N)
    (ht : Monotone times) (hone : times ⟨k+1,by omega⟩ = 1) (i : Fin (n+2)) :
    1+postTimes N k n times hkn i = times ⟨k+1+i.val,by omega⟩ := by
  have hi : 1 ≤ times ⟨k+1+i.val,by omega⟩ := by
    rw [← hone]
    exact ht (show (⟨k+1,by omega⟩ : Fin N) ≤ ⟨k+1+i.val,by omega⟩ by
      change k+1 ≤ k+1+i.val
      omega)
  exact add_tsub_cancel_of_le hi

theorem postTimes_strictMono (N k n : ℕ) (times : Fin N → ℝ≥0) (hkn : k+n+3 ≤ N)
    (ht : StrictMono times) (hone : times ⟨k+1,by omega⟩ = 1) :
    StrictMono (postTimes N k n times hkn) := by
  intro i j hij
  have htime : times ⟨k+1+i.val,by omega⟩ < times ⟨k+1+j.val,by omega⟩ :=
    ht (show (⟨k+1+i.val,by omega⟩ : Fin N) < ⟨k+1+j.val,by omega⟩ by
      change k+1+i.val < k+1+j.val
      have h := hij
      change i.val < j.val at h
      omega)
  have hi := postTimes_absolute N k n times hkn ht.monotone hone i
  have hj := postTimes_absolute N k n times hkn ht.monotone hone j
  rw [← hi,← hj] at htime
  exact (add_lt_add_iff_left 1).mp htime

theorem postTimes_zero (N k n : ℕ) (times : Fin N → ℝ≥0) (hkn : k+n+3 ≤ N)
    (hone : times ⟨k+1,by omega⟩ = 1) : postTimes N k n times hkn 0 = 0 := by
  change times ⟨k+1+0,by omega⟩-1 = 0
  simp only [add_zero,hone,tsub_self]

theorem postTimes_last (N k n : ℕ) (times : Fin N → ℝ≥0) (hkn : k+n+3 ≤ N) :
    postTimes N k n times hkn (Fin.last (n+1)) = times ⟨k+n+2,by omega⟩-1 := by
  unfold postTimes
  congr 2
  apply Fin.ext
  simp only [Fin.val_last]
  omega

theorem active_tuple_reconstruction (N k n : ℕ) (times : Fin N → ℝ≥0)
    (hkn : k+n+3 ≤ N) (ht : Monotone times)
    (hzero : times ⟨0,by omega⟩ = 0) (hone : times ⟨k+1,by omega⟩ = 1)
    (g : ℝ≥0 → ℝ) (hg : g 0 = 0) :
    (fun i : Fin (k+(n+1)+1+1) ↦ g (times ⟨i.val,by omega⟩)) =
      Fin.cons 0 (concatenatedHeights k (n+1)
        (fun i : Fin (k+1) ↦ g (prefixTimes N k times (by omega) i.succ))
        (fun i : Fin (n+1) ↦ g (1+postTimes N k n times hkn i.succ))) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [Fin.cons_zero]
    simpa only [Fin.val_zero,hzero] using hg
  · rw [Fin.cons_succ]
    by_cases hj : j.val < k+1
    · simp only [concatenatedHeights,dif_pos hj,prefixTimes,Fin.val_succ]
    · have hidx : j.val-(k+1) < n+1 := by have h := j.isLt; omega
      let v : Fin (n+1) := ⟨j.val-(k+1),hidx⟩
      have he : j = ⟨k+1+v.val,by omega⟩ := by
        apply Fin.ext
        dsimp [v]
        omega
      rw [he,concatenatedHeights_future,
        postTimes_absolute N k n times hkn ht hone v.succ]
      congr 2

end PerronWright.BrownianCompletedExcursionObservationTimes
