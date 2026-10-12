import PerronWright.Probability.BrownianEntranceKilledChainConcatenation
import PerronWright.Probability.BrownianEntranceDurationScaling

/-! # The literal mixed prefix/future density is the completed entrance shape

Positive deterministic gaps, including the genuine final first-hit gap,
produce the same ordered schedule as the prefix and post-unit observations.
The actual entrance path law, not a conditional-shape premise, identifies
the integrated chain at every completed lifetime.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BigOperators
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianCompletedExcursionMixedSchedule

open BrownianPathLaw BrownianPathDilationLaw BrownianKilledFiniteDimensionalCoordinates
open BrownianKilledFiniteDimensionalDensityCoordinates BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledFiniteDimensionalOrderedDensity BrownianPositiveBridgeMultiPointOrderedLaw
open BrownianPositiveBridgeMultiPointEntrance BrownianKilledFreeEntranceGeometry
open BrownianEntranceKilledChainConcatenation BrownianEntranceFiniteDimensionalFamily
open BrownianEntranceOrderedTimeLaw BrownianEntranceDurationScaling

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

private theorem cumulative_strictMono (m : ℕ) (gaps : ℕ → ℝ≥0)
    (hp : ∀ j < m, 0 < gaps j) : StrictMono (fun i : Fin (m+1) ↦ sampleTime gaps i.val) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  change sampleTime gaps i.val < sampleTime gaps (i.val+1)
  rw [sampleTime_succ]
  exact lt_add_of_pos_right _ (hp i.val i.isLt)

private theorem cumulative_gaps_at (m : ℕ) (gaps : ℕ → ℝ≥0) (j : ℕ) (hj : j < m) :
    orderedGaps m (fun i : Fin (m+1) ↦ sampleTime gaps i.val) j = gaps j := by
  unfold orderedGaps finiteTimeExtension
  simp only [Nat.min_eq_left (show j+1 ≤ m by omega),Nat.min_eq_left (show j ≤ m by omega)]
  rw [sampleTime_succ,add_tsub_cancel_left]

private theorem cumulative_entranceProduct (n : ℕ) (gaps : ℕ → ℝ≥0)
    (hp : ∀ j < n+2, 0 < gaps j) (v : FreeVector (n+1)) :
    entranceProduct n (orderedGaps (n+2) (fun i : Fin (n+3) ↦ sampleTime gaps i.val)) v =
      entranceProduct n gaps v := by
  have hs := cumulative_strictMono (n+2) gaps hp
  have hT := sampleTime_orderedGaps (n+2) (fun i : Fin (n+3) ↦ sampleTime gaps i.val)
    hs.monotone (sampleTime_zero gaps) (Fin.last (n+2))
  simp only [Fin.val_last] at hT
  unfold entranceProduct
  rw [cumulative_gaps_at (n+2) gaps 0 (by omega),
    cumulative_gaps_at (n+2) gaps (n+1) (by omega),hT]
  congr 1
  unfold internalDensity
  apply Finset.prod_congr rfl
  intro i _
  rw [cumulative_gaps_at (n+2) gaps (i.val+1) (by omega)]

private theorem sampleTime_update_before (n : ℕ) (gaps : ℕ → ℝ≥0)
    (terminal : ℝ≥0) (j : ℕ) (hj : j ≤ n+1) :
    sampleTime (Function.update gaps (n+1) terminal) j = sampleTime gaps j := by
  unfold sampleTime
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (show i ≠ n+1 by have := Finset.mem_range.mp hi; omega)]

private theorem sampleTime_concat_prefix (k : ℕ) (pre post : ℕ → ℝ≥0)
    (j : ℕ) (hj : j ≤ k+1) :
    sampleTime (concatenatedGaps k pre post) j = sampleTime pre j := by
  unfold sampleTime
  apply Finset.sum_congr rfl
  intro i hi
  exact if_pos (by have := Finset.mem_range.mp hi; omega)

private def splitHeights (k n : ℕ) (w : FreeVector (k+(n+1)+1)) :
    FreeVector (k+1) × FreeVector (n+1) :=
  (fun i ↦ w ⟨i.val,by omega⟩,fun i ↦ w ⟨k+1+i.val,by omega⟩)

private theorem continuous_splitHeights (k n : ℕ) : Continuous (splitHeights k n) :=
  (continuous_pi (fun _ ↦ continuous_apply _)).prodMk
    (continuous_pi (fun _ ↦ continuous_apply _))

private theorem splitHeights_concat (k n : ℕ) (u : FreeVector (k+1)) (v : FreeVector (n+1)) :
    splitHeights k n (concatenatedHeights k (n+1) u v) = (u,v) := by
  apply Prod.ext
  · funext i
    exact concatenatedHeights_prefix k (n+1) u v i
  · funext i
    exact concatenatedHeights_future k (n+1) u v i

theorem mixed_terminal_chain_shape_lintegral (k n : ℕ)
    (prefixTimes : Fin (k+2) → ℝ≥0) (hprefix : StrictMono prefixTimes)
    (hprefixzero : prefixTimes 0 = 0) (hprefixlast : prefixTimes (Fin.last (k+1)) = 1)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (τ : ℝ≥0) (hτ : times (Fin.last (n+1)) < τ)
    (G : FreeVector (k+1) × FreeVector (n+1) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ u : FreeVector (k+1), ∫⁻ v : FreeVector (n+1),
      ((entranceJoint k (orderedGaps (k+1) prefixTimes) u*
        jointDensity (n+1) (u (Fin.last k)) (orderedGaps (n+1) times) v)*
        BrownianFirstPassageDensityGeometry.density (v (Fin.last n))
          (τ-times (Fin.last (n+1)))/ENNReal.ofReal (Real.sqrt (2/Real.pi)))*G (u,v)) =
      BrownianMinimumFutureReturnDensity.returnDensity (1+(τ : ℝ)) *
        (∫⁻ e : Path,
          G ((fun i : Fin (k+1) ↦ brownianDilation (1+τ) e (prefixTimes i.succ)),
            (fun i : Fin (n+1) ↦ brownianDilation (1+τ) e (1+times i.succ)))
              ∂BrownianEntranceContinuousRealization.pathLaw 1 zero_lt_one) := by
  let pre := orderedGaps (k+1) prefixTimes
  let post := Function.update (orderedGaps (n+1) times) (n+1) (τ-times (Fin.last (n+1)))
  let gaps := concatenatedGaps k pre post
  let M := k+(n+1)
  let ts : Fin (M+3) → ℝ≥0 := fun i ↦ sampleTime gaps i.val
  have hp : ∀ j < M+2, 0 < gaps j := by
    intro j hj
    dsimp [gaps,concatenatedGaps]
    split_ifs with hjk
    · exact orderedGaps_positive (k+1) prefixTimes hprefix j hjk
    · have hd : j-(k+1) ≤ n+1 := by dsimp [M] at hj; omega
      by_cases he : j-(k+1) = n+1
      · dsimp [post]
        rw [he,Function.update_self]
        exact tsub_pos_iff_lt.mpr hτ
      · dsimp [post]
        rw [Function.update_of_ne he]
        exact orderedGaps_positive (n+1) times hstrict _ (by omega)
  have ht : StrictMono ts := cumulative_strictMono (M+2) gaps hp
  have ht0 : ts 0 = 0 := sampleTime_zero gaps
  have hpre : sampleTime pre (k+1) = 1 := by
    simpa only [pre,Fin.val_last,hprefixlast] using
      sampleTime_orderedGaps (k+1) prefixTimes hprefix.monotone hprefixzero (Fin.last (k+1))
  have hpost : sampleTime (orderedGaps (n+1) times) (n+1) = times (Fin.last (n+1)) := by
    exact sampleTime_orderedGaps (n+1) times hstrict.monotone hzero (Fin.last (n+1))
  have htotal : sampleTime gaps (M+2) = 1+τ := by
    rw [show M+2 = k+1+(n+2) by dsimp [M]; omega]
    change sampleTime (concatenatedGaps k pre post) (k+1+(n+2)) = _
    rw [sampleTime_concatenatedGaps,hpre,sampleTime_terminal_extension,hpost,
      add_tsub_cancel_of_le hτ.le]
  have hT : 1 < sampleTime gaps (M+2) := by
    rw [htotal]
    exact lt_add_of_pos_right _ (lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ _) hτ)
  have hTp : 0 < (1+τ : ℝ≥0) := by positivity
  have htslast : ts (Fin.last (M+2)) = 1+τ := by exact htotal
  let F : FreeVector (M+1) → ℝ≥0∞ := fun w ↦ G (splitHeights k n w)
  have hF : Measurable F := hG.comp (continuous_splitHeights k n).measurable
  have hcoords (e : Path) : splitHeights k n (orderedEval (M+1) ts e) =
      ((fun i : Fin (k+1) ↦ e (prefixTimes i.succ)),
       (fun i : Fin (n+1) ↦ e (1+times i.succ))) := by
    apply Prod.ext
    · funext i
      change e (sampleTime gaps (i.val+1)) = _
      rw [sampleTime_concat_prefix k pre post _ (by omega)]
      exact congrArg e (sampleTime_orderedGaps (k+1) prefixTimes hprefix.monotone hprefixzero i.succ)
    · funext i
      change e (sampleTime gaps (k+1+i.val+1)) = _
      rw [show k+1+i.val+1 = k+1+(i.val+1) by omega,
        sampleTime_concatenatedGaps k (i.val+1),hpre,
        sampleTime_update_before n _ _ _ (by omega)]
      exact congrArg (fun t ↦ e (1+t))
        (sampleTime_orderedGaps (n+1) times hstrict.monotone hzero i.succ)
  calc
    _ = ∫⁻ u : FreeVector (k+1), ∫⁻ v : FreeVector (n+1),
        (BrownianMinimumFutureReturnDensity.returnDensity (sampleTime gaps (M+2))*
          entranceProduct M gaps (concatenatedHeights k (n+1) u v))*F (concatenatedHeights k (n+1) u v) := by
      apply lintegral_congr
      intro u
      apply lintegral_congr
      intro v
      have h := mixed_terminal_hitting_density_eq_lifetime_entrance k n pre post hT u v
      dsimp [post] at h
      rw [jointDensity_terminal_extension,Function.update_self] at h
      rw [NNReal.coe_sub hτ.le] at h
      dsimp [F]
      rw [splitHeights_concat]
      exact congrArg (fun x ↦ x*G (u,v)) h
    _ = ∫⁻ w : FreeVector (M+1),
        (BrownianMinimumFutureReturnDensity.returnDensity (sampleTime gaps (M+2))*
          entranceProduct M gaps w)*F w :=
      (lintegral_volume_concatenatedHeights k (n+1)
        ((measurable_const.mul (measurable_entranceProduct M gaps)).mul hF)).symm
    _ = BrownianMinimumFutureReturnDensity.returnDensity (1+(τ : ℝ))*
        ∫⁻ w : FreeVector (M+1), entranceProduct M gaps w*F w := by
      rw [show (sampleTime gaps (M+2) : ℝ) = 1+(τ : ℝ) by rw [htotal]; simp]
      simp_rw [mul_assoc]
      exact lintegral_const_mul _ ((measurable_entranceProduct M gaps).mul hF)
    _ = BrownianMinimumFutureReturnDensity.returnDensity (1+(τ : ℝ))*
        ∫⁻ e : Path, F (orderedEval (M+1) ts e)
          ∂BrownianEntranceContinuousRealization.pathLaw (1+τ) hTp := by
      congr 1
      have h := pathLaw_ordered_entrance_lintegral (1+τ) hTp M ts ht ht0 htslast F hF
      dsimp only [ts] at h
      simp_rw [cumulative_entranceProduct M gaps hp] at h
      exact h.symm
    _ = _ := by
      rw [lintegral_duration_scaling (1+τ) (by positivity)
        (fun e ↦ F (orderedEval (M+1) ts e))
        (hF.comp (continuous_orderedEval (M+1) ts).measurable)]
      simp only [F,hcoords]

end PerronWright.BrownianCompletedExcursionMixedSchedule
