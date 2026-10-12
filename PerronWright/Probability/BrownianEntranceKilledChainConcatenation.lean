import PerronWright.Probability.BrownianKilledFreeEntranceGeometry
import PerronWright.Probability.BrownianCompletedExcursionTerminalDensity

/-! # Literal concatenation of an entrance prefix and a killed future chain

The last prefix height is the initial point of the actual killed future.
Splitting the finite product gives the one-boundary entrance density of
the whole sampled chain. No path law or conditional density is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceKilledChainConcatenation

open BrownianKilledFiniteDimensionalDensityCoordinates BrownianPositiveKilledEndpoint
open BrownianKilledBoundaryEntrance BrownianPositiveBridgeMultiPointEntrance
open BrownianKilledFreeEntranceGeometry

def concatenatedGaps (k : ℕ) (preGaps postGaps : ℕ → ℝ≥0) (j : ℕ) : ℝ≥0 :=
  if j < k + 1 then preGaps j else postGaps (j - (k + 1))

def concatenatedHeights (k n : ℕ) (u : FreeVector (k + 1)) (v : FreeVector n) :
    FreeVector (k + n + 1) := fun i ↦
  if hi : i.val < k + 1 then u ⟨i.val, hi⟩ else v ⟨i.val - (k + 1), by omega⟩

theorem continuous_concatenatedHeights (k n : ℕ) :
    Continuous (fun q : FreeVector (k + 1) × FreeVector n ↦ concatenatedHeights k n q.1 q.2) := by
  apply continuous_pi
  intro i
  by_cases hi : i.val < k + 1
  · simp only [concatenatedHeights, dif_pos hi]
    exact (continuous_apply _).comp continuous_fst
  · simp only [concatenatedHeights, dif_neg hi]
    exact (continuous_apply _).comp continuous_snd

theorem concatenatedHeights_prefix (k n : ℕ) (u : FreeVector (k + 1)) (v : FreeVector n)
    (i : Fin (k + 1)) :
    concatenatedHeights k n u v ⟨i.val, by omega⟩ = u i := by
  simp only [concatenatedHeights, dif_pos i.isLt]

theorem concatenatedHeights_future (k n : ℕ) (u : FreeVector (k + 1)) (v : FreeVector n)
    (i : Fin n) :
    concatenatedHeights k n u v ⟨k + 1 + i.val, by omega⟩ = v i := by
  simp only [concatenatedHeights, dif_neg (by omega : ¬k + 1 + i.val < k + 1)]
  congr 1
  apply Fin.ext
  simp

private theorem left_edge (k n : ℕ) (preGaps postGaps : ℕ → ℝ≥0)
    (u : FreeVector (k + 1)) (v : FreeVector n) (i : Fin k) :
    density (concatenatedHeights k n u v (Fin.castAdd n i).castSucc)
        (concatenatedGaps k preGaps postGaps ((Fin.castAdd n i).val + 1))
        (concatenatedHeights k n u v (Fin.castAdd n i).succ) =
      density (u i.castSucc) (preGaps (i.val + 1)) (u i.succ) := by
  simp only [concatenatedHeights, concatenatedGaps, Fin.val_castSucc, Fin.val_castAdd,
    Fin.val_succ, dif_pos (by omega : i.val < k + 1),
    dif_pos (by omega : i.val + 1 < k + 1), if_pos (by omega : i.val + 1 < k + 1)]
  rfl

private theorem right_initial (k n : ℕ) (u : FreeVector (k + 1)) (v : FreeVector n)
    (j : Fin n) :
    concatenatedHeights k n u v (Fin.natAdd k j).castSucc =
      prependInitial n (u (Fin.last k)) v j.castSucc := by
  by_cases hj : j.val = 0
  · have he : j.castSucc = 0 := Fin.ext hj
    rw [he, prependInitial, Fin.cons_zero]
    simp only [concatenatedHeights, Fin.val_castSucc, Fin.val_natAdd, hj, add_zero,
      dif_pos (by omega : k < k + 1)]
    rfl
  · have hpos : 0 < j.val := Nat.pos_of_ne_zero hj
    let i : Fin n := ⟨j.val - 1, by omega⟩
    have he : j.castSucc = i.succ := Fin.ext (by dsimp [i]; omega)
    rw [he, prependInitial, Fin.cons_succ]
    simp only [concatenatedHeights, Fin.val_castSucc, Fin.val_natAdd,
      dif_neg (by omega : ¬k + j.val < k + 1)]
    congr 1
    apply Fin.ext
    dsimp [i]
    omega

private theorem right_edge (k n : ℕ) (preGaps postGaps : ℕ → ℝ≥0)
    (u : FreeVector (k + 1)) (v : FreeVector n) (j : Fin n) :
    density (concatenatedHeights k n u v (Fin.natAdd k j).castSucc)
        (concatenatedGaps k preGaps postGaps ((Fin.natAdd k j).val + 1))
        (concatenatedHeights k n u v (Fin.natAdd k j).succ) =
      density (prependInitial n (u (Fin.last k)) v j.castSucc) (postGaps j.val) (v j) := by
  rw [right_initial]
  have hsub : k + j.val + 1 - (k + 1) = j.val := by omega
  simp only [concatenatedHeights, concatenatedGaps, Fin.val_succ, Fin.val_natAdd,
    dif_neg (by omega : ¬k + j.val + 1 < k + 1),
    if_neg (by omega : ¬k + j.val + 1 < k + 1), hsub]

theorem entranceJoint_concatenated (k n : ℕ) (preGaps postGaps : ℕ → ℝ≥0)
    (u : FreeVector (k + 1)) (v : FreeVector n) :
    entranceJoint (k + n) (concatenatedGaps k preGaps postGaps) (concatenatedHeights k n u v) =
      entranceJoint k preGaps u * jointDensity n (u (Fin.last k)) postGaps v := by
  rw [entranceJoint, internalDensity, Fin.prod_univ_add]
  have hfirst : concatenatedHeights k n u v 0 = u 0 := concatenatedHeights_prefix k n u v 0
  have hgap : concatenatedGaps k preGaps postGaps 0 = preGaps 0 := by
    simp only [concatenatedGaps, if_pos (Nat.zero_lt_succ k)]
  rw [hfirst, hgap]
  rw [show (∏ i : Fin k,
      density (concatenatedHeights k n u v (Fin.castAdd n i).castSucc)
        (concatenatedGaps k preGaps postGaps ((Fin.castAdd n i).val + 1))
        (concatenatedHeights k n u v (Fin.castAdd n i).succ)) = internalDensity k preGaps u by
      exact Finset.prod_congr rfl (fun i _ ↦ left_edge k n preGaps postGaps u v i),
    show (∏ j : Fin n,
      density (concatenatedHeights k n u v (Fin.natAdd k j).castSucc)
        (concatenatedGaps k preGaps postGaps ((Fin.natAdd k j).val + 1))
        (concatenatedHeights k n u v (Fin.natAdd k j).succ)) =
      jointDensity n (u (Fin.last k)) postGaps v by
        exact Finset.prod_congr rfl (fun j _ ↦ right_edge k n preGaps postGaps u v j)]
  simp only [entranceJoint, mul_assoc]

private def concatenationIndex (k n : ℕ) : Fin (k + 1) ⊕ Fin n ≃ Fin (k + n + 1) where
  toFun := Sum.elim (fun i ↦ ⟨i.val, by omega⟩) (fun j ↦ ⟨k + 1 + j.val, by omega⟩)
  invFun i := if hi : i.val < k + 1 then Sum.inl ⟨i.val, hi⟩
    else Sum.inr ⟨i.val - (k + 1), by omega⟩
  left_inv := by
    rintro (i | j)
    · simp only [Sum.elim_inl, dif_pos i.isLt]
    · simp only [Sum.elim_inr, dif_neg (by omega : ¬k + 1 + j.val < k + 1)]
      congr 1
      apply Fin.ext
      simp
  right_inv := by
    intro i
    dsimp only
    split_ifs with hi
    · rfl
    · apply Fin.ext
      dsimp
      omega

theorem volume_preserving_concatenatedHeights (k n : ℕ) :
    MeasurePreserving (fun q : FreeVector (k + 1) × FreeVector n ↦
      concatenatedHeights k n q.1 q.2)
        ((volume : Measure (FreeVector (k + 1))).prod (volume : Measure (FreeVector n))) volume := by
  have hp := volume_measurePreserving_piCongrLeft
    (fun _ : Fin (k + n + 1) ↦ ℝ) (concatenationIndex k n)
  have hs := volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin (k + 1) ⊕ Fin n ↦ ℝ)
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin (k + n + 1) ↦ ℝ)
      (concatenationIndex k n)) ∘
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin (k + 1) ⊕ Fin n ↦ ℝ)).symm =
      fun q : FreeVector (k + 1) × FreeVector n ↦ concatenatedHeights k n q.1 q.2 := by
    funext q i
    simp only [Function.comp_apply, MeasurableEquiv.coe_piCongrLeft,
      MeasurableEquiv.coe_sumPiEquivProdPi_symm]
    by_cases hi : i.val < k + 1
    · have hx : concatenationIndex k n (Sum.inl ⟨i.val, hi⟩) = i := rfl
      have hvalue := Equiv.piCongrLeft_sumInl (fun _ : Fin (k + n + 1) ↦ ℝ)
        (concatenationIndex k n) q.1 q.2 (⟨i.val, hi⟩ : Fin (k + 1))
      rw [hx] at hvalue
      simpa only [concatenatedHeights, dif_pos hi] using hvalue
    · have hx : concatenationIndex k n (Sum.inr ⟨i.val - (k + 1), by omega⟩) = i := by
        apply Fin.ext
        dsimp [concatenationIndex]
        omega
      have hvalue := Equiv.piCongrLeft_sumInr (fun _ : Fin (k + n + 1) ↦ ℝ)
        (concatenationIndex k n) q.1 q.2 (⟨i.val - (k + 1), by omega⟩ : Fin n)
      rw [hx] at hvalue
      simpa only [concatenatedHeights, dif_neg hi] using hvalue
  simpa only [he, volume_pi, Measure.volume_eq_prod] using hp.comp hs

theorem lintegral_volume_concatenatedHeights (k n : ℕ)
    {F : FreeVector (k + n + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ w, F w) = ∫⁻ u : FreeVector (k + 1), ∫⁻ v : FreeVector n,
      F (concatenatedHeights k n u v) := by
  rw [← (volume_preserving_concatenatedHeights k n).lintegral_comp hF]
  exact lintegral_prod _ (hF.comp (continuous_concatenatedHeights k n).measurable).aemeasurable

theorem concatenatedHeights_last (k n : ℕ) (u : FreeVector (k + 1)) (v : FreeVector (n + 1)) :
    concatenatedHeights k (n + 1) u v (Fin.last (k + (n + 1))) = v (Fin.last n) := by
  have he : (⟨k + 1 + (Fin.last n).val, by omega⟩ : Fin (k + (n + 1) + 1)) =
      Fin.last (k + (n + 1)) := Fin.ext (by simp; omega)
  rw [← he]
  exact concatenatedHeights_future k (n + 1) u v (Fin.last n)

theorem mixed_terminal_hitting_density_eq_lifetime_entrance (k n : ℕ)
    (preGaps postGaps : ℕ → ℝ≥0)
    (hT : 1 < BrownianKilledFiniteDimensionalCoordinates.sampleTime
      (concatenatedGaps k preGaps postGaps) (k + (n + 1) + 2))
    (u : FreeVector (k + 1)) (v : FreeVector (n + 1)) :
    (entranceJoint k preGaps u * jointDensity (n + 1) (u (Fin.last k)) postGaps v) *
        BrownianFirstPassageDensityGeometry.density (v (Fin.last n)) (postGaps (n + 1)) /
          ENNReal.ofReal (Real.sqrt (2 / Real.pi)) =
      BrownianMinimumFutureReturnDensity.returnDensity
        (BrownianKilledFiniteDimensionalCoordinates.sampleTime
          (concatenatedGaps k preGaps postGaps) (k + (n + 1) + 2)) *
        entranceProduct (k + (n + 1)) (concatenatedGaps k preGaps postGaps)
          (concatenatedHeights k (n + 1) u v) := by
  have hgap : concatenatedGaps k preGaps postGaps (k + (n + 1) + 1) = postGaps (n + 1) := by
    simp only [concatenatedGaps, if_neg (by omega : ¬k + (n + 1) + 1 < k + 1)]
    congr 1
    omega
  simpa only [entranceJoint_concatenated, concatenatedHeights_last, hgap] using
    BrownianCompletedExcursionTerminalDensity.terminal_hitting_density_eq_lifetime_entrance
      (k + (n + 1)) (concatenatedGaps k preGaps postGaps) hT (concatenatedHeights k (n + 1) u v)

theorem sampleTime_concatenatedGaps (k n : ℕ) (preGaps postGaps : ℕ → ℝ≥0) :
    BrownianKilledFiniteDimensionalCoordinates.sampleTime (concatenatedGaps k preGaps postGaps)
      (k + 1 + n) =
      BrownianKilledFiniteDimensionalCoordinates.sampleTime preGaps (k + 1) +
        BrownianKilledFiniteDimensionalCoordinates.sampleTime postGaps n := by
  unfold BrownianKilledFiniteDimensionalCoordinates.sampleTime
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    exact if_pos (Finset.mem_range.mp hj)
  · apply Finset.sum_congr rfl
    intro j hj
    simp only [concatenatedGaps, if_neg (by omega : ¬k + 1 + j < k + 1),
      Nat.add_sub_cancel_left]

theorem jointDensity_terminal_extension (n : ℕ) (a : ℝ) (gaps : ℕ → ℝ≥0)
    (terminal : ℝ≥0) (v : FreeVector (n + 1)) :
    jointDensity (n + 1) a (Function.update gaps (n + 1) terminal) v =
      jointDensity (n + 1) a gaps v := by
  unfold jointDensity
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (ne_of_lt i.isLt)]

theorem sampleTime_terminal_extension (n : ℕ) (gaps : ℕ → ℝ≥0) (terminal : ℝ≥0) :
    BrownianKilledFiniteDimensionalCoordinates.sampleTime (Function.update gaps (n + 1) terminal)
      (n + 2) = BrownianKilledFiniteDimensionalCoordinates.sampleTime gaps (n + 1) + terminal := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    BrownianKilledFiniteDimensionalCoordinates.sampleTime_succ, Function.update_self]
  congr 1
  unfold BrownianKilledFiniteDimensionalCoordinates.sampleTime
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (ne_of_lt (Finset.mem_range.mp hj))]

end PerronWright.BrownianEntranceKilledChainConcatenation
