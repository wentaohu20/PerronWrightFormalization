import PerronWright.Probability.BrownianEntranceKernelLaplace
import PerronWright.Probability.BrownianKilledGreenKernel
import PerronWright.Probability.BrownianKilledFreeEntranceGeometry

/-! # Joint geometry of the genuine entrance--interior--exit product

The normalized kernel is the literal density already used for the actual
positive bridge area moments. Its raw numerator has one entrance factor
at each boundary and the actual killed transition at every interior edge.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianEntranceProductGeometry

open BrownianKilledBoundaryEntrance BrownianPositiveBridgeMultiPointEntrance
open BrownianKilledFiniteDimensionalCoordinates BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianKilledAreaMomentDensity BrownianKilledAreaMomentResolvent

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

theorem measurable_joint_entranceNN :
    Measurable (fun q : ℝ≥0 × ℝ ↦ entrance q.1 q.2) := by
  have h := BrownianEntranceKernelLaplace.measurable_joint_entrance.comp
    (measurable_fst.coe_nnreal_real.prodMk measurable_snd)
  simpa only [Function.comp_def,Real.toNNReal_coe] using h

theorem measurable_joint_entranceReal :
    Measurable (fun q : ℝ≥0 × ℝ ↦ entranceReal q.1 q.2) := by
  have h := measurable_joint_entranceNN.ennreal_toReal
  simpa only [Function.comp_def,entrance,ENNReal.toReal_ofReal (entranceReal_nonneg _ _)] using h

theorem measurable_sampleTime (d : ℕ) : Measurable (fun gaps : ℕ → ℝ≥0 ↦ sampleTime gaps d) := by
  unfold sampleTime
  apply Finset.measurable_sum
  intro i _
  exact measurable_pi_apply i

theorem measurable_joint_internalDensity (n : ℕ) :
    Measurable (fun q : (ℕ → ℝ≥0) × FreeVector (n+1) ↦ internalDensity n q.1 q.2) := by
  unfold internalDensity
  apply Finset.measurable_prod
  intro i _
  have hp : Measurable (fun q : (ℕ → ℝ≥0) × FreeVector (n+1) ↦
      (q.1 (i.val+1),(q.2 i.castSucc,q.2 i.succ))) := by fun_prop
  exact measurable_time_joint_density.comp hp

theorem measurable_joint_entranceProduct (n : ℕ) :
    Measurable (fun q : (ℕ → ℝ≥0) × FreeVector (n+1) ↦ entranceProduct n q.1 q.2) := by
  have hx : Measurable (fun q : (ℕ → ℝ≥0) × FreeVector (n+1) ↦ entranceReal (q.1 0) (q.2 0)) :=
    measurable_joint_entranceReal.comp
      (by fun_prop : Measurable (fun q : (ℕ → ℝ≥0) × FreeVector (n+1) ↦ (q.1 0,q.2 0)))
  have hy : Measurable (fun q : (ℕ → ℝ≥0) × FreeVector (n+1) ↦
      entranceReal (q.1 (n+1)) (q.2 (Fin.last n))) :=
    measurable_joint_entranceReal.comp
      (by fun_prop : Measurable (fun q : (ℕ → ℝ≥0) × FreeVector (n+1) ↦
        (q.1 (n+1),q.2 (Fin.last n))))
  have hT := (measurable_sampleTime (n+2)).comp
    (measurable_fst : Measurable (Prod.fst : (ℕ → ℝ≥0) × FreeVector (n+1) → _))
  have hden : Measurable (fun q : (ℕ → ℝ≥0) × FreeVector (n+1) ↦
      (2/(sampleTime q.1 (n+2) : ℝ))*gaussianPDFReal 0 (sampleTime q.1 (n+2)) 0) :=
    (measurable_const.div hT.coe_nnreal_real).mul
      (measurable_uncurry_gaussianPDFReal.comp
        (measurable_const.prodMk (hT.prodMk measurable_const)))
  exact ((hx.mul hy).div hden).ennreal_ofReal.mul (measurable_joint_internalDensity n)

/-- Zero extension of a finite real duration vector, with its actual
nonnegative duration at every edge. -/
def finiteGaps (n : ℕ) (σ : Fin (n+2) → ℝ) (j : ℕ) : ℝ≥0 :=
  if hj : j < n+2 then Real.toNNReal (σ ⟨j,hj⟩) else 0

theorem finiteGaps_at (n : ℕ) (σ : Fin (n+2) → ℝ) (i : Fin (n+2)) :
    finiteGaps n σ i.val = Real.toNNReal (σ i) := by
  simp only [finiteGaps,dif_pos i.isLt]

theorem measurable_finiteGaps (n : ℕ) : Measurable (finiteGaps n) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j < n+2
  · simpa only [finiteGaps,dif_pos hj] using (measurable_pi_apply (⟨j,hj⟩ : Fin (n+2))).real_toNNReal
  · simp only [finiteGaps,dif_neg hj]
    exact measurable_const

theorem realDensity_zero_eq_killed (t x y : ℝ) :
    realDensity 0 t x y = BrownianPositiveKilledEndpoint.density x (Real.toNNReal t) y := by
  by_cases ht : 0 < t
  · rw [realDensity,if_pos ht,density_zero]
  · rw [realDensity,if_neg ht,Real.toNNReal_eq_zero.mpr (le_of_not_gt ht)]
    simp only [BrownianPositiveKilledEndpoint.density,BrownianPositiveKilledEndpoint.densityReal,
      gaussianPDFReal_zero_var,Pi.zero_apply,sub_self]
    simp

def edgeKernel (n : ℕ) (i : Fin (n+2)) (t : ℝ) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  Fin.cases (entrance (Real.toNNReal t) (v 0))
    (fun j ↦ Fin.lastCases (entrance (Real.toNNReal t) (v (Fin.last n)))
      (fun k ↦ realDensity 0 t (v k.castSucc) (v k.succ)) j) i

theorem measurable_edgeKernel (n : ℕ) (i : Fin (n+2)) :
    Measurable (fun q : ℝ × FreeVector (n+1) ↦ edgeKernel n i q.1 q.2) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [edgeKernel,Fin.cases_zero,Function.comp_def] using
      BrownianEntranceKernelLaplace.measurable_joint_entrance.comp
        (by fun_prop : Measurable (fun q : ℝ × FreeVector (n+1) ↦ (q.1,q.2 0)))
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simpa only [edgeKernel,Fin.cases_succ,Fin.lastCases_last,Function.comp_def] using
        BrownianEntranceKernelLaplace.measurable_joint_entrance.comp
          (by fun_prop : Measurable (fun q : ℝ × FreeVector (n+1) ↦ (q.1,q.2 (Fin.last n))))
    · simpa only [edgeKernel,Fin.cases_succ,Fin.lastCases_castSucc,Function.comp_def] using
        (measurable_realDensity 0).comp
          (by fun_prop : Measurable (fun q : ℝ × FreeVector (n+1) ↦
            (q.1,(q.2 k.castSucc,q.2 k.succ))))

theorem edgeKernel_zero_of_nonpos (n : ℕ) (i : Fin (n+2)) (t : ℝ)
    (ht : t ≤ 0) (v : FreeVector (n+1)) : edgeKernel n i t v = 0 := by
  have he (z : ℝ) : entrance (Real.toNNReal t) z = 0 := by
    rw [Real.toNNReal_eq_zero.mpr ht]
    simp only [entrance,entranceReal,gaussianPDFReal_zero_var,Pi.zero_apply,mul_zero]
    simp
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [edgeKernel,Fin.cases_zero] using he (v 0)
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simpa only [edgeKernel,Fin.cases_succ,Fin.lastCases_last] using he (v (Fin.last n))
    · simp only [edgeKernel,Fin.cases_succ,Fin.lastCases_castSucc,realDensity,if_neg (not_lt.mpr ht)]

def rawNumerator (n : ℕ) (σ : Fin (n+2) → ℝ) (v : FreeVector (n+1)) : ℝ≥0∞ :=
  ∏ i, edgeKernel n i (σ i) v

theorem measurable_rawNumerator (n : ℕ) :
    Measurable (fun q : (Fin (n+2) → ℝ) × FreeVector (n+1) ↦ rawNumerator n q.1 q.2) := by
  unfold rawNumerator
  apply Finset.measurable_prod
  intro i _
  exact (measurable_edgeKernel n i).comp
    (by fun_prop : Measurable (fun q : (Fin (n+2) → ℝ) × FreeVector (n+1) ↦ (q.1 i,q.2)))

theorem rawNumerator_eq_factors (n : ℕ) (σ : Fin (n+2) → ℝ) (v : FreeVector (n+1)) :
    rawNumerator n σ v = entrance (Real.toNNReal (σ 0)) (v 0)*
      (∏ k : Fin n, realDensity 0 (σ k.castSucc.succ) (v k.castSucc) (v k.succ))*
        entrance (Real.toNNReal (σ (Fin.last (n+1)))) (v (Fin.last n)) := by
  unfold rawNumerator
  rw [Fin.prod_univ_succ,Fin.prod_univ_castSucc]
  rw [show Fin.last (n+1) = (Fin.last n).succ by exact (Fin.succ_last n).symm]
  simp only [edgeKernel,Fin.cases_zero,Fin.cases_succ,Fin.lastCases_last,
    Fin.lastCases_castSucc,mul_assoc]

theorem rawNumerator_eq_literal_factors (n : ℕ) (σ : Fin (n+2) → ℝ) (v : FreeVector (n+1)) :
    rawNumerator n σ v = entrance (finiteGaps n σ 0) (v 0)*internalDensity n (finiteGaps n σ) v*
      entrance (finiteGaps n σ (n+1)) (v (Fin.last n)) := by
  rw [rawNumerator_eq_factors]
  simp only [internalDensity,realDensity_zero_eq_killed]
  have h0 := finiteGaps_at n σ (0 : Fin (n+2))
  have hl := finiteGaps_at n σ (Fin.last (n+1))
  simp only [Fin.val_zero,Fin.val_last] at h0 hl
  rw [h0,hl]
  congr 2
  apply Finset.prod_congr rfl
  intro k _
  rw [← finiteGaps_at n σ k.castSucc.succ]
  rfl

/-- The actual normalized positive-bridge density, with finite gaps. -/
theorem entranceProduct_eq_rawNumerator (n : ℕ) (σ : Fin (n+2) → ℝ)
    (hT : 0 < sampleTime (finiteGaps n σ) (n+2)) (v : FreeVector (n+1)) :
    entranceProduct n (finiteGaps n σ) v = rawNumerator n σ v/
      ENNReal.ofReal ((2/(sampleTime (finiteGaps n σ) (n+2) : ℝ))*
        gaussianPDFReal 0 (sampleTime (finiteGaps n σ) (n+2)) 0) := by
  rw [entranceProduct_eq_factors n _ hT,rawNumerator_eq_literal_factors]

theorem entranceProduct_mul_normalization (n : ℕ) (σ : Fin (n+2) → ℝ)
    (hT : 0 < sampleTime (finiteGaps n σ) (n+2)) (v : FreeVector (n+1)) :
    entranceProduct n (finiteGaps n σ) v*
      ENNReal.ofReal ((2/(sampleTime (finiteGaps n σ) (n+2) : ℝ))*
        gaussianPDFReal 0 (sampleTime (finiteGaps n σ) (n+2)) 0) = rawNumerator n σ v := by
  have hp := gaussianPDFReal_pos 0 (sampleTime (finiteGaps n σ) (n+2)) 0 (ne_of_gt hT)
  have hd : 0 < (2/(sampleTime (finiteGaps n σ) (n+2) : ℝ))*
      gaussianPDFReal 0 (sampleTime (finiteGaps n σ) (n+2)) 0 := by positivity
  rw [entranceProduct_eq_rawNumerator n σ hT]
  exact ENNReal.div_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top

def positiveGaps (d : ℕ) : Set (Fin d → ℝ) := {σ | ∀ i, 0 < σ i}

theorem measurableSet_positiveGaps (d : ℕ) : MeasurableSet (positiveGaps d) := by
  simpa only [positiveGaps,Set.ofPred_forall] using
    MeasurableSet.iInter (fun i : Fin d ↦
      measurableSet_lt measurable_const (measurable_pi_apply i : Measurable (fun σ : Fin d → ℝ ↦ σ i)))

theorem rawNumerator_zero_off_positiveGaps (n : ℕ) (σ : Fin (n+2) → ℝ)
    (hσ : σ ∉ positiveGaps (n+2)) (v : FreeVector (n+1)) : rawNumerator n σ v = 0 := by
  obtain ⟨i,hi⟩ := not_forall.mp hσ
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (edgeKernel_zero_of_nonpos n i _ (le_of_not_gt hi) v)

end PerronWright.BrownianEntranceProductGeometry
