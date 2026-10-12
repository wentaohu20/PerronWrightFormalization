import PerronWright.Probability.AnnealedProfileFunctionalContinuous

/-!
# Continuous profile functionals evaluated at the actual sampled mark

Exact empirical averaging and label reindexing identify the continuous
probability-measure functionals with normalized exposure moments in the
literal selected residual.  Repeated type values cause no restrictions.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedProfileFunctionalSampled

open AnnealedProfileFunctionalContinuous EmpiricalMarkConcentration EmpiricalTypeMarks
  FreshTypeAveraging FreshTypeCumulantExpansion FreshTypeEmpiricalIdentities
  ExactFactorialExpectation AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
  AnnealedTupleResidualConnectedLawWeights AnnealedTupleResidualConnectedLawCoordinates
  ProfileFiniteCollection ProjectiveFiniteCollection ProfileLaplace ConnectedTypeLaw

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

theorem exposureProfile_typesMark (M : CompactBJRModel S) {k : ℕ}
    (hk : 0 < k) (x : Fin k → S) (y : S) :
    exposureProfile M (typesMark hk x) y = (k:ℝ)⁻¹ * exposure M x y := by
  have h := typesMark_integral hk x (⟨fun z ↦ M.kernel z y,by fun_prop⟩ : C(S,ℝ))
  simpa only [exposureProfile,exposure,typeSum,ContinuousMap.coe_mk] using h

theorem exposureMomentFunctional_typesMark (M : CompactBJRModel S) {k : ℕ}
    (hk : 0 < k) (x : Fin k → S) (j : ℕ) :
    exposureMomentFunctional M j (typesMark hk x) = (k:ℝ)⁻¹ ^ j * exposureMoment M x j := by
  rw [exposureMomentFunctional_eq_power_integral]
  simp_rw [exposureProfile_typesMark,mul_pow]
  rw [integral_const_mul]
  rfl

theorem degreeFunctional_typesMark (M : CompactBJRModel S) {k : ℕ}
    (hk : 0 < k) (x : Fin k → S) :
    degreeFunctional M (typesMark hk x) = (k:ℝ)⁻¹ * totalDegree M x := by
  exact typesMark_integral hk x M.degreeFunction

theorem varianceFunctional_typesMark (M : CompactBJRModel S) {k : ℕ}
    (hk : 0 < k) (x : Fin k → S) :
    varianceFunctional M (typesMark hk x) = (k:ℝ)⁻¹ ^ 2 * exposureVariance M x := by
  rw [varianceFunctional,exposureMomentFunctional_typesMark,degreeFunctional_typesMark]
  unfold exposureVariance
  ring

theorem thirdCumulantFunctional_typesMark (M : CompactBJRModel S) {k : ℕ}
    (hk : 0 < k) (x : Fin k → S) :
    thirdCumulantFunctional M (typesMark hk x) = (k:ℝ)⁻¹ ^ 3 * exposureThirdCumulant M x := by
  rw [thirdCumulantFunctional,exposureMomentFunctional_typesMark,
    exposureMomentFunctional_typesMark,degreeFunctional_typesMark]
  unfold exposureThirdCumulant
  ring

theorem pairFunctional_typesMark (H : C(S × S,ℝ)) {k : ℕ} (hk : 0 < k) (x : Fin k → S) :
    pairFunctional H (typesMark hk x) = (k:ℝ)⁻¹ ^ 2 * ∑ i : Fin k, ∑ j : Fin k, H (x i,x j) := by
  let ρ : Measure S := typesMark hk x
  let g : C(S,ℝ) := KernelMap.action ρ H 1
  have hi : Integrable (fun z ↦ H z) (ρ.prod ρ) :=
    H.continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hg (z : S) : g z = (k:ℝ)⁻¹ * ∑ j : Fin k, H (z,x j) := by
    rw [show g z = ∫ y, H (z,y) ∂ρ by simp only [g,KernelMap.action_apply,ContinuousMap.one_apply,mul_one]]
    have h := typesMark_integral hk x (⟨fun y ↦ H (z,y),by fun_prop⟩ : C(S,ℝ))
    change (∫ y, H (z,y) ∂ρ) = (k:ℝ)⁻¹ * ∑ j : Fin k, H (z,x j) at h
    exact h
  unfold pairFunctional
  change (∫ z, H z ∂ρ.prod ρ) = _
  rw [integral_prod _ hi]
  have hgg : (fun z ↦ ∫ y, H (z,y) ∂ρ) = (fun z ↦ g z) := by
    funext z
    simp only [g,KernelMap.action_apply,ContinuousMap.one_apply,mul_one]
  rw [hgg]
  have hav := typesMark_integral hk x g
  change (∫ z, g z ∂ρ) = (k:ℝ)⁻¹ * ∑ i : Fin k, g (x i) at hav
  rw [hav]
  simp_rw [hg]
  rw [← Finset.mul_sum]
  ring

theorem kernelPairFunctional_typesMark (M : CompactBJRModel S) {k : ℕ}
    (hk : 0 < k) (x : Fin k → S) :
    kernelPairFunctional M (typesMark hk x) = (k:ℝ)⁻¹ ^ 2 * pairKernelSum M x :=
  pairFunctional_typesMark M.kernel.toContinuousMap hk x

def selectedPooledEquiv {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) :
    Fin (Fintype.card (SelectedVertices k)) ≃ ↥(selectedUnion (blocksOfPlacement hk f)) :=
  (Fintype.equivFin (SelectedVertices k)).symm.trans (selectedVerticesEquiv hk f)

omit [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
theorem selectedTypes_comp_selectedPooledEquiv {n q : ℕ} {k : Fin q → ℕ}
    (hk : ∀ i, 0 < k i) (f : Placements n k) (p : StateFamily (S := S) k) :
    (selectedTypes hk f (fun i ↦ (p i).1)) ∘ selectedPooledEquiv hk f = pooledTypes k p := by
  funext v
  simp only [Function.comp_apply,selectedPooledEquiv,Equiv.trans_apply,selectedTypes,pooledTypes]
  exact congrArg (fun w : SelectedVertices k ↦ (p w.1).1 w.2)
    ((selectedVerticesEquiv hk f).symm_apply_apply ((Fintype.equivFin (SelectedVertices k)).symm v))

theorem exposure_comp_equiv {I J : Type*} [Fintype I] [Fintype J]
    (M : CompactBJRModel S) (e : I ≃ J) (x : J → S) (y : S) :
    exposure M (x ∘ e) y = exposure M x y := Equiv.sum_comp e (fun i ↦ M.kernel (x i) y)

theorem totalDegree_comp_equiv {I J : Type*} [Fintype I] [Fintype J]
    (M : CompactBJRModel S) (e : I ≃ J) (x : J → S) :
    totalDegree M (x ∘ e) = totalDegree M x := Equiv.sum_comp e (fun i ↦ M.degreeFunction (x i))

theorem exposureMoment_comp_equiv {I J : Type*} [Fintype I] [Fintype J]
    (M : CompactBJRModel S) (e : I ≃ J) (x : J → S) (j : ℕ) :
    exposureMoment M (x ∘ e) j = exposureMoment M x j := by
  unfold exposureMoment
  simp_rw [exposure_comp_equiv]

theorem pairKernelSum_comp_equiv {I J : Type*} [Fintype I] [Fintype J]
    (M : CompactBJRModel S) (e : I ≃ J) (x : J → S) :
    pairKernelSum M (x ∘ e) = pairKernelSum M x := by
  unfold pairKernelSum
  calc
    _ = ∑ i : I, ∑ j : J, M.kernel (x (e i)) (x j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp e (fun j ↦ M.kernel (x (e i)) (x j))
    _ = _ := Equiv.sum_comp e (fun i ↦ ∑ j : J, M.kernel (x i) (x j))

theorem exposureMoment_selected_eq_pooled {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) (j : ℕ) :
    exposureMoment M (selectedTypes hk f (fun i ↦ (p i).1)) j = exposureMoment M (pooledTypes k p) j := by
  have h := exposureMoment_comp_equiv M (selectedPooledEquiv hk f)
    (selectedTypes hk f (fun i ↦ (p i).1)) j
  rw [selectedTypes_comp_selectedPooledEquiv] at h
  exact h.symm

theorem totalDegree_selected_eq_pooled {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) :
    totalDegree M (selectedTypes hk f (fun i ↦ (p i).1)) = totalDegree M (pooledTypes k p) := by
  have h := totalDegree_comp_equiv M (selectedPooledEquiv hk f)
    (selectedTypes hk f (fun i ↦ (p i).1))
  rw [selectedTypes_comp_selectedPooledEquiv] at h
  exact h.symm

theorem pairKernelSum_selected_eq_pooled {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) :
    pairKernelSum M (selectedTypes hk f (fun i ↦ (p i).1)) = pairKernelSum M (pooledTypes k p) := by
  have h := pairKernelSum_comp_equiv M (selectedPooledEquiv hk f)
    (selectedTypes hk f (fun i ↦ (p i).1))
  rw [selectedTypes_comp_selectedPooledEquiv] at h
  exact h.symm

theorem exposureVariance_selected_eq_pooled {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) :
    exposureVariance M (selectedTypes hk f (fun i ↦ (p i).1)) = exposureVariance M (pooledTypes k p) := by
  simp only [exposureVariance,exposureMoment_selected_eq_pooled,totalDegree_selected_eq_pooled]

theorem exposureThirdCumulant_selected_eq_pooled {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) :
    exposureThirdCumulant M (selectedTypes hk f (fun i ↦ (p i).1)) = exposureThirdCumulant M (pooledTypes k p) := by
  simp only [exposureThirdCumulant,exposureMoment_selected_eq_pooled,totalDegree_selected_eq_pooled]

/-- The actual selected fresh-exposure moments are exactly the continuous
moment functionals of the pooled mark, after the natural total-size scaling. -/
theorem exposureMomentFunctional_pooledMark_eq_selected {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hq : 0 < q) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) (j : ℕ) :
    exposureMomentFunctional M j (pooledMark hq k hk p) =
      (∑ i, (k i : ℝ))⁻¹ ^ j * exposureMoment M (selectedTypes hk f (fun i ↦ (p i).1)) j := by
  rw [pooledMark,exposureMomentFunctional_typesMark,pooled_card_real,exposureMoment_selected_eq_pooled]

theorem degreeFunctional_pooledMark_eq_selected {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hq : 0 < q) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) :
    degreeFunctional M (pooledMark hq k hk p) =
      (∑ i, (k i : ℝ))⁻¹ * totalDegree M (selectedTypes hk f (fun i ↦ (p i).1)) := by
  rw [pooledMark,degreeFunctional_typesMark,pooled_card_real,totalDegree_selected_eq_pooled]

theorem kernelPairFunctional_pooledMark_eq_selected {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hq : 0 < q) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) :
    kernelPairFunctional M (pooledMark hq k hk p) =
      (∑ i, (k i : ℝ))⁻¹ ^ 2 * pairKernelSum M (selectedTypes hk f (fun i ↦ (p i).1)) := by
  rw [pooledMark,kernelPairFunctional_typesMark,pooled_card_real,pairKernelSum_selected_eq_pooled]

theorem varianceFunctional_pooledMark_eq_selected {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hq : 0 < q) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) :
    varianceFunctional M (pooledMark hq k hk p) =
      (∑ i, (k i : ℝ))⁻¹ ^ 2 * exposureVariance M (selectedTypes hk f (fun i ↦ (p i).1)) := by
  rw [pooledMark,varianceFunctional_typesMark,pooled_card_real,exposureVariance_selected_eq_pooled]

theorem thirdCumulantFunctional_pooledMark_eq_selected {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hq : 0 < q) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) :
    thirdCumulantFunctional M (pooledMark hq k hk p) =
      (∑ i, (k i : ℝ))⁻¹ ^ 3 * exposureThirdCumulant M (selectedTypes hk f (fun i ↦ (p i).1)) := by
  rw [pooledMark,thirdCumulantFunctional_typesMark,pooled_card_real,exposureThirdCumulant_selected_eq_pooled]

end PerronWright.AnnealedProfileFunctionalSampled
