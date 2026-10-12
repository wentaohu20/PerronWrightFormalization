import PerronWright.Probability.FreshTypeEmpiricalIdentities
import PerronWright.Probability.AnnealedResidualCumulantExpansion
import PerronWright.Probability.ProjectiveQuadratic
import PerronWright.Probability.ProjectiveFiniteCollection
import PerronWright.Analysis.PerronFunctional

/-!
# Genuine Perron centering of the fresh-type residual kernel

The canonical residual kernel has zero Perron row and column integrals.
Consequently its empirical double sum is exactly the centered quadratic
observable already used by the project's profile concentration theorems.
No centering or moment identity is imposed as an assumption.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FreshTypePerronCentering

open ProjectiveKernel ProjectiveKernelClosure FreshTypeEmpiricalIdentities
  FreshTypeAveraging FreshTypeCumulantExpansion AnnealedResidualFixedBlock
  AnnealedResidualCumulantExpansion
  ExactFactorialExpectation AnnealedTupleResidualCounting AnnealedTupleResidualPatternFormula
  AnnealedTupleResidualConnectedLawWeights AnnealedTupleResidualConnectedLawCoordinates
  ProfileFiniteCollection ProjectiveFiniteCollection

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

theorem degreeFunction_eq_action_one (M : CompactBJRModel S) :
    M.degreeFunction = M.kernel.action M.mu 1 := by
  ext x
  simp only [CompactBJRModel.degreeFunction,ContinuousKernel.degreeMap_apply,
    ContinuousKernel.action_apply,ContinuousMap.one_apply,mul_one]
  rfl

theorem perronLaw_degreeFunction_integral (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (∫ x, M.degreeFunction x ∂M.perronLaw hM) = 1 := by
  rw [M.perronLaw_integral hM M.degreeFunction,degreeFunction_eq_action_one]
  change M.weightedIntegral hM (M.kernel.action M.mu 1) = 1
  rw [M.weightedIntegral_action hM]
  simpa only [CompactBJRModel.weightedIntegral,ContinuousMap.one_apply,mul_one] using
    M.perronFunction_integral hM

theorem perronLaw_centeredDegree_integral (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (∫ x, (M.degreeFunction x - 1) ∂M.perronLaw hM) = 0 := by
  rw [integral_sub (M.degreeFunction.continuous.integrable_of_hasCompactSupport
    isClosed_closure.isCompact) (integrable_const 1),perronLaw_degreeFunction_integral]
  simp

theorem perronLaw_row_integral_eq_action (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (H : C(S × S, ℝ)) (x : S) :
    (∫ y, H (x,y) ∂M.perronLaw hM) = KernelMap.action M.mu H (M.perronFunction hM) x := by
  have h := M.perronLaw_integral hM (⟨fun y ↦ H (x,y),by fun_prop⟩ : C(S,ℝ))
  rw [KernelMap.action_apply]
  exact h.trans (integral_congr_ae (Filter.Eventually.of_forall (fun y ↦ mul_comm _ _)))

theorem iteratedKernelMap_one_perron_action (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    KernelMap.action M.mu (M.iteratedKernelMap 1) (M.perronFunction hM) = M.perronFunction hM := by
  rw [CompactBJRModel.iteratedKernelMap_succ,CompactBJRModel.iteratedKernelMap_zero,
    KernelMap.action_comp,KernelMap.action_toContinuousMap,KernelMap.action_toContinuousMap,
    M.perronFunction_fixed hM,M.perronFunction_fixed hM]

/-- The actual model residual kernel has zero Perron row integral. -/
theorem residualKernel_perron_row_integral (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (x : S) : (∫ y, residualKernel M (x,y) ∂M.perronLaw hM) = 0 := by
  have hκ₂ := perronLaw_row_integral_eq_action M hM (M.iteratedKernelMap 1) x
  rw [iteratedKernelMap_one_perron_action] at hκ₂
  have hκ := perronLaw_row_integral_eq_action M hM M.kernel.toContinuousMap x
  rw [KernelMap.action_toContinuousMap,M.perronFunction_fixed hM] at hκ
  have he : (fun y ↦ residualKernel M (x,y)) =
      fun y ↦ M.iteratedKernelMap 1 (x,y) - M.kernel x y -
        (M.degreeFunction x - 1) * (M.degreeFunction y - 1) := rfl
  rw [he,integral_sub,integral_sub,integral_const_mul,perronLaw_centeredDegree_integral,
    hκ₂,hκ,mul_zero,sub_self,sub_zero]
  · exact (by fun_prop : Continuous (fun y ↦ M.iteratedKernelMap 1 (x,y))).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  · exact (by fun_prop : Continuous (fun y ↦ M.kernel x y)).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  · exact (by fun_prop : Continuous (fun y ↦ M.iteratedKernelMap 1 (x,y) - M.kernel x y)).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  · exact (by fun_prop : Continuous (fun y ↦ (M.degreeFunction x-1)*(M.degreeFunction y-1))).integrable_of_hasCompactSupport
      isClosed_closure.isCompact

theorem residualKernel_symmetric (M : CompactBJRModel S) (x y : S) :
    residualKernel M (x,y) = residualKernel M (y,x) := by
  have hκ₂ : (∫ z, M.kernel x z * M.kernel z y ∂M.mu) =
      ∫ z, M.kernel y z * M.kernel z x ∂M.mu := by
    apply integral_congr_ae
    filter_upwards [] with z
    change M.kernel x z * M.kernel z y = M.kernel y z * M.kernel z x
    rw [M.kernel.symmetric x z,M.kernel.symmetric z y]
    ring
  rw [residualKernel_apply,residualKernel_apply,hκ₂,M.kernel.symmetric x y]
  ring

theorem residualKernel_perron_column_integral (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (y : S) : (∫ x, residualKernel M (x,y) ∂M.perronLaw hM) = 0 := by
  simp_rw [residualKernel_symmetric M _ y]
  exact residualKernel_perron_row_integral M hM y

/-- The centered and uncentered residual-kernel double integrals coincide
for any genuine probability law, by proved Perron orthogonality. -/
theorem residual_centeredQuadraticCLM_eq_doubleIntegral (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (ν : Measure S) [IsProbabilityMeasure ν] :
    centeredQuadraticCLM ν (M.perronLaw hM) (residualKernel M) =
      ∫ z, residualKernel M z ∂ν.prod ν := by
  have hi (ρ τ : Measure S) [IsProbabilityMeasure ρ] [IsProbabilityMeasure τ] :
      Integrable (fun z ↦ residualKernel M z) (ρ.prod τ) :=
    (residualKernel M).continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have hνp : (∫ z, residualKernel M z ∂ν.prod (M.perronLaw hM)) = 0 := by
    rw [integral_prod _ (hi ν (M.perronLaw hM))]
    simp_rw [residualKernel_perron_row_integral]
    simp
  have hpν : (∫ z, residualKernel M z ∂(M.perronLaw hM).prod ν) = 0 := by
    rw [integral_prod_symm _ (hi (M.perronLaw hM) ν)]
    simp_rw [residualKernel_perron_column_integral]
    simp
  have hpp : (∫ z, residualKernel M z ∂(M.perronLaw hM).prod (M.perronLaw hM)) = 0 := by
    rw [integral_prod _ (hi (M.perronLaw hM) (M.perronLaw hM))]
    simp_rw [residualKernel_perron_row_integral]
    simp
  rw [centeredQuadraticCLM_apply,hνp,hpν,hpp]
  ring

/-- The centered empirical quadratic is the actual sampled-label double
sum divided by its number of vertices. -/
theorem empiricalQuadratic_residualKernel_eq_sum (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) {k : ℕ} (x : Fin k → S) (hk : 0 < k) :
    empiricalQuadratic M hM x Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0,hk⟩⟩) (residualKernel M) =
      (k : ℝ)⁻¹ * residualKernelSum M x := by
  let ρ := EmpiricalTypeMarks.empiricalMeasure x Finset.univ
  let : IsProbabilityMeasure ρ := EmpiricalTypeMarks.empiricalMeasure_isProbability x Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨⟨0,hk⟩⟩)
  let H := residualKernel M
  let g : C(S,ℝ) := KernelMap.action ρ H 1
  have hg (z : S) : g z = (k:ℝ)⁻¹ * ∑ j : Fin k, H (z,x j) := by
    rw [show g z = ∫ y, H (z,y) ∂ρ by simp only [g,KernelMap.action_apply,ContinuousMap.one_apply,mul_one]]
    have h := EmpiricalTypeMarks.empiricalMeasure_integral x Finset.univ
      (⟨fun y ↦ H (z,y),by fun_prop⟩ : C(S,ℝ))
    simpa only [Finset.card_univ,Fintype.card_fin,ρ,ContinuousMap.coe_mk] using h
  have hi : Integrable (fun z ↦ H z) (ρ.prod ρ) :=
    H.continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact
  have he : (∫ z, H z ∂ρ.prod ρ) = (k:ℝ)⁻¹ * ((k:ℝ)⁻¹ * residualKernelSum M x) := by
    rw [integral_prod _ hi]
    have hgg : (fun z ↦ ∫ y, H (z,y) ∂ρ) = (fun z ↦ g z) := by
      funext z
      simp only [g,KernelMap.action_apply,ContinuousMap.one_apply,mul_one]
    rw [hgg]
    rw [show (∫ z, g z ∂ρ) = (k:ℝ)⁻¹ * ∑ i : Fin k, g (x i) by
      simpa only [Finset.card_univ,Fintype.card_fin,ρ] using
        EmpiricalTypeMarks.empiricalMeasure_integral x Finset.univ g]
    simp_rw [hg]
    rw [← Finset.mul_sum]
    rfl
  unfold empiricalQuadratic
  rw [residual_centeredQuadraticCLM_eq_doubleIntegral]
  simp only [Finset.card_univ,Fintype.card_fin]
  change (k:ℝ) * (∫ z, H z ∂ρ.prod ρ) = _
  rw [he]
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

theorem residualKernelSum_equiv {I J : Type*} [Fintype I] [Fintype J]
    (M : CompactBJRModel S) (e : I ≃ J) (x : J → S) :
    residualKernelSum M (x ∘ e) = residualKernelSum M x := by
  unfold residualKernelSum
  calc
    _ = ∑ i : I, ∑ j : J, residualKernel M (x (e i),x j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp e (fun j ↦ residualKernel M (x (e i),x j))
    _ = _ := Equiv.sum_comp e (fun i ↦ ∑ j : J, residualKernel M (x i,x j))

/-- The exact selected-type coordinate system in the finite factorial
formula and the exact pooled profile coordinate system give the same
residual-kernel double sum, by actual label reindexing. -/
theorem selected_residualKernelSum_eq_pooled_sum {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) :
    residualKernelSum M (selectedTypes hk f (fun i ↦ (p i).1)) =
      residualKernelSum M (pooledTypes k p) := by
  let e : Fin (Fintype.card (SelectedVertices k)) ≃ ↥(selectedUnion (blocksOfPlacement hk f)) :=
    (Fintype.equivFin (SelectedVertices k)).symm.trans (selectedVerticesEquiv hk f)
  have hc : (selectedTypes hk f (fun i ↦ (p i).1)) ∘ e = pooledTypes k p := by
    funext v
    simp only [Function.comp_apply,e,Equiv.trans_apply,selectedTypes,pooledTypes]
    exact congrArg (fun w : SelectedVertices k ↦ (p w.1).1 w.2)
      ((selectedVerticesEquiv hk f).symm_apply_apply ((Fintype.equivFin (SelectedVertices k)).symm v))
  have h := residualKernelSum_equiv M e (selectedTypes hk f (fun i ↦ (p i).1))
  rw [hc] at h
  exact h.symm

/-- Terminal exact pooled-statistic bridge: the quadratic term in the
literal annealed residual is the genuine centered pooled observable already
controlled by the product connected-law concentration theorem. -/
theorem selected_residualKernelSum_eq_totalSize_mul_pooledQuadratic {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hq : 0 < q)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (p : StateFamily (S := S) k) :
    residualKernelSum M (selectedTypes hk f (fun i ↦ (p i).1)) =
      (∑ i, (k i : ℝ)) * pooledQuadratic M hM hq k hk (residualKernel M) p := by
  rw [selected_residualKernelSum_eq_pooled_sum]
  have h := empiricalQuadratic_residualKernel_eq_sum M hM (pooledTypes k p) (pooled_card_pos hq k hk)
  change pooledQuadratic M hM hq k hk (residualKernel M) p = _ at h
  rw [h]
  rw [pooled_card_real]
  have hpos := totalSize_pos hq k hk
  exact (mul_inv_cancel_left₀ hpos.ne' _).symm

theorem selected_critical_quadratic_eq_pooledQuadratic {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hq : 0 < q)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (p : StateFamily (S := S) k) (s₀ : S) :
    let u := selectedTypes hk f (fun i ↦ (p i).1)
    (∑ i, (k i : ℝ)) * totalDegree M u -
      internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f)) u s₀ +
        exposureVariance M u / 2 - (∑ i, (k i : ℝ)) ^ 2 / 2 =
      (∑ i, (k i : ℝ)) * pooledQuadratic M hM hq k hk (residualKernel M) p / 2 +
        diagonalKernelSum M u / 2 := by
  have h := critical_quadratic_internalPair_identity M (selectedUnion (blocksOfPlacement hk f))
    (selectedTypes hk f (fun i ↦ (p i).1)) s₀
  rw [selectedUnion_blocksOfPlacement_card,Nat.cast_sum,
    selected_residualKernelSum_eq_totalSize_mul_pooledQuadratic M hM hq hk f p] at h
  exact h

/-- Actual pooled form of the finite-n logarithmic exponent, before the
bounded-error approximation.  The retained final term is the exact
`K/n` correction to the third cumulant. -/
def pooledCumulantExponent {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (t : ℝ) (hq : 0 < q)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (p : StateFamily (S := S) k) : ℝ :=
  let K : ℝ := ∑ i, (k i : ℝ)
  let u := selectedTypes hk f (fun i ↦ (p i).1)
  K * pooledQuadratic M hM hq k hk (residualKernel M) p / (2 * (n:ℝ)) +
    t * diagonalKernelSum M u / (2 * (n:ℝ)) +
    (t-1) * K * totalDegree M u / (n:ℝ) -
    (t-1) * pairKernelSum M u / (2 * (n:ℝ)) +
    (t^2-1) * exposureVariance M u / (2 * (n:ℝ)) -
    t^2 * K * exposureVariance M u / (2 * (n:ℝ)^2) -
    (t^3 * exposureThirdCumulant M u + K^3) / (6 * (n:ℝ)^2) +
    t^3 * K * exposureThirdCumulant M u / (6 * (n:ℝ)^3)

theorem selectedCumulantExponent_eq_pooledCumulantExponent {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (t : ℝ) (hn : 0 < n) (hq : 0 < q)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (p : StateFamily (S := S) k) (s₀ : S) :
    selectedCumulantExponent M t hk f (selectedTypes hk f (fun i ↦ (p i).1)) s₀ -
      (∑ i, (k i : ℝ))^2 / (2*(n:ℝ)) - (∑ i, (k i : ℝ))^3 / (6*(n:ℝ)^2) =
        pooledCumulantExponent M hM t hq hk f p := by
  have hK : ∑ i, k i ≤ n := by
    have h := Finset.card_le_card ((selectedUnion (blocksOfPlacement hk f)).subset_univ)
    simpa only [selectedUnion_blocksOfPlacement_card,Finset.card_univ,Fintype.card_fin] using h
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hQ := selected_critical_quadratic_eq_pooledQuadratic M hM hq hk f p s₀
  dsimp only at hQ
  have hP := pairKernelSum_eq_internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f))
    (selectedTypes hk f (fun i ↦ (p i).1)) s₀
  have heQ : (∑ i, (k i : ℝ)) * pooledQuadratic M hM hq k hk (residualKernel M) p =
      2 * (∑ i, (k i : ℝ)) * totalDegree M (selectedTypes hk f (fun i ↦ (p i).1)) -
      2 * internalPairWeightOn M (selectedUnion (blocksOfPlacement hk f))
        (selectedTypes hk f (fun i ↦ (p i).1)) s₀ +
      exposureVariance M (selectedTypes hk f (fun i ↦ (p i).1)) - (∑ i, (k i : ℝ))^2 -
      diagonalKernelSum M (selectedTypes hk f (fun i ↦ (p i).1)) := by linarith only [hQ]
  unfold selectedCumulantExponent freshCumulantPolynomial pooledCumulantExponent
  dsimp only
  rw [Nat.cast_sub hK,Nat.cast_sum]
  rw [heQ,hP]
  field_simp
  ring

/-- Terminal finite-n bridge from the actual Q-law observable to the actual
pooled centered quadratic and raw selected exposure cumulants.  The bound
contains neither an assumed residual expansion nor a assumed law limit. -/
theorem log_residualObservable_pooled_cumulant_bound {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (t : ℝ) (ht : 0 ≤ t)
    (hn : 0 < n) (hq : 0 < q) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (p : StateFamily (S := S) k) (s₀ : S)
    (hsmall : t * exposureBound (I := ↥(selectedUnion (blocksOfPlacement hk f))) M /
      (n : ℝ) ≤ 1 / 2) :
    |(Real.log (residualObservable M t hk f s₀ p) -
      (∑ i, (k i : ℝ))^2 / (2*(n:ℝ)) - (∑ i, (k i : ℝ))^3 / (6*(n:ℝ)^2)) -
        pooledCumulantExponent M hM t hq hk f p| ≤
      selectedErrorBound M t hk f (fun i ↦ (p i).2) := by
  rw [← selectedCumulantExponent_eq_pooledCumulantExponent M hM t hn hq hk f p s₀]
  have he : (Real.log (residualObservable M t hk f s₀ p) -
      (∑ i, (k i : ℝ))^2 / (2*(n:ℝ)) - (∑ i, (k i : ℝ))^3 / (6*(n:ℝ)^2)) -
      (selectedCumulantExponent M t hk f (selectedTypes hk f (fun i ↦ (p i).1)) s₀ -
        (∑ i, (k i : ℝ))^2 / (2*(n:ℝ)) - (∑ i, (k i : ℝ))^3 / (6*(n:ℝ)^2)) =
      Real.log (residualObservable M t hk f s₀ p) -
        selectedCumulantExponent M t hk f (selectedTypes hk f (fun i ↦ (p i).1)) s₀ := by ring
  rw [he]
  exact log_selectedResidual_cumulant_bound M t ht hk f (fun i ↦ (p i).2)
    (selectedTypes hk f (fun i ↦ (p i).1)) s₀ hsmall

end PerronWright.FreshTypePerronCentering
