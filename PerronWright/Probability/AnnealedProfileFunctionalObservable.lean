import PerronWright.Probability.AnnealedProfileFunctionalFiniteError
import PerronWright.Probability.AnnealedResidualCriticalError

/-!
# Support and measurability of the actual annealed residual observable

The graph eligibility assertion is derived from the literal connected
law density.  It is not a supplied sampling-support assumption.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedProfileFunctionalObservable

open AnnealedGraph ExactFactorialExpectation SelectedConfiguration AnnealedResidualFixedBlock
  FreshTypeAveraging FreshTypeCumulantExpansion FreshTypePerronCentering
  AnnealedResidualCumulantExpansion AnnealedTupleResidualConnectedLawCoordinates
  AnnealedTupleResidualConnectedLawFormula AnnealedTupleResidualConnectedLawGraphTuple
  AnnealedTupleResidualConnectedLawWeights AnnealedTupleResidualCounting
  AnnealedTupleResidualPatternFormula
  AnnealedProfileFunctionalContinuous AnnealedProfileFunctionalExponent
  AnnealedProfileFunctionalResidual AnnealedProfileFunctionalFiniteError
  AnnealedProfileFunctionalL1 AnnealedResidualCriticalError
  ProfileFiniteCollection ProjectiveFiniteCollection ProjectiveKernelClosure
  ProfileCollectionScaleMatched ProfileSquareMoment BoundedConcentrationTransfer
  EmpiricalTypeMarks EmpiricalMarkConcentration

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

theorem connectedLaw_eligible_ae (M : CompactBJRModel S) (g : C(S,ℝ)) (k r : ℕ)
    (hC : 0 < M.fieldConnectedWeight g k r) :
    ∀ᵐ p ∂ConnectedTypeLaw.law M g k r hC, ConnectedTypeLaw.Eligible r p.2 := by
  unfold ConnectedTypeLaw.law
  let d := fun p : ConnectedTypeLaw.State S k ↦
    ENNReal.ofReal (ConnectedTypeLaw.weight M g k r p / M.fieldConnectedWeight g k r)
  have hd : Measurable d := ENNReal.measurable_ofReal.comp
    ((ConnectedTypeLaw.weight_measurable M g k r).div_const _)
  change ∀ᵐ p ∂((typeLaw M k).prod Measure.count).withDensity d, _
  apply (ae_withDensity_iff hd).mpr
  apply Eventually.of_forall
  intro p hp
  by_contra he
  dsimp only [d] at hp
  simp only [ConnectedTypeLaw.weight,if_neg he,zero_div,ENNReal.ofReal_zero,ne_eq,not_true_eq_false] at hp

theorem productLaw_eligible_ae {q : ℕ} (M : CompactBJRModel S)
    (k r : Fin q → ℕ) (g : Fin q → C(S,ℝ))
    (hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i)) :
    ∀ᵐ p ∂productLaw M k r g hC, ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2 := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun i ↦ ConnectedTypeLaw.law M (g i) (k i) (r i) (hC i)) i).quasiMeasurePreserving.ae
    (connectedLaw_eligible_ae M (g i) (k i) (r i) (hC i))

theorem normalizedOdds_measurable : Measurable normalizedOdds := by
  unfold normalizedOdds
  exact Measurable.ite (measurableSet_singleton (0:ℝ)) measurable_const
    ((measurable_id.exp.sub measurable_const).div measurable_id)

theorem totalDegree_continuous {I : Type*} [Fintype I] (M : CompactBJRModel S) :
    Continuous (totalDegree (I := I) M) := by
  unfold totalDegree
  exact continuous_finsetSum _ (fun i _ ↦ M.degreeFunction.continuous.comp (continuous_apply i))

theorem selectedResidual_measurable {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i)
    (f : Placements n k) (H : GraphTuple k) (s₀ : S) :
    Measurable (fun u : ↥(selectedUnion (blocksOfPlacement hk f)) → S ↦
      selectedResidual M t hk f H u s₀) := by
  unfold selectedResidual
  apply Measurable.mul
  · apply Measurable.mul
    · exact ((measurable_const.mul (totalDegree_continuous M).measurable).sub
        ((measurable_const.mul (internalPairWeightOn_continuous M _ s₀).measurable).div_const _)).exp
    · exact (isolationFactor_continuous M t n).measurable.pow_const _
  · apply Finset.measurable_prod
    intro e _
    exact normalizedOdds_measurable.comp
      (((M.edgeFactor_continuous t e).comp (combineTypes_continuous _ s₀)).measurable.div_const _)

theorem residualObservable_measurable {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (t : ℝ) (hk : ∀ i, 0 < k i)
    (f : Placements n k) (s₀ : S) : Measurable (residualObservable M t hk f s₀) := by
  let e := dependentPiProd (fun i : Fin q ↦ Fin (k i) → S)
    (fun i : Fin q ↦ SimpleGraph (Fin (k i)))
  have hm : Measurable (fun p : ((i : Fin q) → Fin (k i) → S) × GraphTuple k ↦
      residualObservable M t hk f s₀ (e.symm p)) := by
    apply measurable_from_prod_countable_left
    intro H
    exact (selectedResidual_measurable M t hk f H s₀).comp (selectedTypes_continuous hk f).measurable
  have hh := hm.comp e.measurable
  change Measurable (fun p ↦ residualObservable M t hk f s₀ (e.symm (e p))) at hh
  simpa only [MeasurableEquiv.symm_apply_apply] using hh

def perronExponent (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda : ℝ) (n K : ℕ) : ℝ :=
  let t := CriticalScaling.time lambda n
  M.alpha hM/2*((t-1)*(K:ℝ)^2/(n:ℝ)) - M.beta hM/6*((K:ℝ)^3/(n:ℝ)^2)

def normalizedResidualObservable {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (p : StateFamily (S := S) k) : ℝ :=
  Real.exp (-((∑ i,(k i:ℝ))^2/(2*(n:ℝ))) -
    (∑ i,(k i:ℝ))^3/(6*(n:ℝ)^2) - perronExponent M hM lambda n (∑ i,k i)) *
      residualObservable M (CriticalScaling.time lambda n) hk f s₀ p

theorem normalizedResidualObservable_measurable {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S) :
    Measurable (normalizedResidualObservable M hM lambda hk f s₀) :=
  (residualObservable_measurable M _ hk f s₀).const_mul _

theorem normalizedResidualObservable_eq_exp_log {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S) (p : StateFamily (S := S) k) :
    normalizedResidualObservable M hM lambda hk f s₀ p =
      Real.exp (Real.log (residualObservable M (CriticalScaling.time lambda n) hk f s₀ p) -
        (∑ i,(k i:ℝ))^2/(2*(n:ℝ)) - (∑ i,(k i:ℝ))^3/(6*(n:ℝ)^2) -
          perronExponent M hM lambda n (∑ i,k i)) := by
  have hp := selectedResidual_pos M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) hk f (fun i ↦ (p i).2)
    (selectedTypes hk f (fun i ↦ (p i).1)) s₀
  change 0 < residualObservable M (CriticalScaling.time lambda n) hk f s₀ p at hp
  change _ * residualObservable M (CriticalScaling.time lambda n) hk f s₀ p = _
  calc
    _ = Real.exp (-((∑ i,(k i:ℝ))^2/(2*(n:ℝ))) -
        (∑ i,(k i:ℝ))^3/(6*(n:ℝ)^2) - perronExponent M hM lambda n (∑ i,k i)) *
          Real.exp (Real.log (residualObservable M (CriticalScaling.time lambda n) hk f s₀ p)) := by
      rw [Real.exp_log hp]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Pointwise comparison on eligible graphs, with the literal fresh/odds
error and the explicit diagonal/cumulant envelope kept separate. -/
theorem normalizedResidualObservable_exponent_bound {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda T : ℝ)
    (hn : 0 < n) (hq : 0 < q) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (s₀ : S) (p : StateFamily (S := S) k) {R : ℕ}
    (hT : CriticalScaling.time lambda n ≤ T)
    (hr : ∀ i, r i ≤ R) (hp : ∀ i, ConnectedTypeLaw.Eligible (r i) (p i).2)
    (hsmall : CriticalScaling.time lambda n *
      exposureBound (I := ↥(selectedUnion (blocksOfPlacement hk f))) M / (n:ℝ) ≤ 1/2) :
    |(Real.log (residualObservable M (CriticalScaling.time lambda n) hk f s₀ p) -
      (∑ i,(k i:ℝ))^2/(2*(n:ℝ)) - (∑ i,(k i:ℝ))^3/(6*(n:ℝ)^2) -
        perronExponent M hM lambda n (∑ i,k i)) -
          centeredProfileExponent M hM lambda n hq k hk p| ≤
      finiteCorrectionEnvelope M (CriticalScaling.time lambda n) n (∑ i,k i) +
        envelope n (∑ i,k i) q R (T*‖M.kernel.toContinuousMap‖) := by
  have he := log_residualObservable_pooled_cumulant_bound M hM (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) hn hq hk f p s₀ hsmall
  have hb := selectedErrorBound_le_envelope M (CriticalScaling.time lambda n) T
    (CriticalScaling.time_nonneg lambda n) hT hk f (fun i ↦ (p i).2) hp hr
  have hc := pooledCumulantExponent_eq_centered_add_finiteCorrection M hM lambda hq hk f p
  dsimp only at hc
  have hident : (Real.log (residualObservable M (CriticalScaling.time lambda n) hk f s₀ p) -
      (∑ i,(k i:ℝ))^2/(2*(n:ℝ)) - (∑ i,(k i:ℝ))^3/(6*(n:ℝ)^2) -
        perronExponent M hM lambda n (∑ i,k i)) -
          centeredProfileExponent M hM lambda n hq k hk p =
      finiteCorrection M (CriticalScaling.time lambda n) n hq k hk p +
        ((Real.log (residualObservable M (CriticalScaling.time lambda n) hk f s₀ p) -
          (∑ i,(k i:ℝ))^2/(2*(n:ℝ)) - (∑ i,(k i:ℝ))^3/(6*(n:ℝ)^2)) -
            pooledCumulantExponent M hM (CriticalScaling.time lambda n) hq hk f p) := by
    unfold perronExponent
    dsimp only
    rw [Nat.cast_sum]
    linarith only [hc]
  rw [hident]
  exact (abs_add_le _ _).trans (add_le_add (finiteCorrection_bound M _ n hq k hk p) (he.trans hb))

/-- Integrability of the centered profile exponential at every finite
size follows from the actual QP moment and the compact profile bound. -/
theorem centeredProfileExponent_exp_integrable {q : ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (hQP : M.QP)
    (lambda : ℝ) (n : ℕ) (hq : 0 < q) (k r : Fin q → ℕ) (hk : ∀ i, 0 < k i)
    (g : Fin q → C(S,ℝ)) (hC : ∀ i, 0 < M.fieldConnectedWeight (g i) (k i) (r i)) :
    Integrable (fun p ↦ Real.exp (centeredProfileExponent M hM lambda n hq k hk p))
      (productLaw M k r g hC) := by
  let μ := productLaw M k r g hC
  let γ : ℝ := (∑ i,(k i:ℝ))/(2*(n:ℝ))
  let Q := fun p : StateFamily (S := S) k ↦
    γ * pooledQuadratic M hM hq k hk (residualKernel M) p
  let z := residualParameter lambda n (∑ i,k i)
  let Z := actualProfileRemainder M hM lambda n hq k hk
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  obtain ⟨a,f,hrep,he⟩ := residualKernel_hasRepresentation M hQP
  have hQ : Measurable Q := by
    dsimp only [Q]
    rw [he]
    exact (pooledQuadratic_measurable_of_representation M hM hq k hk hrep).const_mul _
  have hZ : Measurable Z := pooled_jointContinuousFunctional_measurable hq k hk z
    (profileRemainder M hM) (profileRemainder_joint_continuous M hM)
  obtain ⟨B,hB,hbound⟩ := jointContinuousFunctional_bound (fun _ : ℕ ↦ z)
    tendsto_const_nhds (perronMark M hM) (profileRemainder M hM) (profileRemainder_joint_continuous M hM)
  have hb (p : StateFamily (S := S) k) : |Z p| ≤ B + |profileRemainder M hM z (perronMark M hM)| := by
    have hh := hbound 0 (pooledMark hq k hk p)
    have ht := abs_add_le (Z p-profileRemainder M hM z (perronMark M hM))
      (profileRemainder M hM z (perronMark M hM))
    simp only [sub_add_cancel] at ht
    exact ht.trans (add_le_add hh le_rfl)
  have hi : Integrable (fun p ↦ Real.exp |Q p|) μ := by
    have hh := integrable_exp_pooledQuadratic M hM hq k r hk g hC hrep γ hγ
    rw [← he] at hh
    simpa only [Q,abs_mul,abs_of_nonneg hγ] using hh
  exact exp_add_integrable μ Q Z hQ hZ hb hi

theorem normalizedResidualObservable_integrable {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ)
    (hn : 0 < n) (ht : 0 < CriticalScaling.time lambda n)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n)) (k i) (r i)) :
    Integrable (normalizedResidualObservable M hM lambda hk f s₀)
      (productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hC) :=
  (residualObservable_integrable_connectedLaw M (CriticalScaling.time lambda n) ht hn k r hk f s₀ hC).const_mul _

end PerronWright.AnnealedProfileFunctionalObservable
