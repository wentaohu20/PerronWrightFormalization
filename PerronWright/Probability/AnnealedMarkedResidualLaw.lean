import PerronWright.Probability.AnnealedProfileFunctionalAsymptotic

/-!
# Genuine residual-weighted connected laws

The density is the literal normalized residual and the normalization is
its actual expectation.  Positivity, integrability and total mass are
proved from the model, including a zero-time finite prefix.
-/

open MeasureTheory Filter Topology
open scoped Topology Real BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.AnnealedMarkedResidualLaw

open AnnealedGraph FreshTypeAveraging AnnealedTupleResidualCounting
  AnnealedTupleResidualConnectedLawCoordinates AnnealedTupleResidualConnectedLawWeights
  AnnealedProfileFunctionalObservable AnnealedResidualCumulantExpansion
  ProfileFiniteCollection

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

theorem residualObservable_zero {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hk : ∀ i, 0 < k i) (f : Placements n k)
    (s₀ : S) (p : StateFamily (S := S) k) : residualObservable M 0 hk f s₀ p = 1 := by
  have he (x : Fin n → S) (e : Sym2 (Fin n)) : M.edgeFactor 0 x e = 0 := by
    induction e using Sym2.inductionOn with
    | _ a b => simp only [CompactBJRModel.edgeFactor_mk,zero_mul]
  have ha (u : ↥(ExactFactorialExpectation.selectedUnion
      (AnnealedTupleResidualPatternFormula.blocksOfPlacement hk f)) → S) : isolationFactor M 0 n u = 1 := by
    unfold isolationFactor freshAbsence
    simp only [zero_mul,neg_zero,zero_div,Real.exp_zero,integral_const,
      probReal_univ,smul_eq_mul,one_mul]
  have hO : normalizedOdds 0 = 1 := by rw [normalizedOdds,if_pos rfl]
  simp only [residualObservable,selectedResidual,zero_mul,zero_div,sub_zero,Real.exp_zero,
    he,ha,hO,Finset.prod_const_one,one_pow,one_mul]

theorem normalizedResidualObservable_pos {n q : ℕ} {k : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S) (p : StateFamily (S := S) k) :
    0 < normalizedResidualObservable M hM lambda hk f s₀ p := by
  unfold normalizedResidualObservable
  exact mul_pos (Real.exp_pos _) (selectedResidual_pos M _ (CriticalScaling.time_nonneg lambda n)
    hk f (fun i ↦ (p i).2) (selectedTypes hk f (fun i ↦ (p i).1)) s₀)

/-- The actual residual is integrable also when clipping makes the time
zero: then it is the constant one, rather than a division limit. -/
theorem normalizedResidualObservable_integrable_alltime {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ) (hn : 0 < n)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n)) (k i) (r i)) :
    Integrable (normalizedResidualObservable M hM lambda hk f s₀)
      (productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hC) := by
  by_cases ht : 0 < CriticalScaling.time lambda n
  · exact normalizedResidualObservable_integrable M hM lambda hn ht hk f s₀ hC
  · have ht0 : CriticalScaling.time lambda n = 0 :=
      le_antisymm (le_of_not_gt ht) (CriticalScaling.time_nonneg lambda n)
    have he : normalizedResidualObservable M hM lambda hk f s₀ =
        fun _ : StateFamily (S := S) k ↦ Real.exp (-((∑ i,(k i:ℝ))^2/(2*(n:ℝ))) -
          (∑ i,(k i:ℝ))^3/(6*(n:ℝ)^2) - perronExponent M hM lambda n (∑ i,k i)) := by
      funext p
      simp only [normalizedResidualObservable,ht0,residualObservable_zero,mul_one]
    rw [he]
    exact integrable_const _

def weightedMeasure {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n)) (k i) (r i)) :
    Measure (StateFamily (S := S) k) :=
  (productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hC).withDensity
    (fun p ↦ ENNReal.ofReal (normalizedResidualObservable M hM lambda hk f s₀ p))

theorem densityMeasure_isFinite {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → ℝ) (hF : Integrable F μ) (hn : ∀ ω, 0 ≤ F ω) :
    IsFiniteMeasure (μ.withDensity (fun ω ↦ ENNReal.ofReal (F ω))) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hF (Eventually.of_forall hn)]
  exact ENNReal.ofReal_ne_top

theorem weightedMeasure_isFinite {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ) (hn : 0 < n)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n)) (k i) (r i)) :
    IsFiniteMeasure (weightedMeasure M hM lambda hk f s₀ hC) :=
  densityMeasure_isFinite _ _ (normalizedResidualObservable_integrable_alltime M hM lambda hn hk f s₀ hC)
    (fun p ↦ (normalizedResidualObservable_pos M hM lambda hk f s₀ p).le)

theorem residualExpectation_pos {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ) (hn : 0 < n)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n)) (k i) (r i)) :
    0 < ∫ p, normalizedResidualObservable M hM lambda hk f s₀ p
      ∂productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hC := by
  rw [integral_pos_iff_support_of_nonneg
    (fun p ↦ (normalizedResidualObservable_pos M hM lambda hk f s₀ p).le)
    (normalizedResidualObservable_integrable_alltime M hM lambda hn hk f s₀ hC)]
  have hs : Function.support (normalizedResidualObservable M hM lambda hk f s₀) = Set.univ := by
    ext p
    change (normalizedResidualObservable M hM lambda hk f s₀ p ≠ 0) ↔ True
    exact iff_true_intro (normalizedResidualObservable_pos M hM lambda hk f s₀ p).ne'
  rw [hs,measure_univ]
  exact zero_lt_one

def weightedLaw {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ) (hn : 0 < n)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n)) (k i) (r i)) :
    ProbabilityMeasure (StateFamily (S := S) k) := by
  let μ := productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hC
  let F := normalizedResidualObservable M hM lambda hk f s₀
  let Z := ∫ p, F p ∂μ
  have hZ : 0 < Z := residualExpectation_pos M hM lambda hn hk f s₀ hC
  refine ⟨μ.withDensity (fun p ↦ ENNReal.ofReal (F p / Z)),?_⟩
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((normalizedResidualObservable_integrable_alltime M hM lambda hn hk f s₀ hC).div_const Z)
      (Eventually.of_forall (fun p ↦ div_nonneg (normalizedResidualObservable_pos M hM lambda hk f s₀ p).le hZ.le)),
    integral_div,div_self hZ.ne']
  norm_num

/-- Literal expectation under the genuine normalized residual law. -/
theorem weightedLaw_integral {n q : ℕ} {k r : Fin q → ℕ}
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ) (hn : 0 < n)
    (hk : ∀ i, 0 < k i) (f : Placements n k) (s₀ : S)
    (hC : ∀ i, 0 < M.fieldConnectedWeight (M.scalarField (CriticalScaling.time lambda n)) (k i) (r i))
    (G : StateFamily (S := S) k → ℝ) :
    (∫ p, G p ∂(weightedLaw M hM lambda hn hk f s₀ hC : Measure _)) =
      (∫ p, normalizedResidualObservable M hM lambda hk f s₀ p * G p
        ∂productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hC) /
      (∫ p, normalizedResidualObservable M hM lambda hk f s₀ p
        ∂productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hC) := by
  let μ := productLaw M k r (fun _ ↦ M.scalarField (CriticalScaling.time lambda n)) hC
  let F := normalizedResidualObservable M hM lambda hk f s₀
  let Z := ∫ p, F p ∂μ
  have hZ : 0 < Z := residualExpectation_pos M hM lambda hn hk f s₀ hC
  change (∫ p, G p ∂μ.withDensity (fun p ↦ ENNReal.ofReal (F p/Z))) = _
  have hd : Measurable (fun p ↦ ENNReal.ofReal (F p/Z)) := ENNReal.measurable_ofReal.comp
    ((normalizedResidualObservable_measurable M hM lambda hk f s₀).div_const Z)
  rw [integral_withDensity_eq_integral_toReal_smul hd
    (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  have hp (p : StateFamily (S := S) k) : 0 ≤ F p/Z :=
    div_nonneg (normalizedResidualObservable_pos M hM lambda hk f s₀ p).le hZ.le
  simp_rw [ENNReal.toReal_ofReal (hp _),smul_eq_mul,div_mul_eq_mul_div]
  rw [integral_div]

end PerronWright.AnnealedMarkedResidualLaw
