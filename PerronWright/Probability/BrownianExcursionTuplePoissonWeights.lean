import PerronWright.Probability.BrownianExcursionPointProcessLaw

/-!
# Exact full-excursion tuple weights under the actual Poisson marking law

Every order is included. Distinct rational representatives are proved
to represent distinct full components. The genuine conditional kernel
gives the product of the literal full-area Poisson probabilities.
Nonnegative Tonelli gives the whole Brownian source expectation without
assuming any finite moment, Palm formula or excursion density.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical BigOperators NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionTuplePoissonWeights

open BrownianPathLaw BrownianPathReflectionLaw FullHorizonExcursionComponents
open FullHorizonExcursionSection BrownianFullHorizonExcursionAreas
open BrownianExcursionWindowPointMeasure BrownianFullHorizonPoissonMarks

def poissonWeight (A : ℝ≥0) (r : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(A : ℝ)) * (A : ℝ)^r / ((r.factorial : ℕ) : ℝ))

theorem measurable_poissonWeight (r : ℕ) : Measurable (fun A : ℝ≥0 ↦ poissonWeight A r) := by
  exact ENNReal.continuous_ofReal.measurable.comp
    (((NNReal.continuous_coe.measurable.neg.exp).mul
      (NNReal.continuous_coe.measurable.pow_const r)).div_const _)

variable {d : ℕ}

def sourceEvent (lambda : ℝ) (a b : Fin d → ℝ) (e : Fin d → ℚ) (f : Path) : Prop :=
  Function.Injective e ∧ ∀ i,
    Representative (driftedReflectionPath lambda f) (e i) ∧
      lengthValue lambda (e i) f ∈ Icc (a i) (b i)

theorem measurable_sourceEvent (lambda : ℝ) (a b : Fin d → ℝ) (e : Fin d → ℚ) :
    Measurable (sourceEvent lambda a b e) := by
  apply Measurable.and measurable_const
  apply Measurable.forall
  intro i
  apply measurableSet_setOfPred.mp
  exact ((measurableSet_representative (e i)).preimage
    (measurable_driftedReflectionPath lambda)).inter
      ((measurable_lengthValue lambda (e i)) measurableSet_Icc)

theorem sourceEvent_components_distinct {lambda : ℝ} {a b : Fin d → ℝ}
    {e : Fin d → ℚ} {f : Path} (he : sourceEvent lambda a b e f) :
    Pairwise (fun i j ↦ component (driftedReflectionPath lambda f) (e i : ℝ) ≠
      component (driftedReflectionPath lambda f) (e j : ℝ)) := by
  intro i j hij hc
  exact hij (he.1 (representatives_eq_of_component_eq (he.2 i).1 (he.2 j).1 hc))

theorem sourceEvent_components_disjoint {lambda : ℝ} {a b : Fin d → ℝ}
    {e : Fin d → ℚ} {f : Path} (he : sourceEvent lambda a b e f) :
    Pairwise (fun i j ↦ Disjoint (component (driftedReflectionPath lambda f) (e i : ℝ))
      (component (driftedReflectionPath lambda f) (e j : ℝ))) := by
  intro i j hij
  exact components_disjoint_of_ne (sourceEvent_components_distinct he hij)

theorem sourceEvent_components_bounded {lambda : ℝ} {a b : Fin d → ℝ}
    {e : Fin d → ℚ} {f : Path} (he : sourceEvent lambda a b e f)
    (ha : ∀ i, 0 < a i) (i : Fin d) :
    BddAbove (component (driftedReflectionPath lambda f) (e i : ℝ)) := by
  by_contra hb
  have hr : rightEndpoint (e i : ℝ) (driftedReflectionPath lambda f) = 0 := by
    simp only [rightEndpoint,if_pos (he.2 i).1.1,Real.sSup_of_not_bddAbove hb]
  have hl := FullHorizonExcursionEndpoints.leftEndpoint_nonneg (e i : ℝ) (driftedReflectionPath lambda f)
  have hp : 0 < length (e i : ℝ) (driftedReflectionPath lambda f) :=
    (ha i).trans_le (he.2 i).2.1
  rw [length,hr] at hp
  linarith

theorem sourceEvent_full_area_eq_integral {lambda : ℝ} {a b : Fin d → ℝ}
    {e : Fin d → ℚ} {f : Path} (he : sourceEvent lambda a b e f)
    (ha : ∀ i, 0 < a i) (i : Fin d) :
    (excursionArea (e i : ℝ) lambda f : ℝ) =
      ∫ s in component (driftedReflectionPath lambda f) (e i : ℝ),
        BrownianWindowExcursions.realEval (driftedReflectionPath lambda f) s :=
  excursionArea_eq_component_integral (sourceEvent_components_bounded he ha i)

def contribution (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (e : Fin d → ℚ) (p : Path × (ℕ → ℕ)) : ℝ≥0∞ :=
  if sourceEvent lambda a b e p.1 ∧ (∀ i, rationalCount p.2 (e i) = r i) then 1 else 0

theorem measurable_contribution (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (e : Fin d → ℚ) : Measurable (contribution lambda a b r e) := by
  apply Measurable.ite _ measurable_const measurable_const
  apply Measurable.setOf
  exact ((measurable_sourceEvent lambda a b e).comp measurable_fst).and
    (Measurable.forall (fun i ↦
      (((measurable_pi_apply (Encodable.encode (e i))).comp measurable_snd).eq measurable_const)))

def weight (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (e : Fin d → ℚ) (f : Path) : ℝ≥0∞ :=
  if sourceEvent lambda a b e f then
    ∏ i, poissonWeight (retainedArea (e i) lambda f) (r i) else 0

set_option backward.isDefEq.respectTransparency true in
theorem measurable_weight (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (e : Fin d → ℚ) : Measurable (weight lambda a b r e) := by
  apply Measurable.ite (measurable_sourceEvent lambda a b e).setOf _ measurable_const
  apply Finset.measurable_prod
  intro i _
  have hm := (measurable_retainedArea_all_parameters (e i)).comp
    (f := fun f : Path ↦ (lambda,f))
    ((measurable_const : Measurable (fun _ : Path ↦ lambda)).prodMk measurable_id)
  have hA : Measurable (fun f : Path ↦ retainedArea (e i) lambda f) := by
    simpa only [Function.comp_def] using hm
  exact (measurable_poissonWeight (r i)).comp hA

theorem weight_eq_full_area (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (e : Fin d → ℚ) (f : Path) :
    weight lambda a b r e f = if sourceEvent lambda a b e f then
      ∏ i, poissonWeight (excursionArea (e i : ℝ) lambda f) (r i) else 0 := by
  by_cases hs : sourceEvent lambda a b e f
  · simp only [weight,if_pos hs]
    apply Finset.prod_congr rfl
    intro i _
    rw [retainedArea,if_pos (hs.2 i).1]
  · simp only [weight,if_neg hs]

/-- Exact conditional probability for a genuine injective tuple, derived
from the actual countable product kernel's independence. -/
theorem markLaw_tuple_event (lambda : ℝ) (f : Path) (e : Fin d → ℚ)
    (he : Function.Injective e) (r : Fin d → ℕ) :
    markLaw lambda f {m | ∀ i, rationalCount m (e i) = r i} =
      ∏ i, poissonWeight (retainedArea (e i) lambda f) (r i) := by
  have hi := (iIndepFun.precomp he (markLaw_rationalCounts_independent lambda f)).measure_inter_preimage_eq_mul
    Finset.univ (sets := fun i ↦ {r i}) (fun i _ ↦ measurableSet_singleton (r i))
  have hs : {m : ℕ → ℕ | ∀ i, rationalCount m (e i) = r i} =
      ⋂ i ∈ (Finset.univ : Finset (Fin d)), (fun m : ℕ → ℕ ↦ rationalCount m (e i)) ⁻¹' {r i} := by
    ext m
    simp
  rw [hs,hi]
  apply Finset.prod_congr rfl
  intro i _
  calc
    _ = poissonMeasure (retainedArea (e i) lambda f) {r i} := by
      convert (markLaw_hasLaw_rationalCount lambda f (e i)).measure_eq
        (measurableSet_singleton (r i)) using 1
      · congr 1
      · congr 1
    _ = _ := poissonMeasure_singleton _ _

theorem conditional_contribution (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (e : Fin d → ℚ) (f : Path) :
    (∫⁻ m, contribution lambda a b r e (f,m) ∂markLaw lambda f) =
      weight lambda a b r e f := by
  by_cases hs : sourceEvent lambda a b e f
  · let A : Set (ℕ → ℕ) := {m | ∀ i, rationalCount m (e i) = r i}
    have hA : MeasurableSet A :=
      (Measurable.forall (fun i ↦ (measurable_pi_apply (Encodable.encode (e i))).eq measurable_const)).setOf
    have hc : (fun m ↦ contribution lambda a b r e (f,m)) = A.indicator 1 := by
      funext m
      simp [contribution,A,hs,Set.indicator_apply]
    rw [hc,lintegral_indicator_one hA,markLaw_tuple_event lambda f e hs.1 r]
    exact (if_pos hs).symm
  · simp [contribution,weight,hs]

def statistic (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (p : Path × (ℕ → ℕ)) : ℝ≥0∞ :=
  ∑' e : Fin d → ℚ, contribution lambda a b r e p

theorem measurable_statistic (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ) :
    Measurable (statistic lambda a b r) :=
  Measurable.tsum (fun e ↦ measurable_contribution lambda a b r e)

theorem conditional_statistic (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ) (f : Path) :
    (∫⁻ m, statistic lambda a b r (f,m) ∂markLaw lambda f) =
      ∑' e : Fin d → ℚ, weight lambda a b r e f := by
  change (∫⁻ m, ∑' e : Fin d → ℚ, contribution lambda a b r e (f,m) ∂markLaw lambda f) = _
  rw [lintegral_tsum]
  · exact tsum_congr (fun e ↦ conditional_contribution lambda a b r e f)
  · intro e
    exact ((measurable_contribution lambda a b r e).comp (measurable_const.prodMk measurable_id)).aemeasurable

/-- Every order, actual Brownian source, and literal complete excursion
areas. Both sides are nonnegative extended integrals; no finite moment
or normalization is an input. -/
theorem joint_expectation_eq_source_weights (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ) :
    (∫⁻ p, statistic lambda a b r p ∂pathJointLaw lambda) =
      ∫⁻ f, ∑' e : Fin d → ℚ, weight lambda a b r e f ∂pathLaw := by
  rw [pathJointLaw,CountablePoissonKernel.jointLaw,
    Measure.lintegral_compProd (measurable_statistic lambda a b r)]
  apply lintegral_congr
  intro f
  exact conditional_statistic lambda a b r f

theorem joint_expectation_eq_complete_area_weights (lambda : ℝ)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) :
    (∫⁻ p, statistic lambda a b r p ∂pathJointLaw lambda) =
      ∫⁻ f, ∑' e : Fin d → ℚ, if sourceEvent lambda a b e f then
        ∏ i, poissonWeight (excursionArea (e i : ℝ) lambda f) (r i) else 0 ∂pathLaw := by
  rw [joint_expectation_eq_source_weights]
  apply lintegral_congr
  intro f
  exact tsum_congr (fun e ↦ weight_eq_full_area lambda a b r e f)

def actualStatistic (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ)
    (p : (ℕ → ℝ) × (ℕ → ℕ)) : ℝ≥0∞ := statistic lambda a b r (measurablePath p.1,p.2)

theorem measurable_actualStatistic (lambda : ℝ) (a b : Fin d → ℝ) (r : Fin d → ℕ) :
    Measurable (actualStatistic lambda a b r) :=
  (measurable_statistic lambda a b r).comp
    ((measurable_measurablePath.comp measurable_fst).prodMk measurable_snd)

theorem actual_joint_expectation_eq_source_weights (lambda : ℝ)
    (a b : Fin d → ℝ) (r : Fin d → ℕ) :
    (∫⁻ p, actualStatistic lambda a b r p ∂actualJointLaw lambda) =
      ∫⁻ x, ∑' e : Fin d → ℚ, weight lambda a b r e (measurablePath x)
        ∂BrownianGaussianSkeleton.rationalLaw := by
  have hm : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ (measurablePath p.1,p.2)) :=
    (measurable_measurablePath.comp measurable_fst).prodMk measurable_snd
  calc
    _ = ∫⁻ p, statistic lambda a b r p ∂pathJointLaw lambda := by
      rw [← BrownianFullHorizonMarkJointLaw.actualJointLaw_map_to_path lambda,
        lintegral_map (measurable_statistic lambda a b r) hm]
      rfl
    _ = ∫⁻ f, ∑' e : Fin d → ℚ, weight lambda a b r e f ∂pathLaw :=
      joint_expectation_eq_source_weights lambda a b r
    _ = _ := by
      rw [pathLaw,lintegral_map (Measurable.tsum (fun e ↦ measurable_weight lambda a b r e))
        measurable_measurablePath]

end PerronWright.BrownianExcursionTuplePoissonWeights
