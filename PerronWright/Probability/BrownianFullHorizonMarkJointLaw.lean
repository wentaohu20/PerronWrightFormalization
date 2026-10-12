import PerronWright.Probability.BrownianFullHorizonPoissonMarks

/-!
# Full-horizon marks jointly with the actual Brownian source

The continuous-path and original Gaussian-source constructions agree
exactly after pushforward. The actual Brownian driver is preserved, and
the untruncated component and area identities hold under this joint law.
The marked interval data are genuine measurable pushforwards, not a
supplied excursion or conditional marking law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

namespace PerronWright.BrownianFullHorizonMarkJointLaw

open BrownianPathLaw BrownianGaussianSkeleton BrownianPathReflectionLaw
open BrownianFullHorizonPoissonMarks BrownianFullHorizonExcursions
open BrownianFullHorizonExcursionAreas FullHorizonExcursionComponents
open FullHorizonExcursionEndpoints FullHorizonExcursionSection
open BrownianActualWindowExcursions (actualPath)

theorem actualJointLaw_map_to_path (lambda : ℝ) :
    (actualJointLaw lambda).map
      (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ (measurablePath p.1,p.2)) =
      pathJointLaw lambda := by
  have hm : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦
      (measurablePath p.1,p.2)) :=
    (measurable_measurablePath.comp measurable_fst).prodMk measurable_snd
  ext A hA
  rw [Measure.map_apply hm hA,actualJointLaw,CountablePoissonKernel.jointLaw,
    Measure.compProd_apply (hA.preimage hm),pathJointLaw,
    CountablePoissonKernel.jointLaw,Measure.compProd_apply hA,pathLaw,
    lintegral_map (Kernel.measurable_kernel_prodMk_left
      (κ := CountablePoissonKernel.rateKernel (naturalRates lambda)
        (measurable_naturalRates lambda)) hA) measurable_measurablePath]
  apply lintegral_congr
  intro x
  rfl

theorem hasLaw_actual_path_mark_pair (lambda : ℝ) :
    HasLaw (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦ (measurablePath p.1,p.2))
      (pathJointLaw lambda) (actualJointLaw lambda) :=
  ⟨((measurable_measurablePath.comp measurable_fst).prodMk measurable_snd).aemeasurable,
    actualJointLaw_map_to_path lambda⟩

theorem actualJointLaw_hasLaw_finite (lambda : ℝ) (I : Finset ℝ≥0) :
    HasLaw (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦
      I.restrict (fun t ↦ measurablePath p.1 t))
      (BrownianReal.projectiveFamily I) (actualJointLaw lambda) :=
  (pathJointLaw_hasLaw_finite lambda I).fun_comp
    (hasLaw_actual_path_mark_pair lambda)

theorem isBrownian_actualJointLaw (lambda : ℝ) :
    IsBrownianReal (fun t (p : (ℕ → ℝ) × (ℕ → ℕ)) ↦ measurablePath p.1 t)
      (actualJointLaw lambda) :=
  ⟨⟨actualJointLaw_hasLaw_finite lambda⟩,
    Eventually.of_forall (fun p ↦ continuous_path (measurablePath p.1))⟩

/-- Lifting a proved source almost-sure fact does not change the source law. -/
theorem ae_actualJointLaw_of_ae_source (lambda : ℝ) {P : (ℕ → ℝ) → Prop}
    (hP : ∀ᵐ x ∂rationalLaw, P x) :
    ∀ᵐ p ∂actualJointLaw lambda, P p.1 := by
  apply ae_of_ae_map (μ := actualJointLaw lambda)
    (f := (Prod.fst : (ℕ → ℝ) × (ℕ → ℕ) → (ℕ → ℝ)))
    (p := P) measurable_fst.aemeasurable
  rw [actualJointLaw_source]
  exact hP

theorem ae_all_actual_reflection_eq_under_joint (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda, ∀ c : ℝ, ∀ t : ℝ≥0,
      driftedReflectionPath c (measurablePath p.1) t =
        BrownianParabolicReflection.reflection c t p.1 :=
  ae_actualJointLaw_of_ae_source lambda ae_all_actual_driftedReflection_eq

theorem ae_all_full_components_bddAbove_under_joint (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda, ∀ c q : ℝ,
      BddAbove (component (actualPath c p.1) q) :=
  ae_actualJointLaw_of_ae_source lambda ae_all_actual_components_bddAbove

theorem ae_all_full_component_area_eq_raw_under_joint (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda, ∀ c q : ℝ,
      (excursionArea q c (measurablePath p.1) : ℝ) =
        ∫ s in connectedComponentIn (rawPositiveSet c p.1) q,
          BrownianParabolicReflection.reflection c (Real.toNNReal s) p.1 :=
  ae_actualJointLaw_of_ae_source lambda ae_all_excursionArea_eq_raw

theorem ae_all_retainedArea_pos_iff_under_joint (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda, ∀ c : ℝ, ∀ q : ℚ,
      0 < retainedArea q c (measurablePath p.1) ↔
        Representative (actualPath c p.1) q :=
  ae_actualJointLaw_of_ae_source lambda ae_all_retainedArea_pos_iff

/-- Every active interval is the actual finite, zero-ended excursion,
including under the jointly sampled full-horizon mark construction. -/
theorem ae_all_actual_excursion_properties_under_joint (lambda : ℝ) :
    ∀ᵐ p ∂actualJointLaw lambda, ∀ c q : ℝ,
      q ∈ positiveSet (actualPath c p.1) →
        component (actualPath c p.1) q =
          Ioo (leftEndpoint q (actualPath c p.1)) (rightEndpoint q (actualPath c p.1)) ∧
        0 ≤ leftEndpoint q (actualPath c p.1) ∧
        leftEndpoint q (actualPath c p.1) < q ∧ q < rightEndpoint q (actualPath c p.1) ∧
        BrownianWindowExcursions.realEval (actualPath c p.1)
          (leftEndpoint q (actualPath c p.1)) = 0 ∧
        BrownianWindowExcursions.realEval (actualPath c p.1)
          (rightEndpoint q (actualPath c p.1)) = 0 ∧
        0 < length q (actualPath c p.1) :=
  ae_actualJointLaw_of_ae_source lambda ae_all_actual_excursion_properties

def markedIntervalData (lambda : ℝ) (p : Path × (ℕ → ℕ))
    (q : ℚ) : (Bool × (ℝ × ℝ)) × ℕ :=
  (intervalData (driftedReflectionPath lambda p.1) q,rationalCount p.2 q)

theorem measurable_markedIntervalData (lambda : ℝ) :
    Measurable (markedIntervalData lambda) := by
  apply measurable_pi_lambda
  intro q
  exact ((measurable_pi_apply q).comp
    (measurable_intervalData.comp ((measurable_driftedReflectionPath lambda).comp
      measurable_fst))).prodMk
    ((measurable_pi_apply (Encodable.encode q)).comp measurable_snd)

def markedIntervalLaw (lambda : ℝ) : Measure (ℚ → (Bool × (ℝ × ℝ)) × ℕ) :=
  (pathJointLaw lambda).map (markedIntervalData lambda)

instance (lambda : ℝ) : IsProbabilityMeasure (markedIntervalLaw lambda) :=
  Measure.isProbabilityMeasure_map (measurable_markedIntervalData lambda).aemeasurable

/-- The full interval/count law is realized by the actual Gaussian source
and its constructed area-rate Poisson marks, without an excursion premise. -/
theorem hasLaw_actual_markedIntervalData (lambda : ℝ) :
    HasLaw (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦
      fun q ↦ (actualData lambda p.1 q,rationalCount p.2 q))
      (markedIntervalLaw lambda) (actualJointLaw lambda) := by
  have h0 : HasLaw (markedIntervalData lambda) (markedIntervalLaw lambda)
      (pathJointLaw lambda) :=
    ⟨(measurable_markedIntervalData lambda).aemeasurable,rfl⟩
  have h1 := h0.fun_comp (hasLaw_actual_path_mark_pair lambda)
  apply h1.congr
  exact Eventually.of_forall (fun p ↦ by funext q; rfl)

theorem markedIntervalLaw_eq_map_actualJointLaw (lambda : ℝ) :
    markedIntervalLaw lambda = (actualJointLaw lambda).map
      (fun p : (ℕ → ℝ) × (ℕ → ℕ) ↦
        fun q ↦ (actualData lambda p.1 q,rationalCount p.2 q)) :=
  (hasLaw_actual_markedIntervalData lambda).map_eq.symm

end PerronWright.BrownianFullHorizonMarkJointLaw
