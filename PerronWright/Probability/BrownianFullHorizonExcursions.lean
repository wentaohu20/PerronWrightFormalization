import PerronWright.Probability.FullHorizonExcursionEndpoints
import PerronWright.Probability.BrownianFullHorizonDrift
import PerronWright.Probability.BrownianActualWindowExcursions

/-!
# Actual full-horizon reflected Brownian excursions

The genuine Brownian growth theorem supplies negative-infinite drift for
every parameter on one full set. The deterministic construction then
proves finite, zero-ended full excursions, with exact eventual window
stability. The rational-section endpoint law is a measurable pushforward
of the actual Brownian path law; there is no excursion-realization input.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullHorizonExcursions

open BrownianPathLaw BrownianPathReflectionLaw BrownianGaussianSkeleton
open FullHorizonExcursionComponents FullHorizonExcursionSection FullHorizonExcursionEndpoints
open BrownianActualWindowExcursions (actualPath measurable_actualPath measurable_actualPath_all_parameters)

def retained (q : ℚ) (f : Path) : Bool := if Representative f q then true else false

def intervalData (f : Path) (q : ℚ) : Bool × (ℝ × ℝ) :=
  (retained q f,leftEndpoint (q : ℝ) f,rightEndpoint (q : ℝ) f)

theorem measurable_retained (q : ℚ) : Measurable (retained q) :=
  Measurable.ite (measurableSet_representative q) measurable_const measurable_const

theorem measurable_intervalData : Measurable intervalData :=
  measurable_pi_lambda _ (fun q ↦ (measurable_retained q).prodMk
    ((measurable_leftEndpoint (q : ℝ)).prodMk (measurable_rightEndpoint (q : ℝ))))

@[simp] theorem retained_eq_true (q : ℚ) (f : Path) :
    retained q f = true ↔ Representative f q := by simp [retained]

def actualData (lambda : ℝ) (x : ℕ → ℝ) : ℚ → Bool × (ℝ × ℝ) :=
  intervalData (actualPath lambda x)

theorem measurable_actualData (lambda : ℝ) : Measurable (actualData lambda) :=
  measurable_intervalData.comp (measurable_actualPath lambda)

theorem measurable_actualData_all_parameters : Measurable
    (fun p : ℝ × (ℕ → ℝ) ↦ actualData p.1 p.2) :=
  measurable_intervalData.comp measurable_actualPath_all_parameters

def excursionDataLaw (lambda : ℝ) : Measure (ℚ → Bool × (ℝ × ℝ)) :=
  (driftedReflectionLaw lambda).map intervalData

instance (lambda : ℝ) : IsProbabilityMeasure (excursionDataLaw lambda) :=
  Measure.isProbabilityMeasure_map measurable_intervalData.aemeasurable

theorem hasLaw_actualData (lambda : ℝ) :
    HasLaw (actualData lambda) (excursionDataLaw lambda) rationalLaw :=
  (show HasLaw intervalData (excursionDataLaw lambda) (driftedReflectionLaw lambda) from
    ⟨measurable_intervalData.aemeasurable,rfl⟩).fun_comp (hasLaw_actual_driftedReflectionPath lambda)

theorem excursionDataLaw_eq_map_rationalLaw (lambda : ℝ) :
    excursionDataLaw lambda = rationalLaw.map (actualData lambda) :=
  (hasLaw_actualData lambda).map_eq.symm

/-- The actual modified continuous path inherits the proved drift limit,
simultaneously for every parameter, rather than assuming it anew. -/
theorem ae_all_path_drift_atBot : ∀ᵐ x ∂rationalLaw, ∀ lambda : ℝ,
    Tendsto (driftPath lambda (measurablePath x)) atTop atBot := by
  filter_upwards [BrownianFullHorizonDrift.ae_all_parameter_continuous_drift_atBot,
    ae_all_measurablePath_eval] with x hd hx
  intro lambda
  have he : (driftPath lambda (measurablePath x) : ℝ≥0 → ℝ) =
      (fun t ↦ BrownianParabolicReflection.drift lambda t x) := by
    funext t
    change measurablePath x t + lambda * (t : ℝ) - (t : ℝ)^2 / 2 =
      BrownianContinuousModification.process t x + lambda * (t : ℝ) - (t : ℝ)^2 / 2
    rw [hx t]
  rw [he]
  exact (hd lambda).2

theorem ae_all_actual_return_times : ∀ᵐ x ∂rationalLaw, ∀ lambda : ℝ, ∀ q : ℝ≥0,
    ∃ t : ℝ≥0, q < t ∧ actualPath lambda x t = 0 := by
  filter_upwards [ae_all_path_drift_atBot] with x hx
  intro lambda q
  exact ReflectionExcursionReturns.exists_zero_after
    (continuous_path (driftPath lambda (measurablePath x))) (hx lambda) q

theorem ae_all_actual_components_bddAbove : ∀ᵐ x ∂rationalLaw, ∀ lambda q : ℝ,
    BddAbove (component (actualPath lambda x) q) := by
  filter_upwards [ae_all_path_drift_atBot] with x hx
  intro lambda q
  exact reflection_component_bddAbove (driftPath lambda (measurablePath x)) (hx lambda) q

theorem ae_all_actual_component_window_stability : ∀ᵐ x ∂rationalLaw, ∀ lambda q : ℝ,
    ∃ H : ℝ, 0 < H ∧ q < H ∧ ∀ L ≥ H,
      BrownianWindowExcursions.component L (actualPath lambda x) q =
        component (actualPath lambda x) q := by
  filter_upwards [ae_all_actual_components_bddAbove] with x hx
  intro lambda q
  exact exists_stable_window _ q (hx lambda q)

/-- Full, finite excursion intervals have zero at both genuine endpoints. -/
theorem ae_all_actual_excursion_properties : ∀ᵐ x ∂rationalLaw, ∀ lambda q : ℝ,
    q ∈ positiveSet (actualPath lambda x) →
      component (actualPath lambda x) q =
        Ioo (leftEndpoint q (actualPath lambda x)) (rightEndpoint q (actualPath lambda x)) ∧
      0 ≤ leftEndpoint q (actualPath lambda x) ∧
      leftEndpoint q (actualPath lambda x) < q ∧ q < rightEndpoint q (actualPath lambda x) ∧
      BrownianWindowExcursions.realEval (actualPath lambda x) (leftEndpoint q (actualPath lambda x)) = 0 ∧
      BrownianWindowExcursions.realEval (actualPath lambda x) (rightEndpoint q (actualPath lambda x)) = 0 ∧
      0 < length q (actualPath lambda x) := by
  filter_upwards [ae_all_path_drift_atBot] with x hx
  intro lambda q hq
  have hb := reflection_component_bddAbove (driftPath lambda (measurablePath x)) (hx lambda) q
  have hz := reflection_endpoints_zero (driftPath lambda (measurablePath x)) (hx lambda) hq
  have hbound := endpoint_bounds hq hb
  exact ⟨component_eq_Ioo hq hb,hbound.1,hbound.2.1,hbound.2.2,hz.1,hz.2,length_pos hq hb⟩

theorem actual_positiveSet_decomposition (lambda : ℝ) (x : ℕ → ℝ) :
    positiveSet (actualPath lambda x) =
      ⋃ q : ℚ, ⋃ (_ : (actualData lambda x q).1 = true), component (actualPath lambda x) (q : ℝ) := by
  simpa only [actualData,intervalData,retained_eq_true] using
    positiveSet_eq_union_representatives (actualPath lambda x)

theorem actual_retained_components_disjoint {lambda : ℝ} {x : ℕ → ℝ} {q r : ℚ}
    (hq : (actualData lambda x q).1 = true) (hr : (actualData lambda x r).1 = true) (hqr : q ≠ r) :
    Disjoint (component (actualPath lambda x) (q : ℝ)) (component (actualPath lambda x) (r : ℝ)) :=
  representative_components_disjoint ((retained_eq_true q _).mp hq)
    ((retained_eq_true r _).mp hr) hqr

theorem countable_actual_retained_components (lambda : ℝ) (x : ℕ → ℝ) :
    Set.Countable {J : Set ℝ | ∃ q : ℚ, (actualData lambda x q).1 = true ∧
      component (actualPath lambda x) (q : ℝ) = J} := by
  apply (countable_range (fun q : ℚ ↦ component (actualPath lambda x) (q : ℝ))).mono
  rintro J ⟨q,_,rfl⟩
  exact mem_range_self q

def rawPositiveSet (lambda : ℝ) (x : ℕ → ℝ) : Set ℝ := Ioi 0 ∩
  {s | 0 < BrownianParabolicReflection.reflection lambda (Real.toNNReal s) x}

theorem ae_all_actual_positiveSet_eq_raw : ∀ᵐ x ∂rationalLaw, ∀ lambda : ℝ,
    positiveSet (actualPath lambda x) = rawPositiveSet lambda x := by
  filter_upwards [ae_all_actual_driftedReflection_eq] with x hx
  intro lambda
  ext s
  simp only [positiveSet,rawPositiveSet,mem_inter_iff,mem_ofPred_eq,
    BrownianWindowExcursions.realEval,actualPath,hx lambda (Real.toNNReal s)]
  rfl

theorem ae_all_actual_component_eq_raw : ∀ᵐ x ∂rationalLaw, ∀ lambda q : ℝ,
    component (actualPath lambda x) q = connectedComponentIn (rawPositiveSet lambda x) q := by
  filter_upwards [ae_all_actual_positiveSet_eq_raw] with x hx
  intro lambda q
  exact congrArg (fun s : Set ℝ ↦ connectedComponentIn s q) (hx lambda)

end PerronWright.BrownianFullHorizonExcursions
