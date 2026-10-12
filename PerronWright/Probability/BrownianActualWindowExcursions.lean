import PerronWright.Probability.BrownianWindowExcursionEndpoints

/-!
# The actual reflected Brownian bounded-window excursion law

The coordinate law below records rational representatives, and their actual
connected-interval endpoints. A Boolean distinguishes retained anchors
from duplicates; no duplicate positive excursion is retained. The law is
a genuine measurable pushforward of the constructed reflected Brownian
path law. On one full set it enumerates the literal sampled reflection's
components simultaneously for every drift parameter and bounded window.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianActualWindowExcursions

open BrownianPathLaw BrownianPathReflectionLaw BrownianWindowExcursions
open BrownianWindowExcursionEndpoints BrownianGaussianSkeleton BrownianContinuousModification

def retained (H : ℝ) (q : ℚ) (f : Path) : Bool := if Representative H f q then true else false

def intervalData (H : ℝ) (f : Path) (q : ℚ) : Bool × (ℝ × ℝ) :=
  (retained H q f,leftEndpoint H (q : ℝ) f,rightEndpoint H (q : ℝ) f)

theorem measurable_retained (H : ℝ) (q : ℚ) : Measurable (retained H q) :=
  Measurable.ite (measurableSet_representative H q) measurable_const measurable_const

theorem measurable_intervalData (H : ℝ) : Measurable (intervalData H) :=
  measurable_pi_lambda _ (fun q ↦ (measurable_retained H q).prodMk
    ((measurable_leftEndpoint H (q : ℝ)).prodMk (measurable_rightEndpoint H (q : ℝ))))

@[simp] theorem retained_eq_true (H : ℝ) (q : ℚ) (f : Path) :
    retained H q f = true ↔ Representative H f q := by simp [retained]

def actualPath (lambda : ℝ) (x : ℕ → ℝ) : Path :=
  driftedReflectionPath lambda (measurablePath x)

theorem measurable_actualPath (lambda : ℝ) : Measurable (actualPath lambda) :=
  (measurable_driftedReflectionPath lambda).comp measurable_measurablePath

theorem measurable_actualPath_all_parameters : Measurable
    (fun p : ℝ × (ℕ → ℝ) ↦ actualPath p.1 p.2) :=
  continuous_driftedReflectionPath.measurable.comp
    (measurable_fst.prodMk (measurable_measurablePath.comp measurable_snd))

def actualData (H lambda : ℝ) (x : ℕ → ℝ) (q : ℚ) : Bool × (ℝ × ℝ) :=
  intervalData H (actualPath lambda x) q

theorem measurable_actualData (H lambda : ℝ) : Measurable (actualData H lambda) :=
  (measurable_intervalData H).comp (measurable_actualPath lambda)

theorem measurable_actualData_all_parameters (H : ℝ) : Measurable
    (fun p : ℝ × (ℕ → ℝ) ↦ actualData H p.1 p.2) :=
  (measurable_intervalData H).comp measurable_actualPath_all_parameters

def clippedExcursionDataLaw (H lambda : ℝ) : Measure (ℚ → Bool × (ℝ × ℝ)) :=
  (driftedReflectionLaw lambda).map (intervalData H)

instance (H lambda : ℝ) : IsProbabilityMeasure (clippedExcursionDataLaw H lambda) :=
  Measure.isProbabilityMeasure_map (measurable_intervalData H).aemeasurable

theorem hasLaw_actualData (H lambda : ℝ) :
    HasLaw (actualData H lambda) (clippedExcursionDataLaw H lambda) rationalLaw :=
  (show HasLaw (intervalData H) (clippedExcursionDataLaw H lambda) (driftedReflectionLaw lambda) from
    ⟨(measurable_intervalData H).aemeasurable,rfl⟩).fun_comp (hasLaw_actual_driftedReflectionPath lambda)

theorem clippedExcursionDataLaw_eq_map_rationalLaw (H lambda : ℝ) :
    clippedExcursionDataLaw H lambda = rationalLaw.map (actualData H lambda) :=
  (hasLaw_actualData H lambda).map_eq.symm

theorem actual_positiveWindow_decomposition (H lambda : ℝ) (x : ℕ → ℝ) :
    positiveWindow H (actualPath lambda x) =
      ⋃ q : ℚ, ⋃ (_ : (actualData H lambda x q).1 = true),
        component H (actualPath lambda x) (q : ℝ) := by
  simpa only [actualData,intervalData,retained_eq_true] using
    positiveWindow_eq_union_representatives H (actualPath lambda x)

theorem actual_retained_components_disjoint {H lambda : ℝ} {x : ℕ → ℝ} {q r : ℚ}
    (hq : (actualData H lambda x q).1 = true) (hr : (actualData H lambda x r).1 = true) (hqr : q ≠ r) :
    Disjoint (component H (actualPath lambda x) (q : ℝ))
      (component H (actualPath lambda x) (r : ℝ)) :=
  representative_components_disjoint ((retained_eq_true H q _).mp hq)
    ((retained_eq_true H r _).mp hr) hqr

theorem actual_retained_interval {H lambda : ℝ} {x : ℕ → ℝ} {q : ℚ}
    (hq : (actualData H lambda x q).1 = true) :
    component H (actualPath lambda x) (q : ℝ) =
      Ioo (actualData H lambda x q).2.1 (actualData H lambda x q).2.2 :=
  component_eq_Ioo ((retained_eq_true H q _).mp hq).1

theorem actual_retained_bounds {H lambda : ℝ} {x : ℕ → ℝ} {q : ℚ}
    (hq : (actualData H lambda x q).1 = true) :
    0 ≤ (actualData H lambda x q).2.1 ∧ (actualData H lambda x q).2.1 < (q : ℝ) ∧
      (q : ℝ) < (actualData H lambda x q).2.2 ∧ (actualData H lambda x q).2.2 ≤ H :=
  endpoint_bounds ((retained_eq_true H q _).mp hq).1

theorem countable_actual_retained_components (H lambda : ℝ) (x : ℕ → ℝ) :
    Set.Countable {J : Set ℝ | ∃ q : ℚ, (actualData H lambda x q).1 = true ∧
      component H (actualPath lambda x) (q : ℝ) = J} := by
  apply (countable_range (fun q : ℚ ↦ component H (actualPath lambda x) (q : ℝ))).mono
  rintro J ⟨q,_,rfl⟩
  exact mem_range_self q

theorem actual_retained_intervals_injective {H lambda : ℝ} {x : ℕ → ℝ} {q r : ℚ}
    (hq : (actualData H lambda x q).1 = true) (hr : (actualData H lambda x r).1 = true)
    (he : (actualData H lambda x q).2 = (actualData H lambda x r).2) : q = r := by
  apply representatives_eq_of_component_eq ((retained_eq_true H q _).mp hq)
    ((retained_eq_true H r _).mp hr)
  rw [actual_retained_interval hq,actual_retained_interval hr]
  rw [congrArg Prod.fst he,congrArg Prod.snd he]

def rawPositiveWindow (H lambda : ℝ) (x : ℕ → ℝ) : Set ℝ := Ioo 0 H ∩
  {s | 0 < ContinuousPathReflection.reflected
    (ContinuousPathReflection.parabolicDrift lambda (fun t ↦ process t x)) (Real.toNNReal s)}

/-- The actual full set covers every parameter, every window and every
real anchor; it is not a separately assumed mark-concentration event. -/
theorem ae_all_actual_positiveWindow_eq_raw : ∀ᵐ x ∂rationalLaw, ∀ lambda H : ℝ,
    positiveWindow H (actualPath lambda x) = rawPositiveWindow H lambda x := by
  filter_upwards [ae_all_actual_driftedReflection_eq] with x hx
  intro lambda H
  ext s
  simp only [positiveWindow,rawPositiveWindow,mem_inter_iff,mem_ofPred_eq,realEval,actualPath,
    hx lambda (Real.toNNReal s)]

theorem ae_all_actual_component_eq_raw : ∀ᵐ x ∂rationalLaw, ∀ lambda H q : ℝ,
    component H (actualPath lambda x) q = connectedComponentIn (rawPositiveWindow H lambda x) q := by
  filter_upwards [ae_all_actual_positiveWindow_eq_raw] with x hx
  intro lambda H q
  exact congrArg (fun s : Set ℝ ↦ connectedComponentIn s q) (hx lambda H)

end PerronWright.BrownianActualWindowExcursions
