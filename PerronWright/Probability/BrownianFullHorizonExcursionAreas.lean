import PerronWright.Probability.BrownianFullHorizonExcursions
import PerronWright.Probability.BrownianWindowExcursionAreas

/-!
# Genuine measurable full-horizon Brownian excursion areas

Full endpoints and the actual moving-interval integral define these
areas measurably. Exact window stabilization identifies them with literal
component integrals. The actual Brownian growth theorem discharges all
finite-component conditions on one full set for every parameter and anchor.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullHorizonExcursionAreas

open BrownianPathLaw BrownianPathReflectionLaw BrownianGaussianSkeleton
open FullHorizonExcursionComponents FullHorizonExcursionSection FullHorizonExcursionEndpoints
open BrownianFullHorizonExcursions
open BrownianActualWindowExcursions (actualPath)

def leftTime (q lambda : ℝ) (f : Path) : ℝ≥0 :=
  Real.toNNReal (leftEndpoint q (driftedReflectionPath lambda f))

def rightTime (q lambda : ℝ) (f : Path) : ℝ≥0 :=
  Real.toNNReal (rightEndpoint q (driftedReflectionPath lambda f))

@[simp] theorem coe_leftTime (q lambda : ℝ) (f : Path) :
    (leftTime q lambda f : ℝ) = leftEndpoint q (driftedReflectionPath lambda f) :=
  Real.coe_toNNReal _ (leftEndpoint_nonneg q _)

@[simp] theorem coe_rightTime (q lambda : ℝ) (f : Path) :
    (rightTime q lambda f : ℝ) = rightEndpoint q (driftedReflectionPath lambda f) :=
  Real.coe_toNNReal _ (rightEndpoint_nonneg q _)

theorem measurable_leftTime_all_parameters (q : ℝ) :
    Measurable (fun p : ℝ × Path ↦ leftTime q p.1 p.2) :=
  continuous_real_toNNReal.measurable.comp
    ((measurable_leftEndpoint q).comp continuous_driftedReflectionPath.measurable)

theorem measurable_rightTime_all_parameters (q : ℝ) :
    Measurable (fun p : ℝ × Path ↦ rightTime q p.1 p.2) :=
  continuous_real_toNNReal.measurable.comp
    ((measurable_rightEndpoint q).comp continuous_driftedReflectionPath.measurable)

def excursionArea (q lambda : ℝ) (f : Path) : ℝ≥0 :=
  BrownianReflectedAreaCounts.area lambda (leftTime q lambda f) (rightTime q lambda f) f

theorem measurable_excursionArea_all_parameters (q : ℝ) :
    Measurable (fun p : ℝ × Path ↦ excursionArea q p.1 p.2) :=
  BrownianReflectedAreaCounts.measurable_area_all_parameters.comp
    (measurable_id.prodMk ((measurable_leftTime_all_parameters q).prodMk
      (measurable_rightTime_all_parameters q)))

set_option backward.isDefEq.respectTransparency true in
theorem measurable_excursionArea (q lambda : ℝ) : Measurable (excursionArea q lambda) := by
  have hm := (measurable_excursionArea_all_parameters q).comp
    (f := fun f : Path ↦ (lambda,f))
    ((measurable_const : Measurable (fun _ : Path ↦ lambda)).prodMk measurable_id)
  simpa only [Function.comp_def] using hm

theorem excursionArea_eq_window {H q lambda : ℝ} {f : Path} (hqH : q < H)
    (he : BrownianWindowExcursions.component H (driftedReflectionPath lambda f) q =
      component (driftedReflectionPath lambda f) q) :
    excursionArea q lambda f = BrownianWindowExcursionAreas.excursionArea H q lambda f := by
  have hep := endpoints_eq_window hqH he
  change BrownianReflectedAreaCounts.area lambda
    (Real.toNNReal (leftEndpoint q (driftedReflectionPath lambda f)))
    (Real.toNNReal (rightEndpoint q (driftedReflectionPath lambda f))) f =
      BrownianReflectedAreaCounts.area lambda
        (Real.toNNReal (BrownianWindowExcursionEndpoints.leftEndpoint H q (driftedReflectionPath lambda f)))
        (Real.toNNReal (BrownianWindowExcursionEndpoints.rightEndpoint H q (driftedReflectionPath lambda f))) f
  rw [hep.1,hep.2]

theorem representative_iff_window {H : ℝ} {q : ℚ} {f : Path} (hqH : (q : ℝ) < H)
    (he : BrownianWindowExcursions.component H f (q : ℝ) = component f (q : ℝ)) :
    BrownianWindowExcursions.Representative H f q ↔ Representative f q := by
  have ha : (q : ℝ) ∈ BrownianWindowExcursions.positiveWindow H f ↔
      (q : ℝ) ∈ positiveSet f := by
    change (0 < (q : ℝ) ∧ (q : ℝ) < H) ∧ 0 < BrownianWindowExcursions.realEval f q ↔
      0 < (q : ℝ) ∧ 0 < BrownianWindowExcursions.realEval f q
    simp only [hqH,and_true]
  simp only [BrownianWindowExcursions.Representative,Representative,ha,he]

theorem integrableOn_component (f : Path) (q : ℝ) (hb : BddAbove (component f q)) :
    IntegrableOn (BrownianWindowExcursions.realEval f) (component f q) := by
  obtain ⟨H,_,_,he⟩ := exists_stable_window f q hb
  rw [← he H le_rfl]
  exact BrownianWindowExcursionAreas.integrableOn_component H q f

/-- The area is the actual Lebesgue integral over the full excursion. -/
theorem excursionArea_eq_component_integral {q lambda : ℝ} {f : Path}
    (hb : BddAbove (component (driftedReflectionPath lambda f) q)) :
    (excursionArea q lambda f : ℝ) =
      ∫ s in component (driftedReflectionPath lambda f) q,
        BrownianWindowExcursions.realEval (driftedReflectionPath lambda f) s := by
  obtain ⟨H,_,hqH,he⟩ := exists_stable_window _ q hb
  rw [excursionArea_eq_window hqH (he H le_rfl),← he H le_rfl]
  exact BrownianWindowExcursionAreas.excursionArea_eq_component_integral_all H q lambda f

theorem excursionArea_pos {q lambda : ℝ} {f : Path}
    (hq : q ∈ positiveSet (driftedReflectionPath lambda f))
    (hb : BddAbove (component (driftedReflectionPath lambda f) q)) :
    0 < excursionArea q lambda f := by
  obtain ⟨H,_,hqH,he⟩ := exists_stable_window _ q hb
  rw [excursionArea_eq_window hqH (he H le_rfl)]
  exact BrownianWindowExcursionAreas.excursionArea_pos ⟨⟨hq.1,hqH⟩,hq.2⟩

def retainedArea (q : ℚ) (lambda : ℝ) (f : Path) : ℝ≥0 :=
  if Representative (driftedReflectionPath lambda f) q then excursionArea (q : ℝ) lambda f else 0

theorem measurable_retainedArea_all_parameters (q : ℚ) :
    Measurable (fun p : ℝ × Path ↦ retainedArea q p.1 p.2) :=
  Measurable.ite
    ((measurableSet_representative q).preimage continuous_driftedReflectionPath.measurable)
    (measurable_excursionArea_all_parameters (q : ℝ)) measurable_const

def areaData (lambda : ℝ) (f : Path) : ℚ → ℝ≥0 := fun q ↦ retainedArea q lambda f

theorem measurable_areaData_all_parameters :
    Measurable (fun p : ℝ × Path ↦ areaData p.1 p.2) :=
  measurable_pi_lambda _ measurable_retainedArea_all_parameters

set_option backward.isDefEq.respectTransparency true in
theorem measurable_areaData (lambda : ℝ) : Measurable (areaData lambda) := by
  have hm := measurable_areaData_all_parameters.comp (f := fun f : Path ↦ (lambda,f))
    ((measurable_const : Measurable (fun _ : Path ↦ lambda)).prodMk measurable_id)
  simpa only [Function.comp_def] using hm

def excursionAreaLaw (lambda : ℝ) : Measure (ℚ → ℝ≥0) := pathLaw.map (areaData lambda)

instance (lambda : ℝ) : IsProbabilityMeasure (excursionAreaLaw lambda) :=
  Measure.isProbabilityMeasure_map (measurable_areaData lambda).aemeasurable

theorem hasLaw_actual_areaData (lambda : ℝ) :
    HasLaw (fun x ↦ areaData lambda (measurablePath x)) (excursionAreaLaw lambda) rationalLaw :=
  (show HasLaw (areaData lambda) (excursionAreaLaw lambda) pathLaw from
    ⟨(measurable_areaData lambda).aemeasurable,rfl⟩).fun_comp hasLaw_measurablePath

theorem excursionAreaLaw_eq_map_rationalLaw (lambda : ℝ) :
    excursionAreaLaw lambda = rationalLaw.map (fun x ↦ areaData lambda (measurablePath x)) :=
  (hasLaw_actual_areaData lambda).map_eq.symm

theorem ae_all_actual_component_integrable : ∀ᵐ x ∂rationalLaw, ∀ lambda q : ℝ,
    IntegrableOn (BrownianWindowExcursions.realEval (actualPath lambda x))
      (component (actualPath lambda x) q) := by
  filter_upwards [ae_all_actual_components_bddAbove] with x hx
  intro lambda q
  exact integrableOn_component _ q (hx lambda q)

theorem ae_all_excursionArea_eq_component_integral : ∀ᵐ x ∂rationalLaw, ∀ lambda q : ℝ,
    (excursionArea q lambda (measurablePath x) : ℝ) =
      ∫ s in component (actualPath lambda x) q,
        BrownianWindowExcursions.realEval (actualPath lambda x) s := by
  filter_upwards [ae_all_actual_components_bddAbove] with x hx
  intro lambda q
  exact excursionArea_eq_component_integral (hx lambda q)

theorem ae_all_retainedArea_pos_iff : ∀ᵐ x ∂rationalLaw, ∀ lambda : ℝ, ∀ q : ℚ,
    0 < retainedArea q lambda (measurablePath x) ↔ Representative (actualPath lambda x) q := by
  filter_upwards [ae_all_actual_components_bddAbove] with x hx
  intro lambda q
  by_cases hq : Representative (actualPath lambda x) q
  · simp only [retainedArea,actualPath] at hq ⊢
    simp only [hq,if_true,iff_true]
    exact excursionArea_pos hq.1 (hx lambda (q : ℝ))
  · simp only [retainedArea,actualPath] at hq ⊢
    simp only [hq,if_false,lt_self_iff_false]

theorem ae_all_excursionArea_window_stability : ∀ᵐ x ∂rationalLaw, ∀ lambda q : ℝ,
    ∃ H : ℝ, 0 < H ∧ q < H ∧ ∀ L ≥ H,
      excursionArea q lambda (measurablePath x) =
        BrownianWindowExcursionAreas.excursionArea L q lambda (measurablePath x) := by
  filter_upwards [ae_all_actual_component_window_stability] with x hx
  intro lambda q
  obtain ⟨H,h0,hqH,he⟩ := hx lambda q
  exact ⟨H,h0,hqH,fun L hL ↦ excursionArea_eq_window (hqH.trans_le hL) (he L hL)⟩

theorem ae_all_retainedArea_window_stability : ∀ᵐ x ∂rationalLaw, ∀ lambda : ℝ, ∀ q : ℚ,
    ∃ H : ℝ, 0 < H ∧ (q : ℝ) < H ∧ ∀ L ≥ H,
      retainedArea q lambda (measurablePath x) =
        BrownianWindowExcursionAreas.retainedArea L lambda q (measurablePath x) := by
  filter_upwards [ae_all_actual_component_window_stability] with x hx
  intro lambda q
  obtain ⟨H,h0,hqH,he⟩ := hx lambda (q : ℝ)
  refine ⟨H,h0,hqH,fun L hL ↦ ?_⟩
  have hrep := representative_iff_window (hqH.trans_le hL) (he L hL)
  change (if Representative (actualPath lambda x) q then excursionArea (q : ℝ) lambda (measurablePath x) else 0) =
    (if BrownianWindowExcursions.Representative L (actualPath lambda x) q then
      BrownianWindowExcursionAreas.excursionArea L (q : ℝ) lambda (measurablePath x) else 0)
  rw [hrep,excursionArea_eq_window (hqH.trans_le hL) (he L hL)]

theorem ae_all_excursionArea_eq_raw : ∀ᵐ x ∂rationalLaw, ∀ lambda q : ℝ,
    (excursionArea q lambda (measurablePath x) : ℝ) =
      ∫ s in connectedComponentIn (rawPositiveSet lambda x) q,
        BrownianParabolicReflection.reflection lambda (Real.toNNReal s) x := by
  filter_upwards [ae_all_excursionArea_eq_component_integral,ae_all_actual_component_eq_raw,
    ae_all_actual_driftedReflection_eq] with x ha hc he
  intro lambda q
  rw [ha lambda q,hc lambda q]
  apply setIntegral_congr_fun
  · rw [← hc lambda q]
    exact (isOpen_component (actualPath lambda x) q).measurableSet
  · intro s _
    exact he lambda (Real.toNNReal s)

theorem aemeasurable_raw_excursionArea (q lambda : ℝ) : AEMeasurable
    (fun x : ℕ → ℝ ↦ ∫ s in connectedComponentIn (rawPositiveSet lambda x) q,
      BrownianParabolicReflection.reflection lambda (Real.toNNReal s) x) rationalLaw := by
  have hm : Measurable (fun x : ℕ → ℝ ↦ (excursionArea q lambda (measurablePath x) : ℝ)) :=
    NNReal.continuous_coe.measurable.comp ((measurable_excursionArea q lambda).comp measurable_measurablePath)
  exact hm.aemeasurable.congr (ae_all_excursionArea_eq_raw.mono (fun _ hx ↦ hx lambda q))

end PerronWright.BrownianFullHorizonExcursionAreas
