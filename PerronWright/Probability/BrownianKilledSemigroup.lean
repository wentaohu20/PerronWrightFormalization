import PerronWright.Probability.BrownianKilledTransitionKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.Comp

/-! # Genuine deterministic-time killed Brownian composition

The continuous path survives on two consecutive intervals exactly when
the stopped past survives and its actual independent forward increments
survive above the shifted level. Tonelli applied to the proved whole-path
product law yields the actual killed endpoint composition formula.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledSemigroup

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathReflection
open ContinuousPathFirstPassage BrownianKilledTransitionKernel

theorem survival_add_iff (level : ℝ) (s t : ℝ≥0) (f : Path) :
    f ∈ survival level (s+t) ↔
      f ∈ survival level s ∧ futurePath s f ∈ survival (level-f s) t := by
  simp only [mem_survival_iff]
  constructor
  · intro h
    constructor
    · intro u hu
      exact h u (hu.trans (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ t)))
    · intro u hu
      have he := h (s+u) (by gcongr)
      rw [futurePath_eval]
      linarith
  · rintro ⟨hh,hf⟩ u hu
    rcases le_or_gt u s with hs | hs
    · exact hh u hs
    · have hsub : u-s ≤ t := (tsub_le_iff_right).mpr (by simpa only [add_comm t s] using hu)
      have he := hf (u-s) hsub
      rw [futurePath_eval,add_tsub_cancel_of_le hs.le] at he
      linarith

theorem past_survival_iff (level : ℝ) (s : ℝ≥0) (f : Path) :
    pastPath s f ∈ survival level s ↔ f ∈ survival level s := by
  simp only [mem_survival_iff]
  constructor <;> intro h u hu
  · simpa only [pastPath_eval,min_eq_left hu] using h u hu
  · simpa only [pastPath_eval,min_eq_left hu] using h u hu

theorem endpoint_add (s t : ℝ≥0) (f : Path) :
    f (s+t) = f s+futurePath s f t := by
  rw [futurePath_eval]
  ring

/-- Literal killed law started at x, expressed using the actually
constructed zero-started Brownian path law. -/
def transitionLaw (level : ℝ) (t : ℝ≥0) (x : ℝ) : Measure ℝ :=
  (killedEndpointLaw (level-x) t).map (fun y : ℝ ↦ x+y)

instance transitionLaw_isFinite (level : ℝ) (t : ℝ≥0) (x : ℝ) :
    IsFiniteMeasure (transitionLaw level t x) := by
  unfold transitionLaw
  infer_instance

def tailEvent (level : ℝ) (t : ℝ≥0) (B : Set ℝ) : Set (ℝ × Path) :=
  {p | p.2 ∈ survival (level-p.1) t ∧ p.1+p.2 t ∈ B}

theorem measurableSet_tailEvent (level : ℝ) (t : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) : MeasurableSet (tailEvent level t B) := by
  apply MeasurableSet.inter
  · exact (isOpen_lt (continuous_const.sub continuous_fst)
      ((continuous_minimum_at t).comp continuous_snd)).measurableSet
  · exact (measurable_fst.add ((continuous_eval t).measurable.comp measurable_snd)) hB

theorem transitionLaw_apply (level : ℝ) (t : ℝ≥0) (x : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    transitionLaw level t x B =
      pathLaw ((fun g : Path ↦ (x,g)) ⁻¹' tailEvent level t B) := by
  have hm : Measurable (fun y : ℝ ↦ x+y) := by fun_prop
  rw [transitionLaw,Measure.map_apply hm hB,killedEndpointLaw_apply _ _ (hm hB)]
  congr 1
  ext g
  simp only [mem_ofPred_eq,mem_preimage,tailEvent,mem_survival_iff_firstPassage]

theorem measurable_transitionLaw_apply (level : ℝ) (t : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) : Measurable (fun x : ℝ ↦ transitionLaw level t x B) := by
  have he : (fun x : ℝ ↦ transitionLaw level t x B) =
      (fun x : ℝ ↦ pathLaw ((fun g : Path ↦ (x,g)) ⁻¹' tailEvent level t B)) :=
    funext (fun x ↦ transitionLaw_apply level t x hB)
  rw [he]
  exact measurable_measure_prodMk_left (measurableSet_tailEvent level t hB)

def segmentEvent (level : ℝ) (s t : ℝ≥0) (B : Set ℝ) : Set (Path × Path) :=
  {p | p.1 ∈ survival level s ∧ (p.1 s,p.2) ∈ tailEvent level t B}

theorem measurableSet_segmentEvent (level : ℝ) (s t : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) : MeasurableSet (segmentEvent level s t B) :=
  (measurable_fst (measurableSet_survival level s)).inter
    ((((continuous_eval s).measurable.comp measurable_fst).prodMk measurable_snd)
      (measurableSet_tailEvent level t hB))

theorem segmentEvent_preimage (level : ℝ) (s t : ℝ≥0) (B : Set ℝ) :
    (fun f : Path ↦ (pastPath s f,futurePath s f)) ⁻¹' segmentEvent level s t B =
      {f : Path | f ∈ survival level (s+t) ∧ f (s+t) ∈ B} := by
  ext f
  simp only [mem_preimage,segmentEvent,tailEvent,mem_ofPred_eq,pastPath_eval,min_self,
    past_survival_iff,survival_add_iff,endpoint_add]
  exact and_assoc.symm

/-- Product-law disintegration at an actual deterministic time, with
both segments constrained by their literal survival events. -/
theorem killedEndpointLaw_eq_past_integral (level : ℝ) (s t : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) :
    killedEndpointLaw level (s+t) B =
      ∫⁻ p in survival level s, transitionLaw level t (p s) B ∂pastLaw s := by
  let A := segmentEvent level s t B
  have hA : MeasurableSet A := measurableSet_segmentEvent level s t hB
  have hj : Measurable (fun f : Path ↦ (pastPath s f,futurePath s f)) :=
    (measurable_pastPath s).prodMk (measurable_futurePath s)
  have he : killedEndpointLaw level (s+t) B = ((pastLaw s).prod pathLaw) A := by
    rw [← past_future_jointLaw s,Measure.map_apply hj hA,segmentEvent_preimage,
      killedEndpointLaw_apply level (s+t) hB]
    congr 1
    ext f
    simp only [mem_ofPred_eq,mem_survival_iff_firstPassage]
  rw [he,Measure.prod_apply hA,← lintegral_indicator (measurableSet_survival level s)]
  apply lintegral_congr
  intro p
  have hs : (fun g : Path ↦ (p,g)) ⁻¹' A =
      if p ∈ survival level s then (fun g : Path ↦ (p s,g)) ⁻¹' tailEvent level t B else ∅ := by
    ext g
    by_cases hp : p ∈ survival level s <;> simp [A,segmentEvent,hp]
  rw [hs]
  by_cases hp : p ∈ survival level s
  · rw [if_pos hp,indicator_of_mem hp,transitionLaw_apply level t (p s) hB]
  · simp only [if_neg hp,measure_empty,indicator_of_notMem hp]

/-- Exact conversion of a nonnegative stopped-past endpoint test into
the actual killed endpoint measure, with no integrability assumption. -/
theorem lintegral_past_survival_eq_killed (level : ℝ) (s : ℝ≥0)
    {F : ℝ → ℝ≥0∞} (hm : Measurable F) :
    (∫⁻ p in survival level s, F (p s) ∂pastLaw s) =
      ∫⁻ x, F x ∂killedEndpointLaw level s := by
  rw [killedEndpointLaw,lintegral_map hm (continuous_eval s).measurable]
  have hF : Measurable ((survival level s).indicator
      (fun p : Path ↦ F (p s))) :=
    (hm.comp (continuous_eval s).measurable).indicator (measurableSet_survival level s)
  rw [← lintegral_indicator (measurableSet_survival level s),
    ← lintegral_indicator (measurableSet_survival level s),pastLaw,
    lintegral_map hF (measurable_pastPath s)]
  apply lintegral_congr
  intro f
  by_cases hf : f ∈ survival level s
  · have hp := (past_survival_iff level s f).mpr hf
    simp only [indicator_of_mem hf,indicator_of_mem hp,pastPath_eval,min_self]
  · have hp : pastPath s f ∉ survival level s := (past_survival_iff level s f).not.mpr hf
    simp only [indicator_of_notMem hf,indicator_of_notMem hp]

/-- Genuine killed endpoint Chapman--Kolmogorov identity. It is derived
from deterministic independent increments, with no Markov identity input. -/
theorem killedEndpointLaw_composition (level : ℝ) (s t : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) :
    killedEndpointLaw level (s+t) B =
      ∫⁻ x, transitionLaw level t x B ∂killedEndpointLaw level s := by
  rw [killedEndpointLaw_eq_past_integral level s t hB]
  exact lintegral_past_survival_eq_killed level s (measurable_transitionLaw_apply level t hB)

theorem transitionLaw_translate (level x z : ℝ) (t : ℝ≥0)
    {B : Set ℝ} (hB : MeasurableSet B) :
    transitionLaw (level-x) t z ((fun y : ℝ ↦ x+y) ⁻¹' B) =
      transitionLaw level t (x+z) B := by
  have hm : Measurable (fun y : ℝ ↦ x+y) := by fun_prop
  rw [transitionLaw_apply _ _ _ (hm hB),transitionLaw_apply _ _ _ hB]
  congr 1
  ext g
  have hl : level-x-z = level-(x+z) := by ring
  simp only [mem_preimage,tailEvent,mem_ofPred_eq,hl,add_assoc]

/-- Actual killed transition composition at every initial state, proved
by translation of the actual zero-started deterministic segment law. -/
theorem transitionLaw_composition (level : ℝ) (s t : ℝ≥0) (x : ℝ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    transitionLaw level (s+t) x B =
      ∫⁻ y, transitionLaw level t y B ∂transitionLaw level s x := by
  have hm : Measurable (fun y : ℝ ↦ x+y) := by fun_prop
  rw [transitionLaw,Measure.map_apply hm hB,killedEndpointLaw_composition _ _ _ (hm hB)]
  change (∫⁻ z, transitionLaw (level-x) t z ((fun y : ℝ ↦ x+y) ⁻¹' B)
    ∂killedEndpointLaw (level-x) s) = _
  rw [transitionLaw,lintegral_map (measurable_transitionLaw_apply level t hB) hm]
  exact lintegral_congr (fun z ↦ transitionLaw_translate level x z t hB)

theorem transitionLaw_univ_le_one (level : ℝ) (t : ℝ≥0) (x : ℝ) :
    transitionLaw level t x univ ≤ 1 := by
  rw [transitionLaw_apply level t x MeasurableSet.univ]
  exact (measure_mono (subset_univ _)).trans_eq (measure_univ : pathLaw univ = 1)

def killedKernel (level : ℝ) (t : ℝ≥0) : Kernel ℝ ℝ :=
  ⟨transitionLaw level t,Measure.measurable_measure.mpr
    (fun _ hB ↦ measurable_transitionLaw_apply level t hB)⟩

@[simp] theorem killedKernel_apply (level : ℝ) (t : ℝ≥0) (x : ℝ) :
    killedKernel level t x = transitionLaw level t x := rfl

instance killedKernel_isFinite (level : ℝ) (t : ℝ≥0) : IsFiniteKernel (killedKernel level t) :=
  ⟨⟨1,ENNReal.one_lt_top,transitionLaw_univ_le_one level t⟩⟩

/-- The semigroup identity is a conclusion for the genuine measurable
killed Brownian kernel, not an additional stochastic-process interface. -/
theorem killedKernel_semigroup (level : ℝ) (s t : ℝ≥0) :
    killedKernel level (s+t) = (killedKernel level t) ∘ₖ (killedKernel level s) := by
  ext x B hB
  rw [Kernel.comp_apply' _ _ _ hB]
  exact transitionLaw_composition level s t x hB

end PerronWright.BrownianKilledSemigroup
