import PerronWright.Probability.BrownianSublinearGrowth
import PerronWright.Probability.ParabolicLongExcursions
import PerronWright.Probability.DisjointIntervalPacking
import PerronWright.Probability.BrownianFullHorizonExcursions

/-!
# Actual full Brownian excursions are finite on every positive size window

The actual Gaussian fourth moments imply sublinear growth; the proved
parabolic long-excursion window bound and finite interval packing then
give genuine local finiteness. Both the nonrepeating rational section
and the set of literal full connected components are covered.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianLongExcursionLocalFiniteness

open BrownianPathLaw BrownianPathReflectionLaw BrownianGaussianSkeleton
open BrownianContinuousModification FullHorizonExcursionComponents FullHorizonExcursionSection
open FullHorizonExcursionEndpoints BrownianFullHorizonExcursions ParabolicLongExcursions

def longAnchors (a : ℝ) (g : Path) : Set ℚ :=
  {q | Representative g q ∧ a ≤ length (q : ℝ) g}

def longComponents (a : ℝ) (g : Path) : Set (Set ℝ) :=
  {J | ∃ q : ℝ, q ∈ positiveSet g ∧ a ≤ length q g ∧ J = component g q}

theorem measurable_longAnchors (a : ℝ) : Measurable (longAnchors a) := by
  apply measurable_set_iff.mpr
  intro q
  exact measurableSet_setOfPred.mp ((measurableSet_representative q).inter
    (measurableSet_le measurable_const (measurable_length (q : ℝ))))

theorem measurableSet_finite_longAnchors (a : ℝ) :
    MeasurableSet {g : Path | (longAnchors a g).Finite} :=
  MeasurableSet.setOfPred_finite.preimage (measurable_longAnchors a)

theorem length_eq_of_component_eq {g : Path} {q r : ℝ}
    (hq : q ∈ positiveSet g) (hr : r ∈ positiveSet g)
    (he : component g q = component g r) : length q g = length r g := by
  simp only [length,rightEndpoint,leftEndpoint,if_pos hq,if_pos hr,he]

theorem finite_longAnchors (f : Path)
    (hf : Tendsto (fun t : ℝ≥0 ↦ f t / (t : ℝ)) atTop (𝓝 0))
    (lambda : ℝ) (hlim : Tendsto (driftPath lambda f) atTop atBot)
    (a : ℝ) (ha : 0 < a) : (longAnchors a (driftedReflectionPath lambda f)).Finite := by
  let g := driftedReflectionPath lambda f
  obtain ⟨H,_,hH⟩ := long_excursion_uniform_window f hf lambda hlim a ha
  apply DisjointIntervalPacking.finite_set_of_length_lower_bound
    (longAnchors a g) (fun q ↦ leftEndpoint (q : ℝ) g)
    (fun q ↦ rightEndpoint (q : ℝ) g) ha
  · exact fun q _ ↦ leftEndpoint_nonneg (q : ℝ) g
  · exact fun q hq ↦ (hH (q : ℝ) hq.1.1 hq.2).1.le
  · exact fun q hq ↦ hq.2
  · intro q hq r hr hqr
    have hd := representative_components_disjoint hq.1 hr.1 hqr
    rw [component_eq_Ioo hq.1.1 (reflection_component_bddAbove (driftPath lambda f) hlim (q : ℝ)),
      component_eq_Ioo hr.1.1 (reflection_component_bddAbove (driftPath lambda f) hlim (r : ℝ))] at hd
    exact hd

theorem longComponents_subset_image (a : ℝ) (g : Path) :
    longComponents a g ⊆ (fun q : ℚ ↦ component g (q : ℝ)) '' longAnchors a g := by
  intro J hJ
  obtain ⟨q,hq,hlen,rfl⟩ := hJ
  obtain ⟨r,hr,he⟩ := exists_representative hq
  refine ⟨r,⟨hr,?_⟩,he⟩
  rw [length_eq_of_component_eq hr.1 hq he]
  exact hlen

theorem finite_longComponents (f : Path)
    (hf : Tendsto (fun t : ℝ≥0 ↦ f t / (t : ℝ)) atTop (𝓝 0))
    (lambda : ℝ) (hlim : Tendsto (driftPath lambda f) atTop atBot)
    (a : ℝ) (ha : 0 < a) : (longComponents a (driftedReflectionPath lambda f)).Finite :=
  ((finite_longAnchors f hf lambda hlim a ha).image
    (fun q : ℚ ↦ component (driftedReflectionPath lambda f) (q : ℝ))).subset
      (longComponents_subset_image a _)

theorem ae_sublinear_measurablePath :
    ∀ᵐ x ∂rationalLaw, Tendsto (fun t : ℝ≥0 ↦ measurablePath x t / (t : ℝ)) atTop (𝓝 0) := by
  filter_upwards [BrownianSublinearGrowth.ae_sublinear_process,ae_all_measurablePath_eval]
    with x hx he
  have h : (fun t : ℝ≥0 ↦ measurablePath x t / (t : ℝ)) =
      (fun t ↦ process t x / (t : ℝ)) := funext (fun t ↦ by rw [he t])
  rw [h]
  exact hx

/-- Terminal actual Brownian statement: one full-measure source set gives
finitely many full excursions of length at least every positive cutoff,
simultaneously for every parabolic parameter. No growth or local-finiteness
hypothesis is left in the statement. -/
theorem ae_all_actual_long_excursions_finite :
    ∀ᵐ x ∂rationalLaw, ∀ lambda a : ℝ, 0 < a →
      (longAnchors a (BrownianActualWindowExcursions.actualPath lambda x)).Finite ∧
      (longComponents a (BrownianActualWindowExcursions.actualPath lambda x)).Finite := by
  filter_upwards [ae_sublinear_measurablePath,ae_all_path_drift_atBot] with x hs hd
  intro lambda a ha
  exact ⟨finite_longAnchors (measurablePath x) hs lambda (hd lambda) a ha,
    finite_longComponents (measurablePath x) hs lambda (hd lambda) a ha⟩

theorem ae_all_actual_long_excursions_uniform_window :
    ∀ᵐ x ∂rationalLaw, ∀ lambda a : ℝ, 0 < a → ∃ H : ℝ, 0 < H ∧
      ∀ q : ℝ, q ∈ positiveSet (BrownianActualWindowExcursions.actualPath lambda x) →
        a ≤ length q (BrownianActualWindowExcursions.actualPath lambda x) →
        rightEndpoint q (BrownianActualWindowExcursions.actualPath lambda x) < H ∧
        component (BrownianActualWindowExcursions.actualPath lambda x) q ⊆ Ioo 0 H := by
  filter_upwards [ae_sublinear_measurablePath,ae_all_path_drift_atBot] with x hs hd
  intro lambda a ha
  exact long_excursion_uniform_window (measurablePath x) hs lambda (hd lambda) a ha

/-- The genuine path probability law, not only its original Gaussian
source representation, is locally finite on every positive size window. -/
theorem ae_pathLaw_long_excursions_finite (lambda a : ℝ) (ha : 0 < a) :
    ∀ᵐ f ∂pathLaw,
      (longAnchors a (driftedReflectionPath lambda f)).Finite ∧
      (longComponents a (driftedReflectionPath lambda f)).Finite := by
  have hm : MeasurableSet {f : Path | (longAnchors a (driftedReflectionPath lambda f)).Finite} :=
    (measurableSet_finite_longAnchors a).preimage (measurable_driftedReflectionPath lambda)
  have hA : ∀ᵐ f ∂pathLaw, (longAnchors a (driftedReflectionPath lambda f)).Finite := by
    rw [pathLaw]
    apply (ae_map_iff measurable_measurablePath.aemeasurable hm).mpr
    exact ae_all_actual_long_excursions_finite.mono (fun x hx ↦ (hx lambda a ha).1)
  filter_upwards [hA] with f hf
  exact ⟨hf,(hf.image (fun q : ℚ ↦ component (driftedReflectionPath lambda f) (q : ℝ))).subset
    (longComponents_subset_image a _)⟩

theorem ae_reflectedLaw_long_excursions_finite (lambda a : ℝ) (ha : 0 < a) :
    ∀ᵐ g ∂driftedReflectionLaw lambda,
      (longAnchors a g).Finite ∧ (longComponents a g).Finite := by
  have hA : ∀ᵐ g ∂driftedReflectionLaw lambda, (longAnchors a g).Finite := by
    rw [driftedReflectionLaw]
    exact (ae_map_iff (measurable_driftedReflectionPath lambda).aemeasurable
      (measurableSet_finite_longAnchors a)).mpr
        ((ae_pathLaw_long_excursions_finite lambda a ha).mono (fun _ h ↦ h.1))
  filter_upwards [hA] with g hg
  exact ⟨hg,(hg.image (fun q : ℚ ↦ component g (q : ℝ))).subset
    (longComponents_subset_image a g)⟩

theorem ae_all_actual_sizeWindow_anchors_finite :
    ∀ᵐ x ∂rationalLaw, ∀ lambda a b : ℝ, 0 < a →
      {q : ℚ | Representative (BrownianActualWindowExcursions.actualPath lambda x) q ∧
        length (q : ℝ) (BrownianActualWindowExcursions.actualPath lambda x) ∈ Icc a b}.Finite := by
  filter_upwards [ae_all_actual_long_excursions_finite] with x hx
  intro lambda a b ha
  exact ((hx lambda a ha).1).subset (fun q hq ↦ ⟨hq.1,hq.2.1⟩)

end PerronWright.BrownianLongExcursionLocalFiniteness
