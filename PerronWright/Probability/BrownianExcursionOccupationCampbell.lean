import PerronWright.Probability.FullHorizonExcursionOccupation
import PerronWright.Probability.BrownianFullHorizonExcursions

/-! # Genuine excursion occupation / Campbell exchange

The actual Brownian growth theorem makes every reflected component finite.
The literal occupation of a time point therefore equals the countable
length-size-biased representative sum. Tonelli exchanges the actual time
and Brownian source integrals; inverse-length occupation recovers the
unweighted Campbell sum, without assuming a finite first moment.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianExcursionOccupationCampbell

open BrownianPathLaw BrownianPathReflectionLaw BrownianFullHorizonExcursions
open FullHorizonExcursionComponents FullHorizonExcursionSection FullHorizonExcursionEndpoints

def occupation (lambda : ℝ) (H : (Path × ℝ × ℝ) → ℝ≥0∞) (p : Path × ℝ) : ℝ≥0∞ :=
  FullHorizonExcursionOccupation.occupation H p.1 (driftedReflectionPath lambda p.1) p.2

theorem measurable_occupation (lambda : ℝ) (H : (Path × ℝ × ℝ) → ℝ≥0∞)
    (hH : Measurable H) : Measurable (occupation lambda H) := by
  have hmap : Measurable (fun p : Path × ℝ ↦ (p.1,driftedReflectionPath lambda p.1,p.2)) :=
    measurable_fst.prodMk (((measurable_driftedReflectionPath lambda).comp measurable_fst).prodMk
      measurable_snd)
  exact (FullHorizonExcursionOccupation.measurable_joint_occupation H hH).comp hmap

def retainedWeight (lambda : ℝ) (H : (Path × ℝ × ℝ) → ℝ≥0∞) (q : ℚ) (f : Path) : ℝ≥0∞ :=
  if Representative (driftedReflectionPath lambda f) q then
    ENNReal.ofReal (length (q : ℝ) (driftedReflectionPath lambda f))*
      H (f,leftEndpoint (q : ℝ) (driftedReflectionPath lambda f),
        length (q : ℝ) (driftedReflectionPath lambda f)) else 0

theorem measurable_retainedWeight (lambda : ℝ) (H : (Path × ℝ × ℝ) → ℝ≥0∞)
    (hH : Measurable H) (q : ℚ) : Measurable (retainedWeight lambda H q) := by
  have hlen : Measurable (fun f : Path ↦ length (q : ℝ) (driftedReflectionPath lambda f)) :=
    (measurable_length (q : ℝ)).comp (measurable_driftedReflectionPath lambda)
  have hleft : Measurable (fun f : Path ↦ leftEndpoint (q : ℝ) (driftedReflectionPath lambda f)) :=
    (measurable_leftEndpoint (q : ℝ)).comp (measurable_driftedReflectionPath lambda)
  have hmark : Measurable (fun f : Path ↦
      H (f,leftEndpoint (q : ℝ) (driftedReflectionPath lambda f),
        length (q : ℝ) (driftedReflectionPath lambda f))) :=
    hH.comp (measurable_id.prodMk (hleft.prodMk hlen))
  exact Measurable.ite
    ((measurableSet_representative q).preimage (measurable_driftedReflectionPath lambda))
      (hlen.ennreal_ofReal.mul hmark) measurable_const

theorem ae_components_bddAbove (lambda : ℝ) : ∀ᵐ f ∂pathLaw, ∀ q : ℚ,
    BddAbove (component (driftedReflectionPath lambda f) (q : ℝ)) := by
  have hm : MeasurableSet {f : Path | ∀ q : ℚ,
      BddAbove (component (driftedReflectionPath lambda f) (q : ℝ))} := by
    have h : MeasurableSet (⋂ q : ℚ,
        {f : Path | BddAbove (component (driftedReflectionPath lambda f) (q : ℝ))}) :=
      MeasurableSet.iInter (fun q ↦ (measurableSet_component_bddAbove (q : ℝ)).preimage
        (measurable_driftedReflectionPath lambda))
    convert h using 1
    ext f
    simp only [mem_iInter,mem_ofPred_eq]
  rw [pathLaw]
  apply (ae_map_iff measurable_measurablePath.aemeasurable hm).mpr
  exact ae_all_actual_components_bddAbove.mono (fun x hx q ↦ hx lambda (q : ℝ))

theorem actual_length_sizeBiased_campbell (lambda : ℝ) (H : (Path × ℝ × ℝ) → ℝ≥0∞)
    (hH : Measurable H) :
    (∫⁻ t : ℝ, ∫⁻ f : Path, occupation lambda H (f,t) ∂pathLaw) =
      ∑' q : ℚ, ∫⁻ f : Path, retainedWeight lambda H q f ∂pathLaw := by
  have hs : (∫⁻ f : Path, ∫⁻ t : ℝ, occupation lambda H (f,t) ∂volume ∂pathLaw) =
      ∫⁻ t : ℝ, ∫⁻ f : Path, occupation lambda H (f,t) ∂pathLaw :=
    lintegral_lintegral_swap (measurable_occupation lambda H hH).aemeasurable
  rw [← hs]
  calc
    _ = ∫⁻ f : Path, ∑' q : ℚ, retainedWeight lambda H q f ∂pathLaw := by
      apply lintegral_congr_ae
      filter_upwards [ae_components_bddAbove lambda] with f hf
      exact FullHorizonExcursionOccupation.lintegral_occupation_eq_length_sum H f
        (driftedReflectionPath lambda f) hf
    _ = _ := lintegral_tsum (fun q ↦ (measurable_retainedWeight lambda H hH q).aemeasurable)

theorem actual_campbell_inverse_length (lambda : ℝ) (H : (Path × ℝ × ℝ) → ℝ≥0∞)
    (hH : Measurable H) :
    (∫⁻ t : ℝ, ∫⁻ f : Path,
      occupation lambda (fun p ↦ H p/ENNReal.ofReal p.2.2) (f,t) ∂pathLaw) =
      ∑' q : ℚ, ∫⁻ f : Path,
        if Representative (driftedReflectionPath lambda f) q then
          H (f,leftEndpoint (q : ℝ) (driftedReflectionPath lambda f),
            length (q : ℝ) (driftedReflectionPath lambda f)) else 0 ∂pathLaw := by
  have hnorm : Measurable (fun p : Path × ℝ × ℝ ↦ H p/ENNReal.ofReal p.2.2) :=
    hH.div measurable_snd.snd.ennreal_ofReal
  rw [actual_length_sizeBiased_campbell lambda _ hnorm]
  apply tsum_congr
  intro q
  apply lintegral_congr_ae
  filter_upwards [ae_components_bddAbove lambda] with f hf
  by_cases hq : Representative (driftedReflectionPath lambda f) q
  · simp only [retainedWeight,if_pos hq]
    have hl := length_pos hq.1 (hf q)
    rw [mul_comm]
    exact ENNReal.div_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hl) ENNReal.ofReal_ne_top
  · simp only [retainedWeight,if_neg hq]

end PerronWright.BrownianExcursionOccupationCampbell
