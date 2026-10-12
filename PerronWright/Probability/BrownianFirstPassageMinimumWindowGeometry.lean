import PerronWright.Probability.BrownianFirstPassageEndpointGeometry

/-! # Exact first-hit geometry for a minimum-depth window

Before its first hit of a level the path lies above that level. After
the actual hit, staying above a lower level is exactly the future path
staying above the difference. This is deterministic path geometry;
the actual Brownian terminal below discharges hit and finiteness.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageMinimumWindowGeometry

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianFirstPassageUncappedLaw BrownianFirstPassageZeroDrift
open BrownianFirstPassageEndpointGeometry

theorem survival_after_firstPassage_iff (level δ : ℝ) (hδ : 0 < δ)
    (T : ℝ≥0) (f : Path) (hstart : level < f 0)
    (hfin : firstPassage level f ≠ ⊤) (ht : passageTime level f ≤ T) :
    f ∈ survival (level-δ) T ↔
      passageFuture level f ∈ survival (-δ) (remainingTime T (realTime level f)) := by
  rw [remainingTime_realTime T level f ht,mem_survival_iff,mem_survival_iff]
  have hh : f (passageTime level f) = level := firstPassage_exact_level level f hstart hfin
  constructor
  · intro hf u hu
    have hb : passageTime level f+u ≤ T := by
      simpa only [add_comm] using (le_tsub_iff_right ht).mp hu
    have he := hf (passageTime level f+u) hb
    rw [passageFuture,futurePath_eval,hh]
    linarith
  · intro hf r hr
    rcases lt_or_ge r (passageTime level f) with hlt | hle
    · have he : (r : ℝ≥0∞) < firstPassage level f := by
        rw [← ENNReal.coe_toNNReal hfin]
        exact ENNReal.coe_lt_coe.mpr hlt
      exact (by linarith : level-δ < level).trans (before_firstPassage level f r he)
    · have hsub : r-passageTime level f ≤ T-passageTime level f :=
        tsub_le_tsub_right hr _
      have he := hf (r-passageTime level f) hsub
      rw [passageFuture,futurePath_eval,add_tsub_cancel_of_le hle,hh] at he
      linarith

def futureSurvival (δ : ℝ) (T : ℝ≥0) : Set (ℝ × Path) :=
  {p | p.2 ∈ survival (-δ) (remainingTime T p.1)}

theorem measurableSet_futureSurvival (δ : ℝ) (T : ℝ≥0) :
    MeasurableSet (futureSurvival δ T) := by
  have ht : Measurable (fun p : ℝ × Path ↦ (remainingTime T p.1 : ℝ≥0∞)) :=
    ENNReal.continuous_coe.measurable.comp
      ((continuous_remainingTime T).measurable.comp measurable_fst)
  have hf : Measurable (fun p : ℝ × Path ↦ firstPassage (-δ) p.2) :=
    (measurable_firstPassage (-δ)).comp measurable_snd
  have he : futureSurvival δ T =
      {p : ℝ × Path | (remainingTime T p.1 : ℝ≥0∞) < firstPassage (-δ) p.2} := by
    ext p
    exact mem_survival_iff_firstPassage (-δ) (remainingTime T p.1) p.2
  rw [he]
  exact measurableSet_lt ht hf

theorem ae_survival_after_firstPassage_iff (level : ℝ) (hlevel : level < 0)
    (δ : ℝ) (hδ : 0 < δ) (T : ℝ≥0) :
    ∀ᵐ f ∂pathLaw, realTime level f < (T : ℝ) →
      (f ∈ survival (level-δ) T ↔
        (realTime level f,passageFuture level f) ∈ futureSurvival δ T) := by
  filter_upwards [ae_firstPassage_ne_top level hlevel,
    isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hfin h0
  intro ht
  apply survival_after_firstPassage_iff level δ hδ T f (by simpa only [h0] using hlevel) hfin
  exact_mod_cast ht.le

end PerronWright.BrownianFirstPassageMinimumWindowGeometry
