import PerronWright.Probability.BrownianMinimumFutureEndpointLaw
import PerronWright.Probability.BrownianMinimumFutureFirstReturn
import PerronWright.Probability.BrownianFirstPassageDensityLaw

/-! # Genuine entrance-source return as a random-height Brownian mixture

The true source prefix is retained. Its independent fresh Brownian future
first reaches the negative of the actual endpoint height. The already
proved hitting density and actual endpoint law give the arbitrary Borel
joint test formula; no return or excursion distribution is presumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumFutureReturnMixture

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianMinimumFutureEntranceSource BrownianMinimumFuturePostUnit
open BrownianMinimumFutureFirstReturn BrownianMinimumFutureEndpointLaw
open BrownianFirstPassageDistribution BrownianFirstPassageDensityLaw

private theorem actual_return_real_eq :
    ∀ᵐ g : Path ∂unitSourceLaw,
      (firstReturnZero g).toReal = 1+realTime (-g 1) (futurePath 1 g) := by
  filter_upwards [ae_unitSourceLaw_firstReturn_eq,ae_unitSourceLaw_post_unit_passage_finite]
    with g he hfin
  rw [he,ENNReal.toReal_add (by norm_num) hfin,ENNReal.toReal_one]
  rfl

/-- Arbitrary Borel tests retain the actual prefix and actual return duration.
The mixing density is the true Brownian passage density at its random height. -/
theorem actual_firstReturn_prefix_lintegral {Ψ : Path × ℝ → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ g : Path, Ψ (pastPath 1 g,(firstReturnZero g).toReal) ∂unitSourceLaw) =
      ∫⁻ p : Path, (∫⁻ s : ℝ,
        BrownianFirstPassageDensityGeometry.density (p 1) s*Ψ (p,1+s))
          ∂unitSourceLaw.map (pastPath 1) := by
  let μ := unitSourceLaw.map (pastPath 1)
  let : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (measurable_pastPath 1).aemeasurable
  have hJ : Measurable (fun z : Path × Path ↦ Ψ (z.1,1+realTime (-z.1 1) z.2)) := by
    have hτ : Measurable (fun z : Path × Path ↦ realTime (-z.1 1) z.2) :=
      measurable_coe_nnreal_real.comp (measurable_joint_firstPassage.comp
        (((continuous_eval 1).measurable.comp measurable_fst).neg.prodMk measurable_snd)).ennreal_toNNReal
    exact hΨ.comp (measurable_fst.prodMk (measurable_const.add hτ))
  have hp : ∀ᵐ p : Path ∂μ, 0 < p 1 := by
    apply (ae_map_iff (measurable_pastPath 1).aemeasurable
      (measurableSet_lt measurable_const (continuous_eval 1).measurable)).mpr
    simpa only [pastPath_eval,min_self] using ae_unitSourceLaw_endpoint_pos
  calc
    _ = ∫⁻ g : Path, Ψ (pastPath 1 g,1+realTime (-g 1) (futurePath 1 g)) ∂unitSourceLaw := by
      apply lintegral_congr_ae
      filter_upwards [actual_return_real_eq] with g hg
      rw [hg]
    _ = ∫⁻ z : Path × Path, Ψ (z.1,1+realTime (-z.1 1) z.2) ∂μ.prod pathLaw := by
      rw [← actual_source_past_future_jointLaw,lintegral_map hJ
        ((measurable_pastPath 1).prodMk (measurable_futurePath 1))]
      simp only [pastPath_eval,min_self]
    _ = ∫⁻ p : Path, ∫⁻ h : Path, Ψ (p,1+realTime (-p 1) h) ∂pathLaw ∂μ :=
      lintegral_prod _ hJ.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hp] with p hpos
      exact lintegral_firstPassage_density (p 1) hpos (fun s : ℝ ↦ Ψ (p,1+s))
        (hΨ.comp (measurable_const.prodMk (measurable_const.add measurable_id)))

/-- The literal endpoint/return joint mixture under the actual source.
Nonpositive endpoint heights contribute zero through the proved density. -/
theorem actual_firstReturn_endpoint_lintegral {H : ℝ × ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ g : Path, H (g 1,(firstReturnZero g).toReal) ∂unitSourceLaw) =
      ∫⁻ x : ℝ, endpointDensity x*(∫⁻ s : ℝ,
        BrownianFirstPassageDensityGeometry.density x s*H (x,1+s)) := by
  let Ψ : Path × ℝ → ℝ≥0∞ := fun p ↦ H (p.1 1,p.2)
  have hΨ : Measurable Ψ := hH.comp
    (((continuous_eval 1).measurable.comp measurable_fst).prodMk measurable_snd)
  have h := actual_firstReturn_prefix_lintegral hΨ
  simp only [Ψ,pastPath_eval,min_self] at h
  let F : ℝ → ℝ≥0∞ := fun x ↦ ∫⁻ s : ℝ,
    BrownianFirstPassageDensityGeometry.density x s*H (x,1+s)
  have hF : Measurable F :=
    (BrownianHeatResolvent.measurable_joint_passageDensity.mul
      (hH.comp (measurable_fst.prodMk (measurable_const.add measurable_snd)))).lintegral_prod_right'
  have he : (∫⁻ p : Path, F (p 1) ∂unitSourceLaw.map (pastPath 1)) =
      ∫⁻ g : Path, F (g 1) ∂unitSourceLaw := by
    have hm : Measurable (fun p : Path ↦ F (p 1)) := hF.comp (continuous_eval 1).measurable
    rw [lintegral_map hm (measurable_pastPath 1)]
    simp only [pastPath_eval,min_self]
  change (∫⁻ g : Path, H (g 1,(firstReturnZero g).toReal) ∂unitSourceLaw) =
    ∫⁻ p : Path, F (p 1) ∂unitSourceLaw.map (pastPath 1) at h
  rw [he,actual_endpoint_lintegral hF] at h
  exact h

end PerronWright.BrownianMinimumFutureReturnMixture
