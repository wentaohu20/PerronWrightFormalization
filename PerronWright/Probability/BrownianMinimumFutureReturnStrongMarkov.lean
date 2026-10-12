import PerronWright.Probability.BrownianMinimumFutureReturnPathGeometry

/-! # Actual whole-future Brownian law after the entrance source return

The true unit-prefix/fresh-Brownian product is stopped at the negative
of its actual random endpoint height. The proved Brownian first-passage
product and genuine passage finiteness are integrated over that prefix.
Literal stopped-path reconstruction then yields the full return product.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumFutureReturnStrongMarkov

open BrownianPathLaw BrownianPathIndependentIncrements BrownianFirstPassagePastFibers
open BrownianMinimumFutureEntranceSource BrownianMinimumFuturePostUnit
open BrownianMinimumFutureFirstReturn BrownianMinimumFutureReturnPathGeometry
open BrownianFirstPassageUncappedLaw ContinuousPathFirstPassage

private def rebuiltPast (q : Path × Path) : ℝ≥0 × Path :=
  (1+passageTime (-q.1 1) q.2,
    splicePath 1 (q.1,pastPath (passageTime (-q.1 1) q.2) q.2))

private def rebuiltFuture (q : Path × Path) : Path := passageFuture (-q.1 1) q.2

private theorem measurable_joint_passageTime :
    Measurable (fun q : Path × Path ↦ passageTime (-q.1 1) q.2) :=
  (measurable_joint_firstPassage.comp
    (((continuous_eval 1).measurable.comp measurable_fst).neg.prodMk measurable_snd)).ennreal_toNNReal

private theorem measurable_rebuiltPast : Measurable rebuiltPast :=
  (measurable_const.add measurable_joint_passageTime).prodMk
    ((measurable_splicePath 1).comp (measurable_fst.prodMk
      (continuous_joint_pastPath.measurable.comp (measurable_joint_passageTime.prodMk measurable_snd))))

private theorem measurable_rebuiltFuture : Measurable rebuiltFuture :=
  continuous_joint_futurePath.measurable.comp (measurable_joint_passageTime.prodMk measurable_snd)

private def insertStopped (p : Path) (q : ℝ≥0 × Path) : ℝ≥0 × Path :=
  (1+q.1,splicePath 1 (p,q.2))

private theorem measurable_insertStopped (p : Path) : Measurable (insertStopped p) :=
  (measurable_const.add measurable_fst).prodMk
    ((measurable_splicePath 1).comp (measurable_const.prodMk measurable_snd))

private theorem fixed_prefix_passage_lintegral (p : Path) (hp : 0 < p 1)
    {Ψ : (ℝ≥0 × Path) × Path → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ h : Path, Ψ (rebuiltPast (p,h),rebuiltFuture (p,h)) ∂pathLaw) =
      ∫⁻ h : Path, ∫⁻ k : Path, Ψ (rebuiltPast (p,h),k) ∂pathLaw ∂pathLaw := by
  let Φ : (ℝ≥0 × Path) × Path → ℝ≥0∞ := fun q ↦ Ψ (insertStopped p q.1,q.2)
  have hΦ : Measurable Φ := hΨ.comp
    (((measurable_insertStopped p).comp measurable_fst).prodMk measurable_snd)
  have hi : Measurable (fun q : ℝ≥0 × Path ↦ ∫⁻ k : Path, Φ (q,k) ∂pathLaw) :=
    hΦ.lintegral_prod_right'
  have hj := (measurable_passagePast (-p 1)).prodMk (measurable_passageFuture (-p 1))
  have he : pathLaw.map (fun h ↦ (passagePast (-p 1) h,passageFuture (-p 1) h)) =
      (pathLaw.map (passagePast (-p 1))).prod pathLaw :=
    passage_jointLaw_of_ae_finite (-p 1)
      (BrownianFirstPassageZeroDrift.ae_firstPassage_ne_top (-p 1) (neg_neg_of_pos hp))
  change (∫⁻ h : Path, Φ (passagePast (-p 1) h,passageFuture (-p 1) h) ∂pathLaw) =
    ∫⁻ h : Path, ∫⁻ k : Path, Φ (passagePast (-p 1) h,k) ∂pathLaw ∂pathLaw
  rw [← lintegral_map hΦ hj,he,lintegral_prod _ hΦ.aemeasurable]
  exact lintegral_map hi (measurable_passagePast (-p 1))

private theorem rebuilt_jointLaw :
    ((unitSourceLaw.map (pastPath 1)).prod pathLaw).map
        (fun q ↦ (rebuiltPast q,rebuiltFuture q)) =
      (((unitSourceLaw.map (pastPath 1)).prod pathLaw).map rebuiltPast).prod pathLaw := by
  let μ := unitSourceLaw.map (pastPath 1)
  let : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (measurable_pastPath 1).aemeasurable
  have hp : ∀ᵐ p : Path ∂μ, 0 < p 1 := by
    apply (ae_map_iff (measurable_pastPath 1).aemeasurable
      (measurableSet_lt measurable_const (continuous_eval 1).measurable)).mpr
    simpa only [pastPath_eval,min_self] using ae_unitSourceLaw_endpoint_pos
  apply Measure.ext_of_lintegral
  intro Ψ hΨ
  have hi : Measurable (fun q : ℝ≥0 × Path ↦ ∫⁻ k : Path, Ψ (q,k) ∂pathLaw) :=
    hΨ.lintegral_prod_right'
  rw [lintegral_map hΨ (measurable_rebuiltPast.prodMk measurable_rebuiltFuture),
    lintegral_prod _ hΨ.aemeasurable,lintegral_map hi measurable_rebuiltPast]
  have hl := lintegral_prod (μ := μ) (ν := pathLaw)
    (fun q : Path × Path ↦ Ψ (rebuiltPast q,rebuiltFuture q))
    (hΨ.comp (measurable_rebuiltPast.prodMk measurable_rebuiltFuture)).aemeasurable
  have hr := lintegral_prod (μ := μ) (ν := pathLaw)
    (fun q : Path × Path ↦ ∫⁻ k : Path, Ψ (rebuiltPast q,k) ∂pathLaw)
    (hi.comp measurable_rebuiltPast).aemeasurable
  rw [hl,hr]
  apply lintegral_congr_ae
  filter_upwards [hp] with p hpos
  exact fixed_prefix_passage_lintegral p hpos hΨ

private theorem ae_rebuiltPast_eq :
    ∀ᵐ g : Path ∂unitSourceLaw,
      rebuiltPast (pastPath 1 g,futurePath 1 g) = returnTaggedPast g := by
  filter_upwards [ae_returnTaggedPast_reconstruction] with g hg
  simpa only [rebuiltPast,pastPath_eval,min_self] using hg.symm

private theorem ae_rebuiltFuture_eq :
    ∀ᵐ g : Path ∂unitSourceLaw,
      rebuiltFuture (pastPath 1 g,futurePath 1 g) = returnFuturePath g := by
  filter_upwards [ae_returnFuturePath_reconstruction] with g hg
  simpa only [rebuiltFuture,pastPath_eval,min_self] using hg.symm

/-- The complete actual stopped excursion, with its literal return time,
is independent of an entire fresh Brownian future. No strong-Markov or
return-finiteness property is assumed as a premise. -/
theorem actual_return_past_future_jointLaw :
    unitSourceLaw.map (fun g : Path ↦ (returnTaggedPast g,returnFuturePath g)) =
      (unitSourceLaw.map returnTaggedPast).prod pathLaw := by
  have hj := (measurable_pastPath 1).prodMk (measurable_futurePath 1)
  have hp : unitSourceLaw.map (fun g : Path ↦ rebuiltPast (pastPath 1 g,futurePath 1 g)) =
      unitSourceLaw.map returnTaggedPast := Measure.map_congr ae_rebuiltPast_eq
  calc
    _ = unitSourceLaw.map (fun g : Path ↦
        (rebuiltPast (pastPath 1 g,futurePath 1 g),rebuiltFuture (pastPath 1 g,futurePath 1 g))) := by
      apply Measure.map_congr
      filter_upwards [ae_rebuiltPast_eq,ae_rebuiltFuture_eq] with g hgp hgf
      rw [hgp,hgf]
    _ = (((unitSourceLaw.map (pastPath 1)).prod pathLaw).map
        (fun q ↦ (rebuiltPast q,rebuiltFuture q))) := by
      rw [← actual_source_past_future_jointLaw,
        Measure.map_map (measurable_rebuiltPast.prodMk measurable_rebuiltFuture) hj]
      rfl
    _ = (((unitSourceLaw.map (pastPath 1)).prod pathLaw).map rebuiltPast).prod pathLaw :=
      rebuilt_jointLaw
    _ = _ := by
      rw [← actual_source_past_future_jointLaw,Measure.map_map measurable_rebuiltPast hj]
      exact congrArg (fun ν : Measure (ℝ≥0 × Path) ↦ ν.prod pathLaw) hp

theorem actual_return_past_future_lintegral
    {Ψ : (ℝ≥0 × Path) × Path → ℝ≥0∞} (hΨ : Measurable Ψ) :
    (∫⁻ g : Path, Ψ (returnTaggedPast g,returnFuturePath g) ∂unitSourceLaw) =
      ∫⁻ p : ℝ≥0 × Path, ∫⁻ k : Path, Ψ (p,k) ∂pathLaw
        ∂unitSourceLaw.map returnTaggedPast := by
  rw [← lintegral_map' hΨ.aemeasurable
    (aemeasurable_returnTaggedPast.prodMk aemeasurable_returnFuturePath),actual_return_past_future_jointLaw]
  let : IsProbabilityMeasure (unitSourceLaw.map returnTaggedPast) :=
    Measure.isProbabilityMeasure_map aemeasurable_returnTaggedPast
  exact lintegral_prod _ hΨ.aemeasurable

theorem actual_return_future_law : unitSourceLaw.map returnFuturePath = pathLaw := by
  let : IsProbabilityMeasure (unitSourceLaw.map returnTaggedPast) :=
    Measure.isProbabilityMeasure_map aemeasurable_returnTaggedPast
  have he := congrArg (Measure.map (Prod.snd : (ℝ≥0 × Path) × Path → Path))
    actual_return_past_future_jointLaw
  rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
      (aemeasurable_returnTaggedPast.prodMk aemeasurable_returnFuturePath),
    Measure.map_snd_prod,measure_univ,one_smul] at he
  exact he

private theorem measurable_returnSplice :
    Measurable (fun q : (ℝ≥0 × Path) × Path ↦ splicePath q.1.1 (q.1.2,q.2)) := by
  apply Continuous.measurable
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_fst.fst.snd.eval (continuous_snd.min continuous_fst.fst.fst)).add
    (continuous_fst.snd.eval (continuous_snd.sub continuous_fst.fst.fst))

/-- Splicing the actual complete stopped excursion with its independent
fresh Brownian future recovers the actual whole entrance-source law. -/
theorem actual_return_whole_splice_law :
    ((unitSourceLaw.map returnTaggedPast).prod pathLaw).map
      (fun q : (ℝ≥0 × Path) × Path ↦ splicePath q.1.1 (q.1.2,q.2)) = unitSourceLaw := by
  rw [← actual_return_past_future_jointLaw,
    AEMeasurable.map_map_of_aemeasurable measurable_returnSplice.aemeasurable
      (aemeasurable_returnTaggedPast.prodMk aemeasurable_returnFuturePath)]
  change unitSourceLaw.map (fun g : Path ↦ splicePath (firstReturnZero g).toNNReal
    (pastPath (firstReturnZero g).toNNReal g,futurePath (firstReturnZero g).toNNReal g)) = unitSourceLaw
  have he : (fun g : Path ↦ splicePath (firstReturnZero g).toNNReal
      (pastPath (firstReturnZero g).toNNReal g,futurePath (firstReturnZero g).toNNReal g)) = id :=
    funext (fun g ↦ splice_past_future (firstReturnZero g).toNNReal g)
  rw [he,Measure.map_id]

theorem actual_return_whole_lintegral {F : Path → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ g : Path, F g ∂unitSourceLaw) =
      ∫⁻ p : ℝ≥0 × Path, ∫⁻ k : Path, F (splicePath p.1 (p.2,k)) ∂pathLaw
        ∂unitSourceLaw.map returnTaggedPast := by
  let : IsProbabilityMeasure (unitSourceLaw.map returnTaggedPast) :=
    Measure.isProbabilityMeasure_map aemeasurable_returnTaggedPast
  calc
    _ = ∫⁻ g : Path, F g ∂((unitSourceLaw.map returnTaggedPast).prod pathLaw).map
        (fun q : (ℝ≥0 × Path) × Path ↦ splicePath q.1.1 (q.1.2,q.2)) := by
      rw [actual_return_whole_splice_law]
    _ = ∫⁻ q : (ℝ≥0 × Path) × Path, F (splicePath q.1.1 (q.1.2,q.2))
        ∂(unitSourceLaw.map returnTaggedPast).prod pathLaw :=
      lintegral_map hF measurable_returnSplice
    _ = _ := lintegral_prod _ (hF.comp measurable_returnSplice).aemeasurable

end PerronWright.BrownianMinimumFutureReturnStrongMarkov
