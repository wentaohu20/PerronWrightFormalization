import PerronWright.Probability.BrownianMinimumFutureReturnStrongMarkov
import PerronWright.Probability.BrownianMinimumFutureReturnScaling
import PerronWright.Probability.ContinuousPathPositiveReturnMeasurable
import PerronWright.Probability.BrownianMinimumFutureWholeLaw

/-! # Complete stopped excursion and fresh whole future at every source scale

Actual Brownian dilation transports both the fixed-prefix product and the
literal complete-return product of the genuine minimum-future source.
These are zero-drift source identities. A parabolic continuation after the
prefix changes its physical return; no drifted return is identified with
the zero-drift return by this module.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumFutureScaledStrongMarkov

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathDilationLaw
open BrownianMinimumFutureEntranceSource BrownianMinimumFuturePostUnit
open BrownianMinimumFutureFirstReturn BrownianMinimumFutureReturnPathGeometry
open BrownianMinimumFutureReturnStrongMarkov BrownianMinimumFutureReturnScaling
open ContinuousPathPositiveReturnMeasurable

def sourceLaw (c : ℝ≥0) : Measure Path := unitSourceLaw.map (brownianDilation c)

instance sourceLaw_isProbability (c : ℝ≥0) : IsProbabilityMeasure (sourceLaw c) :=
  Measure.isProbabilityMeasure_map (measurable_brownianDilation c).aemeasurable

theorem pastPath_brownianDilation (c t : ℝ≥0) (hc : 0 < c) (g : Path) :
    pastPath (c*t) (brownianDilation c g) = brownianDilation c (pastPath t g) := by
  apply ContinuousMap.ext
  intro s
  change Real.sqrt (c : ℝ)*g (min s (c*t)/c) = Real.sqrt (c : ℝ)*g (min (s/c) t)
  rw [← min_div_div_right (show (0 : ℝ≥0) ≤ c from bot_le),
    mul_div_cancel_left₀ t (ne_of_gt hc)]

theorem futurePath_brownianDilation (c t : ℝ≥0) (hc : 0 < c) (g : Path) :
    futurePath (c*t) (brownianDilation c g) = brownianDilation c (futurePath t g) := by
  apply ContinuousMap.ext
  intro s
  change Real.sqrt (c : ℝ)*g ((c*t+s)/c)-Real.sqrt (c : ℝ)*g ((c*t)/c) =
    Real.sqrt (c : ℝ)*(g (t+s/c)-g t)
  rw [add_div,mul_div_cancel_left₀ t (ne_of_gt hc)]
  ring

private def scalePast (c : ℝ≥0) (p : ℝ≥0 × Path) : ℝ≥0 × Path :=
  (c*p.1,brownianDilation c p.2)

private theorem measurable_scalePast (c : ℝ≥0) : Measurable (scalePast c) :=
  (measurable_const.mul measurable_fst).prodMk
    ((measurable_brownianDilation c).comp measurable_snd)

theorem returnTaggedPast_brownianDilation (c : ℝ≥0) (hc : 0 < c) (g : Path) :
    returnTaggedPast (brownianDilation c g) =
      (c*(firstReturnZero g).toNNReal,brownianDilation c (pastPath (firstReturnZero g).toNNReal g)) := by
  rw [returnTaggedPast,firstReturnZero_brownianDilation c hc,
    ENNReal.toNNReal_mul,ENNReal.toNNReal_coe,pastPath_brownianDilation c _ hc]

theorem returnFuturePath_brownianDilation (c : ℝ≥0) (hc : 0 < c) (g : Path) :
    returnFuturePath (brownianDilation c g) = brownianDilation c (returnFuturePath g) := by
  rw [returnFuturePath,firstReturnZero_brownianDilation c hc,
    ENNReal.toNNReal_mul,ENNReal.toNNReal_coe,futurePath_brownianDilation c _ hc]
  rfl

theorem actual_scaled_source_past_future_jointLaw (c : ℝ≥0) (hc : 0 < c) :
    (sourceLaw c).map (fun g ↦ (pastPath c g,futurePath c g)) =
      ((sourceLaw c).map (pastPath c)).prod pathLaw := by
  let e : Path × Path → Path × Path := Prod.map (brownianDilation c) (brownianDilation c)
  have he : Measurable e := (measurable_brownianDilation c).prodMap (measurable_brownianDilation c)
  have hp : (sourceLaw c).map (pastPath c) =
      (unitSourceLaw.map (pastPath 1)).map (brownianDilation c) := by
    rw [sourceLaw,Measure.map_map (measurable_pastPath c) (measurable_brownianDilation c),
      Measure.map_map (measurable_brownianDilation c) (measurable_pastPath 1)]
    congr 1
    funext g
    change pastPath c (brownianDilation c g) = brownianDilation c (pastPath 1 g)
    simpa only [mul_one] using pastPath_brownianDilation c 1 hc g
  calc
    _ = unitSourceLaw.map (e ∘ (fun g ↦ (pastPath 1 g,futurePath 1 g))) := by
      rw [sourceLaw,Measure.map_map ((measurable_pastPath c).prodMk (measurable_futurePath c))
        (measurable_brownianDilation c)]
      congr 1
      funext g
      change (pastPath c (brownianDilation c g),futurePath c (brownianDilation c g)) = _
      simp only [e,Function.comp_def,Prod.map_apply]
      simpa only [mul_one] using congrArg₂ Prod.mk
        (pastPath_brownianDilation c 1 hc g) (futurePath_brownianDilation c 1 hc g)
    _ = (unitSourceLaw.map (fun g ↦ (pastPath 1 g,futurePath 1 g))).map e :=
      (Measure.map_map he ((measurable_pastPath 1).prodMk (measurable_futurePath 1))).symm
    _ = _ := by
      rw [actual_source_past_future_jointLaw,← Measure.map_prod_map _ _
        (measurable_brownianDilation c) (measurable_brownianDilation c),
        pathLaw_brownianDilation c hc,← hp]

private theorem measurable_variableSplice :
    Measurable (fun q : (ℝ≥0 × Path) × Path ↦ splicePath q.1.1 (q.1.2,q.2)) := by
  apply Continuous.measurable
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_fst.fst.snd.eval (continuous_snd.min continuous_fst.fst.fst)).add
    (continuous_fst.snd.eval (continuous_snd.sub continuous_fst.fst.fst))

theorem actual_scaled_source_whole_lintegral (c : ℝ≥0) (hc : 0 < c)
    {F : Path → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ g, F g ∂sourceLaw c) =
      ∫⁻ p, ∫⁻ h : Path, F (splicePath c (p,h)) ∂pathLaw ∂(sourceLaw c).map (pastPath c) := by
  let : IsProbabilityMeasure ((sourceLaw c).map (pastPath c)) :=
    Measure.isProbabilityMeasure_map (measurable_pastPath c).aemeasurable
  have hsp : (((sourceLaw c).map (pastPath c)).prod pathLaw).map (splicePath c) = sourceLaw c := by
    rw [← actual_scaled_source_past_future_jointLaw c hc,
      Measure.map_map (measurable_splicePath c) ((measurable_pastPath c).prodMk (measurable_futurePath c))]
    have hid : splicePath c ∘ (fun g ↦ (pastPath c g,futurePath c g)) = id :=
      funext (fun g ↦ splice_past_future c g)
    rw [hid,Measure.map_id]
  calc
    _ = ∫⁻ g, F g ∂(((sourceLaw c).map (pastPath c)).prod pathLaw).map (splicePath c) := by rw [hsp]
    _ = ∫⁻ q : Path × Path, F (splicePath c q)
        ∂((sourceLaw c).map (pastPath c)).prod pathLaw := lintegral_map hF (measurable_splicePath c)
    _ = _ := lintegral_prod _ (hF.comp (measurable_splicePath c)).aemeasurable

theorem actual_scaled_return_past_future_jointLaw (c : ℝ≥0) (hc : 0 < c) :
    (sourceLaw c).map (fun g ↦ (returnTaggedPast g,returnFuturePath g)) =
      ((sourceLaw c).map returnTaggedPast).prod pathLaw := by
  let e : (ℝ≥0 × Path) × Path → (ℝ≥0 × Path) × Path :=
    Prod.map (scalePast c) (brownianDilation c)
  have he : Measurable e := (measurable_scalePast c).prodMap (measurable_brownianDilation c)
  have hj := measurable_returnTaggedPast.prodMk measurable_returnFuturePath
  have hp : (sourceLaw c).map returnTaggedPast =
      (unitSourceLaw.map returnTaggedPast).map (scalePast c) := by
    rw [sourceLaw,Measure.map_map measurable_returnTaggedPast (measurable_brownianDilation c),
      Measure.map_map (measurable_scalePast c) measurable_returnTaggedPast]
    congr 1
    funext g
    exact returnTaggedPast_brownianDilation c hc g
  let : IsProbabilityMeasure (unitSourceLaw.map returnTaggedPast) :=
    Measure.isProbabilityMeasure_map measurable_returnTaggedPast.aemeasurable
  calc
    _ = unitSourceLaw.map (e ∘ (fun g ↦ (returnTaggedPast g,returnFuturePath g))) := by
      rw [sourceLaw,Measure.map_map hj (measurable_brownianDilation c)]
      congr 1
      funext g
      exact congrArg₂ Prod.mk (returnTaggedPast_brownianDilation c hc g)
        (returnFuturePath_brownianDilation c hc g)
    _ = (unitSourceLaw.map (fun g ↦ (returnTaggedPast g,returnFuturePath g))).map e :=
      (Measure.map_map he hj).symm
    _ = _ := by
      rw [actual_return_past_future_jointLaw,← Measure.map_prod_map _ _
        (measurable_scalePast c) (measurable_brownianDilation c),pathLaw_brownianDilation c hc,← hp]

theorem actual_scaled_return_whole_lintegral (c : ℝ≥0) (hc : 0 < c)
    {F : Path → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ g, F g ∂sourceLaw c) =
      ∫⁻ p : ℝ≥0 × Path, ∫⁻ h : Path, F (splicePath p.1 (p.2,h)) ∂pathLaw
        ∂(sourceLaw c).map returnTaggedPast := by
  let : IsProbabilityMeasure ((sourceLaw c).map returnTaggedPast) :=
    Measure.isProbabilityMeasure_map measurable_returnTaggedPast.aemeasurable
  have hsp : (((sourceLaw c).map returnTaggedPast).prod pathLaw).map
      (fun q : (ℝ≥0 × Path) × Path ↦ splicePath q.1.1 (q.1.2,q.2)) = sourceLaw c := by
    rw [← actual_scaled_return_past_future_jointLaw c hc,Measure.map_map measurable_variableSplice
      (measurable_returnTaggedPast.prodMk measurable_returnFuturePath)]
    have hid : (fun q : (ℝ≥0 × Path) × Path ↦ splicePath q.1.1 (q.1.2,q.2)) ∘
        (fun g ↦ (returnTaggedPast g,returnFuturePath g)) = id :=
      funext (fun g ↦ splice_past_future (firstReturnZero g).toNNReal g)
    rw [hid,Measure.map_id]
  calc
    _ = ∫⁻ g, F g ∂(((sourceLaw c).map returnTaggedPast).prod pathLaw).map
        (fun q : (ℝ≥0 × Path) × Path ↦ splicePath q.1.1 (q.1.2,q.2)) := by rw [hsp]
    _ = ∫⁻ q : (ℝ≥0 × Path) × Path, F (splicePath q.1.1 (q.1.2,q.2))
        ∂((sourceLaw c).map returnTaggedPast).prod pathLaw := lintegral_map hF measurable_variableSplice
    _ = _ := lintegral_prod _ (hF.comp measurable_variableSplice).aemeasurable

end PerronWright.BrownianMinimumFutureScaledStrongMarkov
