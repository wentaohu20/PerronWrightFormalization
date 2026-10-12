import PerronWright.Probability.BrownianMinimumSplitLaw
import PerronWright.Probability.BrownianParabolicWholePathTilt

/-! # Actual parabolic whole-path minimum split

The true finite-horizon density is applied to the already proved full
Brownian minimum-split law. The future after the remaining horizon is
given its literal residual parabolic drift. All tests are arbitrary
nonnegative Borel functions; no unbounded weak-limit or conditional
minimum-law premise is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianParabolicMinimumSplitLaw

open BrownianPathLaw BrownianPathIndependentIncrements BrownianPathReflectionLaw
open ContinuousPathLeastMinimum ContinuousPathMinimumSplitBandAverage
open BrownianParabolicWholePathTilt BrownianParabolicDriftTiltGeometry
open BrownianMinimumSplitLaw BrownianMinimumSplitCandidate BrownianPathDilationLaw
open BrownianMinimumFutureEntranceSource BrownianFirstPassageEndpointGeometry

private theorem wholeLift_eval (lambda : ℝ) (T : ℝ≥0) (f : Path) (t : ℝ≥0) :
    wholeLift lambda T f t = f t+(lambda-(T : ℝ))*((t-T : ℝ≥0) : ℝ)-
      ((t-T : ℝ≥0) : ℝ)^2/2 := by
  simp only [wholeLift,shiftedSplice,splicePath_eval,pastPath_eval,
    min_assoc,min_self,driftPath_apply,futurePath_tsub]
  ring

private theorem wholeLift_prefix (lambda : ℝ) (T : ℝ≥0) (f : Path)
    (t : ℝ≥0) (ht : t ≤ T) : wholeLift lambda T f t = f t := by
  rw [wholeLift_eval,tsub_eq_zero_of_le ht]
  simp

private theorem continuous_joint_wholeLift :
    Continuous (fun q : ℝ × (ℝ≥0 × Path) ↦ wholeLift q.1 q.2.1 q.2.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h : Continuous (fun q : (ℝ × (ℝ≥0 × Path)) × ℝ≥0 ↦
      q.1.2.2 q.2+(q.1.1-(q.1.2.1 : ℝ))*((q.2-q.1.2.1 : ℝ≥0) : ℝ)-
        ((q.2-q.1.2.1 : ℝ≥0) : ℝ)^2/2) := by
    exact ((continuous_fst.snd.snd.eval continuous_snd).add
      ((continuous_fst.fst.sub (NNReal.continuous_coe.comp continuous_fst.snd.fst)).mul
        (NNReal.continuous_coe.comp (continuous_snd.sub continuous_fst.snd.fst)))).sub
      (((NNReal.continuous_coe.comp (continuous_snd.sub continuous_fst.snd.fst)).pow 2).div_const 2)
  convert h using 1
  funext q
  exact wholeLift_eval q.1.1 q.1.2.1 q.1.2.2 q.2

private theorem minimumValue_wholeLift (lambda : ℝ) (T : ℝ≥0) (f : Path) :
    minimumValue T (wholeLift lambda T f) = minimumValue T f := by
  unfold minimumValue
  congr 1
  ext x
  constructor <;> rintro ⟨t,ht,rfl⟩
  · exact ⟨t,ht,(wholeLift_prefix lambda T f t ht.2).symm⟩
  · exact ⟨t,ht,wholeLift_prefix lambda T f t ht.2⟩

private theorem leastMinimizer_wholeLift (lambda : ℝ) (T : ℝ≥0) (f : Path) :
    leastMinimizer T (wholeLift lambda T f) = leastMinimizer T f := by
  unfold leastMinimizer
  congr 1
  ext t
  simp only [minimizingTimes,mem_inter_iff,mem_Icc,mem_ofPred_eq,minimumValue_wholeLift]
  by_cases ht : t ≤ T
  · rw [wholeLift_prefix lambda T f t ht]
  · simp only [ht,and_false,false_and]

private theorem pastPath_wholeLift (lambda : ℝ) (T s : ℝ≥0) (f : Path) (hs : s ≤ T) :
    pastPath s (wholeLift lambda T f) = pastPath s f := by
  apply ContinuousMap.ext
  intro t
  change wholeLift lambda T f (min t s) = f (min t s)
  exact wholeLift_prefix lambda T f _ ((min_le_right t s).trans hs)

private theorem futurePath_wholeLift (lambda : ℝ) (T s : ℝ≥0) (f : Path) (hs : s ≤ T) :
    futurePath s (wholeLift lambda T f) = wholeLift (lambda-(s : ℝ)) (T-s) (futurePath s f) := by
  apply ContinuousMap.ext
  intro t
  have hsub : (s+t)-T = t-(T-s) := by
    calc
      _ = (s+t)-(s+(T-s)) :=
        congrArg (fun u : ℝ≥0 ↦ (s+t)-u) (add_tsub_cancel_of_le hs).symm
      _ = _ := add_tsub_add_eq_tsub_left s t (T-s)
  rw [futurePath_eval,wholeLift_eval,wholeLift_prefix lambda T f s hs,wholeLift_eval,
    futurePath_eval,hsub,NNReal.coe_sub hs]
  ring

def liftSplit (lambda : ℝ) (T : ℝ≥0) (z : (ℝ≥0 × Path) × (ℝ × Path)) :
    (ℝ≥0 × Path) × (ℝ × Path) :=
  (z.1,z.2.1,wholeLift (lambda-(z.1.1 : ℝ)) (T-z.1.1) z.2.2)

theorem measurable_liftSplit (lambda : ℝ) (T : ℝ≥0) : Measurable (liftSplit lambda T) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk
    (continuous_joint_wholeLift.measurable.comp
      ((measurable_const.sub (NNReal.continuous_coe.measurable.comp measurable_fst.fst)).prodMk
        ((measurable_const.sub measurable_fst.fst).prodMk measurable_snd.snd))))

theorem minimumPoint_wholeLift (lambda : ℝ) (T : ℝ≥0) (f : Path) :
    minimumPoint T (wholeLift lambda T f) = liftSplit lambda T (minimumPoint T f) := by
  simp only [minimumPoint,liftSplit,leastMinimizer_wholeLift,minimumValue_wholeLift]
  rw [pastPath_wholeLift lambda T _ f (leastMinimizer_le_time T f),
    futurePath_wholeLift lambda T _ f (leastMinimizer_le_time T f)]

private def reconstruct (z : (ℝ≥0 × Path) × (ℝ × Path)) : Path :=
  splicePath z.1.1 (z.1.2,z.2.2)

private theorem continuous_reconstruct : Continuous reconstruct := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_fst.fst.snd.eval (continuous_snd.min continuous_fst.fst.fst)).add
    (continuous_fst.snd.snd.eval (continuous_snd.sub continuous_fst.fst.fst))

def splitDensity (lambda : ℝ) (T : ℝ≥0) (z : (ℝ≥0 × Path) × (ℝ × Path)) : ℝ≥0∞ :=
  density lambda T (reconstruct z)

theorem measurable_splitDensity (lambda : ℝ) (T : ℝ≥0) : Measurable (splitDensity lambda T) :=
  (measurable_density lambda T).comp continuous_reconstruct.measurable

theorem actual_parabolic_minimum_split_law (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    pathLaw.map (fun f ↦ minimumPoint T (driftPath lambda f)) =
      ((candidateLaw T).withDensity (splitDensity lambda T)).map (liftSplit lambda T) := by
  apply Measure.ext_of_lintegral
  intro Φ hΦ
  have hm := measurable_minimumPoint T
  have hl := measurable_liftSplit lambda T
  have hw := (measurable_splitDensity lambda T).mul (hΦ.comp hl)
  have hd : Measurable (driftPath lambda) :=
    BrownianParabolicFirstPassagePastFibers.measurable_actual_driftPath lambda
  change (∫⁻ z, Φ z ∂pathLaw.map (minimumPoint T ∘ driftPath lambda)) = _
  rw [lintegral_map hΦ (hm.comp hd)]
  change (∫⁻ f, (Φ ∘ minimumPoint T) (driftPath lambda f) ∂pathLaw) = _
  rw [actual_whole_parabolic_lintegral lambda T (hΦ.comp hm),lintegral_map hΦ hl]
  change (∫⁻ f, density lambda T f*Φ (minimumPoint T (wholeLift lambda T f)) ∂pathLaw) =
    ∫⁻ z, (Φ ∘ liftSplit lambda T) z ∂(candidateLaw T).withDensity (splitDensity lambda T)
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_splitDensity lambda T) (hΦ.comp hl),
    ← actual_minimum_split_law T hT]
  change _ = ∫⁻ z, (splitDensity lambda T*(Φ ∘ liftSplit lambda T)) z
    ∂pathLaw.map (minimumPoint T)
  rw [lintegral_map hw hm]
  apply lintegral_congr
  intro f
  rw [minimumPoint_wholeLift]
  simp only [Pi.mul_apply,Function.comp_def,splitDensity,reconstruct,minimumPoint_reconstruct]

theorem actual_parabolic_minimum_split_lintegral (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (Φ : ((ℝ≥0 × Path) × (ℝ × Path)) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ f, Φ (minimumPoint T (driftPath lambda f)) ∂pathLaw) =
      ∫⁻ a in Ioi (0 : ℝ), ∫⁻ p in {p : ℝ≥0 × Path | p.1 < T},
        (ENNReal.ofReal entranceCoefficient*ENNReal.ofReal (1/Real.sqrt ((T : ℝ)-(p.1 : ℝ))))*
          (∫⁻ g, density lambda T (splicePath p.1
            (p.2,brownianDilation (remainingTime T (p.1 : ℝ)) g))*
              Φ (p,-a,wholeLift (lambda-(p.1 : ℝ)) (T-p.1)
                (brownianDilation (remainingTime T (p.1 : ℝ)) g)) ∂unitSourceLaw)
            ∂BrownianFirstPassageMinimumWindowPastFutureLaw.passagePastLaw (-a) := by
  have hm := measurable_minimumPoint T
  have hd : Measurable (driftPath lambda) :=
    BrownianParabolicFirstPassagePastFibers.measurable_actual_driftPath lambda
  have hl := measurable_liftSplit lambda T
  change (∫⁻ f, Φ ((minimumPoint T ∘ driftPath lambda) f) ∂pathLaw) = _
  rw [← lintegral_map hΦ (hm.comp hd)]
  change (∫⁻ z, Φ z ∂pathLaw.map (fun f ↦ minimumPoint T (driftPath lambda f))) = _
  rw [actual_parabolic_minimum_split_law lambda T hT,lintegral_map hΦ hl]
  change (∫⁻ z, (Φ ∘ liftSplit lambda T) z
    ∂(candidateLaw T).withDensity (splitDensity lambda T)) = _
  rw [
    lintegral_withDensity_eq_lintegral_mul _ (measurable_splitDensity lambda T) (hΦ.comp hl)]
  exact lintegral_candidateLaw T _ ((measurable_splitDensity lambda T).mul (hΦ.comp hl))

end PerronWright.BrownianParabolicMinimumSplitLaw
