import PerronWright.Probability.BrownianKilledAreaMomentGeometry
import PerronWright.Probability.BrownianKilledAreaMomentSegments
import PerronWright.Probability.BrownianKilledAreaDuhamelGeometry

/-!
# All-order Kac insertion for the actual killed Brownian area moments

The pathwise power identity is integrated against the actual path law.
Tonelli exchanges time and path, and the proved independent-segment law
identifies each time insertion with the real killed transition measure.
All integrals are nonnegative; no moment-finiteness condition is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledAreaMomentRecursion

open BrownianPathLaw BrownianPathIndependentIncrements ContinuousPathFirstPassage
open BrownianKilledAreaGeometry BrownianKilledSemigroup BrownianKilledTransitionKernel
open BrownianKilledAreaMomentGeometry BrownianKilledAreaMomentKernel
open BrownianKilledAreaMomentSegments BrownianKilledAreaDuhamelGeometry

def areaPowerInsertion (level x : ℝ) (T : ℝ≥0) (n : ℕ) (p : ℝ × Path) : ℝ≥0∞ :=
  ENNReal.ofReal ((x-level)+p.2 (Real.toNNReal p.1)) *
    ENNReal.ofReal (shiftedArea level x T p.2-
      shiftedArea level x (Real.toNNReal p.1) p.2) ^ n

theorem measurable_areaPowerInsertion (level x : ℝ) (T : ℝ≥0) (n : ℕ) :
    Measurable (areaPowerInsertion level x T n) := by
  have hh : Measurable (fun p : ℝ × Path ↦ (x-level)+p.2 (Real.toNNReal p.1)) :=
    measurable_const.add (continuous_joint_eval.measurable.comp
      (measurable_snd.prodMk (continuous_real_toNNReal.measurable.comp measurable_fst)))
  have hT : Measurable (fun p : ℝ × Path ↦ shiftedArea level x T p.2) :=
    (measurable_joint_shiftedArea level T).comp (measurable_const.prodMk measurable_snd)
  have hs : Measurable (fun p : ℝ × Path ↦ shiftedArea level x (Real.toNNReal p.1) p.2) :=
    (measurable_time_state_shiftedArea level).comp
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd))
  exact hh.ennreal_ofReal.mul ((hT.sub hs).ennreal_ofReal.pow_const n)

def insertionIntegrand (level x : ℝ) (T : ℝ≥0) (n : ℕ)
    (F : ℝ → ℝ≥0∞) (p : ℝ × Path) : ℝ≥0∞ :=
  BrownianKilledAreaKernel.weight level 0 T x p.2 *
    areaPowerInsertion level x T n p * F (x+p.2 T)

theorem measurable_insertionIntegrand (level x : ℝ) (T : ℝ≥0) (n : ℕ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (insertionIntegrand level x T n F) :=
  (((BrownianKilledAreaKernel.measurable_weight level 0 T x).comp measurable_snd).mul
    (measurable_areaPowerInsertion level x T n)).mul
      (hF.comp (measurable_const.add ((continuous_eval T).measurable.comp measurable_snd)))

theorem momentWeight_endpoint_insertion (level x : ℝ) (T : ℝ≥0) (n : ℕ)
    (F : ℝ → ℝ≥0∞) (f : Path) :
    momentWeight level (n+1) T x f * F (x+f T) =
      ((n+1 : ℕ) : ℝ≥0∞) * ∫⁻ s in Ioc (0 : ℝ) (T : ℝ),
        insertionIntegrand level x T n F (s,f) := by
  by_cases hf : f ∈ survival (level-x) T
  · have hi : (fun s : ℝ ↦ insertionIntegrand level x T n F (s,f)) =
        (fun s : ℝ ↦ areaPowerInsertion level x T n (s,f) * F (x+f T)) := by
      funext s
      simp only [insertionIntegrand,BrownianKilledAreaSemigroup.weight_zero,
        indicator_of_mem hf,one_mul]
    have hb : Measurable (fun s : ℝ ↦ areaPowerInsertion level x T n (s,f)) :=
      (measurable_areaPowerInsertion level x T n).comp
        (measurable_id.prodMk measurable_const)
    rw [momentWeight,indicator_of_mem hf,
      ofReal_shiftedArea_power_insertion_difference level x T f n hf,hi]
    change (((n+1 : ℕ) : ℝ≥0∞) *
        ∫⁻ s in Ioc (0 : ℝ) (T : ℝ), areaPowerInsertion level x T n (s,f)) *
        F (x+f T) = _
    rw [lintegral_mul_const _ hb,mul_assoc]
  · simp only [momentWeight,zero_mul,
      insertionIntegrand,BrownianKilledAreaSemigroup.weight_zero,
      indicator_of_notMem hf,lintegral_zero,mul_zero]

/-- Genuine all-order killed-area Kac insertion.  The moment measure is
the actual surviving Brownian path-area pushforward defined above, and the
intermediate transition is the actual unweighted killed endpoint law. -/
theorem momentLaw_lintegral_insertion (level : ℝ) (T : ℝ≥0) (x : ℝ) (n : ℕ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂momentLaw level (n+1) T x) =
      ((n+1 : ℕ) : ℝ≥0∞) * ∫⁻ s in Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ z, ENNReal.ofReal (z-level) *
          (∫⁻ y, F y ∂momentLaw level n (T-Real.toNNReal s) z)
          ∂transitionLaw level (Real.toNNReal s) x := by
  have hm := measurable_insertionIntegrand level x T n hF
  rw [momentLaw_lintegral level (n+1) T x hF]
  simp_rw [momentWeight_endpoint_insertion]
  rw [lintegral_const_mul _ hm.lintegral_prod_left']
  congr 1
  rw [← lintegral_lintegral_swap
    (f := fun s : ℝ ↦ fun f : Path ↦ insertionIntegrand level x T n F (s,f))
    (μ := volume.restrict (Ioc (0 : ℝ) (T : ℝ))) (ν := pathLaw) hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  let a : ℝ≥0 := Real.toNNReal s
  let b : ℝ≥0 := T-a
  have ha : a ≤ T := Real.toNNReal_le_iff_le_coe.mpr hs.2
  have hab : a+b = T := add_tsub_cancel_of_le ha
  have hrem (f : Path) : shiftedArea level x T f-shiftedArea level x a f =
      shiftedArea level (x+f a) b (futurePath a f) := by
    have h := shiftedArea_add level x a b f
    rw [hab] at h
    linarith only [h]
  have he (f : Path) : insertionIntegrand level x T n F (s,f) =
      BrownianKilledAreaKernel.weight level 0 (a+b) x f *
        ENNReal.ofReal (x+f a-level) *
        ENNReal.ofReal (shiftedArea level (x+f a) b (futurePath a f)) ^ n *
        F (x+f (a+b)) := by
    rw [hab]
    change BrownianKilledAreaKernel.weight level 0 T x f *
        (ENNReal.ofReal ((x-level)+f a) *
          ENNReal.ofReal (shiftedArea level x T f-shiftedArea level x a f) ^ n) *
        F (x+f T) = _
    rw [hrem,show (x-level)+f a = x+f a-level by ring]
    simp only [mul_assoc]
  change (∫⁻ f, insertionIntegrand level x T n F (s,f) ∂pathLaw) =
    ∫⁻ z, ENNReal.ofReal (z-level) *
      (∫⁻ y, F y ∂momentLaw level n b z) ∂transitionLaw level a x
  rw [lintegral_congr he]
  exact lintegral_surviving_future_moment level n a b x hF

theorem momentLaw_apply_insertion (level : ℝ) (T : ℝ≥0) (x : ℝ) (n : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B) :
    momentLaw level (n+1) T x B =
      ((n+1 : ℕ) : ℝ≥0∞) * ∫⁻ s in Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ z, ENNReal.ofReal (z-level) * momentLaw level n (T-Real.toNNReal s) z B
          ∂transitionLaw level (Real.toNNReal s) x := by
  simpa only [lintegral_indicator hB,lintegral_one,Measure.restrict_apply_univ] using
    momentLaw_lintegral_insertion level T x n
      (measurable_const.indicator hB :
        Measurable (B.indicator (fun _ : ℝ ↦ (1 : ℝ≥0∞))))

theorem momentKernel_lintegral_insertion (level : ℝ) (T : ℝ≥0) (x : ℝ) (n : ℕ)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂momentKernel level (n+1) T x) =
      ((n+1 : ℕ) : ℝ≥0∞) * ∫⁻ s in Ioc (0 : ℝ) (T : ℝ),
        ∫⁻ z, ENNReal.ofReal (z-level) *
          (∫⁻ y, F y ∂momentKernel level n (T-Real.toNNReal s) z)
          ∂killedKernel level (Real.toNNReal s) x :=
  momentLaw_lintegral_insertion level T x n hF

theorem momentLaw_succ_zero_duration (level x : ℝ) (n : ℕ) :
    momentLaw level (n+1) 0 x = 0 := by
  ext B hB
  rw [momentLaw_apply_insertion level 0 x n hB]
  simp

end PerronWright.BrownianKilledAreaMomentRecursion
