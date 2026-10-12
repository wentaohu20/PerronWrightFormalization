import PerronWright.Probability.BrownianFirstPassageMinimumWindowFutureLevelIntegral
import PerronWright.Probability.ContinuousPathMinimumFutureBandAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Literal normalized minimum windows are truncated unit bands

This is a deterministic change of variables for the actual level/path
window, retaining the entire future at first passage. The negative-level
restriction becomes an explicit truncation inside the unit band.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumWindowLevelAverage

open BrownianPathLaw ContinuousPathFirstPassage ContinuousPathLeastMinimum
open BrownianFirstPassageUncappedLaw BrownianFirstPassageMinimumWindowLevelIntegral
open BrownianFirstPassageMinimumWindowFutureLevelIntegral

def levelPoint (a : ℝ) (f : Path) : ℝ≥0 × ℝ × Path :=
  (passageTime (-a) f,-a,passageFuture (-a) f)

theorem measurable_joint_levelPoint :
    Measurable (fun p : ℝ × Path ↦ levelPoint p.1 p.2) := by
  have hp : Measurable (fun p : ℝ × Path ↦ (-p.1,p.2)) :=
    measurable_fst.neg.prodMk measurable_snd
  exact (measurable_joint_firstPassage.ennreal_toNNReal.comp hp).prodMk
    (measurable_fst.neg.prodMk (measurable_joint_passageFuture.comp hp))

def windowSet (δ : ℝ) (T : ℝ≥0) : Set (ℝ × Path) :=
  {p | firstPassage (-p.1) p.2 < (T : ℝ≥0∞) ∧ p.2 ∈ survival (-p.1-δ) T}

theorem measurableSet_windowSet (δ : ℝ) (T : ℝ≥0) : MeasurableSet (windowSet δ T) := by
  have hτ := measurable_joint_firstPassage.comp (measurable_fst.neg.prodMk measurable_snd)
  have hs : MeasurableSet {p : ℝ × Path | p.2 ∈ survival (-p.1-δ) T} := by
    change MeasurableSet {p : ℝ × Path | -p.1-δ <
      ContinuousPathReflection.runningMinimum p.2 T}
    exact measurableSet_lt (measurable_fst.neg.sub_const δ)
      ((continuous_minimum_at T).measurable.comp measurable_snd)
  exact (hτ measurableSet_Iio).inter hs

def windowLevelTest (δ : ℝ) (T : ℝ≥0) (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) :
    ℝ × Path → ℝ :=
  (windowSet δ T).indicator (fun p ↦ Ψ (levelPoint p.1 p.2))

theorem measurable_windowLevelTest (δ : ℝ) (T : ℝ≥0)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) : Measurable (windowLevelTest δ T Ψ) :=
  (Ψ.continuous.measurable.comp measurable_joint_levelPoint).indicator
    (measurableSet_windowSet δ T)

theorem windowLevelTest_eq_band (δ : ℝ) (T : ℝ≥0)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (f : Path)
    (hinterior : leastMinimizer T f < T) (a : ℝ) :
    windowLevelTest δ T Ψ (a,f) =
      (Ioc (-minimumValue T f-δ) (-minimumValue T f)).indicator
        (fun a ↦ Ψ (levelPoint a f)) a := by
  have hτ : firstPassage (-a) f < (T : ℝ≥0∞) ↔ a ≤ -minimumValue T f := by
    rw [firstPassage_lt_iff_minimum_of_interior T f hinterior]
    constructor <;> intro h <;> linarith
  have hs : f ∈ survival (-a-δ) T ↔ -minimumValue T f-δ < a := by
    change -a-δ < minimumValue T f ↔ _
    constructor <;> intro h <;> linarith
  simp only [windowLevelTest,windowSet,Set.indicator,mem_ofPred_eq,hτ,hs,mem_Ioc]
  simp only [and_comm]

def levelWindowAverage (T : ℝ≥0) (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ)
    (δ : ℝ) (f : Path) : ℝ :=
  δ⁻¹ * ∫ a : ℝ in Ioi 0, windowLevelTest δ T Ψ (a,f)

def truncatedUnitBandAverage (T : ℝ≥0) (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ)
    (δ : ℝ) (f : Path) : ℝ :=
  ∫ θ : ℝ in Ioc 0 1,
    if minimumValue T f+δ*θ < 0 then
      Ψ (ContinuousPathMinimumFutureBandAverage.bandPoint T δ f θ) else 0

theorem levelWindowAverage_eq_truncated (T : ℝ≥0)
    (Ψ : (ℝ≥0 × ℝ × Path) →ᵇ ℝ) (δ : ℝ) (hδ : 0 < δ) (f : Path)
    (hinterior : leastMinimizer T f < T) :
    levelWindowAverage T Ψ δ f = truncatedUnitBandAverage T Ψ δ f := by
  let A : ℝ := -minimumValue T f
  let F : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun a ↦ Ψ (levelPoint a f))
  have he : (fun a : ℝ ↦ windowLevelTest δ T Ψ (a,f)) =
      (Ioc (A-δ) A).indicator (fun a ↦ Ψ (levelPoint a f)) :=
    funext (windowLevelTest_eq_band δ T Ψ f hinterior)
  have hswap : (∫ a : ℝ in Ioi 0, (Ioc (A-δ) A).indicator
      (fun a ↦ Ψ (levelPoint a f)) a) = ∫ a : ℝ in Ioc (A-δ) A, F a := by
    rw [integral_indicator measurableSet_Ioc]
    change (∫ a : ℝ, Ψ (levelPoint a f)
      ∂(volume.restrict (Ioi 0)).restrict (Ioc (A-δ) A)) = _
    rw [Measure.restrict_restrict measurableSet_Ioc]
    change _ = ∫ a : ℝ in Ioc (A-δ) A, (Ioi (0 : ℝ)).indicator
      (fun a ↦ Ψ (levelPoint a f)) a
    rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
    rw [inter_comm]
  have haff : (∫ θ : ℝ in Ioc 0 1, F (A-δ*θ)) =
      δ⁻¹ * ∫ a : ℝ in Ioc (A-δ) A, F a := by
    have h := intervalIntegral.integral_comp_sub_mul F (a := (0 : ℝ)) (b := 1)
      (ne_of_gt hδ) A
    simp only [mul_one,mul_zero,sub_zero] at h
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by linarith : A-δ ≤ A)] at h
    exact h
  have hg (θ : ℝ) : F (A-δ*θ) =
      if minimumValue T f+δ*θ < 0 then
        Ψ (ContinuousPathMinimumFutureBandAverage.bandPoint T δ f θ) else 0 := by
    have hl : -(A-δ*θ) = minimumValue T f+δ*θ := by dsimp [A]; ring
    have hc : 0 < A-δ*θ ↔ minimumValue T f+δ*θ < 0 := by dsimp [A]; constructor <;> intro h <;> linarith
    simp only [F,Set.indicator,mem_Ioi,hc,levelPoint,
      ContinuousPathMinimumFutureBandAverage.bandPoint,hl]
  rw [levelWindowAverage,he,hswap,← haff,truncatedUnitBandAverage]
  apply integral_congr_ae
  exact Eventually.of_forall hg

end PerronWright.BrownianMinimumWindowLevelAverage
