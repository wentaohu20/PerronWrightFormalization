import PerronWright.Probability.BrownianPathLaw
import PerronWright.Probability.ContinuousPathReflection
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Continuous path operations and the actual reflected Brownian law

Running minima, reflection and parabolic drift are literal operations on
the actual compact-open continuous-path space. Joint continuity of the
minimum follows by minimizing over the rescaled fixed compact interval.
The ensuing probability measures are genuine pushforwards of the proved
Brownian path law, and agree with the actual sampled-process reflection.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Classical NNReal ENNReal BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianPathReflectionLaw

open BrownianGaussianSkeleton BrownianContinuousModification BrownianPathLaw
open ContinuousPathReflection

def minimumPath (f : Path) : Path :=
  (⟨runningMinimum f,continuous_runningMinimum (continuous_path f)⟩ : C(ℝ≥0,ℝ))

def reflectionPath (f : Path) : Path :=
  (⟨reflected f,continuous_reflected (continuous_path f)⟩ : C(ℝ≥0,ℝ))

def driftPath (lambda : ℝ) (f : Path) : Path :=
  (⟨parabolicDrift lambda f,continuous_parabolicDrift (continuous_path f) lambda⟩ : C(ℝ≥0,ℝ))

def driftedReflectionPath (lambda : ℝ) (f : Path) : Path := reflectionPath (driftPath lambda f)

@[simp] theorem minimumPath_apply (f : Path) (t : ℝ≥0) : minimumPath f t = runningMinimum f t := rfl
@[simp] theorem reflectionPath_apply (f : Path) (t : ℝ≥0) : reflectionPath f t = reflected f t := rfl
@[simp] theorem driftPath_apply (lambda : ℝ) (f : Path) (t : ℝ≥0) :
    driftPath lambda f t = f t + lambda * (t : ℝ) - (t : ℝ) ^ 2 / 2 := rfl

/-- The minimum is continuous jointly in the actual path and the time,
not merely continuous separately in time for a fixed path. -/
theorem continuous_joint_minimum :
    Continuous (fun p : Path × ℝ≥0 ↦ runningMinimum p.1 p.2) := by
  have hc : Continuous (fun p : (Path × ℝ≥0) × ℝ≥0 ↦ p.1.1 (p.1.2 * p.2)) :=
    (continuous_fst.fst).eval (continuous_fst.snd.mul continuous_snd)
  have hm := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) 1)).continuous_sInf
    (f := fun p : Path × ℝ≥0 ↦ fun u : ℝ≥0 ↦ p.1 (p.2 * u)) hc
  have he : (fun p : Path × ℝ≥0 ↦ sInf ((fun u ↦ p.1 (p.2 * u)) '' Set.Icc 0 1)) =
      (fun p : Path × ℝ≥0 ↦ runningMinimum p.1 p.2) := by
    funext p
    exact congrArg sInf (rescaled_image p.1 p.2).symm
  rw [he] at hm
  exact hm

/-- Genuine continuity for the compact-open / locally uniform topology. -/
theorem continuous_minimumPath : Continuous minimumPath :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_joint_minimum

theorem continuous_reflectionPath : Continuous reflectionPath :=
  ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_joint_eval.sub continuous_joint_minimum)

theorem continuous_driftPath : Continuous (fun p : ℝ × Path ↦ driftPath p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((continuous_fst.snd.eval continuous_snd).add
    (continuous_fst.fst.mul (NNReal.continuous_coe.comp continuous_snd))).sub
    (((NNReal.continuous_coe.comp continuous_snd).pow 2).div_const 2)

theorem continuous_driftedReflectionPath : Continuous (fun p : ℝ × Path ↦ driftedReflectionPath p.1 p.2) :=
  continuous_reflectionPath.comp continuous_driftPath

theorem measurable_minimumPath : Measurable minimumPath := continuous_minimumPath.measurable
theorem measurable_reflectionPath : Measurable reflectionPath := continuous_reflectionPath.measurable
theorem measurable_driftedReflectionPath (lambda : ℝ) : Measurable (driftedReflectionPath lambda) :=
  (continuous_driftedReflectionPath.comp (continuous_const.prodMk continuous_id)).measurable

def minimumLaw : Measure Path := pathLaw.map minimumPath
def reflectionLaw : Measure Path := pathLaw.map reflectionPath
def driftedReflectionLaw (lambda : ℝ) : Measure Path := pathLaw.map (driftedReflectionPath lambda)

instance : IsProbabilityMeasure minimumLaw := Measure.isProbabilityMeasure_map measurable_minimumPath.aemeasurable
instance : IsProbabilityMeasure reflectionLaw := Measure.isProbabilityMeasure_map measurable_reflectionPath.aemeasurable
instance (lambda : ℝ) : IsProbabilityMeasure (driftedReflectionLaw lambda) :=
  Measure.isProbabilityMeasure_map (measurable_driftedReflectionPath lambda).aemeasurable

theorem hasLaw_actual_reflectionPath :
    HasLaw (fun x ↦ reflectionPath (measurablePath x)) reflectionLaw rationalLaw := by
  exact (show HasLaw reflectionPath reflectionLaw pathLaw from ⟨measurable_reflectionPath.aemeasurable,rfl⟩).fun_comp
    hasLaw_measurablePath

theorem hasLaw_actual_driftedReflectionPath (lambda : ℝ) :
    HasLaw (fun x ↦ driftedReflectionPath lambda (measurablePath x)) (driftedReflectionLaw lambda) rationalLaw := by
  exact (show HasLaw (driftedReflectionPath lambda) (driftedReflectionLaw lambda) pathLaw from
    ⟨(measurable_driftedReflectionPath lambda).aemeasurable,rfl⟩).fun_comp hasLaw_measurablePath

theorem reflectionLaw_eq_map_rationalLaw :
    reflectionLaw = rationalLaw.map (fun x ↦ reflectionPath (measurablePath x)) :=
  hasLaw_actual_reflectionPath.map_eq.symm

theorem driftedReflectionLaw_eq_map_rationalLaw (lambda : ℝ) :
    driftedReflectionLaw lambda = rationalLaw.map (fun x ↦ driftedReflectionPath lambda (measurablePath x)) :=
  (hasLaw_actual_driftedReflectionPath lambda).map_eq.symm

/-- The actual reflected path agrees at all real times simultaneously
with the literal running-minimum reflection of the original process. -/
theorem ae_all_actual_reflection_eq : ∀ᵐ x ∂rationalLaw, ∀ t : ℝ≥0,
    reflectionPath (measurablePath x) t = reflected (fun s ↦ process s x) t := by
  filter_upwards [ae_all_measurablePath_eval] with x hx
  intro t
  exact congrArg (fun f : ℝ≥0 → ℝ ↦ reflected f t) (funext hx)

theorem ae_all_actual_driftedReflection_eq : ∀ᵐ x ∂rationalLaw, ∀ lambda : ℝ, ∀ t : ℝ≥0,
    driftedReflectionPath lambda (measurablePath x) t =
      reflected (parabolicDrift lambda (fun s ↦ process s x)) t := by
  filter_upwards [ae_all_measurablePath_eval] with x hx
  intro lambda t
  exact congrArg (fun f : ℝ≥0 → ℝ ↦ reflected (parabolicDrift lambda f) t) (funext hx)

theorem aemeasurable_actual_reflection (t : ℝ≥0) :
    AEMeasurable (fun x ↦ reflected (fun s ↦ process s x) t) rationalLaw := by
  have hm : Measurable (fun x ↦ reflectionPath (measurablePath x) t) :=
    (continuous_eval t).measurable.comp (measurable_reflectionPath.comp measurable_measurablePath)
  exact hm.aemeasurable.congr (ae_all_actual_reflection_eq.mono (fun _ hx ↦ hx t))

theorem aemeasurable_actual_driftedReflection (lambda : ℝ) (t : ℝ≥0) :
    AEMeasurable (fun x ↦ reflected (parabolicDrift lambda (fun s ↦ process s x)) t) rationalLaw := by
  have hm : Measurable (fun x ↦ driftedReflectionPath lambda (measurablePath x) t) :=
    (continuous_eval t).measurable.comp ((measurable_driftedReflectionPath lambda).comp measurable_measurablePath)
  exact hm.aemeasurable.congr (ae_all_actual_driftedReflection_eq.mono (fun _ hx ↦ hx lambda t))

/-- A genuine jointly measurable surface representative, including the
random sample, the drift parameter, and the real time. It agrees with
the literal sampled reflection for all parameters on the same full set. -/
theorem measurable_actual_driftedReflectionField : Measurable
    (fun p : ((ℕ → ℝ) × ℝ) × ℝ≥0 ↦
      driftedReflectionPath p.1.2 (measurablePath p.1.1) p.2) := by
  exact continuous_joint_eval.measurable.comp
    ((continuous_driftedReflectionPath.measurable.comp
      (measurable_fst.snd.prodMk (measurable_measurablePath.comp measurable_fst.fst))).prodMk measurable_snd)

theorem reflectionPath_nonneg (f : Path) (t : ℝ≥0) : 0 ≤ reflectionPath f t :=
  reflected_nonneg (continuous_path f) t

theorem reflectionLaw_integral (F : Path →ᵇ ℝ) :
    (∫ f, F f ∂reflectionLaw) = (∫ x, F (reflectionPath (measurablePath x)) ∂rationalLaw) := by
  simpa only [Function.comp_def] using
    (hasLaw_actual_reflectionPath.integral_comp F.continuous.aestronglyMeasurable).symm

theorem driftedReflectionLaw_integral (lambda : ℝ) (F : Path →ᵇ ℝ) :
    (∫ f, F f ∂driftedReflectionLaw lambda) =
      (∫ x, F (driftedReflectionPath lambda (measurablePath x)) ∂rationalLaw) := by
  simpa only [Function.comp_def] using
    ((hasLaw_actual_driftedReflectionPath lambda).integral_comp F.continuous.aestronglyMeasurable).symm

end PerronWright.BrownianPathReflectionLaw
