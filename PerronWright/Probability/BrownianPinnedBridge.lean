import PerronWright.Probability.BrownianPathLaw
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-! # Genuine pinned bridge of the constructed Brownian driver

The process is the literal linear transform B(t) - (t/T) B(T) of
the already constructed Brownian path law. Its Gaussian finite laws,
exact covariance, and independence from the endpoint are proved.
Pinning the parabolically drifted driver cancels the lambda term and
leaves the exact t(T-t)/2 mean. This is a distributional foundation,
not an excursion conditioning, Wright area identity, or Aldous density.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianPinnedBridge

open BrownianPathLaw

def bridge (T t : ℝ≥0) (f : Path) : ℝ :=
  f t - (t : ℝ) / (T : ℝ) * f T

theorem continuous_bridge (T t : ℝ≥0) : Continuous (bridge T t) :=
  (continuous_eval t).sub ((continuous_eval T).const_mul ((t : ℝ)/(T : ℝ)))

theorem continuous_sample_bridge (T : ℝ≥0) (f : Path) :
    Continuous (fun t ↦ bridge T t f) :=
  (continuous_path f).sub ((NNReal.continuous_coe.div_const (T : ℝ)).mul continuous_const)

private def augmented (T : ℝ≥0) (i : Option ℝ≥0) (f : Path) : ℝ :=
  match i with
  | none => f T
  | some t => bridge T t f

private theorem augmented_isGaussianProcess (T : ℝ≥0) :
    IsGaussianProcess (augmented T) pathLaw := by
  apply isBrownian_pathLaw.toIsPreBrownianReal.isGaussianProcess.of_isGaussianProcess
  intro i
  cases i with
  | none =>
      let I : Finset ℝ≥0 := {T}
      let L : (I → ℝ) →L[ℝ] ℝ :=
        { toFun x := x ⟨T,by simp [I]⟩
          map_add' x y := by simp
          map_smul' c x := by simp }
      refine ⟨I,L,?_⟩
      intro f
      rfl
  | some t =>
      let I : Finset ℝ≥0 := {t,T}
      let L : (I → ℝ) →L[ℝ] ℝ :=
        { toFun x := x ⟨t,by simp [I]⟩ - (t : ℝ)/(T : ℝ) * x ⟨T,by simp [I]⟩
          map_add' x y := by simp; ring
          map_smul' c x := by simp; ring }
      refine ⟨I,L,?_⟩
      intro f
      rfl

theorem bridge_isGaussianProcess (T : ℝ≥0) : IsGaussianProcess (bridge T) pathLaw :=
  (augmented_isGaussianProcess T).comp_right Option.some

theorem bridge_hasGaussianLaw (T t : ℝ≥0) : HasGaussianLaw (bridge T t) pathLaw :=
  (bridge_isGaussianProcess T).hasGaussianLaw_eval t

theorem integral_bridge (T t : ℝ≥0) : (∫ f, bridge T t f ∂pathLaw) = 0 := by
  unfold bridge
  rw [integral_sub,integral_const_mul,
    isBrownian_pathLaw.toIsPreBrownianReal.integral_eval,
    isBrownian_pathLaw.toIsPreBrownianReal.integral_eval]
  · ring
  · exact isBrownian_pathLaw.toIsPreBrownianReal.integrable_eval t
  · exact (isBrownian_pathLaw.toIsPreBrownianReal.integrable_eval T).const_mul _

private theorem covariance_driver (s t : ℝ≥0) :
    cov[fun f : Path ↦ f s,fun f : Path ↦ f t;pathLaw] = min (s : ℝ) (t : ℝ) := by
  simpa only [NNReal.coe_min] using isBrownian_pathLaw.toIsPreBrownianReal.covariance_eval s t

private theorem driver_memLp_two (t : ℝ≥0) : MemLp (fun f : Path ↦ f t) 2 pathLaw :=
  (isBrownian_pathLaw.toIsPreBrownianReal.isGaussianProcess.hasGaussianLaw_eval t).memLp_two

theorem covariance_bridge_endpoint (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) :
    cov[bridge T t,fun f : Path ↦ f T;pathLaw] = 0 := by
  unfold bridge
  rw [covariance_fun_sub_left (driver_memLp_two t)
    ((driver_memLp_two T).const_mul _) (driver_memLp_two T),
    covariance_const_mul_left,covariance_driver,covariance_driver,
    min_eq_left (show (t : ℝ) ≤ T from ht),min_self]
  have hne : (T : ℝ) ≠ 0 := ne_of_gt (show 0 < (T : ℝ) from hT)
  field_simp
  ring

theorem covariance_bridge (T s t : ℝ≥0) (hT : 0 < T) (hs : s ≤ T) (ht : t ≤ T) :
    cov[bridge T s,bridge T t;pathLaw] =
      min (s : ℝ) (t : ℝ) - (s : ℝ)*(t : ℝ)/(T : ℝ) := by
  unfold bridge
  rw [covariance_fun_sub_fun_sub (driver_memLp_two s)
    ((driver_memLp_two T).const_mul _) (driver_memLp_two t)
    ((driver_memLp_two T).const_mul _)]
  simp only [covariance_const_mul_left,covariance_const_mul_right,covariance_driver,
    min_eq_left (show (s : ℝ) ≤ T from hs),min_eq_right (show (t : ℝ) ≤ T from ht),min_self]
  have hne : (T : ℝ) ≠ 0 := ne_of_gt (show 0 < (T : ℝ) from hT)
  field_simp
  ring

theorem variance_bridge (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) :
    Var[bridge T t;pathLaw] = (t : ℝ)*((T : ℝ)-(t : ℝ))/(T : ℝ) := by
  rw [← covariance_self (continuous_bridge T t).measurable.aemeasurable,
    covariance_bridge T t t hT ht ht,min_self]
  have hne : (T : ℝ) ≠ 0 := ne_of_gt (show 0 < (T : ℝ) from hT)
  field_simp

/-- Exact actual Gaussian marginal, not an assumed bridge law. -/
theorem hasLaw_bridge_eval (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) :
    HasLaw (bridge T t) (gaussianReal 0
      (Real.toNNReal ((t : ℝ)*((T : ℝ)-(t : ℝ))/(T : ℝ)))) pathLaw := by
  refine ⟨(continuous_bridge T t).measurable.aemeasurable,?_⟩
  rw [(bridge_hasGaussianLaw T t).map_eq_gaussianReal,integral_bridge,variance_bridge T t hT ht]

/-- Independence is proved for the entire time-indexed bridge on [0,T],
not only for one selected coordinate. -/
theorem bridge_process_independent_endpoint (T : ℝ≥0) (hT : 0 < T) :
    IndepFun (fun f : Path ↦ fun t : Iic T ↦ bridge T t f) (fun f : Path ↦ f T) pathLaw := by
  let X : Iic T → Path → ℝ := fun t ↦ bridge T t
  let Y : Unit → Path → ℝ := fun _ f ↦ f T
  have hG : IsGaussianProcess (Sum.elim X Y) pathLaw := by
    have he : Sum.elim X Y = augmented T ∘
        (fun i : Sum (Iic T) Unit ↦ match i with | .inl t => some t.val | .inr _ => none) := by
      funext i
      cases i <;> rfl
    rw [he]
    exact (augmented_isGaussianProcess T).comp_right _
  have hI : IndepFun (fun f t ↦ X t f) (fun f t ↦ Y t f) pathLaw :=
    hG.indepFun_of_covariance_eq_zero
      (fun t ↦ (continuous_bridge T t).measurable.aemeasurable)
      (fun _ ↦ (continuous_eval T).measurable.aemeasurable)
      (fun t _ ↦ covariance_bridge_endpoint T t hT t.property)
  simpa only [X,Y,Function.comp_def,id_eq] using hI.comp measurable_id (measurable_pi_apply ())

theorem ae_bridge_zero (T : ℝ≥0) : ∀ᵐ f ∂pathLaw, bridge T 0 f = 0 := by
  simpa only [bridge,NNReal.coe_zero,zero_div,zero_mul,sub_zero] using
    isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero

theorem bridge_endpoint_zero (T : ℝ≥0) (hT : 0 < T) (f : Path) : bridge T T f = 0 := by
  have hne : (T : ℝ) ≠ 0 := ne_of_gt (show 0 < (T : ℝ) from hT)
  simp only [bridge,div_self hne,one_mul,sub_self]

def pinnedParabolic (lambda : ℝ) (T t : ℝ≥0) (f : Path) : ℝ :=
  (f t + lambda*(t : ℝ) - (t : ℝ)^2/2) -
    (t : ℝ)/(T : ℝ)*(f T + lambda*(T : ℝ) - (T : ℝ)^2/2)

theorem pinnedParabolic_eq_bridge (lambda : ℝ) (T t : ℝ≥0) (hT : 0 < T) (f : Path) :
    pinnedParabolic lambda T t f = bridge T t f + (t : ℝ)*((T : ℝ)-(t : ℝ))/2 := by
  have hne : (T : ℝ) ≠ 0 := ne_of_gt (show 0 < (T : ℝ) from hT)
  unfold pinnedParabolic bridge
  field_simp
  ring

/-- Pinning the literal parabolic driver cancels the critical parameter.
This does not condition that driver to be a positive excursion. -/
theorem hasLaw_pinnedParabolic_eval (lambda : ℝ) (T t : ℝ≥0)
    (hT : 0 < T) (ht : t ≤ T) :
    HasLaw (pinnedParabolic lambda T t)
      (gaussianReal ((t : ℝ)*((T : ℝ)-(t : ℝ))/2)
        (Real.toNNReal ((t : ℝ)*((T : ℝ)-(t : ℝ))/(T : ℝ)))) pathLaw := by
  have he : pinnedParabolic lambda T t =
      fun f ↦ bridge T t f + (t : ℝ)*((T : ℝ)-(t : ℝ))/2 :=
    funext (pinnedParabolic_eq_bridge lambda T t hT)
  rw [he]
  simpa only [zero_add] using
    gaussianReal_add_const (hasLaw_bridge_eval T t hT ht) ((t : ℝ)*((T : ℝ)-(t : ℝ))/2)

end PerronWright.BrownianPinnedBridge

