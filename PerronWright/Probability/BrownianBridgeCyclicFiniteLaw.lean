import PerronWright.Probability.BrownianBridgeCycleKernel
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Genuine cyclic invariance of all indexed pinned-bridge laws

Every rotated coordinate is an explicit finite linear transform of
the actual Brownian bridge. Gaussianity, means, and the cyclic kernel
algebra prove finite-dimensional invariance. Projective uniqueness
then proves the complete indexed law. No bridge-invariance or
Vervaat theorem is used as an interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeCyclicFiniteLaw

open BrownianPathLaw BrownianPinnedBridge BrownianPinnedBridgeFiniteLaw
open BrownianBridgeCycleKernel

def rotation (T s t : ℝ≥0) (f : Path) : ℝ :=
  bridge T (cycleTime T s t) f-bridge T s f

theorem continuous_rotation (T s t : ℝ≥0) : Continuous (rotation T s t) :=
  (continuous_bridge T _).sub (continuous_bridge T s)

theorem rotation_isGaussianProcess (T s : ℝ≥0) : IsGaussianProcess (rotation T s) pathLaw := by
  apply (bridge_isGaussianProcess T).of_isGaussianProcess
  intro t
  let I : Finset ℝ≥0 := {cycleTime T s t,s}
  let L : (I → ℝ) →L[ℝ] ℝ :=
    { toFun x := x ⟨cycleTime T s t,by simp [I]⟩-x ⟨s,by simp [I]⟩
      map_add' x y := by simp; ring
      map_smul' c x := by simp; ring }
  exact ⟨I,L,fun _ ↦ rfl⟩

theorem integral_rotation (T s t : ℝ≥0) : (∫ f, rotation T s t f ∂pathLaw) = 0 := by
  unfold rotation
  rw [integral_sub (bridge_hasGaussianLaw T _).integrable (bridge_hasGaussianLaw T s).integrable,
    integral_bridge,integral_bridge,sub_self]

theorem covariance_rotation (T s t u : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (ht : t ≤ T) (hu : u ≤ T) :
    cov[rotation T s t,rotation T s u;pathLaw] =
      min (t : ℝ) (u : ℝ)-(t : ℝ)*(u : ℝ)/(T : ℝ) := by
  unfold rotation
  rw [covariance_fun_sub_fun_sub (bridge_hasGaussianLaw T _).memLp_two
    (bridge_hasGaussianLaw T s).memLp_two (bridge_hasGaussianLaw T _).memLp_two
    (bridge_hasGaussianLaw T s).memLp_two,
    covariance_bridge T _ _ hT (cycleTime_le T s t hs ht) (cycleTime_le T s u hs hu),
    covariance_bridge T _ s hT (cycleTime_le T s t hs ht) hs,
    covariance_bridge T s _ hT hs (cycleTime_le T s u hs hu),
    covariance_bridge T s s hT hs hs,min_self]
  exact cycle_kernel_identity T s t u hT hs ht hu

variable {ι : Type*} [Fintype ι]

def linearRotationTest (T s : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) (f : Path) : ℝ :=
  ∑ i, c i*rotation T s (t i) f

theorem hasGaussianLaw_linearRotationTest (T s : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) :
    HasGaussianLaw (linearRotationTest T s t c) pathLaw := by
  have h := ((rotation_isGaussianProcess T s).comp_right t).smul c
  convert! h.hasGaussianLaw_fun_sum (I := Finset.univ) using 1

theorem integral_linearRotationTest (T s : ℝ≥0) (t : ι → ℝ≥0) (c : ι → ℝ) :
    (∫ f, linearRotationTest T s t c f ∂pathLaw) = 0 := by
  unfold linearRotationTest
  rw [integral_finsetSum _ (fun i _ ↦
    ((rotation_isGaussianProcess T s).hasGaussianLaw_eval (t i)).integrable.const_mul _)]
  simp only [integral_const_mul,integral_rotation,mul_zero,Finset.sum_const_zero]

theorem variance_linearRotationTest (T s : ℝ≥0) (hT : 0 < T) (hs : s ≤ T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) :
    Var[linearRotationTest T s t c;pathLaw] = quadraticVariance T t c := by
  have hmem (i : ι) : MemLp (fun f ↦ c i*rotation T s (t i) f) 2 pathLaw :=
    ((rotation_isGaussianProcess T s).hasGaussianLaw_eval (t i)).memLp_two.const_mul _
  unfold linearRotationTest
  rw [variance_fun_sum hmem]
  simp only [covariance_const_mul_left,covariance_const_mul_right,
    covariance_rotation T s _ _ hT hs (ht _) (ht _),quadraticVariance]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hasLaw_linearRotationTest (T s : ℝ≥0) (hT : 0 < T) (hs : s ≤ T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (c : ι → ℝ) :
    HasLaw (linearRotationTest T s t c)
      (gaussianReal 0 (Real.toNNReal (quadraticVariance T t c))) pathLaw := by
  refine ⟨(hasGaussianLaw_linearRotationTest T s t c).aemeasurable,?_⟩
  rw [(hasGaussianLaw_linearRotationTest T s t c).map_eq_gaussianReal,
    integral_linearRotationTest,variance_linearRotationTest T s hT hs t ht c]

theorem finite_rotation_law (T s : ℝ≥0) (hT : 0 < T) (hs : s ≤ T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) :
    pathLaw.map (fun f : Path ↦ fun i ↦ rotation T s (t i) f) =
      pathLaw.map (fun f : Path ↦ fun i ↦ bridge T (t i) f) := by
  have hm := measurable_pi_lambda _ (fun i ↦ (continuous_rotation T s (t i)).measurable)
  have hm' := measurable_pi_lambda _ (fun i ↦ (continuous_bridge T (t i)).measurable)
  apply Measure.ext_of_charFunDual
  funext L
  let c : ι → ℝ := fun i ↦ L (fun j ↦ if i=j then 1 else 0)
  have hsplit (x : ι → ℝ) : L x = ∑ i, c i*x i := by
    change L.toLinearMap x = _
    rw [LinearMap.pi_apply_eq_sum_univ L.toLinearMap x]
    apply Finset.sum_congr rfl
    intro i _
    change x i*L (fun j ↦ if i=j then 1 else 0) = L (fun j ↦ if i=j then 1 else 0)*x i
    exact mul_comm _ _
  have hleft : HasLaw (fun f : Path ↦ L (fun i ↦ rotation T s (t i) f))
      (gaussianReal 0 (Real.toNNReal (quadraticVariance T t c))) pathLaw := by
    have he : (fun f : Path ↦ L (fun i ↦ rotation T s (t i) f)) = linearRotationTest T s t c :=
      funext (fun _ ↦ hsplit _)
    rw [he]
    exact hasLaw_linearRotationTest T s hT hs t ht c
  have hright : HasLaw (fun f : Path ↦ L (fun i ↦ bridge T (t i) f))
      (gaussianReal 0 (Real.toNNReal (quadraticVariance T t c))) pathLaw := by
    have he : (fun f : Path ↦ L (fun i ↦ bridge T (t i) f)) = linearTest T t c :=
      funext (fun _ ↦ hsplit _)
    rw [he]
    exact hasLaw_linearTest T hT t ht c
  rw [charFunDual_apply,charFunDual_apply,integral_map hm.aemeasurable (by fun_prop),
    integral_map hm'.aemeasurable (by fun_prop)]
  simpa only [Function.comp_def] using
    (hleft.integral_comp (f := fun x : ℝ ↦ Complex.exp ((x : ℂ)*Complex.I)) (by fun_prop)).trans
      (hright.integral_comp (f := fun x : ℝ ↦ Complex.exp ((x : ℂ)*Complex.I)) (by fun_prop)).symm

omit [Fintype ι] in
theorem indexed_rotation_law (T s : ℝ≥0) (hT : 0 < T) (hs : s ≤ T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) :
    pathLaw.map (fun f : Path ↦ fun i ↦ rotation T s (t i) f) =
      pathLaw.map (fun f : Path ↦ fun i ↦ bridge T (t i) f) := by
  let X : ι → Path → ℝ := fun i ↦ rotation T s (t i)
  let Y : ι → Path → ℝ := fun i ↦ bridge T (t i)
  have hm : Measurable (fun f : Path ↦ fun i ↦ X i f) :=
    measurable_pi_lambda _ (fun i ↦ (continuous_rotation T s (t i)).measurable)
  have hm' : Measurable (fun f : Path ↦ fun i ↦ Y i f) :=
    measurable_pi_lambda _ (fun i ↦ (continuous_bridge T (t i)).measurable)
  have hx := isProjectiveLimit_map (X := X) (P := pathLaw) hm.aemeasurable
  have hy := isProjectiveLimit_map (X := Y) (P := pathLaw) hm'.aemeasurable
  have he (I : Finset ι) : pathLaw.map (fun f ↦ I.restrict (X · f)) =
      pathLaw.map (fun f ↦ I.restrict (Y · f)) :=
    finite_rotation_law T s hT hs (fun i : I ↦ t i) (fun i ↦ ht i)
  simp only [he] at hx
  exact hx.unique hy

end PerronWright.BrownianBridgeCyclicFiniteLaw
