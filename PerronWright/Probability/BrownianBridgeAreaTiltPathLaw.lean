import PerronWright.Probability.BrownianBridgeAreaTiltTests
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Full actual pinned-bridge path law under continuous area tilt

Finite dual tests determine all finite bridge laws; projective
uniqueness gives the entire indexed law. A genuine stopped continuous
bridge and the proved rational evaluation measurable embedding lift
this to the compact-open path Borel law. The mean is precisely the
literal pinned parabolic driver at tilt parameter one. This is not
positive-excursion conditioning.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianBridgeAreaTiltPathLaw

open BrownianPathLaw BrownianPinnedBridge BrownianPinnedBridgeFiniteLaw
open BrownianPinnedBridgeArea BrownianPinnedBridgeAreaTilt
open BrownianBridgeAreaCrossKernel BrownianBridgeAreaTiltTests
open BrownianGaussianSkeleton

variable {ι : Type*} [Fintype ι]

theorem finite_bridge_law_areaTilt (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (u : ℝ) :
    (tiltedAreaLaw T u).map (fun f : Path ↦ fun i ↦ bridge T (t i) f) =
      pathLaw.map (fun f : Path ↦ fun i ↦ bridge T (t i) f+u*crossMean T (t i)) := by
  let := tiltedAreaLaw_isProbability T hT u
  have hm : Measurable (fun f : Path ↦ fun i ↦ bridge T (t i) f) :=
    measurable_pi_lambda _ (fun i ↦ (continuous_bridge T (t i)).measurable)
  have hm' : Measurable (fun f : Path ↦ fun i ↦ bridge T (t i) f+u*crossMean T (t i)) :=
    measurable_pi_lambda _ (fun i ↦ (continuous_bridge T (t i)).measurable.add_const _)
  apply Measure.ext_of_charFunDual
  funext L
  let c : ι → ℝ := fun i ↦ L (fun j ↦ if i = j then 1 else 0)
  have hsplit (x : ι → ℝ) : L x = ∑ i, c i*x i := by
    change L.toLinearMap x = _
    rw [LinearMap.pi_apply_eq_sum_univ L.toLinearMap x]
    apply Finset.sum_congr rfl
    intro i _
    change x i*L (fun j ↦ if i = j then 1 else 0) = L (fun j ↦ if i = j then 1 else 0)*x i
    exact mul_comm _ _
  have hleft : HasLaw (fun f : Path ↦ L (fun i ↦ bridge T (t i) f))
      (gaussianReal (u*testCrossMean T t c) (Real.toNNReal (quadraticVariance T t c)))
      (tiltedAreaLaw T u) := by
    have he : (fun f : Path ↦ L (fun i ↦ bridge T (t i) f)) = linearTest T t c := by
      funext f
      exact hsplit _
    rw [he]
    exact hasLaw_linearTest_areaTilt T hT t ht c u
  have hright : HasLaw (fun f : Path ↦ L (fun i ↦ bridge T (t i) f+u*crossMean T (t i)))
      (gaussianReal (u*testCrossMean T t c) (Real.toNNReal (quadraticVariance T t c)))
      pathLaw := by
    have he : (fun f : Path ↦ L (fun i ↦ bridge T (t i) f+u*crossMean T (t i))) =
        (fun f ↦ linearTest T t c f+u*testCrossMean T t c) := by
      funext f
      rw [hsplit]
      simp only [linearTest,testCrossMean,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    simpa only [zero_add] using
      gaussianReal_add_const (hasLaw_linearTest T hT t ht c) (u*testCrossMean T t c)
  rw [charFunDual_apply,charFunDual_apply,integral_map hm.aemeasurable (by fun_prop),
    integral_map hm'.aemeasurable (by fun_prop)]
  simpa only [Function.comp_def] using
    (hleft.integral_comp (f := fun x : ℝ ↦ Complex.exp ((x : ℂ)*Complex.I)) (by fun_prop)).trans
      (hright.integral_comp (f := fun x : ℝ ↦ Complex.exp ((x : ℂ)*Complex.I)) (by fun_prop)).symm

omit [Fintype ι] in
/-- Full indexed law, derived from actual finite tests and projective
uniqueness, for an arbitrary family of times in [0,T]. -/
theorem indexed_bridge_law_areaTilt (T : ℝ≥0) (hT : 0 < T)
    (t : ι → ℝ≥0) (ht : ∀ i, t i ≤ T) (u : ℝ) :
    (tiltedAreaLaw T u).map (fun f : Path ↦ fun i ↦ bridge T (t i) f) =
      pathLaw.map (fun f : Path ↦ fun i ↦ bridge T (t i) f+u*crossMean T (t i)) := by
  let := tiltedAreaLaw_isProbability T hT u
  let X : ι → Path → ℝ := fun i ↦ bridge T (t i)
  let Y : ι → Path → ℝ := fun i f ↦ bridge T (t i) f+u*crossMean T (t i)
  have hm : Measurable (fun f : Path ↦ fun i ↦ X i f) :=
    measurable_pi_lambda _ (fun i ↦ (continuous_bridge T (t i)).measurable)
  have hm' : Measurable (fun f : Path ↦ fun i ↦ Y i f) :=
    measurable_pi_lambda _ (fun i ↦ (continuous_bridge T (t i)).measurable.add_const _)
  have hx := isProjectiveLimit_map (X := X) (P := tiltedAreaLaw T u) hm.aemeasurable
  have hy := isProjectiveLimit_map (X := Y) (P := pathLaw) hm'.aemeasurable
  have he (I : Finset ι) :
      (tiltedAreaLaw T u).map (fun f ↦ I.restrict (X · f)) =
        pathLaw.map (fun f ↦ I.restrict (Y · f)) :=
    finite_bridge_law_areaTilt T hT (fun i : I ↦ t i) (fun i ↦ ht i) u
  simp only [he] at hx
  exact hx.unique hy

omit [Fintype ι] in
theorem whole_bridge_law_areaTilt (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (tiltedAreaLaw T u).map (fun f : Path ↦ fun t : Iic T ↦ bridge T t f) =
      pathLaw.map (fun f : Path ↦ fun t : Iic T ↦ bridge T t f+u*crossMean T t) :=
  indexed_bridge_law_areaTilt T hT (fun t : Iic T ↦ t.val) (fun t ↦ t.property) u

def stoppedBridgePath (T : ℝ≥0) (f : Path) : Path :=
  ⟨fun t ↦ bridge T (min t T) f,
    (continuous_sample_bridge T f).comp (continuous_id.min continuous_const)⟩

def meanPath (T : ℝ≥0) (u : ℝ) : Path :=
  ⟨fun t ↦ u*crossMean T (min t T),by unfold crossMean; fun_prop⟩

def shiftedBridgePath (T : ℝ≥0) (u : ℝ) (f : Path) : Path :=
  ⟨fun t ↦ stoppedBridgePath T f t+meanPath T u t,
    (continuous_path (stoppedBridgePath T f)).add (continuous_path (meanPath T u))⟩

theorem measurable_stoppedBridgePath (T : ℝ≥0) : Measurable (stoppedBridgePath T) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun f : Path ↦ fun q ↦ bridge T (min (rationalTimeReal q) T) f)
  exact measurable_pi_lambda _ (fun q ↦ (continuous_bridge T (min (rationalTimeReal q) T)).measurable)

theorem measurable_shiftedBridgePath (T : ℝ≥0) (u : ℝ) : Measurable (shiftedBridgePath T u) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun f : Path ↦ fun q ↦
    bridge T (min (rationalTimeReal q) T) f+u*crossMean T (min (rationalTimeReal q) T))
  exact measurable_pi_lambda _ (fun q ↦
    (continuous_bridge T (min (rationalTimeReal q) T)).measurable.add_const _)

/-- The actual compact-open continuous path Borel law under the true
signed-area tilt is exactly the deterministic parabolic mean shift. -/
theorem pathLaw_areaTilt_eq_shift (T : ℝ≥0) (hT : 0 < T) (u : ℝ) :
    (tiltedAreaLaw T u).map (stoppedBridgePath T) = pathLaw.map (shiftedBridgePath T u) := by
  apply rationalEval_measurableEmbedding.map_injective
  rw [Measure.map_map continuous_rationalEval.measurable (measurable_stoppedBridgePath T),
    Measure.map_map continuous_rationalEval.measurable (measurable_shiftedBridgePath T u)]
  exact indexed_bridge_law_areaTilt T hT (fun q ↦ min (rationalTimeReal q) T)
    (fun _ ↦ min_le_right _ _) u

theorem shiftedBridgePath_one_eq_pinnedParabolic (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T)
    (f : Path) (t : ℝ≥0) :
    shiftedBridgePath T 1 f t = pinnedParabolic lambda T (min t T) f := by
  rw [pinnedParabolic_eq_bridge lambda T (min t T) hT]
  change bridge T (min t T) f+1*crossMean T (min t T) = _
  simp only [one_mul,crossMean]

/-- The literal parabolically drifted driver pinned at T, stopped at T.
Continuity is proved by its pointwise equality with the genuine shifted
bridge; it is not a positivity-conditioned process. -/
def pinnedParabolicPath (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) (f : Path) : Path :=
  ⟨fun t ↦ pinnedParabolic lambda T (min t T) f,
    (continuous_path (shiftedBridgePath T 1 f)).congr
      (shiftedBridgePath_one_eq_pinnedParabolic lambda T hT f)⟩

theorem pinnedParabolicPath_eq_shift (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    pinnedParabolicPath lambda T hT f = shiftedBridgePath T 1 f := by
  apply ContinuousMap.ext
  intro t
  exact (shiftedBridgePath_one_eq_pinnedParabolic lambda T hT f t).symm

theorem pathLaw_areaTilt_one_eq_pinnedParabolic (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    (tiltedAreaLaw T 1).map (stoppedBridgePath T) = pathLaw.map (pinnedParabolicPath lambda T hT) := by
  have he : pinnedParabolicPath lambda T hT = shiftedBridgePath T 1 :=
    funext (pinnedParabolicPath_eq_shift lambda T hT)
  rw [he]
  exact pathLaw_areaTilt_eq_shift T hT 1

theorem weighted_bridgePathLaw_eq_pinnedParabolic (lambda : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    (pathLaw.withDensity (fun f ↦ ENNReal.ofReal (Real.exp (area T f-(T : ℝ)^3/24)))).map
      (stoppedBridgePath T) = pathLaw.map (pinnedParabolicPath lambda T hT) := by
  have h := pathLaw_areaTilt_one_eq_pinnedParabolic lambda T hT
  rw [tiltedAreaLaw_eq_withDensity T hT 1] at h
  simpa only [one_mul,one_pow,mul_one] using h

theorem hasLaw_bridge_areaTilt (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) (u : ℝ) :
    HasLaw (bridge T t) (gaussianReal (u*crossMean T t)
      (Real.toNNReal ((t : ℝ)*((T : ℝ)-(t : ℝ))/(T : ℝ)))) (tiltedAreaLaw T u) := by
  have he : linearTest T (fun _ : Unit ↦ t) (fun _ ↦ (1 : ℝ)) = bridge T t := by
    funext f
    simp only [linearTest,Fintype.sum_unique,one_mul]
  have hv : quadraticVariance T (fun _ : Unit ↦ t) (fun _ ↦ (1 : ℝ)) =
      (t : ℝ)*((T : ℝ)-(t : ℝ))/(T : ℝ) := by
    rw [← variance_linearTest T hT _ (fun _ ↦ ht),he,variance_bridge T t hT ht]
  have h := hasLaw_linearTest_areaTilt T hT (fun _ : Unit ↦ t) (fun _ ↦ ht) (fun _ ↦ 1) u
  rw [he,hv] at h
  simpa only [testCrossMean,Fintype.sum_unique,one_mul] using h

theorem covariance_bridge_areaTilt (T s t : ℝ≥0) (hT : 0 < T)
    (hs : s ≤ T) (ht : t ≤ T) (u : ℝ) :
    cov[bridge T s,bridge T t;tiltedAreaLaw T u] =
      min (s : ℝ) (t : ℝ)-(s : ℝ)*(t : ℝ)/(T : ℝ) := by
  have hL : HasLaw (stoppedBridgePath T) (pathLaw.map (shiftedBridgePath T u)) (tiltedAreaLaw T u) :=
    ⟨(measurable_stoppedBridgePath T).aemeasurable,pathLaw_areaTilt_eq_shift T hT u⟩
  have hR : HasLaw (shiftedBridgePath T u) (pathLaw.map (shiftedBridgePath T u)) pathLaw :=
    ⟨(measurable_shiftedBridgePath T u).aemeasurable,rfl⟩
  have hcL := hL.covariance_fun_comp (f := fun f : Path ↦ f s) (g := fun f : Path ↦ f t)
    (continuous_eval s).measurable.aemeasurable (continuous_eval t).measurable.aemeasurable
  have hcR := hR.covariance_fun_comp (f := fun f : Path ↦ f s) (g := fun f : Path ↦ f t)
    (continuous_eval s).measurable.aemeasurable (continuous_eval t).measurable.aemeasurable
  have he := hcL.trans hcR.symm
  change cov[fun f ↦ bridge T (min s T) f,fun f ↦ bridge T (min t T) f;tiltedAreaLaw T u] =
    cov[fun f ↦ bridge T (min s T) f+u*crossMean T (min s T),
      fun f ↦ bridge T (min t T) f+u*crossMean T (min t T);pathLaw] at he
  simp only [min_eq_left hs,min_eq_left ht] at he
  rw [he,covariance_add_const_left (bridge_hasGaussianLaw T s).integrable,
    covariance_add_const_right (bridge_hasGaussianLaw T t).integrable,
    covariance_bridge T s t hT hs ht]

end PerronWright.BrownianBridgeAreaTiltPathLaw
