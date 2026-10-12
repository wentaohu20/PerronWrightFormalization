import PerronWright.Probability.BrownianBridgeCycleKernel

/-! # Literal continuous closed-bridge cyclic splicing

The pointwise closed bridge is f(t)-f(0)-(t/T)(f(T)-f(0)).
It agrees with the actual pinned Brownian bridge almost everywhere,
while its endpoints agree for every input path. This makes the cyclic
splice a genuine stopped continuous path, including off the support of
the Brownian probability law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBridgeCyclicPath

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeCycleKernel
open BrownianGaussianSkeleton

def closedBridge (T t : ℝ≥0) (f : Path) : ℝ :=
  bridge T t f-(1-(t : ℝ)/(T : ℝ))*f 0

theorem closedBridge_zero (T : ℝ≥0) (f : Path) : closedBridge T 0 f = 0 := by
  simp [closedBridge,bridge]

theorem closedBridge_endpoint (T : ℝ≥0) (hT : 0 < T) (f : Path) :
    closedBridge T T f = 0 := by
  simp [closedBridge,bridge_endpoint_zero T hT f,div_self (ne_of_gt (show 0 < (T : ℝ) from hT))]

theorem continuous_closedBridge (T t : ℝ≥0) : Continuous (closedBridge T t) :=
  (continuous_bridge T t).sub ((continuous_eval 0).const_mul _)

theorem continuous_sample_closedBridge (T : ℝ≥0) (f : Path) :
    Continuous (fun t ↦ closedBridge T t f) := by
  unfold closedBridge
  exact (continuous_sample_bridge T f).sub
    ((continuous_const.sub (NNReal.continuous_coe.div_const _)).mul continuous_const)

theorem ae_closedBridge_eq_bridge (T : ℝ≥0) :
    ∀ᵐ f ∂pathLaw, ∀ t, closedBridge T t f = bridge T t f := by
  filter_upwards [isBrownian_pathLaw.toIsPreBrownianReal.eval_zero_ae_eq_zero] with f hf
  intro t
  simp [closedBridge,hf]

def stoppedClosedBridgePath (T : ℝ≥0) (f : Path) : Path :=
  ⟨fun t ↦ closedBridge T (min t T) f,
    (continuous_sample_closedBridge T f).comp (continuous_id.min continuous_const)⟩

def cyclicValue (T s t : ℝ≥0) (f : Path) : ℝ :=
  closedBridge T (cycleTime T s t) f-closedBridge T s f

theorem continuous_sample_cyclicValue (T : ℝ≥0) (hT : 0 < T) (s : ℝ≥0) (f : Path) :
    Continuous (fun t ↦ cyclicValue T s t f) := by
  have hp : Continuous (fun t : ℝ≥0 ↦ s+t) := continuous_const.add continuous_id
  have hm : Continuous (fun t : ℝ≥0 ↦ s+t-T) := hp.sub continuous_const
  have hleft : Continuous (fun t ↦ closedBridge T (s+t) f-closedBridge T s f) :=
    ((continuous_sample_closedBridge T f).comp hp).sub continuous_const
  have hright : Continuous (fun t ↦ closedBridge T (s+t-T) f-closedBridge T s f) :=
    ((continuous_sample_closedBridge T f).comp hm).sub continuous_const
  have h := hleft.if_le hright hp (continuous_const : Continuous (fun _ : ℝ≥0 ↦ T)) (fun t ht ↦ by
    simp only [ht,tsub_self,closedBridge_zero,closedBridge_endpoint T hT f])
  apply h.congr
  intro t
  dsimp only [cyclicValue,cycleTime]
  split_ifs <;> rfl

def cyclicBridgePath (T : ℝ≥0) (hT : 0 < T) (s : ℝ≥0) (f : Path) : Path :=
  ⟨fun t ↦ cyclicValue T s (min t T) f,
    (continuous_sample_cyclicValue T hT s f).comp (continuous_id.min continuous_const)⟩

theorem cyclicBridgePath_zero (T : ℝ≥0) (hT : 0 < T) (s : ℝ≥0)
    (hs : s ≤ T) (f : Path) : cyclicBridgePath T hT s f 0 = 0 := by
  change cyclicValue T s (min 0 T) f = 0
  simp [cyclicValue,cycleTime_zero T s hs]

theorem cyclicBridgePath_endpoint (T : ℝ≥0) (hT : 0 < T) (s : ℝ≥0)
    (f : Path) : cyclicBridgePath T hT s f T = 0 := by
  change cyclicValue T s (min T T) f = 0
  simp only [min_self,cyclicValue,cycleTime_endpoint]
  by_cases hs : s=0
  · simp [hs,closedBridge_zero,closedBridge_endpoint T hT f]
  · simp [hs]

theorem cyclicBridgePath_stopped (T : ℝ≥0) (hT : 0 < T) (s : ℝ≥0)
    (f : Path) (t : ℝ≥0) (ht : T ≤ t) : cyclicBridgePath T hT s f t = 0 := by
  change cyclicValue T s (min t T) f = 0
  rw [min_eq_right ht]
  have h := cyclicBridgePath_endpoint T hT s f
  change cyclicValue T s (min T T) f = 0 at h
  simpa only [min_self] using h

theorem measurable_stoppedClosedBridgePath (T : ℝ≥0) :
    Measurable (stoppedClosedBridgePath T) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun f : Path ↦ fun q ↦ closedBridge T (min (rationalTimeReal q) T) f)
  exact measurable_pi_lambda _ (fun q ↦ (continuous_closedBridge T _).measurable)

theorem measurable_cyclicBridgePath (T : ℝ≥0) (hT : 0 < T) (s : ℝ≥0) :
    Measurable (cyclicBridgePath T hT s) := by
  apply rationalEval_measurableEmbedding.measurable_comp_iff.mp
  change Measurable (fun f : Path ↦ fun q ↦ cyclicValue T s (min (rationalTimeReal q) T) f)
  exact measurable_pi_lambda _ (fun q ↦
    ((continuous_closedBridge T _).sub (continuous_closedBridge T s)).measurable)

end PerronWright.BrownianBridgeCyclicPath
