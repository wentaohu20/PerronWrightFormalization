import PerronWright.Probability.BrownianFirstPassageUncappedLaw
import PerronWright.Probability.BrownianFirstPassageZeroDrift
import PerronWright.Probability.BrownianFirstPassageBridgeLaw

/-! # Literal first-passage endpoint reconstruction

For the actual Brownian path, the first negative-level passage is finite
and hits that level exactly. Before a fixed later endpoint, its genuine
future path reconstructs the endpoint. The Gaussian in the numerical
endpoint map below is an actual future Brownian evaluation law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianFirstPassageEndpointGeometry

open BrownianPathLaw BrownianFirstPassageUncappedLaw BrownianPathIndependentIncrements
open BrownianFirstPassageZeroDrift

def realTime (level : ℝ) (f : Path) : ℝ := passageTime level f

theorem measurable_realTime (level : ℝ) : Measurable (realTime level) :=
  NNReal.continuous_coe.measurable.comp (measurable_passageTime level)

def timeLaw (level : ℝ) : Measure ℝ := pathLaw.map (realTime level)

instance timeLaw_isProbability (level : ℝ) : IsProbabilityMeasure (timeLaw level) :=
  Measure.isProbabilityMeasure_map (measurable_realTime level).aemeasurable

def remainingTime (T : ℝ≥0) (s : ℝ) : ℝ≥0 := Real.toNNReal ((T : ℝ)-s)

theorem continuous_remainingTime (T : ℝ≥0) : Continuous (remainingTime T) :=
  continuous_real_toNNReal.comp (continuous_const.sub continuous_id)

theorem remainingTime_realTime (T : ℝ≥0) (level : ℝ) (f : Path)
    (ht : passageTime level f ≤ T) :
    remainingTime T (realTime level f) = T-passageTime level f := by
  rw [remainingTime,realTime,← NNReal.coe_sub ht,Real.toNNReal_coe]

def futureEndpoint (level : ℝ) (T : ℝ≥0) (p : ℝ × Path) : ℝ :=
  level+p.2 (remainingTime T p.1)

theorem continuous_futureEndpoint (level : ℝ) (T : ℝ≥0) :
    Continuous (futureEndpoint level T) :=
  continuous_const.add (continuous_joint_eval.comp
    (continuous_snd.prodMk ((continuous_remainingTime T).comp continuous_fst)))

def endpointMap (level : ℝ) (T : ℝ≥0) (p : ℝ × Path) : ℝ × ℝ :=
  (p.1,futureEndpoint level T p)

theorem continuous_endpointMap (level : ℝ) (T : ℝ≥0) :
    Continuous (endpointMap level T) :=
  continuous_fst.prodMk (continuous_futureEndpoint level T)

theorem ae_endpoint_reconstruction (level : ℝ) (hlevel : level < 0) (T : ℝ≥0) :
    ∀ᵐ f ∂pathLaw, realTime level f < (T : ℝ) →
      futureEndpoint level T (realTime level f,passageFuture level f) = f T := by
  filter_upwards [ae_firstPassage_exact_level level hlevel] with f hf
  intro ht
  have hle : passageTime level f ≤ T := by exact_mod_cast ht.le
  rw [futureEndpoint,remainingTime_realTime T level f hle,passageFuture,futurePath_eval,
    add_tsub_cancel_of_le hle]
  change level+(f T-f (ContinuousPathFirstPassage.firstPassage level f).toNNReal) = f T
  rw [hf]
  ring

theorem futureEndpoint_gaussianLaw (level : ℝ) (T : ℝ≥0) (s : ℝ) :
    pathLaw.map (fun g : Path ↦ futureEndpoint level T (s,g)) =
      gaussianReal level (remainingTime T s) := by
  have he := (isBrownian_pathLaw.toIsPreBrownianReal.hasLaw_eval (remainingTime T s)).map_eq
  have hm : Measurable (fun z : ℝ ↦ level+z) := measurable_const.add measurable_id
  change pathLaw.map ((fun z : ℝ ↦ level+z) ∘ (fun g : Path ↦ g (remainingTime T s))) = _
  rw [← Measure.map_map hm (continuous_eval (remainingTime T s)).measurable,he,
    gaussianReal_map_const_add,zero_add]

end PerronWright.BrownianFirstPassageEndpointGeometry
