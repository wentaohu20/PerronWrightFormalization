import PerronWright.Probability.BrownianMinimumWindowNonnegativeLimit

/-! # Literal minimum-time, minimum-level and terminal displacement tests

The terminal displacement is evaluated from the actual whole future at
the minimizer. Joint path evaluation is continuous and its value is
exactly B_T minus the minimum, including all continuous paths. Thus the
proved minimum-window density limit applies to the literal endpoint
triple, not a hypothetical reconstructed endpoint.
-/

open MeasureTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianMinimumEndpointTests

open BrownianPathLaw ContinuousPathLeastMinimum BrownianPathIndependentIncrements
open ContinuousPathMinimumFutureBandAverage BrownianMinimumWindowNonnegativeLimit
open BrownianFirstPassageEndpointGeometry ContinuousPathFirstPassage

def endpointMap (T : ℝ≥0) (p : ℝ≥0 × ℝ × Path) : ℝ≥0 × ℝ × ℝ :=
  (p.1,p.2.1,p.2.2 (T-p.1))

theorem continuous_endpointMap (T : ℝ≥0) : Continuous (endpointMap T) :=
  continuous_fst.prodMk (continuous_snd.fst.prodMk
    (continuous_joint_eval.comp (continuous_snd.snd.prodMk (continuous_const.sub continuous_fst))))

def endpointTest (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) : (ℝ≥0 × ℝ × Path) →ᵇ ℝ :=
  Φ.compContinuous ⟨endpointMap T,continuous_endpointMap T⟩

theorem endpointTest_minimumPoint (T : ℝ≥0) (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (f : Path) :
    endpointTest T Φ (minimumPoint T f) =
      Φ (leastMinimizer T f,minimumValue T f,f T-minimumValue T f) := by
  change Φ (leastMinimizer T f,minimumValue T f,
    futurePath (leastMinimizer T f) f (T-leastMinimizer T f)) = _
  rw [futurePath_eval,add_tsub_cancel_of_le (leastMinimizer_le_time T f),leastMinimizer_value]

theorem actual_minimum_endpoint_density_limit (T : ℝ≥0) (hT : 0 < T)
    (Φ : (ℝ≥0 × ℝ × ℝ) →ᵇ ℝ) (hΦ : ∀ p, 0 ≤ Φ p) :
    Tendsto (fun δ : ℝ ↦
      (∫⁻ a in Ioi (0 : ℝ), ∫⁻ s in Iio (T : ℝ),
        BrownianFirstPassageDensityGeometry.density a s *
          ∫⁻ g in survival (-δ) (remainingTime T s),
            ENNReal.ofReal (Φ (Real.toNNReal s,-a,g (T-Real.toNNReal s))) ∂pathLaw)/
        ENNReal.ofReal δ) (𝓝[>] 0)
      (𝓝 (∫⁻ f, ENNReal.ofReal
        (Φ (leastMinimizer T f,minimumValue T f,f T-minimumValue T f)) ∂pathLaw)) := by
  have h := actual_future_density_limit T hT (endpointTest T Φ) (fun p ↦ hΦ _)
  simp_rw [endpointTest_minimumPoint] at h
  simpa only [sourceTest,endpointTest,
    BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,endpointMap] using h

end PerronWright.BrownianMinimumEndpointTests
