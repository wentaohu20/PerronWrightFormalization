import PerronWright.Probability.BrownianKilledFreeEntranceTests

/-! # Actual nonnegative finite-tuple entrance tests

The real joint-test limit is converted under the actual finite surviving
path law and the proved finite entrance measure, with no new limit input.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianKilledFreeEntranceNonnegativeTests

open BrownianPathLaw ContinuousPathFirstPassage BrownianKilledFiniteDimensionalOrderedTimes
open BrownianKilledFiniteDimensionalOrderedDensity BrownianKilledFiniteDimensionalDensityCoordinates
open BrownianKilledFreeEntranceTests

local instance freeVectorMeasurable (n : ℕ) : MeasurableSpace (FreeVector n) := MeasurableSpace.pi

theorem actual_unshifted_ordered_nonnegative_test_tendsto (n : ℕ)
    (times : Fin (n+2) → ℝ≥0) (hstrict : StrictMono times) (hzero : times 0 = 0)
    (G : (ℝ × FreeVector (n+1)) →ᵇ ℝ) (hG : ∀ q, 0 ≤ G q) :
    Tendsto (fun a : ℝ ↦ (∫⁻ f in survival (-a) (times (Fin.last (n+1))),
      ENNReal.ofReal (G (a,fun i : Fin (n+1) ↦ f (times i.succ))) ∂pathLaw)/ENNReal.ofReal a)
      (𝓝[>] 0) (𝓝 (∫⁻ v, ENNReal.ofReal (G (0,v))
        ∂freeEntranceLaw n (orderedGaps (n+1) times))) := by
  let := freeEntranceLaw_isFinite n (orderedGaps (n+1) times) (orderedGaps_positive (n+1) times hstrict)
  have hientrance : Integrable (fun v : FreeVector (n+1) ↦ G (0,v))
      (freeEntranceLaw n (orderedGaps (n+1) times)) :=
    (integrable_const ‖G‖).mono' (by fun_prop) (Eventually.of_forall (fun _ ↦ G.norm_coe_le_norm _))
  have hc (a : ℝ) : Continuous (fun f : Path ↦ G (a,fun i : Fin (n+1) ↦ f (times i.succ))) :=
    G.continuous.comp (continuous_const.prodMk (continuous_pi (fun i ↦ continuous_eval (times i.succ))))
  have hi (a : ℝ) : Integrable (fun f : Path ↦ G (a,fun i : Fin (n+1) ↦ f (times i.succ)))
      (pathLaw.restrict (survival (-a) (times (Fin.last (n+1))))) :=
    (integrable_const ‖G‖).mono' (hc a).aestronglyMeasurable (Eventually.of_forall (fun _ ↦ G.norm_coe_le_norm _))
  have ht := ENNReal.tendsto_ofReal (actual_unshifted_ordered_test_tendsto n times hstrict hzero G)
  rw [ofReal_integral_eq_lintegral_ofReal hientrance (Eventually.of_forall (fun _ ↦ hG _))] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [ENNReal.ofReal_div_of_pos ha,
    ofReal_integral_eq_lintegral_ofReal (hi a) (Eventually.of_forall (fun _ ↦ hG _))]

end PerronWright.BrownianKilledFreeEntranceNonnegativeTests
