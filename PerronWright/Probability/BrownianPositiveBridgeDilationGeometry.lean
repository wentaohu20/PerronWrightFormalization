import PerronWright.Probability.BrownianPositiveBridgeConditioning
import PerronWright.Probability.BrownianBridgeMinimumDilationLaw

/-! # Literal positive-bridge conditioning under Brownian path dilation

Time and space are scaled together in the actual pinned path constraint.
These are pointwise identities, not an excursion identification or an
assumed conditional scaling law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeDilationGeometry

open BrownianPathLaw BrownianPathDilationLaw BrownianFirstPassageBridgeLaw
open BrownianPositiveBridgeConditioning

theorem brownianDilation_translate (T : ℝ≥0) (a : ℝ) (g : Path) :
    brownianDilation T (translate a g) = translate (Real.sqrt (T : ℝ)*a) (brownianDilation T g) := by
  apply ContinuousMap.ext
  intro t
  change Real.sqrt (T : ℝ)*(g (t/T)+a) = Real.sqrt (T : ℝ)*g (t/T)+Real.sqrt (T : ℝ)*a
  ring

theorem brownianDilation_mem_bridgeConstraint_iff (T : ℝ≥0) (hT : 0 < T) (a : ℝ) (g : Path) :
    brownianDilation T g ∈ bridgeConstraint (-Real.sqrt (T : ℝ)*a) T 0 ↔
      g ∈ bridgeConstraint (-a) 1 0 := by
  rw [mem_bridgeConstraint_iff,mem_bridgeConstraint_iff]
  simp only [mul_zero,add_zero]
  have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hT
  constructor
  · intro h r hr
    have ht : T*r ≤ T := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr (zero_le : (0 : ℝ≥0) ≤ T)
    have he := h (T*r) ht
    change -Real.sqrt (T : ℝ)*a < Real.sqrt (T : ℝ)*g (T*r/T) at he
    rw [mul_div_cancel_left₀ r (ne_of_gt hT)] at he
    nlinarith
  · intro h t ht
    have hr : t/T ≤ 1 := (div_le_iff₀ hT).mpr (by simpa only [one_mul] using ht)
    have he := h (t/T) hr
    change -Real.sqrt (T : ℝ)*a < Real.sqrt (T : ℝ)*g (t/T)
    nlinarith

theorem brownianDilation_bridgeConstraint_preimage (T : ℝ≥0) (hT : 0 < T) (a : ℝ) :
    brownianDilation T ⁻¹' bridgeConstraint (-Real.sqrt (T : ℝ)*a) T 0 =
      bridgeConstraint (-a) 1 0 := by
  ext g
  exact brownianDilation_mem_bridgeConstraint_iff T hT a g

theorem pinnedLaw_duration_scaling (T : ℝ≥0) (hT : 0 < T) :
    pinnedLaw T = (pinnedLaw 1).map (brownianDilation T) :=
  BrownianBridgeMinimumDilationLaw.bridgePathLaw_duration_scaling T hT

end PerronWright.BrownianPositiveBridgeDilationGeometry
