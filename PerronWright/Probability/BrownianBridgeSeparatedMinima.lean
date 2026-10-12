import PerronWright.Probability.BrownianBridgeGaussianRegression

/-! # Actual Gaussian bridge minima on separated intervals never tie

Genuine increment regression gives an independent scalar with a diffuse
Gaussian law. For each residual path, strict separation of the computed
regression slopes permits at most one scalar producing a tie. Tonelli
therefore makes the actual bridge tie event null.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBridgeSeparatedMinima

open BrownianPathLaw BrownianPinnedBridge BrownianBridgeAreaTiltPathLaw
open BrownianBridgeRegressionKernel BrownianBridgeGaussianRegression ContinuousPathIntervalMinimum

theorem ae_separated_interval_minima_ne (T l a b w : ℝ≥0) (hT : 0 < T)
    (hla : l ≤ a) (hab : a < b) (hbw : b ≤ w) (hw : w < T) :
    ∀ᵐ f ∂pathLaw, intervalMinimum l a (stoppedBridgePath T f) ≠
      intervalMinimum b w (stoppedBridgePath T f) := by
  let ψ := slopePath T a b
  let H : Set (Path × ℝ) := {p | intervalMinimum l a (perturbedPath p.1 ψ p.2) =
    intervalMinimum b w (perturbedPath p.1 ψ p.2)}
  have hH : MeasurableSet H :=
    measurableSet_eq_fun ((continuous_intervalMinimum l a).measurable.comp
      (measurable_joint_perturbedPath ψ)) ((continuous_intervalMinimum b w).measurable.comp
      (measurable_joint_perturbedPath ψ))
  have hvar := gapVariance_pos T a b hT hab (hbw.trans_lt hw)
  let G := gaussianReal 0 (Real.toNNReal (gapVariance T a b))
  let : NullSingletonClass G := nullSingletonClass_gaussianReal
    (ne_of_gt (Real.toNNReal_pos.mpr hvar))
  have hsection (f : Path) : G (Prod.mk f ⁻¹' H) = 0 := by
    apply Set.Subsingleton.measure_zero
    apply separated_minima_tie_subsingleton l a b w hla hbw f ψ 0 (slope T a b w)
      (slope_pos_right T a b w hT hab hbw hw)
    · intro t ht
      change slope T a b (min t T) ≤ 0
      rw [min_eq_left (ht.2.trans (hab.le.trans (hbw.trans hw.le)))]
      exact slope_nonpos_left T a b t hT hab (hbw.trans_lt hw) ht.2
    · intro t ht
      change slope T a b w ≤ slope T a b (min t T)
      rw [min_eq_left (ht.2.trans hw.le)]
      exact slope_right_lower_bound T a b t w hT hab ht.1 ht.2 hw
  have hz : (residualLaw T a b).prod G H = 0 := by
    rw [Measure.prod_apply hH]
    simp only [hsection,lintegral_zero]
  have hm := (measurable_residualPath T a b).prodMk (continuous_increment T a b).measurable
  have he : {f : Path | intervalMinimum l a (stoppedBridgePath T f) =
      intervalMinimum b w (stoppedBridgePath T f)} =
      (fun f ↦ (residualPath T a b f,increment T a b f)) ⁻¹' H := by
    ext f
    change _ ↔ intervalMinimum l a (perturbedPath (residualPath T a b f) ψ (increment T a b f)) =
      intervalMinimum b w (perturbedPath (residualPath T a b f) ψ (increment T a b f))
    rw [reconstruct_stoppedBridgePath]
    rfl
  have hj := residual_increment_jointLaw T a b hT hab (hbw.trans_lt hw)
  have hzero : pathLaw {f : Path | intervalMinimum l a (stoppedBridgePath T f) =
      intervalMinimum b w (stoppedBridgePath T f)} = 0 := by
    rw [he,← Measure.map_apply hm hH,hj]
    exact hz
  simpa only [ae_iff,not_not] using hzero

end PerronWright.BrownianBridgeSeparatedMinima
