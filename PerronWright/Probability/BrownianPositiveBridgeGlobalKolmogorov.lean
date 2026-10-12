import PerronWright.Probability.BrownianPositiveBridgeGlobalIncrementMoments
import Mathlib.Probability.Process.Kolmogorov

/-! # Common Kolmogorov condition for the actual full positive bridge

Literal evaluations on `[0,T]` satisfy the common fourth-moment, second-
time-power condition, including both endpoints. The finite coefficient
was proved from actual killed laws and genuine conditional FDDs. This
leaf does not assume or yet assert full path-family tightness or Vervaat.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeGlobalKolmogorov

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianPositiveBridgeGlobalIncrementMoments

abbrev ClosedTime (T : ℝ≥0) := {s : ℝ≥0 // s ≤ T}

def process (T : ℝ≥0) (s : ClosedTime T) (g : Path) : ℝ := g s.val

def commonCoefficient (T : ℝ≥0) : ℝ≥0 := (globalCoefficient T).toNNReal

theorem measurable_process (T : ℝ≥0) (s : ClosedTime T) : Measurable (process T s) :=
  (continuous_eval s.val).measurable

theorem eventually_uniform_closed_interval_kolmogorov (T : ℝ≥0) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      IsKolmogorovProcess (process T) (positiveBridgeLaw a T) 4 2 (commonCoefficient T) := by
  have hc : (commonCoefficient T : ℝ≥0∞) = globalCoefficient T :=
    ENNReal.coe_toNNReal (globalCoefficient_ne_top T hT)
  filter_upwards [eventually_uniform_pair_fourth_increment T hT] with a ha
  apply IsKolmogorovProcess.mk_of_secondCountableTopology
  · intro s
    exact measurable_process T s
  · intro u v
    have he := ha u.val v.val u.property v.property
    have hfun : (fun g : Path ↦ edist (process T u g) (process T v g)^(4 : ℝ)) =
        fun g : Path ↦ ENNReal.ofReal (‖g v.val-g u.val‖^4) := by
      funext g
      rw [process,process,edist_dist,Real.dist_eq]
      simp only [ENNReal.rpow_ofNat]
      rw [← ENNReal.ofReal_pow (abs_nonneg _),norm_sub_rev,Real.norm_eq_abs]
    rw [hfun,hc]
    change _ ≤ globalCoefficient T*(edist u.val v.val)^(2 : ℝ)
    rw [edist_dist,NNReal.dist_eq]
    simp only [ENNReal.rpow_ofNat]
    rw [← ENNReal.ofReal_pow (abs_nonneg _),abs_sub_comm]
    exact he
  · norm_num
  · norm_num

end PerronWright.BrownianPositiveBridgeGlobalKolmogorov
