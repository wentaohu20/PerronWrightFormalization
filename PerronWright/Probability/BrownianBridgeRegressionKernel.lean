import PerronWright.Probability.BrownianBridgeDiffuseIncrements

/-! # Actual bridge increment regression covariance and separating slope

The covariance and variance are computed from the constructed Brownian
bridge Gaussian laws. The resulting deterministic regression slope is
nonpositive before a and uniformly positive on every compact interval
after b and below T. These are derived inequalities, not interfaces.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators Classical NNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianBridgeRegressionKernel

open BrownianPathLaw BrownianPinnedBridge

def increment (T a b : ℝ≥0) (f : Path) : ℝ := bridge T b f-bridge T a f

def gapVariance (T a b : ℝ≥0) : ℝ :=
  ((b : ℝ)-(a : ℝ))*((T : ℝ)-((b : ℝ)-(a : ℝ)))/(T : ℝ)

def crossKernel (T a b t : ℝ≥0) : ℝ :=
  (min (t : ℝ) (b : ℝ)-(t : ℝ)*(b : ℝ)/(T : ℝ))-
    (min (t : ℝ) (a : ℝ)-(t : ℝ)*(a : ℝ)/(T : ℝ))

def slope (T a b t : ℝ≥0) : ℝ := crossKernel T a b t/gapVariance T a b

theorem continuous_increment (T a b : ℝ≥0) : Continuous (increment T a b) :=
  (continuous_bridge T b).sub (continuous_bridge T a)

theorem increment_hasGaussianLaw (T a b : ℝ≥0) : HasGaussianLaw (increment T a b) pathLaw :=
  (bridge_isGaussianProcess T).hasGaussianLaw_fun_sub

theorem integral_increment (T a b : ℝ≥0) : (∫ f, increment T a b f ∂pathLaw) = 0 := by
  unfold increment
  rw [integral_sub (bridge_hasGaussianLaw T b).integrable (bridge_hasGaussianLaw T a).integrable,
    integral_bridge,integral_bridge,sub_self]

theorem covariance_bridge_increment (T a b t : ℝ≥0) (hT : 0 < T)
    (ha : a ≤ T) (hb : b ≤ T) (ht : t ≤ T) :
    cov[bridge T t,increment T a b;pathLaw] = crossKernel T a b t := by
  unfold increment
  rw [covariance_fun_sub_right (bridge_hasGaussianLaw T t).memLp_two
    (bridge_hasGaussianLaw T b).memLp_two (bridge_hasGaussianLaw T a).memLp_two,
    covariance_bridge T t b hT ht hb,covariance_bridge T t a hT ht ha]
  rfl

theorem variance_increment (T a b : ℝ≥0) (hT : 0 < T) (hab : a ≤ b) (hb : b ≤ T) :
    Var[increment T a b;pathLaw] = gapVariance T a b := by
  unfold increment
  rw [variance_fun_sub (bridge_hasGaussianLaw T b).memLp_two (bridge_hasGaussianLaw T a).memLp_two,
    variance_bridge T b hT hb,variance_bridge T a hT (hab.trans hb),
    covariance_bridge T b a hT hb (hab.trans hb),min_eq_right (show (a : ℝ) ≤ b from hab)]
  unfold gapVariance
  have hne : (T : ℝ) ≠ 0 := ne_of_gt hT
  field_simp
  ring

theorem gapVariance_pos (T a b : ℝ≥0) (hT : 0 < T) (hab : a < b) (hb : b < T) :
    0 < gapVariance T a b := by
  unfold gapVariance
  have hd : 0 < (b : ℝ)-(a : ℝ) := sub_pos.mpr hab
  have hp : 0 < (T : ℝ)-((b : ℝ)-(a : ℝ)) := by linarith [a.coe_nonneg]
  exact div_pos (mul_pos hd hp) hT

theorem hasLaw_increment (T a b : ℝ≥0) (hT : 0 < T) (hab : a ≤ b) (hb : b ≤ T) :
    HasLaw (increment T a b) (gaussianReal 0 (Real.toNNReal (gapVariance T a b))) pathLaw := by
  refine ⟨(continuous_increment T a b).measurable.aemeasurable,?_⟩
  rw [(increment_hasGaussianLaw T a b).map_eq_gaussianReal,integral_increment,
    variance_increment T a b hT hab hb]

theorem continuous_sample_slope (T a b : ℝ≥0) : Continuous (slope T a b) := by
  unfold slope crossKernel
  fun_prop

def slopePath (T a b : ℝ≥0) : Path :=
  ⟨fun t ↦ slope T a b (min t T),(continuous_sample_slope T a b).comp (continuous_id.min continuous_const)⟩

theorem crossKernel_left (T a b t : ℝ≥0) (hab : a ≤ b) (ht : t ≤ a) :
    crossKernel T a b t = -(t : ℝ)*((b : ℝ)-(a : ℝ))/(T : ℝ) := by
  unfold crossKernel
  rw [min_eq_left (show (t : ℝ) ≤ b from ht.trans hab),min_eq_left (show (t : ℝ) ≤ a from ht)]
  ring

theorem crossKernel_right (T a b t : ℝ≥0) (hT : 0 < T) (hab : a ≤ b) (ht : b ≤ t) :
    crossKernel T a b t = ((b : ℝ)-(a : ℝ))*((T : ℝ)-(t : ℝ))/(T : ℝ) := by
  unfold crossKernel
  rw [min_eq_right (show (b : ℝ) ≤ t from ht),min_eq_right (show (a : ℝ) ≤ t from hab.trans ht)]
  have hne : (T : ℝ) ≠ 0 := ne_of_gt hT
  field_simp

theorem slope_nonpos_left (T a b t : ℝ≥0) (hT : 0 < T) (hab : a < b) (hb : b < T) (ht : t ≤ a) :
    slope T a b t ≤ 0 := by
  rw [slope,crossKernel_left T a b t hab.le ht]
  exact div_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg)
      (sub_nonneg.mpr hab.le)) hT.le) (gapVariance_pos T a b hT hab hb).le

theorem slope_pos_right (T a b t : ℝ≥0) (hT : 0 < T) (hab : a < b) (htb : b ≤ t) (ht : t < T) :
    0 < slope T a b t := by
  rw [slope,crossKernel_right T a b t hT hab.le htb]
  exact div_pos (div_pos (mul_pos (sub_pos.mpr hab) (sub_pos.mpr ht)) hT)
    (gapVariance_pos T a b hT hab (htb.trans_lt ht))

theorem slope_right_lower_bound (T a b t w : ℝ≥0) (hT : 0 < T) (hab : a < b)
    (hbt : b ≤ t) (htw : t ≤ w) (hw : w < T) : slope T a b w ≤ slope T a b t := by
  rw [slope,slope,crossKernel_right T a b w hT hab.le (hbt.trans htw),
    crossKernel_right T a b t hT hab.le hbt]
  apply div_le_div_of_nonneg_right _ (gapVariance_pos T a b hT hab ((hbt.trans htw).trans_lt hw)).le
  apply div_le_div_of_nonneg_right _ (show 0 ≤ (T : ℝ) from hT.le)
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (show (t : ℝ) ≤ w from htw) T)
    (sub_nonneg.mpr (show (a : ℝ) ≤ b from hab.le))

end PerronWright.BrownianBridgeRegressionKernel
