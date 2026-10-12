import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
A concrete local-disc estimate for dented-domain transfer.  The excluded
cone is written in Cartesian coordinates; no holomorphy is assumed here.
The point is to obtain a disc radius proportional to the distance from
the singularity, uniformly for centers in the closed unit disc.
-/

noncomputable section

namespace PerronWright.Transfer

/-- A point in the left half-plane based at `1` is quantitatively separated
from a right-pointing cone of slope `m`. -/
theorem left_half_cone_separation {z w : ℂ} {m : ℝ}
    (hm : 0 ≤ m) (hz : (z - 1).re ≤ 0)
    (hwre : 0 ≤ (w - 1).re)
    (hwim : |(w - 1).im| ≤ m * (w - 1).re) :
    ‖z - 1‖ ≤ (m + 2) * ‖w - z‖ := by
  have hre : (w - 1).re = (w - z).re + (z - 1).re := by
    simp only [Complex.sub_re]
    ring
  have him : (z - 1).im = (w - 1).im - (w - z).im := by
    simp only [Complex.sub_im]
    ring
  have hdre := Complex.abs_re_le_norm (w - z)
  have hdim := Complex.abs_im_le_norm (w - z)
  have hure : |(z - 1).re| ≤ ‖w - z‖ := by
    rw [abs_of_nonpos hz]
    have := (le_abs_self (w - z).re).trans hdre
    linarith
  have huim : |(z - 1).im| ≤ (m + 1) * ‖w - z‖ := by
    rw [him]
    have htri : |(w - 1).im - (w - z).im| ≤
        |(w - 1).im| + |(w - z).im| := abs_sub _ _
    have hvr : (w - 1).re ≤ ‖w - z‖ := by
      have := (le_abs_self (w - z).re).trans hdre
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hvr hm]
  calc
    ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (m + 2) * ‖w - z‖ := by linarith

/-- The unit disc lies in the left half-plane based at the singularity. -/
theorem unit_disc_left_half {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (z - 1).re ≤ 0 := by
  have hre := Complex.re_le_norm z
  simpa only [Complex.sub_re, Complex.one_re] using
    (show z.re - 1 ≤ 0 by linarith)

/-- A proportional disc centered inside the unit disc avoids the whole
excluded cone.  The `m + 3` margin is deliberately strict. -/
theorem proportional_disc_avoids_cone {z w : ℂ} {m : ℝ}
    (hm : 0 ≤ m) (hz : ‖z‖ ≤ 1)
    (hclose : ‖w - z‖ < ‖z - 1‖ / (m + 3)) :
    ¬ (0 ≤ (w - 1).re ∧
      |(w - 1).im| ≤ m * (w - 1).re) := by
  rintro ⟨hwre, hwim⟩
  have hsep := left_half_cone_separation hm (unit_disc_left_half hz) hwre hwim
  have hden : 0 < m + 3 := by linarith
  have hmul : (m + 2) * ‖w - z‖ < ‖z - 1‖ := by
    have h := (lt_div_iff₀ hden).mp hclose
    nlinarith [norm_nonneg (w - z)]
  exact (not_lt_of_ge hsep) hmul

/-- A Cartesian version of the usual dented domain.  Its exclusion is
the closed right-pointing cone based at the singularity. -/
def cartesianDelta (η m : ℝ) : Set ℂ :=
  {w | ‖w‖ < 1 + η ∧
    ¬ (0 ≤ (w - 1).re ∧
      |(w - 1).im| ≤ m * (w - 1).re)}

theorem isOpen_cartesianDelta (η m : ℝ) :
    IsOpen (cartesianDelta η m) := by
  have houter : IsOpen {w : ℂ | ‖w‖ < 1 + η} :=
    isOpen_lt (by fun_prop) continuous_const
  have hconeRe : IsClosed {w : ℂ | (0 : ℝ) ≤ (w - 1).re} :=
    isClosed_le continuous_const (by fun_prop)
  have hconeIm : IsClosed
      {w : ℂ | |(w - 1).im| ≤ m * (w - 1).re} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hcone : IsClosed
      {w : ℂ | 0 ≤ (w - 1).re ∧
        |(w - 1).im| ≤ m * (w - 1).re} :=
    hconeRe.inter hconeIm
  change IsOpen
    ({w : ℂ | ‖w‖ < 1 + η} ∩
      {w : ℂ | 0 ≤ (w - 1).re ∧
        |(w - 1).im| ≤ m * (w - 1).re}ᶜ)
  exact houter.inter hcone.isOpen_compl

/-- The Cartesian dented domain really is a continuation of the open
unit disc whenever its radial margin is positive. -/
theorem unit_ball_subset_cartesianDelta {η m : ℝ} (hη : 0 < η) :
    Metric.ball (0 : ℂ) 1 ⊆ cartesianDelta η m := by
  intro z hz
  have hnorm : ‖z‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  constructor
  · linarith
  · intro hcone
    have hre : z.re ≤ ‖z‖ := Complex.re_le_norm z
    have hleft : (z - 1).re < 0 := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    exact (not_le_of_gt hleft) hcone.1

/-- At unit-disc centers sufficiently close to `1`, the same
proportional disc is wholly contained in the Cartesian Δ-domain.
This supplies both the outer-radius and dent-avoidance conditions. -/
theorem proportional_disc_subset_cartesianDelta {z w : ℂ} {η m : ℝ}
    (hm : 0 ≤ m) (hz : ‖z‖ ≤ 1) (hnear : ‖z - 1‖ < η)
    (hclose : ‖w - z‖ < ‖z - 1‖ / (m + 3)) :
    w ∈ cartesianDelta η m := by
  have hden : 0 < m + 3 := by linarith
  have hdist : ‖w - z‖ < η := by
    have h := (lt_div_iff₀ hden).mp hclose
    nlinarith [norm_nonneg (w - z)]
  constructor
  · have htriangle : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      calc
        ‖w‖ = ‖(w - z) + z‖ := by congr 1; ring
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
    linarith
  · exact proportional_disc_avoids_cone hm hz hclose

/-- A smaller closed Cauchy disc stays strictly inside the dented domain.
The explicit factor `2` leaves a margin at every boundary point. -/
theorem closedBall_subset_cartesianDelta {z : ℂ} {η m : ℝ}
    (hm : 0 ≤ m) (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1)
    (hnear : ‖z - 1‖ < η) :
    Metric.closedBall z (‖z - 1‖ / (2 * (m + 3))) ⊆
      cartesianDelta η m := by
  intro w hw
  have hden : 0 < m + 3 := by linarith
  have hden2 : 0 < 2 * (m + 3) := by positivity
  have hn : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have hdist : ‖w - z‖ ≤ ‖z - 1‖ / (2 * (m + 3)) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
  have hsmall : ‖w - z‖ < ‖z - 1‖ / (m + 3) := by
    apply (lt_div_iff₀ hden).mpr
    have h := (le_div_iff₀ hden2).mp hdist
    nlinarith [norm_nonneg (w - z)]
  exact proportional_disc_subset_cartesianDelta hm hz hnear hsmall

end PerronWright.Transfer
