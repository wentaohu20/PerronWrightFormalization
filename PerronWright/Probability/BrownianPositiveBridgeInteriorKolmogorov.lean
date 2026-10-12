import PerronWright.Probability.BrownianPositiveBridgeIncrementMoments
import Mathlib.Probability.Process.Kolmogorov

/-! # Genuine common Kolmogorov condition on every interior time window

The process is literal evaluation of the actual positive conditioned
bridge path. Its common finite fourth-moment coefficient is proved from
the Gaussian product density, rather than supplied as a hypothesis.
This is an interior estimate, not a full-horizon tightness declaration.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.BrownianPositiveBridgeInteriorKolmogorov

open BrownianPathLaw BrownianPositiveBridgeConditioning BrownianPositiveBridgeIncrementMoments

abbrev InteriorTime (δ T : ℝ≥0) := {s : ℝ≥0 // δ ≤ s ∧ s+δ ≤ T}

def process (δ T : ℝ≥0) (s : InteriorTime δ T) (g : Path) : ℝ := g s.val

def commonCoefficient (δ T : ℝ≥0) : ℝ≥0 := (fourthIncrementCoefficient δ T).toNNReal

theorem measurable_process (δ T : ℝ≥0) (s : InteriorTime δ T) : Measurable (process δ T s) :=
  (continuous_eval s.val).measurable

theorem edist_gap (u v : ℝ≥0) (huv : u ≤ v) :
    edist u v = ENNReal.ofReal ((v-u : ℝ≥0) : ℝ) := by
  rw [edist_dist]
  congr 1
  rw [NNReal.dist_eq,abs_of_nonpos (sub_nonpos.mpr (show (u : ℝ) ≤ v from huv)),
    NNReal.coe_sub huv]
  ring

theorem eventually_uniform_interior_kolmogorov (δ T : ℝ≥0) (hδ : 0 < δ) (hT : 0 < T) :
    ∀ᶠ a : ℝ in 𝓝[>] 0,
      IsKolmogorovProcess (process δ T) (positiveBridgeLaw a T) 4 2 (commonCoefficient δ T) := by
  have hc : (commonCoefficient δ T : ℝ≥0∞) = fourthIncrementCoefficient δ T :=
    ENNReal.coe_toNNReal (fourthIncrementCoefficient_ne_top δ T hT)
  filter_upwards [eventually_uniform_interior_fourth_increment δ T hδ hT] with a ha
  apply IsKolmogorovProcess.mk_of_secondCountableTopology
  · intro s
    exact measurable_process δ T s
  · intro u v
    have hordered : ∀ u v : InteriorTime δ T, u.val ≤ v.val →
        (∫⁻ g, edist (process δ T u g) (process δ T v g)^(4 : ℝ) ∂positiveBridgeLaw a T) ≤
          (commonCoefficient δ T : ℝ≥0∞)*edist u v^(2 : ℝ) := by
      intro u v huv
      have hvT : v.val ≤ T := (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ δ)).trans v.property.2
      have ht : δ ≤ T-v.val := le_tsub_of_add_le_right (by simpa only [add_comm] using v.property.2)
      have hsum : u.val+(v.val-u.val)+(T-v.val) = T := by
        rw [add_tsub_cancel_of_le huv,add_tsub_cancel_of_le hvT]
      have he := ha u.val (v.val-u.val) (T-v.val) u.property.1 ht hsum
      rw [add_tsub_cancel_of_le huv] at he
      have hfun : (fun g : Path ↦ edist (process δ T u g) (process δ T v g)^(4 : ℝ)) =
          fun g : Path ↦ ENNReal.ofReal (‖g v.val-g u.val‖^4) := by
        funext g
        rw [process,process,edist_dist,Real.dist_eq]
        simp only [ENNReal.rpow_ofNat]
        rw [← ENNReal.ofReal_pow (abs_nonneg _),norm_sub_rev,Real.norm_eq_abs]
      rw [hfun,hc]
      change _ ≤ fourthIncrementCoefficient δ T*(edist u.val v.val)^(2 : ℝ)
      rw [edist_gap u.val v.val huv]
      simp only [ENNReal.rpow_ofNat]
      rw [← ENNReal.ofReal_pow (NNReal.coe_nonneg _)]
      exact he
    rcases le_total u.val v.val with huv | hvu
    · exact hordered u v huv
    · simpa only [edist_comm] using hordered v u hvu
  · norm_num
  · norm_num

end PerronWright.BrownianPositiveBridgeInteriorKolmogorov
