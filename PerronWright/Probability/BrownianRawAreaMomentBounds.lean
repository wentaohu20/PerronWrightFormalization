import PerronWright.Probability.BrownianPositiveBridgeAreaScaling
import PerronWright.Probability.BrownianKilledAreaMomentFiniteness
import Mathlib.Algebra.Order.Ring.Basic

/-! # Genuine polynomial bounds for all surviving Brownian area moments

The raw Brownian area has exact duration scaling under the actual whole
path law. Its finite unit absolute moment gives an explicit polynomial
bound for every shifted surviving-path moment measure. No pointwise
Green estimate or moment-finiteness premise is supplied.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianRawAreaMomentBounds

open BrownianPathLaw BrownianPathDilationLaw BrownianBridgeCyclicArea
open BrownianPositiveBridgeAreaScaling BrownianKilledAreaGeometry
open BrownianKilledAreaMomentKernel BrownianKilledAreaMomentFiniteness

theorem integrable_abs_pathArea_pow (T : ℝ≥0) (n : ℕ) :
    Integrable (fun f : Path ↦ |pathArea T f|^n) pathLaw := by
  simpa only [shiftedArea,sub_self,mul_zero,zero_add] using
    integrable_abs_shiftedArea_pow 0 0 T n

def rawAbsoluteMoment (n : ℕ) : ℝ := ∫ f : Path, |pathArea 1 f|^n ∂pathLaw

theorem rawAbsoluteMoment_nonneg (n : ℕ) : 0 ≤ rawAbsoluteMoment n :=
  integral_nonneg (fun _ ↦ pow_nonneg (abs_nonneg _) _)

theorem raw_absolute_moment_duration_scaling (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ f : Path, |pathArea T f|^n ∂pathLaw) =
      ((T : ℝ)^(3/2 : ℝ))^n*rawAbsoluteMoment n := by
  calc
    _ = ∫ f : Path, |pathArea T f|^n ∂pathLaw.map (brownianDilation T) := by
      rw [pathLaw_brownianDilation T hT]
    _ = ∫ f : Path, |pathArea T (brownianDilation T f)|^n ∂pathLaw :=
      integral_map (measurable_brownianDilation T).aemeasurable
        (((measurable_pathArea T).abs.pow_const n).aestronglyMeasurable)
    _ = _ := by
      simp_rw [pathArea_brownianDilation T hT,abs_mul,
        abs_of_nonneg (Real.rpow_nonneg T.coe_nonneg (3/2 : ℝ)),mul_pow]
      exact integral_const_mul _ _

theorem absolute_shifted_area_moment_bound (level x : ℝ) (T : ℝ≥0)
    (hT : 0 < T) (n : ℕ) :
    (∫ f : Path, |shiftedArea level x T f|^n ∂pathLaw) ≤
      (2 : ℝ)^(n-1)*((T : ℝ)^n*|x-level|^n+
        ((T : ℝ)^(3/2 : ℝ))^n*rawAbsoluteMoment n) := by
  have hi := integrable_abs_pathArea_pow T n
  have hb (f : Path) : |shiftedArea level x T f|^n ≤
      (2 : ℝ)^(n-1)*(|(T : ℝ)*(x-level)|^n+|pathArea T f|^n) := by
    calc
      _ ≤ (|(T : ℝ)*(x-level)|+|pathArea T f|)^n := by
        apply pow_le_pow_left₀ (abs_nonneg _)
        exact abs_add_le _ _
      _ ≤ _ := add_pow_le (abs_nonneg _) (abs_nonneg _) n
  calc
    _ ≤ ∫ f : Path, (2 : ℝ)^(n-1)*
        (|(T : ℝ)*(x-level)|^n+|pathArea T f|^n) ∂pathLaw :=
      integral_mono (integrable_abs_shiftedArea_pow level x T n)
        (((integrable_const _).add hi).const_mul _) hb
    _ = (2 : ℝ)^(n-1)*(|(T : ℝ)*(x-level)|^n+
        (∫ f : Path, |pathArea T f|^n ∂pathLaw)) := by
      rw [integral_const_mul,integral_add (integrable_const _) hi]
      simp only [integral_const,probReal_univ,one_smul]
    _ = _ := by
      rw [raw_absolute_moment_duration_scaling T hT n,abs_mul,
        abs_of_nonneg T.coe_nonneg,mul_pow]

theorem momentLaw_real_mass_bound (level x : ℝ) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (momentLaw level n T x).real univ ≤
      (2 : ℝ)^(n-1)*((T : ℝ)^n*|x-level|^n+
        ((T : ℝ)^(3/2 : ℝ))^n*rawAbsoluteMoment n) :=
  (momentLaw_univ_le_absoluteMoment level n T x).trans
    (absolute_shifted_area_moment_bound level x T hT n)

end PerronWright.BrownianRawAreaMomentBounds
