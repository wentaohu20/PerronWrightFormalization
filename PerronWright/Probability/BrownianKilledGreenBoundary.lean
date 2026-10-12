import PerronWright.Probability.BrownianKilledGreenKernel
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Exact boundary response of the genuine killed Green kernel

The boundary slope is proved from the actual duration resolvent's Green
formula, with a uniform level-gap bound for later nonnegative insertions.
No boundary derivative or Green interface is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianKilledGreenBoundary

open BrownianKilledGreenKernel BrownianKilledAreaMomentResolvent

theorem greenReal_symm (p x y : ℝ) : greenReal p x y = greenReal p y x := by
  unfold greenReal
  rw [abs_sub_comm,add_comm x y]

theorem greenReal_of_le (p x y : ℝ) (hxy : x ≤ y) :
    greenReal p x y = Real.exp (-y*Real.sqrt (2*p))/Real.sqrt (2*p)*
      (Real.exp (x*Real.sqrt (2*p))-Real.exp (-x*Real.sqrt (2*p))) := by
  have he1 : -(y-x)*Real.sqrt (2*p) = -y*Real.sqrt (2*p)+x*Real.sqrt (2*p) := by ring
  have he2 : -(x+y)*Real.sqrt (2*p) = -y*Real.sqrt (2*p)+ -x*Real.sqrt (2*p) := by ring
  unfold greenReal
  rw [abs_of_nonneg (sub_nonneg.mpr hxy),he1,he2,Real.exp_add,Real.exp_add]
  ring

theorem greenReal_le_exp_gap (p x y : ℝ) :
    greenReal p x y ≤ Real.exp (-|y-x| * Real.sqrt (2*p))/Real.sqrt (2*p) := by
  unfold greenReal
  exact div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) (Real.sqrt_nonneg _)

theorem greenReal_le_two_min_exp_gap (p : ℝ) (hp : 0 < p) (x y : ℝ) :
    greenReal p x y ≤ 2*min x y*Real.exp (-|y-x| * Real.sqrt (2*p)) := by
  have hs : 0 < Real.sqrt (2*p) := Real.sqrt_pos.mpr (by positivity)
  have he : |y-x|+2*min x y = x+y := by
    rcases le_total x y with h | h
    · rw [min_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · rw [min_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]
      ring
  have hfactor : greenReal p x y = Real.exp (-|y-x| * Real.sqrt (2*p)) *
      (1-Real.exp (-2*min x y*Real.sqrt (2*p)))/Real.sqrt (2*p) := by
    unfold greenReal
    rw [← he,show -(|y-x|+2*min x y)*Real.sqrt (2*p) =
      -|y-x| * Real.sqrt (2*p)+ -2*min x y*Real.sqrt (2*p) by ring,Real.exp_add]
    ring
  have hb : 1-Real.exp (-2*min x y*Real.sqrt (2*p)) ≤ 2*min x y*Real.sqrt (2*p) := by
    have h := Real.add_one_le_exp (-2*min x y*Real.sqrt (2*p))
    linarith
  rw [hfactor]
  apply (div_le_iff₀ hs).mpr
  calc
    _ ≤ Real.exp (-|y-x| * Real.sqrt (2*p))*(2*min x y*Real.sqrt (2*p)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by ring

theorem greenReal_boundary_slope (p : ℝ) (hp : 0 < p) (y : ℝ) (hy : 0 < y) :
    Tendsto (fun x : ℝ ↦ greenReal p x y/x) (𝓝[>] 0)
      (𝓝 (2*Real.exp (-y*Real.sqrt (2*p)))) := by
  let s := Real.sqrt (2*p)
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr (by positivity : 0 < 2*p)).ne'
  have hd : HasDerivAt (fun x : ℝ ↦ Real.exp (x*s)-Real.exp (-x*s)) (2*s) 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).mul_const s).exp).sub
      ((((hasDerivAt_id (0 : ℝ)).neg).mul_const s).exp) using 1; simp; ring
  have hl : Tendsto (fun x : ℝ ↦ (Real.exp (x*s)-Real.exp (-x*s))/x) (𝓝[>] 0) (𝓝 (2*s)) := by
    simpa only [zero_add,zero_mul,neg_zero,Real.exp_zero,sub_self,sub_zero,
      smul_eq_mul,div_eq_mul_inv,mul_comm] using hd.tendsto_slope_zero_right
  have hmul := hl.const_mul (Real.exp (-y*s)/s)
  have htarget : Real.exp (-y*s)/s*(2*s) = 2*Real.exp (-y*s) := by field_simp
  rw [htarget] at hmul
  apply hmul.congr'
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] 0, x ≤ y :=
    (eventually_lt_nhds hy).filter_mono nhdsWithin_le_nhds |>.mono (fun _ hx ↦ hx.le)
  filter_upwards [hsmall] with x hx
  rw [greenReal_of_le p x y hx]
  dsimp only [s]
  ring

theorem actual_resolvent_boundary_slope (p : ℝ) (hp : 0 < p) (y : ℝ) (hy : 0 < y) :
    Tendsto (fun x : ℝ ↦ (resolvent 0 p x y).toReal/x) (𝓝[>] 0)
      (𝓝 (2*Real.exp (-y*Real.sqrt (2*p)))) := by
  apply (greenReal_boundary_slope p hp y hy).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [resolvent_zero_eq_green p hp x y (show 0 < x from hx) hy,
    ENNReal.toReal_ofReal (greenReal_nonneg p x y hx hy)]

end PerronWright.BrownianKilledGreenBoundary
