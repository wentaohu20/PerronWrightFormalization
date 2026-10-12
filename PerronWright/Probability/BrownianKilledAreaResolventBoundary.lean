import PerronWright.Probability.BrownianKilledAreaResolventPointwiseFiniteness

/-! # Genuine all-order boundary response of killed-area resolvents

The true zeroth Green slope passes through every actual Kac insertion by
dominated convergence. Its domination is proved from the exponential gap
bound and the finite initial-state moment mass, not imposed as an interface.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Classical NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianKilledAreaResolventBoundary

open BrownianKilledAreaMomentResolvent BrownianKilledGreenKernel
open BrownianKilledGreenBoundary BrownianKilledGreenWeightedBound
open BrownianKilledAreaResolventPointwiseFiniteness

theorem greenReal_div_start_mul_target_le (p : ℝ) (hp : 0 < p)
    (x z : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (hz : 0 ≤ z) :
    greenReal p x z/x*z ≤ 2*Real.exp (Real.sqrt (2*p))/Real.sqrt (2*p) := by
  let s := Real.sqrt (2*p)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hg : greenReal p x z/x ≤ 2*Real.exp (-|z-x| *s) := by
    apply (div_le_iff₀ hx).mpr
    calc
      _ ≤ 2*min x z*Real.exp (-|z-x| *s) := greenReal_le_two_min_exp_gap p hp x z
      _ ≤ 2*x*Real.exp (-|z-x| *s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_left x z) (by norm_num))
          (Real.exp_pos _).le
      _ = _ := by ring
  have he : Real.exp (-|z-x| *s) ≤ Real.exp s*Real.exp (-z*s) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha : -|z-x| ≤ x-z := by linarith [le_abs_self (z-x)]
    have h := mul_le_mul_of_nonneg_right ha hs.le
    nlinarith
  calc
    _ ≤ 2*Real.exp (-|z-x| *s)*z := mul_le_mul_of_nonneg_right hg hz
    _ ≤ 2*(Real.exp s*Real.exp (-z*s))*z := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) hz
    _ = (2*Real.exp s)*(z*Real.exp (-z*s)) := by ring
    _ ≤ (2*Real.exp s)*(1/s) :=
      mul_le_mul_of_nonneg_left (mul_exp_neg_mul_le_inv s hs z) (by positivity)
    _ = _ := by dsimp only [s]; ring

theorem actual_normalized_green_mul_target_le (p : ℝ) (hp : 0 < p)
    (x z : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    ENNReal.ofReal ((resolvent 0 p x z).toReal/x)*ENNReal.ofReal z ≤
      ENNReal.ofReal (2*Real.exp (Real.sqrt (2*p))/Real.sqrt (2*p)) := by
  by_cases hz : 0 < z
  · rw [resolvent_zero_eq_green p hp x z hx hz,
      ENNReal.toReal_ofReal (greenReal_nonneg p x z hx hz),← ENNReal.ofReal_mul' hz.le]
    exact ENNReal.ofReal_le_ofReal (greenReal_div_start_mul_target_le p hp x z hx hx1 hz.le)
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hz),mul_zero]
    exact zero_le

theorem normalized_succ_eq (n : ℕ) (p : ℝ) (hp : 0 < p) (x y : ℝ) (hx : 0 < x) :
    resolvent (n+1) p x y/ENNReal.ofReal x = ((n+1 : ℕ) : ℝ≥0∞)*
      ∫⁻ z : ℝ, ENNReal.ofReal ((resolvent 0 p x z).toReal/x)*ENNReal.ofReal z*
        resolvent n p z y := by
  have hi : (ENNReal.ofReal x)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr
    (ENNReal.ofReal_ne_zero_iff.mpr hx)
  have he (z : ℝ) : ENNReal.ofReal ((resolvent 0 p x z).toReal/x) =
      resolvent 0 p x z*(ENNReal.ofReal x)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos hx,ENNReal.ofReal_toReal (resolvent_zero_ne_top p hp x z),
      div_eq_mul_inv]
  calc
    _ = ((n+1 : ℕ) : ℝ≥0∞)*((ENNReal.ofReal x)⁻¹*
        ∫⁻ z : ℝ, resolvent 0 p x z*ENNReal.ofReal z*resolvent n p z y) := by
      rw [resolvent_succ,div_eq_mul_inv]
      ac_rfl
    _ = ((n+1 : ℕ) : ℝ≥0∞)*∫⁻ z : ℝ, (ENNReal.ofReal x)⁻¹*
        (resolvent 0 p x z*ENNReal.ofReal z*resolvent n p z y) := by
      rw [lintegral_const_mul' _ _ hi]
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro z
      rw [he]
      ac_rfl

theorem boundary_insert_mass_ne_top (n : ℕ) (p : ℝ) (hp : 0 < p) (y : ℝ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p)))*ENNReal.ofReal z*
      resolvent n p z y) ≠ ⊤ := by
  have hs : 0 < Real.sqrt (2*p) := Real.sqrt_pos.mpr (by positivity)
  have hb : (∫⁻ z : ℝ, ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p)))*ENNReal.ofReal z*
      resolvent n p z y) ≤ ENNReal.ofReal (2/Real.sqrt (2*p))*(∫⁻ z : ℝ, resolvent n p z y) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro z
    refine mul_le_mul' ?_ le_rfl
    by_cases hz : 0 < z
    · rw [← ENNReal.ofReal_mul' hz.le]
      apply ENNReal.ofReal_le_ofReal
      have h := mul_le_mul_of_nonneg_left
        (mul_exp_neg_mul_le_inv (Real.sqrt (2*p)) hs z) (by norm_num : (0 : ℝ) ≤ 2)
      calc
        _ = 2*(z*Real.exp (-z*Real.sqrt (2*p))) := by ring
        _ ≤ 2*(1/Real.sqrt (2*p)) := h
        _ = _ := by ring
    · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hz),mul_zero]
      exact zero_le
  have hf : ENNReal.ofReal (2/Real.sqrt (2*p))*(∫⁻ z : ℝ, resolvent n p z y) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (initial_total_mass_ne_top n p hp y)
  exact ne_of_lt (hb.trans_lt (lt_top_iff_ne_top.mpr hf))

theorem actual_resolvent_succ_boundary_slope (n : ℕ) (p : ℝ) (hp : 0 < p) (y : ℝ) :
    Tendsto (fun x : ℝ ↦ resolvent (n+1) p x y/ENNReal.ofReal x) (𝓝[>] 0)
      (𝓝 (((n+1 : ℕ) : ℝ≥0∞)*∫⁻ z : ℝ,
        ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p)))*ENNReal.ofReal z*resolvent n p z y)) := by
  let F (x z : ℝ) := ENNReal.ofReal ((resolvent 0 p x z).toReal/x)*ENNReal.ofReal z*
    resolvent n p z y
  let C := ENNReal.ofReal (2*Real.exp (Real.sqrt (2*p))/Real.sqrt (2*p))
  have hmeas (x : ℝ) : Measurable (F x) :=
    (((((measurable_resolvent 0 p).comp
      (measurable_const.prodMk measurable_id)).ennreal_toReal.div_const x).ennreal_ofReal).mul
        measurable_id.ennreal_ofReal).mul
      ((measurable_resolvent n p).comp (measurable_id.prodMk measurable_const))
  have hbound : ∀ᶠ x : ℝ in 𝓝[>] 0, ∀ᵐ z : ℝ ∂volume, F x z ≤ C*resolvent n p z y := by
    have hsmall : ∀ᶠ x : ℝ in 𝓝[>] 0, x ≤ 1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds |>.mono
        (fun _ hx ↦ hx.le)
    filter_upwards [self_mem_nhdsWithin,hsmall] with x hx hx1
    exact Eventually.of_forall (fun z ↦ mul_le_mul'
      (actual_normalized_green_mul_target_le p hp x z hx hx1) le_rfl)
  have hfin : (∫⁻ z : ℝ, C*resolvent n p z y) ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (initial_total_mass_ne_top n p hp y)
  have hlim : ∀ᵐ z : ℝ ∂volume, Tendsto (fun x : ℝ ↦ F x z) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p)))*ENNReal.ofReal z*
        resolvent n p z y)) := by
    apply Eventually.of_forall
    intro z
    by_cases hz : 0 < z
    · have h := ENNReal.tendsto_ofReal (actual_resolvent_boundary_slope p hp z hz)
      exact ENNReal.Tendsto.mul_const
        (ENNReal.Tendsto.mul_const h (Or.inr ENNReal.ofReal_ne_top))
        (Or.inr (resolvent_ne_top n p hp z y))
    · simp only [F,ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hz),mul_zero,zero_mul]
      exact tendsto_const_nhds
  have h := tendsto_lintegral_filter_of_dominated_convergence
    (fun z ↦ C*resolvent n p z y) (Eventually.of_forall hmeas) hbound hfin hlim
  have hh := ENNReal.Tendsto.const_mul h (Or.inr (by simp : ((n+1 : ℕ) : ℝ≥0∞) ≠ ⊤))
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (normalized_succ_eq n p hp x y hx).symm

theorem actual_resolvent_succ_boundary_slope_real (n : ℕ) (p : ℝ) (hp : 0 < p) (y : ℝ) :
    Tendsto (fun x : ℝ ↦ (resolvent (n+1) p x y).toReal/x) (𝓝[>] 0)
      (𝓝 (((n+1 : ℕ) : ℝ)*∫ z : ℝ,
        2*Real.exp (-z*Real.sqrt (2*p))*(ENNReal.ofReal z).toReal*(resolvent n p z y).toReal)) := by
  let A (z : ℝ) := ENNReal.ofReal (2*Real.exp (-z*Real.sqrt (2*p)))*ENNReal.ofReal z*
    resolvent n p z y
  have heM : Measurable (fun z : ℝ ↦ 2*Real.exp (-z*Real.sqrt (2*p))) :=
    measurable_const.mul ((measurable_id.neg.mul_const (Real.sqrt (2*p))).exp)
  have hA : Measurable A := (heM.ennreal_ofReal.mul measurable_id.ennreal_ofReal).mul
    ((measurable_resolvent n p).comp (measurable_id.prodMk measurable_const))
  have hf : ((n+1 : ℕ) : ℝ≥0∞)*(∫⁻ z : ℝ, A z) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (boundary_insert_mass_ne_top n p hp y)
  have h := (ENNReal.tendsto_toReal hf).comp (actual_resolvent_succ_boundary_slope n p hp y)
  have he : (∫⁻ z : ℝ, A z).toReal = ∫ z : ℝ,
      2*Real.exp (-z*Real.sqrt (2*p))*(ENNReal.ofReal z).toReal*(resolvent n p z y).toReal := by
    rw [← integral_toReal hA.aemeasurable (Eventually.of_forall (fun z ↦
      lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (resolvent_ne_top n p hp z y))))]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    simp only [A,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity :
      0 ≤ 2*Real.exp (-z*Real.sqrt (2*p)))]
  rw [ENNReal.toReal_mul,ENNReal.toReal_natCast,he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  dsimp only [Function.comp_def]
  rw [ENNReal.toReal_div,ENNReal.toReal_ofReal (show 0 ≤ x from hx.le)]

end PerronWright.BrownianKilledAreaResolventBoundary
