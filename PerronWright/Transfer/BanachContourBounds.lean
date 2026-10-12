import PerronWright.Transfer.BanachCauchy
import PerronWright.Transfer.DeltaContour
import PerronWright.Transfer.DeltaDecay

/-! Genuine Banach-valued bounds for the local keyhole circle. -/

open Real MeasureTheory Set
noncomputable section

namespace PerronWright.Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem banach_norm_radial_integral_le {a M c : ℝ} {n : ℕ} {f : ℝ → E}
    (ha : -1 < a) (hM : 0 ≤ M) (hc : 0 < c) (hn : 0 < n)
    (hbound : ∀ t ∈ Set.Ioc (0 : ℝ) M,
      ‖f t‖ ≤ t ^ a * exp (-(c * (n : ℝ) * t))) :
    ‖∫ t in (0 : ℝ)..M, f t‖ ≤
      (1 / (c * n)) ^ (a + 1) * Gamma (a + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hrate : 0 < c * (n : ℝ) := mul_pos hc hn'
  have ha' : 0 < a + 1 := by linarith
  have hkey := Real.integral_rpow_mul_exp_neg_mul_Ioi ha' hrate
  have hint : IntegrableOn
      (fun t : ℝ => t ^ ((a + 1) - 1) * exp (-((c * n) * t)))
      (Ioi 0) := .of_integral_ne_zero (by
        rw [hkey]
        exact (mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hrate) _)
          (Real.Gamma_pos_of_pos ha')).ne')
  have hmajor : IntervalIntegrable
      (fun t : ℝ => t ^ a * exp (-(c * (n : ℝ) * t)))
      MeasureTheory.volume 0 M := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hM]
    simpa only [add_sub_cancel_right] using hint.mono_set Ioc_subset_Ioi_self
  exact (intervalIntegral.norm_integral_le_of_norm_le hM
    (Filter.Eventually.of_forall (fun t ht => hbound t ht)) hmajor).trans
      (laplace_ray_bound ha hM hc hn)

theorem banach_radial_piece_bound {F : ℂ → E} {d : ℂ}
    {M a : ℝ} {n : ℕ}
    (hd : ‖d‖ = 1) (hdre : d.re = 3 / 5)
    (hM : 0 ≤ M) (hM1 : M ≤ 1) (ha : -1 < a) (hn : 0 < n)
    (hF : ∀ t ∈ Ioc (0 : ℝ) M,
      ‖F ((1 : ℂ) + (t : ℂ) * d)‖ ≤ t ^ a) :
    ‖∫ t in (0 : ℝ)..M,
        (d * (((1 : ℂ) + (t : ℂ) * d)⁻¹ ^ (n + 1))) •
          F ((1 : ℂ) + (t : ℂ) * d)‖ ≤
      (1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1) := by
  apply banach_norm_radial_integral_le ha hM (by norm_num) hn
  intro t ht
  have ht0 : 0 ≤ t := ht.1.le
  have ht1 : t ≤ 1 := ht.2.trans hM1
  let z : ℂ := 1 + (t : ℂ) * d
  have hden : ‖z⁻¹ ^ (n + 1)‖ ≤ exp (-((n : ℝ) * t / 4)) :=
    ray_inverse_pow_bound d hd hdre ht0 ht1 n
  calc
    ‖(d * z⁻¹ ^ (n + 1)) • F z‖ = ‖F z‖ * ‖z⁻¹ ^ (n + 1)‖ := by
      rw [norm_smul, norm_mul, hd, one_mul, mul_comm]
    _ ≤ t ^ a * exp (-((n : ℝ) * t / 4)) :=
      mul_le_mul (hF t ht) hden (norm_nonneg _)
        (Real.rpow_nonneg ht0 _)
    _ = t ^ a * exp (-((1 / 4 : ℝ) * (n : ℝ) * t)) := by
      congr 1
      ring_nf

theorem banach_outer_arc_bound {F : ℂ → E}
    {R M θ₀ θ₁ : ℝ} {n : ℕ}
    (hR : 1 < R) (hM : 0 ≤ M) (hθ : θ₀ ≤ θ₁)
    (hF : ∀ θ ∈ Icc θ₀ θ₁, ‖F (circleMap 0 R θ)‖ ≤ M) :
    ‖∫ θ in θ₀..θ₁,
        (deriv (circleMap 0 R) θ *
          ((circleMap 0 R θ)⁻¹ ^ (n + 1))) •
            F (circleMap 0 R θ)‖ ≤
      (θ₁ - θ₀) * (R * M * exp (-((n : ℝ) * (log R / 2)))) := by
  have hR0 : 0 ≤ R := le_of_lt (lt_trans zero_lt_one hR)
  have hconst : ∀ θ ∈ Set.uIoc θ₀ θ₁,
      ‖(deriv (circleMap 0 R) θ *
          ((circleMap 0 R θ)⁻¹ ^ (n + 1))) •
            F (circleMap 0 R θ)‖ ≤
        R * M * exp (-((n : ℝ) * (log R / 2))) := by
    intro θ hθmem
    have hθmem' : θ ∈ Icc θ₀ θ₁ :=
      Ioc_subset_Icc_self (by simpa [uIoc_of_le hθ] using hθmem)
    let z : ℂ := circleMap 0 R θ
    have hz : ‖z‖ = R := by
      simp [z, norm_circleMap_zero, abs_of_pos (lt_trans zero_lt_one hR)]
    have hden : ‖z⁻¹ ^ (n + 1)‖ ≤
        exp (-((n : ℝ) * (log R / 2))) :=
      outer_circle_inverse_pow_bound hR hz n
    calc
      ‖(deriv (circleMap 0 R) θ * z⁻¹ ^ (n + 1)) • F z‖ =
          R * (‖F z‖ * ‖z⁻¹ ^ (n + 1)‖) := by
        rw [norm_smul, norm_mul, deriv_circleMap, norm_mul,
          Complex.norm_I, hz, mul_one]
        ring
      _ ≤ R * (M * exp (-((n : ℝ) * (log R / 2)))) := by
        apply mul_le_mul_of_nonneg_left _ hR0
        exact mul_le_mul (hF θ hθmem') hden (norm_nonneg _) hM
      _ = R * M * exp (-((n : ℝ) * (log R / 2))) := by ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hconst
  rw [abs_of_nonneg (sub_nonneg.mpr hθ)] at hb
  convert hb using 1
  ring_nf

theorem banach_outer_arc_integral_isLittleO {F : ℂ → E}
    {R B θ₀ θ₁ : ℝ} (hR : 1 < R) (hB : 0 ≤ B) (hθ : θ₀ ≤ θ₁)
    (hF : ∀ θ ∈ Icc θ₀ θ₁, ‖F (circleMap 0 R θ)‖ ≤ B)
    (a : ℝ) :
    (fun n : ℕ => ∫ θ in θ₀..θ₁,
        (deriv (circleMap 0 R) θ *
          ((circleMap 0 R θ)⁻¹ ^ (n + 1))) •
            F (circleMap 0 R θ)) =o[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ a) := by
  let c := Real.log R / 2
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (Real.log_pos hR) (by norm_num)
  have hdom :
      (fun n : ℕ => ∫ θ in θ₀..θ₁,
        (deriv (circleMap 0 R) θ *
          ((circleMap 0 R θ)⁻¹ ^ (n + 1))) •
            F (circleMap 0 R θ)) =O[Filter.atTop]
        (fun n : ℕ => Real.exp (-(c * (n : ℝ)))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨(θ₁ - θ₀) * R * B, Filter.Eventually.of_forall ?_⟩
    intro n
    have hb := banach_outer_arc_bound hR hB hθ hF (n := n)
    have hnorm : ‖Real.exp (-(c * (n : ℝ)))‖ =
        Real.exp (-(c * (n : ℝ))) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hnorm]
    refine hb.trans_eq ?_
    dsimp [c]
    ring_nf
  exact hdom.trans_isLittleO (exp_neg_nat_isLittleO_rpow hc a)

theorem banach_inner_circle_piece_bound {F : ℂ → E} {a : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hF : ∀ z ∈ Metric.sphere (1 : ℂ) (1 / (2 * (n : ℝ))),
      ‖F z‖ ≤ ‖z - 1‖ ^ a) :
    ‖∮ z in C((1 : ℂ), 1 / (2 * (n : ℝ))),
      z⁻¹ ^ (n + 1) • F z‖ ≤
      (2 * π * exp 2) * (1 / (2 * (n : ℝ))) ^ (a + 1) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hbound : ∀ z ∈ Metric.sphere (1 : ℂ) (1 / (2 * (n : ℝ))),
      ‖z⁻¹ ^ (n + 1) • F z‖ ≤
        (1 / (2 * (n : ℝ))) ^ a * exp 2 := by
    intro z hz
    have hz' : ‖z - 1‖ = 1 / (2 * (n : ℝ)) := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    rw [norm_smul]
    calc
      ‖z⁻¹ ^ (n + 1)‖ * ‖F z‖ = ‖F z‖ * ‖z⁻¹ ^ (n + 1)‖ := mul_comm _ _
      _ ≤ (1 / (2 * (n : ℝ))) ^ a * exp 2 :=
        mul_le_mul (by simpa only [hz'] using hF z hz)
          (inner_circle_inverse_bound hn hz')
          (norm_nonneg _) (Real.rpow_nonneg hr.le _)
  have hb := circleIntegral.norm_integral_le_of_norm_le_const hr.le hbound
  calc
    ‖∮ z in C((1 : ℂ), 1 / (2 * (n : ℝ))),
        z⁻¹ ^ (n + 1) • F z‖ ≤
        2 * π * (1 / (2 * (n : ℝ))) *
          ((1 / (2 * (n : ℝ))) ^ a * exp 2) := hb
    _ = (2 * π * exp 2) * (1 / (2 * (n : ℝ))) ^ (a + 1) := by
      rw [Real.rpow_add hr]
      simp only [Real.rpow_one]
      ring

theorem banach_contour_piece_sum_bound {F : ℂ → E} {dUp dDown : ℂ}
    {M R B θ₀ θ₁ a : ℝ} {n : ℕ}
    (hdUp : ‖dUp‖ = 1) (hreUp : dUp.re = 3 / 5)
    (hdDown : ‖dDown‖ = 1) (hreDown : dDown.re = 3 / 5)
    (hM : 0 ≤ M) (hM1 : M ≤ 1) (hR : 1 < R) (hB : 0 ≤ B)
    (hθ : θ₀ ≤ θ₁) (ha : -1 < a) (hn : 0 < n)
    (hFUp : ∀ t ∈ Ioc (0 : ℝ) M,
      ‖F ((1 : ℂ) + (t : ℂ) * dUp)‖ ≤ t ^ a)
    (hFDown : ∀ t ∈ Ioc (0 : ℝ) M,
      ‖F ((1 : ℂ) + (t : ℂ) * dDown)‖ ≤ t ^ a)
    (hFi : ∀ z ∈ Metric.sphere (1 : ℂ) (1 / (2 * (n : ℝ))),
      ‖F z‖ ≤ ‖z - 1‖ ^ a)
    (hFo : ∀ θ ∈ Icc θ₀ θ₁,
      ‖F (circleMap 0 R θ)‖ ≤ B) :
    ‖(∫ t in (0 : ℝ)..M,
          (dUp * (((1 : ℂ) + (t : ℂ) * dUp)⁻¹ ^ (n + 1))) •
            F ((1 : ℂ) + (t : ℂ) * dUp)) +
      (∫ t in (0 : ℝ)..M,
          (dDown * (((1 : ℂ) + (t : ℂ) * dDown)⁻¹ ^ (n + 1))) •
            F ((1 : ℂ) + (t : ℂ) * dDown)) +
      (∮ z in C((1 : ℂ), 1 / (2 * (n : ℝ))),
        z⁻¹ ^ (n + 1) • F z) +
      (∫ θ in θ₀..θ₁,
          (deriv (circleMap 0 R) θ *
            ((circleMap 0 R θ)⁻¹ ^ (n + 1))) •
              F (circleMap 0 R θ))‖ ≤
      2 * ((1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1)) +
      (2 * π * exp 2) * (1 / (2 * (n : ℝ))) ^ (a + 1) +
      (θ₁ - θ₀) * (R * B * exp (-((n : ℝ) * (log R / 2)))) := by
  let U : E := ∫ t in (0 : ℝ)..M,
    (dUp * (((1 : ℂ) + (t : ℂ) * dUp)⁻¹ ^ (n + 1))) •
      F ((1 : ℂ) + (t : ℂ) * dUp)
  let L : E := ∫ t in (0 : ℝ)..M,
    (dDown * (((1 : ℂ) + (t : ℂ) * dDown)⁻¹ ^ (n + 1))) •
      F ((1 : ℂ) + (t : ℂ) * dDown)
  let I : E := ∮ z in C((1 : ℂ), 1 / (2 * (n : ℝ))),
    z⁻¹ ^ (n + 1) • F z
  let O : E := ∫ θ in θ₀..θ₁,
    (deriv (circleMap 0 R) θ *
      ((circleMap 0 R θ)⁻¹ ^ (n + 1))) • F (circleMap 0 R θ)
  have hU : ‖U‖ ≤ (1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1) :=
    banach_radial_piece_bound hdUp hreUp hM hM1 ha hn hFUp
  have hL : ‖L‖ ≤ (1 / ((1 / 4 : ℝ) * n)) ^ (a + 1) * Gamma (a + 1) :=
    banach_radial_piece_bound hdDown hreDown hM hM1 ha hn hFDown
  have hI : ‖I‖ ≤
      (2 * π * exp 2) * (1 / (2 * (n : ℝ))) ^ (a + 1) :=
    banach_inner_circle_piece_bound hn hFi
  have hO : ‖O‖ ≤
      (θ₁ - θ₀) * (R * B * exp (-((n : ℝ) * (log R / 2)))) :=
    banach_outer_arc_bound hR hB hθ hFo
  change ‖U + L + I + O‖ ≤ _
  have h1 := norm_add_le U L
  have h2 := norm_add_le (U + L) I
  have h3 := norm_add_le (U + L + I) O
  linarith

end PerronWright.Transfer
