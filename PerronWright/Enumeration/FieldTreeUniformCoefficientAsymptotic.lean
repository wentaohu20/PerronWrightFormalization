import PerronWright.Enumeration.FieldTreeDeltaRemainder
import PerronWright.Enumeration.ZeroFieldTreeCoefficientAsymptotic
import PerronWright.Transfer.UniformCartesianTransfer

/-!
# Field-uniform tree Taylor-coefficient asymptotics

The field ball is used only as an index type for the family-uniform
Cartesian transfer theorem.  No compactness of that ball is asserted.
There is one radius, one analytic cubic amplitude, and one pair of constants
`K,N` such that, simultaneously for every field in the ball and every
`n >= N`, the literal normalized field-tree coefficient differs from its
`(1-w)^(3/2)` main term by at most `K n^(-3)`.
-/

open Filter Topology Set Asymptotics
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.FieldTreeUniformCoefficientAsymptotic

namespace Delta

export PerronWright.FieldTreeDeltaRemainder
  (exists_normalizedFieldTree_cartesianDelta_transfer_data)

end Delta


namespace Global

export PerronWright.FieldTreeEGFMatching
  (normalizedFieldTreeFMS)

end Global

namespace ZF

export PerronWright.ZeroFieldTreeCoefficientAsymptotic
  (taylorCoefficient_cartesianDeltaSqrt_cube)

end ZF

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem oneDimensionalFMS_eq_ofScalars
    (p : FormalMultilinearSeries ℂ ℂ ℂ) :
    p = FormalMultilinearSeries.ofScalars ℂ (fun n ↦ p.coeff n) := by
  let P : PowerSeries ℂ := oneDimensionalPowerSeries p
  have hP : oneDimensionalFormalMultilinearSeries P =
      FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ PowerSeries.coeff n P) := by
    let c : ℕ → ℂ := fun n ↦ PowerSeries.coeff n P
    have hpower : oneDimensionalPowerSeries
        (FormalMultilinearSeries.ofScalars ℂ c) = P := by
      apply PowerSeries.ext
      intro n
      simp only [oneDimensionalPowerSeries_coeff,
        FormalMultilinearSeries.coeff_ofScalars, c]
    calc
      oneDimensionalFormalMultilinearSeries P =
          oneDimensionalFormalMultilinearSeries
            (oneDimensionalPowerSeries
              (FormalMultilinearSeries.ofScalars ℂ c)) :=
        congrArg oneDimensionalFormalMultilinearSeries hpower.symm
      _ = FormalMultilinearSeries.ofScalars ℂ c :=
        oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries _
      _ = FormalMultilinearSeries.ofScalars ℂ
          (fun n ↦ PowerSeries.coeff n P) := by rfl
  calc
    p = oneDimensionalFormalMultilinearSeries P :=
      (oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries p).symm
    _ = FormalMultilinearSeries.ofScalars ℂ
        (fun n ↦ PowerSeries.coeff n P) := hP
    _ = FormalMultilinearSeries.ofScalars ℂ (fun n ↦ p.coeff n) := by
      congr 1
      funext n
      simp only [P, oneDimensionalPowerSeries_coeff]

private theorem taylorCoefficient_eq_fms_coeff
    {F : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hF : HasFPowerSeriesAt F p 0) (n : ℕ) :
    Transfer.taylorCoefficient F n = p.coeff n := by
  have hp := oneDimensionalFMS_eq_ofScalars p
  rw [hp] at hF
  exact Transfer.taylorCoefficient_eq_seriesCoefficient hF n

private theorem taylorCoefficient_eq_banachTaylorCoefficient
    (F : ℂ → ℂ) (n : ℕ) :
    Transfer.taylorCoefficient F n =
      Transfer.banachTaylorCoefficient F n := by
  simp only [Transfer.taylorCoefficient,
    Transfer.banachTaylorCoefficient, smul_eq_mul, div_eq_mul_inv]
  ring

private theorem taylorCoefficient_const_mul
    (c : ℂ) (F : ℂ → ℂ) (n : ℕ) :
    Transfer.taylorCoefficient (fun w ↦ c * F w) n =
      c * Transfer.taylorCoefficient F n := by
  simp only [Transfer.taylorCoefficient,
    iteratedDeriv_const_mul_field, mul_div_assoc]

private theorem taylorCoefficient_add
    {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hG : AnalyticAt ℂ G 0) (n : ℕ) :
    Transfer.taylorCoefficient (fun w ↦ F w + G w) n =
      Transfer.taylorCoefficient F n +
        Transfer.taylorCoefficient G n := by
  simp only [Transfer.taylorCoefficient,
    iteratedDeriv_fun_add hF.contDiffAt hG.contDiffAt, add_div]

private theorem taylorCoefficient_fieldAffine_eq_zero
    (C A : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    Transfer.taylorCoefficient (fun w : ℂ ↦ C + A * (1 - w)) n = 0 := by
  have hfun : (fun w : ℂ ↦ C + A * (1 - w)) =
      (fun w : ℂ ↦ (C + A) + (-A) * w) := by
    funext w
    ring
  rw [hfun, Transfer.taylorCoefficient,
    iteratedDeriv_const_add (by omega : 0 < n) (C + A),
    iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_fun_id_zero,
    if_neg (by omega : n ≠ 1), mul_zero, zero_div]

/-- Uniform coefficient form of the joint field-tree transfer theorem.
The coefficient on the left is literally the normalized complex-field tree
FMS coefficient, not an auxiliary continuation coefficient. -/
theorem exists_normalizedFieldTree_coefficient_uniform_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (A₃ : C(S, ℂ) → ℂ) (s K : ℝ) (N : ℕ),
      0 < s ∧ 0 < K ∧
      AnalyticOnNhd ℂ A₃ (Metric.ball (0 : C(S, ℂ)) s) ∧
      A₃ 0 = 2 * (FoldCoefficients.gamma M hM : ℂ) / 3 ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        ∀ n : ℕ, N ≤ n →
          ‖(Global.normalizedFieldTreeFMS M hM g).coeff n -
              A₃ g * (Transfer.coefficient (-(3 / 2)) n : ℂ)‖ ≤
            K * (n : ℝ) ^ (-(3 : ℝ)) := by
  obtain ⟨C, A₂, A₃, G, H, eta, m, s, B,
      heta, hm, hm43, hs, hB, hC, hA₂, hA₃,
      hA₂zero, hA₃zero, hG, hH, hFormula, hHbound, hTaylor⟩ :=
    Delta.exists_normalizedFieldTree_cartesianDelta_transfer_data M hM

  let 𝒢 := ↥(Metric.ball (0 : C(S, ℂ)) s)
  let Hslice : 𝒢 → ℂ → ℂ := fun g w ↦ H (w, (g : C(S, ℂ)))
  let Q : 𝒢 → ℂ → ℂ := fun g w ↦ ((B : ℂ)⁻¹) * Hslice g w
  have hQdiff : ∀ g : 𝒢,
      DifferentiableOn ℂ (Q g) (Transfer.cartesianDelta eta m) := by
    intro g w hw
    have hHs : AnalyticAt ℂ (Hslice g) w :=
      (hH (w, (g : C(S, ℂ))) ⟨hw, g.property⟩).comp_of_eq
        (analyticAt_id.prod analyticAt_const) rfl
    exact (analyticAt_const.mul hHs).differentiableAt.differentiableWithinAt
  have hQpower : ∀ g : 𝒢, ∀ w ∈ Transfer.cartesianDelta eta m,
      ‖Q g w‖ ≤ ‖w - 1‖ ^ (2 : ℝ) := by
    intro g w hw
    have hBnorm : ‖((B : ℂ)⁻¹)‖ = B⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    calc
      ‖Q g w‖ = B⁻¹ * ‖H (w, (g : C(S, ℂ)))‖ := by
        dsimp only [Q, Hslice]
        rw [norm_mul, hBnorm]
      _ ≤ B⁻¹ * (B * ‖w - 1‖ ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (hHbound (w, (g : C(S, ℂ))) ⟨hw, g.property⟩)
          (inv_nonneg.mpr hB.le)
      _ = ‖w - 1‖ ^ (2 : ℝ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul]

  let Mcontour : ℝ := min (eta / 2) 1
  have hMcontour : 0 < Mcontour := by
    dsimp only [Mcontour]
    exact lt_min (half_pos heta) zero_lt_one
  have hMcontourOne : Mcontour ≤ 1 := min_le_right _ _
  have hMcontourEta : Mcontour < eta :=
    (min_le_left (eta / 2) 1).trans_lt (half_lt_self heta)
  obtain ⟨KQ, hKQ, hQcoeff⟩ :=
    Transfer.exists_uniform_banachCartesianTaylorCoefficient_bound
      (F := Q) (M := Mcontour) (eta := eta) (m := m)
      (a := (2 : ℝ)) hMcontour hMcontourOne hMcontourEta
      hm.le hm43 (by norm_num) hQdiff hQpower
  obtain ⟨NQ, hNQ⟩ := Filter.eventually_atTop.1 hQcoeff
  let K : ℝ := B * KQ
  let N : ℕ := max NQ 2
  have hK : 0 < K := mul_pos hB hKQ
  refine ⟨A₃, s, K, N, hs, hK, hA₃, hA₃zero, ?_⟩
  intro g hg n hn
  have hnQ : NQ ≤ n := (le_max_left NQ 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right NQ 2).trans hn
  let gi : 𝒢 := ⟨g, hg⟩
  have hQn : ‖Transfer.banachTaylorCoefficient (Q gi) n‖ ≤
      KQ * (n : ℝ) ^ (-((2 : ℝ) + 1)) :=
    hNQ n hnQ gi
  have hQn' : ‖Transfer.banachTaylorCoefficient (Q gi) n‖ ≤
      KQ * (n : ℝ) ^ (-(3 : ℝ)) := by
    simpa only [show -((2 : ℝ) + 1) = -(3 : ℝ) by norm_num] using hQn

  let H_g : ℂ → ℂ := fun w ↦ H (w, g)
  have hCoeffScale :
      Transfer.banachTaylorCoefficient H_g n =
        (B : ℂ) * Transfer.banachTaylorCoefficient (Q gi) n := by
    simp only [Transfer.banachTaylorCoefficient, Q, Hslice, gi,
      iteratedDeriv_const_mul_field, smul_eq_mul]
    field_simp [hB.ne']
    rfl
  have hHcoeffBound :
      ‖Transfer.taylorCoefficient H_g n‖ ≤
        K * (n : ℝ) ^ (-(3 : ℝ)) := by
    rw [taylorCoefficient_eq_banachTaylorCoefficient, hCoeffScale,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    calc
      B * ‖Transfer.banachTaylorCoefficient (Q gi) n‖ ≤
          B * (KQ * (n : ℝ) ^ (-(3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hQn' hB.le
      _ = K * (n : ℝ) ^ (-(3 : ℝ)) := by
        dsimp only [K]
        ring

  have hzeroDelta : (0 : ℂ) ∈ Transfer.cartesianDelta eta m :=
    Transfer.unit_ball_subset_cartesianDelta heta
      (by simpa only [Metric.mem_ball, dist_zero_right, norm_zero] using
        (zero_lt_one : (0 : ℝ) < 1))
  have hG0 : AnalyticAt ℂ (fun w : ℂ ↦ G (w, g)) 0 :=
    (hG (0, g) ⟨hzeroDelta, hg⟩).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  have hAffine0 : AnalyticAt ℂ
      (fun w : ℂ ↦ C g + A₂ g * (1 - w)) 0 := by
    fun_prop
  have hX0 : AnalyticAt ℂ Transfer.cartesianDeltaSqrt 0 :=
    Transfer.analyticOnNhd_cartesianDeltaSqrt
      (m := m) hm.le 0 hzeroDelta
  have hCubic0 : AnalyticAt ℂ
      (fun w : ℂ ↦ A₃ g * Transfer.cartesianDeltaSqrt w ^ 3) 0 :=
    analyticAt_const.mul (hX0.pow 3)
  have hP0 : AnalyticAt ℂ
      (fun w : ℂ ↦ C g + A₂ g * (1 - w) +
        A₃ g * Transfer.cartesianDeltaSqrt w ^ 3) 0 :=
    hAffine0.add hCubic0
  have hCoeffGenuine :
      Transfer.taylorCoefficient (fun w : ℂ ↦ G (w, g)) n =
        (Global.normalizedFieldTreeFMS M hM g).coeff n :=
    taylorCoefficient_eq_fms_coeff (hTaylor g hg) n
  have hCubicCoeff :
      Transfer.taylorCoefficient
          (fun w : ℂ ↦ A₃ g *
            Transfer.cartesianDeltaSqrt w ^ 3) n =
        A₃ g * (Transfer.coefficient (-(3 / 2)) n : ℂ) := by
    rw [taylorCoefficient_const_mul,
      ZF.taylorCoefficient_cartesianDeltaSqrt_cube]
  have hsumCoeff :
      Transfer.taylorCoefficient
          (fun w : ℂ ↦ C g + A₂ g * (1 - w) +
            A₃ g * Transfer.cartesianDeltaSqrt w ^ 3) n =
        A₃ g * (Transfer.coefficient (-(3 / 2)) n : ℂ) := by
    have hadd := taylorCoefficient_add hAffine0 hCubic0 n
    rw [hadd, taylorCoefficient_fieldAffine_eq_zero (C g) (A₂ g) hn2,
      hCubicCoeff, zero_add]
  have hsub := Transfer.taylorCoefficient_sub
    (F := fun w : ℂ ↦ G (w, g))
    (G := fun w : ℂ ↦ C g + A₂ g * (1 - w) +
      A₃ g * Transfer.cartesianDeltaSqrt w ^ 3)
    hG0 hP0 n
  have hfun : (fun w : ℂ ↦
      G (w, g) - (C g + A₂ g * (1 - w) +
        A₃ g * Transfer.cartesianDeltaSqrt w ^ 3)) = H_g := by
    funext w
    rw [hFormula (w, g)]
    dsimp only [H_g]
    ring
  rw [hfun, hsumCoeff, hCoeffGenuine] at hsub
  rw [← hsub]
  exact hHcoeffBound

end PerronWright.FieldTreeUniformCoefficientAsymptotic
