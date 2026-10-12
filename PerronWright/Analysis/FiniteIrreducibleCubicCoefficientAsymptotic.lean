import PerronWright.Analysis.FiniteIrreducibleCubicTransferData
import PerronWright.Enumeration.PositiveSurplusCubicConstantPositivity
import PerronWright.Enumeration.PositiveSurplusWrightTransferMain
import PerronWright.Transfer.HalfStepHierarchy
import PerronWright.Transfer.UniformCartesianTransfer

/-!
# Field-uniform coefficient transfer for the positive-surplus cubic part

The finite Puiseux polynomial supplied by the joint vertical Taylor theorem
is transferred term by term.  Every vertical degree `j` below `3 * ell`
loses `j/2` powers of the coefficient index relative to the leading term.
The global square-root remainder is handled by the family-uniform Cartesian
transfer theorem.  The final statement is normalized by the exact leading
pure-power coefficient and keeps the field displacement and the universal
half-step transfer error separate.
-/

open Filter Topology Set Asymptotics
open scoped Classical Topology BigOperators ENNReal NNReal

noncomputable section

namespace PerronWright.FiniteIrreducibleCubicCoefficientAsymptotic

open PerronWright.GraphCore PerronWright.FiniteIrreducibleKernelAmplitude

namespace Data

export PerronWright.FiniteIrreducibleCubicTransferData
  (positiveSurplusCubicPuiseuxPolynomial
   exists_normalizedFieldCubicPart_cartesianDelta_transfer_data)

end Data

namespace Global

export PerronWright.FiniteIrreducibleCubicGlobalContinuation
  (normalizedFieldCubicPartFMS
   normalizedFieldCubicPartFMS_coeff)

end Global

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
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
    {F H : ℂ → ℂ} (hF : AnalyticAt ℂ F 0)
    (hH : AnalyticAt ℂ H 0) (n : ℕ) :
    Transfer.taylorCoefficient (fun w ↦ F w + H w) n =
      Transfer.taylorCoefficient F n +
        Transfer.taylorCoefficient H n := by
  simp only [Transfer.taylorCoefficient,
    iteratedDeriv_fun_add hF.contDiffAt hH.contDiffAt, add_div]

private theorem taylorCoefficient_const_of_pos
    (c : ℂ) {n : ℕ} (hn : 0 < n) :
    Transfer.taylorCoefficient (fun _ : ℂ ↦ c) n = 0 := by
  simp only [Transfer.taylorCoefficient, iteratedDeriv_const,
    if_neg hn.ne', zero_div]

private theorem taylorCoefficient_finset_sum
    {I : Type*} [DecidableEq I] (s : Finset I)
    (F : I → ℂ → ℂ)
    (hF : ∀ i ∈ s, AnalyticAt ℂ (F i) 0) (n : ℕ) :
    Transfer.taylorCoefficient (fun w ↦ ∑ i ∈ s, F i w) n =
      ∑ i ∈ s, Transfer.taylorCoefficient (F i) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Transfer.taylorCoefficient]
  | @insert i s hi ih =>
      have hiA : AnalyticAt ℂ (F i) 0 :=
        hF i (Finset.mem_insert_self i s)
      have hsA : AnalyticAt ℂ (fun w ↦ ∑ j ∈ s, F j w) 0 := by
        have hsum : AnalyticAt ℂ (∑ j ∈ s, F j) 0 := by
          apply Finset.analyticAt_sum
          intro j hj
          exact hF j (Finset.mem_insert_of_mem hj)
        have hfun : (∑ j ∈ s, F j) =
            (fun w ↦ ∑ j ∈ s, F j w) := by
          funext w
          exact Finset.sum_apply w s F
        rw [← hfun]
        exact hsum
      simp only [Finset.sum_insert hi]
      rw [taylorCoefficient_add hiA hsA n,
        ih (fun j hj ↦ hF j (Finset.mem_insert_of_mem hj))]

private theorem taylorCoefficient_sqrt_inv_pow_mul
    (c : ℂ) (m n : ℕ) :
    Transfer.taylorCoefficient
        (fun w : ℂ ↦
          (Transfer.cartesianDeltaSqrt w ^ m)⁻¹ * c) n =
      c * (Transfer.coefficient (((m : ℝ) / 2 : ℝ)) n : ℂ) := by
  have hfun :
      (fun w : ℂ ↦ (Transfer.cartesianDeltaSqrt w ^ m)⁻¹ * c) =
        (fun w : ℂ ↦ c * (1 - w) ^
          (-(((((m : ℝ) / 2 : ℝ)) : ℂ)))) := by
    funext w
    rw [Transfer.cartesianDeltaSqrt_inv_pow_eq_neg_cpow]
    ring
  rw [hfun, taylorCoefficient_const_mul,
    Transfer.taylorCoefficient_pure]

omit [Fintype S] [DecidableEq S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
private theorem taylorCoefficient_puiseuxPolynomial
    (ell : ℕ) (a : ℕ → C(S, ℂ) → ℂ)
    (g : C(S, ℂ)) (n : ℕ) :
    Transfer.taylorCoefficient
        (fun w : ℂ ↦
          Data.positiveSurplusCubicPuiseuxPolynomial ell a (w, g)) n =
      ∑ j ∈ Finset.range (3 * ell),
        a j g *
          (Transfer.coefficient
            (((3 * ell - j : ℕ) : ℝ) / 2) n : ℂ) := by
  unfold Data.positiveSurplusCubicPuiseuxPolynomial
  rw [taylorCoefficient_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact taylorCoefficient_sqrt_inv_pow_mul (a j g)
      (3 * ell - j) n
  · intro j hj
    have hpure : AnalyticAt ℂ
        (fun w : ℂ ↦ (1 - w) ^
          (-(((((3 * ell - j : ℕ) : ℝ) / 2 : ℝ)) : ℂ))) 0 :=
      (Transfer.powerSeries_neg_cpow
        (((3 * ell - j : ℕ) : ℝ) / 2)).hasFPowerSeriesAt.analyticAt
    have hterm : AnalyticAt ℂ
        (fun w : ℂ ↦ a j g * (1 - w) ^
          (-(((((3 * ell - j : ℕ) : ℝ) / 2 : ℝ)) : ℂ))) 0 :=
      analyticAt_const.mul hpure
    exact hterm.congr
      (Filter.EventuallyEq.symm (Filter.Eventually.of_forall fun w ↦ by
        change (Transfer.cartesianDeltaSqrt w ^ (3 * ell - j))⁻¹ *
          a j g = a j g * (1 - w) ^
            (-(((((3 * ell - j : ℕ) : ℝ) / 2 : ℝ)) : ℂ))
        rw [Transfer.cartesianDeltaSqrt_inv_pow_eq_neg_cpow]
        ring))

/-- Before normalization by the leading coefficient, the actual cubic-part
FMS coefficient is the complete finite half-step sum plus a uniform
`O(k^(-3/2))` remainder. -/
theorem exists_normalizedFieldCubicPart_coefficient_halfStep_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ (a : ℕ → C(S, ℂ) → ℂ) (s K : ℝ) (N : ℕ),
      0 < s ∧ 0 < K ∧
      (∀ j < 3 * ell + 1,
        AnalyticOnNhd ℂ (a j) (Metric.ball (0 : C(S, ℂ)) s)) ∧
      a 0 0 = positiveSurplusCubicEGFConstant ell *
        (Real.sqrt (M.beta hM) : ℂ) ^ ell ∧
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        ∀ n : ℕ, N ≤ n →
          ‖(Global.normalizedFieldCubicPartFMS M hM g ell).coeff n -
              ∑ j ∈ Finset.range (3 * ell),
                a j g *
                  (Transfer.coefficient
                    (((3 * ell - j : ℕ) : ℝ) / 2) n : ℂ)‖ ≤
            K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨a, G, R, eta, m, s, B,
      heta, hm, hm43, hs, hB, ha, haZero, hG, hR,
      hFormula, hRbound, hTaylor⟩ :=
    Data.exists_normalizedFieldCubicPart_cartesianDelta_transfer_data
      M hM hell
  let 𝒢 := ↥(Metric.ball (0 : C(S, ℂ)) s)
  let Rslice : 𝒢 → ℂ → ℂ := fun g w ↦ R (w, (g : C(S, ℂ)))
  let Q : 𝒢 → ℂ → ℂ := fun g w ↦ ((B : ℂ)⁻¹) * Rslice g w
  have hQdiff : ∀ g : 𝒢,
      DifferentiableOn ℂ (Q g) (Transfer.cartesianDelta eta m) := by
    intro g w hw
    have hRs : AnalyticAt ℂ (Rslice g) w :=
      (hR (w, (g : C(S, ℂ))) ⟨hw, g.property⟩).comp_of_eq
        (analyticAt_id.prod analyticAt_const) rfl
    exact (analyticAt_const.mul hRs).differentiableAt.differentiableWithinAt
  have hQpower : ∀ g : 𝒢, ∀ w ∈ Transfer.cartesianDelta eta m,
      ‖Q g w‖ ≤ ‖w - 1‖ ^ (1 / 2 : ℝ) := by
    intro g w hw
    have hBnorm : ‖((B : ℂ)⁻¹)‖ = B⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    calc
      ‖Q g w‖ = B⁻¹ * ‖R (w, (g : C(S, ℂ)))‖ := by
        dsimp only [Q, Rslice]
        rw [norm_mul, hBnorm]
      _ ≤ B⁻¹ * (B * ‖w - 1‖ ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (hRbound (w, (g : C(S, ℂ))) ⟨hw, g.property⟩)
          (inv_nonneg.mpr hB.le)
      _ = ‖w - 1‖ ^ (1 / 2 : ℝ) := by
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
      (a := (1 / 2 : ℝ)) hMcontour hMcontourOne hMcontourEta
      hm.le hm43 (by norm_num) hQdiff hQpower
  obtain ⟨NQ, hNQ⟩ := Filter.eventually_atTop.1 hQcoeff
  let K : ℝ := B * KQ
  let N : ℕ := max NQ 1
  have hK : 0 < K := mul_pos hB hKQ
  refine ⟨a, s, K, N, hs, hK, ha, haZero, ?_⟩
  intro g hg n hn
  have hnQ : NQ ≤ n := (le_max_left NQ 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right NQ 1).trans hn
  have hn0 : 0 < n := Nat.zero_lt_one.trans_le hn1
  let gi : 𝒢 := ⟨g, hg⟩
  have hQn : ‖Transfer.banachTaylorCoefficient (Q gi) n‖ ≤
      KQ * (n : ℝ) ^ (-((1 / 2 : ℝ) + 1)) :=
    hNQ n hnQ gi
  have hQn' : ‖Transfer.banachTaylorCoefficient (Q gi) n‖ ≤
      KQ * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    simpa only [show -((1 / 2 : ℝ) + 1) = -(3 / 2 : ℝ) by
      norm_num] using hQn
  let Rg : ℂ → ℂ := fun w ↦ R (w, g)
  have hCoeffScale :
      Transfer.banachTaylorCoefficient Rg n =
        (B : ℂ) * Transfer.banachTaylorCoefficient (Q gi) n := by
    simp only [Transfer.banachTaylorCoefficient, Q, Rslice, Rg, gi,
      iteratedDeriv_const_mul_field, smul_eq_mul]
    field_simp [hB.ne']
  have hRcoeffBound :
      ‖Transfer.taylorCoefficient Rg n‖ ≤
        K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [taylorCoefficient_eq_banachTaylorCoefficient, hCoeffScale,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    calc
      B * ‖Transfer.banachTaylorCoefficient (Q gi) n‖ ≤
          B * (KQ * (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hQn' hB.le
      _ = K * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
        dsimp only [K]
        ring
  have hzeroDelta : (0 : ℂ) ∈ Transfer.cartesianDelta eta m :=
    Transfer.unit_ball_subset_cartesianDelta heta
      (by simpa only [Metric.mem_ball, dist_zero_right, norm_zero] using
        (zero_lt_one : (0 : ℝ) < 1))
  have hG0 : AnalyticAt ℂ (fun w : ℂ ↦ G (w, g)) 0 :=
    (hG (0, g) ⟨hzeroDelta, hg⟩).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  have hR0 : AnalyticAt ℂ Rg 0 :=
    (hR (0, g) ⟨hzeroDelta, hg⟩).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  let Pg : ℂ → ℂ := fun w ↦
    Data.positiveSurplusCubicPuiseuxPolynomial ell a (w, g)
  have hP0 : AnalyticAt ℂ Pg 0 := by
    have hfun : Pg = (fun w : ℂ ↦
        G (w, g) - (fun _ : ℂ ↦ a (3 * ell) g) w - Rg w) := by
      funext w
      rw [hFormula (w, g)]
      dsimp only [Pg, Rg]
      ring
    rw [hfun]
    exact (hG0.sub analyticAt_const).sub hR0
  have hPcoeff : Transfer.taylorCoefficient Pg n =
      ∑ j ∈ Finset.range (3 * ell),
        a j g *
          (Transfer.coefficient
            (((3 * ell - j : ℕ) : ℝ) / 2) n : ℂ) := by
    exact taylorCoefficient_puiseuxPolynomial ell a g n
  have hConstCoeff : Transfer.taylorCoefficient
      (fun _ : ℂ ↦ a (3 * ell) g) n = 0 :=
    taylorCoefficient_const_of_pos _ hn0
  have hSingularCoeff : Transfer.taylorCoefficient
      (fun w : ℂ ↦ Pg w + a (3 * ell) g) n =
        ∑ j ∈ Finset.range (3 * ell),
          a j g *
            (Transfer.coefficient
              (((3 * ell - j : ℕ) : ℝ) / 2) n : ℂ) := by
    rw [taylorCoefficient_add hP0 analyticAt_const n,
      hPcoeff, hConstCoeff, add_zero]
  have hCoeffGenuine :
      Transfer.taylorCoefficient (fun w : ℂ ↦ G (w, g)) n =
        (Global.normalizedFieldCubicPartFMS M hM g ell).coeff n :=
    taylorCoefficient_eq_fms_coeff (hTaylor g hg) n
  have hRcoeffFormula : Transfer.taylorCoefficient Rg n =
      (Global.normalizedFieldCubicPartFMS M hM g ell).coeff n -
        ∑ j ∈ Finset.range (3 * ell),
          a j g *
            (Transfer.coefficient
              (((3 * ell - j : ℕ) : ℝ) / 2) n : ℂ) := by
    have hsub := Transfer.taylorCoefficient_sub
      (F := fun w : ℂ ↦ G (w, g))
      (G := fun w : ℂ ↦ Pg w + a (3 * ell) g)
      hG0 (hP0.add analyticAt_const) n
    have hfun : (fun w : ℂ ↦
        G (w, g) - (Pg w + a (3 * ell) g)) = Rg := by
      funext w
      rw [hFormula (w, g)]
      dsimp only [Pg, Rg]
      ring
    rw [hfun, hSingularCoeff, hCoeffGenuine] at hsub
    exact hsub
  rw [← hRcoeffFormula]
  exact hRcoeffBound

/-- The exact cubic leading coefficient never vanishes at positive
surplus. -/
theorem positiveSurplusCubicExactPurePowerCoefficient_ne_zero
    (ell k : ℕ) (hell : 0 < ell) :
    positiveSurplusCubicExactPurePowerCoefficient ell k ≠ 0 := by
  apply mul_ne_zero (positiveSurplusCubicEGFConstant_ne_zero ell hell)
  exact Complex.ofReal_ne_zero.mpr
    (Transfer.coefficient_pos
      (positiveSurplusCubicExponent ell) (by
        unfold positiveSurplusCubicExponent
        positivity) k).ne'

private theorem one_le_coefficient_of_one_le
    (s : ℝ) (hs : 1 ≤ s) (n : ℕ) :
    1 ≤ Transfer.coefficient s n := by
  have hfactorial :
      (∏ j ∈ Finset.range n, ((1 : ℝ) + j)) = (n.factorial : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
        push_cast
        ring
  have hprod :
      (∏ j ∈ Finset.range n, ((1 : ℝ) + j)) ≤
        ∏ j ∈ Finset.range n, (s + j) := by
    apply Finset.prod_le_prod
    · intro j hj
      positivity
    · intro j hj
      linarith
  have hfactPos : (0 : ℝ) < n.factorial := by positivity
  unfold Transfer.coefficient
  exact (le_div_iff₀ hfactPos).2 (by
    rw [← hfactorial]
    simpa using hprod)

private theorem rpow_neg_nat_half_isBigO_neg_half
    {j : ℕ} (hj : 1 ≤ j) :
    (fun n : ℕ ↦ (n : ℝ) ^ (-((j : ℝ) / 2))) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hjreal : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _), one_mul]
  apply Real.rpow_le_rpow_of_exponent_le hnreal
  nlinarith [hjreal]

/-- Local field-uniform relative estimate.  The denominator is the exact
coefficient of the leading cubic pure power; the model-dependent value at
zero field is precisely `(sqrt beta)^ell`. -/
theorem exists_normalizedFieldCubicPart_coefficient_local_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ epsilon K : ℝ, 0 < epsilon ∧ 0 < K ∧
      ∀ᶠ n : ℕ in atTop, ∀ g : C(S, ℂ),
        ‖g‖ ≤ epsilon →
        ‖(Global.normalizedFieldCubicPartFMS M hM g ell).coeff n /
              positiveSurplusCubicExactPurePowerCoefficient ell n -
            (Real.sqrt (M.beta hM) : ℂ) ^ ell‖ ≤
          K * (‖g‖ + (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨a, s, Krem, Nrem, hs, hKrem, ha, haZero, hcoeff⟩ :=
    exists_normalizedFieldCubicPart_coefficient_halfStep_bound
      M hM hell
  have hzero : (0 : C(S, ℂ)) ∈ Metric.ball 0 s := by
    simpa only [Metric.mem_ball, dist_self] using hs
  have ha0at : AnalyticAt ℂ (a 0) 0 :=
    ha 0 (by omega) 0 hzero
  have ha0O : (fun g : C(S, ℂ) ↦ a 0 g - a 0 0) =O[𝓝 0]
      (fun g : C(S, ℂ) ↦ g) := by
    simpa only [sub_zero] using ha0at.differentiableAt.isBigO_sub
  obtain ⟨L₀, hL₀⟩ := isBigO_iff.mp ha0O
  let L : ℝ := max L₀ 1
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right L₀ 1)
  have hLipEventually : ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      ‖a 0 g - a 0 0‖ ≤ L * ‖g‖ := by
    filter_upwards [hL₀] with g hg
    exact hg.trans
      (mul_le_mul_of_nonneg_right (le_max_left L₀ 1) (norm_nonneg g))
  obtain ⟨sLip, hsLip, hLipBall⟩ :=
    Metric.eventually_nhds_iff.mp hLipEventually

  let p : ℕ := 3 * ell
  have hp : 0 < p := by dsimp only [p]; omega
  have haBoundEventually : ∀ᶠ g : C(S, ℂ) in 𝓝 0,
      ∀ j : Fin p, ‖a j g‖ ≤ ‖a j 0‖ + 1 := by
    rw [Filter.eventually_all]
    intro j
    have hjlt : (j : ℕ) < 3 * ell := by
      simpa only [p] using j.2
    have haj : AnalyticAt ℂ (a j) 0 :=
      ha j (by omega) 0 hzero
    have hclose : ∀ᶠ g : C(S, ℂ) in 𝓝 0,
        a j g ∈ Metric.ball (a j 0) 1 :=
      haj.continuousAt (Metric.ball_mem_nhds (a j 0) zero_lt_one)
    filter_upwards [hclose] with g hg
    have htri : ‖a j g‖ ≤ ‖a j g - a j 0‖ + ‖a j 0‖ := by
      have := norm_add_le (a j g - a j 0) (a j 0)
      simpa only [sub_add_cancel] using this
    have hdist : ‖a j g - a j 0‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hg
    calc
      ‖a j g‖ ≤ ‖a j g - a j 0‖ + ‖a j 0‖ := htri
      _ ≤ ‖a j 0‖ + 1 := by linarith
  obtain ⟨sBound, hsBound, haBoundBall⟩ :=
    Metric.eventually_nhds_iff.mp haBoundEventually

  let J : Finset ℕ := (Finset.range p).erase 0
  have hLowerO :
      (fun n : ℕ ↦ ∑ j ∈ J,
        (‖a j 0‖ + 1) *
          |Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
            Transfer.coefficient (((p : ℕ) : ℝ) / 2) n|) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
    have hsum :
        (∑ j ∈ J, fun n : ℕ ↦
          (‖a j 0‖ + 1) *
            |Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
              Transfer.coefficient (((p : ℕ) : ℝ) / 2) n|) =O[atTop]
          (fun n : ℕ ↦ (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
      apply IsBigO.sum (s := J)
      intro j hj
      have hjRange : j ∈ Finset.range p := (Finset.mem_erase.mp hj).2
      have hjlt : j < 3 * ell := by
        simpa only [p] using Finset.mem_range.mp hjRange
      have hjpos : 1 ≤ j :=
        Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase hj)
      have hratio := Transfer.coefficient_halfStep_ratio_isBigO
        ell j hell hjlt
      have hratioAbs :
          (fun n : ℕ ↦
            |Transfer.coefficient (((3 * ell - j : ℕ) : ℝ) / 2) n /
              Transfer.coefficient (((3 * ell : ℕ) : ℝ) / 2) n|) =O[atTop]
            (fun n : ℕ ↦ (n : ℝ) ^ (-((j : ℝ) / 2))) := by
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using
            hratio.norm_norm
      have hhalf := hratioAbs.trans
        (rpow_neg_nat_half_isBigO_neg_half hjpos)
      simpa only [p] using
        hhalf.const_mul_left (‖a j 0‖ + 1)
    have hfun :
        (∑ j ∈ J, fun n : ℕ ↦
          (‖a j 0‖ + 1) *
            |Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
              Transfer.coefficient (((p : ℕ) : ℝ) / 2) n|) =
          (fun n : ℕ ↦ ∑ j ∈ J,
            (‖a j 0‖ + 1) *
              |Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
                Transfer.coefficient (((p : ℕ) : ℝ) / 2) n|) := by
      funext n
      exact Finset.sum_apply n J _
    rw [← hfun]
    exact hsum
  rw [isBigO_iff] at hLowerO
  obtain ⟨Clower₀, hClower₀⟩ := hLowerO
  let Clower : ℝ := max Clower₀ 1
  have hClower : 0 < Clower :=
    lt_of_lt_of_le zero_lt_one (le_max_right Clower₀ 1)
  have hLowerEventually : ∀ᶠ n : ℕ in atTop,
      (∑ j ∈ J, (‖a j 0‖ + 1) *
        |Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
          Transfer.coefficient (((p : ℕ) : ℝ) / 2) n|) ≤
        Clower * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [hClower₀] with n hn
    have hsumNonneg : 0 ≤ ∑ j ∈ J, (‖a j 0‖ + 1) *
        |Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
          Transfer.coefficient (((p : ℕ) : ℝ) / 2) n| :=
      Finset.sum_nonneg fun j _ ↦ mul_nonneg (by positivity) (abs_nonneg _)
    have hn' : (∑ j ∈ J, (‖a j 0‖ + 1) *
        |Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
          Transfer.coefficient (((p : ℕ) : ℝ) / 2) n|) ≤
        Clower₀ * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hsumNonneg,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hn
    exact hn'.trans (mul_le_mul_of_nonneg_right
      (le_max_left Clower₀ 1)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

  let c : ℂ := positiveSurplusCubicEGFConstant ell
  have hc : c ≠ 0 := positiveSurplusCubicEGFConstant_ne_zero ell hell
  have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  let Camp : ℝ := L / ‖c‖
  let Clow : ℝ := Clower / ‖c‖
  let Crem : ℝ := Krem / ‖c‖
  let K : ℝ := Camp + Clow + Crem + 1
  have hCamp : 0 < Camp := div_pos hL hcnorm
  have hClow : 0 < Clow := div_pos hClower hcnorm
  have hCrem : 0 < Crem := div_pos hKrem hcnorm
  have hK : 0 < K := by dsimp only [K]; positivity
  let radius : ℝ := min s (min sLip sBound)
  have hradius : 0 < radius := lt_min hs (lt_min hsLip hsBound)
  let epsilon : ℝ := radius / 2
  have hepsilon : 0 < epsilon := half_pos hradius
  refine ⟨epsilon, K, hepsilon, hK, ?_⟩
  filter_upwards [eventually_ge_atTop (max Nrem 1), hLowerEventually]
    with n hn hLower
  intro g hg
  have hnRem : Nrem ≤ n := (le_max_left Nrem 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right Nrem 1).trans hn
  have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn1
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hepsRadius : epsilon < radius := by
    dsimp only [epsilon]
    linarith
  have hgr : ‖g‖ < radius := hg.trans_lt hepsRadius
  have hgs : g ∈ Metric.ball (0 : C(S, ℂ)) s := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hgr.trans_le (min_le_left s (min sLip sBound))
  have hgsLip : g ∈ Metric.ball (0 : C(S, ℂ)) sLip := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hgr.trans_le ((min_le_right s _).trans (min_le_left sLip sBound))
  have hgsBound : g ∈ Metric.ball (0 : C(S, ℂ)) sBound := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hgr.trans_le ((min_le_right s _).trans (min_le_right sLip sBound))
  have hAmp : ‖a 0 g - a 0 0‖ ≤ L * ‖g‖ := hLipBall hgsLip
  have hCoeff := hcoeff g hgs n hnRem
  let s₀ : ℝ := ((p : ℕ) : ℝ) / 2
  have hs₀ : 0 < s₀ := by dsimp only [s₀, p]; positivity
  have hs₀one : 1 ≤ s₀ := by
    have hellOne : (1 : ℕ) ≤ ell := Nat.one_le_iff_ne_zero.mpr hell.ne'
    have hellReal : (1 : ℝ) ≤ ell := by exact_mod_cast hellOne
    dsimp only [s₀, p]
    push_cast
    nlinarith
  let c₀ : ℝ := Transfer.coefficient s₀ n
  have hc₀pos : 0 < c₀ := Transfer.coefficient_pos s₀ hs₀ n
  have hc₀one : 1 ≤ c₀ := one_le_coefficient_of_one_le s₀ hs₀one n
  let E : ℂ := (Global.normalizedFieldCubicPartFMS M hM g ell).coeff n -
    ∑ j ∈ Finset.range p,
      a j g *
        (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ)
  have hE : ‖E‖ ≤ Krem * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    simpa only [E, p] using hCoeff
  have h0mem : 0 ∈ Finset.range p := Finset.mem_range.mpr hp
  have hSumSplit :
      (∑ j ∈ Finset.range p,
        a j g *
          (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ)) =
        a 0 g * (c₀ : ℂ) +
          ∑ j ∈ J,
            a j g *
              (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ) := by
    have h := Finset.sum_erase_add
      (s := Finset.range p)
      (f := fun j ↦ a j g *
        (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ))
      h0mem
    calc
      (∑ j ∈ Finset.range p, a j g *
          (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ)) =
          (∑ j ∈ J, a j g *
            (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ)) +
              a 0 g * (c₀ : ℂ) := by
        simpa only [J, Nat.sub_zero, s₀, c₀] using h.symm
      _ = a 0 g * (c₀ : ℂ) +
          ∑ j ∈ J, a j g *
            (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ) :=
        add_comm _ _
  have hLowerComplex :
      ‖∑ j ∈ J,
          a j g *
            ((Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
              c₀ : ℝ) : ℂ)‖ ≤
        Clower * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖∑ j ∈ J, a j g *
          ((Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
            c₀ : ℝ) : ℂ)‖ ≤
          ∑ j ∈ J, ‖a j g *
            ((Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
              c₀ : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ J, (‖a j 0‖ + 1) *
          |Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n / c₀| := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          (haBoundBall hgsBound ⟨j,
            Finset.mem_range.mp (Finset.mem_erase.mp hj).2⟩)
          (abs_nonneg _)
      _ ≤ Clower * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        simpa only [s₀, c₀] using hLower
  have hLeadBound : ‖(a 0 g - a 0 0) / c‖ ≤ Camp * ‖g‖ := by
    rw [norm_div]
    calc
      ‖a 0 g - a 0 0‖ / ‖c‖ ≤ (L * ‖g‖) / ‖c‖ :=
        div_le_div_of_nonneg_right hAmp hcnorm.le
      _ = Camp * ‖g‖ := by dsimp only [Camp]; ring
  have hLowerBound :
      ‖(∑ j ∈ J,
          a j g *
            (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ)) /
          (c * (c₀ : ℂ))‖ ≤
        Clow * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hsumdiv :
        (∑ j ∈ J, a j g *
          ((Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
            c₀ : ℝ) : ℂ)) =
          (∑ j ∈ J, a j g *
            (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ)) /
              (c₀ : ℂ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      rw [mul_div_assoc]
    have hrewrite :
        (∑ j ∈ J, a j g *
          (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ)) /
            (c * (c₀ : ℂ)) =
          c⁻¹ * ∑ j ∈ J, a j g *
            ((Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
              c₀ : ℝ) : ℂ) := by
      rw [hsumdiv]
      field_simp [hc, hc₀pos.ne']
    rw [hrewrite, norm_mul, norm_inv]
    calc
      ‖c‖⁻¹ * ‖∑ j ∈ J, a j g *
          ((Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n /
            c₀ : ℝ) : ℂ)‖ ≤
          ‖c‖⁻¹ *
            (Clower * (n : ℝ) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hLowerComplex (inv_nonneg.mpr (norm_nonneg c))
      _ = Clow * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        dsimp only [Clow]
        field_simp [hcnorm.ne']
  have hRemBound : ‖E / (c * (c₀ : ℂ))‖ ≤
      Crem * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hc₀pos]
    have hden : 0 < ‖c‖ * c₀ := mul_pos hcnorm hc₀pos
    calc
      ‖E‖ / (‖c‖ * c₀) ≤
          (Krem * (n : ℝ) ^ (-(3 / 2 : ℝ))) /
            (‖c‖ * c₀) := div_le_div_of_nonneg_right hE hden.le
      _ ≤ (Krem / ‖c‖) * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
        have hc₀inv : c₀⁻¹ ≤ 1 := (inv_le_one₀ hc₀pos).mpr hc₀one
        calc
          (Krem * (n : ℝ) ^ (-(3 / 2 : ℝ))) /
                (‖c‖ * c₀) =
              ((Krem / ‖c‖) *
                (n : ℝ) ^ (-(3 / 2 : ℝ))) * c₀⁻¹ := by
            rw [div_eq_mul_inv, mul_inv_rev, div_eq_mul_inv]
            ring
          _ ≤ ((Krem / ‖c‖) *
                (n : ℝ) ^ (-(3 / 2 : ℝ))) * 1 := by
            apply mul_le_mul_of_nonneg_left hc₀inv
            exact mul_nonneg (div_nonneg hKrem.le hcnorm.le)
              (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          _ = (Krem / ‖c‖) *
                (n : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ Crem * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        dsimp only [Crem]
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hKrem.le hcnorm.le)
        exact Real.rpow_le_rpow_of_exponent_le hnreal (by norm_num)
  have hExact : positiveSurplusCubicExactPurePowerCoefficient ell n =
      c * (c₀ : ℂ) := by
    unfold positiveSurplusCubicExactPurePowerCoefficient
      positiveSurplusCubicExponent
    dsimp only [c, c₀, s₀, p]
    congr 2
    push_cast
    ring
  have hRatio :
      (Global.normalizedFieldCubicPartFMS M hM g ell).coeff n /
            positiveSurplusCubicExactPurePowerCoefficient ell n -
          (Real.sqrt (M.beta hM) : ℂ) ^ ell =
        (a 0 g - a 0 0) / c +
          (∑ j ∈ J, a j g *
            (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ)) /
              (c * (c₀ : ℂ)) +
          E / (c * (c₀ : ℂ)) := by
    rw [hExact]
    have hEeq : (Global.normalizedFieldCubicPartFMS M hM g ell).coeff n =
        (∑ j ∈ Finset.range p, a j g *
          (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ)) + E := by
      dsimp only [E]
      ring
    rw [hEeq, hSumSplit, haZero]
    field_simp [hc, hc₀pos.ne']
    ring
  rw [hRatio]
  calc
    ‖(a 0 g - a 0 0) / c +
        (∑ j ∈ J, a j g *
          (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ)) /
            (c * (c₀ : ℂ)) + E / (c * (c₀ : ℂ))‖ ≤
        ‖(a 0 g - a 0 0) / c‖ +
          ‖(∑ j ∈ J, a j g *
            (Transfer.coefficient (((p - j : ℕ) : ℝ) / 2) n : ℂ)) /
              (c * (c₀ : ℂ))‖ +
          ‖E / (c * (c₀ : ℂ))‖ := by
      exact norm_add₃_le
    _ ≤ Camp * ‖g‖ +
          Clow * (n : ℝ) ^ (-(1 / 2 : ℝ)) +
          Crem * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      exact add_le_add (add_le_add hLeadBound hLowerBound) hRemBound
    _ ≤ K * (‖g‖ + (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
      have hg0 : 0 ≤ ‖g‖ := norm_nonneg g
      have hn0 : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg (Nat.cast_nonneg n) _
      dsimp only [K]
      nlinarith [hCamp.le, hClow.le, hCrem.le]

end PerronWright.FiniteIrreducibleCubicCoefficientAsymptotic
