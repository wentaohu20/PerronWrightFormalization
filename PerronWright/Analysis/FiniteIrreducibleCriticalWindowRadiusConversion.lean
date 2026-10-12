import PerronWright.Analysis.FiniteIrreducibleScalarLogRadiusTaylor

/-!
# Critical-window conversion for the literal finite scalar radius

The analytic calculation gives a cubic Taylor remainder for `log rho(t)`.
This file converts that local statement into the multiplicative estimate used
in the Perron--Wright window `|t - 1| = O(k^(-1/2))`.
-/

open Filter Asymptotics MeasureTheory
open scoped Topology Real

noncomputable section

namespace PerronWright.FiniteIrreducibleCriticalWindowRadiusConversion

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- The real critical radius on the physical scalar slice.  It is positive
in a neighborhood of `t = 1`. -/
def realScalarRadius (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (t : ℝ) : ℝ :=
  (FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).re

/-- The Gaussian rate in the critical window. -/
def criticalQuadraticRate (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) : ℝ :=
  M.alpha hM ^ 2 / (2 * M.beta hM)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem criticalQuadraticRate_pos (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    0 < criticalQuadraticRate M hM := by
  unfold criticalQuadraticRate
  exact div_pos (sq_pos_of_pos (M.alpha_pos hM))
    (mul_pos (by norm_num) (M.beta_pos hM))

theorem realScalarRadius_pos_eventually (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ t : ℝ in 𝓝 1, 0 < realScalarRadius M hM t := by
  filter_upwards [
    FiniteIrreducibleScalarFieldResponse.scalarRadius_real_positive_near_one M hM]
    with t ht
  exact ht.2

/-- The complex cubic Taylor estimate and the physical real branch give the
corresponding real logarithmic estimate. -/
theorem real_logScalarRadius_cubic_remainder
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    (fun t : ℝ ↦
      Real.log (realScalarRadius M hM t) -
        criticalQuadraticRate M hM * (t - 1) ^ 2)
      =O[𝓝 (1 : ℝ)] (fun t : ℝ ↦ |t - 1| ^ 3) := by
  obtain ⟨C, hC⟩ := isBigO_iff.mp
    (FiniteIrreducibleScalarLogRadiusTaylor.logScalarRadius_cubic_remainder M hM)
  apply isBigO_iff.mpr
  refine ⟨max C 0, ?_⟩
  have hshift : Tendsto (fun t : ℝ ↦ ((t - 1 : ℝ) : ℂ))
      (𝓝 (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    have hcont : ContinuousAt (fun t : ℝ ↦ ((t - 1 : ℝ) : ℂ)) 1 :=
      Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_id.sub continuousAt_const)
    simpa only [sub_self, Complex.ofReal_zero] using hcont.tendsto
  have hbound := hshift.eventually hC
  filter_upwards [hbound,
    FiniteIrreducibleScalarLogRadiusTaylor.logScalarRadius_real_branch M hM]
    with t ht hbranch
  have hone : (1 : ℂ) + ((t - 1 : ℝ) : ℂ) = (t : ℂ) := by
    push_cast
    ring
  have hcoef :
      (M.alpha hM : ℂ) ^ 2 / (2 * (M.beta hM : ℂ)) =
        (criticalQuadraticRate M hM : ℂ) := by
    unfold criticalQuadraticRate
    push_cast
    ring
  have heq :
      FiniteIrreducibleScalarLogRadiusTaylor.logScalarRadius M hM
          (1 + ((t - 1 : ℝ) : ℂ)) -
          ((M.alpha hM : ℂ) ^ 2 / (2 * (M.beta hM : ℂ))) *
            ((t - 1 : ℝ) : ℂ) ^ 2 =
        ((Real.log (realScalarRadius M hM t) -
          criticalQuadraticRate M hM * (t - 1) ^ 2 : ℝ) : ℂ) := by
    rw [hone, hbranch, hcoef]
    simp only [realScalarRadius, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_pow]
  rw [heq] at ht
  calc
    ‖Real.log (realScalarRadius M hM t) -
        criticalQuadraticRate M hM * (t - 1) ^ 2‖ ≤
        C * ‖‖((t - 1 : ℝ) : ℂ)‖ ^ 3‖ := by
      simpa only [Complex.norm_real] using ht
    _ ≤ max C 0 * ‖|t - 1| ^ 3‖ := by
      have hpow : 0 ≤ |t - 1| ^ 3 := by positivity
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_abs,
        abs_of_nonneg hpow] using
          mul_le_mul_of_nonneg_right (le_max_left C 0) hpow

/-- An explicit local form of the real logarithmic remainder, bundled with
the positivity needed to exponentiate it. -/
theorem exists_real_logScalarRadius_cubic_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ t : ℝ, |t - 1| < δ →
        0 < realScalarRadius M hM t ∧
        |Real.log (realScalarRadius M hM t) -
            criticalQuadraticRate M hM * (t - 1) ^ 2| ≤
          C * |t - 1| ^ 3 := by
  obtain ⟨C₀, hC₀⟩ := isBigO_iff.mp
    (real_logScalarRadius_cubic_remainder M hM)
  let C : ℝ := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1)
  have hbound : ∀ᶠ t : ℝ in 𝓝 1,
      |Real.log (realScalarRadius M hM t) -
          criticalQuadraticRate M hM * (t - 1) ^ 2| ≤
        C * |t - 1| ^ 3 := by
    filter_upwards [hC₀] with t ht
    have hpow : 0 ≤ |t - 1| ^ 3 := by positivity
    calc
      |Real.log (realScalarRadius M hM t) -
          criticalQuadraticRate M hM * (t - 1) ^ 2| =
          ‖Real.log (realScalarRadius M hM t) -
            criticalQuadraticRate M hM * (t - 1) ^ 2‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ C₀ * ‖|t - 1| ^ 3‖ := ht
      _ ≤ C * |t - 1| ^ 3 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hpow]
        exact mul_le_mul_of_nonneg_right (le_max_left C₀ 1) hpow
  have hlocal := hbound.and (realScalarRadius_pos_eventually M hM)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro t ht
  have htball : t ∈ Metric.ball (1 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq] using ht
  exact (hball htball).symm

/-- Multiplicative critical-window conversion.  The condition
`sqrt(k) * |t - 1| ≤ L` is the division-free form of
`|t - 1| ≤ L k^(-1/2)` for positive `k`. -/
theorem exists_criticalWindowRadius_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ,
        Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        |(realScalarRadius M hM t)⁻¹ ^ k /
              Real.exp (-criticalQuadraticRate M hM * (k : ℝ) *
                (t - 1) ^ 2) - 1| ≤
          A / Real.sqrt (k : ℝ) := by
  obtain ⟨δ, C, hδ, hC, hlocal⟩ :=
    exists_real_logScalarRadius_cubic_bound M hM
  let A : ℝ := 2 * C * (L + 1) ^ 3
  have hLp : 0 < L + 1 := by linarith
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  refine ⟨A, hA, ?_⟩
  have hsqrt : Tendsto (fun k : ℕ ↦ Real.sqrt (k : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun k : ℕ ↦ (Real.sqrt (k : ℝ))⁻¹) atTop
      (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp hsqrt
  have hnearLim : Tendsto
      (fun k : ℕ ↦ (L + 1) * (Real.sqrt (k : ℝ))⁻¹) atTop
      (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hinv
  have hsmallLim : Tendsto
      (fun k : ℕ ↦ C * (L + 1) ^ 3 *
        (Real.sqrt (k : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hinv
  have hnear : ∀ᶠ k : ℕ in atTop,
      (L + 1) * (Real.sqrt (k : ℝ))⁻¹ < δ :=
    hnearLim.eventually (isOpen_Iio.mem_nhds hδ)
  have hsmall : ∀ᶠ k : ℕ in atTop,
      C * (L + 1) ^ 3 * (Real.sqrt (k : ℝ))⁻¹ < 1 :=
    hsmallLim.eventually (isOpen_Iio.mem_nhds zero_lt_one)
  filter_upwards [eventually_ge_atTop 1, hnear, hsmall]
    with k hk hknear hksmall
  intro t hwindow
  let s : ℝ := Real.sqrt (k : ℝ)
  let y : ℝ := |t - 1|
  let r : ℝ := Real.log (realScalarRadius M hM t) -
    criticalQuadraticRate M hM * (t - 1) ^ 2
  have hkpos : 0 < k := by omega
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hspos : 0 < s := Real.sqrt_pos.2 hkreal
  have hsy : s * y ≤ L := by simpa only [s, y] using hwindow
  have hy : y ≤ L / s := (le_div_iff₀ hspos).2 (by
    simpa only [mul_comm] using hsy)
  have hylocal : |t - 1| < δ := by
    calc
      |t - 1| = y := rfl
      _ ≤ L / s := hy
      _ ≤ (L + 1) / s :=
        div_le_div_of_nonneg_right (by linarith) hspos.le
      _ = (L + 1) * (Real.sqrt (k : ℝ))⁻¹ := by
        simp only [s, div_eq_mul_inv]
      _ < δ := hknear
  obtain ⟨hρ, hr⟩ := hlocal t hylocal
  have hsquare : s ^ 2 = (k : ℝ) := by
    dsimp only [s]
    exact Real.sq_sqrt hkreal.le
  have hsy' : s * y ≤ L + 1 := hsy.trans (by linarith)
  have hcubePow : (s * y) ^ 3 ≤ (L + 1) ^ 3 :=
    pow_le_pow_left₀ (mul_nonneg hspos.le (abs_nonneg _)) hsy' 3
  have hcube : (k : ℝ) * y ^ 3 ≤ (L + 1) ^ 3 / s := by
    rw [le_div_iff₀ hspos]
    calc
      (k : ℝ) * y ^ 3 * s = (s * y) ^ 3 := by
        rw [← hsquare]
        ring
      _ ≤ (L + 1) ^ 3 := hcubePow
  have hscaled : |-(k : ℝ) * r| ≤
      C * (L + 1) ^ 3 / s := by
    calc
      |-(k : ℝ) * r| = (k : ℝ) * |r| := by
        rw [abs_mul, abs_neg, abs_of_pos hkreal]
      _ ≤ (k : ℝ) * (C * y ^ 3) :=
        mul_le_mul_of_nonneg_left (by simpa only [r, y] using hr) hkreal.le
      _ ≤ C * ((L + 1) ^ 3 / s) := by
        calc
          (k : ℝ) * (C * y ^ 3) = C * ((k : ℝ) * y ^ 3) := by ring
          _ ≤ C * ((L + 1) ^ 3 / s) :=
            mul_le_mul_of_nonneg_left hcube hC.le
      _ = C * (L + 1) ^ 3 / s := by ring
  have hscaledOne : |-(k : ℝ) * r| ≤ 1 :=
    hscaled.trans (le_of_lt (by
      simpa only [s, div_eq_mul_inv, mul_assoc] using hksmall))
  have hexpError : |Real.exp (-(k : ℝ) * r) - 1| ≤ A / s := by
    calc
      |Real.exp (-(k : ℝ) * r) - 1| ≤
          2 * |-(k : ℝ) * r| :=
        Real.abs_exp_sub_one_le hscaledOne
      _ ≤ 2 * (C * (L + 1) ^ 3 / s) :=
        mul_le_mul_of_nonneg_left hscaled (by norm_num)
      _ = A / s := by
        dsimp only [A]
        ring
  have hfactor :
      (realScalarRadius M hM t)⁻¹ ^ k =
        Real.exp (-criticalQuadraticRate M hM * (k : ℝ) *
            (t - 1) ^ 2) * Real.exp (-(k : ℝ) * r) := by
    calc
      (realScalarRadius M hM t)⁻¹ ^ k =
          (Real.exp (-Real.log (realScalarRadius M hM t))) ^ k := by
        rw [Real.exp_neg, Real.exp_log hρ]
      _ = Real.exp ((k : ℝ) *
          (-Real.log (realScalarRadius M hM t))) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp (-criticalQuadraticRate M hM * (k : ℝ) *
            (t - 1) ^ 2) * Real.exp (-(k : ℝ) * r) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [r]
        ring
  have hgauss : 0 < Real.exp
      (-criticalQuadraticRate M hM * (k : ℝ) * (t - 1) ^ 2) :=
    Real.exp_pos _
  rw [hfactor]
  have hquot :
      Real.exp (-criticalQuadraticRate M hM * (k : ℝ) *
          (t - 1) ^ 2) * Real.exp (-(k : ℝ) * r) /
          Real.exp (-criticalQuadraticRate M hM * (k : ℝ) *
            (t - 1) ^ 2) =
        Real.exp (-(k : ℝ) * r) := by
    field_simp [hgauss.ne']
  rw [hquot]
  simpa only [s] using hexpError

/-- Equivalent difference form of the critical-window conversion. -/
theorem exists_criticalWindowRadius_difference_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ,
        Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        |(realScalarRadius M hM t)⁻¹ ^ k -
            Real.exp (-criticalQuadraticRate M hM * (k : ℝ) *
              (t - 1) ^ 2)| ≤
          Real.exp (-criticalQuadraticRate M hM * (k : ℝ) *
              (t - 1) ^ 2) *
            (A / Real.sqrt (k : ℝ)) := by
  obtain ⟨A, hA, hrel⟩ :=
    exists_criticalWindowRadius_relative_bound M hM L hL
  refine ⟨A, hA, ?_⟩
  filter_upwards [hrel] with k hk
  intro t ht
  have h := hk t ht
  let G : ℝ := Real.exp (-criticalQuadraticRate M hM * (k : ℝ) *
    (t - 1) ^ 2)
  have hG : 0 < G := Real.exp_pos _
  have hid :
      |(realScalarRadius M hM t)⁻¹ ^ k - G| =
        G * |(realScalarRadius M hM t)⁻¹ ^ k / G - 1| := by
    have halg :
        (realScalarRadius M hM t)⁻¹ ^ k - G =
          G * ((realScalarRadius M hM t)⁻¹ ^ k / G - 1) := by
      field_simp [hG.ne']
    rw [halg, abs_mul, abs_of_pos hG]
  rw [show Real.exp (-criticalQuadraticRate M hM * (k : ℝ) *
      (t - 1) ^ 2) = G by rfl, hid]
  exact mul_le_mul_of_nonneg_left h hG.le

end PerronWright.FiniteIrreducibleCriticalWindowRadiusConversion
