import PerronWright.Enumeration.PositiveSurplusNoncubicFieldWeightAsymptotic
import PerronWright.Enumeration.PositiveSurplusCubicPerronWrightFormula

/-!
# Scalar shrinking-window bound for the noncubic positive-surplus part

The scalar noncubic contribution is compared directly with the cubic
Perron--Wright radius main term.  Its extra fold-coordinate factor gives a
half-step loss, uniformly on every shrinking scalar window.  No noncubic
term is used as a denominator.
-/

open Filter Topology Set Asymptotics
open scoped Classical Topology BigOperators ENNReal NNReal Real Nat

noncomputable section

namespace PerronWright.PositiveSurplusNoncubicPerronWrightBound

open PerronWright.GraphCore

namespace Field

export PerronWright.PositiveSurplusNoncubicFieldWeightAsymptotic
  (complexFieldNoncubicPartConnectedWeight
   complexFieldNoncubicPartConnectedWeight_eq
   radius_pow_mul_complexFieldNoncubicPartConnectedWeight
   exists_complexFieldNoncubicPartConnectedWeight_cubicMain_bound)

end Field

namespace Scalar

export PerronWright.PositiveSurplusCubicPerronWrightFormula
  (scalarNoncubicPartContribution scalarCubicPartRadiusMainTerm)

end Scalar

namespace Radius

export PerronWright.CriticalWindowRadiusConversion
  (realScalarRadius realScalarRadius_pos_eventually)

end Radius

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Any real neighborhood of one eventually contains every shrinking
window `|t-1| ≤ eta k`. -/
theorem shrinkingWindow_eventually_mem_nhds
    (eta : ℕ → ℝ) (heta : Tendsto eta atTop (nhds 0))
    {p : ℝ → Prop} (hp : ∀ᶠ t : ℝ in nhds 1, p t) :
    ∀ᶠ k : ℕ in atTop, ∀ t : ℝ,
      |t - 1| ≤ eta k → p t := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hp
  have hnear : ∀ᶠ k : ℕ in atTop, eta k < delta :=
    heta.eventually (isOpen_Iio.mem_nhds hdelta)
  filter_upwards [hnear] with k hk
  intro t ht
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  exact ht.trans_lt hk

private theorem exists_scalarFieldComplex_real_lipschitz
    (M : CompactBJRModel S) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ t : ℝ in nhds 1,
      ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ ≤
        B * |t - 1| := by
  have hO :=
    (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M).differentiableAt.isBigO_sub
  obtain ⟨B₀, hB₀⟩ := isBigO_iff.mp hO
  let B : ℝ := max B₀ 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right B₀ 1)
  have hcast : Tendsto Complex.ofReal (nhds (1 : ℝ)) (nhds (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt
  have hbound := hcast.eventually hB₀
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound] with t ht
  have hbase := ScalarFieldResponse.scalarFieldComplex_one M
  calc
    ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ =
        ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ) -
          ScalarFieldResponse.scalarFieldComplex M 1‖ := by
            rw [hbase, sub_zero]
    _ ≤ B₀ * ‖(t : ℂ) - 1‖ := ht
    _ ≤ B * ‖(t : ℂ) - 1‖ :=
      mul_le_mul_of_nonneg_right (le_max_left B₀ 1) (norm_nonneg _)
    _ = B * |t - 1| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]

private theorem scalarSurplusPower_succ_eq_pow
    (ell : ℕ) (t : ℝ) :
    BoundedSurplusScalarPower.scalarSurplusPower (ell + 1) t =
      t ^ ell := by
  unfold BoundedSurplusScalarPower.scalarSurplusPower
  have hexp : (((ell + 1 : ℕ) : ℤ) - 1) = (ell : ℤ) := by omega
  rw [hexp, zpow_natCast]

/-- On every nonnegative shrinking scalar window, the full noncubic
contribution is uniformly a half-step below the cubic physical radius main
term. -/
theorem exists_scalarNoncubicPart_cubicRadiusMain_bound_uniform_eta
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (nhds 0) →
      ∀ᶠ k : ℕ in atTop, ∀ t : ℝ, |t - 1| ≤ eta k →
        ‖Scalar.scalarNoncubicPartContribution M t ell k /
            Scalar.scalarCubicPartRadiusMainTerm M hM ell k t‖ ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨epsilon, Kfield, hepsilon, hKfield, hfield⟩ :=
    Field.exists_complexFieldNoncubicPartConnectedWeight_cubicMain_bound
      M hM hell
  obtain ⟨Bfield, hBfield, hfieldLocal⟩ :=
    exists_scalarFieldComplex_real_lipschitz M
  obtain ⟨Cpower, hCpower, hpowerLocal⟩ :=
    BoundedSurplusScalarPower.exists_scalarSurplusPower_uniform_local_bound
      (ell + 1)
  let Kcore : ℝ := Kfield * (Bfield + 1)
  have hKcore : 0 < Kcore := by dsimp only [Kcore]; positivity
  let K : ℝ := (Cpower + 1) * Kcore
  have hK : 0 < K := mul_pos (by linarith [hCpower]) hKcore
  refine ⟨K, hK, ?_⟩
  intro eta hetaNonneg heta
  have hhalf : Tendsto
      (fun k : ℕ ↦ (k : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have hscale : Tendsto
      (fun k : ℕ ↦ eta k + (k : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by
    simpa only [zero_add] using heta.add hhalf
  have hscaleOne : ∀ᶠ k : ℕ in atTop,
      eta k + (k : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    (hscale.eventually (isOpen_Iio.mem_nhds zero_lt_one)).mono
      (fun _ hk ↦ hk.le)
  have hfieldScale : Tendsto (fun k : ℕ ↦ Bfield * eta k)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul heta
  have hfieldSmall : ∀ᶠ k : ℕ in atTop,
      Bfield * eta k < epsilon :=
    hfieldScale.eventually (isOpen_Iio.mem_nhds hepsilon)
  have hlocal : ∀ᶠ t : ℝ in nhds 1,
      ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ ≤
          Bfield * |t - 1| ∧
        (∀ r : ℕ, r ≤ ell + 1 →
          |BoundedSurplusScalarPower.scalarSurplusPower r t - 1| ≤
            Cpower * |t - 1|) ∧
        ((ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).im = 0 ∧
          0 < (ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).re) :=
    hfieldLocal.and
      (hpowerLocal.and
        (ScalarFieldResponse.scalarCriticalRadius_real_positive_near_one
          M hM))
  have hlocalWindow :=
    shrinkingWindow_eventually_mem_nhds eta heta hlocal
  filter_upwards [hfield, hscaleOne, hfieldSmall, hlocalWindow,
    eventually_ge_atTop 1] with k hkfield hkscale hkfieldSmall hklocal hkone
  intro t htWindow
  obtain ⟨hgLocal, hpowerAt, hrhoLocal⟩ := hklocal t htWindow
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  let x : ℝ := (k : ℝ) ^ (-(1 / 2 : ℝ))
  let delta : ℝ := eta k + x
  have hx : 0 ≤ x := by
    dsimp only [x]
    exact Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hdelta : 0 ≤ delta := by
    dsimp only [delta]
    exact add_nonneg (hetaNonneg k) hx
  have hdeltaOne : delta ≤ 1 := by
    simpa only [delta, x] using hkscale
  let g : C(S, ℂ) :=
    ScalarFieldResponse.scalarFieldComplex M (t : ℂ)
  have hgEta : ‖g‖ ≤ Bfield * eta k := by
    calc
      ‖g‖ ≤ Bfield * |t - 1| := by simpa only [g] using hgLocal
      _ ≤ Bfield * eta k :=
        mul_le_mul_of_nonneg_left htWindow hBfield.le
  have hg : ‖g‖ ≤ epsilon := hgEta.trans hkfieldSmall.le
  have hfieldBound := hkfield g hg
  let rho : ℝ := Radius.realScalarRadius M hM t
  let base : ℂ :=
    (Real.sqrt (M.beta hM) : ℂ) ^ ell *
      positiveSurplusCubicFactorialMain ell k
  let W : ℂ := Field.complexFieldNoncubicPartConnectedWeight M g ell k
  have hrho : 0 < rho := hrhoLocal.2
  have hrhoEq : RadiusResponse.radius M hM g = (rho : ℂ) := by
    change ScalarRadiusSecond.scalarRadius M hM (t : ℂ) =
      ((ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).re : ℂ)
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hrhoLocal.1
  have hfieldLower :
      ‖(rho : ℂ) ^ k * W / base‖ ≤ Kcore * delta := by
    rw [hrhoEq] at hfieldBound
    calc
      ‖(rho : ℂ) ^ k * W / base‖ ≤
          Kfield * (‖g‖ + x) := by
        simpa only [g, W, base, x] using hfieldBound
      _ ≤ Kfield * (Bfield * eta k + x) :=
        mul_le_mul_of_nonneg_left
          (by simpa only [add_comm] using add_le_add_right hgEta x) hKfield.le
      _ ≤ Kcore * delta := by
        dsimp only [Kcore, delta]
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left ?_ hKfield.le
        nlinarith [hetaNonneg k, hx, mul_nonneg hBfield.le hx]
  have hpowerReal : |t ^ ell - 1| ≤ Cpower * eta k := by
    have hp := hpowerAt (ell + 1) (le_refl _)
    rw [scalarSurplusPower_succ_eq_pow] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left htWindow hCpower.le)
  have hpowerNorm : ‖(t : ℂ) ^ ell‖ ≤ Cpower + 1 := by
    calc
      ‖(t : ℂ) ^ ell‖ = ‖((t : ℂ) ^ ell - 1) + 1‖ := by
        congr 1
        ring
      _ ≤ ‖(t : ℂ) ^ ell - 1‖ + 1 := by
        simpa only [norm_one] using
          norm_add_le ((t : ℂ) ^ ell - 1) (1 : ℂ)
      _ = |t ^ ell - 1| + 1 := by
        have hcast : (t : ℂ) ^ ell - 1 = ((t ^ ell - 1 : ℝ) : ℂ) := by
          norm_cast
        rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ Cpower * eta k + 1 := by
        simpa only [add_comm] using add_le_add_right hpowerReal 1
      _ ≤ Cpower + 1 := by
        have hetaOne : eta k ≤ 1 := by
          dsimp only [delta, x] at hdeltaOne
          linarith
        nlinarith [mul_le_mul_of_nonneg_left hetaOne hCpower.le]
  have hb : base ≠ 0 := by
    dsimp only [base]
    apply mul_ne_zero
    · exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.2 (M.beta_pos hM)).ne')
    · rw [positiveSurplusCubicFactorialMain_eq_exp_rpow
        ell hell hkpos]
      apply mul_ne_zero (positiveSurplusWrightConstant_ne_zero ell hell)
      exact Complex.ofReal_ne_zero.mpr
        (mul_pos (Real.exp_pos _)
          (Real.rpow_pos_of_pos (by exact_mod_cast hkpos) _)).ne'
  have hratio :
      Scalar.scalarNoncubicPartContribution M t ell k /
          Scalar.scalarCubicPartRadiusMainTerm M hM ell k t =
        (t : ℂ) ^ ell * ((rho : ℂ) ^ k * W / base) := by
    have hrhoC : (rho : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hrho.ne'
    dsimp only [
      PerronWright.PositiveSurplusCubicPerronWrightFormula.scalarNoncubicPartContribution,
      PerronWright.PositiveSurplusCubicPerronWrightFormula.scalarCubicPartRadiusMainTerm,
      g, W, base, rho]
    rw [Field.complexFieldNoncubicPartConnectedWeight_eq]
    rw [inv_pow]
    field_simp [hrhoC, pow_ne_zero k hrhoC, hb]
  rw [hratio, norm_mul]
  calc
    ‖(t : ℂ) ^ ell‖ * ‖(rho : ℂ) ^ k * W / base‖ ≤
        (Cpower + 1) * (Kcore * delta) :=
      mul_le_mul hpowerNorm hfieldLower (norm_nonneg _)
        (by positivity)
    _ = K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
      dsimp only [K, delta, x]
      ring

/-- Compatibility form with a prescribed shrinking window. -/
theorem exists_scalarNoncubicPart_cubicRadiusMain_bound_of_tendsto
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {ell : ℕ} (hell : 0 < ell)
    (eta : ℕ → ℝ) (hetaNonneg : ∀ k, 0 ≤ eta k)
    (heta : Tendsto eta atTop (nhds 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ, |t - 1| ≤ eta k →
        ‖Scalar.scalarNoncubicPartContribution M t ell k /
            Scalar.scalarCubicPartRadiusMainTerm M hM ell k t‖ ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, huniform⟩ :=
    exists_scalarNoncubicPart_cubicRadiusMain_bound_uniform_eta M hM hell
  exact ⟨K, hK, huniform eta hetaNonneg heta⟩

end PerronWright.PositiveSurplusNoncubicPerronWrightBound
