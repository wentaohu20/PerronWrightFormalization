import PerronWright.Analysis.FiniteIrreducibleConnectedFieldAsymptotic
import PerronWright.Analysis.BoundedSurplusScalarPower
import PerronWright.Analysis.FiniteIrreducibleCriticalWindowRadiusConversion
import PerronWright.Analysis.RelativeErrorProduct

/-!
# Scalar Perron--Wright asymptotics for literal finite irreducible types

The contribution is the complete genuine connected weight, not the cubic
summand. The exact complex-field estimate is specialized to the physical
scalar field and combined with the proved finite scalar log-radius Taylor
expansion. Symmetric nonnegative irreducible matrices, including bipartite
ones with eigenvalue -1, are permitted.

The final real connected-weight statements are the literal physical formula
at every fixed positive surplus. Tree and unicyclic cases remain separate.
-/

open Filter Topology Set Asymptotics
open scoped Classical Topology BigOperators ENNReal NNReal Real Nat

noncomputable section

namespace PerronWright.FiniteIrreducibleConnectedPerronWrightFormula

open PerronWright.GraphCore

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

namespace Field

/-- An index-compatible abbreviation of the exact original connected weight. -/
def complexFieldConnectedWeight
    (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) (ell k : ℕ) : ℂ :=
  M.bjrModel.complexFieldConnectedWeight g k (ell + 1)

theorem exists_complexFieldConnectedWeight_local_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ epsilon K : ℝ, 0 < epsilon ∧ 0 < K ∧
      ∀ᶠ k : ℕ in atTop, ∀ g : C(S, ℂ),
        ‖g‖ ≤ epsilon →
        ‖(FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
            complexFieldConnectedWeight M g ell k /
            ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
              positiveSurplusCubicFactorialMain ell k) - 1‖ ≤
          K * (‖g‖ + (k : ℝ) ^ (-(1 / 2 : ℝ))) :=
  FiniteIrreducibleConnectedFieldAsymptotic.exists_complexFieldConnectedWeight_local_relative_bound
    M hM hell

end Field

namespace Radius
export PerronWright.FiniteIrreducibleCriticalWindowRadiusConversion
  (realScalarRadius criticalQuadraticRate
   realScalarRadius_pos_eventually
   exists_criticalWindowRadius_relative_bound)
end Radius

/-- Physical scalar specialization of the full genuine connected weight. -/
def scalarConnectedContribution
    (M : FiniteIrreducibleModel S) (t : ℝ) (ell k : ℕ) : ℂ :=
  (t : ℂ) ^ ell *
    Field.complexFieldConnectedWeight M
      (ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)) ell k

/-- The physical scalar specialization equals the original annealed
simple connected-graph partition function. -/
theorem scalarConnectedContribution_eq_connectedWeight
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 < t) (ell k : ℕ) :
    scalarConnectedContribution M t ell k =
      (M.bjrModel.connectedWeight t k (ell + 1) : ℂ) := by
  have h := ScalarFieldResponse.connectedWeight_scalarFieldComplex
    M.bjrModel t ht k (ell + 1)
  have hexp : (((ell + 1 : ℕ) : ℤ) - 1) = (ell : ℤ) := by omega
  rw [hexp, zpow_natCast] at h
  exact h.symm

/-- The radius-dependent total connected-graph Perron--Wright main term. -/
def scalarConnectedRadiusMainTerm
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell k : ℕ) (t : ℝ) : ℂ :=
  ((Radius.realScalarRadius M hM t : ℂ)⁻¹) ^ k *
    ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
      positiveSurplusCubicFactorialMain ell k)

/-- The Gaussian critical-window main term for the total connected weight. -/
def scalarConnectedGaussianMainTerm
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (ell k : ℕ) (t : ℝ) : ℂ :=
  ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
      positiveSurplusCubicFactorialMain ell k) *
    (Real.exp (-Radius.criticalQuadraticRate M hM * (k : ℝ) *
      (t - 1) ^ 2) : ℂ)

/-- The radius main term exposes exactly the physical Wright constant and
the positive-surplus power scale. -/
theorem scalarConnectedRadiusMainTerm_eq_exp_rpow
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell k : ℕ} (hell : 0 < ell) (hk : 0 < k) (t : ℝ) :
    scalarConnectedRadiusMainTerm M hM ell k t =
      ((Radius.realScalarRadius M hM t : ℂ)⁻¹) ^ k *
        ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
          positiveSurplusWrightConstant ell *
            (Real.exp (-(k : ℝ)) *
              (k : ℝ) ^
                ((k : ℝ) + positiveSurplusCubicExponent ell - 1 / 2) : ℝ)) := by
  unfold scalarConnectedRadiusMainTerm
  rw [positiveSurplusCubicFactorialMain_eq_exp_rpow ell hell hk]
  push_cast
  ring

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
/-- The Gaussian main term in the same literal Wright normalization. -/
theorem scalarConnectedGaussianMainTerm_eq_exp_rpow
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell k : ℕ} (hell : 0 < ell) (hk : 0 < k) (t : ℝ) :
    scalarConnectedGaussianMainTerm M hM ell k t =
      (Real.sqrt (M.beta hM) : ℂ) ^ ell *
        positiveSurplusWrightConstant ell *
          (Real.exp (-(k : ℝ)) *
            (k : ℝ) ^
              ((k : ℝ) + positiveSurplusCubicExponent ell - 1 / 2) : ℝ) *
        (Real.exp (-Radius.criticalQuadraticRate M hM * (k : ℝ) *
          (t - 1) ^ 2) : ℂ) := by
  unfold scalarConnectedGaussianMainTerm
  rw [positiveSurplusCubicFactorialMain_eq_exp_rpow ell hell hk]
  push_cast
  ring

private theorem rpow_neg_half_eq_inv_sqrt {k : ℕ} (hk : 0 < k) :
    (k : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (k : ℝ))⁻¹ := by
  have hkreal : (0 : ℝ) ≤ k := by exact_mod_cast hk.le
  rw [Real.rpow_neg hkreal, ← Real.sqrt_eq_rpow]

private theorem eventually_shrinking_window_mem_nhds
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

private theorem eventually_sqrt_window_mem_nhds
    (L : ℝ) {p : ℝ → Prop}
    (hp : ∀ᶠ t : ℝ in nhds 1, p t) :
    ∀ᶠ k : ℕ in atTop, ∀ t : ℝ,
      Real.sqrt (k : ℝ) * |t - 1| ≤ L → p t := by
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hp
  have hsqrt : Tendsto (fun k : ℕ ↦ Real.sqrt (k : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun k : ℕ ↦ (Real.sqrt (k : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hsqrt
  have hnearLim : Tendsto
      (fun k : ℕ ↦ (L + 1) * (Real.sqrt (k : ℝ))⁻¹)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hinv
  have hnear : ∀ᶠ k : ℕ in atTop,
      (L + 1) * (Real.sqrt (k : ℝ))⁻¹ < delta :=
    hnearLim.eventually (isOpen_Iio.mem_nhds hdelta)
  filter_upwards [eventually_ge_atTop 1, hnear] with k hk hknear
  intro t hwindow
  have hkpos : 0 < k := by omega
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hspos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have hy : |t - 1| ≤ L / Real.sqrt (k : ℝ) := by
    exact (le_div_iff₀ hspos).2 (by simpa only [mul_comm] using hwindow)
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  calc
    |t - 1| ≤ L / Real.sqrt (k : ℝ) := hy
    _ ≤ (L + 1) / Real.sqrt (k : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hspos.le
    _ = (L + 1) * (Real.sqrt (k : ℝ))⁻¹ := by rw [div_eq_mul_inv]
    _ < delta := hknear

private theorem exists_scalarFieldComplex_real_lipschitz
    (M : FiniteIrreducibleModel S) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ t : ℝ in nhds 1,
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
        B * |t - 1| := by
  have hO :=
    (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M.bjrModel).differentiableAt.isBigO_sub
  obtain ⟨B0, hB0⟩ := isBigO_iff.mp hO
  let B : ℝ := max B0 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right B0 1)
  have hcast : Tendsto Complex.ofReal (nhds (1 : ℝ)) (nhds (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt
  have hbound := hcast.eventually hB0
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound] with t ht
  have hbase := ScalarFieldResponse.scalarFieldComplex_one M.bjrModel
  calc
    ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ =
        ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ) -
          ScalarFieldResponse.scalarFieldComplex M.bjrModel 1‖ := by rw [hbase, sub_zero]
    _ ≤ B0 * ‖(t : ℂ) - 1‖ := ht
    _ ≤ B * ‖(t : ℂ) - 1‖ :=
      mul_le_mul_of_nonneg_right (le_max_left B0 1) (norm_nonneg _)
    _ = B * |t - 1| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]

private theorem norm_two_factor_sub_one_le
    {a b : ℂ} {x A B : ℝ}
    (hx : 0 ≤ x) (hxone : x ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ‖a - 1‖ ≤ A * x) (hb : ‖b - 1‖ ≤ B * x) :
    ‖a * b - 1‖ ≤ (A * (1 + B) + B) * x := by
  have hBx : B * x ≤ B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hxone hB
  have hbNorm : ‖b‖ ≤ 1 + B := by
    calc
      ‖b‖ = ‖(b - 1) + 1‖ := by
        congr 1
        ring
      _ ≤ ‖b - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ B * x + 1 := by simpa using add_le_add_right hb 1
      _ ≤ 1 + B := by linarith
  have hdecomp : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [hdecomp]
  calc
    ‖(a - 1) * b + (b - 1)‖ ≤
        ‖a - 1‖ * ‖b‖ + ‖b - 1‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_mul_le _ _) (le_refl _))
    _ ≤ (A * x) * (1 + B) + B * x :=
      add_le_add
        (mul_le_mul ha hbNorm (norm_nonneg _) (mul_nonneg hA hx)) hb
    _ = (A * (1 + B) + B) * x := by ring

private theorem scalarSurplusPower_succ_eq_pow
    (ell : ℕ) (t : ℝ) :
    BoundedSurplusScalarPower.scalarSurplusPower (ell + 1) t =
      t ^ ell := by
  unfold BoundedSurplusScalarPower.scalarSurplusPower
  have hexp : (((ell + 1 : ℕ) : ℤ) - 1) = (ell : ℤ) := by omega
  rw [hexp, zpow_natCast]

/-- Radius form of the scalar total connected-graph formula on an arbitrary
nonnegative shrinking window. -/
theorem exists_scalarConnected_radius_relative_bound_uniform_eta
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (nhds 0) →
      ∀ᶠ k : ℕ in atTop, ∀ t : ℝ, |t - 1| ≤ eta k →
        ‖scalarConnectedContribution M t ell k /
            scalarConnectedRadiusMainTerm M hM ell k t - 1‖ ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨epsilon, Kfield, hepsilon, hKfield, hfield⟩ :=
    Field.exists_complexFieldConnectedWeight_local_relative_bound
      M hM hell
  obtain ⟨Bfield, hBfield, hfieldLocal⟩ :=
    exists_scalarFieldComplex_real_lipschitz M
  obtain ⟨Cpower, hCpower, hpowerLocal⟩ :=
    BoundedSurplusScalarPower.exists_scalarSurplusPower_uniform_local_bound
      (ell + 1)
  let Kcore : ℝ := Kfield * (Bfield + 1)
  have hKcore : 0 < Kcore := by dsimp only [Kcore]; positivity
  let K : ℝ := Cpower * (1 + Kcore) + Kcore
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro eta hetaNonneg heta
  have hhalf : Tendsto
      (fun k : ℕ ↦ (k : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have hscale : Tendsto
      (fun k : ℕ ↦ eta k + (k : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by simpa only [zero_add] using heta.add hhalf
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
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
          Bfield * |t - 1| ∧
        (∀ r : ℕ, r ≤ ell + 1 →
          |BoundedSurplusScalarPower.scalarSurplusPower r t - 1| ≤
            Cpower * |t - 1|) ∧
        ((FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).im = 0 ∧
          0 < (FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).re) :=
    hfieldLocal.and
      (hpowerLocal.and
        (FiniteIrreducibleScalarFieldResponse.scalarRadius_real_positive_near_one M hM))
  have hlocalWindow :=
    eventually_shrinking_window_mem_nhds eta heta hlocal
  filter_upwards [hfield, hscaleOne, hfieldSmall, hlocalWindow,
    eventually_ge_atTop 1] with k hkfield hkscale hkfieldSmall hklocal hkone
  intro t htWindow
  obtain ⟨hgLocal, hpowerAt, hrhoLocal⟩ :=
    hklocal t htWindow
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  let x : ℝ := (k : ℝ) ^ (-(1 / 2 : ℝ))
  let delta : ℝ := eta k + x
  have hx : 0 ≤ x := by
    dsimp only [x]
    exact Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hdelta : 0 ≤ delta := by
    dsimp only [delta]
    exact add_nonneg (hetaNonneg k) hx
  have hdeltaOne : delta ≤ 1 := by simpa only [delta, x] using hkscale
  let g : C(S, ℂ) :=
    ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)
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
  let W : ℂ := Field.complexFieldConnectedWeight M g ell k
  have hrho : 0 < rho := hrhoLocal.2
  have hrhoEq : FiniteIrreducibleRadiusResponse.radius M hM g = (rho : ℂ) := by
    change FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ) =
      ((FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).re : ℂ)
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hrhoLocal.1
  have hfieldError :
      ‖(rho : ℂ) ^ k * W / base - 1‖ ≤ Kcore * delta := by
    rw [hrhoEq] at hfieldBound
    calc
      ‖(rho : ℂ) ^ k * W / base - 1‖ ≤
          Kfield * (‖g‖ + x) := by
        simpa only [g, W, base, x] using hfieldBound
      _ ≤ Kfield * (Bfield * eta k + x) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hgEta x) hKfield.le
      _ ≤ Kcore * delta := by
        have hextra : 0 ≤ Bfield * x + eta k :=
          add_nonneg (mul_nonneg hBfield.le hx) (hetaNonneg k)
        have hinner :
            Bfield * eta k + x ≤ (Bfield + 1) * (eta k + x) := by
          calc
            Bfield * eta k + x ≤
                Bfield * eta k + x + (Bfield * x + eta k) :=
              le_add_of_nonneg_right hextra
            _ = (Bfield + 1) * (eta k + x) := by ring
        calc
          Kfield * (Bfield * eta k + x) ≤
              Kfield * ((Bfield + 1) * (eta k + x)) :=
            mul_le_mul_of_nonneg_left hinner hKfield.le
          _ = Kcore * delta := by dsimp only [Kcore, delta]; ring
  have hpowerReal : |t ^ ell - 1| ≤ Cpower * eta k := by
    have hp := hpowerAt (ell + 1) (le_refl _)
    rw [scalarSurplusPower_succ_eq_pow] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left htWindow hCpower.le)
  have hpower : ‖(t : ℂ) ^ ell - 1‖ ≤ Cpower * delta := by
    have hcast : (t : ℂ) ^ ell - 1 = ((t ^ ell - 1 : ℝ) : ℂ) := by
      norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    exact hpowerReal.trans
      (mul_le_mul_of_nonneg_left (by
        dsimp only [delta, x]
        linarith) hCpower.le)
  have hb : base ≠ 0 := by
    dsimp only [base]
    apply mul_ne_zero
    · exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.2 (M.beta_pos hM)).ne')
    · rw [positiveSurplusCubicFactorialMain_eq_exp_rpow ell hell hkpos]
      apply mul_ne_zero (positiveSurplusWrightConstant_ne_zero ell hell)
      exact Complex.ofReal_ne_zero.mpr
        (mul_pos (Real.exp_pos _)
          (Real.rpow_pos_of_pos (by exact_mod_cast hkpos) _)).ne'
  have hratio :
      scalarConnectedContribution M t ell k /
          scalarConnectedRadiusMainTerm M hM ell k t =
        (t : ℂ) ^ ell * ((rho : ℂ) ^ k * W / base) := by
    have hrhoC : (rho : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hrho.ne'
    dsimp only [scalarConnectedContribution,
      scalarConnectedRadiusMainTerm, g, W, base, rho]
    rw [inv_pow]
    field_simp [hrhoC, pow_ne_zero k hrhoC, hb]
  rw [hratio]
  exact norm_two_factor_sub_one_le hdelta hdeltaOne hCpower.le
    hKcore.le hpower hfieldError

/-- Compatibility form with a prescribed shrinking window. -/
theorem exists_scalarConnected_radius_relative_bound_of_tendsto
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell)
    (eta : ℕ → ℝ) (hetaNonneg : ∀ k, 0 ≤ eta k)
    (heta : Tendsto eta atTop (nhds 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ, |t - 1| ≤ eta k →
        ‖scalarConnectedContribution M t ell k /
            scalarConnectedRadiusMainTerm M hM ell k t - 1‖ ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, huniform⟩ :=
    exists_scalarConnected_radius_relative_bound_uniform_eta M hM hell
  exact ⟨K, hK, huniform eta hetaNonneg heta⟩

/-- Radius form on the standard critical window. -/
theorem exists_scalarConnected_radius_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ, Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        ‖scalarConnectedContribution M t ell k /
            scalarConnectedRadiusMainTerm M hM ell k t - 1‖ ≤
          K / Real.sqrt (k : ℝ) := by
  let eta : ℕ → ℝ := fun k ↦
    L * (k : ℝ) ^ (-(1 / 2 : ℝ))
  have hetaNonneg : ∀ k, 0 ≤ eta k := fun k ↦
    mul_nonneg hL (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have heta : Tendsto eta atTop (nhds 0) := by
    have hhalf : Tendsto
        (fun k : ℕ ↦ (k : ℝ) ^ (-(1 / 2 : ℝ)))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
        tendsto_natCast_atTop_atTop
    simpa only [eta, mul_zero] using tendsto_const_nhds.mul hhalf
  obtain ⟨K0, hK0, hmain⟩ :=
    exists_scalarConnected_radius_relative_bound_of_tendsto
      M hM hell eta hetaNonneg heta
  let K : ℝ := K0 * (L + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop 1] with k hk hkone
  intro t hwindow
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hspos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  let x : ℝ := (k : ℝ) ^ (-(1 / 2 : ℝ))
  have hx : x = (Real.sqrt (k : ℝ))⁻¹ :=
    rpow_neg_half_eq_inv_sqrt hkpos
  have ht : |t - 1| ≤ eta k := by
    have hdiv := (le_div_iff₀ hspos).2 (by
      simpa only [mul_comm] using hwindow)
    simpa only [eta, x, div_eq_mul_inv, ← hx] using hdiv
  have hbound := hk t ht
  calc
    ‖scalarConnectedContribution M t ell k /
        scalarConnectedRadiusMainTerm M hM ell k t - 1‖ ≤
        K0 * (eta k + x) := by simpa only [x] using hbound
    _ = K / Real.sqrt (k : ℝ) := by
      dsimp only [K, eta, x]
      rw [rpow_neg_half_eq_inv_sqrt hkpos, div_eq_mul_inv]
      ring

/-- The pure field ratio on the scalar critical window, before inserting
the elementary scalar factor `t^ell`. -/
private theorem exists_scalarConnectedFieldRatio_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ, Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        ‖(Radius.realScalarRadius M hM t : ℂ) ^ k *
              Field.complexFieldConnectedWeight M
                (ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)) ell k /
              ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
                positiveSurplusCubicFactorialMain ell k) - 1‖ ≤
          K / Real.sqrt (k : ℝ) := by
  obtain ⟨epsilon, Kfield, hepsilon, hKfield, hfield⟩ :=
    Field.exists_complexFieldConnectedWeight_local_relative_bound
      M hM hell
  obtain ⟨Bfield, hBfield, hfieldLocal⟩ :=
    exists_scalarFieldComplex_real_lipschitz M
  let U : ℝ := Bfield * L
  have hU : 0 ≤ U := mul_nonneg hBfield.le hL
  let K : ℝ := Kfield * (U + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hhalf : Tendsto
      (fun k : ℕ ↦ (k : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have hfieldScale : Tendsto
      (fun k : ℕ ↦ U * (k : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hhalf
  have hfieldSmall : ∀ᶠ k : ℕ in atTop,
      U * (k : ℝ) ^ (-(1 / 2 : ℝ)) < epsilon :=
    hfieldScale.eventually (isOpen_Iio.mem_nhds hepsilon)
  have hlocal : ∀ᶠ t : ℝ in nhds 1,
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
          Bfield * |t - 1| ∧
        ((FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).im = 0 ∧
          0 < (FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).re) :=
    hfieldLocal.and
      (FiniteIrreducibleScalarFieldResponse.scalarRadius_real_positive_near_one M hM)
  have hlocalWindow := eventually_sqrt_window_mem_nhds L hlocal
  filter_upwards [hfield, hfieldSmall, hlocalWindow,
    eventually_ge_atTop 1] with k hkfield hkfieldSmall hklocal hkone
  intro t hwindow
  obtain ⟨hgLocal, hrhoLocal⟩ := hklocal t hwindow
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hspos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  let x : ℝ := (k : ℝ) ^ (-(1 / 2 : ℝ))
  have hxSqrt : x = (Real.sqrt (k : ℝ))⁻¹ :=
    rpow_neg_half_eq_inv_sqrt hkpos
  have htScale : |t - 1| ≤ L * x := by
    have hdiv := (le_div_iff₀ hspos).2 (by
      simpa only [mul_comm] using hwindow)
    rw [div_eq_mul_inv, ← hxSqrt] at hdiv
    exact hdiv
  let g : C(S, ℂ) :=
    ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)
  have hgU : ‖g‖ ≤ U * x := by
    calc
      ‖g‖ ≤ Bfield * |t - 1| := by simpa only [g] using hgLocal
      _ ≤ Bfield * (L * x) :=
        mul_le_mul_of_nonneg_left htScale hBfield.le
      _ = U * x := by dsimp only [U]; ring
  have hg : ‖g‖ ≤ epsilon := by
    exact hgU.trans hkfieldSmall.le
  have hbound := hkfield g hg
  let rho : ℝ := Radius.realScalarRadius M hM t
  have hrhoEq : FiniteIrreducibleRadiusResponse.radius M hM g = (rho : ℂ) := by
    change FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ) =
      ((FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).re : ℂ)
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hrhoLocal.1
  rw [hrhoEq] at hbound
  calc
    ‖(rho : ℂ) ^ k *
          Field.complexFieldConnectedWeight M g ell k /
          ((Real.sqrt (M.beta hM) : ℂ) ^ ell *
            positiveSurplusCubicFactorialMain ell k) - 1‖ ≤
        Kfield * (‖g‖ + x) := by simpa only [g, rho, x] using hbound
    _ ≤ Kfield * (U * x + x) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hgU x) hKfield.le
    _ = K / Real.sqrt (k : ℝ) := by
      dsimp only [K, U]
      rw [hxSqrt, div_eq_mul_inv]
      ring

/-- Gaussian critical-window formula for the scalar total connected weight. -/
theorem exists_scalarConnected_gaussian_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ, Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        ‖scalarConnectedContribution M t ell k /
            scalarConnectedGaussianMainTerm M hM ell k t - 1‖ ≤
          K / Real.sqrt (k : ℝ) := by
  obtain ⟨Kfield, hKfield, hfield⟩ :=
    exists_scalarConnectedFieldRatio_relative_bound M hM hell L hL
  obtain ⟨Kradius, hKradius, hradius⟩ :=
    Radius.exists_criticalWindowRadius_relative_bound M hM L hL
  obtain ⟨Cpower, hCpower, hpowerLocal⟩ :=
    BoundedSurplusScalarPower.exists_scalarSurplusPower_uniform_local_bound
      (ell + 1)
  let Apower : ℝ := Cpower * L
  have hApower : 0 ≤ Apower := mul_nonneg hCpower.le hL
  let Kpref : ℝ := Apower * (1 + Kradius) + Kradius
  have hKpref : 0 < Kpref := by dsimp only [Kpref]; positivity
  let K : ℝ := Kpref * (1 + Kfield) + Kfield
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hrhoWindow := eventually_sqrt_window_mem_nhds L
    (Radius.realScalarRadius_pos_eventually M hM)
  have hpowerWindow := eventually_sqrt_window_mem_nhds L hpowerLocal
  filter_upwards [hfield, hradius, hpowerWindow, hrhoWindow,
    eventually_ge_atTop 1] with
      k hkfield hkradius hkpower hkrho hkone
  intro t hwindow
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  let x : ℝ := (Real.sqrt (k : ℝ))⁻¹
  have hx : 0 ≤ x := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hxone : x ≤ 1 := by
    dsimp only [x]
    exact inv_le_one_of_one_le₀
      ((Real.one_le_sqrt).2 (by exact_mod_cast hkone))
  have hfieldBound := hkfield t hwindow
  have hradiusBound := hkradius t hwindow
  have hpowerAt := hkpower t hwindow
  have hrho := hkrho t hwindow
  let rho : ℝ := Radius.realScalarRadius M hM t
  let G : ℝ := Real.exp
    (-Radius.criticalQuadraticRate M hM * (k : ℝ) * (t - 1) ^ 2)
  let B : ℂ :=
    (Real.sqrt (M.beta hM) : ℂ) ^ ell *
      positiveSurplusCubicFactorialMain ell k
  have hG : 0 < G := by dsimp only [G]; positivity
  have hB : B ≠ 0 := by
    dsimp only [B]
    apply mul_ne_zero
    · exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.2 (M.beta_pos hM)).ne')
    · rw [positiveSurplusCubicFactorialMain_eq_exp_rpow ell hell hkpos]
      apply mul_ne_zero (positiveSurplusWrightConstant_ne_zero ell hell)
      exact Complex.ofReal_ne_zero.mpr
        (mul_pos (Real.exp_pos _)
          (Real.rpow_pos_of_pos (by exact_mod_cast hkpos) _)).ne'
  have hspos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have htScale : |t - 1| ≤ L * x := by
    have hdiv := (le_div_iff₀ hspos).2 (by
      simpa only [mul_comm] using hwindow)
    simpa only [x, div_eq_mul_inv] using hdiv
  have hpowerReal : |t ^ ell - 1| ≤ Apower * x := by
    have hp := hpowerAt (ell + 1) (le_refl _)
    rw [scalarSurplusPower_succ_eq_pow] at hp
    calc
      |t ^ ell - 1| ≤ Cpower * |t - 1| := hp
      _ ≤ Cpower * (L * x) :=
        mul_le_mul_of_nonneg_left htScale hCpower.le
      _ = Apower * x := by dsimp only [Apower]; ring
  have hradiusReal : |rho⁻¹ ^ k / G - 1| ≤ Kradius * x := by
    simpa only [rho, G, x, div_eq_mul_inv] using hradiusBound
  have hprefReal :
      |t ^ ell * (rho⁻¹ ^ k / G) - 1| ≤ Kpref * x := by
    have htwo := PerronWright.RelativeErrorProduct.abs_two_factor_sub_one_le
      hx hxone hApower hKradius.le hpowerReal hradiusReal
    simpa only [Kpref] using htwo
  have hpref :
      ‖((t ^ ell * (rho⁻¹ ^ k / G) : ℝ) : ℂ) - 1‖ ≤
        Kpref * x := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact hprefReal
  let g : C(S, ℂ) :=
    ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)
  let W : ℂ := Field.complexFieldConnectedWeight M g ell k
  have hfieldError :
      ‖(rho : ℂ) ^ k * W / B - 1‖ ≤ Kfield * x := by
    simpa only [g, W, B, rho, x, div_eq_mul_inv] using hfieldBound
  have hfactor :
      scalarConnectedContribution M t ell k /
          scalarConnectedGaussianMainTerm M hM ell k t =
        ((t ^ ell * (rho⁻¹ ^ k / G) : ℝ) : ℂ) *
          ((rho : ℂ) ^ k * W / B) := by
    have hrho0 : rho ≠ 0 := by
      dsimp only [rho]
      exact hrho.ne'
    have hGC : (G : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hG.ne'
    have hprefCast :
        ((t ^ ell * (rho⁻¹ ^ k / G) : ℝ) : ℂ) =
          (t : ℂ) ^ ell *
            (((rho : ℂ)⁻¹) ^ k / (G : ℂ)) := by
      push_cast
      rfl
    rw [hprefCast]
    dsimp only [scalarConnectedContribution,
      scalarConnectedGaussianMainTerm, g, W, B, rho, G]
    have hrhoC : (rho : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hrho0
    rw [inv_pow]
    field_simp [hrhoC, pow_ne_zero k hrhoC, hGC, hB]
    change
      (t : ℂ) ^ ell * W / B =
        ((t : ℂ) ^ ell * W * (rho : ℂ) ^ k) /
          (B * (rho : ℂ) ^ k)
    field_simp [hB, pow_ne_zero k hrhoC]
  rw [hfactor]
  have htwo := norm_two_factor_sub_one_le hx hxone
    hKpref.le hKfield.le hpref hfieldError
  simpa only [K, x, div_eq_mul_inv] using htwo

end PerronWright.FiniteIrreducibleConnectedPerronWrightFormula
