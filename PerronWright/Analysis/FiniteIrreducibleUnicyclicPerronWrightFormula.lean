import PerronWright.Analysis.FiniteIrreducibleFieldUnicyclicCoefficientAsymptotic
import PerronWright.Analysis.FiniteIrreducibleCriticalWindowRadiusConversion
import PerronWright.Enumeration.UnicyclicPerronWrightFormula
import PerronWright.Transfer.QuantitativeStirling

/-!
# The physical scalar Perron--Wright formula at surplus one

This file converts the field-uniform logarithmic coefficient estimate into
the physical scalar formula for the literal quantity
`M.bjrModel.connectedWeight t k 1` of a literal finite irreducible model.
No primitivity or two-step positivity is imposed. No Wright-constant hypothesis is
introduced: the coefficient `1 / (4 k)` and quantitative Stirling give the
constant `sqrt (2 * pi) / 4` directly.

The first physical theorem keeps the genuine critical radius `rho(t)` in the
main term.  A second theorem uses the cubic expansion of `log rho(t)` to give
the Gaussian critical-window form.  In both statements the constant and the
eventual threshold are chosen before `t`.
-/

open Filter Topology Set Asymptotics MeasureTheory
open scoped Classical Topology ENNReal NNReal Real Nat

noncomputable section

namespace PerronWright.FiniteIrreducibleUnicyclicPerronWrightFormula

namespace Field

export PerronWright.FiniteIrreducibleFieldUnicyclicCoefficientAsymptotic
  (exists_complexFieldUnicyclic_connectedWeight_uniform_bound)

end Field

namespace Tree

abbrev physicalTreeRadius {S : Type*} [Fintype S] [DecidableEq S]
    [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (t : ℝ) : ℝ :=
  PerronWright.FiniteIrreducibleCriticalWindowRadiusConversion.realScalarRadius M hM t

end Tree

namespace Radius

export PerronWright.FiniteIrreducibleCriticalWindowRadiusConversion
  (criticalQuadraticRate exists_criticalWindowRadius_relative_bound)

end Radius

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

export PerronWright.UnicyclicPerronWrightFormula
  (unicyclicCoefficientMainTerm unicyclicWrightConstant
   unicyclicPerronWrightMainTerm unicyclicPerronWrightMainTerm_eq
   unicyclicPerronWrightMainTerm_eq_exp_rpow
   factorialStirlingMainTerm_mul_unicyclicCoefficientMainTerm_eq)

private theorem rpow_neg_half_eq_inv_sqrt {k : ℕ} (hk : 0 < k) :
    (k : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (k : ℝ))⁻¹ := by
  have hkreal : (0 : ℝ) ≤ k := by exact_mod_cast hk.le
  rw [Real.rpow_neg hkreal, ← Real.sqrt_eq_rpow]

private theorem rpow_neg_one_le_neg_half {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ)⁻¹ ≤ (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hkreal (by norm_num)

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
  have hy : |t - 1| ≤ L / Real.sqrt (k : ℝ) :=
    (le_div_iff₀ hspos).2 (by simpa only [mul_comm] using hwindow)
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  calc
    |t - 1| ≤ L / Real.sqrt (k : ℝ) := hy
    _ ≤ (L + 1) / Real.sqrt (k : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hspos.le
    _ = (L + 1) * (Real.sqrt (k : ℝ))⁻¹ := by
      rw [div_eq_mul_inv]
    _ < delta := hknear

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

private theorem exists_scalarFieldComplex_real_lipschitz
    (M : FiniteIrreducibleModel S) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ t : ℝ in nhds 1,
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
        B * |t - 1| := by
  have hO :=
    (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M.bjrModel).differentiableAt.isBigO_sub
  obtain ⟨B₀, hB₀⟩ := isBigO_iff.mp hO
  let B : ℝ := max B₀ 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right B₀ 1)
  have hcast : Tendsto Complex.ofReal (nhds (1 : ℝ)) (nhds (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt
  have hbound := hcast.eventually hB₀
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound] with t ht
  have hbase := ScalarFieldResponse.scalarFieldComplex_one M.bjrModel
  calc
    ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ =
        ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ) -
          ScalarFieldResponse.scalarFieldComplex M.bjrModel 1‖ := by rw [hbase, sub_zero]
    _ ≤ B₀ * ‖(t : ℂ) - 1‖ := ht
    _ ≤ B * ‖(t : ℂ) - 1‖ :=
      mul_le_mul_of_nonneg_right (le_max_left B₀ 1) (norm_nonneg _)
    _ = B * |t - 1| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]

private theorem abs_two_factor_sub_one_le
    {a b x A B : ℝ}
    (hx : 0 ≤ x) (hxone : x ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : |a - 1| ≤ A * x) (hb : |b - 1| ≤ B * x) :
    |a * b - 1| ≤ (A * (1 + B) + B) * x := by
  have hBx : B * x ≤ B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hxone hB
  have hbabs : |b| ≤ 1 + B := by
    calc
      |b| = |(b - 1) + 1| := by
        apply congrArg abs
        ring
      _ ≤ |b - 1| + 1 := by simpa using abs_add_le (b - 1) 1
      _ ≤ B * x + 1 := by linarith
      _ ≤ 1 + B := by linarith
  have hdecomp : a * b - 1 = (a - 1) * b + (b - 1) := by ring
  rw [hdecomp]
  calc
    |(a - 1) * b + (b - 1)| ≤ |a - 1| * |b| + |b - 1| := by
      simpa only [abs_mul] using abs_add_le ((a - 1) * b) (b - 1)
    _ ≤ (A * x) * (1 + B) + B * x :=
      add_le_add
        (mul_le_mul ha hbabs (abs_nonneg _) (mul_nonneg hA hx)) hb
    _ = (A * (1 + B) + B) * x := by ring

/-- Uniform relative form of the field-unicyclic coefficient theorem in an
arbitrary fixed shrinking field window. -/
theorem exists_complexFieldUnicyclic_coefficient_shrinking_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (U : ℝ) (_hU : 0 ≤ U) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ g : C(S, ℂ),
        ‖g‖ ≤ U * (k : ℝ) ^ (-(1 / 2 : ℝ)) →
        ‖((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
              (M.bjrModel.complexFieldConnectedWeight g k 1 /
                (k.factorial : ℂ))) /
              (unicyclicCoefficientMainTerm k : ℂ) - 1‖ ≤
          K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨s, K₀, N₀, hs, hK₀, hcoeff⟩ :=
    Field.exists_complexFieldUnicyclic_connectedWeight_uniform_bound M hM
  let K : ℝ := 4 * K₀
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hhalf : Tendsto
      (fun k : ℕ ↦ (k : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have hwindow : Tendsto
      (fun k : ℕ ↦ U * (k : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hhalf
  have hnear : ∀ᶠ k : ℕ in atTop,
      U * (k : ℝ) ^ (-(1 / 2 : ℝ)) < s :=
    hwindow.eventually (isOpen_Iio.mem_nhds hs)
  filter_upwards [eventually_ge_atTop (max N₀ 1), hnear]
    with k hk hknear
  intro g hg
  have hkN : N₀ ≤ k := (le_max_left N₀ 1).trans hk
  have hkone : 1 ≤ k := (le_max_right N₀ 1).trans hk
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hgs : g ∈ Metric.ball (0 : C(S, ℂ)) s := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hg.trans_lt hknear
  have habs := hcoeff g hgs k hkN
  let z : ℂ := (FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
    (M.bjrModel.complexFieldConnectedWeight g k 1 / (k.factorial : ℂ))
  let q : ℝ := unicyclicCoefficientMainTerm k
  have hq : 0 < q := by
    dsimp only [q, unicyclicCoefficientMainTerm]
    positivity
  have hkcomplex : (k : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hqcast : (q : ℂ) = (1 / 4 : ℂ) * (k : ℂ)⁻¹ := by
    dsimp only [q, unicyclicCoefficientMainTerm]
    push_cast
    field_simp [hkcomplex]
  have habs' :
      ‖z - (q : ℂ)‖ ≤ K₀ * (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [hqcast]
    simpa only [z] using habs
  have hrewrite : z / (q : ℂ) - 1 =
      (z - (q : ℂ)) / (q : ℂ) := by
    have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    field_simp [hqc]
  rw [hrewrite, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hq]
  have hpow :
      (k : ℝ) ^ (-(3 / 2 : ℝ)) * (k : ℝ) =
        (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      (k : ℝ) ^ (-(3 / 2 : ℝ)) * (k : ℝ) =
          (k : ℝ) ^ (-(3 / 2 : ℝ)) * (k : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (k : ℝ) ^ (-(3 / 2 : ℝ) + 1) := by
        rw [← Real.rpow_add hkreal]
      _ = (k : ℝ) ^ (-(1 / 2 : ℝ)) := by norm_num
  calc
    ‖z - (q : ℂ)‖ / q ≤
        (K₀ * (k : ℝ) ^ (-(3 / 2 : ℝ))) / q :=
      div_le_div_of_nonneg_right
        habs' hq.le
    _ = (4 * K₀) *
          ((k : ℝ) ^ (-(3 / 2 : ℝ)) * (k : ℝ)) := by
      dsimp only [q, unicyclicCoefficientMainTerm]
      field_simp [hkreal.ne']
    _ = K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [hpow]

/-- Field-uniform surplus-one Perron--Wright estimate after conversion from
EGF coefficients to labelled weights. -/
theorem exists_complexFieldUnicyclic_connectedWeight_perronWright_shrinking_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (U : ℝ) (hU : 0 ≤ U) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ g : C(S, ℂ),
        ‖g‖ ≤ U * (k : ℝ) ^ (-(1 / 2 : ℝ)) →
        ‖((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
              M.bjrModel.complexFieldConnectedWeight g k 1) /
              (unicyclicPerronWrightMainTerm k : ℂ) - 1‖ ≤
          K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K₀, hK₀, hcoeff⟩ :=
    exists_complexFieldUnicyclic_coefficient_shrinking_relative_bound
      M hM U hU
  let K : ℝ := 1 + 2 * K₀
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcoeff, eventually_ge_atTop 1] with k hk hkone
  intro g hg
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  let q : ℝ := unicyclicCoefficientMainTerm k
  let S₀ : ℝ := Transfer.factorialStirlingMainTerm k
  let P : ℝ := unicyclicPerronWrightMainTerm k
  let z : ℂ := (FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
    (M.bjrModel.complexFieldConnectedWeight g k 1 / (k.factorial : ℂ))
  let a : ℂ := z / (q : ℂ) - 1
  let b : ℝ := (k.factorial : ℝ) / S₀ - 1
  have hq : 0 < q := by
    dsimp only [q, unicyclicCoefficientMainTerm]
    positivity
  have hS₀ : 0 < S₀ := by
    dsimp only [S₀, Transfer.factorialStirlingMainTerm]
    positivity
  have hP : S₀ * q = P := by
    rfl
  have ha : ‖a‖ ≤ K₀ * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simpa only [a, z, q] using hk g hg
  have hb := Transfer.factorial_stirling_relative_error_bound k hkpos
  have hbhalf : |b| ≤ (1 / 6 : ℝ) *
      (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      |b| ≤ 1 / (6 * (k : ℝ)) := by
        simpa only [b, S₀] using hb
      _ = (1 / 6 : ℝ) * (k : ℝ)⁻¹ := by ring
      _ ≤ (1 / 6 : ℝ) * (k : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (rpow_neg_one_le_neg_half hkone) (by norm_num)
  have hbone : |b| ≤ 1 / 6 := by
    calc
      |b| ≤ 1 / (6 * (k : ℝ)) := by
        simpa only [b, S₀] using hb
      _ ≤ 1 / 6 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        have hkrealOne : (1 : ℝ) ≤ k := by exact_mod_cast hkone
        nlinarith
  have hdecomp :
      ((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
          M.bjrModel.complexFieldConnectedWeight g k 1) / (P : ℂ) - 1 =
        (b : ℂ) + a + (b : ℂ) * a := by
    have hfact : (k.factorial : ℂ) ≠ 0 := by
      exact_mod_cast k.factorial_ne_zero
    have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    have hSc : (S₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS₀.ne'
    have hPSc : (S₀ : ℂ) * (q : ℂ) = (P : ℂ) := by
      exact_mod_cast hP
    have hweight :
        (FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
            M.bjrModel.complexFieldConnectedWeight g k 1 =
          (k.factorial : ℂ) * z := by
      dsimp only [z]
      field_simp [hfact]
    have hfactRatio :
        (k.factorial : ℂ) / (S₀ : ℂ) = (b : ℂ) + 1 := by
      dsimp only [b]
      push_cast
      ring
    have hcoeffRatio : z / (q : ℂ) = a + 1 := by
      dsimp only [a]
      ring
    calc
      ((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
            M.bjrModel.complexFieldConnectedWeight g k 1) / (P : ℂ) - 1 =
          ((k.factorial : ℂ) * z) /
              ((S₀ : ℂ) * (q : ℂ)) - 1 := by
        rw [hweight, hPSc]
      _ = ((k.factorial : ℂ) / (S₀ : ℂ)) *
            (z / (q : ℂ)) - 1 := by
        field_simp [hSc, hqc]
      _ = ((b : ℂ) + 1) * (a + 1) - 1 := by
        rw [hfactRatio, hcoeffRatio]
      _ = (b : ℂ) + a + (b : ℂ) * a := by ring
  rw [hdecomp]
  calc
    ‖(b : ℂ) + a + (b : ℂ) * a‖ ≤
        ‖(b : ℂ)‖ + ‖a‖ + ‖(b : ℂ)‖ * ‖a‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (norm_mul_le _ _))
    _ ≤ (1 / 6 : ℝ) * (k : ℝ) ^ (-(1 / 2 : ℝ)) +
        K₀ * (k : ℝ) ^ (-(1 / 2 : ℝ)) +
        (1 / 6 : ℝ) *
          (K₀ * (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (add_le_add hbhalf ha)
        (mul_le_mul hbone ha (norm_nonneg _) (by norm_num))
    _ ≤ K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hpow : 0 ≤ (k : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg (Nat.cast_nonneg k) _
      dsimp only [K]
      nlinarith [mul_nonneg hK₀.le hpow]

/-- The surplus-one coefficient estimate is uniform on one fixed complex
field neighbourhood.  In contrast with the tree case, its leading
logarithmic coefficient is independent of the field. -/
theorem exists_complexFieldUnicyclic_coefficient_local_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ s K : ℝ, 0 < s ∧ 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        ‖((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
              (M.bjrModel.complexFieldConnectedWeight g k 1 /
                (k.factorial : ℂ))) /
              (unicyclicCoefficientMainTerm k : ℂ) - 1‖ ≤
          K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨s, K₀, N₀, hs, hK₀, hcoeff⟩ :=
    Field.exists_complexFieldUnicyclic_connectedWeight_uniform_bound M hM
  let K : ℝ := 4 * K₀
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨s, K, hs, hK, ?_⟩
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with k hk
  intro g hg
  have hkN : N₀ ≤ k := (le_max_left N₀ 1).trans hk
  have hkone : 1 ≤ k := (le_max_right N₀ 1).trans hk
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have habs := hcoeff g hg k hkN
  let z : ℂ := (FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
    (M.bjrModel.complexFieldConnectedWeight g k 1 / (k.factorial : ℂ))
  let q : ℝ := unicyclicCoefficientMainTerm k
  have hq : 0 < q := by
    dsimp only [q, unicyclicCoefficientMainTerm]
    positivity
  have hkcomplex : (k : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hqcast : (q : ℂ) = (1 / 4 : ℂ) * (k : ℂ)⁻¹ := by
    dsimp only [q, unicyclicCoefficientMainTerm]
    push_cast
    field_simp [hkcomplex]
  have habs' :
      ‖z - (q : ℂ)‖ ≤ K₀ * (k : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [hqcast]
    simpa only [z] using habs
  have hrewrite : z / (q : ℂ) - 1 =
      (z - (q : ℂ)) / (q : ℂ) := by
    have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    field_simp [hqc]
  rw [hrewrite, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hq]
  have hpow :
      (k : ℝ) ^ (-(3 / 2 : ℝ)) * (k : ℝ) =
        (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      (k : ℝ) ^ (-(3 / 2 : ℝ)) * (k : ℝ) =
          (k : ℝ) ^ (-(3 / 2 : ℝ)) * (k : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (k : ℝ) ^ (-(3 / 2 : ℝ) + 1) := by
        rw [← Real.rpow_add hkreal]
      _ = (k : ℝ) ^ (-(1 / 2 : ℝ)) := by norm_num
  calc
    ‖z - (q : ℂ)‖ / q ≤
        (K₀ * (k : ℝ) ^ (-(3 / 2 : ℝ))) / q :=
      div_le_div_of_nonneg_right habs' hq.le
    _ = (4 * K₀) *
          ((k : ℝ) ^ (-(3 / 2 : ℝ)) * (k : ℝ)) := by
      dsimp only [q, unicyclicCoefficientMainTerm]
      field_simp [hkreal.ne']
    _ = K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [hpow]

/-- Fixed-neighbourhood field-uniform surplus-one Perron--Wright estimate
after conversion from normalized EGF coefficients to labelled weights. -/
theorem exists_complexFieldUnicyclic_connectedWeight_perronWright_local_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ s K : ℝ, 0 < s ∧ 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ g ∈ Metric.ball (0 : C(S, ℂ)) s,
        ‖((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
              M.bjrModel.complexFieldConnectedWeight g k 1) /
              (unicyclicPerronWrightMainTerm k : ℂ) - 1‖ ≤
          K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨s, K₀, hs, hK₀, hcoeff⟩ :=
    exists_complexFieldUnicyclic_coefficient_local_relative_bound M hM
  let K : ℝ := 1 + 2 * K₀
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨s, K, hs, hK, ?_⟩
  filter_upwards [hcoeff, eventually_ge_atTop 1] with k hk hkone
  intro g hg
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  let q : ℝ := unicyclicCoefficientMainTerm k
  let S₀ : ℝ := Transfer.factorialStirlingMainTerm k
  let P : ℝ := unicyclicPerronWrightMainTerm k
  let z : ℂ := (FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
    (M.bjrModel.complexFieldConnectedWeight g k 1 / (k.factorial : ℂ))
  let a : ℂ := z / (q : ℂ) - 1
  let b : ℝ := (k.factorial : ℝ) / S₀ - 1
  have hq : 0 < q := by
    dsimp only [q, unicyclicCoefficientMainTerm]
    positivity
  have hS₀ : 0 < S₀ := by
    dsimp only [S₀, Transfer.factorialStirlingMainTerm]
    positivity
  have hP : S₀ * q = P := by rfl
  have ha : ‖a‖ ≤ K₀ * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simpa only [a, z, q] using hk g hg
  have hb := Transfer.factorial_stirling_relative_error_bound k hkpos
  have hbhalf : |b| ≤ (1 / 6 : ℝ) *
      (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      |b| ≤ 1 / (6 * (k : ℝ)) := by
        simpa only [b, S₀] using hb
      _ = (1 / 6 : ℝ) * (k : ℝ)⁻¹ := by ring
      _ ≤ (1 / 6 : ℝ) * (k : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (rpow_neg_one_le_neg_half hkone) (by norm_num)
  have hbone : |b| ≤ 1 / 6 := by
    calc
      |b| ≤ 1 / (6 * (k : ℝ)) := by
        simpa only [b, S₀] using hb
      _ ≤ 1 / 6 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        have hkrealOne : (1 : ℝ) ≤ k := by exact_mod_cast hkone
        nlinarith
  have hdecomp :
      ((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
          M.bjrModel.complexFieldConnectedWeight g k 1) / (P : ℂ) - 1 =
        (b : ℂ) + a + (b : ℂ) * a := by
    have hfact : (k.factorial : ℂ) ≠ 0 := by
      exact_mod_cast k.factorial_ne_zero
    have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
    have hSc : (S₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS₀.ne'
    have hPSc : (S₀ : ℂ) * (q : ℂ) = (P : ℂ) := by
      exact_mod_cast hP
    have hweight :
        (FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
            M.bjrModel.complexFieldConnectedWeight g k 1 =
          (k.factorial : ℂ) * z := by
      dsimp only [z]
      field_simp [hfact]
    have hfactRatio :
        (k.factorial : ℂ) / (S₀ : ℂ) = (b : ℂ) + 1 := by
      dsimp only [b]
      push_cast
      ring
    have hcoeffRatio : z / (q : ℂ) = a + 1 := by
      dsimp only [a]
      ring
    calc
      ((FiniteIrreducibleRadiusResponse.radius M hM g) ^ k *
            M.bjrModel.complexFieldConnectedWeight g k 1) / (P : ℂ) - 1 =
          ((k.factorial : ℂ) * z) /
              ((S₀ : ℂ) * (q : ℂ)) - 1 := by
        rw [hweight, hPSc]
      _ = ((k.factorial : ℂ) / (S₀ : ℂ)) *
            (z / (q : ℂ)) - 1 := by
        field_simp [hSc, hqc]
      _ = ((b : ℂ) + 1) * (a + 1) - 1 := by
        rw [hfactRatio, hcoeffRatio]
      _ = (b : ℂ) + a + (b : ℂ) * a := by ring
  rw [hdecomp]
  calc
    ‖(b : ℂ) + a + (b : ℂ) * a‖ ≤
        ‖(b : ℂ)‖ + ‖a‖ + ‖(b : ℂ)‖ * ‖a‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) (norm_mul_le _ _))
    _ ≤ (1 / 6 : ℝ) * (k : ℝ) ^ (-(1 / 2 : ℝ)) +
        K₀ * (k : ℝ) ^ (-(1 / 2 : ℝ)) +
        (1 / 6 : ℝ) *
          (K₀ * (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (add_le_add hbhalf ha)
        (mul_le_mul hbone ha (norm_nonneg _) (by norm_num))
    _ ≤ K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hpow : 0 ≤ (k : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_nonneg (Nat.cast_nonneg k) _
      dsimp only [K]
      nlinarith [mul_nonneg hK₀.le hpow]

/-- At surplus one the scalar-field bridge has no residual power of `t`:
the literal paper weight is exactly the complex-field weight. -/
theorem complexFieldConnectedWeight_scalar_unicyclic
    (M : FiniteIrreducibleModel S) (t : ℝ) (ht : 0 < t) (k : ℕ) :
    M.bjrModel.complexFieldConnectedWeight
        (ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)) k 1 =
      (M.bjrModel.connectedWeight t k 1 : ℂ) := by
  have h := ScalarFieldResponse.connectedWeight_scalarFieldComplex M.bjrModel t ht k 1
  norm_num at h
  exact h.symm

/-- The literal radius-dependent main term
`w₁ rho(t)^(-k) e^(-k) k^(k-1/2)`. -/
def physicalUnicyclicRadiusMainTerm
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (k : ℕ) (t : ℝ) : ℝ :=
  (Tree.physicalTreeRadius M hM t)⁻¹ ^ k *
    unicyclicPerronWrightMainTerm k

/-- Literal closed form of the radius-dependent main term. -/
theorem physicalUnicyclicRadiusMainTerm_eq_exp_rpow
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {k : ℕ} (hk : 0 < k) (t : ℝ) :
    physicalUnicyclicRadiusMainTerm M hM k t =
      unicyclicWrightConstant *
        (Tree.physicalTreeRadius M hM t)⁻¹ ^ k *
          Real.exp (-(k : ℝ)) *
            (k : ℝ) ^ ((k : ℝ) - 1 / 2) := by
  unfold physicalUnicyclicRadiusMainTerm
  rw [unicyclicPerronWrightMainTerm_eq_exp_rpow hk]
  ring

/-- The Gaussian critical-window version of the surplus-one main term. -/
def physicalUnicyclicGaussianMainTerm
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (k : ℕ) (t : ℝ) : ℝ :=
  unicyclicPerronWrightMainTerm k *
    Real.exp (-Radius.criticalQuadraticRate M hM * (k : ℝ) *
      (t - 1) ^ 2)

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
/-- Literal closed form of the Gaussian critical-window main term. -/
theorem physicalUnicyclicGaussianMainTerm_eq_exp_rpow
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {k : ℕ} (hk : 0 < k) (t : ℝ) :
    physicalUnicyclicGaussianMainTerm M hM k t =
      unicyclicWrightConstant * Real.exp (-(k : ℝ)) *
        Real.exp (-Radius.criticalQuadraticRate M hM * (k : ℝ) *
          (t - 1) ^ 2) *
            (k : ℝ) ^ ((k : ℝ) - 1 / 2) := by
  unfold physicalUnicyclicGaussianMainTerm
  rw [unicyclicPerronWrightMainTerm_eq_exp_rpow hk]
  ring

/-- Radius form of the surplus-one Perron--Wright estimate on an arbitrary
nonnegative window `eta k → 0`. -/
theorem exists_unicyclicPerronWright_radius_relative_bound_uniform_eta
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (nhds 0) →
      ∀ᶠ k : ℕ in atTop, ∀ t : ℝ,
        |t - 1| ≤ eta k →
        |M.bjrModel.connectedWeight t k 1 /
            physicalUnicyclicRadiusMainTerm M hM k t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨Bfield, hBfield, hfieldLocal⟩ :=
    exists_scalarFieldComplex_real_lipschitz M
  obtain ⟨s, K, hs, hK, hfield⟩ :=
    exists_complexFieldUnicyclic_connectedWeight_perronWright_local_relative_bound
      M hM
  refine ⟨K, hK, ?_⟩
  intro eta hetaNonneg heta
  have hfieldWindowTendsto : Tendsto (fun k : ℕ ↦ Bfield * eta k)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul heta
  have hfieldSmall : ∀ᶠ k : ℕ in atTop, Bfield * eta k < s :=
    hfieldWindowTendsto.eventually (isOpen_Iio.mem_nhds hs)
  have hhalf : ∀ᶠ t : ℝ in nhds 1, (1 / 2 : ℝ) < t :=
    Ioi_mem_nhds (by norm_num)
  have hlocal : ∀ᶠ t : ℝ in nhds 1,
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
          Bfield * |t - 1| ∧
        ((FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).im = 0 ∧
          0 < (FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).re) ∧
        (1 / 2 : ℝ) < t :=
    hfieldLocal.and
      ((FiniteIrreducibleScalarFieldResponse.scalarRadius_real_positive_near_one M hM).and
        hhalf)
  have hlocalWindow :=
    eventually_shrinking_window_mem_nhds eta heta hlocal
  filter_upwards [hfield, hfieldSmall, hlocalWindow, eventually_ge_atTop 1]
    with k hkfield hkfieldSmall hklocal hkone
  intro t hwindow
  obtain ⟨hgLocal, hrhoLocal, htHalf⟩ := hklocal t hwindow
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  let x : ℝ := (k : ℝ) ^ (-(1 / 2 : ℝ))
  have hx : 0 ≤ x := by
    dsimp only [x]
    exact Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hgEta :
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
        Bfield * eta k := by
    calc
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
          Bfield * |t - 1| := hgLocal
      _ ≤ Bfield * eta k :=
        mul_le_mul_of_nonneg_left hwindow hBfield.le
  have hg : ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ) ∈
      Metric.ball (0 : C(S, ℂ)) s := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hgEta.trans_lt hkfieldSmall
  have hfieldBound := hkfield
    (ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)) hg
  let rho : ℝ := Tree.physicalTreeRadius M hM t
  let P : ℝ := unicyclicPerronWrightMainTerm k
  have hrho : 0 < rho := hrhoLocal.2
  have ht : 0 < t := lt_trans (by norm_num) htHalf
  have hP : 0 < P := by
    dsimp only [P, unicyclicPerronWrightMainTerm,
      Transfer.factorialStirlingMainTerm, unicyclicCoefficientMainTerm]
    positivity
  have hrhoEq :
      FiniteIrreducibleRadiusResponse.radius M hM
          (ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)) =
        (rho : ℂ) := by
    change FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ) =
      ((FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).re : ℂ)
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hrhoLocal.1
  have hweight := complexFieldConnectedWeight_scalar_unicyclic M t ht k
  have hfieldReal :
      |rho ^ k * M.bjrModel.connectedWeight t k 1 / P - 1| ≤ K * x := by
    rw [hrhoEq, hweight] at hfieldBound
    have hfieldCast :
        (rho : ℂ) ^ k * (M.bjrModel.connectedWeight t k 1 : ℂ) / (P : ℂ) - 1 =
          ((rho ^ k * M.bjrModel.connectedWeight t k 1 / P - 1 : ℝ) : ℂ) := by
      norm_cast
    rw [hfieldCast, Complex.norm_real, Real.norm_eq_abs] at hfieldBound
    simpa only [x] using hfieldBound
  have hfactor :
      M.bjrModel.connectedWeight t k 1 /
          physicalUnicyclicRadiusMainTerm M hM k t =
        rho ^ k * M.bjrModel.connectedWeight t k 1 / P := by
    dsimp only [physicalUnicyclicRadiusMainTerm, rho, P]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]
    ring
  rw [hfactor]
  calc
    |rho ^ k * M.bjrModel.connectedWeight t k 1 / P - 1| ≤ K * x :=
      hfieldReal
    _ ≤ K * (eta k + x) := by
      exact mul_le_mul_of_nonneg_left
        (by linarith [hetaNonneg k]) hK.le

/-- Compatibility form with a prescribed shrinking window. -/
theorem exists_unicyclicPerronWright_radius_relative_bound_of_tendsto
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (eta : ℕ → ℝ) (hetaNonneg : ∀ k, 0 ≤ eta k)
    (heta : Tendsto eta atTop (nhds 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ,
        |t - 1| ≤ eta k →
        |M.bjrModel.connectedWeight t k 1 /
            physicalUnicyclicRadiusMainTerm M hM k t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, huniform⟩ :=
    exists_unicyclicPerronWright_radius_relative_bound_uniform_eta M hM
  exact ⟨K, hK, huniform eta hetaNonneg heta⟩

/-- Physical surplus-one Perron--Wright formula with the genuine critical
radius left in the main term. -/
theorem exists_unicyclicPerronWright_radius_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ,
        Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        |M.bjrModel.connectedWeight t k 1 /
            physicalUnicyclicRadiusMainTerm M hM k t - 1| ≤
          K / Real.sqrt (k : ℝ) := by
  obtain ⟨Bfield, hBfield, hfieldLocal⟩ :=
    exists_scalarFieldComplex_real_lipschitz M
  let Ufield : ℝ := Bfield * L
  have hUfield : 0 ≤ Ufield := mul_nonneg hBfield.le hL
  obtain ⟨K, hK, hfield⟩ :=
    exists_complexFieldUnicyclic_connectedWeight_perronWright_shrinking_relative_bound
      M hM Ufield hUfield
  refine ⟨K, hK, ?_⟩
  have hhalf : ∀ᶠ t : ℝ in nhds 1, (1 / 2 : ℝ) < t :=
    Ioi_mem_nhds (by norm_num)
  have hlocal : ∀ᶠ t : ℝ in nhds 1,
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
          Bfield * |t - 1| ∧
        ((FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).im = 0 ∧
          0 < (FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).re) ∧
        (1 / 2 : ℝ) < t :=
    hfieldLocal.and
      ((FiniteIrreducibleScalarFieldResponse.scalarRadius_real_positive_near_one M hM).and
        hhalf)
  have hlocalWindow := eventually_sqrt_window_mem_nhds L hlocal
  filter_upwards [hfield, hlocalWindow, eventually_ge_atTop 1]
    with k hkfield hklocal hkone
  intro t hwindow
  obtain ⟨hgLocal, hrhoLocal, htHalf⟩ := hklocal t hwindow
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hspos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  let x : ℝ := (k : ℝ) ^ (-(1 / 2 : ℝ))
  have hxSqrt : x = (Real.sqrt (k : ℝ))⁻¹ :=
    rpow_neg_half_eq_inv_sqrt hkpos
  have hy : |t - 1| ≤ L * x := by
    have hdiv := (le_div_iff₀ hspos).2 (by
      simpa only [mul_comm] using hwindow)
    rw [div_eq_mul_inv, ← hxSqrt] at hdiv
    exact hdiv
  have hg :
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
        Ufield * x := by
    calc
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
          Bfield * |t - 1| := hgLocal
      _ ≤ Bfield * (L * x) :=
        mul_le_mul_of_nonneg_left hy hBfield.le
      _ = Ufield * x := by dsimp only [Ufield]; ring
  have hfieldBound := hkfield
    (ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)) hg
  let rho : ℝ := Tree.physicalTreeRadius M hM t
  let P : ℝ := unicyclicPerronWrightMainTerm k
  have hrho : 0 < rho := hrhoLocal.2
  have ht : 0 < t := lt_trans (by norm_num) htHalf
  have hP : 0 < P := by
    dsimp only [P, unicyclicPerronWrightMainTerm,
      Transfer.factorialStirlingMainTerm, unicyclicCoefficientMainTerm]
    positivity
  have hrhoEq :
      FiniteIrreducibleRadiusResponse.radius M hM
          (ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)) =
        (rho : ℂ) := by
    change FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ) =
      ((FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).re : ℂ)
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hrhoLocal.1
  have hweight := complexFieldConnectedWeight_scalar_unicyclic M t ht k
  have hfieldReal :
      |rho ^ k * M.bjrModel.connectedWeight t k 1 / P - 1| ≤ K * x := by
    rw [hrhoEq, hweight] at hfieldBound
    have hfieldCast :
        (rho : ℂ) ^ k * (M.bjrModel.connectedWeight t k 1 : ℂ) / (P : ℂ) - 1 =
          ((rho ^ k * M.bjrModel.connectedWeight t k 1 / P - 1 : ℝ) : ℂ) := by
      norm_cast
    rw [hfieldCast, Complex.norm_real, Real.norm_eq_abs] at hfieldBound
    simpa only [x] using hfieldBound
  have hfactor :
      M.bjrModel.connectedWeight t k 1 /
          physicalUnicyclicRadiusMainTerm M hM k t =
        rho ^ k * M.bjrModel.connectedWeight t k 1 / P := by
    dsimp only [physicalUnicyclicRadiusMainTerm, rho, P]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]
    ring
  rw [hfactor]
  simpa only [hxSqrt, div_eq_mul_inv] using hfieldReal

/-- Gaussian critical-window form of the physical surplus-one formula. -/
theorem exists_unicyclicPerronWright_gaussian_relative_bound
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ,
        Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        |M.bjrModel.connectedWeight t k 1 /
            physicalUnicyclicGaussianMainTerm M hM k t - 1| ≤
          K / Real.sqrt (k : ℝ) := by
  obtain ⟨Bfield, hBfield, hfieldLocal⟩ :=
    exists_scalarFieldComplex_real_lipschitz M
  let Ufield : ℝ := Bfield * L
  have hUfield : 0 ≤ Ufield := mul_nonneg hBfield.le hL
  obtain ⟨Kfield, hKfield, hfield⟩ :=
    exists_complexFieldUnicyclic_connectedWeight_perronWright_shrinking_relative_bound
      M hM Ufield hUfield
  obtain ⟨Kradius, hKradius, hradius⟩ :=
    Radius.exists_criticalWindowRadius_relative_bound M hM L hL
  let K : ℝ := Kradius * (1 + Kfield) + Kfield
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hhalf : ∀ᶠ t : ℝ in nhds 1, (1 / 2 : ℝ) < t :=
    Ioi_mem_nhds (by norm_num)
  have hlocal : ∀ᶠ t : ℝ in nhds 1,
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
          Bfield * |t - 1| ∧
        ((FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).im = 0 ∧
          0 < (FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).re) ∧
        (1 / 2 : ℝ) < t :=
    hfieldLocal.and
      ((FiniteIrreducibleScalarFieldResponse.scalarRadius_real_positive_near_one M hM).and
        hhalf)
  have hlocalWindow := eventually_sqrt_window_mem_nhds L hlocal
  filter_upwards [hfield, hradius, hlocalWindow, eventually_ge_atTop 1]
    with k hkfield hkradius hklocal hkone
  intro t hwindow
  obtain ⟨hgLocal, hrhoLocal, htHalf⟩ := hklocal t hwindow
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hspos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  let x : ℝ := (k : ℝ) ^ (-(1 / 2 : ℝ))
  have hx : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hxone : x ≤ 1 := by
    dsimp only [x]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hkone) (by norm_num)
  have hxSqrt : x = (Real.sqrt (k : ℝ))⁻¹ :=
    rpow_neg_half_eq_inv_sqrt hkpos
  have hy : |t - 1| ≤ L * x := by
    have hdiv := (le_div_iff₀ hspos).2 (by
      simpa only [mul_comm] using hwindow)
    rw [div_eq_mul_inv, ← hxSqrt] at hdiv
    exact hdiv
  have hg :
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
        Ufield * x := by
    calc
      ‖ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)‖ ≤
          Bfield * |t - 1| := hgLocal
      _ ≤ Bfield * (L * x) :=
        mul_le_mul_of_nonneg_left hy hBfield.le
      _ = Ufield * x := by dsimp only [Ufield]; ring
  have hfieldBound := hkfield
    (ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)) hg
  have hradiusBound := hkradius t hwindow
  let rho : ℝ := Tree.physicalTreeRadius M hM t
  let P : ℝ := unicyclicPerronWrightMainTerm k
  let G : ℝ := Real.exp
    (-Radius.criticalQuadraticRate M hM * (k : ℝ) * (t - 1) ^ 2)
  have hrho : 0 < rho := hrhoLocal.2
  have ht : 0 < t := lt_trans (by norm_num) htHalf
  have hP : 0 < P := by
    dsimp only [P, unicyclicPerronWrightMainTerm,
      Transfer.factorialStirlingMainTerm, unicyclicCoefficientMainTerm]
    positivity
  have hG : 0 < G := by dsimp only [G]; positivity
  have hrhoEq :
      FiniteIrreducibleRadiusResponse.radius M hM
          (ScalarFieldResponse.scalarFieldComplex M.bjrModel (t : ℂ)) =
        (rho : ℂ) := by
    change FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ) =
      ((FiniteIrreducibleScalarFieldResponse.scalarRadius M hM (t : ℂ)).re : ℂ)
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hrhoLocal.1
  have hweight := complexFieldConnectedWeight_scalar_unicyclic M t ht k
  have hfieldReal :
      |rho ^ k * M.bjrModel.connectedWeight t k 1 / P - 1| ≤ Kfield * x := by
    rw [hrhoEq, hweight] at hfieldBound
    have hfieldCast :
        (rho : ℂ) ^ k * (M.bjrModel.connectedWeight t k 1 : ℂ) / (P : ℂ) - 1 =
          ((rho ^ k * M.bjrModel.connectedWeight t k 1 / P - 1 : ℝ) : ℂ) := by
      norm_cast
    rw [hfieldCast, Complex.norm_real, Real.norm_eq_abs] at hfieldBound
    simpa only [x] using hfieldBound
  have hradiusReal : |rho⁻¹ ^ k / G - 1| ≤ Kradius * x := by
    simpa only [rho, G, Tree.physicalTreeRadius, div_eq_mul_inv,
      hxSqrt, mul_assoc] using hradiusBound
  have hfactor :
      M.bjrModel.connectedWeight t k 1 /
          physicalUnicyclicGaussianMainTerm M hM k t =
        (rho⁻¹ ^ k / G) *
          (rho ^ k * M.bjrModel.connectedWeight t k 1 / P) := by
    have hrhone : rho ≠ 0 := hrho.ne'
    have hPne : P ≠ 0 := hP.ne'
    have hGne : G ≠ 0 := hG.ne'
    dsimp only [physicalUnicyclicGaussianMainTerm, P, G]
    field_simp [hrhone, hPne, hGne]
    have hcancel : rho⁻¹ ^ k * rho ^ k = 1 := by
      rw [← mul_pow]
      field_simp [hrhone]
      simp
    calc
      M.bjrModel.connectedWeight t k 1 / P =
          (rho⁻¹ ^ k * rho ^ k) *
            (M.bjrModel.connectedWeight t k 1 / P) := by rw [hcancel]; ring
      _ = M.bjrModel.connectedWeight t k 1 * (1 / rho) ^ k * rho ^ k / P := by
        simp only [one_div]
        ring
  rw [hfactor]
  have htwo := abs_two_factor_sub_one_le hx hxone
    hKradius.le hKfield.le hradiusReal hfieldReal
  simpa only [K, hxSqrt, div_eq_mul_inv] using htwo

/-- The same radius-dependent formula with the paper's window written as
`|t-1| <= L k^(-1/2)`. -/
theorem exists_unicyclicPerronWright_radius_relative_bound_rpow_window
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ,
        |t - 1| ≤ L * (k : ℝ) ^ (-(1 / 2 : ℝ)) →
        |M.bjrModel.connectedWeight t k 1 /
            physicalUnicyclicRadiusMainTerm M hM k t - 1| ≤
          K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K, hK, hmain⟩ :=
    exists_unicyclicPerronWright_radius_relative_bound M hM L hL
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop 1] with k hk hkone
  intro t ht
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hspos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have hx := rpow_neg_half_eq_inv_sqrt (k := k) hkpos
  have hwindow : Real.sqrt (k : ℝ) * |t - 1| ≤ L := by
    calc
      Real.sqrt (k : ℝ) * |t - 1| ≤
          Real.sqrt (k : ℝ) *
            (L * (k : ℝ) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left ht hspos.le
      _ = L := by
        rw [hx]
        field_simp [hspos.ne']
  have hbound := hk t hwindow
  calc
    |M.bjrModel.connectedWeight t k 1 /
          physicalUnicyclicRadiusMainTerm M hM k t - 1| ≤
        K / Real.sqrt (k : ℝ) := hbound
    _ = K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← hx]

/-- The Gaussian formula with the paper's window written literally as
`|t-1| <= L k^(-1/2)`. -/
theorem exists_unicyclicPerronWright_gaussian_relative_bound_rpow_window
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ,
        |t - 1| ≤ L * (k : ℝ) ^ (-(1 / 2 : ℝ)) →
        |M.bjrModel.connectedWeight t k 1 /
            physicalUnicyclicGaussianMainTerm M hM k t - 1| ≤
          K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K, hK, hmain⟩ :=
    exists_unicyclicPerronWright_gaussian_relative_bound M hM L hL
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop 1] with k hk hkone
  intro t ht
  have hkpos : 0 < k := Nat.zero_lt_one.trans_le hkone
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hspos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkreal
  have hx := rpow_neg_half_eq_inv_sqrt (k := k) hkpos
  have hwindow : Real.sqrt (k : ℝ) * |t - 1| ≤ L := by
    calc
      Real.sqrt (k : ℝ) * |t - 1| ≤
          Real.sqrt (k : ℝ) *
            (L * (k : ℝ) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left ht hspos.le
      _ = L := by
        rw [hx]
        field_simp [hspos.ne']
  have hbound := hk t hwindow
  calc
    |M.bjrModel.connectedWeight t k 1 /
          physicalUnicyclicGaussianMainTerm M hM k t - 1| ≤
        K / Real.sqrt (k : ℝ) := hbound
    _ = K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← hx]

end PerronWright.FiniteIrreducibleUnicyclicPerronWrightFormula
