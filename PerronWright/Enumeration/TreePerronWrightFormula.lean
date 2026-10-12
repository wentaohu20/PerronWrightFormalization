import PerronWright.Enumeration.FieldTreeConnectedWeightAsymptotic
import PerronWright.Enumeration.ScalarFieldRootedTreeRadius
import PerronWright.Analysis.CriticalWindowRadiusConversion
import PerronWright.Analysis.ScalarFieldBridge

/-!
# The physical scalar Perron--Wright tree formula

The literal quantity `CompactBJRModel.connectedWeight t k 0` is the paper's
`C_t(k,0)`.  This file specializes the complex-field tree theorem to

`g_t = (log t) 1 - (t-1) d`,

identifies the analytic critical activity with the genuine rooted-tree
radius, and combines its cubic logarithmic expansion with the uniform field
coefficient estimate.  For each fixed window width `L`, all constants and
eventual thresholds are common to every real `t` satisfying
`sqrt(k) * |t-1| <= L`.
-/

open Filter Topology Set Asymptotics MeasureTheory
open scoped Classical Topology ENNReal NNReal Real Nat

noncomputable section

namespace PerronWright.TreePerronWrightFormula

namespace Field

export PerronWright.FieldTreeConnectedWeightAsymptotic
  (fieldTreePerronWrightMainTerm
    exists_complexFieldConnectedWeight_perronWright_shrinking_relative_bound
    exists_complexFieldConnectedWeight_perronWright_local_relative_bound)

end Field

namespace Radius

export PerronWright.CriticalWindowRadiusConversion
  (realScalarRadius criticalQuadraticRate
    exists_real_logScalarRadius_cubic_bound
    exists_criticalWindowRadius_relative_bound)

end Radius

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The physical critical radius `rho(t)`. -/
def physicalTreeRadius (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (t : ℝ) : ℝ :=
  Radius.realScalarRadius M hM t

/-- The radius form of the tree Perron--Wright main term.  The residual
factor `t⁻¹ = 1 + O(|t-1|)` is deliberately left in the relative error, as
in the statement of the paper. -/
def physicalTreeRadiusMainTerm (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (k : ℕ) (t : ℝ) : ℝ :=
  (physicalTreeRadius M hM t)⁻¹ ^ k *
    Field.fieldTreePerronWrightMainTerm M hM k

/-- Literal paper form of the radius-dependent tree main term. -/
theorem physicalTreeRadiusMainTerm_eq_exp_rpow
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {k : ℕ} (hk : 0 < k) (t : ℝ) :
    physicalTreeRadiusMainTerm M hM k t =
      (M.beta hM) ^ (-(1 / 2 : ℝ)) *
        (physicalTreeRadius M hM t)⁻¹ ^ k *
          Real.exp (-(k : ℝ)) *
            (k : ℝ) ^ ((k : ℝ) - 2) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hbase :
      ((k : ℝ) / Real.exp 1) ^ k =
        Real.exp (-(k : ℝ)) * (k : ℝ) ^ k := by
    rw [div_pow, Real.exp_one_pow, Real.exp_neg]
    ring
  have hrpow :
      (k : ℝ) ^ (-(2 : ℝ)) * (k : ℝ) ^ (k : ℝ) =
        (k : ℝ) ^ ((k : ℝ) - 2) := by
    rw [← Real.rpow_add hkreal]
    congr 1
    ring
  unfold physicalTreeRadiusMainTerm
    PerronWright.FieldTreeConnectedWeightAsymptotic.fieldTreePerronWrightMainTerm
  rw [hbase]
  calc
    (physicalTreeRadius M hM t)⁻¹ ^ k *
          ((M.beta hM) ^ (-(1 / 2 : ℝ)) *
            (k : ℝ) ^ (-(2 : ℝ)) *
              (Real.exp (-(k : ℝ)) * (k : ℝ) ^ k)) =
        (M.beta hM) ^ (-(1 / 2 : ℝ)) *
          (physicalTreeRadius M hM t)⁻¹ ^ k *
            Real.exp (-(k : ℝ)) *
              ((k : ℝ) ^ (-(2 : ℝ)) * (k : ℝ) ^ (k : ℝ)) := by
      rw [Real.rpow_natCast]
      ring
    _ = (M.beta hM) ^ (-(1 / 2 : ℝ)) *
          (physicalTreeRadius M hM t)⁻¹ ^ k *
            Real.exp (-(k : ℝ)) *
              (k : ℝ) ^ ((k : ℝ) - 2) := by
      rw [hrpow]

/-- The Gaussian Perron--Wright main term for trees. -/
def physicalTreeGaussianMainTerm (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (k : ℕ) (t : ℝ) : ℝ :=
  Field.fieldTreePerronWrightMainTerm M hM k *
    Real.exp (-Radius.criticalQuadraticRate M hM * (k : ℝ) * (t - 1) ^ 2)

/-- The real scalar field is the real form of the analytic complex field. -/
theorem scalarFieldComplex_eq_complexifyField
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t) :
    ScalarFieldResponse.scalarFieldComplex M (t : ℂ) =
      CompactBJRModel.complexifyField (M.scalarField t) :=
  ScalarFieldResponse.scalarFieldComplex_ofReal M t ht

/-- At surplus zero, the literal paper weight and the complex field weight
differ by exactly one scalar factor `t`. -/
theorem complexFieldConnectedWeight_scalar_tree
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 < t) (k : ℕ) :
    M.complexFieldConnectedWeight
        (ScalarFieldResponse.scalarFieldComplex M (t : ℂ)) k 0 =
      (t : ℂ) * (M.connectedWeight t k 0 : ℂ) := by
  have h := ScalarFieldResponse.connectedWeight_scalarFieldComplex
    M t ht k 0
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  norm_num [zpow_neg_one] at h
  calc
    M.complexFieldConnectedWeight
        (ScalarFieldResponse.scalarFieldComplex M (t : ℂ)) k 0 =
        (t : ℂ) * ((t : ℂ)⁻¹ *
          M.complexFieldConnectedWeight
            (ScalarFieldResponse.scalarFieldComplex M (t : ℂ)) k 0) := by
      field_simp [htC]
    _ = (t : ℂ) * (M.connectedWeight t k 0 : ℂ) := by
      rw [← h]

private theorem rpow_neg_half_eq_inv_sqrt {k : ℕ} (hk : 0 < k) :
    (k : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (k : ℝ))⁻¹ := by
  have hkreal : (0 : ℝ) ≤ k := by exact_mod_cast hk.le
  rw [Real.rpow_neg hkreal, ← Real.sqrt_eq_rpow]

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
  have htball : t ∈ Metric.ball (1 : ℝ) delta := by
    rw [Metric.mem_ball, Real.dist_eq]
    calc
      |t - 1| ≤ L / Real.sqrt (k : ℝ) := hy
      _ ≤ (L + 1) / Real.sqrt (k : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hspos.le
      _ = (L + 1) * (Real.sqrt (k : ℝ))⁻¹ := by
        rw [div_eq_mul_inv]
      _ < delta := hknear
  exact hball htball

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
          ScalarFieldResponse.scalarFieldComplex M 1‖ := by rw [hbase, sub_zero]
    _ ≤ B₀ * ‖(t : ℂ) - 1‖ := ht
    _ ≤ B * ‖(t : ℂ) - 1‖ :=
      mul_le_mul_of_nonneg_right (le_max_left B₀ 1) (norm_nonneg _)
    _ = B * |t - 1| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]

/-- The analytic scalar critical activity is the genuine convergence radius
of the rooted-tree series, specialized to the physical real field. -/
theorem exists_physicalTreeRadius_eq_rootedTreeFMS_radius
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, |t - 1| < delta →
      (FieldRootedTree.fms M
          (ScalarFieldResponse.scalarFieldComplex M (t : ℂ))).radius =
        ‖(physicalTreeRadius M hM t : ℂ)‖ₑ := by
  obtain ⟨epsilon, hepsilon, hRadius⟩ :=
    FieldRootedTree.fms_radius_eq_critical_radius_eventually M hM
  have hg : Tendsto
      (fun t : ℝ ↦ ScalarFieldResponse.scalarFieldComplex M (t : ℂ))
      (nhds 1) (nhds 0) := by
    have hc :=
      (ScalarFieldResponse.scalarFieldComplex_analyticAt_one M).continuousAt
    change Tendsto (ScalarFieldResponse.scalarFieldComplex M)
      (nhds (1 : ℂ))
      (nhds (ScalarFieldResponse.scalarFieldComplex M 1)) at hc
    rw [ScalarFieldResponse.scalarFieldComplex_one] at hc
    exact hc.comp Complex.continuous_ofReal.continuousAt
  have hfield : ∀ᶠ t : ℝ in nhds 1,
      ScalarFieldResponse.scalarFieldComplex M (t : ℂ) ∈
        Metric.ball (0 : C(S, ℂ)) epsilon :=
    hg.eventually (Metric.ball_mem_nhds 0 hepsilon)
  have hlocal := hfield.and
    (ScalarFieldResponse.scalarCriticalRadius_real_positive_near_one M hM)
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨delta, hdelta, ?_⟩
  intro t ht
  have htball : t ∈ Metric.ball (1 : ℝ) delta := by
    simpa only [Metric.mem_ball, Real.dist_eq] using ht
  obtain ⟨hgt, hrho⟩ := hball htball
  have hrhoEq :
      RadiusResponse.radius M hM
          (ScalarFieldResponse.scalarFieldComplex M (t : ℂ)) =
        (physicalTreeRadius M hM t : ℂ) := by
    change ScalarRadiusSecond.scalarRadius M hM (t : ℂ) =
      ((ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).re : ℂ)
    apply Complex.ext
    · simp
    · have him :
          (ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).im = 0 := by
        change
          (RadiusResponse.radius M hM
            (ScalarFieldResponse.scalarFieldComplex M (t : ℂ))).im = 0
        exact hrho.1
      simpa only [Complex.ofReal_im] using him
  rw [hRadius _ hgt, hrhoEq]

/-- The cubic logarithmic expansion of the genuine physical radius. -/
theorem exists_physicalTreeRadius_log_cubic_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ t : ℝ, |t - 1| < delta →
        0 < physicalTreeRadius M hM t ∧
        |Real.log (physicalTreeRadius M hM t) -
            M.alpha hM ^ 2 / (2 * M.beta hM) * (t - 1) ^ 2| ≤
          C * |t - 1| ^ 3 := by
  simpa only [physicalTreeRadius,
    Radius.criticalQuadraticRate] using
      Radius.exists_real_logScalarRadius_cubic_bound M hM

private theorem abs_three_factor_sub_one_le
    {a b c x A B C : ℝ}
    (hx : 0 ≤ x) (hxone : x ≤ 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : |a - 1| ≤ A * x)
    (hb : |b - 1| ≤ B * x)
    (hc : |c - 1| ≤ C * x) :
    |a * b * c - 1| ≤
      (A * (1 + B) * (1 + C) + B * (1 + C) + C) * x := by
  have hBx : B * x ≤ B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hxone hB
  have hCx : C * x ≤ C := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hxone hC
  have hbabs : |b| ≤ 1 + B := by
    calc
      |b| = |(b - 1) + 1| := by
        congr 1
        ring
      _ ≤ |b - 1| + 1 := by simpa using abs_add_le (b - 1) 1
      _ ≤ B * x + 1 := by linarith
      _ ≤ 1 + B := by linarith
  have hcabs : |c| ≤ 1 + C := by
    calc
      |c| = |(c - 1) + 1| := by
        congr 1
        ring
      _ ≤ |c - 1| + 1 := by simpa using abs_add_le (c - 1) 1
      _ ≤ C * x + 1 := by linarith
      _ ≤ 1 + C := by linarith
  have hdecomp :
      a * b * c - 1 = (a - 1) * b * c + (b - 1) * c + (c - 1) := by ring
  rw [hdecomp]
  calc
    |(a - 1) * b * c + (b - 1) * c + (c - 1)| ≤
        |a - 1| * |b| * |c| + |b - 1| * |c| + |c - 1| := by
      calc
        |(a - 1) * b * c + (b - 1) * c + (c - 1)| ≤
            |(a - 1) * b * c + (b - 1) * c| + |c - 1| :=
          abs_add_le _ _
        _ ≤ (|(a - 1) * b * c| + |(b - 1) * c|) + |c - 1| :=
          add_le_add (abs_add_le _ _) (le_refl _)
        _ = |a - 1| * |b| * |c| + |b - 1| * |c| + |c - 1| := by
          simp only [abs_mul]
    _ ≤ (A * x) * (1 + B) * (1 + C) +
        (B * x) * (1 + C) + C * x := by
      have h1 : |a - 1| * |b| * |c| ≤
          (A * x) * (1 + B) * (1 + C) :=
        mul_le_mul
          (mul_le_mul ha hbabs (abs_nonneg _) (mul_nonneg hA hx))
          hcabs (abs_nonneg _) (by positivity)
      have h2 : |b - 1| * |c| ≤ (B * x) * (1 + C) :=
        mul_le_mul hb hcabs (abs_nonneg _) (mul_nonneg hB hx)
      exact add_le_add (add_le_add h1 h2) hc
    _ = (A * (1 + B) * (1 + C) + B * (1 + C) + C) * x := by ring

/-- Radius form of the tree Perron--Wright estimate on an arbitrary
nonnegative window `eta k → 0`.  The error keeps the window scale and the
coefficient-transfer scale separate. -/
theorem exists_treePerronWright_radius_relative_bound_uniform_eta
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ K : ℝ, 0 < K ∧ ∀ eta : ℕ → ℝ,
      (∀ k, 0 ≤ eta k) → Tendsto eta atTop (nhds 0) →
      ∀ᶠ k : ℕ in atTop, ∀ t : ℝ,
        |t - 1| ≤ eta k →
        |M.connectedWeight t k 0 /
            physicalTreeRadiusMainTerm M hM k t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨Bfield, hBfield, hfieldLocal⟩ :=
    exists_scalarFieldComplex_real_lipschitz M
  obtain ⟨epsilon, Kfield, hepsilon, hKfield, hfield⟩ :=
    Field.exists_complexFieldConnectedWeight_perronWright_local_relative_bound
      M hM
  let Bscale : ℝ := max Bfield 1
  have hBscale : 0 < Bscale :=
    lt_of_lt_of_le zero_lt_one (le_max_right Bfield 1)
  let Kscaled : ℝ := Kfield * Bscale
  have hKscaled : 0 < Kscaled := mul_pos hKfield hBscale
  let Ktime : ℝ := 2
  let K : ℝ := Ktime * (1 + Kscaled) + Kscaled
  have hKtime : 0 < Ktime := by norm_num [Ktime]
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro eta hetaNonneg heta
  have hhalfTendsto : Tendsto
      (fun k : ℕ ↦ (k : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have htotalTendsto : Tendsto
      (fun k : ℕ ↦ eta k + (k : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by
    simpa only [zero_add] using heta.add hhalfTendsto
  have htotalSmall : ∀ᶠ k : ℕ in atTop,
      eta k + (k : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    htotalTendsto.eventually (isOpen_Iio.mem_nhds (by norm_num))
  have hfieldWindowTendsto : Tendsto (fun k : ℕ ↦ Bfield * eta k)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul heta
  have hfieldSmall : ∀ᶠ k : ℕ in atTop,
      Bfield * eta k < epsilon :=
    hfieldWindowTendsto.eventually (isOpen_Iio.mem_nhds hepsilon)
  have hhalf : ∀ᶠ t : ℝ in nhds 1, (1 / 2 : ℝ) < t :=
    Ioi_mem_nhds (by norm_num)
  have hlocal : ∀ᶠ t : ℝ in nhds 1,
      ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ ≤
          Bfield * |t - 1| ∧
        ((ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).im = 0 ∧
          0 < (ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).re) ∧
        (1 / 2 : ℝ) < t :=
    hfieldLocal.and
      ((ScalarFieldResponse.scalarCriticalRadius_real_positive_near_one M hM).and
        hhalf)
  have hlocalWindow :=
    eventually_shrinking_window_mem_nhds eta heta hlocal
  filter_upwards [hfield, hlocalWindow, hfieldSmall, htotalSmall,
      eventually_ge_atTop 1]
    with k hkfield hklocal hkfieldSmall hksmall hkone
  intro t hwindow
  obtain ⟨hgLocal, hrhoLocal, htHalf⟩ := hklocal t hwindow
  have hkpos : 0 < k := by omega
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hkpos
  let x : ℝ := (k : ℝ) ^ (-(1 / 2 : ℝ))
  let y : ℝ := eta k + x
  have hx : 0 ≤ x := by
    dsimp only [x]
    exact Real.rpow_nonneg (Nat.cast_nonneg k) _
  have heta0 : 0 ≤ eta k := hetaNonneg k
  have hy : 0 ≤ y := by dsimp only [y]; positivity
  have hyone : y ≤ 1 := by
    dsimp only [y, x]
    exact hksmall.le
  have hgEta :
      ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ ≤
        Bfield * eta k := by
    calc
      ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ ≤
          Bfield * |t - 1| := hgLocal
      _ ≤ Bfield * eta k :=
        mul_le_mul_of_nonneg_left hwindow hBfield.le
  have hg :
      ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ ≤ epsilon :=
    hgEta.trans hkfieldSmall.le
  have hfieldBound := hkfield
    (ScalarFieldResponse.scalarFieldComplex M (t : ℂ)) hg
  let rho : ℝ := physicalTreeRadius M hM t
  let P : ℝ := Field.fieldTreePerronWrightMainTerm M hM k
  have hrho : 0 < rho := hrhoLocal.2
  have ht : 0 < t := lt_trans (by norm_num) htHalf
  have hP : 0 < P := by
    dsimp only [P, Field.fieldTreePerronWrightMainTerm,
      PerronWright.FieldTreeConnectedWeightAsymptotic.fieldTreePerronWrightMainTerm]
    have hbeta : 0 < (M.beta hM) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_pos_of_pos (M.beta_pos hM) _
    have hkpow : 0 < (k : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_pos_of_pos hkreal _
    have hbase : 0 < (k : ℝ) / Real.exp 1 :=
      div_pos hkreal (Real.exp_pos 1)
    exact mul_pos (mul_pos hbeta hkpow) (pow_pos hbase k)
  have hrhoEq :
      RadiusResponse.radius M hM
          (ScalarFieldResponse.scalarFieldComplex M (t : ℂ)) =
        (rho : ℂ) := by
    change ScalarRadiusSecond.scalarRadius M hM (t : ℂ) =
      ((ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).re : ℂ)
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hrhoLocal.1
  have hweight := complexFieldConnectedWeight_scalar_tree M t ht k
  have hfieldRaw :
      |rho ^ k * (t * M.connectedWeight t k 0) / P - 1| ≤
        Kfield *
          (‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ + x) := by
    rw [hrhoEq, hweight] at hfieldBound
    have hfieldCast :
        (rho : ℂ) ^ k *
              ((t : ℂ) * (M.connectedWeight t k 0 : ℂ)) / (P : ℂ) - 1 =
            ((rho ^ k * (t * M.connectedWeight t k 0) / P - 1 : ℝ) : ℂ) := by
      norm_cast
    rw [hfieldCast, Complex.norm_real, Real.norm_eq_abs] at hfieldBound
    simpa only [P, x] using hfieldBound
  have hinside :
      ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ + x ≤
        Bscale * y := by
    calc
      ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ + x ≤
          Bfield * eta k + x := add_le_add hgEta (le_refl x)
      _ ≤ Bscale * eta k + Bscale * x := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left Bfield 1) heta0)
          (by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (le_max_right Bfield 1) hx)
      _ = Bscale * y := by dsimp only [y]; ring
  have hfieldReal :
      |rho ^ k * (t * M.connectedWeight t k 0) / P - 1| ≤
        Kscaled * y := by
    calc
      |rho ^ k * (t * M.connectedWeight t k 0) / P - 1| ≤
          Kfield *
            (‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ + x) :=
        hfieldRaw
      _ ≤ Kfield * (Bscale * y) :=
        mul_le_mul_of_nonneg_left hinside hKfield.le
      _ = Kscaled * y := by dsimp only [Kscaled]; ring
  have htime : |t⁻¹ - 1| ≤ Ktime * y := by
    have htLower : (1 / 2 : ℝ) ≤ t := htHalf.le
    have hEq : |t⁻¹ - 1| = |t - 1| / t := by
      have halg : t⁻¹ - 1 = -(t - 1) / t := by
        field_simp [ht.ne']
        ring
      rw [halg, abs_div, abs_neg, abs_of_pos ht]
    rw [hEq]
    calc
      |t - 1| / t ≤ |t - 1| / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) htLower
      _ = 2 * |t - 1| := by ring
      _ ≤ 2 * eta k := mul_le_mul_of_nonneg_left hwindow (by norm_num)
      _ ≤ 2 * y := by
        dsimp only [y]
        linarith
      _ = Ktime * y := by rfl
  have hfactor :
      M.connectedWeight t k 0 /
          physicalTreeRadiusMainTerm M hM k t =
        t⁻¹ * (rho ^ k * (t * M.connectedWeight t k 0) / P) := by
    have htne : t ≠ 0 := ht.ne'
    have hrhone : rho ≠ 0 := hrho.ne'
    have hPne : P ≠ 0 := hP.ne'
    dsimp only [physicalTreeRadiusMainTerm, rho, P]
    rw [inv_pow]
    field_simp [htne, hrhone, hPne]
  rw [hfactor]
  have htriple := abs_three_factor_sub_one_le hy hyone hKtime.le
    hKscaled.le (by norm_num : (0 : ℝ) ≤ 0) htime hfieldReal
    (by simp : |(1 : ℝ) - 1| ≤ 0 * y)
  simpa only [mul_one, add_zero, K] using htriple

/-- Compatibility form with the shrinking window fixed before the constant
is unpacked.  The stronger theorem above shows that the returned constant
is in fact independent of that window. -/
theorem exists_treePerronWright_radius_relative_bound_of_tendsto
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (eta : ℕ → ℝ) (hetaNonneg : ∀ k, 0 ≤ eta k)
    (heta : Tendsto eta atTop (nhds 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ,
        |t - 1| ≤ eta k →
        |M.connectedWeight t k 0 /
            physicalTreeRadiusMainTerm M hM k t - 1| ≤
          K * (eta k + (k : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨K, hK, huniform⟩ :=
    exists_treePerronWright_radius_relative_bound_uniform_eta M hM
  exact ⟨K, hK, huniform eta hetaNonneg heta⟩

/-- The tree case of the physical Perron--Wright formula.  The weight on the
left is the literal finite-graph quantity `C_t(k,0)`. -/
theorem exists_treePerronWright_gaussian_relative_bound
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ,
        Real.sqrt (k : ℝ) * |t - 1| ≤ L →
        |M.connectedWeight t k 0 /
            physicalTreeGaussianMainTerm M hM k t - 1| ≤
          K / Real.sqrt (k : ℝ) := by
  obtain ⟨Bfield, hBfield, hfieldLocal⟩ :=
    exists_scalarFieldComplex_real_lipschitz M
  let Ufield : ℝ := Bfield * L
  have hUfield : 0 ≤ Ufield := mul_nonneg hBfield.le hL
  obtain ⟨Kfield, hKfield, hfield⟩ :=
    Field.exists_complexFieldConnectedWeight_perronWright_shrinking_relative_bound
      M hM Ufield hUfield
  obtain ⟨Kradius, hKradius, hradius⟩ :=
    Radius.exists_criticalWindowRadius_relative_bound M hM L hL
  let Ktime : ℝ := 2 * L
  let K : ℝ :=
    Ktime * (1 + Kradius) * (1 + Kfield) +
      Kradius * (1 + Kfield) + Kfield
  have hKtime : 0 ≤ Ktime := by dsimp only [Ktime]; positivity
  have hKfirst : 0 ≤ Ktime * (1 + Kradius) * (1 + Kfield) :=
    mul_nonneg
      (mul_nonneg hKtime (by linarith : 0 ≤ 1 + Kradius))
      (by linarith : 0 ≤ 1 + Kfield)
  have hKsecond : 0 ≤ Kradius * (1 + Kfield) :=
    mul_nonneg hKradius.le (by linarith)
  have hK : 0 < K := by
    dsimp only [K]
    linarith
  refine ⟨K, hK, ?_⟩
  have hhalf : ∀ᶠ t : ℝ in nhds 1, (1 / 2 : ℝ) < t :=
    Ioi_mem_nhds (by norm_num)
  have hlocal : ∀ᶠ t : ℝ in nhds 1,
      ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ ≤
          Bfield * |t - 1| ∧
        ((ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).im = 0 ∧
          0 < (ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).re) ∧
        (1 / 2 : ℝ) < t :=
    hfieldLocal.and
      ((ScalarFieldResponse.scalarCriticalRadius_real_positive_near_one M hM).and hhalf)
  have hlocalWindow := eventually_sqrt_window_mem_nhds L hlocal
  filter_upwards [hfield, hradius, hlocalWindow, eventually_ge_atTop 1]
    with k hkfield hkradius hklocal hkone
  intro t hwindow
  obtain ⟨hgLocal, hrhoLocal, htHalf⟩ := hklocal t hwindow
  have hkpos : 0 < k := by omega
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
      ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ ≤ Ufield * x := by
    calc
      ‖ScalarFieldResponse.scalarFieldComplex M (t : ℂ)‖ ≤
          Bfield * |t - 1| := hgLocal
      _ ≤ Bfield * (L * x) :=
        mul_le_mul_of_nonneg_left hy hBfield.le
      _ = Ufield * x := by dsimp only [Ufield]; ring
  have hfieldBound := hkfield
    (ScalarFieldResponse.scalarFieldComplex M (t : ℂ)) hg
  have hradiusBound := hkradius t hwindow
  let rho : ℝ := physicalTreeRadius M hM t
  let P : ℝ := Field.fieldTreePerronWrightMainTerm M hM k
  let G : ℝ := Real.exp
    (-Radius.criticalQuadraticRate M hM * (k : ℝ) * (t - 1) ^ 2)
  have hrho : 0 < rho := by
    exact hrhoLocal.2
  have ht : 0 < t := lt_trans (by norm_num) htHalf
  have hP : 0 < P := by
    dsimp only [P, Field.fieldTreePerronWrightMainTerm,
      PerronWright.FieldTreeConnectedWeightAsymptotic.fieldTreePerronWrightMainTerm]
    have hbeta : 0 < (M.beta hM) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_pos_of_pos (M.beta_pos hM) _
    have hkpow : 0 < (k : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_pos_of_pos hkreal _
    have hbase : 0 < (k : ℝ) / Real.exp 1 :=
      div_pos hkreal (Real.exp_pos 1)
    exact mul_pos (mul_pos hbeta hkpow) (pow_pos hbase k)
  have hG : 0 < G := by dsimp only [G]; positivity
  have hrhoEq :
      RadiusResponse.radius M hM
          (ScalarFieldResponse.scalarFieldComplex M (t : ℂ)) =
        (rho : ℂ) := by
    change ScalarRadiusSecond.scalarRadius M hM (t : ℂ) =
      ((ScalarRadiusSecond.scalarRadius M hM (t : ℂ)).re : ℂ)
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hrhoLocal.1
  have hweight := complexFieldConnectedWeight_scalar_tree M t ht k
  have hfieldReal :
      |rho ^ k * (t * M.connectedWeight t k 0) / P - 1| ≤
        Kfield * x := by
    rw [hrhoEq, hweight] at hfieldBound
    have hfieldCast :
        (rho : ℂ) ^ k *
              ((t : ℂ) * (M.connectedWeight t k 0 : ℂ)) / (P : ℂ) - 1 =
            ((rho ^ k * (t * M.connectedWeight t k 0) / P - 1 : ℝ) : ℂ) := by
      norm_cast
    rw [hfieldCast, Complex.norm_real, Real.norm_eq_abs] at hfieldBound
    simpa only [P, x] using hfieldBound
  have hradiusReal : |rho⁻¹ ^ k / G - 1| ≤ Kradius * x := by
    simpa only [rho, G, physicalTreeRadius, div_eq_mul_inv, hxSqrt,
      mul_assoc] using hradiusBound
  have htime : |t⁻¹ - 1| ≤ Ktime * x := by
    have htLower : (1 / 2 : ℝ) ≤ t := htHalf.le
    have hEq : |t⁻¹ - 1| = |t - 1| / t := by
      have halg : t⁻¹ - 1 = -(t - 1) / t := by
        field_simp [ht.ne']
        ring
      rw [halg, abs_div, abs_neg, abs_of_pos ht]
    rw [hEq]
    calc
      |t - 1| / t ≤ |t - 1| / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) htLower
      _ = 2 * |t - 1| := by ring
      _ ≤ 2 * (L * x) := mul_le_mul_of_nonneg_left hy (by norm_num)
      _ = Ktime * x := by dsimp only [Ktime]; ring
  have hfactor :
      M.connectedWeight t k 0 /
          physicalTreeGaussianMainTerm M hM k t =
        t⁻¹ * (rho⁻¹ ^ k / G) *
          (rho ^ k * (t * M.connectedWeight t k 0) / P) := by
    have htne : t ≠ 0 := ht.ne'
    have hrhone : rho ≠ 0 := hrho.ne'
    have hPne : P ≠ 0 := hP.ne'
    have hGne : G ≠ 0 := hG.ne'
    dsimp only [physicalTreeGaussianMainTerm, P, G]
    field_simp [htne, hrhone, hPne, hGne]
    have hcancel : (1 / rho) ^ k * rho ^ k = 1 := by
      rw [← mul_pow]
      field_simp [hrhone]
      simp
    calc
      M.connectedWeight t k 0 /
            Field.fieldTreePerronWrightMainTerm M hM k =
          M.connectedWeight t k 0 * ((1 / rho) ^ k * rho ^ k) /
            Field.fieldTreePerronWrightMainTerm M hM k := by
        rw [hcancel]
        ring
      _ = M.connectedWeight t k 0 * (1 / rho) ^ k * rho ^ k /
            Field.fieldTreePerronWrightMainTerm M hM k := by ring
  rw [hfactor]
  have htriple := abs_three_factor_sub_one_le hx hxone hKtime
    hKradius.le hKfield.le htime hradiusReal hfieldReal
  simpa only [K, hxSqrt, div_eq_mul_inv] using htriple

/-- The same formula with the paper's window written literally as
`|t-1| <= L k^(-1/2)`. -/
theorem exists_treePerronWright_gaussian_relative_bound_rpow_window
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ k : ℕ in atTop,
      ∀ t : ℝ,
        |t - 1| ≤ L * (k : ℝ) ^ (-(1 / 2 : ℝ)) →
        |M.connectedWeight t k 0 /
            physicalTreeGaussianMainTerm M hM k t - 1| ≤
          K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨K, hK, hmain⟩ :=
    exists_treePerronWright_gaussian_relative_bound M hM L hL
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop 1] with k hk hkone
  intro t ht
  have hkpos : 0 < k := by omega
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
    |M.connectedWeight t k 0 /
          physicalTreeGaussianMainTerm M hM k t - 1| ≤
        K / Real.sqrt (k : ℝ) := hbound
    _ = K * (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, ← hx]

end PerronWright.TreePerronWrightFormula
