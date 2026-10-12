import PerronWright.Enumeration.ZeroFieldTreeIntegratedSingularity
import PerronWright.Enumeration.RootedTreeRadiusLower
import PerronWright.Analysis.NormalizedFoldActivity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Matching the local tree primitive to the genuine labelled-tree EGF

The unrooted tree function in this file is not postulated.  It is the sum of
the complexification of the literal coefficients in `CompactBJRModel.treeEGF`.
We prove convergence in the unit disk from the already established rooted
coefficient bound.  The formal identity

`vertex-rooted = X * derivative(unrooted)`

then becomes an identity of analytic functions in the unit disk.  On the
positive fold ray this identifies the derivative of the genuine tree EGF
with `treeFoldDerivative`, so the local primitive differs from it by one
additive constant.
-/

open Filter Topology MeasureTheory Set
open scoped Classical Topology ENNReal NNReal

noncomputable section

namespace PerronWright.ZeroFieldTreeEGFMatching

open PerronWright.ZeroFieldTreeLocalSingularity
open PerronWright.ZeroFieldTreeIntegratedSingularity

namespace MPR

export PerronWright.MarkedPathResolvent
  (scalarIntegralCLM scalarIntegralCLM_apply)

end MPR

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Coefficientwise complexification of the literal zero-field unrooted-tree
EGF. -/
def complexTreeEGF (M : CompactBJRModel S) : PowerSeries ℂ :=
  PowerSeries.map (algebraMap ℝ ℂ) (M.treeEGF 0)

@[simp] theorem complexTreeEGF_coeff
    (M : CompactBJRModel S) (n : ℕ) :
    PowerSeries.coeff n (complexTreeEGF M) =
      Complex.ofReal (PowerSeries.coeff n (M.treeEGF 0)) := by
  simp [complexTreeEGF]

/-- The one-dimensional analytic series attached to the literal tree
coefficients. -/
def zeroFieldTreeFMS (M : CompactBJRModel S) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  oneDimensionalFormalMultilinearSeries (complexTreeEGF M)

/-- The genuine analytic sum of the literal unrooted-tree coefficients. -/
def zeroFieldTreeSeries (M : CompactBJRModel S) (w : ℂ) : ℂ :=
  (zeroFieldTreeFMS M).sum w

private theorem treeEGF_coeff_nonneg
    (M : CompactBJRModel S) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (M.treeEGF 0) := by
  by_cases hn : n = 0
  · simp [hn, CompactBJRModel.treeEGF]
  · simp only [CompactBJRModel.treeEGF, PowerSeries.coeff_mk, hn,
      ↓reduceIte]
    exact div_nonneg (M.fieldConnectedWeight_nonneg 0 n 0)
      (Nat.cast_nonneg n.factorial)

private theorem vertexRootedTreeEGF_coeff_le_one
    (M : CompactBJRModel S) (n : ℕ) :
    PowerSeries.coeff n (M.vertexRootedTreeEGF 0) ≤ 1 := by
  rw [M.vertexRootedTreeEGF_coeff_eq_typeRootedTreeEGF_integral]
  calc
    (∫ x : S, PowerSeries.coeff n M.typeRootedTreeEGF x ∂M.mu) ≤
        ∫ _x : S, (1 : ℝ) ∂M.mu := by
      apply integral_mono
      · exact (PowerSeries.coeff n M.typeRootedTreeEGF).continuous
          |>.integrable_of_hasCompactSupport isClosed_closure.isCompact
      · exact integrable_const 1
      · intro x
        exact (le_abs_self _).trans
          ((PowerSeries.coeff n M.typeRootedTreeEGF).norm_coe_le_norm x
            |>.trans (M.typeRootedTreeEGF_coeff_norm_le_one n))
    _ = 1 := by simp [integral_const, probReal_univ]

private theorem treeEGF_coeff_le_one
    (M : CompactBJRModel S) (n : ℕ) :
    PowerSeries.coeff n (M.treeEGF 0) ≤ 1 := by
  cases n with
  | zero => simp [CompactBJRModel.treeEGF]
  | succ n =>
      let k := n + 1
      have hk : 0 < k := by simp [k]
      have hroot : PowerSeries.coeff k (M.vertexRootedTreeEGF 0) =
          (k : ℝ) * PowerSeries.coeff k (M.treeEGF 0) := by
        simp only [CompactBJRModel.vertexRootedTreeEGF,
          CompactBJRModel.treeEGF, PowerSeries.coeff_mk,
          Nat.ne_of_gt hk, ↓reduceIte]
        rw [M.vertexRootedTreeWeight_eq_card_mul 0 hk]
        ring
      have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hnonneg := treeEGF_coeff_nonneg M k
      have hvertex := vertexRootedTreeEGF_coeff_le_one M k
      rw [hroot] at hvertex
      nlinarith

/-- Every homogeneous term of the genuine unrooted-tree series has norm at
most one. -/
theorem zeroFieldTreeFMS_term_norm_le_one
    (M : CompactBJRModel S) (n : ℕ) :
    ‖zeroFieldTreeFMS M n‖ ≤ 1 := by
  rw [zeroFieldTreeFMS, oneDimensionalFormalMultilinearSeries,
    ContinuousMultilinearMap.norm_mkPiRing, complexTreeEGF_coeff,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (treeEGF_coeff_nonneg M n)]
  exact treeEGF_coeff_le_one M n

/-- The literal unrooted-tree series converges throughout the open unit
disk. -/
theorem one_le_zeroFieldTreeFMS_radius
    (M : CompactBJRModel S) :
    (1 : ℝ≥0∞) ≤ (zeroFieldTreeFMS M).radius := by
  simpa using (zeroFieldTreeFMS M).le_radius_of_bound 1
    (r := (1 : ℝ≥0)) (fun n => by
      simpa using zeroFieldTreeFMS_term_norm_le_one M n)

/-- The genuine unrooted-tree sum is analytic on the open unit disk. -/
theorem zeroFieldTreeSeries_analyticOnNhd_unit
    (M : CompactBJRModel S) :
    AnalyticOnNhd ℂ (zeroFieldTreeSeries M) (Metric.ball (0 : ℂ) 1) := by
  intro w hw
  have hw' : w ∈ Metric.eball 0 (zeroFieldTreeFMS M).radius := by
    apply Metric.eball_subset_eball (one_le_zeroFieldTreeFMS_radius M)
    rw [← ENNReal.coe_one, Metric.eball_coe]
    simpa only [NNReal.coe_one] using hw
  exact (zeroFieldTreeFMS M).analyticOnNhd w hw'

/-- Scalar integration of the actual type-rooted Taylor series. -/
def scalarRootedTreeFMS (M : CompactBJRModel S) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (MPR.scalarIntegralCLM M).compFormalMultilinearSeries
    M.complexTypeRootedTreeFMS

/-- The scalar rooted-tree function obtained from the genuine type-resolved
sum. -/
def scalarRootedTreeSeries (M : CompactBJRModel S) (w : ℂ) : ℂ :=
  MPR.scalarIntegralCLM M (M.rootedTreeSeries w)

private theorem scalarRootedTreeFMS_powerSeries
    (M : CompactBJRModel S) :
    oneDimensionalPowerSeries (scalarRootedTreeFMS M) =
      PowerSeries.map (algebraMap ℝ ℂ) (M.vertexRootedTreeEGF 0) := by
  apply PowerSeries.ext
  intro n
  rw [scalarRootedTreeFMS,
    oneDimensionalPowerSeries_compContinuousLinearMap_coeff]
  rw [oneDimensionalPowerSeries_coeff,
    CompactBJRModel.complexTypeRootedTreeFMS,
    oneDimensionalFormalMultilinearSeries_coeff,
    M.complexTypeRootedTreeEGF_coeff,
    MPR.scalarIntegralCLM_apply, PowerSeries.coeff_map]
  rw [M.vertexRootedTreeEGF_coeff_eq_typeRootedTreeEGF_integral]
  exact integral_complex_ofReal

private theorem complex_vertexRooted_eq_X_derivative_tree
    (M : CompactBJRModel S) :
    PowerSeries.map (algebraMap ℝ ℂ) (M.vertexRootedTreeEGF 0) =
      PowerSeries.X * PowerSeries.derivative ℂ (complexTreeEGF M) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [CompactBJRModel.vertexRootedTreeEGF]
  | succ n =>
      rw [PowerSeries.coeff_map, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_derivative]
      have h := congrArg (PowerSeries.coeff (n + 1))
        (M.vertexRootedTreeEGF_eq_X_derivative 0)
      rw [PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_derivative] at h
      rw [complexTreeEGF_coeff]
      rw [h]
      norm_num [Nat.cast_add, Nat.cast_one]

private theorem scalarRootedTreeFMS_eq_tree_derivative
    (M : CompactBJRModel S) :
    scalarRootedTreeFMS M =
      oneDimensionalFormalMultilinearSeries
        (PowerSeries.X * PowerSeries.derivative ℂ (complexTreeEGF M)) := by
  rw [← oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries
      (scalarRootedTreeFMS M),
    scalarRootedTreeFMS_powerSeries,
    complex_vertexRooted_eq_X_derivative_tree]

private theorem ContinuousLinearMap.comp_hasFPowerSeriesAt_local
    {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (L : A →L[ℂ] B) {f : ℂ → A}
    {p : FormalMultilinearSeries ℂ ℂ A}
    (hp : HasFPowerSeriesAt f p 0) :
    HasFPowerSeriesAt (fun z => L (f z))
      (L.compFormalMultilinearSeries p) 0 := by
  obtain ⟨r, hr⟩ := hp
  exact ⟨r, by
    simpa only [Function.comp_def] using L.comp_hasFPowerSeriesOnBall hr⟩

private theorem hasFPowerSeriesAt_factorial_nsmul_coeff
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    {f : ℂ → A} {p : FormalMultilinearSeries ℂ ℂ A} {z : ℂ}
    (hp : HasFPowerSeriesAt f p z) (n : ℕ) :
    n.factorial • p.coeff n = iteratedDeriv n f z := by
  obtain ⟨r, hr⟩ := hp
  have h := hr.factorial_smul (1 : ℂ) n
  simpa only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] using h

private theorem hasFPowerSeriesAt_mul_oneDimensional
    {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    {f g : ℂ → A}
    {p q : FormalMultilinearSeries ℂ ℂ A}
    (hp : HasFPowerSeriesAt f p 0)
    (hq : HasFPowerSeriesAt g q 0) :
    HasFPowerSeriesAt (fun z => f z * g z)
      (oneDimensionalFormalMultilinearSeries
        (oneDimensionalPowerSeries p * oneDimensionalPowerSeries q)) 0 := by
  obtain ⟨r, hr⟩ := hp.analyticAt.mul hq.analyticAt
  have hfun : f * g = fun z => f z * g z := by rfl
  rw [hfun] at hr
  have hrPower : oneDimensionalPowerSeries r =
      oneDimensionalPowerSeries p * oneDimensionalPowerSeries q := by
    apply PowerSeries.ext
    intro n
    have hfac : (n.factorial : ℂ) ≠ 0 := by
      exact_mod_cast n.factorial_ne_zero
    apply smul_right_injective (R := ℂ) A hfac
    simp only [Algebra.smul_def, map_natCast]
    calc
      (n.factorial : A) *
          PowerSeries.coeff n (oneDimensionalPowerSeries r) =
          iteratedDeriv n (fun z => f z * g z) 0 := by
        rw [oneDimensionalPowerSeries_coeff]
        simpa only [nsmul_eq_mul] using
          hasFPowerSeriesAt_factorial_nsmul_coeff hr n
      _ = ∑ j ∈ Finset.range (n + 1),
          (Nat.choose n j : A) * iteratedDeriv j f 0 *
            iteratedDeriv (n - j) g 0 := by
        exact iteratedDeriv_mul
          (hp.analyticAt.contDiffAt.of_le le_top)
          (hq.analyticAt.contDiffAt.of_le le_top)
      _ = (n.factorial : A) * PowerSeries.coeff n
          (oneDimensionalPowerSeries p * oneDimensionalPowerSeries q) := by
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        simp only [oneDimensionalPowerSeries_coeff, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hchoose := Nat.choose_mul_factorial_mul_factorial hjle
        have hchooseA :
            (Nat.choose n j : A) * (j.factorial : A) *
                ((n - j).factorial : A) = (n.factorial : A) := by
          simpa only [Nat.cast_mul] using
            congrArg (fun m : ℕ => (m : A)) hchoose
        have hpj := hasFPowerSeriesAt_factorial_nsmul_coeff hp j
        have hqj :=
          hasFPowerSeriesAt_factorial_nsmul_coeff hq (n - j)
        simp only [nsmul_eq_mul] at hpj hqj
        rw [← hpj, ← hqj, ← hchooseA]
        ring
  have hrSeries : r = oneDimensionalFormalMultilinearSeries
      (oneDimensionalPowerSeries p * oneDimensionalPowerSeries q) := by
    rw [← oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries r,
      hrPower]
  simpa only [hrSeries] using hr

private theorem zeroFieldTreeSeries_hasFPowerSeriesAt
    (M : CompactBJRModel S) :
    HasFPowerSeriesAt (zeroFieldTreeSeries M) (zeroFieldTreeFMS M) 0 := by
  have hpos : 0 < (zeroFieldTreeFMS M).radius :=
    (by norm_num : (0 : ℝ≥0∞) < 1).trans_le
      (one_le_zeroFieldTreeFMS_radius M)
  exact (zeroFieldTreeFMS M).hasFPowerSeriesOnBall hpos
    |>.hasFPowerSeriesAt

private theorem scalarRootedTreeSeries_hasFPowerSeriesAt
    (M : CompactBJRModel S) :
    HasFPowerSeriesAt (scalarRootedTreeSeries M)
      (oneDimensionalFormalMultilinearSeries
        (PowerSeries.X * PowerSeries.derivative ℂ (complexTreeEGF M))) 0 := by
  have hpos : 0 < M.complexTypeRootedTreeFMS.radius :=
    (by norm_num : (0 : ℝ≥0∞) < 1).trans_le
      M.one_le_complexTypeRootedTreeFMS_radius
  have hroot : HasFPowerSeriesAt M.rootedTreeSeries
      M.complexTypeRootedTreeFMS 0 :=
    (M.complexTypeRootedTreeFMS.hasFPowerSeriesOnBall hpos)
      |>.hasFPowerSeriesAt
  have hcomp := ContinuousLinearMap.comp_hasFPowerSeriesAt_local
    (MPR.scalarIntegralCLM M) hroot
  change HasFPowerSeriesAt (scalarRootedTreeSeries M)
    (scalarRootedTreeFMS M) 0 at hcomp
  rw [scalarRootedTreeFMS_eq_tree_derivative] at hcomp
  exact hcomp

private theorem derivTreeSeries_hasFPowerSeriesAt
    (M : CompactBJRModel S) :
    HasFPowerSeriesAt (deriv (zeroFieldTreeSeries M))
      (oneDimensionalFormalMultilinearSeries
        (PowerSeries.derivative ℂ (complexTreeEGF M))) 0 := by
  let L : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
  let p := zeroFieldTreeFMS M
  have hp : HasFPowerSeriesAt (zeroFieldTreeSeries M) p 0 :=
    zeroFieldTreeSeries_hasFPowerSeriesAt M
  obtain ⟨rho, hrho⟩ := hp
  have hfd0 : HasFPowerSeriesAt (fderiv ℂ (zeroFieldTreeSeries M))
      p.derivSeries 0 := ⟨rho, hrho.fderiv⟩
  have hfd := ContinuousLinearMap.comp_hasFPowerSeriesAt_local L hfd0
  have hpower : oneDimensionalPowerSeries
      (L.compFormalMultilinearSeries p.derivSeries) =
        PowerSeries.derivative ℂ (complexTreeEGF M) := by
    apply PowerSeries.ext
    intro n
    rw [oneDimensionalPowerSeries_compContinuousLinearMap_coeff,
      oneDimensionalPowerSeries_coeff]
    simp only [L, p, ContinuousLinearMap.apply_apply,
      FormalMultilinearSeries.derivSeries_coeff_one,
      PowerSeries.coeff_derivative, nsmul_eq_mul]
    rw [zeroFieldTreeFMS,
      oneDimensionalFormalMultilinearSeries_coeff]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring
  have hseries : L.compFormalMultilinearSeries p.derivSeries =
      oneDimensionalFormalMultilinearSeries
        (PowerSeries.derivative ℂ (complexTreeEGF M)) := by
    rw [← oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries
        (L.compFormalMultilinearSeries p.derivSeries), hpower]
  rw [hseries] at hfd
  convert hfd using 1
  funext z
  rfl

private theorem id_hasFPowerSeriesAt_X :
    HasFPowerSeriesAt (id : ℂ → ℂ)
      (oneDimensionalFormalMultilinearSeries (PowerSeries.X : PowerSeries ℂ)) 0 := by
  let L : ℂ →L[ℂ] ℂ := ContinuousLinearMap.id ℂ ℂ
  have hL := L.hasFPowerSeriesAt 0
  have hpower : oneDimensionalPowerSeries (L.fpowerSeries 0) =
      (PowerSeries.X : PowerSeries ℂ) := by
    apply PowerSeries.ext
    intro n
    cases n with
    | zero => simp [oneDimensionalPowerSeries_coeff,
        FormalMultilinearSeries.coeff, L]
    | succ n =>
        cases n with
        | zero => simp [oneDimensionalPowerSeries_coeff,
            FormalMultilinearSeries.coeff, L]
        | succ n => simp [oneDimensionalPowerSeries_coeff,
            FormalMultilinearSeries.coeff, L,
            ContinuousLinearMap.fpowerSeries_apply_add_two,
            PowerSeries.coeff_X]
  have hseries : L.fpowerSeries 0 =
      oneDimensionalFormalMultilinearSeries (PowerSeries.X : PowerSeries ℂ) := by
    rw [← oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries
        (L.fpowerSeries 0), hpower]
  rw [hseries] at hL
  convert hL using 1
  funext z
  rfl

private theorem rooted_equals_X_mul_tree_deriv_eventually
    (M : CompactBJRModel S) :
    (fun w : ℂ => w * deriv (zeroFieldTreeSeries M) w) =ᶠ[𝓝 0]
      scalarRootedTreeSeries M := by
  have hmul : HasFPowerSeriesAt
      (fun w : ℂ => w * deriv (zeroFieldTreeSeries M) w)
      (oneDimensionalFormalMultilinearSeries
        (PowerSeries.X *
          PowerSeries.derivative ℂ (complexTreeEGF M))) 0 := by
    simpa only [id_eq,
      oneDimensionalPowerSeries_oneDimensionalFormalMultilinearSeries] using
      hasFPowerSeriesAt_mul_oneDimensional
      id_hasFPowerSeriesAt_X (derivTreeSeries_hasFPowerSeriesAt M)
  have hroot : HasFPowerSeriesAt (scalarRootedTreeSeries M)
      (oneDimensionalFormalMultilinearSeries
        (PowerSeries.X *
          PowerSeries.derivative ℂ (complexTreeEGF M))) 0 :=
    scalarRootedTreeSeries_hasFPowerSeriesAt M
  filter_upwards [hmul.eventually_hasSum_sub,
    hroot.eventually_hasSum_sub] with w h₁ h₂
  exact h₁.unique h₂

/-- The formal rooted/unrooted derivative identity holds for the genuine
analytic sums throughout the whole open unit disk. -/
theorem rooted_equals_X_mul_tree_deriv_on_unit
    (M : CompactBJRModel S) :
    Set.EqOn (fun w : ℂ => w * deriv (zeroFieldTreeSeries M) w)
      (scalarRootedTreeSeries M) (Metric.ball (0 : ℂ) 1) := by
  let U : Set ℂ := Metric.ball (0 : ℂ) 1
  let f : ℂ → ℂ := fun w => w * deriv (zeroFieldTreeSeries M) w
  let g : ℂ → ℂ := scalarRootedTreeSeries M
  have hf : AnalyticOnNhd ℂ f U := by
    exact analyticOnNhd_id.mul
      (zeroFieldTreeSeries_analyticOnNhd_unit M).deriv
  have hg : AnalyticOnNhd ℂ g U := by
    intro w hw
    have hwUnit : w ∈ Metric.eball 0 (1 : ℝ≥0∞) := by
      rw [← ENNReal.coe_one, Metric.eball_coe]
      simpa only [NNReal.coe_one] using hw
    have hwRadius : w ∈
        Metric.eball 0 M.complexTypeRootedTreeFMS.radius :=
      Metric.eball_subset_eball M.one_le_complexTypeRootedTreeFMS_radius
        hwUnit
    exact (MPR.scalarIntegralCLM M).analyticAt _ |>.comp
      (M.rootedTreeSeries_analyticOnNhd w hwRadius)
  have hUpre : IsPreconnected U :=
    (convex_ball (0 : ℂ) 1).isPreconnected
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self zero_lt_one
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUpre h0U
    (rooted_equals_X_mul_tree_deriv_eventually M)

/-- Any analytic primitive of `treeFoldDerivative` matches the genuine
labelled-tree sum up to one additive constant on a sufficiently short
positive fold ray. -/
theorem exists_positive_ray_treeSeries_eq_const_add_of_primitive
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (U : ℂ → ℂ) {r : ℝ} (hr : 0 < r)
    (hUderiv : ∀ X ∈ Metric.ball (0 : ℂ) r,
      HasDerivAt U (treeFoldDerivative M hM X) X) :
    ∃ (C : ℂ) (ε : ℝ), 0 < ε ∧
      ∀ x : ℝ, 0 < x → x < ε →
        zeroFieldTreeSeries M ((1 - x ^ 2 : ℝ) : ℂ) = C + U x := by
  obtain ⟨δ, hδ, hfold⟩ :=
    TreeNormalizedFoldActivity.foldProfile_eq_rootedTreeSeries_real_near_one
      M hM
  let ε : ℝ := min r (min 1 (Real.sqrt δ)) / 2
  have hsqrtδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  have hεr : ε < r := by
    dsimp only [ε]
    have := min_le_left r (min 1 (Real.sqrt δ))
    nlinarith
  have hεone : ε < 1 := by
    dsimp only [ε]
    have := (min_le_right r (min 1 (Real.sqrt δ))).trans
      (min_le_left 1 (Real.sqrt δ))
    nlinarith
  have hεδ : ε ^ 2 < δ := by
    have hle : ε < Real.sqrt δ := by
      dsimp only [ε]
      have := (min_le_right r (min 1 (Real.sqrt δ))).trans
        (min_le_right 1 (Real.sqrt δ))
      nlinarith
    nlinarith [Real.sq_sqrt hδ.le]
  let D : ℝ → ℂ := fun x =>
    zeroFieldTreeSeries M ((1 - x ^ 2 : ℝ) : ℂ) - U x
  have hDderiv : ∀ x ∈ Set.Ioo (0 : ℝ) ε,
      HasDerivAt D 0 x := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have hxε : x < ε := hx.2
    have hx1 : x < 1 := hxε.trans hεone
    let w : ℝ := 1 - x ^ 2
    have hw0 : 0 ≤ w := by dsimp only [w]; nlinarith
    have hw1 : w < 1 := by dsimp only [w]; nlinarith
    have hwclose : |w - 1| < δ := by
      dsimp only [w]
      rw [show 1 - x ^ 2 - 1 = -(x ^ 2) by ring,
        abs_neg, abs_of_nonneg (sq_nonneg x)]
      nlinarith [sq_nonneg (ε - x), sq_nonneg (ε + x)]
    have hwball : (w : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hw0]
      exact hw1
    have hroot := rooted_equals_X_mul_tree_deriv_on_unit M hwball
    have hprofile := hfold w hw0 hw1 hwclose
    have hsqrt : Real.sqrt (1 - w) = x := by
      rw [show 1 - w = x ^ 2 by dsimp only [w]; ring,
        Real.sqrt_sq_eq_abs, abs_of_pos hx0]
    have hscalar : scalarRootedTreeSeries M (w : ℂ) =
        foldVertexRootedScalar M hM x := by
      rw [scalarRootedTreeSeries, foldVertexRootedScalar, ← hprofile,
        hsqrt]
    have hwne : (w : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (by
      dsimp only [w]
      nlinarith : 0 < w))
    have htreeDeriv : deriv (zeroFieldTreeSeries M) (w : ℂ) =
        foldVertexRootedScalar M hM x / w := by
      rw [← hscalar]
      apply (eq_div_iff hwne).2
      simpa only [mul_comm] using hroot
    have hwr : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
      have hraw := (hasDerivAt_const x (1 : ℝ)).sub
        ((hasDerivAt_id x).pow 2)
      have heq : (fun y : ℝ => 1 - y ^ 2) =ᶠ[nhds x]
          ((fun _y : ℝ => 1) - id ^ 2) :=
        Filter.Eventually.of_forall (fun y => by simp [pow_two])
      apply (hraw.congr_of_eventuallyEq heq).congr_deriv
      simp only [id_eq]
      ring
    have htreeComplex : HasDerivAt (zeroFieldTreeSeries M)
        (foldVertexRootedScalar M hM x / w) (w : ℂ) :=
      (zeroFieldTreeSeries_analyticOnNhd_unit M (w : ℂ) hwball)
        |>.differentiableAt.hasDerivAt.congr_deriv htreeDeriv
    have htreeRealAt : HasDerivAt
        (fun y : ℝ => zeroFieldTreeSeries M (y : ℂ))
        (foldVertexRootedScalar M hM x / w) (1 - x ^ 2) := by
      simpa only [w] using htreeComplex.comp_ofReal
    have htreeReal := htreeRealAt.scomp x hwr
    have hxball : (x : ℂ) ∈ Metric.ball (0 : ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hx0]
      exact hxε.trans hεr
    have hUcomplex := hUderiv (x : ℂ) hxball
    have hUreal := hUcomplex.comp_ofReal
    have hsame : (-2 * (x : ℂ)) *
          (foldVertexRootedScalar M hM x / w) =
        treeFoldDerivative M hM x := by
      rw [treeFoldDerivative]
      change (-2 * (x : ℂ)) *
          (foldVertexRootedScalar M hM x / (w : ℂ)) =
        (-2 * (x : ℂ)) * foldVertexRootedScalar M hM x /
          (1 - (x : ℂ) ^ 2)
      rw [show (w : ℂ) = 1 - (x : ℂ) ^ 2 by
        norm_cast]
      ring
    have htreeReal' : HasDerivAt
        (fun y : ℝ => zeroFieldTreeSeries M ((1 - y ^ 2 : ℝ) : ℂ))
        (treeFoldDerivative M hM x) x := by
      have htreeRealRaw : HasDerivAt
          (fun y : ℝ => zeroFieldTreeSeries M ((1 - y ^ 2 : ℝ) : ℂ))
          ((-2 * x) • (foldVertexRootedScalar M hM x / w)) x := by
        apply htreeReal.congr_of_eventuallyEq
        exact Filter.Eventually.of_forall (fun y => rfl)
      apply htreeRealRaw.congr_deriv
      simpa only [Complex.real_smul, Complex.ofReal_neg,
        Complex.ofReal_mul, Complex.ofReal_ofNat] using hsame
    exact (htreeReal'.sub hUreal).congr_deriv (sub_self _)
  have hDdiff : DifferentiableOn ℝ D (Set.Ioo (0 : ℝ) ε) :=
    fun x hx => (hDderiv x hx).differentiableAt.differentiableWithinAt
  have hDzero : Set.EqOn (deriv D) 0 (Set.Ioo (0 : ℝ) ε) :=
    fun x hx => (hDderiv x hx).deriv
  obtain ⟨C, hC⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    isPreconnected_Ioo hDdiff hDzero
  refine ⟨C, ε, hε, ?_⟩
  intro x hx0 hxε
  have := hC x ⟨hx0, hxε⟩
  dsimp only [D] at this
  exact sub_eq_iff_eq_add.mp this

/-- On a sufficiently short positive fold ray, the genuine labelled-tree
sum differs from a normalized analytic primitive by one constant. -/
theorem exists_positive_ray_treeSeries_eq_const_add_primitive
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (U : ℂ → ℂ) (C : ℂ) (ε : ℝ),
      0 < ε ∧ U 0 = 0 ∧ AnalyticAt ℂ U 0 ∧
      ∀ x : ℝ, 0 < x → x < ε →
        zeroFieldTreeSeries M ((1 - x ^ 2 : ℝ) : ℂ) = C + U x := by
  obtain ⟨U, r, hr, hU0, hUa, hUderiv⟩ :=
    exists_normalized_zeroFieldTree_fold_primitive M hM
  obtain ⟨C, ε, hε, hmatch⟩ :=
    exists_positive_ray_treeSeries_eq_const_add_of_primitive
      M hM U hr hUderiv
  exact ⟨U, C, ε, hε, hU0,
    hUa 0 (Metric.mem_ball_self hr), hmatch⟩

/-- Consequently the genuine labelled-tree EGF has the claimed integrated
Perron--Wright fold expansion on the positive physical ray. -/
theorem exists_positive_ray_zeroFieldTree_expansion
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ (C : ℂ) (R : ℂ → ℂ) (ε : ℝ),
      0 < ε ∧ AnalyticAt ℂ R 0 ∧
      ∀ x : ℝ, 0 < x → x < ε →
        zeroFieldTreeSeries M ((1 - x ^ 2 : ℝ) : ℂ) =
          C - (x : ℂ) ^ 2 +
            (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) * (x : ℂ) ^ 3 +
            (x : ℂ) ^ 4 * R x := by
  obtain ⟨U, R, r, hr, hU0, hUa, hRa, hUderiv, hUexp⟩ :=
    exists_normalized_zeroFieldTree_fold_expansion M hM
  obtain ⟨C, ε₀, hε₀, hmatch⟩ :=
    exists_positive_ray_treeSeries_eq_const_add_of_primitive
      M hM U hr hUderiv
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
    (show {X : ℂ | U X = -X ^ 2 +
        (2 * (FoldCoefficients.gamma M hM : ℂ) / 3) * X ^ 3 +
        X ^ 4 * R X} ∈ 𝓝 0 from hUexp)
  let ε : ℝ := min ε₀ ρ / 2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  refine ⟨C, R, ε, hε, hRa, ?_⟩
  intro x hx0 hxε
  have hxε₀ : x < ε₀ := by
    dsimp only [ε] at hxε
    have := min_le_left ε₀ ρ
    nlinarith
  have hxρ : ‖(x : ℂ)‖ < ρ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    dsimp only [ε] at hxε
    have := min_le_right ε₀ ρ
    nlinarith
  have hUx := hρsub (by
    simpa only [Metric.mem_ball, dist_zero_right] using hxρ)
  rw [hmatch x hx0 hxε₀]
  rw [hUx]
  ring

end PerronWright.ZeroFieldTreeEGFMatching
