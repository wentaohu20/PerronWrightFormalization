import PerronWright.Probability.AnnealedTupleResidualConnectedLawFormula
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Finite-n analytic bounds for the literal fresh-type isolation factor

All moments here are integrals of the actual fresh exposure.  The Taylor
errors are bounded directly from the model kernel bound, rather than
stored as a cumulant-expansion hypothesis.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FreshTypeCumulantExpansion

open AnnealedGraph FreshTypeAveraging

variable {S : Type*} [MetricSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]

def exposureBound {I : Type*} [Fintype I] (M : CompactBJRModel S) : ℝ :=
  (Fintype.card I : ℝ) * ‖M.kernel.toContinuousMap‖

theorem exposure_le_bound {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (x : I → S) (y : S) : exposure M x y ≤ exposureBound (I := I) M := by
  unfold exposure exposureBound
  calc
    _ ≤ ∑ _i : I, ‖M.kernel.toContinuousMap‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (le_abs_self (M.kernel (x i) y)).trans
        (M.kernel.toContinuousMap.norm_coe_le_norm (x i,y))
    _ = _ := by simp

def exposureMoment {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (x : I → S) (j : ℕ) : ℝ := ∫ y, exposure M x y ^ j ∂M.mu

theorem exposureMoment_nonneg {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (x : I → S) (j : ℕ) : 0 ≤ exposureMoment M x j :=
  integral_nonneg (fun y ↦ pow_nonneg (exposure_nonneg M x y) j)

theorem exposureMoment_le {I : Type*} [Fintype I] (M : CompactBJRModel S)
    (x : I → S) (j : ℕ) : exposureMoment M x j ≤ exposureBound (I := I) M ^ j := by
  have hi := ((exposure_continuous M x).pow j).integrable_of_hasCompactSupport
    isClosed_closure.isCompact (μ := M.mu)
  have hm := integral_mono hi (integrable_const (exposureBound (I := I) M ^ j))
    (fun y ↦ pow_le_pow_left₀ (exposure_nonneg M x y) (exposure_le_bound M x y) j)
  simpa only [exposureMoment,integral_const,probReal_univ,smul_eq_mul,one_mul,Pi.pow_apply] using hm

@[simp] theorem exposureMoment_zero {I : Type*} [Fintype I]
    (M : CompactBJRModel S) (x : I → S) : exposureMoment M x 0 = 1 := by
  simp [exposureMoment]

@[simp] theorem exposureMoment_one {I : Type*} [Fintype I]
    (M : CompactBJRModel S) (x : I → S) : exposureMoment M x 1 = totalDegree M x := by
  simpa only [exposureMoment,pow_one] using integral_exposure M x

def exposureVariance {I : Type*} [Fintype I] (M : CompactBJRModel S) (x : I → S) : ℝ :=
  exposureMoment M x 2 - totalDegree M x ^ 2

def exposureThirdCumulant {I : Type*} [Fintype I] (M : CompactBJRModel S) (x : I → S) : ℝ :=
  exposureMoment M x 3 - 3 * totalDegree M x * exposureMoment M x 2 + 2 * totalDegree M x ^ 3

/-- The normalized odds have a zero-hazard convention compatible with the
sharp interval bounds needed for the paper's finite-n edge correction. -/
theorem normalizedOdds_bounds {z : ℝ} (hz : 0 ≤ z) :
    1 ≤ normalizedOdds z ∧ normalizedOdds z ≤ Real.exp z := by
  by_cases hzero : z = 0
  · simp [hzero]
  · have hpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hzero)
    have hlo := Real.add_one_le_exp z
    have hneg := Real.add_one_le_exp (-z)
    have hmul := mul_le_mul_of_nonneg_left hneg (Real.exp_pos z).le
    have hexp : Real.exp z * Real.exp (-z) = 1 := by rw [← Real.exp_add]; simp
    rw [hexp] at hmul
    simp only [normalizedOdds,if_neg hzero]
    constructor
    · apply (le_div_iff₀ hpos).mpr
      linarith
    · apply (div_le_iff₀ hpos).mpr
      nlinarith only [hmul]

theorem normalizedOdds_pos {z : ℝ} (hz : 0 ≤ z) : 0 < normalizedOdds z :=
  lt_of_lt_of_le zero_lt_one (normalizedOdds_bounds hz).1

theorem log_normalizedOdds_bounds {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ Real.log (normalizedOdds z) ∧ Real.log (normalizedOdds z) ≤ z := by
  have hb := normalizedOdds_bounds hz
  constructor
  · exact Real.log_nonneg hb.1
  · have h := Real.log_le_log (normalizedOdds_pos hz) hb.2
    simpa only [Real.log_exp] using h

/-- Exact logarithmic bookkeeping of the finite present-edge correction. -/
theorem log_normalizedOdds_product_bounds {J : Type*} [Fintype J]
    (z : J → ℝ) (hz : ∀ j, 0 ≤ z j) :
    0 ≤ Real.log (∏ j, normalizedOdds (z j)) ∧
      Real.log (∏ j, normalizedOdds (z j)) ≤ ∑ j, z j := by
  rw [Real.log_prod (fun j _ ↦ (normalizedOdds_pos (hz j)).ne')]
  exact ⟨Finset.sum_nonneg (fun j _ ↦ (log_normalizedOdds_bounds (hz j)).1),
    Finset.sum_le_sum (fun j _ ↦ (log_normalizedOdds_bounds (hz j)).2)⟩

/-- The literal isolation factor is within the exposure bound of one.
This estimate supplies a uniform domain for the logarithmic Taylor series. -/
theorem isolationFactor_sub_one_bound {I : Type*} [Fintype I]
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (x : I → S) :
    |isolationFactor M t n x - 1| ≤ t * exposureBound (I := I) M / (n : ℝ) := by
  have hlo : 1 - t * exposureBound (I := I) M / (n : ℝ) ≤ isolationFactor M t n x := by
    have hi := freshAbsence_integrable M t n x
    have hp (y : S) : 1 - t * exposure M x y / (n : ℝ) ≤ freshAbsence M t n x y := by
      simpa only [freshAbsence,neg_mul,neg_div] using
        Real.one_sub_le_exp_neg (t * exposure M x y / (n : ℝ))
    have hm := integral_mono (integrable_const (1 - t * exposureBound (I := I) M / (n : ℝ))) hi
      (fun y ↦ (show 1 - t * exposureBound (I := I) M / (n : ℝ) ≤
          1 - t * exposure M x y / (n : ℝ) from by
        have h := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (exposure_le_bound M x y) ht) (Nat.cast_nonneg n)
        linarith).trans (hp y))
    simpa only [isolationFactor,freshAbsence,neg_mul,neg_div,
      integral_const,probReal_univ,smul_eq_mul,one_mul] using hm
  have hup := isolationFactor_le_one M ht n x
  rw [abs_of_nonpos (sub_nonpos.mpr hup)]
  linarith

/-- Uniform fourth-order error for the raw literal fresh-type Laplace
factor.  In particular, no conditional-moment interface is assumed. -/
theorem isolationFactor_cubic_raw_bound {I : Type*} [Fintype I]
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (x : I → S)
    (hsmall : t * exposureBound (I := I) M / (n : ℝ) ≤ 1) :
    |isolationFactor M t n x - (1 - (t / (n : ℝ)) * exposureMoment M x 1 +
      (t / (n : ℝ)) ^ 2 * exposureMoment M x 2 / 2 -
      (t / (n : ℝ)) ^ 3 * exposureMoment M x 3 / 6)| ≤
      (t * exposureBound (I := I) M / (n : ℝ)) ^ 4 := by
  let a : ℝ := t / (n : ℝ)
  let B : ℝ := exposureBound (I := I) M
  have ha : 0 ≤ a := div_nonneg ht (Nat.cast_nonneg n)
  have hB : 0 ≤ B := by unfold B exposureBound; positivity
  have hab : a * B ≤ 1 := by simpa only [a,B,div_mul_eq_mul_div] using hsmall
  have hp : (∫ y, 1 - a * exposure M x y + a ^ 2 * exposure M x y ^ 2 / 2 -
      a ^ 3 * exposure M x y ^ 3 / 6 ∂M.mu) =
      1 - a * exposureMoment M x 1 + a ^ 2 * exposureMoment M x 2 / 2 -
      a ^ 3 * exposureMoment M x 3 / 6 := by
    have hj (j : ℕ) : Integrable (fun y ↦ exposure M x y ^ j) M.mu :=
      ((exposure_continuous M x).pow j).integrable_of_hasCompactSupport isClosed_closure.isCompact
    have hj1 : Integrable (fun y ↦ a * exposure M x y) M.mu :=
      (exposure_integrable M x).const_mul a
    have hj2 : Integrable (fun y ↦ a ^ 2 * exposure M x y ^ 2 / 2) M.mu :=
      ((hj 2).const_mul (a ^ 2)).div_const 2
    have hj3 : Integrable (fun y ↦ a ^ 3 * exposure M x y ^ 3 / 6) M.mu :=
      ((hj 3).const_mul (a ^ 3)).div_const 6
    have he1 : (∫ y, 1 - a * exposure M x y + a ^ 2 * exposure M x y ^ 2 / 2 -
        a ^ 3 * exposure M x y ^ 3 / 6 ∂M.mu) =
        (∫ y, 1 - a * exposure M x y + a ^ 2 * exposure M x y ^ 2 / 2 ∂M.mu) -
          (∫ y, a ^ 3 * exposure M x y ^ 3 / 6 ∂M.mu) :=
      integral_sub (((integrable_const 1).sub hj1).add hj2) hj3
    have he2 : (∫ y, 1 - a * exposure M x y + a ^ 2 * exposure M x y ^ 2 / 2 ∂M.mu) =
        (∫ y, 1 - a * exposure M x y ∂M.mu) +
          (∫ y, a ^ 2 * exposure M x y ^ 2 / 2 ∂M.mu) :=
      integral_add ((integrable_const 1).sub hj1) hj2
    have he3 : (∫ y, 1 - a * exposure M x y ∂M.mu) =
        (∫ _y : S, (1 : ℝ) ∂M.mu) - (∫ y, a * exposure M x y ∂M.mu) :=
      integral_sub (integrable_const 1) hj1
    rw [he1,he2,he3]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,
      integral_const_mul,integral_div,exposureMoment,pow_one]
  have hbound (y : S) :
      |freshAbsence M t n x y - (1 - a * exposure M x y +
        a ^ 2 * exposure M x y ^ 2 / 2 - a ^ 3 * exposure M x y ^ 3 / 6)| ≤ (a * B)^4 := by
    have hZ := exposure_nonneg M x y
    have hz : |-(a * exposure M x y)| ≤ 1 := by
      rw [abs_neg,abs_of_nonneg (mul_nonneg ha hZ)]
      exact (mul_le_mul_of_nonneg_left (exposure_le_bound M x y) ha).trans hab
    have he := Real.exp_bound hz (n := 4) (by decide)
    norm_num [Finset.sum_range_succ] at he
    rw [abs_of_nonneg ha,abs_of_nonneg hZ] at he
    have hpow : |-(a * exposure M x y)| ^ 4 ≤ (a * B)^4 := by
      rw [abs_neg,abs_of_nonneg (mul_nonneg ha hZ)]
      exact pow_le_pow_left₀ (mul_nonneg ha hZ)
        (mul_le_mul_of_nonneg_left (exposure_le_bound M x y) ha) 4
    unfold freshAbsence
    rw [show -t * exposure M x y / (n : ℝ) = -(a * exposure M x y) by dsimp [a]; ring]
    have hexpr : 1 - a * exposure M x y + a^2 * exposure M x y^2/2 -
        a^3 * exposure M x y^3/6 =
        1 + (-(a * exposure M x y)) + (-(a * exposure M x y))^2/2 +
          (-(a * exposure M x y))^3/6 := by ring
    rw [hexpr]
    rw [abs_neg,abs_of_nonneg (mul_nonneg ha hZ)] at hpow
    have hr : (a * exposure M x y) ^ 4 * (5 / 96) ≤ (a * B)^4 := by
      nlinarith only [hpow,pow_nonneg (mul_nonneg ha hZ) 4]
    simpa only [neg_sq] using he.trans hr
  unfold isolationFactor
  rw [← hp,← integral_sub (freshAbsence_integrable M t n x)
    (by
      apply Continuous.integrable_of_hasCompactSupport _ isClosed_closure.isCompact
      have hc := exposure_continuous M x
      fun_prop)]
  have hnorm := norm_integral_le_of_norm_le_const (μ := M.mu)
    (f := fun y ↦ freshAbsence M t n x y - (1 - a * exposure M x y +
      a ^ 2 * exposure M x y ^ 2 / 2 - a ^ 3 * exposure M x y ^ 3 / 6)) (C := (a * B)^4)
    (Filter.Eventually.of_forall (fun y ↦ by simpa only [Real.norm_eq_abs] using hbound y))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one,a,B,div_mul_eq_mul_div] using hnorm

/-- Cubic logarithm approximation on a fixed uniform neighbourhood of one. -/
theorem log_cubic_bound {y b : ℝ} (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 2)
    (hy : |y| ≤ b) :
    |Real.log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3)| ≤ 2 * b ^ 4 := by
  have hsmall : |-y| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hsmall 3
  norm_num [Finset.sum_range_succ] at h
  have hd : 0 < 1 - |y| := by linarith
  have hp : |y| ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ (abs_nonneg y) hy 4
  have hr : |y| ^ 4 / (1 - |y|) ≤ 2 * b ^ 4 := by
    apply (div_le_iff₀ hd).mpr
    have hhalf : 1 / 2 ≤ 1 - |y| := by linarith
    nlinarith only [hp,mul_le_mul_of_nonneg_left hhalf (pow_nonneg hb 4)]
  have he : (-y + y ^ 2 / 2 + (-y) ^ 3 / 3) + Real.log (1 + y) =
      Real.log (1 + y) - (y - y ^ 2 / 2 + y ^ 3 / 3) := by
    ring
  rw [he] at h
  exact h.trans hr

/-- Polynomial conversion from raw moments to cumulants, with a proved
fourth-order error rather than an expansion assumption. -/
theorem cubic_moment_conversion_bound {y u v w b : ℝ}
    (hb : 0 ≤ b) (hbsmall : b ≤ 1)
    (hy : |y| ≤ b) (hu : 0 ≤ u) (hub : u ≤ b)
    (hv : 0 ≤ v) (hvb : v ≤ b ^ 2 / 2)
    (hw : 0 ≤ w) (hwb : w ≤ b ^ 3 / 6)
    (herr : |y - (-u + v - w)| ≤ b ^ 4) :
    |(y - y ^ 2 / 2 + y ^ 3 / 3) -
      (-u + v - w - u ^ 2 / 2 + u * v - u ^ 3 / 3)| ≤ 7 * b ^ 4 := by
  let δ := y - (-u + v - w)
  let s := y + u
  have hb2 : b ^ 2 ≤ b := by nlinarith
  have hb3 : b ^ 3 ≤ b ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hb2 hb]
  have hb4 : b ^ 4 ≤ b ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hb3 hb]
  have hd : |δ| ≤ b ^ 4 := herr
  have hs : |s| ≤ 2 * b ^ 2 := by
    have he : s = v - w + δ := by dsimp [s,δ]; ring
    rw [he]
    have ht := (abs_add_le (v-w) δ).trans
      (add_le_add (abs_sub v w) hd)
    rw [abs_of_nonneg hv,abs_of_nonneg hw] at ht
    nlinarith only [ht,hvb,hwb,hb3,hb4]
  have hdw : |δ - w| ≤ 2 * b ^ 3 := by
    have ht := (abs_sub δ w).trans (add_le_add hd (le_refl (|w|)))
    rw [abs_of_nonneg hw] at ht
    nlinarith only [ht,hwb,hb4,pow_nonneg hb 3]
  have hy2 : |y ^ 2| ≤ b ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hu2 : |u ^ 2| ≤ b ^ 2 := by
    rw [abs_pow,abs_of_nonneg hu]
    exact pow_le_pow_left₀ hu hub 2
  have huy : |u * y| ≤ b ^ 2 := by
    rw [abs_mul,abs_of_nonneg hu]
    simpa only [pow_two] using mul_le_mul hub hy (abs_nonneg y) hb
  have hquad : |y ^ 2 - u * y + u ^ 2| ≤ 3 * b ^ 2 := by
    have ht := (abs_add_le (y^2-u*y) (u^2)).trans
      (add_le_add (abs_sub (y^2) (u*y)) (le_refl (|u^2|)))
    linarith
  have hterm1 : |u * (δ-w)| ≤ 2 * b ^ 4 := by
    rw [abs_mul,abs_of_nonneg hu]
    have ht := mul_le_mul hub hdw (abs_nonneg (δ-w)) hb
    nlinarith only [ht]
  have hterm2 : |s ^ 2 / 2| ≤ 2 * b ^ 4 := by
    rw [abs_div,abs_pow]
    norm_num
    have ht := pow_le_pow_left₀ (abs_nonneg s) hs 2
    rw [sq_abs] at ht
    nlinarith only [ht]
  have hterm3 : |s * (y^2-u*y+u^2) / 3| ≤ 2 * b ^ 4 := by
    rw [abs_div,abs_mul]
    norm_num
    have ht := mul_le_mul hs hquad (abs_nonneg _) (by positivity)
    nlinarith only [ht]
  have he : (y-y^2/2+y^3/3)-(-u+v-w-u^2/2+u*v-u^3/3) =
      δ + u*(δ-w) - s^2/2 + s*(y^2-u*y+u^2)/3 := by dsimp [δ,s]; ring
  rw [he]
  have ht := (abs_add_le (δ + u*(δ-w) - s^2/2) (s*(y^2-u*y+u^2)/3)).trans
    (add_le_add ((abs_sub (δ+u*(δ-w)) (s^2/2)).trans
      (add_le_add (abs_add_le δ (u*(δ-w))) (le_refl (|s^2/2|))))
      (le_refl (|s*(y^2-u*y+u^2)/3|)))
  linarith

/-- The paper's cubic cumulant expansion, proved for the literal fresh
isolation factor with a uniform error controlled only by the actual kernel. -/
theorem log_isolationFactor_cumulant_bound {I : Type*} [Fintype I]
    (M : CompactBJRModel S) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (x : I → S)
    (hsmall : t * exposureBound (I := I) M / (n : ℝ) ≤ 1 / 2) :
    |Real.log (isolationFactor M t n x) + (t / (n : ℝ)) * totalDegree M x -
      (t / (n : ℝ)) ^ 2 * exposureVariance M x / 2 +
      (t / (n : ℝ)) ^ 3 * exposureThirdCumulant M x / 6| ≤
        9 * (t * exposureBound (I := I) M / (n : ℝ)) ^ 4 := by
  let a : ℝ := t / (n : ℝ)
  let B : ℝ := exposureBound (I := I) M
  let b : ℝ := a * B
  let y : ℝ := isolationFactor M t n x - 1
  let u : ℝ := a * exposureMoment M x 1
  let v : ℝ := a ^ 2 * exposureMoment M x 2 / 2
  let w : ℝ := a ^ 3 * exposureMoment M x 3 / 6
  have ha : 0 ≤ a := div_nonneg ht (Nat.cast_nonneg n)
  have hB : 0 ≤ B := by unfold B exposureBound; positivity
  have hb : 0 ≤ b := mul_nonneg ha hB
  have hbsmall : b ≤ 1 / 2 := by simpa only [b,a,B,div_mul_eq_mul_div] using hsmall
  have hy : |y| ≤ b := by
    simpa only [y,b,a,B,div_mul_eq_mul_div] using isolationFactor_sub_one_bound M t ht n x
  have hu : 0 ≤ u := mul_nonneg ha (exposureMoment_nonneg M x 1)
  have hub : u ≤ b := by
    have h := mul_le_mul_of_nonneg_left (exposureMoment_le M x 1) ha
    simpa only [pow_one,u,b,B] using h
  have hv : 0 ≤ v := div_nonneg (mul_nonneg (pow_nonneg ha 2) (exposureMoment_nonneg M x 2)) (by norm_num)
  have hvb : v ≤ b ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left (exposureMoment_le M x 2) (pow_nonneg ha 2)
    dsimp [v,b,B]
    nlinarith only [h]
  have hw : 0 ≤ w := div_nonneg (mul_nonneg (pow_nonneg ha 3) (exposureMoment_nonneg M x 3)) (by norm_num)
  have hwb : w ≤ b ^ 3 / 6 := by
    have h := mul_le_mul_of_nonneg_left (exposureMoment_le M x 3) (pow_nonneg ha 3)
    dsimp [w,b,B]
    nlinarith only [h]
  have herr : |y - (-u + v - w)| ≤ b ^ 4 := by
    have h := isolationFactor_cubic_raw_bound M t ht n x (by linarith)
    have he : y - (-u + v - w) = isolationFactor M t n x -
        (1 - a * exposureMoment M x 1 + a ^ 2 * exposureMoment M x 2 / 2 -
          a ^ 3 * exposureMoment M x 3 / 6) := by dsimp [y,u,v,w]; ring
    rw [he]
    simpa only [b,a,B,div_mul_eq_mul_div] using h
  have hl := log_cubic_bound hb hbsmall hy
  have hc := cubic_moment_conversion_bound hb (by linarith) hy hu hub hv hvb hw hwb herr
  have he : Real.log (1+y) - (-u+v-w-u^2/2+u*v-u^3/3) =
      (Real.log (1+y) - (y-y^2/2+y^3/3)) +
        ((y-y^2/2+y^3/3)-(-u+v-w-u^2/2+u*v-u^3/3)) := by ring
  have hsum : |Real.log (1+y) - (-u+v-w-u^2/2+u*v-u^3/3)| ≤ 9*b^4 := by
    rw [he]
    exact (abs_add_le _ _).trans (by linarith)
  have hlog : 1+y = isolationFactor M t n x := by dsimp [y]; ring
  rw [hlog] at hsum
  have hpoly : Real.log (isolationFactor M t n x) - (-u+v-w-u^2/2+u*v-u^3/3) =
      Real.log (isolationFactor M t n x) + a * totalDegree M x -
        a ^ 2 * exposureVariance M x / 2 + a ^ 3 * exposureThirdCumulant M x / 6 := by
    dsimp [u,v,w,exposureVariance,exposureThirdCumulant]
    rw [exposureMoment_one]
    ring
  rw [hpoly] at hsum
  simpa only [b,a,B,div_mul_eq_mul_div] using hsum

end PerronWright.FreshTypeCumulantExpansion
