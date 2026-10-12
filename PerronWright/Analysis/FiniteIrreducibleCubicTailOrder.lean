import PerronWright.Analysis.FiniteIrreducibleCubicProfileAnalytic
import PerronWright.Enumeration.PositiveSurplusCubicFixedDegreeAnalytic
import PerronWright.Analysis.FiniteIrreduciblePathSeriesBounds
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Vanishing order of the positive-surplus cubic profile tail

At fixed positive surplus `ell`, the degree-`d` cubic profile coefficient
contains `2 * ell + d` profile factors.  The binomial--geometric majorant
therefore shows that the tail beginning at degree `N` is
`O(‖w‖ ^ (2 * ell + N))` along every profile germ which is `O(‖w‖)`.

The proof sums the existing coefficient majorant directly.  The binomial
factor is bounded by `2` to its upper argument and the shifted tail is then
dominated by one geometric series; no uniform-convergence hypothesis is
introduced.
-/

open scoped Classical Topology BigOperators
open Asymptotics

noncomputable section

namespace PerronWright.FiniteIrreducibleKernelAmplitude
open GraphCore

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- A one-variable analytic profile with zero constant coefficient is
linearly bounded at the origin. -/
private theorem cubicProfile_isBigO_norm_of_coeff_zero
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    {tau : ℂ → A}
    {p : FormalMultilinearSeries ℂ ℂ A}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    tau =O[𝓝 (0 : ℂ)] (fun w : ℂ ↦ ‖w‖) := by
  have hpartial (w : ℂ) : p.partialSum 1 w = 0 := by
    change (∑ k ∈ Finset.range 1, p k (fun _ : Fin k ↦ w)) = 0
    rw [Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [zero_add,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff, hp0, smul_zero]
  have h := hp.isBigO_sub_partialSum_pow 1
  simpa only [zero_add, hpartial, sub_zero, pow_one, norm_norm] using h

/-- If the profile germ is linearly bounded, then deleting its first `N`
literal cubic degrees leaves a tail of order at least `2 * ell + N`. -/
theorem positiveSurplusCubicProfileSeries_sub_partialSum_isBigO_of_isBigO
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) (N : ℕ)
    {tau : ℂ → C(S, ℂ)}
    (htau : tau =O[𝓝 (0 : ℂ)] (fun w : ℂ ↦ ‖w‖)) :
    (fun w : ℂ ↦
      positiveSurplusCubicProfileSeries M ell (tau w) -
        ∑ d ∈ Finset.range N,
          positiveSurplusCubicAdmissibleProfileCoefficient M.bjrModel (tau w) ell d)
      =O[𝓝 (0 : ℂ)] (fun w : ℂ ↦ ‖w‖ ^ (2 * ell + N)) := by
  obtain ⟨A, hA, hcoeff⟩ :=
    exists_positiveSurplusCubicAdmissibleProfileCoefficient_norm_bound
      M hM hell
  obtain ⟨c, hc⟩ := htau.isBigOWith
  let C : ℝ := max 1 c
  have hCpos : 0 < C :=
    zero_lt_one.trans_le (le_max_left 1 c)
  have hcC : c ≤ C := le_max_right 1 c
  have hlinear : ∀ᶠ w in 𝓝 (0 : ℂ), ‖tau w‖ ≤ C * ‖w‖ := by
    filter_upwards [hc.bound] with w hw
    have hw' : ‖tau w‖ ≤ c * ‖w‖ := by simpa using hw
    exact hw'.trans (mul_le_mul_of_nonneg_right hcC (norm_nonneg w))

  let m : ℕ := 3 * ell - 1
  let b : ℕ := 2 * ell + N
  apply isBigO_iff.mpr
  refine ⟨2 * A * (2 : ℝ) ^ (N + m) * C ^ b, ?_⟩
  filter_upwards [hlinear,
    Metric.ball_mem_nhds (0 : ℂ) (by positivity : 0 < 1 / (4 * C))]
      with w hwlinear hwball
  let q : ℝ := C * ‖w‖
  have hq : 0 ≤ q := mul_nonneg hCpos.le (norm_nonneg w)
  have hqquarter : q < 1 / 4 := by
    have hwball' : ‖w‖ < 1 / (4 * C) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hwball
    calc
      q < C * (1 / (4 * C)) :=
        mul_lt_mul_of_pos_left hwball' hCpos
      _ = 1 / 4 := by field_simp [hCpos.ne']
  have hq1 : q < 1 := hqquarter.trans (by norm_num)
  have hratio0 : 0 ≤ 2 * q := mul_nonneg (by norm_num) hq
  have hratiohalf : 2 * q < 1 / 2 := by linarith
  have hratio1 : 2 * q < 1 := hratiohalf.trans (by norm_num)
  have hprofile : ‖tau w‖ ≤ q := by
    simpa only [q] using hwlinear

  let f : ℕ → ℂ := fun d ↦
    positiveSurplusCubicAdmissibleProfileCoefficient M.bjrModel (tau w) ell d
  have hterm (d : ℕ) :
      ‖f d‖ ≤
        A * ((d + m).choose m : ℝ) * q ^ (2 * ell + d) := by
    simpa only [f, m] using hcoeff (tau w) q hq hprofile d
  have hsumNorm : Summable (fun d : ℕ ↦ ‖f d‖) := by
    simpa only [f] using
      summable_norm_positiveSurplusCubicAdmissibleProfileCoefficient
        M hM hell (tau w) hq hq1 hprofile
  have hsum : Summable f := hsumNorm.of_norm
  have htailIdentity :
      positiveSurplusCubicProfileSeries M ell (tau w) -
          ∑ d ∈ Finset.range N, f d =
        ∑' n : ℕ, f (n + N) := by
    have hsplit := hsum.sum_add_tsum_nat_add N
    change (∑' d : ℕ, f d) - ∑ d ∈ Finset.range N, f d =
      ∑' n : ℕ, f (n + N)
    rw [← hsplit]
    abel

  let D : ℝ := A * (2 : ℝ) ^ (N + m)
  have hD : 0 ≤ D :=
    mul_nonneg hA (pow_nonneg (by norm_num) _)
  have hchoose (n : ℕ) :
      (((n + N + m).choose m : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (n + N + m) := by
    exact_mod_cast Nat.choose_le_two_pow (n + N + m) m
  have hshift (n : ℕ) :
      ‖f (n + N)‖ ≤ (D * q ^ b) * (2 * q) ^ n := by
    calc
      ‖f (n + N)‖ ≤
          A * (((n + N) + m).choose m : ℝ) *
            q ^ (2 * ell + (n + N)) := hterm (n + N)
      _ ≤ A * (2 : ℝ) ^ ((n + N) + m) *
            q ^ (2 * ell + (n + N)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hchoose n) hA)
          (pow_nonneg hq _)
      _ = (D * q ^ b) * (2 * q) ^ n := by
        dsimp only [D, b]
        simp only [pow_add, mul_pow]
        ring
  have hmajor : HasSum
      (fun n : ℕ ↦ (D * q ^ b) * (2 * q) ^ n)
      ((D * q ^ b) * (1 - 2 * q)⁻¹) :=
    (hasSum_geometric_of_lt_one hratio0 hratio1).mul_left
      (D * q ^ b)
  have htailBound :
      ‖∑' n : ℕ, f (n + N)‖ ≤
        (D * q ^ b) * (1 - 2 * q)⁻¹ :=
    tsum_of_norm_bounded hmajor hshift
  have hinv : (1 - 2 * q)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ (sub_pos_of_lt hratio1) two_pos]
    linarith
  have htailFinal :
      ‖positiveSurplusCubicProfileSeries M ell (tau w) -
          ∑ d ∈ Finset.range N,
            positiveSurplusCubicAdmissibleProfileCoefficient M.bjrModel (tau w) ell d‖ ≤
        (2 * A * (2 : ℝ) ^ (N + m) * C ^ b) * ‖w‖ ^ b := by
    change ‖positiveSurplusCubicProfileSeries M ell (tau w) -
      ∑ d ∈ Finset.range N, f d‖ ≤ _
    rw [htailIdentity]
    calc
      ‖∑' n : ℕ, f (n + N)‖ ≤
          (D * q ^ b) * (1 - 2 * q)⁻¹ := htailBound
      _ ≤ (D * q ^ b) * 2 := by
        exact mul_le_mul_of_nonneg_left hinv
          (mul_nonneg hD (pow_nonneg hq _))
      _ = (2 * A * (2 : ℝ) ^ (N + m) * C ^ b) * ‖w‖ ^ b := by
        dsimp only [D, q]
        simp only [mul_pow]
        ring
  simpa only [b, norm_pow, Real.norm_eq_abs, abs_norm] using htailFinal

/-- In particular, an analytic profile with zero constant coefficient has
the preceding tail order.  This is the form used by the Taylor-coefficient
identification layer. -/
theorem positiveSurplusCubicProfileSeries_sub_partialSum_isBigO
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {ell : ℕ} (hell : 0 < ell) (N : ℕ)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    (fun w : ℂ ↦
      positiveSurplusCubicProfileSeries M ell (tau w) -
        ∑ d ∈ Finset.range N,
          positiveSurplusCubicAdmissibleProfileCoefficient M.bjrModel (tau w) ell d)
      =O[𝓝 (0 : ℂ)] (fun w : ℂ ↦ ‖w‖ ^ (2 * ell + N)) :=
  positiveSurplusCubicProfileSeries_sub_partialSum_isBigO_of_isBigO
    M hM hell N (cubicProfile_isBigO_norm_of_coeff_zero hp hp0)

end PerronWright.FiniteIrreducibleKernelAmplitude
