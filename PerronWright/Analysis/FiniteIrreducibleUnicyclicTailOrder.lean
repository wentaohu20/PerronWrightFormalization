import PerronWright.Enumeration.UnicyclicFiniteLengthSumAnalytic
import PerronWright.Analysis.FiniteIrreducibleJointSimpleCycleEGF

/-!
# Vanishing order of the long-cycle tail

If the rooted-tree profile has zero constant term, then it is `O(w)` at the
origin.  The length-`n+3` cycle term is bounded by a constant times
`‖tau(w)‖^(n+3)`; summing from `n = N` gives an `O(w^(N+3))` tail.
-/

open scoped Classical Topology
open Asymptotics
noncomputable section

namespace PerronWright
namespace FiniteIrreducibleJointSimpleCycleTail

open JointSimpleCycleEGF FiniteIrreducibleJointSimpleCycleEGF

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

/-- A one-variable analytic profile whose constant coefficient vanishes is
linearly bounded at the origin. -/
private theorem profile_isBigO_norm_of_coeff_zero
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

/-- The part of the full simple-cycle series contributed by cycle lengths at
least `N+3` vanishes to order at least `N+3` at the origin. -/
theorem profileSimpleCycleSeries_sub_partialSum_isBigO
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (N : ℕ)
    {tau : ℂ → C(S, ℂ)}
    {p : FormalMultilinearSeries ℂ ℂ C(S, ℂ)}
    (hp : HasFPowerSeriesAt tau p 0) (hp0 : p.coeff 0 = 0) :
    (fun w : ℂ ↦
      profileSimpleCycleSeries M.bjrModel (tau w) -
        ∑ n ∈ Finset.range N, profileSimpleCycleTerm M.bjrModel (tau w) n)
      =O[𝓝 (0 : ℂ)] (fun w : ℂ ↦ ‖w‖ ^ (N + 3)) := by
  obtain ⟨m, hm, hmu'⟩ := isCompact_univ.exists_forall_le'
    (M.continuousPerronFunction hM).continuous.continuousOn
    (fun x _ => M.perronFunction_pos hM x)
  have hmu : ∀ x, m ≤ M.continuousPerronFunction hM x :=
    fun x => hmu' x (Set.mem_univ x)
  let A : ℝ := ‖M.bjrModel.kernel.toContinuousMap‖ *
    ‖M.bjrModel.kernel.complexActionCLM M.bjrModel.mu‖ *
    (‖M.continuousPerronFunction hM‖ / m)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity

  obtain ⟨c, hc⟩ :=
    (profile_isBigO_norm_of_coeff_zero hp hp0).isBigOWith
  let C : ℝ := max 1 c
  have hCpos : 0 < C := by
    exact zero_lt_one.trans_le (le_max_left 1 c)
  have hcC : c ≤ C := le_max_right 1 c
  have hlinear : ∀ᶠ w in 𝓝 (0 : ℂ), ‖tau w‖ ≤ C * ‖w‖ := by
    filter_upwards [hc.bound] with w hw
    have hw' : ‖tau w‖ ≤ c * ‖w‖ := by simpa using hw
    exact hw'.trans (mul_le_mul_of_nonneg_right hcC (norm_nonneg w))

  apply isBigO_iff.mpr
  refine ⟨2 * A * C ^ (N + 3), ?_⟩
  filter_upwards [hlinear,
    Metric.ball_mem_nhds (0 : ℂ) (by positivity : 0 < 1 / (2 * C))]
      with w hwlinear hwball
  let q : ℝ := C * ‖w‖
  have hq : 0 ≤ q := mul_nonneg hCpos.le (norm_nonneg w)
  have hqhalf : q < 1 / 2 := by
    have hwball' : ‖w‖ < 1 / (2 * C) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hwball
    calc
      q < C * (1 / (2 * C)) :=
        mul_lt_mul_of_pos_left hwball' hCpos
      _ = 1 / 2 := by field_simp [hCpos.ne']
  have hq1 : q < 1 := hqhalf.trans (by norm_num)
  have hprofile : ∀ x, ‖tau w x‖ ≤ q := by
    intro x
    exact (tau w).norm_coe_le_norm x |>.trans
      (by simpa only [q] using hwlinear)

  let f : ℕ → ℂ := fun n ↦ profileSimpleCycleTerm M.bjrModel (tau w) n
  have hterm (n : ℕ) : ‖f n‖ ≤ (A * q ^ 3) * q ^ n := by
    simpa only [f, A] using
      norm_profileSimpleCycleTerm_le M hM (tau w) q m hq hprofile hm hmu n
  have hsum : Summable f := by
    apply Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hq hq1).mul_left (A * q ^ 3))
    exact hterm
  have htailIdentity :
      profileSimpleCycleSeries M.bjrModel (tau w) - ∑ n ∈ Finset.range N, f n =
        ∑' n : ℕ, f (n + N) := by
    have hsplit := hsum.sum_add_tsum_nat_add N
    change (∑' n : ℕ, f n) - ∑ n ∈ Finset.range N, f n =
      ∑' n : ℕ, f (n + N)
    rw [← hsplit]
    abel

  have hshift (n : ℕ) :
      ‖f (n + N)‖ ≤ (A * q ^ (N + 3)) * q ^ n := by
    calc
      ‖f (n + N)‖ ≤ (A * q ^ 3) * q ^ (n + N) := hterm (n + N)
      _ = (A * q ^ (N + 3)) * q ^ n := by
        simp only [pow_add]
        ring
  have hmajor : HasSum
      (fun n : ℕ ↦ (A * q ^ (N + 3)) * q ^ n)
      ((A * q ^ (N + 3)) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq hq1).mul_left
      (A * q ^ (N + 3))
  have htailBound :
      ‖∑' n : ℕ, f (n + N)‖ ≤
        (A * q ^ (N + 3)) * (1 - q)⁻¹ :=
    tsum_of_norm_bounded hmajor hshift
  have hinv : (1 - q)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_le_comm₀ (sub_pos_of_lt hq1) two_pos]
    linarith
  have htailFinal :
      ‖profileSimpleCycleSeries M.bjrModel (tau w) -
          ∑ n ∈ Finset.range N, profileSimpleCycleTerm M.bjrModel (tau w) n‖ ≤
        (2 * A * C ^ (N + 3)) * ‖w‖ ^ (N + 3) := by
    change ‖profileSimpleCycleSeries M.bjrModel (tau w) -
      ∑ n ∈ Finset.range N, f n‖ ≤ _
    rw [htailIdentity]
    calc
      ‖∑' n : ℕ, f (n + N)‖ ≤
          (A * q ^ (N + 3)) * (1 - q)⁻¹ := htailBound
      _ ≤ (A * q ^ (N + 3)) * 2 := by
        exact mul_le_mul_of_nonneg_left hinv
          (mul_nonneg hA (pow_nonneg hq _))
      _ = (2 * A * C ^ (N + 3)) * ‖w‖ ^ (N + 3) := by
        simp only [q, mul_pow]
        ring
  simpa only [norm_pow, Real.norm_eq_abs, abs_norm] using htailFinal

end FiniteIrreducibleJointSimpleCycleTail
end PerronWright
