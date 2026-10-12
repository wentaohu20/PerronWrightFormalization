import PerronWright.Analysis.FiniteIrreducibleEndpointSum
import PerronWright.Enumeration.RootedTreeClosedDisk

/-! Closed-disk convergence and strict noncritical-circle majorization of the
literal finite irreducible rooted-tree series. The positive first two actual
coefficients, not primitivity of the kernel, break phase alignment. -/
open Filter
open scoped Classical Topology ENNReal NNReal
noncomputable section
namespace PerronWright
variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

private theorem FiniteIrreducibleModel.complexFiniteSum_norm_le_endpoint
    (M : FiniteIrreducibleModel S) {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖∑ i ∈ s,
        M.bjrModel.complexTypeRootedTreeFMS (k i) (fun _ : Fin (k i) => z)‖ ≤
      ‖∑ i ∈ s, PowerSeries.coeff (k i) M.bjrModel.typeRootedTreeEGF‖ := by
  classical
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro x
  calc
    ‖(∑ i ∈ s,
        M.bjrModel.complexTypeRootedTreeFMS (k i) (fun _ : Fin (k i) => z)) x‖
        ≤ ∑ i ∈ s,
            ‖(M.bjrModel.complexTypeRootedTreeFMS (k i)
              (fun _ : Fin (k i) => z)) x‖ := by
          simp only [ContinuousMap.sum_apply]
          exact norm_sum_le _ _
    _ = ∑ i ∈ s,
          ‖z‖ ^ (k i) * PowerSeries.coeff (k i) M.bjrModel.typeRootedTreeEGF x := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [M.bjrModel.complexTypeRootedTreeFMS_apply]
        simp only [ContinuousMap.smul_apply,
          continuousMapComplexifyRingHom_apply,
          TreeRealComplexBridge.complexify_apply, smul_eq_mul,
          norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (M.bjrModel.typeRootedTreeEGF_coeff_nonneg (k i) x)]
    _ ≤ ∑ i ∈ s, PowerSeries.coeff (k i) M.bjrModel.typeRootedTreeEGF x := by
        apply Finset.sum_le_sum
        intro i hi
        have hpow : ‖z‖ ^ (k i) ≤ 1 := by
          simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg z) hz (k i)
        exact mul_le_of_le_one_left
          (M.bjrModel.typeRootedTreeEGF_coeff_nonneg (k i) x) hpow
    _ = ‖(∑ i ∈ s,
          PowerSeries.coeff (k i) M.bjrModel.typeRootedTreeEGF) x‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · simp only [ContinuousMap.sum_apply]
        · simpa only [ContinuousMap.sum_apply] using
            (Finset.sum_nonneg fun i hi =>
              M.bjrModel.typeRootedTreeEGF_coeff_nonneg (k i) x)
    _ ≤ ‖∑ i ∈ s, PowerSeries.coeff (k i) M.bjrModel.typeRootedTreeEGF‖ :=
      (∑ i ∈ s, PowerSeries.coeff (k i) M.bjrModel.typeRootedTreeEGF).norm_coe_le_norm x

/-- The genuine complex rooted-tree terms are unconditionally summable at
every point of the closed unit disk.  This is a conditional comparison with
the endpoint `C(S,ℝ)` sum, not an assertion of norm-summability term by term.
-/
theorem FiniteIrreducibleModel.complexTypeRootedTreeFMS_summable_closedDisk
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {z : ℂ}
    (hz : ‖z‖ ≤ 1) :
    Summable (fun n : ℕ =>
      M.bjrModel.complexTypeRootedTreeFMS n (fun _ : Fin n => z)) := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp
    (M.typeRootedTreeEGF_hasSum_one hM).summable ε hε
  refine ⟨s, ?_⟩
  intro t hts
  exact (M.complexFiniteSum_norm_le_endpoint t id z hz).trans_lt
    (hs t hts)

/-- The canonical rooted-tree series is therefore represented by its actual
labelled-tree terms throughout the closed unit disk. -/
theorem FiniteIrreducibleModel.complexTypeRootedTreeFMS_hasSum_closedDisk
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) {z : ℂ}
    (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ =>
        M.bjrModel.complexTypeRootedTreeFMS n (fun _ : Fin n => z))
      (M.bjrModel.rootedTreeSeries z) := by
  unfold CompactBJRModel.rootedTreeSeries FormalMultilinearSeries.sum
  exact (M.complexTypeRootedTreeFMS_summable_closedDisk hM hz).hasSum

/-- Finite complex Taylor polynomial of the genuine rooted-tree series. -/
def FiniteIrreducibleModel.complexRootedTreePartialSum
    (M : FiniteIrreducibleModel S) (N : ℕ) (z : ℂ) : C(S, ℂ) :=
  ∑ n ∈ Finset.range N,
    M.bjrModel.complexTypeRootedTreeFMS n (fun _ : Fin n => z)

/-- Closed-disk tails are bounded uniformly by the genuine endpoint tail. -/
theorem FiniteIrreducibleModel.complexRootedTreeTail_norm_le_endpoint
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖M.bjrModel.rootedTreeSeries z - M.complexRootedTreePartialSum N z‖ ≤
      ‖(1 : C(S, ℝ)) - M.bjrModel.rootedTreePartialSum N 1‖ := by
  have hc := M.complexTypeRootedTreeFMS_hasSum_closedDisk hM hz
  have hr := M.typeRootedTreeEGF_hasSum_one hM
  have hctail : HasSum
      (fun n : ℕ => M.bjrModel.complexTypeRootedTreeFMS (n + N)
        (fun _ : Fin (n + N) => z))
      (M.bjrModel.rootedTreeSeries z - M.complexRootedTreePartialSum N z) := by
    simpa only [FiniteIrreducibleModel.complexRootedTreePartialSum] using
      (hasSum_nat_add_iff' N).mpr hc
  have hrtail : HasSum
      (fun n : ℕ => PowerSeries.coeff (n + N) M.bjrModel.typeRootedTreeEGF)
      ((1 : C(S, ℝ)) - M.bjrModel.rootedTreePartialSum N 1) := by
    simpa only [CompactBJRModel.rootedTreePartialSum, one_pow, one_smul] using
      (hasSum_nat_add_iff' N).mpr hr
  exact le_of_tendsto_of_tendsto' hctail.norm hrtail.norm fun s =>
    M.complexFiniteSum_norm_le_endpoint s (fun n => n + N) z hz

/-- The genuine complex Taylor polynomials converge uniformly on the closed
unit disk. -/
theorem FiniteIrreducibleModel.complexRootedTreePartialSum_tendstoUniformlyOn_closedDisk
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    TendstoUniformlyOn
      (fun N z => M.complexRootedTreePartialSum N z)
      M.bjrModel.rootedTreeSeries Filter.atTop {z : ℂ | ‖z‖ ≤ 1} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp
    (M.rootedTreePartialSum_tendsto_one hM)) ε hε
  filter_upwards [eventually_ge_atTop N] with n hn
  intro z hz
  rw [dist_eq_norm]
  refine (M.complexRootedTreeTail_norm_le_endpoint hM n hz).trans_lt ?_
  have hdist := hN n hn
  rw [dist_eq_norm] at hdist
  calc
    ‖(1 : C(S, ℝ)) - M.bjrModel.rootedTreePartialSum n 1‖ =
        ‖-(M.bjrModel.rootedTreePartialSum n 1 - 1)‖ := by
          congr 1
          abel
    _ = ‖M.bjrModel.rootedTreePartialSum n 1 - 1‖ := norm_neg _
    _ < ε := hdist

/-- Every genuine complex Taylor polynomial is continuous in the activity. -/
theorem FiniteIrreducibleModel.complexRootedTreePartialSum_continuous
    (M : FiniteIrreducibleModel S) (N : ℕ) :
    Continuous (M.complexRootedTreePartialSum N) := by
  unfold FiniteIrreducibleModel.complexRootedTreePartialSum
  fun_prop

/-- The actual rooted-tree series extends continuously to the closed unit
disk. -/
theorem FiniteIrreducibleModel.rootedTreeSeries_continuousOn_closedDisk
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    ContinuousOn M.bjrModel.rootedTreeSeries {z : ℂ | ‖z‖ ≤ 1} := by
  apply (M.complexRootedTreePartialSum_tendstoUniformlyOn_closedDisk hM).continuousOn
  exact (Filter.Eventually.of_forall fun N =>
    (M.complexRootedTreePartialSum_continuous N).continuousOn).frequently

/-- Applying the critical kernel to the positive one-vertex factor is
strictly positive at every type.  The proof compares it with a small
positive multiple of the proved Perron eigenfunction. -/
theorem FiniteIrreducibleModel.kernelAction_zeroTreeVertexFactor_pos
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (x : S) :
    0 < M.bjrModel.kernel.action M.bjrModel.mu M.bjrModel.zeroTreeVertexFactor x := by
  obtain ⟨c, hc, hcv⟩ := M.bjrModel.zeroTreeVertexFactor_uniform_pos
  let u := M.continuousPerronFunction hM
  let q : ℝ := c / (‖u‖ + 1)
  have hden : 0 < ‖u‖ + 1 := by positivity
  have hq : 0 < q := div_pos hc hden
  have hcomp : ∀ y, (q • u) y ≤ M.bjrModel.zeroTreeVertexFactor y := by
    intro y
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    calc
      q * u y ≤ q * ‖u‖ := by
        apply mul_le_mul_of_nonneg_left _ hq.le
        exact (le_abs_self (u y)).trans (u.norm_coe_le_norm y)
      _ ≤ q * (‖u‖ + 1) := by
        exact (mul_lt_mul_of_pos_left (lt_add_one ‖u‖) hq).le
      _ = c := by
        dsimp only [q]
        exact div_mul_cancel₀ c hden.ne'
      _ ≤ M.bjrModel.zeroTreeVertexFactor y := hcv y
  have hmono := M.bjrModel.kernel.realAction_mono M.bjrModel.mu (q • u)
    M.bjrModel.zeroTreeVertexFactor hcomp x
  have hfixed : M.bjrModel.kernel.action M.bjrModel.mu
      (M.continuousPerronFunction hM) = M.continuousPerronFunction hM :=
    M.continuousPerronFunction_fixed hM
  rw [M.bjrModel.kernel.action_smul, show u = M.continuousPerronFunction hM by rfl,
    hfixed, ContinuousMap.smul_apply, smul_eq_mul] at hmono
  exact (mul_pos hq (M.perronFunction_pos hM x)).trans_le hmono

theorem FiniteIrreducibleModel.typeRootedTreeEGF_coeff_two_pos
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (x : S) :
    0 < PowerSeries.coeff 2 M.bjrModel.typeRootedTreeEGF x := by
  rw [M.bjrModel.typeRootedTreeEGF_coeff_two, ContinuousMap.mul_apply]
  exact mul_pos (by
    rw [M.bjrModel.zeroTreeVertexFactor_apply]
    exact Real.exp_pos _) (M.kernelAction_zeroTreeVertexFactor_pos hM x)

/-- The first two genuine modes already exhibit a strict triangle defect at
every nontrivial point of the unit circle. -/
private theorem positive_unit_modes_norm_lt
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : ℂ}
    (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ‖(a : ℂ) * z + (b : ℂ) * z ^ 2‖ < a + b := by
  have hunitSq : z.re * z.re + z.im * z.im = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply, hz, one_pow] at h
    exact h
  have hrele : z.re ≤ 1 := by
    simpa only [hz] using Complex.re_le_norm z
  have hrene : z.re ≠ 1 := by
    intro hre
    have himsq := Complex.sq_norm_sub_sq_re z
    rw [hz, hre] at himsq
    have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
    apply hz1
    apply Complex.ext
    · simpa using hre
    · simpa using him
  have hrelt : z.re < 1 := lt_of_le_of_ne hrele hrene
  have hcoord :
      ‖(a : ℂ) + (b : ℂ) * z‖ ^ 2 =
        (a + b * z.re) ^ 2 + (b * z.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im,
      zero_add, Complex.mul_im, add_zero]
    ring
  have hdiff :
      (a + b) ^ 2 - ((a + b * z.re) ^ 2 + (b * z.im) ^ 2) =
        2 * a * b * (1 - z.re) := by
    calc
      (a + b) ^ 2 - ((a + b * z.re) ^ 2 + (b * z.im) ^ 2) =
          2 * a * b * (1 - z.re) +
            b ^ 2 * (1 - (z.re * z.re + z.im * z.im)) := by ring
      _ = 2 * a * b * (1 - z.re) := by rw [hunitSq]; ring
  have hsq :
      ‖(a : ℂ) + (b : ℂ) * z‖ ^ 2 < (a + b) ^ 2 := by
    rw [hcoord]
    exact sub_pos.mp (by
      rw [hdiff]
      exact mul_pos (mul_pos (mul_pos (by norm_num) ha) hb)
        (sub_pos.mpr hrelt))
  have hcore : ‖(a : ℂ) + (b : ℂ) * z‖ < a + b :=
    (sq_lt_sq₀ (norm_nonneg _) (add_pos ha hb).le).mp hsq
  calc
    ‖(a : ℂ) * z + (b : ℂ) * z ^ 2‖ =
        ‖z * ((a : ℂ) + (b : ℂ) * z)‖ := by
          congr 1
          ring
    _ = ‖z‖ * ‖(a : ℂ) + (b : ℂ) * z‖ := norm_mul _ _
    _ = ‖(a : ℂ) + (b : ℂ) * z‖ := by rw [hz, one_mul]
    _ < a + b := hcore

private theorem FiniteIrreducibleModel.complexTypeRootedTreeFMS_apply_norm_le_coeff
    (M : FiniteIrreducibleModel S) (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) (x : S) :
    ‖(M.bjrModel.complexTypeRootedTreeFMS n (fun _ : Fin n => z)) x‖ ≤
      PowerSeries.coeff n M.bjrModel.typeRootedTreeEGF x := by
  rw [M.bjrModel.complexTypeRootedTreeFMS_apply]
  simp only [ContinuousMap.smul_apply,
    continuousMapComplexifyRingHom_apply,
    TreeRealComplexBridge.complexify_apply, smul_eq_mul,
    norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (M.bjrModel.typeRootedTreeEGF_coeff_nonneg n x)]
  exact mul_le_of_le_one_left
    (M.bjrModel.typeRootedTreeEGF_coeff_nonneg n x)
    (by simpa only [one_pow] using
      pow_le_pow_left₀ (norm_nonneg z) hz n)

/-- At a fixed type, every finite set of genuine complex terms is bounded
by the same finite set of nonnegative endpoint coefficients. -/
private theorem FiniteIrreducibleModel.complexFiniteSum_apply_norm_le_endpoint
    (M : FiniteIrreducibleModel S) (s : Finset ℕ)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (x : S) :
    ‖∑ n ∈ s,
        (M.bjrModel.complexTypeRootedTreeFMS n (fun _ : Fin n => z)) x‖ ≤
      ∑ n ∈ s, PowerSeries.coeff n M.bjrModel.typeRootedTreeEGF x := by
  calc
    ‖∑ n ∈ s,
        (M.bjrModel.complexTypeRootedTreeFMS n (fun _ : Fin n => z)) x‖ ≤
        ∑ n ∈ s,
          ‖(M.bjrModel.complexTypeRootedTreeFMS n (fun _ : Fin n => z)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ s, PowerSeries.coeff n M.bjrModel.typeRootedTreeEGF x := by
      exact Finset.sum_le_sum fun n hn =>
        M.complexTypeRootedTreeFMS_apply_norm_le_coeff n hz x

/-- The same pointwise comparison for a finite natural tail. -/
private theorem FiniteIrreducibleModel.complexRootedTreePartialSum_sub_apply_norm_le_endpoint
    (M : FiniteIrreducibleModel S) (N K : ℕ) (hNK : N ≤ K)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (x : S) :
    ‖M.complexRootedTreePartialSum K z x -
        M.complexRootedTreePartialSum N z x‖ ≤
      M.bjrModel.rootedTreePartialSum K 1 x -
        M.bjrModel.rootedTreePartialSum N 1 x := by
  unfold FiniteIrreducibleModel.complexRootedTreePartialSum
  unfold CompactBJRModel.rootedTreePartialSum
  simp only [ContinuousMap.sum_apply, one_pow, one_smul]
  rw [← Finset.sum_Ico_eq_sub
      (fun n =>
        (M.bjrModel.complexTypeRootedTreeFMS n (fun _ : Fin n => z)) x) hNK,
    ← Finset.sum_Ico_eq_sub
      (fun n => PowerSeries.coeff n M.bjrModel.typeRootedTreeEGF x) hNK]
  exact M.complexFiniteSum_apply_norm_le_endpoint (Finset.Ico N K) hz x

private theorem FiniteIrreducibleModel.rootedTreeSeries_tail_apply_norm_le_endpoint
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) (x : S) :
    ‖M.bjrModel.rootedTreeSeries z x -
        M.complexRootedTreePartialSum N z x‖ ≤
      1 - M.bjrModel.rootedTreePartialSum N 1 x := by
  have hcMap : Filter.Tendsto
      (fun K => M.complexRootedTreePartialSum K z) Filter.atTop
      (nhds (M.bjrModel.rootedTreeSeries z)) := by
    simpa only [FiniteIrreducibleModel.complexRootedTreePartialSum] using
      (M.complexTypeRootedTreeFMS_hasSum_closedDisk hM hz).tendsto_sum_nat
  have hcEval : Filter.Tendsto
      (fun K => M.complexRootedTreePartialSum K z x) Filter.atTop
      (nhds (M.bjrModel.rootedTreeSeries z x)) :=
    ((continuous_eval_const x).tendsto (M.bjrModel.rootedTreeSeries z)).comp hcMap
  have hrEval0 : Filter.Tendsto
      (fun K => M.bjrModel.rootedTreePartialSum K 1 x) Filter.atTop
      (nhds ((1 : C(S, ℝ)) x)) :=
    ((continuous_eval_const x).tendsto (1 : C(S, ℝ))).comp
      (M.rootedTreePartialSum_tendsto_one hM)
  have hrEval : Filter.Tendsto
      (fun K => M.bjrModel.rootedTreePartialSum K 1 x) Filter.atTop
      (nhds (1 : ℝ)) := by
    simpa only [ContinuousMap.one_apply] using hrEval0
  have hcTail : Filter.Tendsto
      (fun m => M.complexRootedTreePartialSum (m + N) z x -
        M.complexRootedTreePartialSum N z x) Filter.atTop
      (nhds (M.bjrModel.rootedTreeSeries z x -
        M.complexRootedTreePartialSum N z x)) :=
    (hcEval.comp (Filter.tendsto_add_atTop_nat N)).sub tendsto_const_nhds
  have hrTail : Filter.Tendsto
      (fun m => M.bjrModel.rootedTreePartialSum (m + N) 1 x -
        M.bjrModel.rootedTreePartialSum N 1 x) Filter.atTop
      (nhds ((1 : ℝ) - M.bjrModel.rootedTreePartialSum N 1 x)) :=
    (hrEval.comp (Filter.tendsto_add_atTop_nat N)).sub tendsto_const_nhds
  exact le_of_tendsto_of_tendsto' hcTail.norm hrTail fun m =>
    M.complexRootedTreePartialSum_sub_apply_norm_le_endpoint
      N (m + N) (by omega) hz x

/-- After removal of the first two genuine modes, the remaining complex
tail is controlled by the corresponding remaining endpoint mass. -/
private theorem FiniteIrreducibleModel.rootedTreeSeries_lowModes_tail_norm_le
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {z : ℂ} (hz : ‖z‖ = 1) (x : S) :
    ‖M.bjrModel.rootedTreeSeries z x -
        (((PowerSeries.coeff 1 M.bjrModel.typeRootedTreeEGF x : ℝ) : ℂ) * z +
          ((PowerSeries.coeff 2 M.bjrModel.typeRootedTreeEGF x : ℝ) : ℂ) * z ^ 2)‖ ≤
      1 - (PowerSeries.coeff 1 M.bjrModel.typeRootedTreeEGF x +
        PowerSeries.coeff 2 M.bjrModel.typeRootedTreeEGF x) := by
  let a : ℝ := PowerSeries.coeff 1 M.bjrModel.typeRootedTreeEGF x
  let b : ℝ := PowerSeries.coeff 2 M.bjrModel.typeRootedTreeEGF x
  change ‖M.bjrModel.rootedTreeSeries z x - ((a : ℂ) * z + (b : ℂ) * z ^ 2)‖ ≤
    1 - (a + b)
  have htail :=
    M.rootedTreeSeries_tail_apply_norm_le_endpoint hM 3 hz.le x
  have hprefixC :
      M.complexRootedTreePartialSum 3 z x =
        (a : ℂ) * z + (b : ℂ) * z ^ 2 := by
    simp only [FiniteIrreducibleModel.complexRootedTreePartialSum,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      ContinuousMap.add_apply,
      M.bjrModel.complexTypeRootedTreeFMS_apply, ContinuousMap.smul_apply,
      continuousMapComplexifyRingHom_apply,
      TreeRealComplexBridge.complexify_apply, smul_eq_mul,
      M.bjrModel.typeRootedTreeEGF_coeff_zero, ContinuousMap.zero_apply,
      Complex.ofReal_zero, pow_zero, one_mul, pow_one]
    dsimp only [a, b]
    ring
  have hprefixR :
      M.bjrModel.rootedTreePartialSum 3 1 x = a + b := by
    simp only [CompactBJRModel.rootedTreePartialSum,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      one_pow, one_smul, M.bjrModel.typeRootedTreeEGF_coeff_zero]
    rfl
  rw [hprefixC, hprefixR] at htail
  exact htail

/-- At a fixed type, the genuine rooted-tree value has modulus strictly
smaller than one at every point of the unit circle other than `1`. -/
theorem FiniteIrreducibleModel.rootedTreeSeries_apply_norm_lt_one_of_unit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (x : S) :
    ‖M.bjrModel.rootedTreeSeries z x‖ < 1 := by
  let a : ℝ := PowerSeries.coeff 1 M.bjrModel.typeRootedTreeEGF x
  let b : ℝ := PowerSeries.coeff 2 M.bjrModel.typeRootedTreeEGF x
  have ha : 0 < a := M.bjrModel.typeRootedTreeEGF_coeff_one_pos x
  have hb : 0 < b := M.typeRootedTreeEGF_coeff_two_pos hM x
  have htail :
      ‖M.bjrModel.rootedTreeSeries z x - ((a : ℂ) * z + (b : ℂ) * z ^ 2)‖ ≤
        1 - (a + b) := by
    simpa only [a, b] using
      M.rootedTreeSeries_lowModes_tail_norm_le hM hz x
  have hfirst :
      ‖(a : ℂ) * z + (b : ℂ) * z ^ 2‖ < a + b :=
    positive_unit_modes_norm_lt ha hb hz hz1
  calc
    ‖M.bjrModel.rootedTreeSeries z x‖ =
        ‖((a : ℂ) * z + (b : ℂ) * z ^ 2) +
          (M.bjrModel.rootedTreeSeries z x -
            ((a : ℂ) * z + (b : ℂ) * z ^ 2))‖ := by
          congr 1
          abel
    _ ≤ ‖(a : ℂ) * z + (b : ℂ) * z ^ 2‖ +
        ‖M.bjrModel.rootedTreeSeries z x -
          ((a : ℂ) * z + (b : ℂ) * z ^ 2)‖ := norm_add_le _ _
    _ < (a + b) + (1 - (a + b)) := add_lt_add_of_lt_of_le hfirst htail
    _ = 1 := by ring

/-- Hence the `C(S,ℂ)` norm is strictly below one at every nontrivial point
of the unit circle.  Compactness of the type space is used here only to
turn the pointwise strict estimate into a strict supremum estimate. -/
theorem FiniteIrreducibleModel.rootedTreeSeries_norm_lt_one_of_unit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ‖M.bjrModel.rootedTreeSeries z‖ < 1 := by
  exact ((M.bjrModel.rootedTreeSeries z).norm_lt_iff zero_lt_one).mpr
    (M.rootedTreeSeries_apply_norm_lt_one_of_unit hM hz hz1)

/-- On every compact part of the unit circle which avoids the critical
endpoint, the strict modulus estimate has a uniform margin. -/
theorem FiniteIrreducibleModel.exists_rootedTreeSeries_uniform_unitCircle_margin
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty)
    (hunit : ∀ z ∈ K, ‖z‖ = 1) (hnotone : (1 : ℂ) ∉ K) :
    ∃ q : ℝ, q < 1 ∧ ∀ z ∈ K, ‖M.bjrModel.rootedTreeSeries z‖ ≤ q := by
  have hKdisk : K ⊆ {z : ℂ | ‖z‖ ≤ 1} := by
    intro z hz
    exact (hunit z hz).le
  have hcont : ContinuousOn (fun z => ‖M.bjrModel.rootedTreeSeries z‖) K :=
    continuous_norm.comp_continuousOn
      ((M.rootedTreeSeries_continuousOn_closedDisk hM).mono hKdisk)
  obtain ⟨z0, hz0, hmax⟩ := hK.exists_isMaxOn hKne hcont
  refine ⟨‖M.bjrModel.rootedTreeSeries z0‖, ?_, ?_⟩
  · exact M.rootedTreeSeries_norm_lt_one_of_unit hM
      (hunit z0 hz0) (fun hz => hnotone (hz ▸ hz0))
  · intro z hz
    exact hmax hz

end PerronWright
