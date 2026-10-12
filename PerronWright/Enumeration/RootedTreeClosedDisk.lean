import PerronWright.Enumeration.RootedTreeEndpointSum
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# The genuine rooted-tree series on the closed unit disk

This scratch file continues the endpoint argument without inserting an
absolute-convergence hypothesis.  Its basic estimate is coefficientwise:
every finite complex weighted sum with `‖z‖ ≤ 1` is dominated, in the
`C(S)` norm, by the corresponding genuine nonnegative endpoint sum.
-/

open Filter
open scoped Classical Topology ENNReal NNReal
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- An arbitrary complex diagonal evaluation is the genuine real
coefficient, complexified and multiplied by `z^n`. -/
theorem CompactBJRModel.complexTypeRootedTreeFMS_apply
    (M : CompactBJRModel S) (n : ℕ) (z : ℂ) :
    M.complexTypeRootedTreeFMS n (fun _ : Fin n => z) =
      z ^ n • continuousMapComplexifyRingHom
        (PowerSeries.coeff n M.typeRootedTreeEGF) := by
  ext x
  simp only [CompactBJRModel.complexTypeRootedTreeFMS,
    oneDimensionalFormalMultilinearSeries,
    ContinuousMultilinearMap.mkPiRing_apply,
    M.complexTypeRootedTreeEGF_coeff,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ContinuousMap.smul_apply, continuousMapComplexifyRingHom_apply,
    TreeRealComplexBridge.complexify_apply, smul_eq_mul]

/-- Finite complex sums in the closed unit disk are controlled by the
same finite sums of the nonnegative critical endpoint coefficients.  The
indexing map is allowed to repeat indices; this is convenient for tails. -/
private theorem CompactBJRModel.complexFiniteSum_norm_le_endpoint
    (M : CompactBJRModel S) {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖∑ i ∈ s,
        M.complexTypeRootedTreeFMS (k i) (fun _ : Fin (k i) => z)‖ ≤
      ‖∑ i ∈ s, PowerSeries.coeff (k i) M.typeRootedTreeEGF‖ := by
  classical
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro x
  calc
    ‖(∑ i ∈ s,
        M.complexTypeRootedTreeFMS (k i) (fun _ : Fin (k i) => z)) x‖
        ≤ ∑ i ∈ s,
            ‖(M.complexTypeRootedTreeFMS (k i)
              (fun _ : Fin (k i) => z)) x‖ := by
          simp only [ContinuousMap.sum_apply]
          exact norm_sum_le _ _
    _ = ∑ i ∈ s,
          ‖z‖ ^ (k i) * PowerSeries.coeff (k i) M.typeRootedTreeEGF x := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [M.complexTypeRootedTreeFMS_apply]
        simp only [ContinuousMap.smul_apply,
          continuousMapComplexifyRingHom_apply,
          TreeRealComplexBridge.complexify_apply, smul_eq_mul,
          norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (M.typeRootedTreeEGF_coeff_nonneg (k i) x)]
    _ ≤ ∑ i ∈ s, PowerSeries.coeff (k i) M.typeRootedTreeEGF x := by
        apply Finset.sum_le_sum
        intro i hi
        have hpow : ‖z‖ ^ (k i) ≤ 1 := by
          simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg z) hz (k i)
        exact mul_le_of_le_one_left
          (M.typeRootedTreeEGF_coeff_nonneg (k i) x) hpow
    _ = ‖(∑ i ∈ s,
          PowerSeries.coeff (k i) M.typeRootedTreeEGF) x‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · simp only [ContinuousMap.sum_apply]
        · simpa only [ContinuousMap.sum_apply] using
            (Finset.sum_nonneg fun i hi =>
              M.typeRootedTreeEGF_coeff_nonneg (k i) x)
    _ ≤ ‖∑ i ∈ s, PowerSeries.coeff (k i) M.typeRootedTreeEGF‖ :=
      (∑ i ∈ s, PowerSeries.coeff (k i) M.typeRootedTreeEGF).norm_coe_le_norm x

/-- The genuine complex rooted-tree terms are unconditionally summable at
every point of the closed unit disk.  This is a conditional comparison with
the endpoint `C(S,ℝ)` sum, not an assertion of norm-summability term by term.
-/
theorem CompactBJRModel.complexTypeRootedTreeFMS_summable_closedDisk
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) {z : ℂ}
    (hz : ‖z‖ ≤ 1) :
    Summable (fun n : ℕ =>
      M.complexTypeRootedTreeFMS n (fun _ : Fin n => z)) := by
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
theorem CompactBJRModel.complexTypeRootedTreeFMS_hasSum_closedDisk
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) {z : ℂ}
    (hz : ‖z‖ ≤ 1) :
    HasSum (fun n : ℕ =>
        M.complexTypeRootedTreeFMS n (fun _ : Fin n => z))
      (M.rootedTreeSeries z) := by
  unfold CompactBJRModel.rootedTreeSeries FormalMultilinearSeries.sum
  exact (M.complexTypeRootedTreeFMS_summable_closedDisk hM hz).hasSum

/-- Finite complex Taylor polynomial of the genuine rooted-tree series. -/
def CompactBJRModel.complexRootedTreePartialSum
    (M : CompactBJRModel S) (N : ℕ) (z : ℂ) : C(S, ℂ) :=
  ∑ n ∈ Finset.range N,
    M.complexTypeRootedTreeFMS n (fun _ : Fin n => z)

/-- Closed-disk tails are bounded uniformly by the genuine endpoint tail. -/
theorem CompactBJRModel.complexRootedTreeTail_norm_le_endpoint
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖M.rootedTreeSeries z - M.complexRootedTreePartialSum N z‖ ≤
      ‖(1 : C(S, ℝ)) - M.rootedTreePartialSum N 1‖ := by
  have hc := M.complexTypeRootedTreeFMS_hasSum_closedDisk hM hz
  have hr := M.typeRootedTreeEGF_hasSum_one hM
  have hctail : HasSum
      (fun n : ℕ => M.complexTypeRootedTreeFMS (n + N)
        (fun _ : Fin (n + N) => z))
      (M.rootedTreeSeries z - M.complexRootedTreePartialSum N z) := by
    simpa only [CompactBJRModel.complexRootedTreePartialSum] using
      (hasSum_nat_add_iff' N).mpr hc
  have hrtail : HasSum
      (fun n : ℕ => PowerSeries.coeff (n + N) M.typeRootedTreeEGF)
      ((1 : C(S, ℝ)) - M.rootedTreePartialSum N 1) := by
    simpa only [CompactBJRModel.rootedTreePartialSum, one_pow, one_smul] using
      (hasSum_nat_add_iff' N).mpr hr
  exact le_of_tendsto_of_tendsto' hctail.norm hrtail.norm fun s =>
    M.complexFiniteSum_norm_le_endpoint s (fun n => n + N) z hz

/-- The genuine complex Taylor polynomials converge uniformly on the closed
unit disk. -/
theorem CompactBJRModel.complexRootedTreePartialSum_tendstoUniformlyOn_closedDisk
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    TendstoUniformlyOn
      (fun N z => M.complexRootedTreePartialSum N z)
      M.rootedTreeSeries Filter.atTop {z : ℂ | ‖z‖ ≤ 1} := by
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
    ‖(1 : C(S, ℝ)) - M.rootedTreePartialSum n 1‖ =
        ‖-(M.rootedTreePartialSum n 1 - 1)‖ := by
          congr 1
          abel
    _ = ‖M.rootedTreePartialSum n 1 - 1‖ := norm_neg _
    _ < ε := hdist

/-- Every genuine complex Taylor polynomial is continuous in the activity. -/
theorem CompactBJRModel.complexRootedTreePartialSum_continuous
    (M : CompactBJRModel S) (N : ℕ) :
    Continuous (M.complexRootedTreePartialSum N) := by
  unfold CompactBJRModel.complexRootedTreePartialSum
  fun_prop

/-- The actual rooted-tree series extends continuously to the closed unit
disk. -/
theorem CompactBJRModel.rootedTreeSeries_continuousOn_closedDisk
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ContinuousOn M.rootedTreeSeries {z : ℂ | ‖z‖ ≤ 1} := by
  apply (M.complexRootedTreePartialSum_tendstoUniformlyOn_closedDisk hM).continuousOn
  exact (Filter.Eventually.of_forall fun N =>
    (M.complexRootedTreePartialSum_continuous N).continuousOn).frequently

/-- The first genuine rooted-tree coefficient is the one-vertex factor. -/
theorem CompactBJRModel.typeRootedTreeEGF_coeff_one
    (M : CompactBJRModel S) :
    PowerSeries.coeff 1 M.typeRootedTreeEGF = M.zeroTreeVertexFactor := by
  rw [M.typeRootedTreeEGF_eq_rootedTreeFormalRHS]
  exact M.rootedTreeFormalRHS_coeff_one M.typeRootedTreeEGF
    M.kernelAction_typeRootedTreeEGF_constantCoeff

/-- The linear coefficient of the substituted exponential is the linear
coefficient of the substituted series. -/
private theorem powerSeries_subst_exp_coeff_one
    {R : Type*} [CommRing R] [Algebra ℚ R]
    (A : PowerSeries R) (hA0 : PowerSeries.constantCoeff A = 0) :
    PowerSeries.coeff 1
        (PowerSeries.subst A (PowerSeries.exp R)) =
      PowerSeries.coeff 1 A := by
  have hA : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  have hrec := powerSeries_subst_exp_coeff_succ A hA 0
  have hE0 : PowerSeries.constantCoeff
      (PowerSeries.subst A (PowerSeries.exp R)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_subst' hA (PowerSeries.exp R) 0,
      finsum_eq_single _ 0]
    · simp
    · intro d hd
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_pow, hA0, zero_pow hd]
      simp
  simpa only [Nat.cast_zero, zero_add, Nat.cast_one, one_mul,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hE0] using hrec

/-- The second genuine rooted-tree coefficient is the one-edge rooted-tree
profile.  This is extracted from the already proved finite combinatorial
formal identity, rather than assumed as an analytic recurrence. -/
theorem CompactBJRModel.typeRootedTreeEGF_coeff_two
    (M : CompactBJRModel S) :
    PowerSeries.coeff 2 M.typeRootedTreeEGF =
      M.zeroTreeVertexFactor *
        M.kernel.action M.mu M.zeroTreeVertexFactor := by
  let A := M.kernelActionPowerSeries M.typeRootedTreeEGF
  have hA0 : PowerSeries.constantCoeff A = 0 := by
    simpa only [A] using M.kernelAction_typeRootedTreeEGF_constantCoeff
  have hE1 : PowerSeries.coeff 1
      (PowerSeries.subst A (PowerSeries.exp C(S, ℝ))) =
        PowerSeries.coeff 1 A :=
    powerSeries_subst_exp_coeff_one A hA0
  have hfixed := congrArg (PowerSeries.coeff 2)
    M.typeRootedTreeEGF_eq_rootedTreeFormalRHS
  rw [CompactBJRModel.rootedTreeFormalRHS,
    show 2 = 1 + 1 by omega, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_C_mul] at hfixed
  rw [hE1] at hfixed
  simpa only [A, M.kernelActionPowerSeries_coeff,
    M.typeRootedTreeEGF_coeff_one,
    M.kernel.actionCLM_apply] using hfixed

/-- The genuine one-vertex factor has a uniform positive lower bound. -/
theorem CompactBJRModel.zeroTreeVertexFactor_uniform_pos
    (M : CompactBJRModel S) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ M.zeroTreeVertexFactor x := by
  obtain ⟨c, hc, hle⟩ := isCompact_univ.exists_forall_le'
    M.zeroTreeVertexFactor.continuous.continuousOn
    (fun x _ => Real.exp_pos (-M.degreeFunction x))
  exact ⟨c, hc, fun x => hle x (Set.mem_univ x)⟩

/-- Applying the critical kernel to the positive one-vertex factor is
strictly positive at every type.  The proof compares it with a small
positive multiple of the proved Perron eigenfunction. -/
theorem CompactBJRModel.kernelAction_zeroTreeVertexFactor_pos
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (x : S) :
    0 < M.kernel.action M.mu M.zeroTreeVertexFactor x := by
  obtain ⟨c, hc, hcv⟩ := M.zeroTreeVertexFactor_uniform_pos
  let u := M.perronFunction hM
  let q : ℝ := c / (‖u‖ + 1)
  have hden : 0 < ‖u‖ + 1 := by positivity
  have hq : 0 < q := div_pos hc hden
  have hcomp : ∀ y, (q • u) y ≤ M.zeroTreeVertexFactor y := by
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
      _ ≤ M.zeroTreeVertexFactor y := hcv y
  have hmono := M.kernel.realAction_mono M.mu (q • u)
    M.zeroTreeVertexFactor hcomp x
  rw [M.kernel.action_smul, show u = M.perronFunction hM by rfl,
    M.perronFunction_fixed hM, ContinuousMap.smul_apply, smul_eq_mul] at hmono
  exact (mul_pos hq (M.perronFunction_pos hM x)).trans_le hmono

/-- Consequently both low coefficients used to break phase alignment are
strictly positive at every type. -/
theorem CompactBJRModel.typeRootedTreeEGF_coeff_one_pos
    (M : CompactBJRModel S) (x : S) :
    0 < PowerSeries.coeff 1 M.typeRootedTreeEGF x := by
  rw [M.typeRootedTreeEGF_coeff_one, M.zeroTreeVertexFactor_apply]
  exact Real.exp_pos _

theorem CompactBJRModel.typeRootedTreeEGF_coeff_two_pos
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) (x : S) :
    0 < PowerSeries.coeff 2 M.typeRootedTreeEGF x := by
  rw [M.typeRootedTreeEGF_coeff_two, ContinuousMap.mul_apply]
  exact mul_pos (by
    rw [M.zeroTreeVertexFactor_apply]
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

private theorem CompactBJRModel.complexTypeRootedTreeFMS_apply_norm_le_coeff
    (M : CompactBJRModel S) (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) (x : S) :
    ‖(M.complexTypeRootedTreeFMS n (fun _ : Fin n => z)) x‖ ≤
      PowerSeries.coeff n M.typeRootedTreeEGF x := by
  rw [M.complexTypeRootedTreeFMS_apply]
  simp only [ContinuousMap.smul_apply,
    continuousMapComplexifyRingHom_apply,
    TreeRealComplexBridge.complexify_apply, smul_eq_mul,
    norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (M.typeRootedTreeEGF_coeff_nonneg n x)]
  exact mul_le_of_le_one_left
    (M.typeRootedTreeEGF_coeff_nonneg n x)
    (by simpa only [one_pow] using
      pow_le_pow_left₀ (norm_nonneg z) hz n)

/-- At a fixed type, every finite set of genuine complex terms is bounded
by the same finite set of nonnegative endpoint coefficients. -/
private theorem CompactBJRModel.complexFiniteSum_apply_norm_le_endpoint
    (M : CompactBJRModel S) (s : Finset ℕ)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (x : S) :
    ‖∑ n ∈ s,
        (M.complexTypeRootedTreeFMS n (fun _ : Fin n => z)) x‖ ≤
      ∑ n ∈ s, PowerSeries.coeff n M.typeRootedTreeEGF x := by
  calc
    ‖∑ n ∈ s,
        (M.complexTypeRootedTreeFMS n (fun _ : Fin n => z)) x‖ ≤
        ∑ n ∈ s,
          ‖(M.complexTypeRootedTreeFMS n (fun _ : Fin n => z)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ s, PowerSeries.coeff n M.typeRootedTreeEGF x := by
      exact Finset.sum_le_sum fun n hn =>
        M.complexTypeRootedTreeFMS_apply_norm_le_coeff n hz x

/-- The same pointwise comparison for a finite natural tail. -/
private theorem CompactBJRModel.complexRootedTreePartialSum_sub_apply_norm_le_endpoint
    (M : CompactBJRModel S) (N K : ℕ) (hNK : N ≤ K)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (x : S) :
    ‖M.complexRootedTreePartialSum K z x -
        M.complexRootedTreePartialSum N z x‖ ≤
      M.rootedTreePartialSum K 1 x -
        M.rootedTreePartialSum N 1 x := by
  unfold CompactBJRModel.complexRootedTreePartialSum
  unfold CompactBJRModel.rootedTreePartialSum
  simp only [ContinuousMap.sum_apply, one_pow, one_smul]
  rw [← Finset.sum_Ico_eq_sub
      (fun n =>
        (M.complexTypeRootedTreeFMS n (fun _ : Fin n => z)) x) hNK,
    ← Finset.sum_Ico_eq_sub
      (fun n => PowerSeries.coeff n M.typeRootedTreeEGF x) hNK]
  exact M.complexFiniteSum_apply_norm_le_endpoint (Finset.Ico N K) hz x

private theorem CompactBJRModel.rootedTreeSeries_tail_apply_norm_le_endpoint
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) (x : S) :
    ‖M.rootedTreeSeries z x -
        M.complexRootedTreePartialSum N z x‖ ≤
      1 - M.rootedTreePartialSum N 1 x := by
  have hcMap : Filter.Tendsto
      (fun K => M.complexRootedTreePartialSum K z) Filter.atTop
      (nhds (M.rootedTreeSeries z)) := by
    simpa only [CompactBJRModel.complexRootedTreePartialSum] using
      (M.complexTypeRootedTreeFMS_hasSum_closedDisk hM hz).tendsto_sum_nat
  have hcEval : Filter.Tendsto
      (fun K => M.complexRootedTreePartialSum K z x) Filter.atTop
      (nhds (M.rootedTreeSeries z x)) :=
    ((continuous_eval_const x).tendsto (M.rootedTreeSeries z)).comp hcMap
  have hrEval0 : Filter.Tendsto
      (fun K => M.rootedTreePartialSum K 1 x) Filter.atTop
      (nhds ((1 : C(S, ℝ)) x)) :=
    ((continuous_eval_const x).tendsto (1 : C(S, ℝ))).comp
      (M.rootedTreePartialSum_tendsto_one hM)
  have hrEval : Filter.Tendsto
      (fun K => M.rootedTreePartialSum K 1 x) Filter.atTop
      (nhds (1 : ℝ)) := by
    simpa only [ContinuousMap.one_apply] using hrEval0
  have hcTail : Filter.Tendsto
      (fun m => M.complexRootedTreePartialSum (m + N) z x -
        M.complexRootedTreePartialSum N z x) Filter.atTop
      (nhds (M.rootedTreeSeries z x -
        M.complexRootedTreePartialSum N z x)) :=
    (hcEval.comp (Filter.tendsto_add_atTop_nat N)).sub tendsto_const_nhds
  have hrTail : Filter.Tendsto
      (fun m => M.rootedTreePartialSum (m + N) 1 x -
        M.rootedTreePartialSum N 1 x) Filter.atTop
      (nhds ((1 : ℝ) - M.rootedTreePartialSum N 1 x)) :=
    (hrEval.comp (Filter.tendsto_add_atTop_nat N)).sub tendsto_const_nhds
  exact le_of_tendsto_of_tendsto' hcTail.norm hrTail fun m =>
    M.complexRootedTreePartialSum_sub_apply_norm_le_endpoint
      N (m + N) (by omega) hz x

/-- After removal of the first two genuine modes, the remaining complex
tail is controlled by the corresponding remaining endpoint mass. -/
private theorem CompactBJRModel.rootedTreeSeries_lowModes_tail_norm_le
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ = 1) (x : S) :
    ‖M.rootedTreeSeries z x -
        (((PowerSeries.coeff 1 M.typeRootedTreeEGF x : ℝ) : ℂ) * z +
          ((PowerSeries.coeff 2 M.typeRootedTreeEGF x : ℝ) : ℂ) * z ^ 2)‖ ≤
      1 - (PowerSeries.coeff 1 M.typeRootedTreeEGF x +
        PowerSeries.coeff 2 M.typeRootedTreeEGF x) := by
  let a : ℝ := PowerSeries.coeff 1 M.typeRootedTreeEGF x
  let b : ℝ := PowerSeries.coeff 2 M.typeRootedTreeEGF x
  change ‖M.rootedTreeSeries z x - ((a : ℂ) * z + (b : ℂ) * z ^ 2)‖ ≤
    1 - (a + b)
  have htail :=
    M.rootedTreeSeries_tail_apply_norm_le_endpoint hM 3 hz.le x
  have hprefixC :
      M.complexRootedTreePartialSum 3 z x =
        (a : ℂ) * z + (b : ℂ) * z ^ 2 := by
    simp only [CompactBJRModel.complexRootedTreePartialSum,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      ContinuousMap.add_apply,
      M.complexTypeRootedTreeFMS_apply, ContinuousMap.smul_apply,
      continuousMapComplexifyRingHom_apply,
      TreeRealComplexBridge.complexify_apply, smul_eq_mul,
      M.typeRootedTreeEGF_coeff_zero, ContinuousMap.zero_apply,
      Complex.ofReal_zero, pow_zero, one_mul, pow_one]
    dsimp only [a, b]
    ring
  have hprefixR :
      M.rootedTreePartialSum 3 1 x = a + b := by
    simp only [CompactBJRModel.rootedTreePartialSum,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      one_pow, one_smul, M.typeRootedTreeEGF_coeff_zero]
    rfl
  rw [hprefixC, hprefixR] at htail
  exact htail

/-- At a fixed type, the genuine rooted-tree value has modulus strictly
smaller than one at every point of the unit circle other than `1`. -/
theorem CompactBJRModel.rootedTreeSeries_apply_norm_lt_one_of_unit
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (x : S) :
    ‖M.rootedTreeSeries z x‖ < 1 := by
  let a : ℝ := PowerSeries.coeff 1 M.typeRootedTreeEGF x
  let b : ℝ := PowerSeries.coeff 2 M.typeRootedTreeEGF x
  have ha : 0 < a := M.typeRootedTreeEGF_coeff_one_pos x
  have hb : 0 < b := M.typeRootedTreeEGF_coeff_two_pos hM x
  have htail :
      ‖M.rootedTreeSeries z x - ((a : ℂ) * z + (b : ℂ) * z ^ 2)‖ ≤
        1 - (a + b) := by
    simpa only [a, b] using
      M.rootedTreeSeries_lowModes_tail_norm_le hM hz x
  have hfirst :
      ‖(a : ℂ) * z + (b : ℂ) * z ^ 2‖ < a + b :=
    positive_unit_modes_norm_lt ha hb hz hz1
  calc
    ‖M.rootedTreeSeries z x‖ =
        ‖((a : ℂ) * z + (b : ℂ) * z ^ 2) +
          (M.rootedTreeSeries z x -
            ((a : ℂ) * z + (b : ℂ) * z ^ 2))‖ := by
          congr 1
          abel
    _ ≤ ‖(a : ℂ) * z + (b : ℂ) * z ^ 2‖ +
        ‖M.rootedTreeSeries z x -
          ((a : ℂ) * z + (b : ℂ) * z ^ 2)‖ := norm_add_le _ _
    _ < (a + b) + (1 - (a + b)) := add_lt_add_of_lt_of_le hfirst htail
    _ = 1 := by ring

/-- Hence the `C(S,ℂ)` norm is strictly below one at every nontrivial point
of the unit circle.  Compactness of the type space is used here only to
turn the pointwise strict estimate into a strict supremum estimate. -/
theorem CompactBJRModel.rootedTreeSeries_norm_lt_one_of_unit
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ‖M.rootedTreeSeries z‖ < 1 := by
  exact ((M.rootedTreeSeries z).norm_lt_iff zero_lt_one).mpr
    (M.rootedTreeSeries_apply_norm_lt_one_of_unit hM hz hz1)

/-- On every compact part of the unit circle which avoids the critical
endpoint, the strict modulus estimate has a uniform margin. -/
theorem CompactBJRModel.exists_rootedTreeSeries_uniform_unitCircle_margin
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty)
    (hunit : ∀ z ∈ K, ‖z‖ = 1) (hnotone : (1 : ℂ) ∉ K) :
    ∃ q : ℝ, q < 1 ∧ ∀ z ∈ K, ‖M.rootedTreeSeries z‖ ≤ q := by
  have hKdisk : K ⊆ {z : ℂ | ‖z‖ ≤ 1} := by
    intro z hz
    exact (hunit z hz).le
  have hcont : ContinuousOn (fun z => ‖M.rootedTreeSeries z‖) K :=
    continuous_norm.comp_continuousOn
      ((M.rootedTreeSeries_continuousOn_closedDisk hM).mono hKdisk)
  obtain ⟨z0, hz0, hmax⟩ := hK.exists_isMaxOn hKne hcont
  refine ⟨‖M.rootedTreeSeries z0‖, ?_, ?_⟩
  · exact M.rootedTreeSeries_norm_lt_one_of_unit hM
      (hunit z0 hz0) (fun hz => hnotone (hz ▸ hz0))
  · intro z hz
    exact hmax hz

end PerronWright
