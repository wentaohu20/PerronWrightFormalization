import PerronWright.Enumeration.RootedTreePhysicalSeries
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Analysis.Complex.Exponential

/-!
# Domination of enumerative rooted-tree truncations

The finite Taylor truncations of the genuine labelled rooted-tree series are
bounded pointwise by the corresponding Picard iterates of the physical tree
equation.  The key scalar input is a finite, purely algebraic exponential
majorization; no convergence radius is assumed.
-/

open scoped Classical Topology
open Polynomial
noncomputable section

namespace PerronWright

private def powerSeriesPartialEval
    (F : PowerSeries ℝ) (N : ℕ) (w : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, PowerSeries.coeff n F * w ^ n

private theorem powerSeriesPartialEval_eq_trunc_eval
    (F : PowerSeries ℝ) (N : ℕ) (w : ℝ) :
    powerSeriesPartialEval F N w = (PowerSeries.trunc N F).eval w := by
  simpa only [powerSeriesPartialEval, Polynomial.eval,
    RingHom.id_apply] using
    (PowerSeries.eval₂_trunc_eq_sum_range w (RingHom.id ℝ) N F).symm

private theorem polynomial_eval_nonneg_of_coeff_nonneg
    (p : ℝ[X]) {w : ℝ} (hw : 0 ≤ w)
    (hp : ∀ n : ℕ, 0 ≤ p.coeff n) :
    0 ≤ p.eval w := by
  rw [p.eval_eq_sum_range' (Nat.lt_succ_self p.natDegree) w]
  exact Finset.sum_nonneg fun n hn =>
    mul_nonneg (hp n) (pow_nonneg hw n)

private theorem polynomial_eval_le_of_coeff_le
    (p q : ℝ[X]) {w : ℝ} (hw : 0 ≤ w)
    (hpq : ∀ n : ℕ, p.coeff n ≤ q.coeff n) :
    p.eval w ≤ q.eval w := by
  have hnonneg : 0 ≤ (q - p).eval w :=
    polynomial_eval_nonneg_of_coeff_nonneg (q - p) hw fun n => by
      simpa only [Polynomial.coeff_sub, sub_nonneg] using hpq n
  simpa only [Polynomial.eval_sub, sub_nonneg] using hnonneg

private theorem polynomial_coeff_pow_nonneg
    (p : ℝ[X]) (hp : ∀ n : ℕ, 0 ≤ p.coeff n)
    (d n : ℕ) :
    0 ≤ (p ^ d).coeff n := by
  induction d generalizing n with
  | zero =>
      simp only [pow_zero, Polynomial.coeff_one]
      split_ifs <;> norm_num
  | succ d ih =>
      rw [pow_succ, Polynomial.coeff_mul]
      exact Finset.sum_nonneg fun ij hij =>
        mul_nonneg (ih ij.1) (hp ij.2)

private theorem powerSeriesPartialEval_nonneg
    (A : PowerSeries ℝ) (hA : ∀ n : ℕ, 0 ≤ PowerSeries.coeff n A)
    (N : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ powerSeriesPartialEval A N w := by
  unfold powerSeriesPartialEval
  exact Finset.sum_nonneg fun n hn =>
    mul_nonneg (hA n) (pow_nonneg hw n)

private theorem powerSeriesPartialEval_pow_le
    (A : PowerSeries ℝ) (hA : ∀ n : ℕ, 0 ≤ PowerSeries.coeff n A)
    (N d : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    powerSeriesPartialEval (A ^ d) N w ≤
      (powerSeriesPartialEval A N w) ^ d := by
  let q : ℝ[X] := PowerSeries.trunc N A
  have hq : ∀ n : ℕ, 0 ≤ q.coeff n := by
    intro n
    dsimp only [q]
    rw [PowerSeries.coeff_trunc]
    split_ifs
    · exact hA n
    · exact le_rfl
  have hcoeff : ∀ n : ℕ,
      (PowerSeries.trunc N ((q : PowerSeries ℝ) ^ d)).coeff n ≤
        (q ^ d).coeff n := by
    intro n
    rw [PowerSeries.coeff_trunc]
    split_ifs with hn
    · rw [← Polynomial.coe_pow (R := ℝ) (φ := q) d,
        Polynomial.coeff_coe]
    · exact polynomial_coeff_pow_nonneg q hq d n
  rw [powerSeriesPartialEval_eq_trunc_eval,
    powerSeriesPartialEval_eq_trunc_eval]
  rw [← PowerSeries.trunc_trunc_pow A N d]
  calc
    (PowerSeries.trunc N ((q : PowerSeries ℝ) ^ d)).eval w ≤
        (q ^ d).eval w :=
      polynomial_eval_le_of_coeff_le _ _ hw hcoeff
    _ = (q.eval w) ^ d := by rw [Polynomial.eval_pow]

private theorem coeff_pow_eq_zero_of_lt
    (A : PowerSeries ℝ)
    (hA0 : PowerSeries.constantCoeff A = 0)
    {n d : ℕ} (hnd : n < d) :
    PowerSeries.coeff n (A ^ d) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  have hnd' : (n : ℕ∞) < (d : ℕ∞) := by
    simpa only [Nat.cast_lt] using hnd
  exact hnd'.trans_le
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hA0)

private theorem coeff_subst_exp_eq_sum_range
    (A : PowerSeries ℝ)
    (hA0 : PowerSeries.constantCoeff A = 0)
    {n N : ℕ} (hn : n < N) :
    PowerSeries.coeff n
        (PowerSeries.subst A (PowerSeries.exp ℝ)) =
      ∑ d ∈ Finset.range N,
        (1 / (d.factorial : ℝ)) * PowerSeries.coeff n (A ^ d) := by
  have hSubst : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hA0
  rw [PowerSeries.coeff_subst' hSubst (PowerSeries.exp ℝ) n]
  rw [finsum_eq_finsetSum_of_support_subset]
  · apply Finset.sum_congr rfl
    intro d hd
    simp only [PowerSeries.coeff_exp, one_div, smul_eq_mul]
    norm_num
  · intro d hd
    rw [Function.mem_support] at hd
    by_contra hdN
    have hNd : N ≤ d := by
      apply not_lt.mp
      intro hdlt
      exact hdN (Finset.mem_range.mpr hdlt)
    have hzero : PowerSeries.coeff n (A ^ d) = 0 :=
      coeff_pow_eq_zero_of_lt A hA0 (lt_of_lt_of_le hn hNd)
    simp only [hzero, smul_zero, ne_eq, not_true_eq_false] at hd

/-- The finite Taylor polynomial of a substituted exponential is bounded by
the genuine exponential of the corresponding finite input polynomial. -/
private theorem powerSeriesPartialEval_subst_exp_le_exp
    (A : PowerSeries ℝ)
    (hA0 : PowerSeries.constantCoeff A = 0)
    (hA : ∀ n : ℕ, 0 ≤ PowerSeries.coeff n A)
    (N : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    powerSeriesPartialEval
        (PowerSeries.subst A (PowerSeries.exp ℝ)) N w ≤
      Real.exp (powerSeriesPartialEval A N w) := by
  have hx : 0 ≤ powerSeriesPartialEval A N w :=
    powerSeriesPartialEval_nonneg A hA N hw
  calc
    powerSeriesPartialEval
        (PowerSeries.subst A (PowerSeries.exp ℝ)) N w =
        ∑ n ∈ Finset.range N,
          (∑ d ∈ Finset.range N,
            (1 / (d.factorial : ℝ)) * PowerSeries.coeff n (A ^ d)) *
              w ^ n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [coeff_subst_exp_eq_sum_range A hA0 (Finset.mem_range.mp hn)]
    _ = ∑ d ∈ Finset.range N,
          (1 / (d.factorial : ℝ)) *
            powerSeriesPartialEval (A ^ d) N w := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      unfold powerSeriesPartialEval
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring_nf
    _ ≤ ∑ d ∈ Finset.range N,
          (powerSeriesPartialEval A N w) ^ d / (d.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hpow := powerSeriesPartialEval_pow_le A hA N d hw
      have hfac : 0 ≤ (1 / (d.factorial : ℝ)) := by positivity
      calc
        (1 / (d.factorial : ℝ)) *
              powerSeriesPartialEval (A ^ d) N w ≤
            (1 / (d.factorial : ℝ)) *
              (powerSeriesPartialEval A N w) ^ d :=
          mul_le_mul_of_nonneg_left hpow hfac
        _ = (powerSeriesPartialEval A N w) ^ d /
              (d.factorial : ℝ) := by ring_nf
    _ ≤ Real.exp (powerSeriesPartialEval A N w) :=
      Real.sum_le_exp_of_nonneg hx N

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private def continuousMapEvalRingHom (x : S) : C(S, ℝ) →+* ℝ :=
  (Pi.evalRingHom (fun _ : S ↦ ℝ) x).comp ContinuousMap.coeFnRingHom

private def CompactBJRModel.rootedTreeKernelSeriesAt
    (M : CompactBJRModel S) (x : S) : PowerSeries ℝ :=
  PowerSeries.map (continuousMapEvalRingHom x)
    (M.kernelActionPowerSeries M.typeRootedTreeEGF)

@[simp] private theorem CompactBJRModel.rootedTreeKernelSeriesAt_coeff
    (M : CompactBJRModel S) (x : S) (n : ℕ) :
    PowerSeries.coeff n (M.rootedTreeKernelSeriesAt x) =
      M.kernel.action M.mu
        (PowerSeries.coeff n M.typeRootedTreeEGF) x := by
  simp only [CompactBJRModel.rootedTreeKernelSeriesAt,
    PowerSeries.coeff_map, continuousMapEvalRingHom,
    RingHom.coe_comp, Function.comp_apply,
    Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply,
    M.kernelActionPowerSeries_coeff, ContinuousKernel.actionCLM_apply]

private theorem CompactBJRModel.rootedTreeKernelSeriesAt_constantCoeff
    (M : CompactBJRModel S) (x : S) :
    PowerSeries.constantCoeff (M.rootedTreeKernelSeriesAt x) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [M.rootedTreeKernelSeriesAt_coeff,
    M.typeRootedTreeEGF_coeff_zero]
  simp only [← M.kernel.actionCLM_apply, map_zero,
    ContinuousMap.zero_apply]

private theorem CompactBJRModel.rootedTreeKernelSeriesAt_coeff_nonneg
    (M : CompactBJRModel S) (x : S) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (M.rootedTreeKernelSeriesAt x) := by
  rw [M.rootedTreeKernelSeriesAt_coeff]
  exact M.kernel.realAction_nonneg M.mu _
    (fun y ↦ M.typeRootedTreeEGF_coeff_nonneg n y) x

private theorem CompactBJRModel.rootedTreeKernelSeriesAt_partialEval
    (M : CompactBJRModel S) (x : S) (N : ℕ) (w : ℝ) :
    powerSeriesPartialEval (M.rootedTreeKernelSeriesAt x) N w =
      M.kernel.action M.mu (M.rootedTreePartialSum N w) x := by
  unfold powerSeriesPartialEval CompactBJRModel.rootedTreePartialSum
  rw [← ContinuousKernel.actionCLM_apply]
  rw [map_sum]
  simp only [map_smul, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul,
    CompactBJRModel.rootedTreeKernelSeriesAt_coeff,
    ContinuousKernel.actionCLM_apply]
  apply Finset.sum_congr rfl
  intro n hn
  ring_nf

private theorem CompactBJRModel.rootedTreeExponentialSeriesAt
    (M : CompactBJRModel S) (x : S) :
    PowerSeries.map (continuousMapEvalRingHom x)
        (PowerSeries.subst
          (M.kernelActionPowerSeries M.typeRootedTreeEGF)
          (PowerSeries.exp C(S, ℝ))) =
      PowerSeries.subst (M.rootedTreeKernelSeriesAt x)
        (PowerSeries.exp ℝ) := by
  have hA := M.kernelAction_typeRootedTreeEGF_hasSubst
  change MvPowerSeries.map (continuousMapEvalRingHom x)
      (PowerSeries.subst
        (M.kernelActionPowerSeries M.typeRootedTreeEGF)
        (PowerSeries.exp C(S, ℝ))) =
    PowerSeries.subst
      (MvPowerSeries.map (continuousMapEvalRingHom x)
        (M.kernelActionPowerSeries M.typeRootedTreeEGF))
      (PowerSeries.exp ℝ)
  rw [PowerSeries.map_subst hA
    (h := continuousMapEvalRingHom x)
    (PowerSeries.exp C(S, ℝ)), PowerSeries.map_exp]

private theorem CompactBJRModel.rootedTreePartialSum_succ_eq
    (M : CompactBJRModel S) (N : ℕ) (w : ℝ) (x : S) :
    M.rootedTreePartialSum (N + 1) w x =
      w * M.zeroTreeVertexFactor x *
        powerSeriesPartialEval
          (PowerSeries.subst (M.rootedTreeKernelSeriesAt x)
            (PowerSeries.exp ℝ)) N w := by
  induction N with
  | zero =>
      simp [M.rootedTreePartialSum_succ, powerSeriesPartialEval]
  | succ N ih =>
      rw [M.rootedTreePartialSum_succ,
        ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
        ih]
      have hTree := congrArg (PowerSeries.coeff (N + 1))
        M.typeRootedTreeEGF_eq_rootedTreeFormalRHS
      rw [CompactBJRModel.rootedTreeFormalRHS,
        PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_C_mul] at hTree
      have hMap := congrArg (PowerSeries.coeff N)
        (M.rootedTreeExponentialSeriesAt x)
      simp only [PowerSeries.coeff_map, continuousMapEvalRingHom,
        RingHom.coe_comp, Function.comp_apply,
        Pi.evalRingHom_apply, ContinuousMap.coeFnRingHom_apply] at hMap
      rw [hTree, ContinuousMap.mul_apply, hMap]
      unfold powerSeriesPartialEval
      rw [Finset.sum_range_succ]
      ring_nf

private theorem CompactBJRModel.kernel_action_sub_one
    (M : CompactBJRModel S) (V : C(S, ℝ)) (x : S) :
    M.kernel.action M.mu (V - 1) x =
      M.kernel.action M.mu V x - M.degreeFunction x := by
  rw [← M.kernel.actionCLM_apply, map_sub,
    ContinuousMap.sub_apply, M.kernel.actionCLM_apply,
    M.kernel.actionCLM_apply]
  congr 1
  rw [M.kernel.action_apply, CompactBJRModel.degreeFunction,
    M.kernel.degreeMap_apply]
  simp only [ContinuousMap.one_apply, mul_one, ContinuousKernel.degree]

private theorem CompactBJRModel.zeroFactor_mul_exp_kernel_eq_normalizedMap
    (M : CompactBJRModel S) (w : ℝ) (V : C(S, ℝ)) (x : S) :
    w * M.zeroTreeVertexFactor x *
        Real.exp (M.kernel.action M.mu V x) =
      M.normalizedZeroTreeMap w V x := by
  rw [M.zeroTreeVertexFactor_apply, M.normalizedZeroTreeMap_apply,
    M.kernel_action_sub_one]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring_nf

theorem CompactBJRModel.rootedTreePartialSum_succ_le_normalizedZeroTreeMap
    (M : CompactBJRModel S) (N : ℕ) {w : ℝ} (hw : 0 ≤ w) (x : S) :
    M.rootedTreePartialSum (N + 1) w x ≤
      M.normalizedZeroTreeMap w (M.rootedTreePartialSum N w) x := by
  let A := M.rootedTreeKernelSeriesAt x
  have hscalar := powerSeriesPartialEval_subst_exp_le_exp A
    (by simpa only [A] using M.rootedTreeKernelSeriesAt_constantCoeff x)
    (fun n ↦ by simpa only [A] using M.rootedTreeKernelSeriesAt_coeff_nonneg x n)
    N hw
  rw [M.rootedTreePartialSum_succ_eq]
  calc
    w * M.zeroTreeVertexFactor x *
        powerSeriesPartialEval
          (PowerSeries.subst A (PowerSeries.exp ℝ)) N w ≤
      w * M.zeroTreeVertexFactor x *
        Real.exp (powerSeriesPartialEval A N w) := by
      exact mul_le_mul_of_nonneg_left hscalar
        (mul_nonneg hw (by
          rw [M.zeroTreeVertexFactor_apply]
          exact (Real.exp_pos _).le))
    _ = w * M.zeroTreeVertexFactor x *
        Real.exp
          (M.kernel.action M.mu (M.rootedTreePartialSum N w) x) := by
      rw [M.rootedTreeKernelSeriesAt_partialEval]
    _ = M.normalizedZeroTreeMap w (M.rootedTreePartialSum N w) x :=
      M.zeroFactor_mul_exp_kernel_eq_normalizedMap w _ x

theorem CompactBJRModel.rootedTreePartialSum_le_normalizedZeroTreeIter
    (M : CompactBJRModel S) (N : ℕ) {w : ℝ} (hw : 0 ≤ w) (x : S) :
    M.rootedTreePartialSum N w x ≤
      M.normalizedZeroTreeIter w N x := by
  induction N generalizing x with
  | zero => simp
  | succ N ih =>
      rw [M.normalizedZeroTreeIter_succ]
      exact (M.rootedTreePartialSum_succ_le_normalizedZeroTreeMap N hw x).trans
        (M.normalizedZeroTreeMap_mono w hw _ _ ih x)

end PerronWright
