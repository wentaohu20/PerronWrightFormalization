import PerronWright.Analysis.FiniteIrreducibleComplex
import PerronWright.Analysis.TreeMonotone
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The genuine finite least-tree branch and its critical endpoint

The branch is constructed by iterating the actual normalized tree map from
zero. Finite discrete continuity gives uniform convergence of the bounded
monotone iteration, including the critical activity. Positive Perron weights
and the strict exponential inequality prove uniqueness at activity one.
No primitive power or least-branch interface is assumed.
-/

open Filter Topology
open scoped BigOperators

noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

omit [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S] in
theorem weighted_action_identity (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical)
    (q : S → ℝ) :
    (∑ a, M.weight a * M.perronFunction hcrit a * M.action q a) =
      ∑ a, M.weight a * M.perronFunction hcrit a * q a := by
  unfold action
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hu := congrFun (M.perronFunction_fixed hcrit) b
  change (∑ a, M.kernel b a * M.weight a * M.perronFunction hcrit a) =
    M.perronFunction hcrit b at hu
  calc
    (∑ a, M.weight a * M.perronFunction hcrit a *
        (M.kernel a b * M.weight b * q b)) =
      (M.weight b * q b) * ∑ a, M.kernel b a * M.weight a * M.perronFunction hcrit a := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [M.symmetric a b]
        ring
    _ = M.weight b * M.perronFunction hcrit b * q b := by rw [hu]; ring

theorem normalizedZeroTreeMap_one_unique (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) (V : C(S, ℝ))
    (hfix : M.bjrModel.normalizedZeroTreeMap 1 V = V) : V = 1 := by
  let q : S → ℝ := fun a ↦ 1 - V a
  have hfixed (a : S) : q a = 1 - Real.exp (-M.action q a) := by
    have hx := congrArg (fun U : C(S, ℝ) ↦ U a) hfix
    rw [CompactBJRModel.normalizedZeroTreeMap_apply] at hx
    simp only [one_mul] at hx
    change Real.exp (M.continuousKernel.action M.measure (V - 1) a) = V a at hx
    rw [M.continuous_action_apply] at hx
    change Real.exp (M.action (fun b ↦ V b - 1) a) = V a at hx
    have hneg : M.action (fun b ↦ V b - 1) a = -M.action q a := by
      simp only [action, q, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [hneg] at hx
    change 1 - V a = 1 - Real.exp (-M.action q a)
    rw [hx]
  have hn (a : S) : 0 ≤ M.action q a - q a := by
    rw [hfixed a]
    have he := Real.one_sub_le_exp_neg (M.action q a)
    linarith
  have hs : (∑ a, M.weight a * M.perronFunction hcrit a * (M.action q a - q a)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (M.weighted_action_identity hcrit q)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ ↦ mul_nonneg (mul_pos (M.weight_pos a) (M.perronFunction_pos hcrit a)).le
      (hn a))).mp hs
  ext a
  have hgap : M.action q a - q a = 0 :=
    (mul_eq_zero.mp (hall a (Finset.mem_univ a))).resolve_left
      (mul_pos (M.weight_pos a) (M.perronFunction_pos hcrit a)).ne'
  have hK : M.action q a = 0 := by
    by_contra hk
    have he := Real.one_sub_lt_exp_neg hk
    rw [hfixed a] at hgap
    linarith
  have hq : q a = 0 := by simpa only [hK, neg_zero, Real.exp_zero, sub_self] using hfixed a
  change V a = 1
  change 1 - V a = 0 at hq
  linarith

/-- The actual zero-start iteration has a least nonnegative fixed point for
every subcritical or critical activity. Finiteness, not primitivity, gives
the required uniform convergence. -/
theorem normalizedZeroTreeIter_least_fixed (M : FiniteIrreducibleModel S)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    ∃ V : C(S, ℝ), Tendsto (M.bjrModel.normalizedZeroTreeIter w) atTop (𝓝 V) ∧
      (∀ a, 0 ≤ V a ∧ V a ≤ 1) ∧ M.bjrModel.normalizedZeroTreeMap w V = V ∧
      ∀ W : C(S, ℝ), (∀ a, 0 ≤ W a) →
        M.bjrModel.normalizedZeroTreeMap w W = W → ∀ a, V a ≤ W a := by
  let F := M.bjrModel.normalizedZeroTreeIter w
  have hm (a : S) : Monotone (fun n ↦ F n a) :=
    monotone_nat_of_le_succ (fun n ↦ M.bjrModel.normalizedZeroTreeIter_mono w hw n a)
  have hb (a : S) : BddAbove (Set.range (fun n ↦ F n a)) := by
    refine ⟨1, ?_⟩
    rintro y ⟨n, rfl⟩
    exact (M.bjrModel.normalizedZeroTreeIter_bounded w hw hw1 n a).2
  let V : C(S, ℝ) := ⟨fun a ↦ ⨆ n, F n a, continuous_of_discreteTopology⟩
  have hp (a : S) : Tendsto (fun n ↦ F n a) atTop (𝓝 (V a)) :=
    tendsto_atTop_ciSup (hm a) (hb a)
  have hlim : Tendsto F atTop (𝓝 V) := by
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    exact Monotone.tendstoUniformly_of_forall_tendsto (fun n ↦ (F n).continuous)
      (fun m n h a ↦ hm a h) V.continuous hp
  have hfix : M.bjrModel.normalizedZeroTreeMap w V = V := by
    ext a
    have hc : Continuous (fun U : C(S, ℝ) ↦ M.bjrModel.normalizedZeroTreeMap w U a) := by
      change Continuous (fun U : C(S, ℝ) ↦
        w * Real.exp (M.continuousKernel.actionCLM M.measure (U - 1) a))
      fun_prop
    have hmap := (hc.tendsto V).comp hlim
    have hshift := (hp a).comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hmap hshift
  refine ⟨V, hlim, ?_, hfix, ?_⟩
  · intro a
    exact ⟨ge_of_tendsto' (hp a) (fun n ↦
      (M.bjrModel.normalizedZeroTreeIter_bounded w hw hw1 n a).1),
      le_of_tendsto' (hp a) (fun n ↦
      (M.bjrModel.normalizedZeroTreeIter_bounded w hw hw1 n a).2)⟩
  · intro W hW hWfix a
    exact le_of_tendsto' (hp a) (fun n ↦
      M.bjrModel.normalizedZeroTreeIter_le_fixed w hw W hW hWfix n a)

theorem normalizedZeroTreeIter_one_converges (M : FiniteIrreducibleModel S)
    (hcrit : M.IsCritical) :
    Tendsto (M.bjrModel.normalizedZeroTreeIter 1) atTop (𝓝 (1 : C(S, ℝ))) := by
  obtain ⟨V, hV, _, hfix, _⟩ := M.normalizedZeroTreeIter_least_fixed 1 zero_le_one le_rfl
  simpa only [M.normalizedZeroTreeMap_one_unique hcrit V hfix] using hV

end PerronWright.FiniteIrreducibleModel
