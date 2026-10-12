import PerronWright.Analysis.TreeEndpoint
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Topology.Order.MonotoneConvergence

/-! Compactness, endpoint uniqueness, and Dini convergence of the normalized tree iteration. -/

open MeasureTheory Filter
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

omit [MeasurableSpace S] [BorelSpace S] in
private theorem real_exp_continuousMap_apply (f : C(S, ℝ)) (x : S) :
    NormedSpace.exp f x = Real.exp (f x) := by
  simpa only [ContinuousMap.evalAlgHom_apply, ← Real.exp_eq_exp_ℝ] using
    NormedSpace.map_exp (ContinuousMap.evalAlgHom ℝ ℝ x)
      (ContinuousMap.evalCLM ℝ x).continuous f

theorem CompactBJRModel.normalizedZeroTreeIter_one_precompact
    (M : CompactBJRModel S) :
    ∃ K : Set C(S, ℝ), IsCompact K ∧
      ∀ n : ℕ, M.normalizedZeroTreeIter 1 (n + 1) ∈ K := by
  obtain ⟨C, hC, hKC⟩ :=
    (M.kernel.isCompactOperator_actionCLM M.mu).image_closedBall_subset_compact 1
  let K : Set C(S, ℝ) := NormedSpace.exp '' C
  refine ⟨K, hC.image NormedSpace.exp_continuous, ?_⟩
  intro n
  have hnorm : ‖M.normalizedZeroTreeIter 1 n - 1‖ ≤ 1 := by
    apply (ContinuousMap.norm_le _ (by norm_num)).2
    intro x
    have hb := M.normalizedZeroTreeIter_bounded 1 (by norm_num) (by norm_num) n x
    rw [ContinuousMap.sub_apply, ContinuousMap.one_apply, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hball : M.normalizedZeroTreeIter 1 n - 1 ∈ Metric.closedBall (0 : C(S, ℝ)) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hK : M.kernel.actionCLM M.mu (M.normalizedZeroTreeIter 1 n - 1) ∈ C :=
    hKC ⟨_, hball, rfl⟩
  refine ⟨M.kernel.actionCLM M.mu (M.normalizedZeroTreeIter 1 n - 1), hK, ?_⟩
  apply ContinuousMap.ext
  intro x
  rw [M.normalizedZeroTreeIter_succ, M.normalizedZeroTreeMap_apply]
  simp only [one_mul]
  rw [real_exp_continuousMap_apply]
  rfl

theorem CompactBJRModel.normalizedZeroTreeIter_one_subseq_limit
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (fun n => M.normalizedZeroTreeIter 1 (φ n + 1))
        Filter.atTop (nhds (1 : C(S, ℝ))) := by
  obtain ⟨K, hK, hmem⟩ := M.normalizedZeroTreeIter_one_precompact
  let F : ℕ → C(S, ℝ) := fun n => M.normalizedZeroTreeIter 1 (n + 1)
  obtain ⟨V, _, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := F) hmem
  have hmono (x : S) : Monotone (fun n => F n x) := by
    apply monotone_nat_of_le_succ
    intro n
    exact M.normalizedZeroTreeIter_mono 1 (by norm_num) (n + 1) x
  have hfix : M.normalizedZeroTreeMap 1 V = V := by
    apply ContinuousMap.ext
    intro x
    have hcont : Continuous (fun U : C(S, ℝ) => M.normalizedZeroTreeMap 1 U x) := by
      change Continuous (fun U : C(S, ℝ) =>
        1 * Real.exp (M.kernel.action M.mu (U - 1) x))
      have hlinear : Continuous (fun U : C(S, ℝ) =>
          M.kernel.action M.mu (U - 1) x) := by
        change Continuous (fun U : C(S, ℝ) =>
          ((M.kernel.actionCLM M.mu) (U - 1)) x)
        fun_prop
      exact continuous_const.mul (Real.continuous_exp.comp hlinear)
    have hpoint : Filter.Tendsto (fun n => F (φ n) x) Filter.atTop (nhds (V x)) :=
      ((continuous_eval_const x).tendsto V).comp hlim
    have hmap : Filter.Tendsto (fun n =>
        M.normalizedZeroTreeMap 1 (F (φ n)) x)
        Filter.atTop (nhds (M.normalizedZeroTreeMap 1 V x)) :=
      (hcont.tendsto V).comp hlim
    have hshift : Filter.Tendsto (fun n => F (φ n + 1) x)
        Filter.atTop (nhds (V x)) := by
      apply Filter.Tendsto.squeeze hpoint
        (hpoint.comp (Filter.tendsto_add_atTop_nat 1))
      · intro n
        exact hmono x (Nat.le_succ (φ n))
      · intro n
        exact hmono x (Nat.succ_le_iff.mpr (hφ (Nat.lt_succ_self n)))
    have hsame : (fun n => M.normalizedZeroTreeMap 1 (F (φ n)) x) =
        (fun n => F (φ n + 1) x) := by
      funext n
      rfl
    rw [hsame] at hmap
    exact tendsto_nhds_unique hmap hshift
  have hV : V = 1 := M.normalizedZeroTreeMap_one_unique hM V hfix
  exact ⟨φ, hφ, hV ▸ hlim⟩

theorem CompactBJRModel.normalizedZeroTreeIter_one_converges
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    Filter.Tendsto (M.normalizedZeroTreeIter 1)
      Filter.atTop (nhds (1 : C(S, ℝ))) := by
  obtain ⟨φ, hφ, hsub⟩ := M.normalizedZeroTreeIter_one_subseq_limit hM
  let F : ℕ → C(S, ℝ) := fun n => M.normalizedZeroTreeIter 1 (n + 1)
  have hmono (x : S) : Monotone (fun n => F n x) := by
    apply monotone_nat_of_le_succ
    intro n
    exact M.normalizedZeroTreeIter_mono 1 (by norm_num) (n + 1) x
  have hbdd (x : S) : BddAbove (Set.range (fun n => F n x)) := by
    refine ⟨1, ?_⟩
    rintro y ⟨n, rfl⟩
    exact (M.normalizedZeroTreeIter_bounded 1 (by norm_num) (by norm_num)
      (n + 1) x).2
  have hpoint (x : S) : Filter.Tendsto (fun n => F n x)
      Filter.atTop (nhds (1 : ℝ)) := by
    have hbase := tendsto_atTop_ciSup (hmono x) (hbdd x)
    have hsubpoint : Filter.Tendsto (fun n => F (φ n) x)
        Filter.atTop (nhds (1 : ℝ)) :=
      ((continuous_eval_const x).tendsto (1 : C(S, ℝ))).comp hsub
    have heq : (⨆ n, F n x) = 1 :=
      tendsto_nhds_unique (hbase.comp hφ.tendsto_atTop) hsubpoint
    simpa only [heq] using hbase
  have huni : TendstoUniformly (fun n x => F n x) (fun _ => (1 : ℝ))
      Filter.atTop := by
    exact Monotone.tendstoUniformly_of_forall_tendsto
      (fun n => (F n).continuous)
      (fun m n h x => hmono x h)
      continuous_const hpoint
  have hF : Filter.Tendsto F Filter.atTop (nhds (1 : C(S, ℝ))) := by
    exact ContinuousMap.tendsto_iff_tendstoUniformly.mpr huni
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp hF

end PerronWright
