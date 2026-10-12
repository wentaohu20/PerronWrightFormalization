import PerronWright.Analysis.TreeMonotone

/-! Geometric convergence of the actual zero-field least-tree iteration for `0 ≤ w < 1`. -/

open MeasureTheory
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

private theorem exp_sub_exp_le_sub_of_nonpos
    {a b : ℝ} (hba : b ≤ a) (ha : a ≤ 0) :
    Real.exp a - Real.exp b ≤ a - b := by
  have hba0 : b - a ≤ 0 := sub_nonpos.mpr hba
  have hdiff : 0 ≤ 1 - Real.exp (b - a) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr hba0)
  have hmul : Real.exp a * (1 - Real.exp (b - a)) ≤
      1 * (1 - Real.exp (b - a)) :=
    mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr ha) hdiff
  have hlin : 1 - Real.exp (b - a) ≤ a - b := by
    have h := Real.add_one_le_exp (b - a)
    linarith
  calc
    Real.exp a - Real.exp b =
        Real.exp a * (1 - Real.exp (b - a)) := by
          rw [Real.exp_sub]
          field_simp [ne_of_gt (Real.exp_pos a)]
    _ ≤ 1 - Real.exp (b - a) := by simpa using hmul
    _ ≤ a - b := hlin

theorem ContinuousKernel.realAction_sub (k : ContinuousKernel S)
    (mu : Measure S) [IsFiniteMeasure mu] (f g : C(S, ℝ)) :
    k.action mu (f - g) = k.action mu f - k.action mu g := by
  exact (k.actionLinearMap mu).map_sub f g

theorem CompactBJRModel.normalizedZeroTreeMap_order_lipschitz
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (w B : ℝ) (hw : 0 ≤ w)
    (V W : C(S, ℝ))
    (hVW : ∀ x, V x ≤ W x) (hW : ∀ x, W x ≤ 1)
    (hbound : ∀ x, W x - V x ≤ B * M.perronFunction hM x)
    (x : S) :
    M.normalizedZeroTreeMap w W x - M.normalizedZeroTreeMap w V x ≤
      w * B * M.perronFunction hM x := by
  let a := M.kernel.action M.mu (W - 1) x
  let b := M.kernel.action M.mu (V - 1) x
  have hba : b ≤ a :=
    M.kernel.realAction_mono M.mu (V - 1) (W - 1)
      (fun y => sub_le_sub_right (hVW y) 1) x
  have ha : a ≤ 0 := by
    change M.kernel.action M.mu (W - 1) x ≤ 0
    have h := M.kernel.realAction_mono M.mu (W - 1) 0
      (fun y => by simpa using sub_nonpos.mpr (hW y)) x
    simpa only [← M.kernel.actionCLM_apply, map_zero, ContinuousMap.zero_apply] using h
  have haction : a - b = M.kernel.action M.mu (W - V) x := by
    have hsub : (W - 1 : C(S, ℝ)) - (V - 1) = W - V := by abel
    change M.kernel.action M.mu (W - 1) x - M.kernel.action M.mu (V - 1) x =
      M.kernel.action M.mu (W - V) x
    rw [← ContinuousMap.sub_apply, ← M.kernel.realAction_sub M.mu, hsub]
  have hKbound : M.kernel.action M.mu (W - V) x ≤
      B * M.perronFunction hM x := by
    have h := M.kernel.realAction_mono M.mu (W - V)
      (B • M.perronFunction hM)
      (fun y => by simpa only [ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        smul_eq_mul] using hbound y) x
    rw [M.kernel.action_smul, M.perronFunction_fixed hM] at h
    simpa only [ContinuousMap.smul_apply, smul_eq_mul] using h
  calc
    M.normalizedZeroTreeMap w W x - M.normalizedZeroTreeMap w V x =
        w * (Real.exp a - Real.exp b) := by
          simp only [M.normalizedZeroTreeMap_apply]
          ring
    _ ≤ w * (a - b) :=
      mul_le_mul_of_nonneg_left (exp_sub_exp_le_sub_of_nonpos hba ha) hw
    _ = w * M.kernel.action M.mu (W - V) x := by rw [haction]
    _ ≤ w * (B * M.perronFunction hM x) :=
      mul_le_mul_of_nonneg_left hKbound hw
    _ = w * B * M.perronFunction hM x := by ring

theorem CompactBJRModel.normalizedZeroTreeIter_increment
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (w c : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hcu : ∀ x, c ≤ M.perronFunction hM x)
    (n : ℕ) (x : S) :
    M.normalizedZeroTreeIter w (n + 1) x -
      M.normalizedZeroTreeIter w n x ≤
      w ^ (n + 1) / c * M.perronFunction hM x := by
  induction n generalizing x with
  | zero =>
      have hfirst : M.normalizedZeroTreeIter w 1 x ≤ w := by
        rw [M.normalizedZeroTreeIter_succ, M.normalizedZeroTreeIter_zero]
        exact M.normalizedZeroTreeMap_le_w w hw 0 (fun y => by simp) x
      have hscale : w ≤ w / c * M.perronFunction hM x := by
        have h := mul_le_mul_of_nonneg_left (hcu x) hw
        apply (le_div_iff₀ hc).2 at h
        calc
          w ≤ w * M.perronFunction hM x / c := by simpa only [mul_comm w c] using h
          _ = w / c * M.perronFunction hM x := by ring
      simpa [M.normalizedZeroTreeIter_zero] using hfirst.trans hscale
  | succ n ih =>
      have hmono : ∀ y, M.normalizedZeroTreeIter w n y ≤
          M.normalizedZeroTreeIter w (n + 1) y :=
        M.normalizedZeroTreeIter_mono w hw n
      have hW : ∀ y, M.normalizedZeroTreeIter w (n + 1) y ≤ 1 :=
        fun y => (M.normalizedZeroTreeIter_bounded w hw hw1 (n + 1) y).2
      have hstep := M.normalizedZeroTreeMap_order_lipschitz hM
        w (w ^ (n + 1) / c) hw
        (M.normalizedZeroTreeIter w n)
        (M.normalizedZeroTreeIter w (n + 1)) hmono hW ih x
      rw [← M.normalizedZeroTreeIter_succ,
        ← M.normalizedZeroTreeIter_succ] at hstep
      convert hstep using 1; ring

theorem CompactBJRModel.normalizedZeroTreeIter_increment_norm
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (w c : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hcu : ∀ x, c ≤ M.perronFunction hM x)
    (n : ℕ) :
    ‖M.normalizedZeroTreeIter w (n + 1) - M.normalizedZeroTreeIter w n‖ ≤
      w ^ (n + 1) / c * ‖M.perronFunction hM‖ := by
  have hcoef : 0 ≤ w ^ (n + 1) / c := div_nonneg (pow_nonneg hw _) hc.le
  apply (ContinuousMap.norm_le _ (mul_nonneg hcoef (norm_nonneg _))).2
  intro x
  have hnonneg : 0 ≤ M.normalizedZeroTreeIter w (n + 1) x -
      M.normalizedZeroTreeIter w n x :=
    sub_nonneg.mpr (M.normalizedZeroTreeIter_mono w hw n x)
  have hpoint := M.normalizedZeroTreeIter_increment hM w c hw hw1 hc hcu n x
  have hu : M.perronFunction hM x ≤ ‖M.perronFunction hM‖ := by
    simpa only [Real.norm_eq_abs, abs_of_pos (M.perronFunction_pos hM x)] using
      (M.perronFunction hM).norm_coe_le_norm x
  calc
    ‖(M.normalizedZeroTreeIter w (n + 1) -
        M.normalizedZeroTreeIter w n) x‖ =
        M.normalizedZeroTreeIter w (n + 1) x -
          M.normalizedZeroTreeIter w n x := by
            simp only [ContinuousMap.sub_apply, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ ≤ w ^ (n + 1) / c * M.perronFunction hM x := hpoint
    _ ≤ w ^ (n + 1) / c * ‖M.perronFunction hM‖ :=
      mul_le_mul_of_nonneg_left hu hcoef

theorem CompactBJRModel.normalizedZeroTreeIter_converges
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) :
    ∃ V : C(S, ℝ), Filter.Tendsto (M.normalizedZeroTreeIter w)
      Filter.atTop (nhds V) := by
  obtain ⟨c, hc, hcu⟩ := M.perronFunction_uniform_pos hM
  have hbound : Summable (fun n : ℕ =>
      w ^ (n + 1) / c * ‖M.perronFunction hM‖) := by
    have hgeom : Summable (fun n : ℕ => w ^ n) :=
      summable_geometric_of_lt_one hw hw1
    have hfun : (fun n : ℕ => w ^ (n + 1) / c * ‖M.perronFunction hM‖) =
        (fun n : ℕ => (w / c * ‖M.perronFunction hM‖) * w ^ n) := by
      funext n
      rw [pow_succ]
      ring
    rw [hfun]
    exact hgeom.mul_left _
  have hdist : Summable (fun n : ℕ =>
      dist (M.normalizedZeroTreeIter w n)
        (M.normalizedZeroTreeIter w (n + 1))) := by
    apply Summable.of_nonneg_of_le (fun n => dist_nonneg) ?_ hbound
    intro n
    rw [dist_eq_norm, norm_sub_rev]
    exact M.normalizedZeroTreeIter_increment_norm hM w c hw hw1.le hc hcu n
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)

theorem CompactBJRModel.normalizedZeroTreeIter_converges_fixed
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) :
    ∃ V : C(S, ℝ),
      Filter.Tendsto (M.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
      M.normalizedZeroTreeMap w V = V := by
  obtain ⟨V, hV⟩ := M.normalizedZeroTreeIter_converges hM w hw hw1
  refine ⟨V, hV, ?_⟩
  apply ContinuousMap.ext
  intro x
  have hcont : Continuous (fun U : C(S, ℝ) =>
      M.normalizedZeroTreeMap w U x) := by
    change Continuous (fun U : C(S, ℝ) =>
      w * Real.exp (M.kernel.action M.mu (U - 1) x))
    have hlinear : Continuous (fun U : C(S, ℝ) =>
        M.kernel.action M.mu (U - 1) x) := by
      change Continuous (fun U : C(S, ℝ) =>
        ((M.kernel.actionCLM M.mu) (U - 1)) x)
      fun_prop
    exact continuous_const.mul (Real.continuous_exp.comp hlinear)
  have hmap : Filter.Tendsto
      (fun n => M.normalizedZeroTreeMap w (M.normalizedZeroTreeIter w n) x)
      Filter.atTop (nhds (M.normalizedZeroTreeMap w V x)) :=
    (hcont.tendsto V).comp hV
  have hshift : Filter.Tendsto
      (fun n => M.normalizedZeroTreeIter w (n + 1) x)
      Filter.atTop (nhds (V x)) := by
    exact ((continuous_eval_const x).tendsto V).comp
      (hV.comp (Filter.tendsto_add_atTop_nat 1))
  have hsame : (fun n => M.normalizedZeroTreeMap w (M.normalizedZeroTreeIter w n) x) =
      (fun n => M.normalizedZeroTreeIter w (n + 1) x) := by
    funext n
    rfl
  rw [hsame] at hmap
  exact tendsto_nhds_unique hmap hshift

theorem CompactBJRModel.normalizedZeroTreeIter_least_fixed
    (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) :
    ∃ V : C(S, ℝ),
      Filter.Tendsto (M.normalizedZeroTreeIter w) Filter.atTop (nhds V) ∧
      (∀ x, 0 ≤ V x ∧ V x ≤ 1) ∧
      M.normalizedZeroTreeMap w V = V ∧
      ∀ W : C(S, ℝ), (∀ x, 0 ≤ W x) →
        M.normalizedZeroTreeMap w W = W → ∀ x, V x ≤ W x := by
  obtain ⟨V, hV, hfix⟩ := M.normalizedZeroTreeIter_converges_fixed hM w hw hw1
  have hpoint (x : S) : Filter.Tendsto
      (fun n => M.normalizedZeroTreeIter w n x) Filter.atTop (nhds (V x)) :=
    ((continuous_eval_const x).tendsto V).comp hV
  refine ⟨V, hV, ?_, hfix, ?_⟩
  · intro x
    exact ⟨ge_of_tendsto' (hpoint x)
      (fun n => (M.normalizedZeroTreeIter_bounded w hw hw1.le n x).1),
      le_of_tendsto' (hpoint x)
      (fun n => (M.normalizedZeroTreeIter_bounded w hw hw1.le n x).2)⟩
  · intro W hW hWfix x
    exact le_of_tendsto' (hpoint x)
      (fun n => M.normalizedZeroTreeIter_le_fixed w hw W hW hWfix n x)

end PerronWright
