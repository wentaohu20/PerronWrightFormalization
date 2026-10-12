import PerronWright.Analysis.TreeFoldSquareRoot

open MeasureTheory
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem ContinuousKernel.realAction_mono (k : ContinuousKernel S)
    (mu : Measure S) [IsFiniteMeasure mu] (f g : C(S, ℝ))
    (hfg : ∀ y, f y ≤ g y) (x : S) :
    k.action mu f x ≤ k.action mu g x := by
  rw [k.action_apply mu f x, k.action_apply mu g x]
  have hf : Integrable (fun y => k x y * f y) mu :=
    ((k.rows x).continuous.mul f.continuous).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have hg : Integrable (fun y => k x y * g y) mu :=
    ((k.rows x).continuous.mul g.continuous).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  apply integral_mono hf hg
  intro y
  exact mul_le_mul_of_nonneg_left (hfg y) (k.nonneg x y)

theorem ContinuousKernel.realAction_nonneg (k : ContinuousKernel S)
    (mu : Measure S) [IsFiniteMeasure mu] (f : C(S, ℝ))
    (hf : ∀ y, 0 ≤ f y) (x : S) :
    0 ≤ k.action mu f x := by
  rw [k.action_apply mu f x]
  exact integral_nonneg (fun y => mul_nonneg (k.nonneg x y) (hf y))

def CompactBJRModel.normalizedZeroTreeMap (M : CompactBJRModel S)
    (w : ℝ) (V : C(S, ℝ)) : C(S, ℝ) :=
  ⟨fun x => w * Real.exp (M.kernel.action M.mu (V - 1) x),
    continuous_const.mul ((M.kernel.action M.mu (V - 1)).continuous.rexp)⟩

theorem CompactBJRModel.normalizedZeroTreeMap_apply
    (M : CompactBJRModel S) (w : ℝ) (V : C(S, ℝ)) (x : S) :
    M.normalizedZeroTreeMap w V x =
      w * Real.exp (M.kernel.action M.mu (V - 1) x) := rfl

theorem CompactBJRModel.normalizedZeroTreeMap_nonneg
    (M : CompactBJRModel S) (w : ℝ) (hw : 0 ≤ w)
    (V : C(S, ℝ)) (x : S) :
    0 ≤ M.normalizedZeroTreeMap w V x := by
  rw [M.normalizedZeroTreeMap_apply]
  exact mul_nonneg hw (Real.exp_pos _).le

theorem CompactBJRModel.normalizedZeroTreeMap_mono
    (M : CompactBJRModel S) (w : ℝ) (hw : 0 ≤ w)
    (V W : C(S, ℝ)) (hVW : ∀ x, V x ≤ W x) (x : S) :
    M.normalizedZeroTreeMap w V x ≤ M.normalizedZeroTreeMap w W x := by
  rw [M.normalizedZeroTreeMap_apply, M.normalizedZeroTreeMap_apply]
  gcongr
  exact M.kernel.realAction_mono M.mu (V - 1) (W - 1)
    (fun y => sub_le_sub_right (hVW y) 1) x

theorem CompactBJRModel.normalizedZeroTreeMap_le_w
    (M : CompactBJRModel S) (w : ℝ) (hw : 0 ≤ w)
    (V : C(S, ℝ)) (hV : ∀ x, V x ≤ 1) (x : S) :
    M.normalizedZeroTreeMap w V x ≤ w := by
  have hK : M.kernel.action M.mu (V - 1) x ≤ 0 := by
    have h := M.kernel.realAction_mono M.mu (V - 1) 0
      (fun y => by simpa using sub_nonpos.mpr (hV y)) x
    simpa only [← M.kernel.actionCLM_apply, map_zero, ContinuousMap.zero_apply] using h
  rw [M.normalizedZeroTreeMap_apply]
  exact mul_le_of_le_one_right hw (Real.exp_le_one_iff.mpr hK)

def CompactBJRModel.normalizedZeroTreeIter (M : CompactBJRModel S)
    (w : ℝ) : ℕ → C(S, ℝ)
  | 0 => 0
  | n + 1 => M.normalizedZeroTreeMap w (M.normalizedZeroTreeIter w n)

@[simp] theorem CompactBJRModel.normalizedZeroTreeIter_zero
    (M : CompactBJRModel S) (w : ℝ) :
    M.normalizedZeroTreeIter w 0 = 0 := rfl

@[simp] theorem CompactBJRModel.normalizedZeroTreeIter_succ
    (M : CompactBJRModel S) (w : ℝ) (n : ℕ) :
    M.normalizedZeroTreeIter w (n + 1) =
      M.normalizedZeroTreeMap w (M.normalizedZeroTreeIter w n) := rfl

theorem CompactBJRModel.normalizedZeroTreeIter_bounded
    (M : CompactBJRModel S) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (n : ℕ) (x : S) :
    0 ≤ M.normalizedZeroTreeIter w n x ∧
      M.normalizedZeroTreeIter w n x ≤ 1 := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [M.normalizedZeroTreeIter_succ]
      exact ⟨M.normalizedZeroTreeMap_nonneg w hw _ x,
        (M.normalizedZeroTreeMap_le_w w hw _ (fun y => (ih y).2) x).trans hw1⟩

theorem CompactBJRModel.normalizedZeroTreeIter_mono
    (M : CompactBJRModel S) (w : ℝ) (hw : 0 ≤ w)
    (n : ℕ) (x : S) :
    M.normalizedZeroTreeIter w n x ≤
      M.normalizedZeroTreeIter w (n + 1) x := by
  induction n generalizing x with
  | zero =>
      simpa using M.normalizedZeroTreeMap_nonneg w hw 0 x
  | succ n ih =>
      rw [M.normalizedZeroTreeIter_succ, M.normalizedZeroTreeIter_succ,
        M.normalizedZeroTreeIter_succ]
      exact M.normalizedZeroTreeMap_mono w hw _ _ ih x

theorem CompactBJRModel.normalizedZeroTreeIter_le_fixed
    (M : CompactBJRModel S) (w : ℝ) (hw : 0 ≤ w)
    (V : C(S, ℝ)) (hV : ∀ x, 0 ≤ V x)
    (hfix : M.normalizedZeroTreeMap w V = V)
    (n : ℕ) (x : S) :
    M.normalizedZeroTreeIter w n x ≤ V x := by
  induction n generalizing x with
  | zero => simpa using hV x
  | succ n ih =>
      rw [M.normalizedZeroTreeIter_succ]
      calc
        _ ≤ M.normalizedZeroTreeMap w V x :=
          M.normalizedZeroTreeMap_mono w hw _ _ ih x
        _ = V x := congrFun (congrArg DFunLike.coe hfix) x

end PerronWright
