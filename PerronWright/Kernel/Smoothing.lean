import PerronWright.Kernel.SpectrumBridge

/-!
# Smoothing from `L²` to continuous functions

The integral kernel sends every `L²(μ)` vector to a continuous function.
The composition with the canonical inclusion into `L²` is proved to equal
the operator characterized by `(B1)`; it is not an additional model field.
-/

open MeasureTheory

noncomputable section

namespace PerronWright
namespace CompactBJRModel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The continuous representative obtained by applying the kernel to an
arbitrary `L²` vector. -/
def smooth (M : CompactBJRModel S) (v : M.L2) : C(S, ℝ) where
  toFun x := inner ℝ v (ContinuousMap.toLp 2 M.mu ℝ (M.kernel.rows x))
  continuous_toFun := continuous_const.inner
    ((ContinuousMap.toLp 2 M.mu ℝ).continuous.comp M.kernel.rows.continuous)

@[simp] theorem smooth_apply (M : CompactBJRModel S) (v : M.L2) (x : S) :
    M.smooth v x = inner ℝ v (ContinuousMap.toLp 2 M.mu ℝ (M.kernel.rows x)) := rfl

theorem smooth_add (M : CompactBJRModel S) (v w : M.L2) :
    M.smooth (v + w) = M.smooth v + M.smooth w := by
  ext x
  simp [inner_add_left]

theorem smooth_smul (M : CompactBJRModel S) (c : ℝ) (v : M.L2) :
    M.smooth (c • v) = c • M.smooth v := by
  ext x
  simp [inner_smul_left]

theorem norm_smooth_le (M : CompactBJRModel S) (v : M.L2) :
    ‖M.smooth v‖ ≤
      (‖(ContinuousMap.toLp 2 M.mu ℝ : C(S, ℝ) →L[ℝ] M.L2)‖ *
        ‖M.kernel.toContinuousMap‖) * ‖v‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro x
  have hrow : ‖M.kernel.rows x‖ ≤ ‖M.kernel.toContinuousMap‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro y
    exact M.kernel.toContinuousMap.norm_coe_le_norm (x, y)
  calc
    ‖M.smooth v x‖ ≤ ‖v‖ * ‖ContinuousMap.toLp 2 M.mu ℝ (M.kernel.rows x)‖ := by
      exact norm_inner_le_norm (𝕜 := ℝ) v
        (ContinuousMap.toLp 2 M.mu ℝ (M.kernel.rows x))
    _ ≤ ‖v‖ * (‖(ContinuousMap.toLp 2 M.mu ℝ : C(S, ℝ) →L[ℝ] M.L2)‖ *
        ‖M.kernel.rows x‖) := by
      gcongr
      exact (ContinuousMap.toLp 2 M.mu ℝ : C(S, ℝ) →L[ℝ] M.L2).le_opNorm _
    _ ≤ ‖v‖ * (‖(ContinuousMap.toLp 2 M.mu ℝ : C(S, ℝ) →L[ℝ] M.L2)‖ *
        ‖M.kernel.toContinuousMap‖) := by gcongr
    _ = _ := by ring

/-- Smoothing as a continuous linear map from `L²` to `C(S)`. -/
def smoothCLM (M : CompactBJRModel S) : M.L2 →L[ℝ] C(S, ℝ) :=
  LinearMap.mkContinuous
    { toFun := M.smooth
      map_add' := M.smooth_add
      map_smul' := M.smooth_smul }
    (‖(ContinuousMap.toLp 2 M.mu ℝ : C(S, ℝ) →L[ℝ] M.L2)‖ *
      ‖M.kernel.toContinuousMap‖) M.norm_smooth_le

@[simp] theorem smoothCLM_apply (M : CompactBJRModel S) (v : M.L2) :
    M.smoothCLM v = M.smooth v := rfl

@[simp] theorem smooth_toLp (M : CompactBJRModel S) (f : C(S, ℝ)) :
    M.smooth (ContinuousMap.toLp 2 M.mu ℝ f) = M.kernel.action M.mu f := by
  ext x
  rw [smooth_apply, ContinuousMap.inner_toLp, ContinuousKernel.action_apply]
  simp only [conj_trivial, ContinuousKernel.rows_apply]

/-- Every value of the associated `L²` operator has the explicitly
constructed continuous representative. -/
theorem IsAssociatedL2Operator.smoothing (M : CompactBJRModel S)
    (K : M.L2 →L[ℝ] M.L2) (hK : M.IsAssociatedL2Operator K) (v : M.L2) :
    ContinuousMap.toLp 2 M.mu ℝ (M.smooth v) = K v := by
  have hdense : DenseRange
      (ContinuousMap.toLp 2 M.mu ℝ : C(S, ℝ) →L[ℝ] M.L2) :=
    ContinuousMap.toLp_denseRange ℝ M.mu ℝ (by norm_num)
  have heq : (fun w : M.L2 => ContinuousMap.toLp 2 M.mu ℝ (M.smoothCLM w)) = K := by
    apply hdense.equalizer
      ((ContinuousMap.toLp 2 M.mu ℝ).continuous.comp M.smoothCLM.continuous)
      K.continuous
    funext f
    simp only [Function.comp_apply, smoothCLM_apply, smooth_toLp]
    exact (hK.intertwines M K f).symm
  exact congr_fun heq v

/-- Every nonzero `L²` eigenvector with nonzero eigenvalue has a continuous
representative satisfying the pointwise eigenvalue equation.  No spectral
regularity of `L²` representatives is postulated. -/
theorem IsAssociatedL2Operator.exists_continuous_eigenvector
    (M : CompactBJRModel S) (K : M.L2 →L[ℝ] M.L2)
    (hK : M.IsAssociatedL2Operator K) {v : M.L2} {lam : ℝ}
    (hlam : lam ≠ 0) (hv : K v = lam • v) (hv_ne : v ≠ 0) :
    ∃ u : C(S, ℝ), u ≠ 0 ∧ ContinuousMap.toLp 2 M.mu ℝ u = v ∧
      M.kernel.action M.mu u = lam • u := by
  let u : C(S, ℝ) := lam⁻¹ • M.smooth v
  have hu : ContinuousMap.toLp 2 M.mu ℝ u = v := by
    dsimp only [u]
    rw [map_smul, hK.smoothing M K v, hv, smul_smul]
    simp [hlam]
  refine ⟨u, ?_, hu, ?_⟩
  · intro hz
    apply hv_ne
    rw [← hu, hz, map_zero]
  · apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) M.mu
    rw [map_smul, ← hK.intertwines M K u, hu, hv]

end CompactBJRModel
end PerronWright
