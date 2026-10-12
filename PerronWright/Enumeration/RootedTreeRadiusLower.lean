import PerronWright.Enumeration.RootedTreeDomination

open scoped Classical Topology ENNReal NNReal
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Every actual labelled rooted-tree coefficient has sup norm at most one.
This is a consequence of finite-sum domination at the critical parameter,
not a convergence assumption. -/
theorem CompactBJRModel.typeRootedTreeEGF_coeff_norm_le_one
    (M : CompactBJRModel S) (n : ℕ) :
    ‖PowerSeries.coeff n M.typeRootedTreeEGF‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).2
  intro x
  rw [Real.norm_eq_abs,
    abs_of_nonneg (M.typeRootedTreeEGF_coeff_nonneg n x)]
  calc
    PowerSeries.coeff n M.typeRootedTreeEGF x ≤
        M.rootedTreePartialSum (n + 1) 1 x := by
      rw [M.rootedTreePartialSum_succ, ContinuousMap.add_apply,
        one_pow, one_smul]
      exact le_add_of_nonneg_left
        (M.rootedTreePartialSum_nonneg n zero_le_one x)
    _ ≤ M.normalizedZeroTreeIter 1 (n + 1) x :=
      M.rootedTreePartialSum_le_normalizedZeroTreeIter
        (n + 1) zero_le_one x
    _ ≤ 1 :=
      (M.normalizedZeroTreeIter_bounded 1 zero_le_one le_rfl
        (n + 1) x).2

/-- Complexification preserves the norm of every rooted-tree coefficient. -/
theorem CompactBJRModel.complexTypeRootedTreeEGF_coeff_norm
    (M : CompactBJRModel S) (n : ℕ) :
    ‖PowerSeries.coeff n M.complexTypeRootedTreeEGF‖ =
      ‖PowerSeries.coeff n M.typeRootedTreeEGF‖ := by
  rw [M.complexTypeRootedTreeEGF_coeff,
    continuousMapComplexifyRingHom_apply]
  change ‖ContinuousMap.realToRCLike ℂ
      (PowerSeries.coeff n M.typeRootedTreeEGF)‖ = _
  exact (ContinuousMap.isometry_realToRCLike S ℂ).norm_map_of_map_zero
    (map_zero (ContinuousMap.realToRCLikeStarAlgHom S ℂ)) _

/-- Each homogeneous term of the canonical complex Taylor series has norm
at most one. -/
theorem CompactBJRModel.complexTypeRootedTreeFMS_term_norm_le_one
    (M : CompactBJRModel S) (n : ℕ) :
    ‖M.complexTypeRootedTreeFMS n‖ ≤ 1 := by
  rw [CompactBJRModel.complexTypeRootedTreeFMS,
    oneDimensionalFormalMultilinearSeries,
    ContinuousMultilinearMap.norm_mkPiRing,
    M.complexTypeRootedTreeEGF_coeff_norm]
  exact M.typeRootedTreeEGF_coeff_norm_le_one n

/-- The canonical complex rooted-tree Taylor series has convergence radius
at least the critical value one. -/
theorem CompactBJRModel.one_le_complexTypeRootedTreeFMS_radius
    (M : CompactBJRModel S) :
    (1 : ℝ≥0∞) ≤ M.complexTypeRootedTreeFMS.radius := by
  simpa using M.complexTypeRootedTreeFMS.le_radius_of_bound 1
    (r := (1 : ℝ≥0)) (fun n => by
      simpa using M.complexTypeRootedTreeFMS_term_norm_le_one n)

end PerronWright
