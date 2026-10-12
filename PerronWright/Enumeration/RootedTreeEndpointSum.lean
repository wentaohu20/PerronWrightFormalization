import PerronWright.Enumeration.RootedTreeRadiusExact

/-!
# The genuine rooted-tree series at the critical endpoint

The actual nonnegative labelled-tree coefficients have radius exactly one.
This file proves the missing endpoint statement: their finite sums at
activity one converge uniformly to the constant profile one.  The proof is
an Abel-type order squeeze from a subcritical real activity, not an
assertion of complex convergence on the whole critical circle.
-/

open Filter
open scoped Classical Topology ENNReal NNReal
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Increasing a nonnegative real activity increases every finite genuine
rooted-tree sum pointwise. -/
theorem CompactBJRModel.rootedTreePartialSum_mono_parameter
    (M : CompactBJRModel S) (N : ℕ) {v w : ℝ}
    (hv : 0 ≤ v) (hvw : v ≤ w) (x : S) :
    M.rootedTreePartialSum N v x ≤ M.rootedTreePartialSum N w x := by
  unfold CompactBJRModel.rootedTreePartialSum
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  exact Finset.sum_le_sum fun k hk =>
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv hvw k)
      (M.typeRootedTreeEGF_coeff_nonneg k x)

/-- Every finite genuine rooted-tree sum at the critical activity is bounded
above by the critical physical endpoint profile. -/
theorem CompactBJRModel.rootedTreePartialSum_at_one_le_one
    (M : CompactBJRModel S) (N : ℕ) (x : S) :
    M.rootedTreePartialSum N 1 x ≤ 1 := by
  exact (M.rootedTreePartialSum_le_normalizedZeroTreeIter N zero_le_one x).trans
    (M.normalizedZeroTreeIter_bounded 1 zero_le_one le_rfl N x).2

/-- At a fixed truncation, the uniform deficit at the endpoint is no larger
than the deficit at any nonnegative subcritical activity. -/
theorem CompactBJRModel.rootedTreePartialSum_one_gap_le
    (M : CompactBJRModel S) (N : ℕ) {w : ℝ}
    (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    ‖M.rootedTreePartialSum N 1 - 1‖ ≤
      ‖M.rootedTreePartialSum N w - 1‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro x
  have hpw1 : M.rootedTreePartialSum N w x ≤
      M.rootedTreePartialSum N 1 x :=
    M.rootedTreePartialSum_mono_parameter N hw hw1 x
  have hp1 : M.rootedTreePartialSum N 1 x ≤ 1 :=
    M.rootedTreePartialSum_at_one_le_one N x
  have hpw : M.rootedTreePartialSum N w x ≤ 1 := hpw1.trans hp1
  have hpoint :
      ‖(M.rootedTreePartialSum N 1 - 1) x‖ ≤
        ‖(M.rootedTreePartialSum N w - 1) x‖ := by
    simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply,
      Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr hp1),
      abs_of_nonpos (sub_nonpos.mpr hpw)]
    linarith
  exact hpoint.trans
    ((M.rootedTreePartialSum N w - 1).norm_coe_le_norm x)

/-- The genuine finite labelled rooted-tree sums converge uniformly to the
constant profile one at the critical activity. -/
theorem CompactBJRModel.rootedTreePartialSum_tendsto_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    Filter.Tendsto (fun N => M.rootedTreePartialSum N 1)
      Filter.atTop (nhds (1 : C(S, ℝ))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨δ, hδ, hnear⟩ :=
    M.normalizedZeroTreeIter_limit_near_one hM (ε / 2) hε2
  let η : ℝ := min (δ / 2) (1 / 2)
  let w : ℝ := 1 - η
  have hη : 0 < η := lt_min (half_pos hδ) (by norm_num)
  have hηδ : η < δ :=
    (min_le_left (δ / 2) (1 / 2)).trans_lt (half_lt_self hδ)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  have hw : 0 ≤ w := by
    dsimp only [w]
    linarith
  have hw1 : w < 1 := by
    dsimp only [w]
    linarith
  have hclose : |w - 1| < δ := by
    have hwsub : w - 1 = -η := by
      dsimp only [w]
      ring
    rw [hwsub, abs_neg, abs_of_pos hη]
    exact hηδ
  obtain ⟨V, hVlim, -, hVclose⟩ := hnear w hw hw1 hclose
  obtain ⟨W, hWlim, -, -, hseriesW⟩ :=
    M.rootedTreeSeries_eq_physical_fixedPoint hM w hw hw1
  have hVW : V = W := tendsto_nhds_unique hVlim hWlim
  have hseriesReal : M.rootedTreeSeriesReal w = V := by
    unfold CompactBJRModel.rootedTreeSeriesReal
    rw [hseriesW, ← hVW]
    apply ContinuousMap.ext
    intro x
    simp only [ContinuousMap.rclikeToReal_apply,
      TreeRealComplexBridge.complexify_apply]
    change ((V x : ℂ).re) = V x
    exact Complex.ofReal_re (V x)
  have hwBall : (w : ℂ) ∈ Metric.eball 0 (1 : ℝ≥0∞) := by
    rw [← ENNReal.coe_one, Metric.eball_coe]
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hw, NNReal.coe_one] using hw1
  have hconv : (w : ℂ) ∈
      Metric.eball 0 M.complexTypeRootedTreeFMS.radius :=
    Metric.eball_subset_eball M.one_le_complexTypeRootedTreeFMS_radius hwBall
  have hpartial := M.rootedTreePartialSum_tendsto_seriesReal w hconv
  rw [hseriesReal] at hpartial
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hpartial) (ε / 2) hε2
  refine ⟨N, ?_⟩
  intro n hn
  rw [dist_eq_norm]
  calc
    ‖M.rootedTreePartialSum n 1 - 1‖ ≤
        ‖M.rootedTreePartialSum n w - 1‖ :=
      M.rootedTreePartialSum_one_gap_le n hw hw1.le
    _ ≤ ‖M.rootedTreePartialSum n w - V‖ + ‖V - 1‖ := by
      have hsplit : M.rootedTreePartialSum n w - 1 =
          (M.rootedTreePartialSum n w - V) + (V - 1) := by
        abel
      rw [hsplit]
      exact norm_add_le _ _
    _ < ε := by
      have hn' : ‖M.rootedTreePartialSum n w - V‖ < ε / 2 := by
        simpa only [dist_eq_norm] using hN n hn
      linarith

/-- The real rooted-tree coefficient family is unconditionally summable at
the critical endpoint, with sum the constant profile one. -/
theorem CompactBJRModel.typeRootedTreeEGF_hasSum_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    HasSum (fun n : ℕ => PowerSeries.coeff n M.typeRootedTreeEGF)
      (1 : C(S, ℝ)) := by
  classical
  have hseq := M.rootedTreePartialSum_tendsto_one hM
  change Filter.Tendsto
    (fun s : Finset ℕ =>
      ∑ n ∈ s, PowerSeries.coeff n M.typeRootedTreeEGF)
    Filter.atTop (nhds (1 : C(S, ℝ)))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hseq) ε hε
  refine ⟨Finset.range N, ?_⟩
  intro s hs
  rw [dist_eq_norm]
  have hnorm :
      ‖(∑ n ∈ s, PowerSeries.coeff n M.typeRootedTreeEGF) - 1‖ ≤
        ‖M.rootedTreePartialSum N 1 - 1‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro x
    have hlow : M.rootedTreePartialSum N 1 x ≤
        (∑ n ∈ s, PowerSeries.coeff n M.typeRootedTreeEGF) x := by
      simpa only [CompactBJRModel.rootedTreePartialSum, one_pow, one_smul,
        ContinuousMap.sum_apply] using
        (Finset.sum_le_sum_of_subset_of_nonneg hs
          (fun n hn hnr => M.typeRootedTreeEGF_coeff_nonneg n x))
    obtain ⟨K, hK⟩ := s.exists_nat_subset_range
    have hsK : (∑ n ∈ s, PowerSeries.coeff n M.typeRootedTreeEGF) x ≤
        M.rootedTreePartialSum K 1 x := by
      simpa only [CompactBJRModel.rootedTreePartialSum, one_pow, one_smul,
        ContinuousMap.sum_apply] using
        (Finset.sum_le_sum_of_subset_of_nonneg hK
          (fun n hn hns => M.typeRootedTreeEGF_coeff_nonneg n x))
    have hupp : (∑ n ∈ s, PowerSeries.coeff n M.typeRootedTreeEGF) x ≤ 1 :=
      hsK.trans (M.rootedTreePartialSum_at_one_le_one K x)
    have hpartial : M.rootedTreePartialSum N 1 x ≤ 1 :=
      hlow.trans hupp
    have hpoint :
        ‖((∑ n ∈ s, PowerSeries.coeff n M.typeRootedTreeEGF) - 1) x‖ ≤
          ‖(M.rootedTreePartialSum N 1 - 1) x‖ := by
      simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply,
        Real.norm_eq_abs]
      rw [abs_of_nonpos (sub_nonpos.mpr hupp),
        abs_of_nonpos (sub_nonpos.mpr hpartial)]
      linarith
    exact hpoint.trans
      ((M.rootedTreePartialSum N 1 - 1).norm_coe_le_norm x)
  exact hnorm.trans_lt (by
    simpa only [dist_eq_norm] using hN N le_rfl)

/-- Complexifying the real endpoint sum gives the genuine complex
multilinear rooted-tree series at `z = 1`. -/
theorem CompactBJRModel.complexTypeRootedTreeFMS_hasSum_at_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    HasSum (fun n : ℕ =>
        M.complexTypeRootedTreeFMS n (fun _ : Fin n => (1 : ℂ)))
      (1 : C(S, ℂ)) := by
  let A := ContinuousMap.realToRCLikeStarAlgHom S ℂ
  have hmapped := (M.typeRootedTreeEGF_hasSum_one hM).map A
    (ContinuousMap.continuous_realToRCLike S ℂ)
  have hterm :
      (fun n : ℕ =>
        M.complexTypeRootedTreeFMS n (fun _ : Fin n => (1 : ℂ))) =
      A ∘ (fun n : ℕ => PowerSeries.coeff n M.typeRootedTreeEGF) := by
    funext n
    calc
      M.complexTypeRootedTreeFMS n (fun _ : Fin n => (1 : ℂ)) =
          TreeRealComplexBridge.complexify
            ((1 : ℝ) ^ n • PowerSeries.coeff n M.typeRootedTreeEGF) := by
        simpa only [Complex.ofReal_one] using
          M.complexTypeRootedTreeFMS_apply_real n 1
      _ = (A ∘ fun k : ℕ =>
          PowerSeries.coeff k M.typeRootedTreeEGF) n := by
        simp only [one_pow, one_smul, Function.comp_apply, A,
          ContinuousMap.realToRCLikeStarAlgHom_apply]
        rfl
  have hone : (1 : C(S, ℂ)) = A (1 : C(S, ℝ)) := by
    simp only [A, ContinuousMap.realToRCLikeStarAlgHom_apply]
    exact TreeRealComplexBridge.complexify_one.symm
  rw [hterm, hone]
  exact hmapped

/-- Consequently the canonical complex rooted-tree sum has the genuine
critical endpoint value one. -/
theorem CompactBJRModel.rootedTreeSeries_one_eq_one
    (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    M.rootedTreeSeries (1 : ℂ) = (1 : C(S, ℂ)) := by
  unfold CompactBJRModel.rootedTreeSeries FormalMultilinearSeries.sum
  exact (M.complexTypeRootedTreeFMS_hasSum_at_one hM).tsum_eq

end PerronWright
