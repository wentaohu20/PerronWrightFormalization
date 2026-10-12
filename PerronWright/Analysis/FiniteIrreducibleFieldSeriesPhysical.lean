import PerronWright.Analysis.FiniteIrreducibleFieldSeriesNormalization
import PerronWright.Analysis.FiniteIrreduciblePhysicalFold

/-! The genuine labelled field-tree sum equals the actual zero-start least
branch. The constructed small real critical fields have exactly the proved
critical convergence radius, with no primitive/B2 assumption. -/

open Filter Topology
open scoped BigOperators ENNReal
noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem fieldFMS_normalizedTerm (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) {rho : ℝ} (hrho : rho ≠ 0)
    (hfix : M.fieldTreeMap rho g τ = τ) (n : ℕ) (w : ℂ) :
    M.fieldFMS (TreeRealComplexBridge.complexify g) n (fun _ ↦ (rho : ℂ) * w) =
      TreeRealComplexBridge.complexify τ *
        (M.tilted τ hτ).bjrModel.complexTypeRootedTreeFMS n (fun _ ↦ w) := by
  rw [M.fieldFMS_eq_tilted g τ hτ hrho hfix]
  change positiveProfileEquiv τ hτ
    ((M.tilted τ hτ).bjrModel.complexTypeRootedTreeFMS n
      (fun _ ↦ (rho : ℂ)⁻¹ * ((rho : ℂ) * w))) = _
  have ha : (fun _ : Fin n ↦ (rho : ℂ)⁻¹ * ((rho : ℂ) * w)) = fun _ ↦ w := by
    funext i
    rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hrho), one_mul]
  rw [ha]
  exact positiveProfileEquiv_apply τ hτ _

theorem fieldFMS_hasSum_normalized (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) {rho : ℝ} (hrho : rho ≠ 0)
    (hfix : M.fieldTreeMap rho g τ = τ) {w : ℂ}
    (hw : w ∈ Metric.eball 0 (1 : ℝ≥0∞)) :
    HasSum (fun n ↦ M.fieldFMS (TreeRealComplexBridge.complexify g) n
      (fun _ ↦ (rho : ℂ) * w))
      (TreeRealComplexBridge.complexify τ * (M.tilted τ hτ).bjrModel.rootedTreeSeries w) := by
  have hconv : w ∈ Metric.eball 0 (M.tilted τ hτ).bjrModel.complexTypeRootedTreeFMS.radius :=
    Metric.eball_subset_eball (M.tilted τ hτ).bjrModel.one_le_complexTypeRootedTreeFMS_radius hw
  have hs := (positiveProfileEquiv τ hτ).toContinuousLinearMap.hasSum
    ((M.tilted τ hτ).bjrModel.complexTypeRootedTreeFMS_hasSum hconv)
  simpa only [M.fieldFMS_normalizedTerm g τ hτ hrho hfix,
    ContinuousLinearEquiv.coe_coe, Function.comp_apply, positiveProfileEquiv_apply] using hs

theorem fieldFMS_sum_normalized (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) {rho : ℝ} (hrho : rho ≠ 0)
    (hfix : M.fieldTreeMap rho g τ = τ) {w : ℂ}
    (hw : w ∈ Metric.eball 0 (1 : ℝ≥0∞)) :
    (M.fieldFMS (TreeRealComplexBridge.complexify g)).sum ((rho : ℂ) * w) =
      TreeRealComplexBridge.complexify τ * (M.tilted τ hτ).bjrModel.rootedTreeSeries w :=
  (M.fieldFMS_hasSum_normalized g τ hτ hrho hfix hw).tsum_eq

theorem fieldSeries_eq_least_fixedPoint (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) {rho : ℝ} (hrho : rho ≠ 0)
    (hfix : M.fieldTreeMap rho g τ = τ) (w : ℝ) (hw : 0 ≤ w) (hw1 : w < 1) :
    ∃ V : C(S, ℝ), Tendsto (M.fieldTreeIter (rho * w) g) atTop (𝓝 V) ∧
      (∀ a, 0 ≤ V a ∧ V a ≤ τ a) ∧ M.fieldTreeMap (rho * w) g V = V ∧
      (∀ W : C(S, ℝ), (∀ a, 0 ≤ W a) →
        M.fieldTreeMap (rho * w) g W = W → ∀ a, V a ≤ W a) ∧
      (M.fieldFMS (TreeRealComplexBridge.complexify g)).sum ((rho : ℂ) * (w : ℂ)) =
        TreeRealComplexBridge.complexify V := by
  obtain ⟨U, hUlim, -, -, hUseries⟩ :=
    (M.tilted τ hτ).rootedTreeSeries_eq_least_fixedPoint w hw hw1
  obtain ⟨V, hVlim, hVbounds, hVfix, hVleast⟩ :=
    M.fieldTreeIter_least_fixed_of_positive_profile g τ hτ rho hfix w hw hw1.le
  have hc : Continuous (fun f : C(S, ℝ) ↦ τ * f) := continuous_const.mul continuous_id
  have hlim : Tendsto (M.fieldTreeIter (rho * w) g) atTop (𝓝 (τ * U)) := by
    have he : M.fieldTreeIter (rho * w) g =
        fun n ↦ τ * (M.tilted τ hτ).bjrModel.normalizedZeroTreeIter w n :=
      funext (M.fieldTreeIter_conjugacy g τ hτ rho hfix w)
    rw [he]
    exact (hc.tendsto U).comp hUlim
  have hVU : V = τ * U := tendsto_nhds_unique hVlim hlim
  have hwball : (w : ℂ) ∈ Metric.eball 0 (1 : ℝ≥0∞) := by
    rw [← ENNReal.coe_one, Metric.eball_coe]
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hw, NNReal.coe_one] using hw1
  refine ⟨V, hVlim, hVbounds, hVfix, hVleast, ?_⟩
  rw [M.fieldFMS_sum_normalized g τ hτ hrho hfix hwball, hUseries, hVU]
  ext a
  simp only [TreeRealComplexBridge.complexify_apply, ContinuousMap.mul_apply, Complex.ofReal_mul]

theorem fieldTreeIter_limit_near_critical_profile (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) (rho : ℝ)
    (hfix : M.fieldTreeMap rho g τ = τ) (hcritical : (M.tilted τ hτ).IsCritical)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℝ, 0 ≤ w → w < 1 → |w - 1| < δ →
      ∃ V : C(S, ℝ), Tendsto (M.fieldTreeIter (rho * w) g) atTop (𝓝 V) ∧
        M.fieldTreeMap (rho * w) g V = V ∧ ‖V - τ‖ < eta := by
  let etaN := eta / (‖τ‖ + 1)
  have hetaN : 0 < etaN := div_pos heta (by positivity)
  obtain ⟨δ, hδ, hnear⟩ :=
    (M.tilted τ hτ).normalizedZeroTreeIter_limit_near_one hcritical etaN hetaN
  refine ⟨δ, hδ, ?_⟩
  intro w hw hw1 hclose
  obtain ⟨U, hUlim, hUfix, hUnorm⟩ := hnear w hw hw1 hclose
  have hc : Continuous (fun f : C(S, ℝ) ↦ τ * f) := continuous_const.mul continuous_id
  refine ⟨τ * U, ?_, ?_, ?_⟩
  · have he : M.fieldTreeIter (rho * w) g =
        fun n ↦ τ * (M.tilted τ hτ).bjrModel.normalizedZeroTreeIter w n :=
      funext (M.fieldTreeIter_conjugacy g τ hτ rho hfix w)
    rw [he]
    exact (hc.tendsto U).comp hUlim
  · rw [M.fieldTreeMap_conjugacy g τ hτ rho hfix, hUfix]
  · have he : τ * U - τ = τ * (U - 1) := by rw [mul_sub, mul_one]
    rw [he]
    apply (norm_mul_le τ (U - 1)).trans_lt
    have hsmall : (‖τ‖ + 1) * ‖U - 1‖ < eta := by
      have hh := (lt_div_iff₀ (by positivity : 0 < ‖τ‖ + 1)).mp hUnorm
      rwa [mul_comm] at hh
    nlinarith [norm_nonneg (U - 1)]

/-- The genuine labelled series radius is the constructed critical activity
for every sufficiently small real field, including nonzero fields. -/
theorem fieldFMS_radius_eq_critical_radius_real_eventually
    (M : FiniteIrreducibleModel S) (hcrit : M.IsCritical) :
    ∀ᶠ g : C(S, ℂ) in 𝓝 0, star g = g →
      (M.fieldFMS g).radius = ‖FiniteIrreducibleRadiusResponse.radius M hcrit g‖ₑ := by
  filter_upwards [M.real_critical_tilt_eventually hcrit] with g hg
  intro hreal
  obtain ⟨hτ, hρpos, hρim, -, hfix, hcritical⟩ := hg hreal
  have he := M.fieldFMS_radius_eq_of_critical_profile (realPartMap g)
    (realCriticalProfile M hcrit g) hτ hρpos.ne' hfix hcritical
  rw [complexify_realPartMap_of_star g hreal] at he
  have hρc : ((FiniteIrreducibleRadiusResponse.radius M hcrit g).re : ℂ) =
      FiniteIrreducibleRadiusResponse.radius M hcrit g := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using hρim.symm
  exact he.trans (congrArg enorm hρc)

end PerronWright.FiniteIrreducibleModel
