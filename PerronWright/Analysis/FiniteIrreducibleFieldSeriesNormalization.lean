import PerronWright.Analysis.FiniteIrreducibleFieldCriticalTilt
import PerronWright.Analysis.FiniteIrreducibleSeriesScaling
import PerronWright.Analysis.FiniteIrreducibleTreeSeries

/-!
# Exact normalization of the genuine labelled field-tree series

The field series is the existing finite labelled-graph integral series,
not a recursively defined replacement. Its Taylor series is identified
with the actual tilted zero-field series by the proved formal uniqueness
theorem. This gives an exact radius and a genuine least-branch identity.
-/

open Filter Topology
open scoped BigOperators ENNReal
noncomputable section

namespace PerronWright.FiniteIrreducibleModel

variable {S : Type*} [Fintype S] [DecidableEq S]
  [MetricSpace S] [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def positiveProfileUnit (τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) : C(S, ℂ)ˣ where
  val := TreeRealComplexBridge.complexify τ
  inv := ⟨fun a ↦ (τ a : ℂ)⁻¹, continuous_of_discreteTopology⟩
  val_inv := by
    ext a
    exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hτ a).ne')
  inv_val := by
    ext a
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hτ a).ne')

def positiveProfileEquiv (τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) :
    C(S, ℂ) ≃L[ℂ] C(S, ℂ) :=
  { toLinearEquiv :=
      { toFun := fun f ↦ TreeRealComplexBridge.complexify τ * f
        invFun := fun f ↦ (positiveProfileUnit τ hτ)⁻¹.val * f
        left_inv := by
          intro f
          ext a
          change (τ a : ℂ)⁻¹ * ((τ a : ℂ) * f a) = f a
          rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hτ a).ne'), one_mul]
        right_inv := by
          intro f
          ext a
          change (τ a : ℂ) * ((τ a : ℂ)⁻¹ * f a) = f a
          rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hτ a).ne'), one_mul]
        map_add' := fun f h ↦ mul_add _ _ _
        map_smul' := by intros; simp only [mul_smul_comm, RingHom.id_apply] }
    continuous_toFun := continuous_const.mul continuous_id
    continuous_invFun := continuous_const.mul continuous_id }

omit [DecidableEq S] [MeasurableSpace S] [BorelSpace S] in
theorem positiveProfileEquiv_apply (τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) (f : C(S, ℂ)) :
    positiveProfileEquiv τ hτ f = TreeRealComplexBridge.complexify τ * f := by
  rfl

def fieldFMS (M : FiniteIrreducibleModel S) (g : C(S, ℂ)) :
    FormalMultilinearSeries ℂ ℂ C(S, ℂ) :=
  oneDimensionalFormalMultilinearSeries (FieldRootedTree.series M.bjrModel g)

theorem treeResidual_positive_profile_conjugacy (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) (rho : ℝ)
    (hfix : M.fieldTreeMap rho g τ = τ) (w : ℂ) (V : C(S, ℂ)) :
    M.treeResidual (((rho : ℂ) * w, TreeRealComplexBridge.complexify g),
      TreeRealComplexBridge.complexify τ * V) =
        TreeRealComplexBridge.complexify τ *
          (M.tilted τ hτ).treeResidual ((w, 0), V) := by
  let T := TreeRealComplexBridge.complexify τ
  let N := M.tilted τ hτ
  let A := TreeRealComplexBridge.complexify g - TreeCritical.degree M.bjrModel + M.complexOperator T
  let B := -TreeCritical.degree N.bjrModel + N.complexOperator V
  have hT : T = (rho : ℂ) • NormedSpace.exp A := by
    have he := congrArg TreeRealComplexBridge.complexify hfix
    rw [M.complexify_fieldTreeMap] at he
    exact he.symm
  have harg : TreeRealComplexBridge.complexify g - TreeCritical.degree M.bjrModel +
      M.complexOperator (T * V) = A + B := by
    change _ = A + (-N.complexOperator 1 + N.complexOperator V)
    rw [M.tilted_complexOperator τ hτ 1, M.tilted_complexOperator τ hτ V, mul_one]
    change _ = (TreeRealComplexBridge.complexify g - TreeCritical.degree M.bjrModel +
      M.complexOperator T) + (-M.complexOperator T + M.complexOperator (T * V))
    abel
  simp only [treeResidual, TreeCritical.residual, TreeAnalytic.residual, zero_sub]
  change T * V - ((rho : ℂ) * w) • NormedSpace.exp
      (TreeRealComplexBridge.complexify g - TreeCritical.degree M.bjrModel +
        M.complexOperator (T * V)) = T * (V - w • NormedSpace.exp B)
  rw [harg, NormedSpace.exp_add]
  calc
    _ = T * V - T * (w • NormedSpace.exp B) := by
      rw [hT]
      ext a
      simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply,
        ContinuousMap.smul_apply, smul_eq_mul]
      ring
    _ = _ := (mul_sub _ _ _).symm

/-- The actual labelled field-tree Taylor series is exactly the rescaled
and profile-multiplied actual zero-field Taylor series of the tilted law. -/
theorem fieldFMS_eq_tilted (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) {rho : ℝ} (hrho : rho ≠ 0)
    (hfix : M.fieldTreeMap rho g τ = τ) :
    M.fieldFMS (TreeRealComplexBridge.complexify g) =
      (positiveProfileEquiv τ hτ).toContinuousLinearMap.compFormalMultilinearSeries
        ((M.tilted τ hτ).bjrModel.complexTypeRootedTreeFMS.compContinuousLinearMap
          ((rho : ℂ)⁻¹ • ContinuousLinearMap.id ℂ ℂ)) := by
  let N := M.tilted τ hτ
  let R : ℂ →L[ℂ] ℂ := (rho : ℂ)⁻¹ • ContinuousLinearMap.id ℂ ℂ
  let L := (positiveProfileEquiv τ hτ).toContinuousLinearMap
  let phi : ℂ → C(S, ℂ) := fun z ↦ L (N.bjrModel.rootedTreeSeries (R z))
  let p := L.compFormalMultilinearSeries (N.bjrModel.complexTypeRootedTreeFMS.compContinuousLinearMap R)
  have hrad : 0 < N.bjrModel.complexTypeRootedTreeFMS.radius :=
    zero_lt_one.trans_le N.bjrModel.one_le_complexTypeRootedTreeFMS_radius
  have hN0 : (0 : ℂ) ∈ Metric.eball 0 N.bjrModel.complexTypeRootedTreeFMS.radius := by
    simpa only [Metric.mem_eball, edist_self] using hrad
  have hpN : HasFPowerSeriesAt N.bjrModel.rootedTreeSeries
      N.bjrModel.complexTypeRootedTreeFMS (R 0) := by
    rw [map_zero]
    exact ⟨_, N.bjrModel.complexTypeRootedTreeFMS.hasFPowerSeriesOnBall hrad⟩
  have hpR : HasFPowerSeriesAt (fun z ↦ N.bjrModel.rootedTreeSeries (R z))
      (N.bjrModel.complexTypeRootedTreeFMS.compContinuousLinearMap R) 0 :=
    hpN.compContinuousLinearMap
  have hp : HasFPowerSeriesAt phi p 0 := by
    obtain ⟨r, hr⟩ := hpR
    exact ⟨r, L.comp_hasFPowerSeriesOnBall hr⟩
  have hphi0 : phi 0 = 0 := by
    have hNz := N.bjrModel.rootedTreeSeries_residual_zero hN0
    change N.bjrModel.rootedTreeSeries 0 - (0 : ℂ) • _ = 0 at hNz
    simp only [zero_smul, sub_zero] at hNz
    simp only [phi, map_zero, hNz]
  have hres : ∀ᶠ z : ℂ in 𝓝 0,
      M.treeResidual ((z, TreeRealComplexBridge.complexify g), phi z) = 0 := by
    have ht : Tendsto R (𝓝 0) (𝓝 0) := by simpa only [map_zero] using R.continuous.tendsto 0
    filter_upwards [ht.eventually (Metric.isOpen_eball.mem_nhds hN0)] with z hz
    have he := M.treeResidual_positive_profile_conjugacy g τ hτ rho hfix (R z)
      (N.bjrModel.rootedTreeSeries (R z))
    have hactivity : (rho : ℂ) * R z = z := by
      change (rho : ℂ) * ((rho : ℂ)⁻¹ * z) = z
      rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hrho), one_mul]
    rw [hactivity] at he
    change M.treeResidual ((z, TreeRealComplexBridge.complexify g),
      TreeRealComplexBridge.complexify τ * N.bjrModel.rootedTreeSeries (R z)) = _ at he
    rw [show N.treeResidual ((R z, 0), N.bjrModel.rootedTreeSeries (R z)) = 0 from
      N.bjrModel.rootedTreeSeries_residual_zero hz, mul_zero] at he
    simpa only [phi, L, ContinuousLinearEquiv.coe_coe, positiveProfileEquiv_apply] using he
  let psi : ℂ × C(S, ℂ) → C(S, ℂ) := fun q ↦ phi q.1
  have hpsi : AnalyticAt ℂ psi (0, TreeRealComplexBridge.complexify g) :=
    hp.analyticAt.comp_of_eq analyticAt_fst rfl
  obtain ⟨p', hp', -, hactual⟩ := FieldRootedTree.branch_taylorSeries_eq_series M.bjrModel
    (TreeRealComplexBridge.complexify g) psi hpsi hphi0 hres
  have heq : p' = p := hp'.eq_formalMultilinearSeries hp
  change oneDimensionalFormalMultilinearSeries
    (FieldRootedTree.series M.bjrModel (TreeRealComplexBridge.complexify g)) = p
  rw [← hactual, oneDimensionalFormalMultilinearSeries_oneDimensionalPowerSeries, heq]

theorem fieldFMS_radius_eq_of_critical_profile (M : FiniteIrreducibleModel S)
    (g τ : C(S, ℝ)) (hτ : ∀ a, 0 < τ a) {rho : ℝ} (hrho : rho ≠ 0)
    (hfix : M.fieldTreeMap rho g τ = τ) (hcritical : (M.tilted τ hτ).IsCritical) :
    (M.fieldFMS (TreeRealComplexBridge.complexify g)).radius = ‖(rho : ℂ)‖ₑ := by
  rw [M.fieldFMS_eq_tilted g τ hτ hrho hfix,
    FiniteIrreducibleSeriesScaling.radius_range_equiv_eq,
    FiniteIrreducibleSeriesScaling.radius_comp_smul_id_eq _
      (inv_ne_zero (Complex.ofReal_ne_zero.mpr hrho)),
    (M.tilted τ hτ).complexTypeRootedTreeFMS_radius_eq_one hcritical,
    enorm_inv (Complex.ofReal_ne_zero.mpr hrho)]
  simp only [ENNReal.div_eq_inv_mul, mul_one, inv_inv]

end PerronWright.FiniteIrreducibleModel
