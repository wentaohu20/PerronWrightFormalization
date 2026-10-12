import PerronWright.Enumeration.FieldRootedTreeAnalyticGerm

/-! Exact Taylor-radius invariance under invertible range maps and exact
one-dimensional scalar activity scaling. These are generic analytic facts,
independent of all criticality or primitive hypotheses. -/

open scoped ENNReal
noncomputable section

namespace PerronWright.FiniteIrreducibleSeriesScaling

theorem radius_range_equiv_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (p : FormalMultilinearSeries ℂ ℂ E) (u : E ≃L[ℂ] F) :
    (u.toContinuousLinearMap.compFormalMultilinearSeries p).radius = p.radius := by
  apply le_antisymm
  · have he : u.symm.toContinuousLinearMap.compFormalMultilinearSeries
        (u.toContinuousLinearMap.compFormalMultilinearSeries p) = p := by
      funext n
      apply ContinuousMultilinearMap.ext
      intro x
      simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply',
        ContinuousLinearEquiv.coe_coe, u.symm_apply_apply]
    calc
      (u.toContinuousLinearMap.compFormalMultilinearSeries p).radius ≤
          (u.symm.toContinuousLinearMap.compFormalMultilinearSeries
            (u.toContinuousLinearMap.compFormalMultilinearSeries p)).radius :=
        (u.toContinuousLinearMap.compFormalMultilinearSeries p).radius_le_radius_continuousLinearMap_comp
          u.symm.toContinuousLinearMap
      _ = p.radius := congrArg FormalMultilinearSeries.radius he
  · exact p.radius_le_radius_continuousLinearMap_comp u.toContinuousLinearMap

theorem radius_comp_smul_id_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p : FormalMultilinearSeries ℂ ℂ E) {rho : ℂ} (hrho : rho ≠ 0) :
    (p.compContinuousLinearMap (rho • ContinuousLinearMap.id ℂ ℂ)).radius =
      p.radius / ‖rho‖ₑ := by
  let u : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 rho hrho)
  have hu : u.toContinuousLinearMap = rho • ContinuousLinearMap.id ℂ ℂ := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [u, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    exact mul_comm z rho
  have huinv : u.symm.toContinuousLinearMap = rho⁻¹ • ContinuousLinearMap.id ℂ ℂ := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [u, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    exact mul_comm z rho⁻¹
  have hid : ‖ContinuousLinearMap.id ℂ ℂ‖ₑ = 1 := by
    rw [enorm_eq_nnnorm]
    norm_num
  apply le_antisymm
  · rw [← hu]
    calc
      (p.compContinuousLinearMap u.toContinuousLinearMap).radius ≤
          ‖u.symm.toContinuousLinearMap‖ₑ * p.radius := p.radius_compContinuousLinearMap_le u
      _ = p.radius / ‖rho‖ₑ := by
        rw [huinv, enorm_smul, hid, mul_one, enorm_inv hrho]
        simp only [ENNReal.div_eq_inv_mul]
  · have hlower := p.div_le_radius_compContinuousLinearMap
      (rho • ContinuousLinearMap.id ℂ ℂ)
    rw [enorm_smul, hid, mul_one] at hlower
    exact hlower

end PerronWright.FiniteIrreducibleSeriesScaling
