import PerronWright.Analysis.FiniteIrreducibleCriticalWindowRadiusConversion
import PerronWright.Analysis.FiniteIrreducibleFieldComplexRadius

/-!
# The actual finite scalar radius and its quantitative physical expansion

The radius is not merely a component of an implicit critical pair: its
positive real value is proved equal to the convergence radius of the
actual labelled rooted-tree series at the paper's scalar field.
-/

open Filter Topology
open scoped Topology ENNReal

noncomputable section

namespace PerronWright.FiniteIrreduciblePhysicalScalarRadius

open FiniteIrreducibleScalarFieldResponse FiniteIrreducibleCriticalWindowRadiusConversion

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S] [DiscreteTopology S]
  [MeasurableSpace S] [BorelSpace S]

@[simp] theorem realScalarRadius_one (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    realScalarRadius M hM 1 = 1 := by
  simp [realScalarRadius]

theorem realScalarRadius_analytic (M : FiniteIrreducibleModel S) (hM : M.IsCritical) :
    AnalyticAt ℝ (realScalarRadius M hM) 1 := by
  have hR : AnalyticAt ℝ (scalarRadius M hM) ((1 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_one] using (scalarRadius_analytic M hM).restrictScalars
  have hcomp := hR.comp (Complex.ofRealCLM.analyticAt 1)
  exact (Complex.reCLM.analyticAt _).comp hcomp

theorem scalarRadius_eq_ofReal_eventually (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ t : ℝ in 𝓝 1,
      scalarRadius M hM (t : ℂ) = (realScalarRadius M hM t : ℂ) := by
  filter_upwards [scalarRadius_real_positive_near_one M hM] with t ht
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using ht.1

/-- Identification with the genuine rooted-tree convergence radius, on
the positive physical slice. -/
theorem fieldFMS_radius_eq_physical_scalar_radius (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∀ᶠ t : ℝ in 𝓝 1,
      (M.fieldFMS (scalarField M (t : ℂ))).radius =
        ENNReal.ofReal (realScalarRadius M hM t) := by
  obtain ⟨ε, hε, hradius⟩ := M.fieldFMS_radius_eq_critical_radius_complex_eventually hM
  have hc : ContinuousAt (fun t : ℝ ↦ scalarField M (t : ℂ)) 1 := by
    have hc' : ContinuousAt (scalarField M) ((1 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_one] using (scalarField_analytic M).continuousAt
    exact hc'.comp Complex.continuous_ofReal.continuousAt
  have ht : Tendsto (fun t : ℝ ↦ scalarField M (t : ℂ)) (𝓝 1) (𝓝 (0 : C(S, ℂ))) := by
    simpa only [Complex.ofReal_one, scalarField_one] using hc.tendsto
  have he := ht.eventually (Metric.ball_mem_nhds (0 : C(S, ℂ)) hε)
  filter_upwards [he, scalarRadius_eq_ofReal_eventually M hM,
    realScalarRadius_pos_eventually M hM] with t hg hreal hpos
  rw [hradius _ hg]
  change ‖scalarRadius M hM (t : ℂ)‖ₑ = _
  rw [hreal, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

/-- One actual parameter neighborhood supplies analyticity, positivity,
the literal series-radius identity, and the quantitative cubic remainder. -/
theorem exists_physical_scalar_radius_and_cubic_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ t : ℝ, |t - 1| < δ →
      0 < t ∧ 0 < realScalarRadius M hM t ∧
      (M.fieldFMS (scalarField M (t : ℂ))).radius =
        ENNReal.ofReal (realScalarRadius M hM t) ∧
      |Real.log (realScalarRadius M hM t) -
        criticalQuadraticRate M hM * (t - 1) ^ 2| ≤ C * |t - 1| ^ 3 := by
  obtain ⟨δ₁, C, hδ₁, hC, hbound⟩ := exists_real_logScalarRadius_cubic_bound M hM
  have he := (fieldFMS_radius_eq_physical_scalar_radius M hM).and
    (isOpen_Ioi.mem_nhds (by norm_num : (1 : ℝ) ∈ Set.Ioi 0))
  obtain ⟨δ₂, hδ₂, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min δ₁ δ₂, C, lt_min hδ₁ hδ₂, hC, ?_⟩
  intro t ht
  have hb := hbound t (lt_of_lt_of_le ht (min_le_left _ _))
  have he' := hball (show t ∈ Metric.ball (1 : ℝ) δ₂ by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      lt_of_lt_of_le ht (min_le_right δ₁ δ₂))
  exact ⟨he'.2, hb.1, he'.1, hb.2⟩

end PerronWright.FiniteIrreduciblePhysicalScalarRadius
