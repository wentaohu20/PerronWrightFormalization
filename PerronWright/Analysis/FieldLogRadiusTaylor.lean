import PerronWright.Analysis.RadiusResponse
import PerronWright.Enumeration.FieldAnalytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform Banach-field Taylor estimates for the actual log-radius

The radius here is the analytic critical pair, not a surrogate radius.
Its derivative is the negative Perron integral. Analyticity of its
Fréchet derivative and the mean value inequality give a two-field
increment estimate which vanishes when the test field vanishes.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped Topology

noncomputable section

namespace PerronWright.FieldLogRadiusTaylor

section BanachTaylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A local analytic germ has a uniform second-order two-field increment
bound. No compactness of the Banach field ball is required. -/
theorem analytic_increment_bound {F : E → ℂ} (hF : AnalyticAt ℂ F 0) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ g f : E,
      ‖g‖ + ‖f‖ < ε →
      ‖F (g + f) - F g - (fderiv ℂ F 0) f‖ ≤
        C * (‖f‖ ^ 2 + ‖g‖ * ‖f‖) := by
  have hO : (fun z : E ↦ fderiv ℂ F z - fderiv ℂ F 0) =O[𝓝 0]
      (fun z : E ↦ z) := by
    simpa only [sub_zero] using hF.fderiv.differentiableAt.isBigO_sub
  obtain ⟨C₀, hC₀⟩ := isBigO_iff.mp hO
  let C : ℝ := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right C₀ 1)
  have hlocal : ∀ᶠ z : E in 𝓝 0,
      DifferentiableAt ℂ F z ∧
        ‖fderiv ℂ F z - fderiv ℂ F 0‖ ≤ C * ‖z‖ := by
    filter_upwards [hF.eventually_analyticAt, hC₀] with z hz hbound
    exact ⟨hz.differentiableAt, hbound.trans
      (mul_le_mul_of_nonneg_right (le_max_left C₀ 1) (norm_nonneg z))⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
  refine ⟨ε, C, hε, hC, ?_⟩
  intro g f hgf
  let s : Set E := Metric.closedBall 0 (‖g‖ + ‖f‖)
  have hs : Convex ℝ s := convex_closedBall _ _
  have hz (z : E) (hzin : z ∈ s) : ‖z‖ ≤ ‖g‖ + ‖f‖ := by
    simpa only [s, Metric.mem_closedBall, dist_zero_right] using hzin
  have hd (z : E) (hzin : z ∈ s) : DifferentiableAt ℂ F z :=
    (hball (by simpa only [dist_zero_right] using (hz z hzin).trans_lt hgf)).1
  have hb (z : E) (hzin : z ∈ s) :
      ‖fderiv ℂ F z - fderiv ℂ F 0‖ ≤ C * (‖g‖ + ‖f‖) := by
    exact (hball (by simpa only [dist_zero_right] using
      (hz z hzin).trans_lt hgf)).2.trans
        (mul_le_mul_of_nonneg_left (hz z hzin) hC.le)
  have hg : g ∈ s := by
    simp only [s, Metric.mem_closedBall, dist_zero_right]
    linarith [norm_nonneg f]
  have hsum : g + f ∈ s := by
    simpa only [s, Metric.mem_closedBall, dist_zero_right] using norm_add_le g f
  have h := hs.norm_image_sub_le_of_norm_fderiv_le' hd hb hg hsum
  simp only [add_sub_cancel_left] at h
  exact h.trans_eq
    (show C * (‖g‖ + ‖f‖) * ‖f‖ =
      C * (‖f‖ ^ 2 + ‖g‖ * ‖f‖) by ring)

end BanachTaylor

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The principal logarithm of the actual analytic critical radius. -/
def logRadius (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (g : C(S, ℂ)) : ℂ := Complex.log (RadiusResponse.radius M hM g)

theorem logRadius_analytic (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    AnalyticAt ℂ (logRadius M hM) 0 := by
  have hlog : AnalyticAt ℂ Complex.log (RadiusResponse.radius M hM 0) := by
    simpa only [RadiusResponse.radius_base] using
      analyticAt_clog Complex.one_mem_slitPlane
  exact hlog.comp (RadiusResponse.radius_analytic M hM)

@[simp] theorem logRadius_zero (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) : logRadius M hM 0 = 0 := by
  simp [logRadius, RadiusResponse.radius_base]

/-- The exact Banach derivative of the actual log-radius is minus the
Perron-weighted integral, in every continuous field direction. -/
theorem logRadius_fderiv (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (f : C(S, ℂ)) :
    (fderiv ℂ (logRadius M hM) 0) f = -M.weightedIntegralComplex hM f := by
  have hlog : HasDerivAt Complex.log
      (RadiusResponse.radius M hM 0)⁻¹ (RadiusResponse.radius M hM 0) := by
    simpa only [RadiusResponse.radius_base] using
      Complex.hasDerivAt_log Complex.one_mem_slitPlane
  have hd := hlog.comp_hasFDerivAt 0
    (RadiusResponse.radius_analytic M hM).differentiableAt.hasFDerivAt
  have he := congrArg (fun A : C(S, ℂ) →L[ℂ] ℂ ↦ A f) hd.fderiv
  change (fderiv ℂ (logRadius M hM) 0) f = _ at he
  simpa only [smul_apply, smul_eq_mul,
    RadiusResponse.radius_base, inv_one, one_mul,
    RadiusResponse.radius_fderiv_integral] using he

/-- Uniform source-radius Taylor control for two arbitrary small Banach
fields. This is the analytic radius contribution in the centered Laplace
bound, including the mixed `‖g‖ ‖f‖` term. -/
theorem exists_logRadius_increment_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ g f : C(S, ℂ),
      ‖g‖ + ‖f‖ < ε →
      ‖logRadius M hM (g + f) - logRadius M hM g +
          M.weightedIntegralComplex hM f‖ ≤
        C * (‖f‖ ^ 2 + ‖g‖ * ‖f‖) := by
  obtain ⟨ε, C, hε, hC, hbound⟩ := analytic_increment_bound
    (logRadius_analytic M hM)
  refine ⟨ε, C, hε, hC, ?_⟩
  intro g f hgf
  simpa only [logRadius_fderiv, sub_neg_eq_add] using hbound g f hgf

omit [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem norm_complexifyField (f : C(S, ℝ)) :
    ‖CompactBJRModel.complexifyField f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro x
    simpa only [CompactBJRModel.complexifyField_apply, Complex.norm_real] using
      f.norm_coe_le_norm x
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro x
    simpa only [CompactBJRModel.complexifyField_apply, Complex.norm_real] using
      (CompactBJRModel.complexifyField f).norm_coe_le_norm x

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem complexifyField_add (g f : C(S, ℝ)) :
    CompactBJRModel.complexifyField (g + f) =
      CompactBJRModel.complexifyField g + CompactBJRModel.complexifyField f := by
  ext x
  simp

omit [CompactSpace S] [MeasurableSpace S] [BorelSpace S] in
@[simp] theorem complexifyField_star (f : C(S, ℝ)) :
    star (CompactBJRModel.complexifyField f) = CompactBJRModel.complexifyField f := by
  ext x
  simp

theorem weightedIntegralComplex_complexifyField (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (f : C(S, ℝ)) :
    M.weightedIntegralComplex hM (CompactBJRModel.complexifyField f) =
      ((∫ x, f x ∂M.perronLaw hM : ℝ) : ℂ) := by
  rw [M.perronLaw_integral hM]
  unfold CompactBJRModel.weightedIntegralComplex
  simp_rw [CompactBJRModel.complexifyField_apply, ← Complex.ofReal_mul]
  exact integral_complex_ofReal

/-- The positive real slice of the same critical-radius germ. -/
def realRadius (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (g : C(S, ℝ)) : ℝ :=
  (RadiusResponse.radius M hM (CompactBJRModel.complexifyField g)).re

/-- The real logarithm of the actual positive critical radius. -/
def realLogRadius (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (g : C(S, ℝ)) : ℝ := Real.log (realRadius M hM g)

theorem exists_realRadius_positive_branch (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : C(S, ℝ), ‖g‖ < ε →
      0 < realRadius M hM g ∧
      RadiusResponse.radius M hM (CompactBJRModel.complexifyField g) =
        (realRadius M hM g : ℂ) ∧
      logRadius M hM (CompactBJRModel.complexifyField g) =
        (realLogRadius M hM g : ℂ) := by
  obtain ⟨ε, hε, hreal⟩ := CriticalPair.criticalPair_real_positive_radius M hM
  refine ⟨ε, hε, ?_⟩
  intro g hg
  have hr := hreal (CompactBJRModel.complexifyField g)
    (by simpa only [norm_complexifyField] using hg) (complexifyField_star g)
  have him : (RadiusResponse.radius M hM (CompactBJRModel.complexifyField g)).im = 0 :=
    hr.1
  have hpos : 0 < realRadius M hM g := hr.2.1
  have heq : RadiusResponse.radius M hM (CompactBJRModel.complexifyField g) =
      (realRadius M hM g : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him
  refine ⟨hpos, heq, ?_⟩
  unfold logRadius realLogRadius
  rw [heq]
  exact (Complex.ofReal_log hpos.le).symm

/-- The source-radius Taylor bound of Section 5, for actual real fields,
with the center equal to integration against the canonical Perron law. -/
theorem exists_realLogRadius_increment_bound (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ g f : C(S, ℝ),
      ‖g‖ + ‖f‖ < ε →
      |realLogRadius M hM (g + f) - realLogRadius M hM g +
          ∫ x, f x ∂M.perronLaw hM| ≤
        C * (‖f‖ ^ 2 + ‖g‖ * ‖f‖) := by
  obtain ⟨ε₁, C, hε₁, hC, hbound⟩ := exists_logRadius_increment_bound M hM
  obtain ⟨ε₂, hε₂, hreal⟩ := exists_realRadius_positive_branch M hM
  refine ⟨min ε₁ ε₂, C, lt_min hε₁ hε₂, hC, ?_⟩
  intro g f hgf
  have hsum : ‖g + f‖ < ε₂ :=
    (norm_add_le g f).trans_lt (hgf.trans_le (min_le_right _ _))
  have hg : ‖g‖ < ε₂ := by
    have h := hgf.trans_le (min_le_right ε₁ ε₂)
    linarith [norm_nonneg f]
  have hb := hbound (CompactBJRModel.complexifyField g)
    (CompactBJRModel.complexifyField f)
    (by simpa only [norm_complexifyField] using hgf.trans_le (min_le_left _ _))
  rw [← complexifyField_add, (hreal (g + f) hsum).2.2,
    (hreal g hg).2.2, weightedIntegralComplex_complexifyField] at hb
  simpa only [← Complex.ofReal_sub, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs, norm_complexifyField] using hb

end PerronWright.FieldLogRadiusTaylor
