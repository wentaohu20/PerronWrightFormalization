import PerronWright.Probability.FiniteIrreducibleConnectedTypeLaw
import PerronWright.Analysis.FiniteIrreducibleRadiusTaylor
import PerronWright.Analysis.FiniteIrreducibleFieldSeriesPhysical

/-! # Actual finite Perron-centered real-field physical log-radius estimates

The actual critical pair, its exact weighted Perron derivative and its
proved physical rooted-tree series radius are used. No primitivity/B2
assumption or radius identification interface is supplied.
-/

open MeasureTheory Filter Topology
open scoped Classical Topology

noncomputable section
set_option maxHeartbeats 800000
namespace PerronWright.FiniteIrreducibleProfileRadius

open FiniteIrreducibleConnectedTypeLaw FiniteIrreducibleRadiusTaylor
open FieldLogRadiusTaylor (norm_complexifyField complexifyField_star complexifyField_add)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

theorem weightedFunctional_complexifyField (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (f : C(S, ℝ)) :
    M.weightedFunctional hM (CompactBJRModel.complexifyField f) =
      ((∫ a, f a ∂(perronLaw M hM : Measure S) : ℝ) : ℂ) := by
  rw [M.weightedFunctional_apply, integral_perronLaw]
  simp only [CompactBJRModel.complexifyField_apply, Complex.ofReal_sum, Complex.ofReal_mul]

/-- The positive real slice of the same critical-radius germ. -/
def realRadius (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (g : C(S, ℝ)) : ℝ :=
  (FiniteIrreducibleRadiusResponse.radius M hM (CompactBJRModel.complexifyField g)).re

/-- The real logarithm of the actual positive critical radius. -/
def realLogRadius (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (g : C(S, ℝ)) : ℝ := Real.log (realRadius M hM g)

theorem exists_realRadius_positive_branch (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : C(S, ℝ), ‖g‖ < ε →
      0 < realRadius M hM g ∧
      FiniteIrreducibleRadiusResponse.radius M hM (CompactBJRModel.complexifyField g) =
        (realRadius M hM g : ℂ) ∧
      logRadius M hM (CompactBJRModel.complexifyField g) =
        (realLogRadius M hM g : ℂ) := by
  obtain ⟨ε, hε, hreal⟩ := FiniteIrreducibleCriticalPair.criticalPair_real_positive_radius M hM
  refine ⟨ε, hε, ?_⟩
  intro g hg
  have hr := hreal (CompactBJRModel.complexifyField g)
    (by simpa only [norm_complexifyField] using hg) (complexifyField_star g)
  have him : (FiniteIrreducibleRadiusResponse.radius M hM (CompactBJRModel.complexifyField g)).im = 0 :=
    hr.1
  have hpos : 0 < realRadius M hM g := hr.2.1
  have heq : FiniteIrreducibleRadiusResponse.radius M hM (CompactBJRModel.complexifyField g) =
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
theorem exists_realLogRadius_increment_bound (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ g f : C(S, ℝ),
      ‖g‖ + ‖f‖ < ε →
      |realLogRadius M hM (g + f) - realLogRadius M hM g +
          ∫ x, f x ∂(perronLaw M hM : Measure S)| ≤
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
    (hreal g hg).2.2, weightedFunctional_complexifyField] at hb
  simpa only [← Complex.ofReal_sub, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs, norm_complexifyField] using hb


/-- The real radius is the convergence radius of the literal labelled
rooted-tree formal series on one actual real field ball. -/
theorem exists_physical_real_field_radius (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : C(S, ℝ), ‖g‖ < ε →
      0 < realRadius M hM g ∧
      (M.fieldFMS (CompactBJRModel.complexifyField g)).radius =
        ENNReal.ofReal (realRadius M hM g) := by
  obtain ⟨ε₁, hε₁, hreal⟩ := exists_realRadius_positive_branch M hM
  obtain ⟨ε₂, hε₂, hball⟩ := Metric.eventually_nhds_iff.mp
    (M.fieldFMS_radius_eq_critical_radius_real_eventually hM)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro g hg
  have hg₁ := hg.trans_le (min_le_left ε₁ ε₂)
  have hr := hreal g hg₁
  refine ⟨hr.1, ?_⟩
  have hc := hball (y := CompactBJRModel.complexifyField g)
    (by simpa only [dist_zero_right, norm_complexifyField] using
      hg.trans_le (min_le_right ε₁ ε₂)) (complexifyField_star g)
  rw [hc, hr.2.1, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]

end PerronWright.FiniteIrreducibleProfileRadius

