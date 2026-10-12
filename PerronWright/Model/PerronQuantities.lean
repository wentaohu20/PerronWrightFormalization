import PerronWright.Analysis.Positive

/-!
# Canonical Perron quantities for the compact model

The eigenfunction is selected from the proved existence-and-uniqueness
theorem.  In particular, this module adds no new assumption to the model.
-/

open MeasureTheory

noncomputable section

namespace PerronWright
namespace CompactBJRModel

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- The uniquely normalized positive eigenfunction of a regular critical
compact BJR model. -/
def perronFunction (M : CompactBJRModel S) (hM : M.IsRegularCritical) : C(S, ℝ) :=
  Classical.choose (existsUnique_normalized_positive_fixed M hM)

theorem perronFunction_pos (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (x : S) : 0 < M.perronFunction hM x :=
  (Classical.choose_spec (existsUnique_normalized_positive_fixed M hM)).1.1 x

theorem perronFunction_fixed (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    M.kernel.action M.mu (M.perronFunction hM) = M.perronFunction hM :=
  (Classical.choose_spec (existsUnique_normalized_positive_fixed M hM)).1.2.1

theorem perronFunction_integral (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    (∫ x, M.perronFunction hM x ∂M.mu) = 1 :=
  (Classical.choose_spec (existsUnique_normalized_positive_fixed M hM)).1.2.2

/-- Compactness upgrades pointwise positivity to a uniform positive lower
bound, as required by the analytic fold estimates later in the paper. -/
theorem perronFunction_uniform_pos (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c ≤ M.perronFunction hM x := by
  obtain ⟨c, hc, hle⟩ := isCompact_univ.exists_forall_le'
    (M.perronFunction hM).continuous.continuousOn
    (fun x _ => M.perronFunction_pos hM x)
  exact ⟨c, hc, fun x => hle x (Set.mem_univ x)⟩

/-- The nonnegative density of the Perron law with respect to the type law. -/
def perronDensity (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (x : S) : NNReal :=
  ⟨M.perronFunction hM x, (M.perronFunction_pos hM x).le⟩

theorem perronDensity_continuous (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) : Continuous (M.perronDensity hM) :=
  (M.perronFunction hM).continuous.subtype_mk _

/-- The Perron law `u(x) μ(dx)` from the paper. -/
def perronLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical) : Measure S :=
  M.mu.withDensity (fun x => (M.perronDensity hM x : ENNReal))

instance perronLaw_isProbability (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) : IsProbabilityMeasure (M.perronLaw hM) := by
  constructor
  rw [perronLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint0 : Integrable (M.perronFunction hM) M.mu :=
    (M.perronFunction hM).continuous.integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  have heq : (fun x => (M.perronDensity hM x : ℝ)) =
      (M.perronFunction hM : S → ℝ) := by
    funext x
    rfl
  have hint : Integrable (fun x => (M.perronDensity hM x : ℝ)) M.mu := by
    rw [heq]
    exact hint0
  rw [lintegral_coe_eq_integral _ hint]
  change ENNReal.ofReal (∫ x, M.perronFunction hM x ∂M.mu) = 1
  rw [M.perronFunction_integral hM]
  norm_num

/-- Integration against the Perron law is integration against the positive
Perron density with respect to the original type law. -/
theorem perronLaw_integral (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (f : C(S, ℝ)) :
    (∫ x, f x ∂M.perronLaw hM) =
      ∫ x, M.perronFunction hM x * f x ∂M.mu := by
  rw [perronLaw, integral_withDensity_eq_integral_smul
    (M.perronDensity_continuous hM).measurable]
  apply integral_congr_ae
  filter_upwards [] with x
  rfl

/-- The quadratic Perron scale from the paper. -/
def alpha (M : CompactBJRModel S) (hM : M.IsRegularCritical) : ℝ :=
  ∫ x, (M.perronFunction hM x) ^ 2 ∂M.mu

/-- The cubic Perron scale from the paper. -/
def beta (M : CompactBJRModel S) (hM : M.IsRegularCritical) : ℝ :=
  ∫ x, (M.perronFunction hM x) ^ 3 ∂M.mu

theorem alpha_pos (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    0 < M.alpha hM := by
  have hn : (Set.univ : Set S).Nonempty :=
    nonempty_of_measure_ne_zero (μ := M.mu) (by simp)
  obtain ⟨x, -⟩ := hn
  unfold alpha
  apply integral_pos_of_integrable_nonneg_nonzero (x := x)
  · exact (M.perronFunction hM).continuous.pow 2
  · exact ((M.perronFunction hM).continuous.pow 2).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  · intro y
    positivity
  · exact ne_of_gt (pow_pos (M.perronFunction_pos hM x) 2)

theorem beta_pos (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    0 < M.beta hM := by
  have hn : (Set.univ : Set S).Nonempty :=
    nonempty_of_measure_ne_zero (μ := M.mu) (by simp)
  obtain ⟨x, -⟩ := hn
  unfold beta
  apply integral_pos_of_integrable_nonneg_nonzero (x := x)
  · exact (M.perronFunction hM).continuous.pow 3
  · exact ((M.perronFunction hM).continuous.pow 3).integrable_of_hasCompactSupport
      isClosed_closure.isCompact
  · intro y
    exact (pow_pos (M.perronFunction_pos hM y) 3).le
  · exact ne_of_gt (pow_pos (M.perronFunction_pos hM x) 3)

/-- The paper's degree function, now visibly continuous. -/
def degreeFunction (M : CompactBJRModel S) : C(S, ℝ) :=
  M.kernel.degreeMap M.mu

end CompactBJRModel
end PerronWright
