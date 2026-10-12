import PerronWright.Probability.CountableTVWindowTestTransfer

/-! # Actual countable marked-window weak transfer

The canonical law is the genuine constant-mark pushforward of an actual
unmarked weak limit. The empirical marked source is never replaced by
that pushforward. Its bounded tests approach the constant-mark source
tests by the proved actual graph integral estimate. Compactness of the
unmarked window laws also supplies genuine joint subsequential limits.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators Classical Real Topology
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableTVWindowConvergence

open CountableVariationMarks CountableComponentWindowLaw CountableTVWindowTestTransfer
open ComponentWindowPointMeasures FinitePointMeasureCompact FinitePointMeasureMarking
open GraphWindowSource GraphWindowFactorialLimits

def canonicalMarkedWindowLaw (p : VariationMark) (a b : ℝ) (R : ℕ)
    (μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R))) :
    ProbabilityMeasure (PointMeasure (MarkedWindow a b R)) :=
  μ.map (continuous_mapPoint (fun z ↦ (z, p)) (continuous_id.prodMk continuous_const)).measurable.aemeasurable

theorem continuous_canonicalMarkedWindowLaw (p : VariationMark) (a b : ℝ) (R : ℕ) :
    Continuous (canonicalMarkedWindowLaw p a b R) :=
  ProbabilityMeasure.continuous_map
    (continuous_mapPoint (fun z ↦ (z, p)) (continuous_id.prodMk continuous_const))

theorem canonicalMarkedWindowLaw_integral (M : CountableKernel) (level : ℕ → ℕ)
    (lambda a b : ℝ) (R n : ℕ) {lower : ℝ} (hlower : 0 < lower)
    (hlo : ∀ s t, lower ≤ M.kernel s t) (p : VariationMark)
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) :
    (∫ η, F η ∂(canonicalMarkedWindowLaw p a b R
      (windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R n) : Measure _)) =
      ∫ G, F (constantMark p (windowPointMeasure a b R 1 G))
        ∂M.empiricalNormalizedGraphLaw level lambda hlower hlo n := by
  unfold canonicalMarkedWindowLaw
  rw [ProbabilityMeasure.toMeasure_map, integral_map
    (continuous_mapPoint (fun z ↦ (z, p)) (continuous_id.prodMk continuous_const)).measurable.aemeasurable
      F.continuous.measurable.aestronglyMeasurable]
  exact windowLaw_integral (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R n
    (f := fun η ↦ F (constantMark p η))
    ((F.continuous.comp (continuous_mapPoint _ (continuous_id.prodMk continuous_const))).measurable)

theorem means_difference_integral (M : CountableKernel) (level : ℕ → ℕ)
    (lambda a b : ℝ) (R n : ℕ) {lower : ℝ} (hlower : 0 < lower)
    (hlo : ∀ s t, lower ≤ M.kernel s t) (p : VariationMark)
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) :
    (∫ η, F η ∂(M.empiricalMarkedWindowLaw level lambda a b R hlower hlo n : Measure _)) -
      (∫ η, F η ∂(canonicalMarkedWindowLaw p a b R
        (windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R n) : Measure _)) =
    ∫ G, testDifference M level a b R n p F G
      ∂M.empiricalNormalizedGraphLaw level lambda hlower hlo n := by
  rw [M.empiricalMarkedWindowLaw_integral level lambda a b R hlower hlo n F.continuous.measurable,
    canonicalMarkedWindowLaw_integral M level lambda a b R n hlower hlo p F,
    ← integral_sub Integrable.of_finite Integrable.of_finite]
  rfl

theorem means_difference_tendsto_zero
    (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (hlocal : HasUniformLocalLimit (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
      (M.alpha hM) (M.beta hM) lambda)
    (p : VariationMark)
    (hTV : ∀ δ > 0, Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n p δ)
      atTop (𝓝 0))
    (F : PointMeasure (MarkedWindow a b R) →ᵇ ℝ) :
    Tendsto (fun n ↦
      (∫ η, F η ∂(M.empiricalMarkedWindowLaw level lambda a b R hlower hlo n : Measure _)) -
        (∫ η, F η ∂(canonicalMarkedWindowLaw p a b R
          (windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo) a b R n) : Measure _)))
      atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) _
    (testDifference_l1_tendsto_zero M hM level lambda a b ha hab R hlower hlo hlocal p hTV F)
  exact Eventually.of_forall (fun n ↦ by
    rw [means_difference_integral M level lambda a b R n hlower hlo p F]
    exact abs_integral_le_integral_abs)

/-- A composition lemma along a genuine unmarked weak subsequence. It
is used below with a subsequence constructed from actual source tightness. -/
theorem markedWindowLaw_tendsto_of_unmarked
    (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (hlocal : HasUniformLocalLimit (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
      (M.alpha hM) (M.beta hM) lambda)
    (p : VariationMark)
    (hTV : ∀ δ > 0, Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n p δ)
      atTop (𝓝 0))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)))
    (hsource : Tendsto (fun n ↦ windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
      a b R (N n)) atTop (𝓝 μ)) :
    Tendsto (fun n ↦ M.empiricalMarkedWindowLaw level lambda a b R hlower hlo (N n)) atTop
      (𝓝 (canonicalMarkedWindowLaw p a b R μ)) := by
  have hc := (continuous_canonicalMarkedWindowLaw p a b R).tendsto μ |>.comp hsource
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  have hCF := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hc F
  have hdiff := (means_difference_tendsto_zero M hM level lambda a b ha hab R hlower hlo hlocal p hTV F).comp hN
  simpa only [Function.comp_apply, zero_add, sub_add_cancel] using hdiff.add hCF

theorem exists_reindexed_actual_unmarked_and_marked_window_subseq
    (M : CountableKernel) (hM : M.IsRegularCritical) (level : ℕ → ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t)
    (hlocal : HasUniformLocalLimit (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
      (M.alpha hM) (M.beta hM) lambda)
    (p : VariationMark)
    (hTV : ∀ δ > 0, Tendsto (fun n ↦ M.growingWindowBadProbability level lambda a b R hlower hlo n p δ)
      atTop (𝓝 0)) (I : ℕ → ℕ) (hI : Tendsto I atTop atTop) :
    ∃ μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)), ∃ N : ℕ → ℕ, StrictMono N ∧
      Tendsto (fun n ↦ windowLaw (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
        a b R (I (N n))) atTop (𝓝 μ) ∧
      Tendsto (fun n ↦ M.empiricalMarkedWindowLaw level lambda a b R hlower hlo (I (N n))) atTop
        (𝓝 (canonicalMarkedWindowLaw p a b R μ)) := by
  let : Nonempty (SurplusWindow a b R) := ⟨(⟨a, le_rfl, hab⟩, ⟨0, by omega⟩)⟩
  let : MetricSpace (PointMeasure (SurplusWindow a b R)) := TopologicalSpace.metrizableSpaceMetric _
  let : MetricSpace (ProbabilityMeasure (PointMeasure (SurplusWindow a b R))) :=
    TopologicalSpace.metrizableSpaceMetric _
  have hc := isCompact_closure_windowLaws (M.empiricalNormalizedGraphLaw level lambda hlower hlo)
    (M.beta_pos hM) hlocal ha hab R
  obtain ⟨μ, _, N, hN, hμ⟩ := hc.tendsto_subseq
    (fun n ↦ subset_closure (Set.mem_range_self (I n)))
  exact ⟨μ, N, hN, hμ, markedWindowLaw_tendsto_of_unmarked M hM level lambda a b ha hab R
    hlower hlo hlocal p hTV (fun n ↦ I (N n)) (hI.comp hN.tendsto_atTop) μ hμ⟩

end PerronWright.CountableTVWindowConvergence
