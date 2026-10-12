import PerronWright.Probability.BrownianFullHorizonSpatialSupport
import PerronWright.Probability.FinitePoissonArraySuperposition
import PerronWright.Probability.BrownianUnderGraphDisjointCounts

/-!
# Genuine full spatial Poisson counts on bounded Borel windows

Actual strip counts have the proved independent Poisson row law. Their
finite sums, obtained from genuine samplewise strip support, consequently
have the full summed-intensity product law. Thus the full random measure
has actual independent Poisson cell counts; this property is a conclusion.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace PerronWright.BrownianFullHorizonSpatialCounts

open BrownianPathLaw FinitePointMeasureCompact BrownianFullHorizonSpatialKernel
open BrownianFullHorizonSpatialIntensity BrownianFullHorizonSpatialSupport

def spatialCount (a : SpatialAtoms) (A : Set (ℝ × ℝ)) : ℕ :=
  ⌊(spatialMeasure a).real A⌋₊

theorem measurable_spatialCount {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    Measurable (fun a ↦ spatialCount a A) :=
  Nat.measurable_floor.comp (((Measure.measurable_coe hA).comp measurable_spatialMeasure).ennreal_toReal)

theorem spatialCount_eq_sum {a : SpatialAtoms} (ha : StripSupported a) (N : ℕ)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hAN : A ⊆ timeCut N) :
    spatialCount a A = ∑ j ∈ Finset.range N, count (a j) A := by
  unfold spatialCount Measure.real
  rw [spatialMeasure_eq_finite_sum ha N hA hAN,
    ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _)]
  have he : (∑ j ∈ Finset.range N,
      (((a j : FiniteMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) A).toReal) =
      ((∑ j ∈ Finset.range N, count (a j) A : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact measure_real_eq_count (a j) hA
  rw [he,Nat.floor_natCast]

theorem strip_intensity_zero_after (lambda : ℝ) (f : Path) (N j : ℕ)
    (hNj : N ≤ j) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hAN : A ⊆ timeCut N) :
    volume (A ∩ BrownianUnderGraphIntensity.region lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f) = 0 := by
  have he : A ∩ stripRegion lambda f j = ∅ := by
    ext z
    simp only [mem_inter_iff,mem_empty_iff_false]
    apply iff_false_intro
    rintro ⟨hz,hstrip⟩
    have ht : z.1 < (N : ℝ) := hAN hz
    have hj : (j : ℝ) ≤ z.1 := hstrip.1.1
    have hc : (N : ℝ) ≤ j := by exact_mod_cast hNj
    linarith
  have hr := congrArg (fun μ : Measure (ℝ × ℝ) ↦ μ A) (restrict_stripRegion lambda f j)
  change volume.restrict (stripRegion lambda f j) A = volume.restrict
    (BrownianUnderGraphIntensity.region lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f) A at hr
  rw [Measure.restrict_apply hA,Measure.restrict_apply hA,he,measure_empty] at hr
  exact hr.symm

theorem intensity_eq_finite_sum (lambda : ℝ) (f : Path) (N : ℕ)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hAN : A ⊆ timeCut N) :
    intensity lambda f A = ∑ j ∈ Finset.range N,
      volume (A ∩ BrownianUnderGraphIntensity.region lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f) := by
  rw [intensity_apply_eq_tsum lambda f hA]
  apply tsum_eq_sum
  intro j hj
  exact strip_intensity_zero_after lambda f N j
    (Nat.le_of_not_gt (fun h ↦ hj (Finset.mem_range.mpr h))) hA hAN

theorem intensity_toNNReal_eq_sum (lambda : ℝ) (f : Path) (N : ℕ)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (hAN : A ⊆ timeCut N) :
    (intensity lambda f A).toNNReal = ∑ j ∈ Finset.range N,
      (volume (A ∩ BrownianUnderGraphIntensity.region lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f)).toNNReal := by
  rw [intensity_eq_finite_sum lambda f N hA hAN]
  apply ENNReal.toNNReal_sum
  intro j _
  exact (measure_mono inter_subset_right).trans_lt
    (lt_top_iff_ne_top.mpr (BrownianUnderGraphIntensity.volume_region_ne_top lambda _ _ f)) |>.ne

variable {D : Type*} [Fintype D]

def rowCounts (A : D → Set (ℝ × ℝ)) (a : SpatialAtoms) (j : ℕ) (i : D) : ℕ := count (a j) (A i)

def stripRates (lambda : ℝ) (f : Path) (A : D → Set (ℝ × ℝ)) (j : ℕ) (i : D) : ℝ≥0 :=
  (volume (A i ∩ BrownianUnderGraphIntensity.region lambda (j : ℝ≥0) (j + 1 : ℝ≥0) f)).toNNReal

omit [Fintype D] in
theorem measurable_rowCounts (A : D → Set (ℝ × ℝ)) (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (rowCounts A) :=
  measurable_pi_lambda _ (fun j ↦
    (FinitePointMeasureMeasurable.measurable_count_vector A hA).comp (measurable_pi_apply j))

theorem spatialLaw_map_rowCounts (lambda : ℝ) (f : Path) (A : D → Set (ℝ × ℝ))
    (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j))) (hA : ∀ i, MeasurableSet (A i)) :
    (spatialLaw lambda f).map (rowCounts A) =
      FinitePoissonArraySuperposition.matrixLaw (stripRates lambda f A) := by
  rw [spatialLaw]
  change (CountableProductProbabilityKernel.law (stripKernel lambda) f).map
    (fun a j i ↦ count (a j) (A i)) = _
  rw [CountableProductProbabilityKernel.law_map_coordinatewise
    (stripKernel lambda) f (fun _ η ↦ fun i ↦ count η (A i))
      (fun _ ↦ FinitePointMeasureMeasurable.measurable_count_vector A hA)]
  congr 1
  funext j
  exact BrownianUnderGraphDisjointCounts.law_count_vector lambda _ _ f A hAd hA

/-- Actual finite disjoint Borel cell counts under the full spatial law
are exactly independent Poisson variables at the genuine full intensity. -/
theorem spatialLaw_map_count_vector (lambda : ℝ) (f : Path) (N : ℕ)
    (A : D → Set (ℝ × ℝ)) (hAd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (hA : ∀ i, MeasurableSet (A i)) (hAN : ∀ i, A i ⊆ timeCut N) :
    (spatialLaw lambda f).map (fun a i ↦ spatialCount a (A i)) =
      PoissonCountKernel.finiteCountLaw (fun i ↦ (intensity lambda f (A i)).toNNReal) := by
  have hae : (fun a i ↦ spatialCount a (A i)) =ᵐ[spatialLaw lambda f]
      (fun a ↦ FinitePoissonArraySuperposition.sumArray N (rowCounts A a)) := by
    filter_upwards [ae_spatialLaw_stripSupported lambda f] with a ha
    funext i
    exact spatialCount_eq_sum ha N (hA i) (hAN i)
  rw [Measure.map_congr hae]
  change (spatialLaw lambda f).map
    (FinitePoissonArraySuperposition.sumArray N ∘ rowCounts A) = _
  rw [← Measure.map_map
    (FinitePoissonArraySuperposition.measurable_sumArray N) (measurable_rowCounts A hA),
    spatialLaw_map_rowCounts lambda f A hAd hA,
    FinitePoissonArraySuperposition.matrixLaw_map_sumArray]
  congr 1
  funext i
  exact (intensity_toNNReal_eq_sum lambda f N (hA i) (hAN i)).symm

end PerronWright.BrownianFullHorizonSpatialCounts
