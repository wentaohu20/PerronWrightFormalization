import PerronWright.Probability.FinitePointMeasurePolish
import PerronWright.Probability.CountFamilyDeterminacy
import PerronWright.Probability.FactorialCountConvergenceCriterion

/-!
# A generating count family determines the actual point-measure law

Counts on a countable generating pi-system containing the whole window
are a proved measurable embedding of the actual point space. The proved
standard Borel property is obtained from its genuine weak topology.
Actual finite count laws, or their target-determinate mixed factorial
moments, therefore identify the full point-measure probability law.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Topology ENNReal NNReal

noncomputable section
set_option maxHeartbeats 1000000

namespace PerronWright.FinitePointMeasureCountDeterminacy

open FiniteAtomicPointMeasure FinitePointMeasureCompact FinitePointMeasureMeasurable
open FactorialCountDeterminacy FactorialGeneratingSeries FactorialCountConvergenceCriterion

variable {E : Type*} [MeasurableSpace E]
variable {T : Type*}

/-- The actual complete count encoding. -/
def countEncoding (A : T → Set E) (η : PointMeasure E) : T → ℕ :=
  fun i ↦ count η (A i)

theorem cells_measurable (A : T → Set E)
    (hgen : ‹MeasurableSpace E› = MeasurableSpace.generateFrom (Set.range A)) (i : T) :
    MeasurableSet (A i) := by
  rw [hgen]
  exact MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self i)

/-- Equality of actual counts on a generating pi-system containing
`univ` identifies the actual finite integer measure. -/
theorem injective_countEncoding (A : T → Set E)
    (hgen : ‹MeasurableSpace E› = MeasurableSpace.generateFrom (Set.range A))
    (hpi : IsPiSystem (Set.range A)) (huniv : Set.univ ∈ Set.range A) :
    Function.Injective (countEncoding A) := by
  intro η ρ hηρ
  have heval (i : T) : ((η : FiniteMeasure E) : Measure E) (A i) =
      ((ρ : FiniteMeasure E) : Measure E) (A i) := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top ((η : FiniteMeasure E) : Measure E) (A i))
      (measure_ne_top ((ρ : FiniteMeasure E) : Measure E) (A i))).mp
    change ((η : FiniteMeasure E) : Measure E).real (A i) =
      ((ρ : FiniteMeasure E) : Measure E).real (A i)
    rw [measure_real_eq_count η (cells_measurable A hgen i),
      measure_real_eq_count ρ (cells_measurable A hgen i)]
    exact_mod_cast congrFun hηρ i
  apply Subtype.ext
  apply FiniteMeasure.toMeasure_injective
  apply ext_of_generate_finite (Set.range A) hgen hpi
  · intro B hB
    obtain ⟨i, rfl⟩ := hB
    exact heval i
  · obtain ⟨i, hi⟩ := huniv
    rw [← hi]
    exact heval i

variable [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]

/-- Measurable embedding, using the already-proved actual point-space
Polishness rather than assuming count-law determination. -/
theorem measurableEmbedding_countEncoding [Countable T] (A : T → Set E)
    (hgen : ‹MeasurableSpace E› = MeasurableSpace.generateFrom (Set.range A))
    (hpi : IsPiSystem (Set.range A)) (huniv : Set.univ ∈ Set.range A) :
    MeasurableEmbedding (countEncoding A) :=
  (measurable_count_vector A (cells_measurable A hgen)).measurableEmbedding
    (injective_countEncoding A hgen hpi huniv)

/-- Literal count-family probability law under an actual point law. -/
def familyLaw (ν : ProbabilityMeasure (PointMeasure E)) (A : T → Set E)
    (hgen : ‹MeasurableSpace E› = MeasurableSpace.generateFrom (Set.range A)) :
    ProbabilityMeasure (T → ℕ) :=
  countLaw ν A (cells_measurable A hgen)

/-- Literal finite-coordinate count law. -/
def finiteCountLaw (ν : ProbabilityMeasure (PointMeasure E)) (A : T → Set E)
    (hgen : ‹MeasurableSpace E› = MeasurableSpace.generateFrom (Set.range A))
    (I : Finset T) : Measure (I → ℕ) :=
  CountFamilyDeterminacy.finiteLaw (familyLaw ν A hgen : Measure (T → ℕ)) I

instance finiteCountLaw_isFinite (ν : ProbabilityMeasure (PointMeasure E)) (A : T → Set E)
    (hgen : ‹MeasurableSpace E› = MeasurableSpace.generateFrom (Set.range A)) (I : Finset T) :
    IsFiniteMeasure (finiteCountLaw ν A hgen I) := by
  unfold finiteCountLaw
  infer_instance

instance finiteCountLaw_isProbability (ν : ProbabilityMeasure (PointMeasure E)) (A : T → Set E)
    (hgen : ‹MeasurableSpace E› = MeasurableSpace.generateFrom (Set.range A)) (I : Finset T) :
    IsProbabilityMeasure (finiteCountLaw ν A hgen I) := by
  unfold finiteCountLaw CountFamilyDeterminacy.finiteLaw
  apply Measure.isProbabilityMeasure_map
  exact (measurable_pi_lambda _ (fun i : I ↦ measurable_pi_apply (i : T))).aemeasurable

/-- A full actual count-family law identifies the actual point law. -/
theorem probabilityMeasure_eq_of_familyLaw [Countable T]
    (μ ν : ProbabilityMeasure (PointMeasure E)) (A : T → Set E)
    (hgen : ‹MeasurableSpace E› = MeasurableSpace.generateFrom (Set.range A))
    (hpi : IsPiSystem (Set.range A)) (huniv : Set.univ ∈ Set.range A)
    (hlaw : familyLaw μ A hgen = familyLaw ν A hgen) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply (measurableEmbedding_countEncoding A hgen hpi huniv).map_injective
  exact congrArg ProbabilityMeasure.toMeasure hlaw

/-- Equality of every actual finite count law determines the whole
point-measure probability law on the compact metric window. -/
theorem probabilityMeasure_eq_of_finite_countLaws [Countable T]
    (μ ν : ProbabilityMeasure (PointMeasure E)) (A : T → Set E)
    (hgen : ‹MeasurableSpace E› = MeasurableSpace.generateFrom (Set.range A))
    (hpi : IsPiSystem (Set.range A)) (huniv : Set.univ ∈ Set.range A)
    (hfinite : ∀ I : Finset T, finiteCountLaw μ A hgen I = finiteCountLaw ν A hgen I) :
    μ = ν := by
  apply probabilityMeasure_eq_of_familyLaw μ ν A hgen hpi huniv
  apply ProbabilityMeasure.toMeasure_injective
  have hμ : IsProjectiveLimit (familyLaw μ A hgen : Measure (T → ℕ))
      (fun I : Finset T ↦ finiteCountLaw μ A hgen I) := fun _ ↦ rfl
  have hν : IsProjectiveLimit (familyLaw ν A hgen : Measure (T → ℕ))
      (fun I : Finset T ↦ finiteCountLaw μ A hgen I) := fun I ↦ (hfinite I).symm
  exact hμ.unique hν

/-- Actual mixed factorial moments on a countable generating family
determine the whole point-measure law. Only the target finite count
laws need actual total-count exponential moments. -/
theorem probabilityMeasure_eq_of_finite_factorialMoments [Countable T]
    (μ ν : ProbabilityMeasure (PointMeasure E)) (A : T → Set E)
    (hgen : ‹MeasurableSpace E› = MeasurableSpace.generateFrom (Set.range A))
    (hpi : IsPiSystem (Set.range A)) (huniv : Set.univ ∈ Set.range A)
    (hμint : ∀ (I : Finset T) (q : I → ℕ),
      Integrable (factorialPolynomial q) (finiteCountLaw μ A hgen I))
    (hνexp : ∀ I : Finset T, Integrable (fun n ↦ (3 : ℝ) ^ totalCount n)
      (finiteCountLaw ν A hgen I))
    (hmom : ∀ (I : Finset T) (q : I → ℕ),
      factorialMoment (finiteCountLaw μ A hgen I) q =
        factorialMoment (finiteCountLaw ν A hgen I) q) : μ = ν := by
  apply probabilityMeasure_eq_of_finite_countLaws μ ν A hgen hpi huniv
  intro I
  symm
  exact measure_eq_of_factorialMoments
    (finiteCountLaw ν A hgen I) (finiteCountLaw μ A hgen I)
    (factorialPolynomial_integrable_of_total_exp _ (hνexp I)) (hμint I)
    (target_series_of_total_exp _ (hνexp I)) (fun q ↦ (hmom I q).symm)

end PerronWright.FinitePointMeasureCountDeterminacy
