import PerronWright.Probability.FinitePointMeasureFactorialMeasure
import PerronWright.Probability.CountableFiniteTupleSampling

/-!
# Measurable intrinsic factorial test integrals

The factorial-measure map is genuinely measurable from the existing
finite-point-measure weak Borel space. Rectangle evaluations and total
mass, not measurability of a chosen enumeration, prove this fact.
Arbitrary nonnegative Borel coupled tests retain all atom multiplicities.
-/

open MeasureTheory Set
open scoped Classical BigOperators ENNReal

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FinitePointMeasureFactorialKernel

open FinitePointMeasureCompact FinitePointMeasureFintype
open FinitePointMeasureRectangleFactorials FinitePointMeasureFactorialMeasure
open CountableFiniteAtomSampling

variable {E J : Type*} [MeasurableSpace E] [Fintype J]

def testStatistic (Ψ : (J → E) → ℝ≥0∞) (η : PointMeasure E) : ℝ≥0∞ :=
  ∫⁻ z, Ψ z ∂factorialMeasure J η

def rectangleTest (A : J → Set E) (Ψ : (J → E) → ℝ≥0∞) (η : PointMeasure E) : ℝ≥0∞ :=
  testStatistic ((Set.pi univ A).indicator Ψ) η

theorem testStatistic_ofFintype {I : Type*} [Fintype I]
    (x : I → E) (Ψ : (J → E) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    testStatistic Ψ (ofFintype x) = ∑ e : J ↪ I, Ψ (fun j ↦ x (e j)) :=
  factorialMeasure_ofFintype_lintegral x Ψ hΨ

theorem rectangleTest_ofFintype {I : Type*} [Fintype I] (x : I → E)
    (A : J → Set E) (hA : ∀ j, MeasurableSet (A j))
    (Ψ : (J → E) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    rectangleTest A Ψ (ofFintype x) =
      ∑ e : {e : J ↪ I // ∀ j, x (e j) ∈ A j}, Ψ (fun j ↦ x (e.val j)) := by
  unfold rectangleTest
  rw [testStatistic_ofFintype x _ (hΨ.indicator (MeasurableSet.pi Set.countable_univ (fun j _ ↦ hA j)))]
  have hs := Finset.sum_subtype (p := fun e : J ↪ I ↦ ∀ j, x (e j) ∈ A j) (F := inferInstance)
    (Finset.univ.filter (fun e : J ↪ I ↦ ∀ j, x (e j) ∈ A j))
    (by intro e; simp) (fun e : J ↪ I ↦ Ψ (fun j ↦ x (e j)))
  simpa only [Finset.sum_filter,Set.indicator_apply,Set.mem_univ_pi] using hs

variable [TopologicalSpace E] [BorelSpace E] [HasOuterApproxClosed E]

/-- The source sigma structure is the actual finite-measure weak Borel
structure; no Giry/weak-Borel equality is a premise. -/
theorem measurable_factorialMeasure (J : Type*) [Fintype J] :
    Measurable (factorialMeasure J : PointMeasure E → Measure (J → E)) := by
  apply Measurable.measure_of_isPiSystem
    (generateFrom_pi (α := fun _ : J ↦ E)).symm isPiSystem_pi
  · rintro B ⟨A,hA,rfl⟩
    have hm : ∀ j, MeasurableSet (A j) := fun j ↦ hA j (mem_univ j)
    have he : (fun η : PointMeasure E ↦ factorialMeasure J η (Set.pi univ A)) =
        fun η ↦ (rectangleFactorial η A : ℝ≥0∞) :=
      funext (fun η ↦ factorialMeasure_rectangle η A hm)
    rw [he]
    exact (measurable_of_countable (fun n : ℕ ↦ (n : ℝ≥0∞))).comp
      (measurable_rectangleFactorial A hm)
  · have he : (fun η : PointMeasure E ↦ factorialMeasure J η univ) =
        fun η ↦ ((size η).descFactorial (Fintype.card J) : ℝ≥0∞) :=
      funext (factorialMeasure_univ J)
    rw [he]
    exact (measurable_of_countable (fun n : ℕ ↦ (n.descFactorial (Fintype.card J) : ℝ≥0∞))).comp
      measurable_size

theorem measurable_testStatistic (Ψ : (J → E) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    Measurable (testStatistic Ψ) :=
  (Measure.measurable_lintegral hΨ).comp (measurable_factorialMeasure J)

theorem measurable_rectangleTest (A : J → Set E) (hA : ∀ j, MeasurableSet (A j))
    (Ψ : (J → E) → ℝ≥0∞) (hΨ : Measurable Ψ) : Measurable (rectangleTest A Ψ) :=
  measurable_testStatistic _ (hΨ.indicator (MeasurableSet.pi Set.countable_univ (fun j _ ↦ hA j)))

variable [SecondCountableTopology E]

omit [TopologicalSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    [SecondCountableTopology E] in
theorem rectangleTest_ofFinset {I : Type*} (t : Finset I) (x : I → E)
    (A : J → Set E) (hA : ∀ j, MeasurableSet (A j))
    (Ψ : (J → E) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    rectangleTest A Ψ (ofFinset t x) =
      ∑' e : J → I, if Function.Injective e ∧ ∀ j, e j ∈ t ∧ x (e j) ∈ A j
        then Ψ (fun j ↦ x (e j)) else 0 := by
  rw [ofFinset,rectangleTest_ofFintype _ A hA Ψ hΨ]
  exact (CountableFiniteTupleSampling.tsum_tuple_test_eq_finite_sum t x A Ψ).symm

omit [TopologicalSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    [SecondCountableTopology E] in
theorem rectangleTest_pointMeasure {S I : Type*}
    (B : S → Set I) (X : S → I → E) (s : S) (hB : (B s).Finite)
    (A : J → Set E) (hA : ∀ j, MeasurableSet (A j))
    (Ψ : (J → E) → ℝ≥0∞) (hΨ : Measurable Ψ) :
    rectangleTest A Ψ (pointMeasure B X s) =
      ∑' e : J → I, if Function.Injective e ∧ ∀ j, e j ∈ B s ∧ X s (e j) ∈ A j
        then Ψ (fun j ↦ X s (e j)) else 0 := by
  have ht : B s = (hB.toFinset : Set I) := by
    ext i
    exact (Set.Finite.mem_toFinset hB).symm
  rw [pointMeasure_eq_ofFinset B X s hB.toFinset ht,rectangleTest_ofFinset _ _ _ hA Ψ hΨ]
  exact tsum_congr (fun e ↦ by simp only [Set.Finite.mem_toFinset])

end PerronWright.FinitePointMeasureFactorialKernel
