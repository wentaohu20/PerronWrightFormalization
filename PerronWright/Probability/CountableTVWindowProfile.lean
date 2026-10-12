import PerronWright.Probability.CountableTVDistanceTests
import PerronWright.Probability.CountableComponentWindowLaw
import PerronWright.Probability.ComponentWindowMarkedCounts
import PerronWright.Probability.FinitePointMeasureMeasurable

/-! # Literal TV-distance energy and bad marks in a component window

Every sum and event below refers to actual graph components. The event
also has its intrinsic weak-Borel point-measure formulation. The Markov
bound uses an actual finite-graph integral and applies without any
compactness assumption on the variation-mark space.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical Real
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.CountableTVWindowProfile

open CountableVariationMarks ComponentWindowPointMeasures
open ComponentWindowFactorialCounts ComponentWindowMarkedCounts
open CountableComponentWindowLaw FinitePointMeasureCompact

def windowDistance {n : ℕ} (x : Fin n → ℕ) (G : SimpleGraph (Fin n))
    (a b : ℝ) (R : ℕ) (p : VariationMark) : ℝ :=
  ∑ C : WindowComponent a b R 1 G, dist (ofProbability (EmpiricalTypeMarks.componentMark x C.val)) p

theorem windowDistance_nonneg {n : ℕ} (x : Fin n → ℕ) (G : SimpleGraph (Fin n))
    (a b : ℝ) (R : ℕ) (p : VariationMark) : 0 ≤ windowDistance x G a b R p :=
  Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)

theorem windowDistance_le_twice_mass {n : ℕ} (x : Fin n → ℕ)
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) (p : VariationMark) :
    windowDistance x G a b R p ≤ 2 * (Fintype.card (WindowComponent a b R 1 G) : ℝ) := by
  calc
    _ ≤ ∑ _C : WindowComponent a b R 1 G, (2 : ℝ) :=
      Finset.sum_le_sum (fun _ _ ↦ dist_le_two _ _)
    _ = _ := by simp [mul_comm]

private def singletonEmbeddingEquiv (I : Type*) : (Fin 1 ↪ I) ≃ I where
  toFun t := t 0
  invFun x := ⟨fun _ ↦ x, fun i j _ ↦ Subsingleton.elim i j⟩
  left_inv t := by
    apply Function.Embedding.ext
    intro i
    exact congrArg t (Subsingleton.elim 0 i)
  right_inv _ := rfl

theorem windowDistance_eq_integer_sum {n : ℕ} (x : Fin n → ℕ)
    (G : SimpleGraph (Fin n)) (hn : 0 < n) (a b : ℝ) (hb : 0 ≤ b)
    (R : ℕ) (p : VariationMark) :
    windowDistance x G a b R p =
      ∑ r ∈ surplusIndices 1 R,
        ∑ k ∈ integerWindow ((n : ℝ) ^ (2 / 3 : ℝ)) (fun _ ↦ a) (fun _ ↦ b),
          CountableVariationComponentCounts.markedCount x G k r (distanceTest p) := by
  let Ψ : (Fin 1 → ProbabilityMeasure ℕ) → ℝ := fun ν ↦ dist (ofProbability (ν 0)) p
  have he : windowMarkedCount x G a b R Ψ = windowDistance x G a b R p :=
    Fintype.sum_equiv (singletonEmbeddingEquiv _) _ _ (fun _ ↦ rfl)
  rw [← he, windowMarkedCount_eq_sum x G hn a b hb R Ψ]
  rfl

def badTVEvent {n : ℕ} (x : Fin n → ℕ) (a b : ℝ) (R : ℕ)
    (p : VariationMark) (δ : ℝ) : Set (SimpleGraph (Fin n)) :=
  {G | ∃ C : WindowComponent a b R 1 G,
    δ ≤ dist (ofProbability (EmpiricalTypeMarks.componentMark x C.val)) p}

theorem measurableSet_badTVEvent {n : ℕ} (x : Fin n → ℕ) (a b : ℝ)
    (R : ℕ) (p : VariationMark) (δ : ℝ) : MeasurableSet (badTVEvent x a b R p δ) :=
  Set.to_countable _ |>.measurableSet

theorem delta_le_windowDistance_of_bad {n : ℕ} (x : Fin n → ℕ)
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) (p : VariationMark) (δ : ℝ)
    (hbad : G ∈ badTVEvent x a b R p δ) : δ ≤ windowDistance x G a b R p := by
  obtain ⟨C, hC⟩ := hbad
  apply hC.trans
  exact Finset.single_le_sum
    (f := fun C : WindowComponent a b R 1 G ↦
      dist (ofProbability (EmpiricalTypeMarks.componentMark x C.val)) p)
    (fun _ _ ↦ dist_nonneg) (Finset.mem_univ C)

theorem badTVEvent_probability_le {n : ℕ} (x : Fin n → ℕ) (a b : ℝ)
    (R : ℕ) (p : VariationMark) (δ : ℝ) (hδ : 0 < δ)
    (μ : Measure (SimpleGraph (Fin n))) [IsFiniteMeasure μ] :
    μ.real (badTVEvent x a b R p δ) ≤ (∫ G, windowDistance x G a b R p ∂μ) / δ := by
  have hI : Integrable (fun G ↦ windowDistance x G a b R p) μ := Integrable.of_finite
  have hh : μ (badTVEvent x a b R p δ) ≤
      ENNReal.ofReal (∫ G, windowDistance x G a b R p / δ ∂μ) :=
    (hI.div_const δ).measure_le_integral
      (Eventually.of_forall (fun G ↦ div_nonneg (windowDistance_nonneg x G a b R p) hδ.le))
      (fun G hG ↦ (le_div_iff₀ hδ).mpr (by
        simpa only [one_mul] using delta_le_windowDistance_of_bad x G a b R p δ hG))
  calc
    _ ≤ (ENNReal.ofReal (∫ G, windowDistance x G a b R p / δ ∂μ)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    _ = _ := by
      rw [integral_div, ENNReal.toReal_ofReal
        (div_nonneg (integral_nonneg (fun G ↦ windowDistance_nonneg x G a b R p)) hδ.le)]

def badMarkCell (a b : ℝ) (R : ℕ) (p : VariationMark) (δ : ℝ) : Set (MarkedWindow a b R) :=
  {z | δ ≤ dist z.2 p}

theorem isClosed_badMarkCell (a b : ℝ) (R : ℕ) (p : VariationMark) (δ : ℝ) :
    IsClosed (badMarkCell a b R p δ) :=
  isClosed_le continuous_const (continuous_snd.dist continuous_const)

theorem measurableSet_badPointEvent (a b : ℝ) (R : ℕ) (p : VariationMark) (δ : ℝ) :
    MeasurableSet {η : PointMeasure (MarkedWindow a b R) | 0 < count η (badMarkCell a b R p δ)} :=
  measurableSet_lt measurable_const (FinitePointMeasureMeasurable.measurable_count
    (isClosed_badMarkCell a b R p δ).measurableSet)

theorem badTVEvent_iff_badPointCount {n : ℕ} (x : Fin n → ℕ)
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) (p : VariationMark) (δ : ℝ) :
    G ∈ badTVEvent x a b R p δ ↔
      0 < count (markedWindowPointMeasure x G a b R) (badMarkCell a b R p δ) := by
  rw [markedWindowPointMeasure, FinitePointMeasureFintype.count_ofFintype _
    (isClosed_badMarkCell a b R p δ).measurableSet, Fintype.card_pos_iff]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨⟨C, hC⟩⟩
  · rintro ⟨C⟩
    exact ⟨C.val, C.property⟩

end PerronWright.CountableTVWindowProfile
