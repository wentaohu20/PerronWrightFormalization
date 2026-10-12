import PerronWright.Probability.CountableComponentWindowLaw
import PerronWright.Probability.FiniteIrreducibleMarkedPointLawLimit

/-! # Genuine finite graph window limits with literal natural-type TV marks

The source has the original fixed assignment and its actual empirical
probability marks. Finite weak marks are embedded continuously in the
proved natural-type total-variation space. The spatial limit is constructed
from the graph sequence, not given as a hypothesis. No compactness or local
compactness of the total-variation mark space is assumed.
-/

open MeasureTheory Filter Topology
open scoped Classical
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.FiniteVariationWindowLawLimit

open CountableComponentWindowLaw FinitePointMeasureCompact FinitePointMeasureMarking
open FiniteIrreducibleTypePlacementMultiplicity (fiberCount)

variable {S : Type*} [Fintype S] [DecidableEq S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def markedWindowLaw (M : FiniteIrreducibleModel S) (f : S → ℕ)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S) :
    ProbabilityMeasure (PointMeasure (MarkedWindow a b R)) :=
  ⟨(FiniteIrreducibleComponentProcess.graphLaw M lambda n x).map
    (fun G ↦ markedWindowPointMeasure (fun v ↦ f (x v)) G a b R),
    Measure.isProbabilityMeasure_map
      (measurable_markedWindowPointMeasure _ a b R).aemeasurable⟩

theorem markedWindowLaw_eq_finite_map (M : FiniteIrreducibleModel S) (f : S → ℕ)
    (lambda a b : ℝ) (R n : ℕ) (x : Fin n → S) :
    markedWindowLaw M f lambda a b R n x =
      (FiniteIrreducibleMarkedComponentProcess.markedWindowLaw M lambda a b R n x).map
        (continuous_embedPointWindow f a b R).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [markedWindowLaw, ProbabilityMeasure.toMeasure_map,
    FiniteIrreducibleMarkedComponentProcess.markedWindowLaw_toMeasure]
  rw [Measure.map_map (continuous_embedPointWindow f a b R).measurable
    (FiniteIrreducibleMarkedComponentProcess.measurable_markedWindowPointMeasure x a b R)]
  change (FiniteIrreducibleComponentProcess.graphLaw M lambda n x).map
    (fun G ↦ markedWindowPointMeasure (fun v ↦ f (x v)) G a b R) =
    (FiniteIrreducibleComponentProcess.graphLaw M lambda n x).map _
  congr 1
  funext G
  exact (embedPointWindow_actual_marks f x G a b R).symm

def perronVariationMark (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (f : S → ℕ) :
    CountableVariationMarks.VariationMark :=
  FiniteProbabilityVariationEmbedding.embed f
    (FiniteIrreducibleConnectedTypeLaw.perronLaw M hM)

def canonicalPerronVariationLaw (M : FiniteIrreducibleModel S) (hM : M.IsCritical)
    (f : S → ℕ) (a b : ℝ) (R : ℕ)
    (μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R))) :
    ProbabilityMeasure (PointMeasure (MarkedWindow a b R)) :=
  μ.map (continuous_mapPoint (fun z ↦ (z, perronVariationMark M hM f))
    (continuous_id.prodMk continuous_const)).measurable.aemeasurable

theorem canonicalPerronVariationLaw_eq_finite_map (M : FiniteIrreducibleModel S)
    (hM : M.IsCritical) (f : S → ℕ) (a b : ℝ) (R : ℕ)
    (μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R))) :
    canonicalPerronVariationLaw M hM f a b R μ =
      (FiniteIrreducibleMarkedWindowConvergence.canonicalPerronMarkedLaw M hM a b R μ).map
        (continuous_embedPointWindow f a b R).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [canonicalPerronVariationLaw,
    FiniteIrreducibleMarkedWindowConvergence.canonicalPerronMarkedLaw,
    canonicalMarkedLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_embedPointWindow f a b R).measurable
    (continuous_constantMark (E := SurplusWindow a b R)
      (FiniteIrreducibleMarkedComponentProcess.perronWeakMark M hM)).measurable]
  change (μ : Measure _).map
    (mapPoint (fun z ↦ (z, perronVariationMark M hM f))
      (measurable_id.prodMk measurable_const)) =
    (μ : Measure _).map
      (embedPointWindow f a b R ∘
        constantMark (FiniteIrreducibleMarkedComponentProcess.perronWeakMark M hM))
  congr 1
  funext η
  apply Subtype.ext
  apply Subtype.ext
  change (η.val.val.map
    (fun z ↦ (z, perronVariationMark M hM f))) =
    ((η.val.val.map
      (fun z ↦ (z, FiniteIrreducibleMarkedComponentProcess.perronWeakMark M hM))).map
        (embedWindow f a b R))
  have hpair : Measurable (fun z : SurplusWindow a b R ↦
      (z, FiniteIrreducibleMarkedComponentProcess.perronWeakMark M hM)) :=
    measurable_id.prodMk measurable_const
  have hmap := Measure.map_map (continuous_embedWindow f a b R).measurable hpair
    (μ := η.val.val)
  exact hmap.symm

theorem exists_unique_unmarked_and_TVmarkedWindowLaw_limit
    (M : FiniteIrreducibleModel S) (hM : M.IsCritical) (f : S → ℕ)
    (lambda a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℕ)
    (x : (n : ℕ) → Fin n → S) (D : ℝ) (hD : 0 ≤ D)
    (hround : ∀ᶠ n in atTop, ∀ s,
      |(fiberCount (x n) s : ℝ) - (n : ℝ) * M.weight s| ≤ D) :
    ∃! μ : ProbabilityMeasure (PointMeasure (SurplusWindow a b R)),
      Tendsto (fun n ↦ FiniteIrreducibleComponentProcess.unmarkedWindowLaw
        M lambda a b R n (x n)) atTop (𝓝 μ) ∧
      Tendsto (fun n ↦ markedWindowLaw M f lambda a b R n (x n)) atTop
        (𝓝 (canonicalPerronVariationLaw M hM f a b R μ)) := by
  obtain ⟨μ, ⟨hu, hm⟩, _⟩ :=
    FiniteIrreducibleMarkedPointLawLimit.exists_unique_unmarked_and_markedWindowLaw_limit
      M hM lambda a b ha hab R x D hD hround
  have htv := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hm
    (continuous_embedPointWindow f a b R)
  simp_rw [← markedWindowLaw_eq_finite_map,
    ← canonicalPerronVariationLaw_eq_finite_map] at htv
  obtain ⟨_, _, hunique⟩ :=
    FiniteIrreducibleWindowPointLawLimit.exists_unique_unmarkedWindowLaw_limit
      M hM lambda a b ha hab R x D hD hround
  exact ⟨μ, ⟨hu, htv⟩, fun ρ hρ ↦ (hunique ρ hρ.1).trans (hunique μ hu).symm⟩

end PerronWright.FiniteVariationWindowLawLimit
