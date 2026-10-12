import PerronWright.Probability.CountableVariationTopology
import PerronWright.Probability.FiniteProbabilityVariationEmbedding
import PerronWright.Probability.CountableEmpiricalComponentMarks
import PerronWright.Probability.FiniteIrreducibleMarkedComponentProcess

/-! # Actual countable empirical-TV-marked window laws

Each atom is an actual connected component with its literal empirical
natural-type probability measure, in the proved total-variation metric.
Finite weak-marked windows push continuously to these true marked windows.
The entire empirical-normalized graph law, not a marginal proxy, supplies
the source probability. No marked convergence is assumed here.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical NNReal
open scoped PerronWright.ComponentWindowMarkedLaw
noncomputable section

namespace PerronWright.CountableComponentWindowLaw

open ComponentWindowPointMeasures EmpiricalTypeMarks
open FinitePointMeasureCompact FinitePointMeasureFintype FinitePointMeasureMarking
open CountableVariationMarks

abbrev MarkedWindow (a b : ℝ) (R : ℕ) := SurplusWindow a b R × VariationMark

def markedWindowPointMeasure {n : ℕ} (x : Fin n → ℕ) (G : SimpleGraph (Fin n))
    (a b : ℝ) (R : ℕ) : PointMeasure (MarkedWindow a b R) :=
  ofFintype (fun C : WindowComponent a b R 1 G ↦
    (windowAtom a b R 1 C, ofProbability (componentMark x C.val)))

theorem measurable_markedWindowPointMeasure {n : ℕ} (x : Fin n → ℕ)
    (a b : ℝ) (R : ℕ) :
    Measurable (fun G : SimpleGraph (Fin n) ↦ markedWindowPointMeasure x G a b R) :=
  measurable_of_countable _

theorem markedWindowPointMeasure_mass {n : ℕ} (x : Fin n → ℕ)
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) :
    mass (markedWindowPointMeasure x G a b R) = Fintype.card (WindowComponent a b R 1 G) :=
  mass_ofFintype _

theorem markedWindowPointMeasure_forget {n : ℕ} (x : Fin n → ℕ)
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) :
    mapPoint Prod.fst measurable_fst (markedWindowPointMeasure x G a b R) =
      windowPointMeasure a b R 1 G := by
  rw [markedWindowPointMeasure, mapPoint_ofFintype]
  rfl

section FiniteEmbedding

variable {S : Type*} [Fintype S] [MetricSpace S]
  [DiscreteTopology S] [MeasurableSpace S] [BorelSpace S]

def embedWindow (f : S → ℕ) (a b : ℝ) (R : ℕ) :
    ComponentWindowMarkedLaw.MarkedWindow S a b R → MarkedWindow a b R :=
  fun z ↦ (z.1, FiniteProbabilityVariationEmbedding.embed f z.2.val)

theorem continuous_embedWindow (f : S → ℕ) (a b : ℝ) (R : ℕ) :
    Continuous (embedWindow f a b R) :=
  continuous_fst.prodMk ((FiniteProbabilityVariationEmbedding.continuous_embed f).comp
    (WeakProbabilityMarks.continuous_val.comp continuous_snd))

def embedPointWindow (f : S → ℕ) (a b : ℝ) (R : ℕ) :
    PointMeasure (ComponentWindowMarkedLaw.MarkedWindow S a b R) →
      PointMeasure (MarkedWindow a b R) :=
  mapPoint (embedWindow f a b R) (continuous_embedWindow f a b R).measurable

theorem continuous_embedPointWindow (f : S → ℕ) (a b : ℝ) (R : ℕ) :
    Continuous (embedPointWindow f a b R) :=
  continuous_mapPoint _ (continuous_embedWindow f a b R)

theorem embedPointWindow_actual_marks {n : ℕ} (f : S → ℕ) (x : Fin n → S)
    (G : SimpleGraph (Fin n)) (a b : ℝ) (R : ℕ) :
    embedPointWindow f a b R (ComponentWindowMarkedLaw.markedWindowPointMeasure x G a b R) =
      markedWindowPointMeasure (fun v ↦ f (x v)) G a b R := by
  unfold embedPointWindow ComponentWindowMarkedLaw.markedWindowPointMeasure
    markedWindowPointMeasure
  rw [mapPoint_ofFintype]
  congr 1
  funext C
  dsimp only [Function.comp_apply, embedWindow, WeakProbabilityMarks.val_ofProbability]
  apply Prod.ext
  · rfl
  · change ofProbability ((componentMark x C.val).map
      (measurable_of_countable f).aemeasurable) = _
    rw [componentMark_map x C.val f (measurable_of_countable f)]

end FiniteEmbedding

end PerronWright.CountableComponentWindowLaw

namespace PerronWright.CountableKernel

open CountableComponentWindowLaw
open FinitePointMeasureCompact

def empiricalMarkedWindowLaw (M : CountableKernel) (level : ℕ → ℕ)
    (lambda a b : ℝ) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t) (n : ℕ) :
    ProbabilityMeasure (PointMeasure (MarkedWindow a b R)) :=
  ⟨(M.empiricalNormalizedGraphLaw level lambda hlower hlo n).map
    (fun G ↦ markedWindowPointMeasure
      (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) G a b R),
    Measure.isProbabilityMeasure_map (measurable_markedWindowPointMeasure _ a b R).aemeasurable⟩

theorem empiricalMarkedWindowLaw_integral (M : CountableKernel) (level : ℕ → ℕ)
    (lambda a b : ℝ) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t) (n : ℕ)
    {F : PointMeasure (MarkedWindow a b R) → ℝ} (hF : Measurable F) :
    (∫ η, F η ∂(M.empiricalMarkedWindowLaw level lambda a b R hlower hlo n : Measure _)) =
      ∫ G, F (markedWindowPointMeasure
        (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) G a b R)
        ∂M.empiricalNormalizedGraphLaw level lambda hlower hlo n := by
  unfold empiricalMarkedWindowLaw
  exact integral_map (measurable_markedWindowPointMeasure _ a b R).aemeasurable
    hF.aestronglyMeasurable

theorem empiricalMarkedWindowLaw_eq_finite_map (M : CountableKernel) (level : ℕ → ℕ)
    (hpos : ∀ n s, s ∈ Finset.range (level (n + 1) + 1) → 0 < M.empiricalWeights level n s)
    (lambda a b : ℝ) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t) (n : ℕ) :
    M.empiricalMarkedWindowLaw level lambda a b R hlower hlo n =
      (FiniteIrreducibleMarkedComponentProcess.markedWindowLaw
        (M.empiricalFiniteModel level hpos hlower hlo n) lambda a b R (n + 1)
        (M.empiricalVertexTypes level n)).map
          (continuous_embedPointWindow (fun s : Finset.range (level (n + 1) + 1) ↦ (s : ℕ))
            a b R).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [empiricalMarkedWindowLaw, ProbabilityMeasure.toMeasure_map,
    FiniteIrreducibleMarkedComponentProcess.markedWindowLaw_toMeasure]
  rw [Measure.map_map (continuous_embedPointWindow _ a b R).measurable
    (FiniteIrreducibleMarkedComponentProcess.measurable_markedWindowPointMeasure _ a b R)]
  rw [M.empiricalFiniteModel_graphLaw_eq level hpos lambda hlower hlo n]
  change (M.empiricalNormalizedGraphLaw level lambda hlower hlo n).map
    (fun G ↦ markedWindowPointMeasure
      (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) G a b R) =
    (M.empiricalNormalizedGraphLaw level lambda hlower hlo n).map _
  congr 1
  funext G
  exact (embedPointWindow_actual_marks (S := Finset.range (level (n + 1) + 1))
    (fun s ↦ (s : ℕ)) (M.empiricalVertexTypes level n) G a b R).symm

def empiricalUnnormalizedMarkedWindowLaw (M : CountableKernel) (level : ℕ → ℕ)
    (lambda a b : ℝ) (R n : ℕ) :
    ProbabilityMeasure (PointMeasure (MarkedWindow a b R)) :=
  ⟨(M.empiricalUnnormalizedGraphLaw level lambda n).map
    (fun G ↦ markedWindowPointMeasure
      (CountableTypeRealization.vertexTypes M (level (n + 1)) (n + 1)) G a b R),
    Measure.isProbabilityMeasure_map (measurable_markedWindowPointMeasure _ a b R).aemeasurable⟩

theorem empiricalUnnormalizedMarkedWindowLaw_eq_normalized (M : CountableKernel)
    (level : ℕ → ℕ) (lambda a b : ℝ) (R : ℕ)
    {lower : ℝ} (hlower : 0 < lower) (hlo : ∀ s t, lower ≤ M.kernel s t) (n : ℕ) :
    M.empiricalUnnormalizedMarkedWindowLaw level lambda a b R n =
      M.empiricalMarkedWindowLaw level
        (CriticalParameterDrift.effectiveParameter lambda
          (fun k ↦ M.empiricalSpectralRadius level (k - 1)) (n + 1)) a b R hlower hlo n := by
  apply ProbabilityMeasure.toMeasure_injective
  change (M.empiricalUnnormalizedGraphLaw level lambda n).map _ =
    (M.empiricalNormalizedGraphLaw level _ hlower hlo n).map _
  rw [M.empiricalUnnormalizedGraphLaw_eq_normalized level lambda hlower hlo n]

end PerronWright.CountableKernel
