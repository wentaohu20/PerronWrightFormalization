import PerronWright.Probability.ComponentPointProcesses

/-!
# The paper's starred process normalization

Only the size coordinate is multiplied by `beta^(1/3)`; surplus and the
actual empirical probability mark are unchanged.  These definitions use
the graph law already constructed, rather than postulating a process law.
-/

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.ComponentPointProcesses

open ComponentCounts EmpiricalTypeMarks AnnealedGraph

def sizeRescale (c : ℝ) (z : ℝ × ℕ) : ℝ × ℕ := (c * z.1, z.2)

theorem sizeRescale_measurable (c : ℝ) : Measurable (sizeRescale c) :=
  (measurable_const.mul measurable_fst).prodMk measurable_snd

variable {S : Type*} [MeasurableSpace S]

def markedSizeRescale (c : ℝ) (z : (ℝ × ℕ) × ProbabilityMeasure S) :
    (ℝ × ℕ) × ProbabilityMeasure S := (sizeRescale c z.1, z.2)

theorem markedSizeRescale_measurable (c : ℝ) :
    Measurable (markedSizeRescale (S := S) c) :=
  ((sizeRescale_measurable c).comp measurable_fst).prodMk measurable_snd

variable [MetricSpace S] [CompactSpace S] [BorelSpace S]

/-- The positive size scale in the main probabilistic theorem. -/
def sizeScale (M : CompactBJRModel S) (hM : M.IsRegularCritical) : ℝ :=
  M.beta hM ^ (1 / 3 : ℝ)

theorem sizeScale_pos (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    0 < sizeScale M hM := Real.rpow_pos_of_pos (M.beta_pos hM) _

/-- The literal Aldous critical-window parameter, without a convergence
or Brownian-density identification assertion. -/
def aldousParameter (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda : ℝ) : ℝ := M.alpha hM * M.beta hM ^ (-2 / 3 : ℝ) * lambda

/-- The starred finite unmarked measure in the paper. -/
def unmarkedStar (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (G : SimpleGraph (Fin n)) : Measure (ℝ × ℕ) :=
  (unmarked G).map (sizeRescale (sizeScale M hM))

/-- The starred finite measure with the genuine empirical type marks. -/
def markedStar (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → S) :
    Measure ((ℝ × ℕ) × ProbabilityMeasure S) :=
  (marked G x).map (markedSizeRescale (sizeScale M hM))

theorem unmarkedStar_eq_sum (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    unmarkedStar M hM G = ∑ C : G.ConnectedComponent,
      Measure.dirac (sizeScale M hM * (componentSize C : ℝ) /
        (n : ℝ) ^ (2 / 3 : ℝ), componentSurplus C) := by
  unfold unmarkedStar unmarked
  rw [Measure.map_finset_sum' (sizeRescale_measurable _).aemeasurable]
  simp only [Measure.map_dirac' (sizeRescale_measurable _), sizeRescale, atom,
    mul_div_assoc]

theorem markedStar_eq_sum (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → S) :
    markedStar M hM G x = ∑ C : G.ConnectedComponent,
      Measure.dirac ((sizeScale M hM * (componentSize C : ℝ) /
        (n : ℝ) ^ (2 / 3 : ℝ), componentSurplus C), componentMark x C) := by
  unfold markedStar marked
  rw [Measure.map_finset_sum' (markedSizeRescale_measurable _).aemeasurable]
  simp only [Measure.map_dirac' (markedSizeRescale_measurable _),
    markedSizeRescale, sizeRescale, markedAtom, atom, mul_div_assoc]

def unmarkedStarLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda : ℝ) (n : ℕ) : Measure (Measure (ℝ × ℕ)) :=
  (unmarkedLaw M lambda n).map (Measure.map (sizeRescale (sizeScale M hM)))

def markedStarLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda : ℝ) (n : ℕ) : Measure (Measure ((ℝ × ℕ) × ProbabilityMeasure S)) :=
  (markedLaw M lambda n).map (Measure.map (markedSizeRescale (sizeScale M hM)))

instance unmarkedStarLaw_isProbability (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda : ℝ) (n : ℕ) : IsProbabilityMeasure (unmarkedStarLaw M hM lambda n) :=
  Measure.isProbabilityMeasure_map
    (Measure.measurable_map _ (sizeRescale_measurable _)).aemeasurable

instance markedStarLaw_isProbability (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (lambda : ℝ) (n : ℕ) : IsProbabilityMeasure (markedStarLaw M hM lambda n) :=
  Measure.isProbabilityMeasure_map
    (Measure.measurable_map _ (markedSizeRescale_measurable _)).aemeasurable

end PerronWright.ComponentPointProcesses
