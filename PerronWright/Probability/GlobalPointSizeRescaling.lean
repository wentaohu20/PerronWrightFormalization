import PerronWright.Probability.ProperLocalPointMap
import PerronWright.Probability.CompactGlobalPointLawLimit
import PerronWright.Probability.WindowSizeRescaling

/-!
# Literal global positive size rescaling and starred process laws

The ground-space dilation is an actual homeomorphism and hence proper.
Its continuous point-measure pushforward equals the literal rescaled
finite graph Dirac sum and source probability law. The proved full
unmarked global limit therefore transports to the actual starred global
law. Identification with the Aldous construction is not asserted here.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical

noncomputable section

namespace PerronWright.GlobalPointSizeRescaling

open ComponentGlobalPointProcess LocallyFinitePointMeasureVague
open ComponentPointProcesses CompactGlobalPointLawLimit ComponentWindowPointMeasures

def positiveSizeScale {c : ℝ} (hc : 0 < c) : PositiveSizeSurplus ≃ₜ PositiveSizeSurplus where
  toFun z := (⟨c * z.1.val, mul_pos hc z.1.property⟩, z.2)
  invFun z := (⟨z.1.val / c, div_pos z.1.property hc⟩, z.2)
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      dsimp only
      exact mul_div_cancel_left₀ z.1.val (ne_of_gt hc)
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      dsimp only
      exact mul_div_cancel₀ z.1.val (ne_of_gt hc)
    · rfl
  continuous_toFun :=
    ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk
      continuous_snd
  continuous_invFun :=
    (((continuous_subtype_val.comp continuous_fst).div_const c).subtype_mk _).prodMk
      continuous_snd

theorem positiveSizeScale_atom {c : ℝ} (hc : 0 < c) {n : ℕ}
    {G : SimpleGraph (Fin n)} (C : G.ConnectedComponent) :
    ambientEmbedding (positiveSizeScale hc (positiveAtom C)) = componentAtom c C := by
  simp [positiveSizeScale, ambientEmbedding, positiveAtom, componentAtom, ComponentPointProcesses.atom,
    mul_div_assoc]

def scalePoint {c : ℝ} (hc : 0 < c) :
    LocalPointMeasure PositiveSizeSurplus → LocalPointMeasure PositiveSizeSurplus :=
  ProperLocalPointMap.mapPoint (positiveSizeScale hc) (positiveSizeScale hc).isProperMap

theorem continuous_scalePoint {c : ℝ} (hc : 0 < c) : Continuous (scalePoint hc) :=
  ProperLocalPointMap.continuous_mapPoint _ _

/-- The actual global component Dirac sum with sizes multiplied by `c`. -/
def scaledProcess {c : ℝ} (hc : 0 < c) {n : ℕ} (G : SimpleGraph (Fin n)) :
    LocalPointMeasure PositiveSizeSurplus :=
  ofFintype (fun C : G.ConnectedComponent ↦ positiveSizeScale hc (positiveAtom C))

theorem scaledProcess_eq_map {c : ℝ} (hc : 0 < c) {n : ℕ} (G : SimpleGraph (Fin n)) :
    scaledProcess hc G = scalePoint hc (unmarkedProcess G) := by
  exact (ProperLocalPointMap.mapPoint_ofFintype _ _ (positiveAtom (G := G))).symm

theorem measurable_scaledProcess {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Measurable (scaledProcess hc : SimpleGraph (Fin n) → LocalPointMeasure PositiveSizeSurplus) := by
  have he : (scaledProcess hc : SimpleGraph (Fin n) → _) = scalePoint hc ∘ unmarkedProcess :=
    funext (scaledProcess_eq_map hc)
  rw [he]
  exact (continuous_scalePoint hc).measurable.comp (measurable_unmarkedProcess n)

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

def scaledProcessLaw (M : CompactBJRModel S) (lambda : ℝ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  ⟨(AnnealedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map (scaledProcess hc),
    Measure.isProbabilityMeasure_map (measurable_scaledProcess hc n).aemeasurable⟩

/-- Exact finite-size probability pushforward, including `n = 0`. -/
theorem scaledProcessLaw_eq_map (M : CompactBJRModel S) (lambda : ℝ)
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    scaledProcessLaw M lambda hc n = (unmarkedProcessLaw M lambda n).map
      (continuous_scalePoint hc).measurable.aemeasurable := by
  apply Subtype.ext
  change (AnnealedGraph.law M (CriticalScaling.time lambda n)
    (CriticalScaling.time_nonneg lambda n) n).map (scaledProcess hc) =
      ((AnnealedGraph.law M (CriticalScaling.time lambda n)
        (CriticalScaling.time_nonneg lambda n) n).map unmarkedProcess).map (scalePoint hc)
  rw [Measure.map_map (continuous_scalePoint hc).measurable (measurable_unmarkedProcess n)]
  congr 1
  exact funext (scaledProcess_eq_map hc)

theorem exists_unique_scaledProcessLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      Tendsto (scaledProcessLaw M lambda hc) atTop (𝓝 ν) := by
  let ν := (unmarkedProcessLimitLaw M hM hQP lambda).map
    (continuous_scalePoint hc).measurable.aemeasurable
  have hν : Tendsto (scaledProcessLaw M lambda hc) atTop (𝓝 ν) := by
    change Tendsto (fun n ↦ scaledProcessLaw M lambda hc n) atTop (𝓝 ν)
    simpa only [scaledProcessLaw_eq_map, ν] using
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (unmarkedProcessLaw M lambda) (unmarkedProcessLimitLaw M hM hQP lambda)
        (tendsto_unmarkedProcessLimitLaw M hM hQP lambda) (continuous_scalePoint hc)
  exact ⟨ν, hν, fun θ hθ ↦ tendsto_nhds_unique hθ hν⟩

def starredProcessLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ) :
    ℕ → ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus) :=
  scaledProcessLaw M lambda (sizeScale_pos M hM)

/-- Actual full-sequence starred global weak convergence, with the
paper's literal `beta^(1/3)` size normalization. -/
theorem exists_unique_starredProcessLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus),
      Tendsto (starredProcessLaw M hM lambda) atTop (𝓝 ν) :=
  exists_unique_scaledProcessLaw_limit M hM hQP lambda (sizeScale_pos M hM)

end PerronWright.GlobalPointSizeRescaling
