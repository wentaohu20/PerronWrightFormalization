import PerronWright.Probability.CompactGlobalMarkedPointLawLimit
import PerronWright.Probability.GlobalPointSizeRescaling

/-! # Literal global empirical-marked positive size rescaling and starred laws

The actual positive-size homeomorphism acts only on size, leaving the
actual component empirical probability mark unchanged. Its genuine
proper point-measure pushforward equals the literal scaled component
Dirac sum. Canonical Perron marking commutes with this map as an actual
measure identity. Whole marked-law convergence therefore transports to
the literal `beta^(1/3)` starred source. Brownian identification is not
asserted.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GlobalMarkedPointSizeRescaling

open ComponentGlobalPointProcess ComponentGlobalMarkedProcess LocallyFinitePointMeasureVague
open WeakProbabilityMarks GlobalPointMeasureMarking GlobalPointSizeRescaling
open CompactGlobalPointLawLimit CompactGlobalMarkedPointLawLimit
open ComponentWindowMarkedLaw ComponentWindowMarkedTransfer ComponentWindowPointMeasures
open EmpiricalTypeMarks ComponentPointProcesses

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

def markedSizeScale {c : ℝ} (hc : 0 < c) :
    MarkedPositiveSizeSurplus S ≃ₜ MarkedPositiveSizeSurplus S :=
  (positiveSizeScale hc).prodCongr (Homeomorph.refl (WeakMark S))

omit [CompactSpace S] in
@[simp] theorem markedSizeScale_apply {c : ℝ} (hc : 0 < c)
    (z : MarkedPositiveSizeSurplus S) : markedSizeScale hc z = (positiveSizeScale hc z.1, z.2) := rfl

omit [CompactSpace S] in
theorem markedSizeScale_atom_size {c : ℝ} (hc : 0 < c) {n : ℕ}
    (x : Fin n → S) {G : SimpleGraph (Fin n)} (C : G.ConnectedComponent) :
    ambientEmbedding (markedSizeScale hc (positiveMarkedAtom x C)).1 = componentAtom c C :=
  positiveSizeScale_atom hc C

omit [CompactSpace S] in
@[simp] theorem markedSizeScale_atom_mark {c : ℝ} (hc : 0 < c) {n : ℕ}
    (x : Fin n → S) {G : SimpleGraph (Fin n)} (C : G.ConnectedComponent) :
    (markedSizeScale hc (positiveMarkedAtom x C)).2.val = componentMark x C := rfl

def scaleMarkedPoint {c : ℝ} (hc : 0 < c) :
    LocalPointMeasure (MarkedPositiveSizeSurplus S) →
      LocalPointMeasure (MarkedPositiveSizeSurplus S) :=
  ProperLocalPointMap.mapPoint (markedSizeScale hc) (markedSizeScale hc).isProperMap

theorem continuous_scaleMarkedPoint {c : ℝ} (hc : 0 < c) :
    Continuous (scaleMarkedPoint (S := S) hc) := ProperLocalPointMap.continuous_mapPoint _ _

@[simp] theorem scaleMarkedPoint_toMeasure {c : ℝ} (hc : 0 < c)
    (η : LocalPointMeasure (MarkedPositiveSizeSurplus S)) :
    (scaleMarkedPoint hc η : Measure (MarkedPositiveSizeSurplus S)) =
      (η : Measure (MarkedPositiveSizeSurplus S)).map (markedSizeScale hc) := rfl

/-- Literal scaled finite component sum with the actual empirical mark. -/
def scaledMarkedProcess {c : ℝ} (hc : 0 < c) {n : ℕ}
    (x : Fin n → S) (G : SimpleGraph (Fin n)) :
    LocalPointMeasure (MarkedPositiveSizeSurplus S) :=
  ofFintype (fun C : G.ConnectedComponent ↦ markedSizeScale hc (positiveMarkedAtom x C))

@[simp] theorem scaledMarkedProcess_toMeasure {c : ℝ} (hc : 0 < c) {n : ℕ}
    (x : Fin n → S) (G : SimpleGraph (Fin n)) :
    (scaledMarkedProcess hc x G : Measure (MarkedPositiveSizeSurplus S)) =
      ∑ C : G.ConnectedComponent, Measure.dirac (markedSizeScale hc (positiveMarkedAtom x C)) := rfl

theorem scaledMarkedProcess_eq_map {c : ℝ} (hc : 0 < c) {n : ℕ}
    (x : Fin n → S) (G : SimpleGraph (Fin n)) :
    scaledMarkedProcess hc x G = scaleMarkedPoint hc (markedProcess x G) :=
  (ProperLocalPointMap.mapPoint_ofFintype _ _ (positiveMarkedAtom x (G := G))).symm

theorem measurable_scaledMarkedProcess {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Measurable (fun p : AnnealedTypedGraph.State S n ↦
      scaledMarkedProcess hc p.1 (AnnealedTypedGraph.graph p)) := by
  have he : (fun p : AnnealedTypedGraph.State S n ↦
      scaledMarkedProcess hc p.1 (AnnealedTypedGraph.graph p)) =
      scaleMarkedPoint hc ∘ (fun p ↦ markedProcess p.1 (AnnealedTypedGraph.graph p)) :=
    funext (fun p ↦ scaledMarkedProcess_eq_map hc p.1 (AnnealedTypedGraph.graph p))
  rw [he]
  exact (continuous_scaleMarkedPoint hc).measurable.comp (measurable_markedProcess n)

def scaledMarkedProcessLaw (M : CompactBJRModel S) (lambda : ℝ) {c : ℝ}
    (hc : 0 < c) (n : ℕ) : ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  (typedProbability M lambda n).map (measurable_scaledMarkedProcess hc n).aemeasurable

/-- Exact all-size typed graph-law pushforward, including `n = 0`. -/
theorem scaledMarkedProcessLaw_eq_map (M : CompactBJRModel S) (lambda : ℝ)
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    scaledMarkedProcessLaw M lambda hc n = (markedProcessLaw M lambda n).map
      (continuous_scaleMarkedPoint hc).measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [scaledMarkedProcessLaw, markedProcessLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_scaleMarkedPoint hc).measurable (measurable_markedProcess n)]
  congr 1
  exact funext (fun p ↦ scaledMarkedProcess_eq_map hc p.1 (AnnealedTypedGraph.graph p))

/-- The size map and the literal constant probability mark commute. -/
theorem scaleMarkedPoint_constantMark {c : ℝ} (hc : 0 < c) (p : WeakMark S)
    (η : LocalPointMeasure PositiveSizeSurplus) :
    scaleMarkedPoint hc (constantMark p η) = constantMark p (scalePoint hc η) := by
  apply Subtype.ext
  change ((η : Measure PositiveSizeSurplus).map (attachMark p)).map (markedSizeScale hc) =
    ((η : Measure PositiveSizeSurplus).map (positiveSizeScale hc)).map (attachMark p)
  rw [Measure.map_map (markedSizeScale hc).continuous.measurable (continuous_attachMark p).measurable,
    Measure.map_map (continuous_attachMark p).measurable (positiveSizeScale hc).continuous.measurable]
  rfl

theorem canonicalGlobalMarkedLaw_scale (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {c : ℝ} (hc : 0 < c) (μ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus)) :
    (canonicalGlobalMarkedLaw M hM μ).map (continuous_scaleMarkedPoint hc).measurable.aemeasurable =
      canonicalGlobalMarkedLaw M hM (μ.map (continuous_scalePoint hc).measurable.aemeasurable) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [canonicalGlobalMarkedLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_scaleMarkedPoint hc).measurable
      (continuous_constantMark (perronWeakMark M hM)).measurable,
    Measure.map_map (continuous_constantMark (perronWeakMark M hM)).measurable
      (continuous_scalePoint hc).measurable]
  congr 1
  exact funext (scaleMarkedPoint_constantMark hc (perronWeakMark M hM))

def scaledCanonicalMarkedLimitLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (hQP : M.QP) (lambda : ℝ) {c : ℝ} (hc : 0 < c) :
    ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  canonicalGlobalMarkedLaw M hM ((unmarkedProcessLimitLaw M hM hQP lambda).map
    (continuous_scalePoint hc).measurable.aemeasurable)

theorem tendsto_scaledMarkedProcessLaw_canonical (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (scaledMarkedProcessLaw M lambda hc) atTop
      (𝓝 (scaledCanonicalMarkedLimitLaw M hM hQP lambda hc)) := by
  change Tendsto (fun n ↦ scaledMarkedProcessLaw M lambda hc n) atTop
    (𝓝 (scaledCanonicalMarkedLimitLaw M hM hQP lambda hc))
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (markedProcessLaw M lambda) (canonicalGlobalMarkedLimitLaw M hM hQP lambda)
    (tendsto_markedProcessLaw_canonical M hM hQP lambda) (continuous_scaleMarkedPoint hc)
  simpa only [scaledMarkedProcessLaw_eq_map, canonicalGlobalMarkedLimitLaw,
    canonicalGlobalMarkedLaw_scale, scaledCanonicalMarkedLimitLaw] using h

theorem exists_unique_scaledMarkedProcessLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)),
      Tendsto (scaledMarkedProcessLaw M lambda hc) atTop (𝓝 ν) :=
  ⟨scaledCanonicalMarkedLimitLaw M hM hQP lambda hc,
    tendsto_scaledMarkedProcessLaw_canonical M hM hQP lambda hc,
    fun _θ hθ ↦ tendsto_nhds_unique hθ (tendsto_scaledMarkedProcessLaw_canonical M hM hQP lambda hc)⟩

def starredMarkedProcessLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical) (lambda : ℝ) :
    ℕ → ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  scaledMarkedProcessLaw M lambda (sizeScale_pos M hM)

def starredCanonicalMarkedLimitLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (hQP : M.QP) (lambda : ℝ) : ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  scaledCanonicalMarkedLimitLaw M hM hQP lambda (sizeScale_pos M hM)

/-- Whole actual starred empirical-marked source laws converge to
the actual Perron marking of the actual starred unmarked limit. -/
theorem tendsto_starredMarkedProcessLaw_canonical (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    Tendsto (starredMarkedProcessLaw M hM lambda) atTop
      (𝓝 (starredCanonicalMarkedLimitLaw M hM hQP lambda)) :=
  tendsto_scaledMarkedProcessLaw_canonical M hM hQP lambda (sizeScale_pos M hM)

theorem exists_unique_starredMarkedProcessLaw_limit (M : CompactBJRModel S)
    (hM : M.IsRegularCritical) (hQP : M.QP) (lambda : ℝ) :
    ∃! ν : ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)),
      Tendsto (starredMarkedProcessLaw M hM lambda) atTop (𝓝 ν) :=
  exists_unique_scaledMarkedProcessLaw_limit M hM hQP lambda (sizeScale_pos M hM)

/-- The exact ambient finite Dirac sum is the paper's already-defined
starred graph measure, with the same literal empirical probability marks.
This does not identify the Giry sigma algebra with the weak Borel sigma. -/
theorem starredMarked_atoms_eq_paper (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    {n : ℕ} (x : Fin n → S) (G : SimpleGraph (Fin n)) :
    (∑ C : G.ConnectedComponent,
      Measure.dirac (ambientEmbedding (markedSizeScale (sizeScale_pos M hM)
        (positiveMarkedAtom x C)).1,
        (markedSizeScale (sizeScale_pos M hM) (positiveMarkedAtom x C)).2.val)) =
      markedStar M hM G x := by
  rw [markedStar_eq_sum]
  apply Finset.sum_congr rfl
  intro C _
  rw [markedSizeScale_atom_size, markedSizeScale_atom_mark]
  simp only [componentAtom, mul_div_assoc]

end PerronWright.GlobalMarkedPointSizeRescaling
