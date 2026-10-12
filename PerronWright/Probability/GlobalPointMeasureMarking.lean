import PerronWright.Probability.ProperLocalPointMap
import PerronWright.Probability.ComponentGlobalMarkedProcess
import PerronWright.Probability.CompactGlobalPointLawLimit
import PerronWright.Probability.ComponentWindowMarkedConvergence

/-!
# Actual canonical Perron marking of global point measures

The literal constant-mark embedding is proved proper by its actual
closed range. The genuine measure pushforward therefore defines a
vague-continuous integer point-measure map. Its Perron mark is the actual
Perron probability measure and its limiting law is the actual unmarked
global law pushed forward by this proved map.
-/

open MeasureTheory Filter Topology
open scoped BigOperators Classical CompactlySupported
open scoped PerronWright.ComponentWindowMarkedLaw

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PerronWright.GlobalPointMeasureMarking

open ComponentGlobalPointProcess ComponentGlobalMarkedProcess LocallyFinitePointMeasureVague
open WeakProbabilityMarks CompactGlobalPointLawLimit ComponentWindowMarkedTransfer
open ComponentWindowPointMeasures ComponentWindowMarkedLaw

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

def attachMark (p : WeakMark S) : PositiveSizeSurplus → MarkedPositiveSizeSurplus S :=
  fun z ↦ (z, p)

omit [CompactSpace S] in
theorem continuous_attachMark (p : WeakMark S) : Continuous (attachMark p) :=
  continuous_id.prodMk continuous_const

theorem isProperMap_attachMark (p : WeakMark S) : IsProperMap (attachMark p) := by
  have hr : Set.range (attachMark p) = Prod.snd ⁻¹' {p} := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      rfl
    · intro hz
      exact ⟨z.1, Prod.ext rfl (Set.mem_singleton_iff.mp hz).symm⟩
  apply IsClosedEmbedding.isProperMap
  refine ⟨isEmbedding_prodMkLeft p, ?_⟩
  rw [hr]
  exact isClosed_singleton.preimage continuous_snd

def constantMark (p : WeakMark S) : LocalPointMeasure PositiveSizeSurplus →
    LocalPointMeasure (MarkedPositiveSizeSurplus S) :=
  ProperLocalPointMap.mapPoint (attachMark p) (isProperMap_attachMark p)

theorem continuous_constantMark (p : WeakMark S) : Continuous (constantMark p) :=
  ProperLocalPointMap.continuous_mapPoint (attachMark p) (isProperMap_attachMark p)

@[simp] theorem constantMark_toMeasure (p : WeakMark S)
    (η : LocalPointMeasure PositiveSizeSurplus) :
    (constantMark p η : Measure (MarkedPositiveSizeSurplus S)) =
      (η : Measure PositiveSizeSurplus).map (attachMark p) := rfl

theorem constantMark_integral (p : WeakMark S) (η : LocalPointMeasure PositiveSizeSurplus)
    (f : C_c(MarkedPositiveSizeSurplus S, ℝ)) :
    (∫ z, f z ∂(constantMark p η : Measure (MarkedPositiveSizeSurplus S))) =
      ∫ z, ProperLocalPointMap.pullbackTest (attachMark p) (isProperMap_attachMark p) f z
        ∂(η : Measure PositiveSizeSurplus) :=
  ProperLocalPointMap.mapPoint_integral _ _ _ _

theorem constantMark_ofFintype (p : WeakMark S) {I : Type*} [Fintype I]
    (x : I → PositiveSizeSurplus) :
    constantMark p (LocallyFinitePointMeasureVague.ofFintype x) =
      LocallyFinitePointMeasureVague.ofFintype (fun i ↦ (x i, p)) :=
  ProperLocalPointMap.mapPoint_ofFintype _ _ _

def canonicalGlobalMarkedLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (μ : ProbabilityMeasure (LocalPointMeasure PositiveSizeSurplus)) :
    ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  μ.map (continuous_constantMark (perronWeakMark M hM)).measurable.aemeasurable

theorem continuous_canonicalGlobalMarkedLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical) :
    Continuous (canonicalGlobalMarkedLaw M hM) :=
  ProbabilityMeasure.continuous_map (continuous_constantMark (perronWeakMark M hM))

def canonicalGlobalMarkedLimitLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (hQP : M.QP) (lambda : ℝ) :
    ProbabilityMeasure (LocalPointMeasure (MarkedPositiveSizeSurplus S)) :=
  canonicalGlobalMarkedLaw M hM (unmarkedProcessLimitLaw M hM hQP lambda)

theorem tendsto_canonicalGlobalMarkedLaw (M : CompactBJRModel S) (hM : M.IsRegularCritical)
    (hQP : M.QP) (lambda : ℝ) :
    Tendsto (fun n ↦ canonicalGlobalMarkedLaw M hM (unmarkedProcessLaw M lambda n))
      atTop (𝓝 (canonicalGlobalMarkedLimitLaw M hM hQP lambda)) :=
  (continuous_canonicalGlobalMarkedLaw M hM).tendsto _ |>.comp
    (tendsto_unmarkedProcessLimitLaw M hM hQP lambda)

/-- Exact window bridge for the true constant-marked global graph
measure, using the same actual component atoms as the empirical law. -/
theorem constantMark_process_integral_eq_window (p : WeakMark S)
    (a b : ℝ) (R : ℕ) (ha : 0 < a) {n : ℕ} (G : SimpleGraph (Fin n))
    (f : C_c(MarkedPositiveSizeSurplus S, ℝ)) (hf : tsupport f ⊆ markedWindowSet a b R) :
    (∫ z, f z ∂(constantMark p (unmarkedProcess G) : Measure (MarkedPositiveSizeSurplus S))) =
      ∫ z, f (markedPositiveWindowEmbedding a b R ha z)
        ∂((FinitePointMeasureMarking.constantMark p (windowPointMeasure a b R 1 G) :
          FiniteMeasure (MarkedWindow S a b R)) : Measure (MarkedWindow S a b R)) := by
  rw [unmarkedProcess, constantMark_ofFintype, LocallyFinitePointMeasureVague.ofFintype_integral,
    windowPointMeasure, FinitePointMeasureMarking.constantMark,
    FinitePointMeasureMarking.mapPoint_ofFintype, FinitePointMeasureFintype.ofFintype_integral]
  simp only [Function.comp_apply, markedPositiveWindowEmbedding, positiveWindowEmbedding_windowAtom]
  apply Finset.sum_congr_set {C : G.ConnectedComponent |
    componentAtom 1 C ∈ windowSet a b R}
    (fun C ↦ f (positiveAtom C, p))
    (fun C : WindowComponent a b R 1 G ↦ f (positiveAtom C.val, p))
  · intro C _
    rfl
  · intro C hC
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    apply hC
    simpa [markedWindowSet, positiveWindowSet, componentAtom, ComponentPointProcesses.atom,
      positiveAtom, ambientEmbedding] using hf hs

end PerronWright.GlobalPointMeasureMarking
