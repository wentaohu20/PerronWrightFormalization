import PerronWright.Probability.FinitePointMeasurePolish

/-! # Literal probability-measure marks with their actual weak Borel space

The wrapper only chooses the Borel sigma algebra of the genuine weak
topology. Its values are literal ProbabilityMeasure values and the
projection is a homeomorphism. No Giry/weak Borel equality is assumed.
-/

open MeasureTheory Topology
open scoped Topology

noncomputable section

namespace PerronWright.WeakProbabilityMarks

structure WeakMark (S : Type*) [MeasurableSpace S] where
  val : ProbabilityMeasure S

variable {S : Type*} [MeasurableSpace S] [MetricSpace S] [CompactSpace S] [BorelSpace S]

instance : TopologicalSpace (WeakMark S) :=
  TopologicalSpace.induced WeakMark.val inferInstance

def ofProbability (ν : ProbabilityMeasure S) : WeakMark S := ⟨ν⟩

def homeomorph : WeakMark S ≃ₜ ProbabilityMeasure S where
  toFun := WeakMark.val
  invFun := ofProbability
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.mpr continuous_id

instance : TopologicalSpace.MetrizableSpace (WeakMark S) := homeomorph.isEmbedding.metrizableSpace

instance : MetricSpace (WeakMark S) := TopologicalSpace.metrizableSpaceMetric (WeakMark S)

instance : CompactSpace (WeakMark S) := homeomorph.symm.compactSpace

instance : MeasurableSpace (WeakMark S) := borel (WeakMark S)

instance : BorelSpace (WeakMark S) := ⟨rfl⟩

instance : PolishSpace (WeakMark S) := by infer_instance

instance : StandardBorelSpace (WeakMark S) := by infer_instance

omit [CompactSpace S] in
theorem continuous_val : Continuous (WeakMark.val : WeakMark S → ProbabilityMeasure S) :=
  homeomorph.continuous_toFun

omit [CompactSpace S] in
theorem continuous_ofProbability : Continuous (ofProbability : ProbabilityMeasure S → WeakMark S) :=
  homeomorph.continuous_invFun

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
@[simp] theorem val_ofProbability (ν : ProbabilityMeasure S) : (ofProbability ν).val = ν := rfl

omit [MetricSpace S] [CompactSpace S] [BorelSpace S] in
@[simp] theorem ofProbability_val (ν : WeakMark S) : ofProbability ν.val = ν := rfl

end PerronWright.WeakProbabilityMarks
