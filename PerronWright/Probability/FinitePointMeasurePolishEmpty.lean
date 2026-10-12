import PerronWright.Probability.FinitePointMeasurePolish

/-! # Genuine compact integer point-measure Polishness, including empty ground spaces -/

open MeasureTheory Topology
open scoped Classical

noncomputable section

namespace PerronWright.FinitePointMeasurePolishEmpty

open FinitePointMeasureCompact

theorem pointMeasure_polishSpace {E : Type*} [MeasurableSpace E] [MetricSpace E]
    [CompactSpace E] [BorelSpace E] : PolishSpace (PointMeasure E) := by
  rcases isEmpty_or_nonempty E with hE | hE
  · let : IsEmpty E := hE
    let : Subsingleton (FiniteMeasure E) :=
      ⟨fun μ ν ↦ FiniteMeasure.toMeasure_injective (Subsingleton.elim _ _)⟩
    let : Subsingleton (PointMeasure E) :=
      inferInstanceAs (Subsingleton {μ : FiniteMeasure E // IsPointMeasure μ})
    let : Unique (PointMeasure E) :=
      { default := ofAtomsPoint (fun i : Fin 0 ↦ Fin.elim0 i)
        uniq := fun _ ↦ Subsingleton.elim _ _ }
    let e : PointMeasure E ≃ₜ PUnit.{1} :=
      { toEquiv := Equiv.ofUnique _ _
        continuous_toFun := continuous_const
        continuous_invFun := continuous_const }
    exact e.isClosedEmbedding.polishSpace
  · let : Nonempty E := hE
    exact FinitePointMeasurePolish.pointMeasure_polishSpace

end PerronWright.FinitePointMeasurePolishEmpty
