import PerronWright.Enumeration.TreeCoefficientProfile
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
The type-resolved coefficients of the actual finite rooted-tree EGF
are continuous functions on the compact type space.
-/

open MeasureTheory
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem CompactBJRModel.rootGraphSlice_continuous
    (M : CompactBJRModel S) (g : C(S, ℝ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) :
    Continuous (fun x : S => ∫ z : Fin n → S,
      M.fieldGraphWeightIntegrand g H (Fin.insertNth 0 x z)
        ∂Measure.pi (fun _ : Fin n => M.mu)) := by
  have hcons : Continuous
      (fun p : S × (Fin n → S) =>
        (Fin.cons (α := fun _ => S) p.1 p.2 : Fin (n + 1) → S)) := by
    apply continuous_pi
    intro i
    cases i using Fin.cases with
    | zero => simpa using (continuous_fst : Continuous (fun p : S × (Fin n → S) => p.1))
    | succ j =>
        change Continuous (fun p : S × (Fin n → S) => p.2 j)
        exact (continuous_apply j).comp (continuous_snd :
          Continuous (fun p : S × (Fin n → S) => p.2))
  have hins : Continuous
      (fun p : S × (Fin n → S) =>
        (Fin.insertNth (α := fun _ => S) 0 p.1 p.2 : Fin (n + 1) → S)) := by
    simpa only [Fin.insertNth_zero'] using hcons
  have hjoint : Continuous
      (fun p : S × (Fin n → S) =>
        M.fieldGraphWeightIntegrand g H (Fin.insertNth 0 p.1 p.2)) :=
    (M.fieldGraphWeightIntegrand_continuous g H).comp hins
  have hc := continuous_parametric_integral_of_continuous
    (μ := Measure.pi (fun _ : Fin n => M.mu))
    (f := fun x : S => fun z : Fin n → S =>
      M.fieldGraphWeightIntegrand g H (Fin.insertNth 0 x z))
    hjoint isCompact_univ
  simpa only [setIntegral_univ] using hc

theorem CompactBJRModel.rootedTreeCoefficient_continuous
    (M : CompactBJRModel S) (n : ℕ) :
    Continuous (M.rootedTreeCoefficient n) := by
  have hnum : Continuous (M.rootedTreeNumerator n) := by
    unfold CompactBJRModel.rootedTreeNumerator
    apply continuous_finsetSum
    intro H _
    split
    · exact M.rootGraphSlice_continuous 0 H
    · exact continuous_const
  exact hnum.div_const _

/-- The type-resolved finite rooted-tree coefficient as a continuous map. -/
def CompactBJRModel.rootedTreeCoefficientMap
    (M : CompactBJRModel S) (n : ℕ) : C(S, ℝ) :=
  ⟨M.rootedTreeCoefficient n, M.rootedTreeCoefficient_continuous n⟩

@[simp] theorem CompactBJRModel.rootedTreeCoefficientMap_apply
    (M : CompactBJRModel S) (n : ℕ) (x : S) :
    M.rootedTreeCoefficientMap n x = M.rootedTreeCoefficient n x := rfl

end PerronWright
