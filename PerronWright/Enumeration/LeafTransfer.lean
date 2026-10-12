import PerronWright.Enumeration.LeafIntegration
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace PerronWright.GraphCore

open MeasureTheory

/-- Away from the inserted coordinate, the two insertion functions agree
even when their inserted values differ. -/
theorem insertNth_apply_independent {S : Type*} {n : ℕ}
    {v i : Fin (n + 1)} (hi : i ≠ v)
    (y y' : S) (z : Fin n → S) :
    (Fin.insertNth v y z : Fin (n + 1) → S) i =
      (Fin.insertNth v y' z : Fin (n + 1) → S) i := by
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
  simp only [Fin.insertNth_apply_succAbove]

open scoped Classical in
/-- The complete residual vertex/edge factor after deleting a leaf is
independent of the type assigned to that deleted vertex. -/
theorem leaf_residual_independent
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1))
    (y y' : S) (z : Fin n → S) :
    ((∏ i ∈ (Finset.univ.erase v),
        Real.exp (-t * M.degreeFunction
          ((Fin.insertNth v y z : Fin (n + 1) → S) i))) *
      (∏ e ∈ (H.deleteIncidenceSet v).edgeFinset,
        M.edgeFactor t (Fin.insertNth v y z) e)) =
    ((∏ i ∈ (Finset.univ.erase v),
        Real.exp (-t * M.degreeFunction
          ((Fin.insertNth v y' z : Fin (n + 1) → S) i))) *
      (∏ e ∈ (H.deleteIncidenceSet v).edgeFinset,
        M.edgeFactor t (Fin.insertNth v y' z) e)) := by
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [insertNth_apply_independent (Finset.mem_erase.mp hi).1 y y' z]
  · apply Finset.prod_congr rfl
    intro e he
    induction e using Sym2.inductionOn with
    | _ i j =>
        have hnot : v ∉ s(i,j) := by
          rw [H.edgeFinset_deleteIncidenceSet_eq_filter] at he
          exact (Finset.mem_filter.mp he).2
        have hi : i ≠ v := by
          intro h
          subst i
          exact hnot (Sym2.mem_mk_left v j)
        have hj : j ≠ v := by
          intro h
          subst j
          exact hnot (Sym2.mem_mk_right i v)
        simp only [CompactBJRModel.edgeFactor_mk]
        rw [insertNth_apply_independent hi y y' z,
          insertNth_apply_independent hj y y' z]

/-- The actual graph weight also admits Fubini in the order in which the
leaf type is integrated first. -/
theorem graphWeight_fubini_survivors_first
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    M.graphWeight t H =
      ∫ z : Fin n → S, ∫ y : S,
        M.graphWeightIntegrand t H (Fin.insertNth v y z)
          ∂M.mu ∂Measure.pi (fun _ : Fin n => M.mu) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S) v
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => M.mu))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => M.mu) v
  have hf := M.graphWeightIntegrand_integrable t H
  have hprod : Integrable
      (fun p : S × (Fin n → S) => M.graphWeightIntegrand t H (e.symm p))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  calc
    M.graphWeight t H = ∫ y : S, ∫ z : Fin n → S,
        M.graphWeightIntegrand t H (Fin.insertNth v y z)
          ∂Measure.pi (fun _ : Fin n => M.mu) ∂M.mu :=
      graphWeight_fubini_at_vertex M t H v
    _ = ∫ z : Fin n → S, ∫ y : S,
        M.graphWeightIntegrand t H (Fin.insertNth v y z)
          ∂M.mu ∂Measure.pi (fun _ : Fin n => M.mu) := by
      exact integral_integral_swap hprod

/-- The actual one-leaf response of the compact-type model. -/
def leafResponse
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) (a : S) : ℝ :=
  ∫ y : S, Real.exp (-t * M.degreeFunction y) *
    (t * M.kernel y a) ∂M.mu

open scoped Classical in
/-- Integrate the leaf type completely: the response at its neighbor is
multiplied by the exact residual vertex/edge weight on the survivors. -/
theorem graphWeight_leaf_transfer
    {S : Type*} [MetricSpace S] [CompactSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (M : CompactBJRModel S) (t : ℝ) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) {v w : Fin (n + 1)}
    (hv : H.degree v = 1) (hvw : H.Adj v w) (y₀ : S) :
    M.graphWeight t H =
      ∫ z : Fin n → S,
        leafResponse M t ((Fin.insertNth v y₀ z : Fin (n + 1) → S) w) *
          ((∏ i ∈ Finset.univ.erase v,
              Real.exp (-t * M.degreeFunction
                ((Fin.insertNth v y₀ z : Fin (n + 1) → S) i))) *
            (∏ e ∈ (H.deleteIncidenceSet v).edgeFinset,
              M.edgeFactor t (Fin.insertNth v y₀ z) e))
        ∂Measure.pi (fun _ : Fin n => M.mu) := by
  rw [graphWeight_fubini_survivors_first M t H v]
  congr 1
  funext z
  let x₀ : Fin (n + 1) → S := Fin.insertNth v y₀ z
  let R : ℝ :=
    (∏ i ∈ Finset.univ.erase v,
      Real.exp (-t * M.degreeFunction (x₀ i))) *
      (∏ e ∈ (H.deleteIncidenceSet v).edgeFinset,
        M.edgeFactor t x₀ e)
  have hw : w ≠ v := (H.ne_of_adj hvw).symm
  have hpoint (y : S) :
      M.graphWeightIntegrand t H (Fin.insertNth v y z) =
      (Real.exp (-t * M.degreeFunction y) *
        (t * M.kernel y (x₀ w))) * R := by
    rw [leaf_graphWeightIntegrand_split_at_neighbor M t H
      (Fin.insertNth v y z) hv hvw]
    simp only [Fin.insertNth_apply_same]
    rw [insertNth_apply_independent hw y y₀ z]
    congr 1
    exact leaf_residual_independent M t H v y y₀ z
  calc
    (∫ y : S, M.graphWeightIntegrand t H (Fin.insertNth v y z) ∂M.mu) =
      ∫ y : S, (Real.exp (-t * M.degreeFunction y) *
        (t * M.kernel y (x₀ w))) * R ∂M.mu := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact hpoint y
    _ = leafResponse M t (x₀ w) * R := by
      rw [integral_mul_const]
      rfl

end PerronWright.GraphCore
