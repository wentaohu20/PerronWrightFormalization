import PerronWright.Enumeration.TreeEGF
import PerronWright.Analysis.TreeMonotone
import Mathlib.MeasureTheory.Integral.Pi

/-!
The first two coefficients of the actual finite vertex-rooted tree EGF
are identified with the corresponding rooted-tree kernel profiles.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright



variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

theorem CompactBJRModel.vertexRootedTreeWeight_one
    (M : CompactBJRModel S) (g : C(S, ℝ)) :
    M.vertexRootedTreeWeight g 1 =
      M.fieldGraphWeight g (⊥ : SimpleGraph (Fin 1)) := by
  classical
  simp [CompactBJRModel.vertexRootedTreeWeight,
    SimpleGraph.IsTree.of_subsingleton]

theorem CompactBJRModel.fieldGraphWeightIntegrand_one
    (M : CompactBJRModel S) (g : C(S, ℝ)) (x : Fin 1 → S) :
    M.fieldGraphWeightIntegrand g (⊥ : SimpleGraph (Fin 1)) x =
      Real.exp (g (x 0) - M.degreeFunction (x 0)) := by
  simp [CompactBJRModel.fieldGraphWeightIntegrand, SimpleGraph.edgeFinset]

theorem CompactBJRModel.vertexRootedTreeWeight_one_integral
    (M : CompactBJRModel S) (g : C(S, ℝ)) :
    M.vertexRootedTreeWeight g 1 =
      ∫ x : S, Real.exp (g x - M.degreeFunction x) ∂M.mu := by
  rw [M.vertexRootedTreeWeight_one]
  unfold CompactBJRModel.fieldGraphWeight
  simp_rw [M.fieldGraphWeightIntegrand_one g]
  exact integral_comp_eval (μ := fun _ : Fin 1 => M.mu) (i := 0)
    (f := fun x => Real.exp (g x - M.degreeFunction x)) (by fun_prop)

theorem CompactBJRModel.normalizedZeroTreeIter_one_apply
    (M : CompactBJRModel S) (w : ℝ) (x : S) :
    M.normalizedZeroTreeIter w 1 x =
      w * Real.exp (-M.degreeFunction x) := by
  rw [show 1 = 0 + 1 by rfl, M.normalizedZeroTreeIter_succ,
    M.normalizedZeroTreeIter_zero, M.normalizedZeroTreeMap_apply]
  have hK : M.kernel.action M.mu (0 - 1 : C(S, ℝ)) x =
      -M.degreeFunction x := by
    rw [M.kernel.action_apply]
    rw [show M.degreeFunction x = ∫ y, M.kernel x y ∂M.mu from by
      rw [CompactBJRModel.degreeFunction, ContinuousKernel.degreeMap_apply]
      rfl]
    change (∫ y, M.kernel x y * ((0 - 1 : C(S, ℝ)) y) ∂M.mu) =
      -(∫ y, M.kernel x y ∂M.mu)
    simp only [zero_sub, ContinuousMap.neg_apply, ContinuousMap.one_apply,
      mul_neg, mul_one, integral_neg]
  rw [hK]

theorem CompactBJRModel.vertexRootedTreeWeight_one_eq_iter
    (M : CompactBJRModel S) :
    M.vertexRootedTreeWeight 0 1 =
      ∫ x : S, M.normalizedZeroTreeIter 1 1 x ∂M.mu := by
  rw [M.vertexRootedTreeWeight_one_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [M.normalizedZeroTreeIter_one_apply]
  simp

private theorem graph_fin_two_bot_or_top (H : SimpleGraph (Fin 2)) :
    H = ⊥ ∨ H = ⊤ := by
  by_cases h : H.Adj 0 1
  · right
    ext a b
    fin_cases a <;> fin_cases b <;> simp_all [SimpleGraph.adj_comm]
  · left
    ext a b
    fin_cases a <;> fin_cases b <;> simp_all [SimpleGraph.adj_comm]

private theorem tree_fin_two_iff_top (H : SimpleGraph (Fin 2)) :
    H.IsTree ↔ H = ⊤ := by
  constructor
  · intro ht
    rcases graph_fin_two_bot_or_top H with h | h
    · subst H
      have hc := ((SimpleGraph.isTree_iff _).mp ht).1
      rw [SimpleGraph.connected_bot_iff] at hc
      have h01 : (0 : Fin 2) = 1 := @Subsingleton.elim _ hc.1 0 1
      exact False.elim ((by decide : (0 : Fin 2) ≠ 1) h01)
    · exact h
  · intro h
    subst H
    rw [SimpleGraph.isTree_iff_connected_and_card]
    simp
    decide

theorem CompactBJRModel.vertexRootedTreeWeight_two
    (M : CompactBJRModel S) (g : C(S, ℝ)) :
    M.vertexRootedTreeWeight g 2 =
      2 * M.fieldGraphWeight g (⊤ : SimpleGraph (Fin 2)) := by
  classical
  unfold CompactBJRModel.vertexRootedTreeWeight
  rw [Finset.sum_eq_single (⊤ : SimpleGraph (Fin 2))]
  · simp [tree_fin_two_iff_top]
  · intro H hH hne
    simp [tree_fin_two_iff_top, hne]
  · simp

theorem CompactBJRModel.fieldGraphWeightIntegrand_two
    (M : CompactBJRModel S) (x : Fin 2 → S) :
    M.fieldGraphWeightIntegrand 0 (⊤ : SimpleGraph (Fin 2)) x =
      Real.exp (-M.degreeFunction (x 0)) *
      Real.exp (-M.degreeFunction (x 1)) * M.kernel (x 0) (x 1) := by
  classical
  unfold CompactBJRModel.fieldGraphWeightIntegrand
  simp only [ContinuousMap.zero_apply, zero_sub]
  calc
    _ = (∏ i : Fin 2, Real.exp (-M.degreeFunction (x i))) *
        M.edgeFactor 1 x s(0, 1) := by
      congr 1
      apply Finset.prod_eq_single_of_mem
      · simp
      · intro e he hne
        have heq : e = s(0, 1) := by
          fin_cases e <;> simp_all
        exact False.elim (hne heq)
    _ = _ := by
      rw [CompactBJRModel.edgeFactor_mk]
      simp only [one_mul, Fin.prod_univ_two]

theorem CompactBJRModel.fieldGraphWeight_two_integral
    (M : CompactBJRModel S) :
    M.fieldGraphWeight 0 (⊤ : SimpleGraph (Fin 2)) =
      ∫ a : S, ∫ b : S,
        Real.exp (-M.degreeFunction a) *
          Real.exp (-M.degreeFunction b) * M.kernel a b ∂M.mu ∂M.mu := by
  let e := MeasurableEquiv.finTwoArrow (α := S)
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin 2 => M.mu)) (M.mu.prod M.mu) :=
    measurePreserving_finTwoArrow M.mu
  have hf := M.fieldGraphWeightIntegrand_integrable 0
    (⊤ : SimpleGraph (Fin 2))
  have hprod : Integrable
      (fun p : S × S => M.fieldGraphWeightIntegrand 0
        (⊤ : SimpleGraph (Fin 2)) (e.symm p))
      (M.mu.prod M.mu) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  unfold CompactBJRModel.fieldGraphWeight
  calc
    _ = ∫ p : S × S,
        M.fieldGraphWeightIntegrand 0 (⊤ : SimpleGraph (Fin 2))
          (e.symm p) ∂M.mu.prod M.mu := by
      exact (hmp.symm.integral_comp'
        (M.fieldGraphWeightIntegrand 0 (⊤ : SimpleGraph (Fin 2)))).symm
    _ = ∫ a : S, ∫ b : S,
        M.fieldGraphWeightIntegrand 0 (⊤ : SimpleGraph (Fin 2))
          (e.symm (a, b)) ∂M.mu ∂M.mu := by
      rw [integral_prod _ hprod]
    _ = _ := by
      congr 1
      funext a
      congr 1
      funext b
      rw [M.fieldGraphWeightIntegrand_two]
      simp only [e, MeasurableEquiv.finTwoArrow_symm_apply,
        Fin.cons_zero, Fin.cons_one]

/-- The single-vertex rooted-tree profile. -/
def CompactBJRModel.zeroTreeVertexFactor (M : CompactBJRModel S) : C(S, ℝ) :=
  ⟨fun x => Real.exp (-M.degreeFunction x), by fun_prop⟩

@[simp] theorem CompactBJRModel.zeroTreeVertexFactor_apply
    (M : CompactBJRModel S) (x : S) :
    M.zeroTreeVertexFactor x = Real.exp (-M.degreeFunction x) := rfl

theorem CompactBJRModel.zeroTreeVertexFactor_eq_first_iter
    (M : CompactBJRModel S) :
    M.zeroTreeVertexFactor = M.normalizedZeroTreeIter 1 1 := by
  ext x
  rw [M.normalizedZeroTreeIter_one_apply]
  simp

theorem CompactBJRModel.vertexRootedTreeWeight_two_eq_kernel_action
    (M : CompactBJRModel S) :
    M.vertexRootedTreeWeight 0 2 =
      2 * ∫ a : S, M.zeroTreeVertexFactor a *
        M.kernel.action M.mu M.zeroTreeVertexFactor a ∂M.mu := by
  rw [M.vertexRootedTreeWeight_two, M.fieldGraphWeight_two_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with a
  rw [M.kernel.action_apply]
  simp only [M.zeroTreeVertexFactor_apply]
  rw [← integral_const_mul]
  congr 1
  funext b
  ring

end PerronWright
