import PerronWright.Enumeration.TreeCoefficientLowOrder
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
Type-resolved coefficients of the actual finite vertex-rooted tree EGF.
The profile fixes the type at labelled root `0`, integrates all other
vertex types, and divides by the factorial of their number. Its integral
is proved equal to the corresponding EGF coefficient for every size.
No exponential root-decomposition recursion is assumed here.
-/

open MeasureTheory
open scoped Classical
noncomputable section

namespace PerronWright

variable {S : Type*} [MetricSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S]

/-- Fubini for an actual field-weighted finite graph, separating one
distinguished vertex from the remaining labelled vertices. -/
theorem CompactBJRModel.fieldGraphWeight_fubini_at_vertex
    (M : CompactBJRModel S) (g : C(S, ℝ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    M.fieldGraphWeight g H =
      ∫ y : S, ∫ z : Fin n → S,
        M.fieldGraphWeightIntegrand g H (Fin.insertNth v y z)
          ∂Measure.pi (fun _ : Fin n => M.mu) ∂M.mu := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S) v
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => M.mu))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => M.mu) v
  have hf := M.fieldGraphWeightIntegrand_integrable g H
  have hprod : Integrable
      (fun p : S × (Fin n → S) => M.fieldGraphWeightIntegrand g H (e.symm p))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  unfold CompactBJRModel.fieldGraphWeight
  calc
    _ = ∫ p : S × (Fin n → S),
        M.fieldGraphWeightIntegrand g H (e.symm p)
          ∂M.mu.prod (Measure.pi (fun _ : Fin n => M.mu)) := by
      exact (hmp.symm.integral_comp' (M.fieldGraphWeightIntegrand g H)).symm
    _ = _ := by
      rw [integral_prod _ hprod]
      rfl

/-- The unnormalised profile of labelled trees rooted at vertex `0`, with
the root type fixed and the other `n` vertex types integrated out. -/
def CompactBJRModel.rootedTreeNumerator
    (M : CompactBJRModel S) (n : ℕ) (x : S) : ℝ :=
  ∑ H : SimpleGraph (Fin (n + 1)),
    if H.IsTree then
      ∫ z : Fin n → S,
        M.fieldGraphWeightIntegrand 0 H (Fin.insertNth 0 x z)
          ∂Measure.pi (fun _ : Fin n => M.mu)
    else 0

private theorem CompactBJRModel.rootGraphSlice_integrable
    (M : CompactBJRModel S) (g : C(S, ℝ)) {n : ℕ}
    (H : SimpleGraph (Fin (n + 1))) :
    Integrable (fun x : S => ∫ z : Fin n → S,
      M.fieldGraphWeightIntegrand g H (Fin.insertNth 0 x z)
        ∂Measure.pi (fun _ : Fin n => M.mu)) M.mu := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S) 0
  have hmp : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => M.mu))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => M.mu) 0
  have hf := M.fieldGraphWeightIntegrand_integrable g H
  have hprod : Integrable
      (fun p : S × (Fin n → S) => M.fieldGraphWeightIntegrand g H (e.symm p))
      (M.mu.prod (Measure.pi (fun _ : Fin n => M.mu))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  convert hprod.integral_prod_left using 1
  funext x
  congr 1

theorem CompactBJRModel.rootedTreeNumerator_integral
    (M : CompactBJRModel S) (n : ℕ) :
    (∫ x : S, M.rootedTreeNumerator n x ∂M.mu) =
      ∑ H : SimpleGraph (Fin (n + 1)),
        if H.IsTree then M.fieldGraphWeight 0 H else 0 := by
  classical
  unfold CompactBJRModel.rootedTreeNumerator
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro H _
    by_cases hH : H.IsTree
    · simp only [hH, ↓reduceIte]
      exact (M.fieldGraphWeight_fubini_at_vertex 0 H 0).symm
    · simp [hH]
  · intro H _
    by_cases hH : H.IsTree
    · simpa only [hH, ↓reduceIte] using M.rootGraphSlice_integrable 0 H
    · simp [hH]

theorem CompactBJRModel.vertexRootedTreeWeight_succ_eq_rootedTreeNumerator
    (M : CompactBJRModel S) (n : ℕ) :
    M.vertexRootedTreeWeight 0 (n + 1) =
      (n + 1 : ℝ) * ∫ x : S, M.rootedTreeNumerator n x ∂M.mu := by
  rw [M.rootedTreeNumerator_integral]
  unfold CompactBJRModel.vertexRootedTreeWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H _
  by_cases ht : H.IsTree
  · simp [ht, Finset.sum_const, nsmul_eq_mul]
  · simp [ht]

/-- Candidate `(n+1)`st type-resolved rooted-tree coefficient. -/
def CompactBJRModel.rootedTreeCoefficient
    (M : CompactBJRModel S) (n : ℕ) (x : S) : ℝ :=
  M.rootedTreeNumerator n x / (Nat.factorial n : ℝ)

theorem CompactBJRModel.rootedTreeCoefficient_nonneg
    (M : CompactBJRModel S) (n : ℕ) (x : S) :
    0 ≤ M.rootedTreeCoefficient n x := by
  unfold CompactBJRModel.rootedTreeCoefficient
    CompactBJRModel.rootedTreeNumerator
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro H _
    split
    · exact integral_nonneg (fun z =>
        M.fieldGraphWeightIntegrand_nonneg 0 H (Fin.insertNth 0 x z))
    · exact le_rfl
  · exact Nat.cast_nonneg _

theorem CompactBJRModel.vertexRootedTreeEGF_coeff_eq_rootedTreeCoefficient_integral
    (M : CompactBJRModel S) (n : ℕ) :
    PowerSeries.coeff (n + 1) (M.vertexRootedTreeEGF 0) =
      ∫ x : S, M.rootedTreeCoefficient n x ∂M.mu := by
  have hn : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsucc : (n + 1 : ℝ) ≠ 0 := by positivity
  have hint : (∫ x : S, M.rootedTreeCoefficient n x ∂M.mu) =
      (∫ x : S, M.rootedTreeNumerator n x ∂M.mu) /
        (Nat.factorial n : ℝ) := by
    simp only [CompactBJRModel.rootedTreeCoefficient, div_eq_mul_inv,
      integral_mul_const]
  rw [hint]
  simp only [CompactBJRModel.vertexRootedTreeEGF,
    PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
  rw [M.vertexRootedTreeWeight_succ_eq_rootedTreeNumerator,
    Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

end PerronWright
